(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply Qfw3_c1 Q7UD Qsw7 QJjn QgoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes Qfw3_c1.Mq2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import Q7UD.
Import Qsw7 QJjn.
Import QgoP.
Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Definition reserve_entry : Z := 0xc1978.
Definition pushb_entry : Z := 0xc19e4.

Lemma le1_w : forall v : word, le1 v = [Z_to_bv 8 (bv_unsigned v)].
Proof. intros v. unfold le1, word_to_le_bytes. cbn. reflexivity. Qed.

Lemma land1_even : forall n, Z.land (2 * n) 1 = 0.
Proof. intros n. rewrite Z.land_comm. change 1 with (Z.ones 1). rewrite Z.land_comm, Z.land_ones by lia. change (2 ^ 1) with 2. rewrite Z.mul_comm, Z.mod_mul; lia. Qed.

Lemma shiftr1_double : forall n, 0 <= n -> Z.shiftr (2 * n) 1 = n.
Proof. intros n Hn. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. rewrite Z.mul_comm, Z.div_mul; lia. Qed.

Definition reserve_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists a2',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs)
/\ munch [] m m /\ wmono asegs m m /\ mem_inv asegs m.

Definition reserve_stmt : Prop :=
forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (S n r : Z) (szb : byte) (rest : list cell),
a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 r -> 0 <= r <= 22 ->
bv_unsigned szb = 2 * n -> 0 <= n ->
rw_cells asegs m S (C1 szb :: rest) ->
mem_inv asegs m ->
evt asegs (reserve_post ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 reserve_entry) fc None m (seg_rom asegs)).

Lemma reserve_spec : reserve_stmt.
Proof.
unfold reserve_stmt. intros until rest. intros A0 A1 Hr Hsz Hn OBJ MI. subst a0 a1.
pose proof (bv_unsigned_in_range 8 szb) as SR. unfold bv_modulus in SR. cbn in SR.
pose proof (rw_cells_bound _ _ _ _ OBJ) as OB. cbn [cells_size csize] in OB.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold reserve_entry.
step. step. if_falsex.
step. change (zxb szb) with (Z_to_bv 64 (bv_unsigned szb)). rewrite Hsz.
step. rewrite (unsigned_lit (2 * n)) by lia. rewrite land1_even.
step. if_false.
step. step. if_falsex.
step.
finish.
Qed.

Definition pushb_W (sp S n : Z) : list (Z * Z) := [(sp - 64, sp); (S, S + 1); (S + n + 1, S + n + 3)].

Definition pushb_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a1 : word) (S n lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0' a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (szb' : byte),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch (pushb_W (bv_unsigned sp) S n) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ bv_unsigned szb' = 2 * (n + 1)
/\ rw_cells asegs m' S [C1 szb']
/\ rw_cells asegs m' (S + n + 1) [C1 (Z_to_bv 8 (bv_unsigned a1)); C1 b0]
/\ stk asegs m' lo (bv_unsigned sp).

Definition pushb_stmt : Prop :=
forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (S n lo : Z) (szb x y : byte),
a0 = Z_to_bv 64 S ->
bv_unsigned szb = 2 * n -> 0 <= n <= 21 ->
rw_cells asegs m S [C1 szb] ->
rw_cells asegs m (S + n + 1) [C1 x; C1 y] ->
stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 ->
(S + 24 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= S) ->
mem_inv asegs m ->
evt asegs (pushb_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a1 S n lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pushb_entry) fc None m (seg_rom asegs)).

Lemma pushb_spec : pushb_stmt.
Proof.
unfold pushb_stmt. intros until y. intros A0 Hsz Hn SZ WIN ST LO SEP MI. subst a0.
pose proof (bv_unsigned_in_range 8 szb) as SR. unfold bv_modulus in SR. cbn in SR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof (bv_unsigned_in_range 64 a1) as CR. unfold bv_modulus in CR. cbn in CR.
pose proof (rw_cells_bound _ _ _ _ SZ) as OB1. cbn [cells_size csize Nat.add] in OB1.
pose proof (rw_cells_bound _ _ _ _ WIN) as OB2. cbn [cells_size csize Nat.add] in OB2.
pose proof (munch_refl (pushb_W (bv_unsigned sp) S n) m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold pushb_W in MU. unfold pushb_entry.
carve_frame 64%nat ST.
do 9 step.

step. step. change (zxb szb) with (Z_to_bv 64 (bv_unsigned szb)). rewrite Hsz.
step. rewrite (unsigned_lit (2 * n)) by lia. rewrite land1_even.
step. step. if_false.

step. step. if_truex.

step. rewrite (unsigned_lit (2 * n)) by lia. rewrite shiftr1_double by lia.
step. step.
step. rewrite le1_w. rewrite (unsigned_lit (2 * n + 2)) by lia. mem_after_store.
step.

step. replace (S + 1 + n) with (S + n + 1) by lia.
step. rewrite le1_w. mem_after_store.
step. rewrite le1_w. rewrite (unsigned_lit 0) by lia. change (Z_to_bv 8 0) with b0. mem_after_store.

do 10 step.
lazymatch goal with H : rw_cells asegs ?mx (bv_unsigned sp + -64) _ |- _ => rename H into FR2 end.
lazymatch goal with H : stk asegs ?mx lo _ |- _ => rename H into ST2 end.
release_frame FR2 ST2 (bv_unsigned sp).
finish.
2: eassumption.
rewrite Z_to_bv_unsigned. change (bv_wrap 8 (2 * n + 2)) with ((2 * n + 2) mod 2 ^ 8). rewrite Z.mod_small; lia.
Qed.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH QHnV QCcH QfLs Q0Ek Qhd4 Qwm6 Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0.
Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Definition jo_get_A_entry : Z := 0x9a734.

Lemma div8_off : forall p j, p mod 8 = 0 -> 0 <= j < 8 -> (p + j) / 8 = p / 8.
Proof. intros p j Hp Hj. Z.div_mod_to_equations. lia. Qed.

Ltac asan_chk0_off p j :=
step; step; sh_norm; rewrite (div8_off p j) by lia;
step; step; first [ if_false | if_true ]; rewrite ?sxb_zero, ?zxb_zero.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section Regs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).

Definition ret4x (v : word) (m' : word -> option byte) : machine_state -> Prop :=
fun ms' => exists w x y, ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 v w x y a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs).

Lemma jo_get_null_A : forall m lo,
mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 ->
evt asegs (fun ms' => exists m', ret4x (Z_to_bv 64 0) m' ms' /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 jo_get_A_entry) fc None m (seg_rom asegs)).
Proof.
intros m lo MI ST LOS. unfold jo_get_A_entry.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
carve_frame 16%nat ST.
step. step. step. if_true. step. step. step.
apply evt_done. eexists. split; [eexists _, _, _; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
release_frame FR ST (bv_unsigned sp). exact ST.
Qed.

Lemma jo_get_A : forall m lo p ty rc tojs pb udel ud sbcell n,
rw_cells asegs m p (jhdr_cells ty rc tojs pb udel ud) ->
0 < p -> p + 40 <= 2^64 -> p mod 16 = 0 -> 0 <= rc -> rc + 1 < 2^31 -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> alloc_ceiling <= lo -> p + 40 <= alloc_ceiling ->

ro_cells asegs m A_GOT_SB [C8 (Z_to_bv 64 sbcell)] -> ro_cells asegs m sbcell [C8 (Z_to_bv 64 A_SB)] ->
0 < sbcell -> sbcell + 8 <= alloc_ceiling -> (sbcell + 8 <= p \/ p + 40 <= sbcell) -> p / 8 + A_SB + (n + 7) / 8 <= alloc_ceiling ->

8 <= n -> bytes_at asegs m (p / 8 + A_SB) (shadow_bytes n) ->
evt asegs (fun ms' => exists m', ret4x (Z_to_bv 64 p) m' ms' /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (p + 4, p + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' p (jhdr_cells ty (rc + 1) tojs pb udel ud) /\ stk asegs m' lo (bv_unsigned sp))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 jo_get_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until n. intros HDR Hp Hph Hal Hrc Hrc1 MI ST LOS LO PHI GOT CELL Hc0 Hc8 Hcp HSBhi Hn SH.
unfold jhdr_cells in HDR. unfold jo_get_A_entry, A_GOT_SB, A_SB in *.
unfold alloc_ceiling, sp_window_lo, stack_max_size in LO, PHI, Hc8, HSBhi.
assert (SHn : 1 <= (n + 7) / 8) by (apply Z.div_le_lower_bound; lia).
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (p + 4, p + 8)] m) as MU.
pose proof (shadow_head0 asegs m _ n Hn SH) as SH0. clear SH.
carve_frame 16%nat ST.
step. step. step. if_falsex.
step. step. step. step.
asan_chk0_off p 4.
step. step. norm_w32. stepz. step. step. step.
apply evt_done. eexists. split; [eexists _, _, _; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
split. { unfold jhdr_cells. assumption. }
release_frame FR ST (bv_unsigned sp). exact ST.
Qed.
End Regs.
End RC__1.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import QCcH Q0Ek QjDH.Mq0.
Import ListNotations. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Definition str_w (z : Z) : Z := 6 * (z - 49) + 2.
Definition key_w (kn : Z) : Z := 6 * Z.max 0 (kn - 1) + 14.
Definition NULL_W : Z := 4.
Notation W_BOOL := 8 (only parsing).
Notation W_DBL := 9 (only parsing).
Notation W_INT := 20 (only parsing).
Notation W_CONT := 24 (only parsing).
Notation W_UD := 16 (only parsing).
Notation W_HSTR := 50 (only parsing).

Fixpoint jtx (s : jshape) (BS : list blk) {struct s} : option (Z * list blk) :=
match s with
| Sbool => match BS with (_, z) :: r => if z =? 48 then Some (8, r) else None | [] => None end
| Sdouble false => match BS with (_, z) :: r => if z =? 48 then Some (9, r) else None | [] => None end
| Sdouble true => match BS with (_, z) :: (_, udn) :: r => if z =? 48 then Some (16 + Z.max 0 (udn - 1), r) else None | _ => None end
| Sint => match BS with (_, z) :: r => if z =? 56 then Some (20, r) else None | [] => None end
| Sstr false => match BS with (_, z) :: r => if 57 <=? z then Some (str_w z, r) else None | [] => None end
| Sstr true => match BS with (_, z) :: (_, pdn) :: r => if z =? 56 then Some (6 * Z.max 0 (pdn - 1) + 50, r) else None | _ => None end
| Sarr kids =>
match BS with
| (_, z) :: (_, za) :: _ :: r =>
if (z =? 48) && (za =? 32) then
(fix go (ks : list (option jshape)) (bs : list blk) (acc : Z) {struct ks} : option (Z * list blk) :=
match ks with
| [] => Some (acc, bs)
| None :: ks' => go ks' bs (acc + (2 + NULL_W))
| Some s' :: ks' => match jtx s' bs with Some (w, bs') => go ks' bs' (acc + (2 + w)) | None => None end
end) kids r 24
else None
| _ => None
end
| Sobj kids =>
match BS with
| (_, z) :: (_, zt) :: _ :: r =>
if (z =? 48) && (zt =? 56) && (length kids <=? length r)%nat then
(fix go (ks : list (option jshape)) (keys : list blk) (bs : list blk) (acc : Z) {struct ks} : option (Z * list blk) :=
match ks, keys with
| [], _ => Some (acc, bs)
| None :: ks', (_, kn) :: keys' => go ks' keys' bs (acc + (key_w kn + NULL_W))
| Some s' :: ks', (_, kn) :: keys' => match jtx s' bs with Some (w, bs') => go ks' keys' bs' (acc + (key_w kn + w)) | None => None end
| _ :: _, [] => None
end) kids (firstn (length kids) r) (skipn (length kids) r) 24
else None
| _ => None
end
end.

Fixpoint jtxk_arr (ks : list (option jshape)) (bs : list blk) (acc : Z) {struct ks} : option (Z * list blk) :=
match ks with
| [] => Some (acc, bs)
| None :: ks' => jtxk_arr ks' bs (acc + (2 + NULL_W))
| Some s' :: ks' => match jtx s' bs with Some (w, bs') => jtxk_arr ks' bs' (acc + (2 + w)) | None => None end
end.
Fixpoint jtxk_obj (ks : list (option jshape)) (keys : list blk) (bs : list blk) (acc : Z) {struct ks} : option (Z * list blk) :=
match ks, keys with
| [], _ => Some (acc, bs)
| None :: ks', (_, kn) :: keys' => jtxk_obj ks' keys' bs (acc + (key_w kn + NULL_W))
| Some s' :: ks', (_, kn) :: keys' => match jtx s' bs with Some (w, bs') => jtxk_obj ks' keys' bs' (acc + (key_w kn + w)) | None => None end
| _ :: _, [] => None
end.

Lemma jtx_arr_eq : forall kids b0 b1 b2 r,
jtx (Sarr kids) (b0 :: b1 :: b2 :: r) = if (snd b0 =? 48) && (snd b1 =? 32) then jtxk_arr kids r 24 else None.
Proof.
intros kids [a0 z0] [a1 z1] b2 r. cbn [jtx snd]. destruct ((z0 =? 48) && (z1 =? 32)); [|reflexivity].
generalize 24. generalize r. induction kids as [|[s'|] kids IH]; intros r0 acc; cbn [jtxk_arr]; [reflexivity| |apply IH].
destruct (jtx s' r0) as [[w bs']|]; [apply IH | reflexivity].
Qed.
Lemma jtx_obj_eq : forall kids b0 b1 b2 r,
jtx (Sobj kids) (b0 :: b1 :: b2 :: r) =
if (snd b0 =? 48) && (snd b1 =? 56) && (length kids <=? length r)%nat then jtxk_obj kids (firstn (length kids) r) (skipn (length kids) r) 24 else None.
Proof.
intros kids [a0 z0] [a1 z1] b2 r. cbn [jtx snd]. destruct ((z0 =? 48) && (z1 =? 56) && (length kids <=? length r)%nat); [|reflexivity].
generalize 24. generalize (skipn (length kids) r). generalize (firstn (length kids) r).
induction kids as [|[s'|] kids IH]; intros keys r0 acc; cbn [jtxk_obj]; [reflexivity| |].
- destruct keys as [|[k kn] keys]; [reflexivity|]. destruct (jtx s' r0) as [[w bs']|]; [apply IH | reflexivity].
- destruct keys as [|[k kn] keys]; [reflexivity|]. apply IH.
Qed.

Lemma jtx_pb_none : forall s a L, jtx s ((a, 16) :: L) = None.
Proof.
intros s a L. destruct s as [|[|]| |[|]|kids|kids]; cbn [jtx]; try reflexivity.
all: destruct L as [|[a1 z1] L]; try reflexivity. all: destruct L as [|b2 L]; reflexivity.
Qed.

Lemma key_w_nonneg : forall kn, 0 <= key_w kn. Proof. intros. unfold key_w. lia. Qed.
Lemma jtxk_arr_acc : forall (P : jshape -> Prop) ks, (forall s, In (Some s) ks -> forall bs w r, jtx s bs = Some (w, r) -> 0 <= w) ->
forall bs acc w r, jtxk_arr ks bs acc = Some (w, r) -> acc <= w.
Proof.
intros _ ks. induction ks as [|[s'|] ks IH]; intros HK bs acc w r H; cbn [jtxk_arr] in H.
- injection H as <- _. lia.
- destruct (jtx s' bs) as [[w' bs']|] eqn:E; [|discriminate].
pose proof (HK s' (or_introl eq_refl) _ _ _ E). specialize (IH (fun s Hs => HK s (or_intror Hs)) _ _ _ _ H). lia.
- specialize (IH (fun s Hs => HK s (or_intror Hs)) _ _ _ _ H). unfold NULL_W in *. lia.
Qed.
Lemma jtxk_obj_acc : forall ks, (forall s, In (Some s) ks -> forall bs w r, jtx s bs = Some (w, r) -> 0 <= w) ->
forall keys bs acc w r, jtxk_obj ks keys bs acc = Some (w, r) -> acc <= w.
Proof.
intros ks. induction ks as [|[s'|] ks IH]; intros HK keys bs acc w r H; cbn [jtxk_obj] in H.
- injection H as <- _. lia.
- destruct keys as [|[k kn] keys]; [discriminate|]. destruct (jtx s' bs) as [[w' bs']|] eqn:E; [|discriminate].
pose proof (HK s' (or_introl eq_refl) _ _ _ E). pose proof (key_w_nonneg kn). specialize (IH (fun s Hs => HK s (or_intror Hs)) _ _ _ _ _ H). lia.
- destruct keys as [|[k kn] keys]; [discriminate|]. pose proof (key_w_nonneg kn). specialize (IH (fun s Hs => HK s (or_intror Hs)) _ _ _ _ _ H). unfold NULL_W in *. lia.
Qed.
Lemma jtx_nonneg : forall s bs w r, jtx s bs = Some (w, r) -> 0 <= w.
Proof.
induction s as [|u| |h|kids IHk|kids IHk] using jshape_ind2; intros bs w r H.
- cbn in H. destruct bs as [|[a z] bs]; [discriminate|]. destruct (z =? 48); [injection H as <- _; lia | discriminate].
- destruct u; cbn in H.
+ destruct bs as [|[a z] [|[a1 z1] bs]]; try discriminate. destruct (z =? 48); [injection H as <- _; lia | discriminate].
+ destruct bs as [|[a z] bs]; [discriminate|]. destruct (z =? 48); [injection H as <- _; lia | discriminate].
- cbn in H. destruct bs as [|[a z] bs]; [discriminate|]. destruct (z =? 56); [injection H as <- _; lia | discriminate].
- destruct h; cbn in H.
+ destruct bs as [|[a z] [|[a1 z1] bs]]; try discriminate. destruct (z =? 56); [injection H as <- _; lia | discriminate].
+ destruct bs as [|[a z] bs]; [discriminate|]. destruct (Z.leb_spec 57 z); [injection H as <- _; unfold str_w; lia | discriminate].
- destruct bs as [|[a0 z0] [|[a1 z1] [|b2 r0]]]; try discriminate. rewrite jtx_obj_eq in H.
destruct ((snd (a0, z0) =? 48) && (snd (a1, z1) =? 56) && (length kids <=? length r0)%nat); [|discriminate].
pose proof (jtxk_obj_acc kids IHk _ _ _ _ _ H). lia.
- destruct bs as [|[a0 z0] [|[a1 z1] [|b2 r0]]]; try discriminate. rewrite jtx_arr_eq in H.
destruct ((snd (a0, z0) =? 48) && (snd (a1, z1) =? 32)); [|discriminate].
pose proof (jtxk_arr_acc (fun _ => True) kids IHk _ _ _ _ H). lia.
Qed.

Lemma jtxk_arr_frame : forall ks, (forall s, In (Some s) ks -> forall bs w r X, jtx s bs = Some (w, r) -> jtx s (bs ++ X) = Some (w, r ++ X)) ->
forall bs acc w r X, jtxk_arr ks bs acc = Some (w, r) -> jtxk_arr ks (bs ++ X) acc = Some (w, r ++ X).
Proof.
induction ks as [|[s'|] ks IH]; intros HK bs acc w r X H; cbn [jtxk_arr] in H |- *.
- injection H as <- <-. reflexivity.
- destruct (jtx s' bs) as [[w' bs']|] eqn:E; [|discriminate]. rewrite (HK s' (or_introl eq_refl) _ _ _ X E).
apply IH; [intros s Hs; apply HK; right; exact Hs | exact H].
- apply IH; [intros s Hs; apply HK; right; exact Hs | exact H].
Qed.
Lemma jtxk_obj_frame : forall ks, (forall s, In (Some s) ks -> forall bs w r X, jtx s bs = Some (w, r) -> jtx s (bs ++ X) = Some (w, r ++ X)) ->
forall keys bs acc w r X, jtxk_obj ks keys bs acc = Some (w, r) -> jtxk_obj ks keys (bs ++ X) acc = Some (w, r ++ X).
Proof.
induction ks as [|[s'|] ks IH]; intros HK keys bs acc w r X H; cbn [jtxk_obj] in H |- *.
- injection H as <- <-. reflexivity.
- destruct keys as [|[k kn] keys]; [discriminate|]. destruct (jtx s' bs) as [[w' bs']|] eqn:E; [|discriminate]. rewrite (HK s' (or_introl eq_refl) _ _ _ X E).
apply IH; [intros s Hs; apply HK; right; exact Hs | exact H].
- destruct keys as [|[k kn] keys]; [discriminate|]. apply IH; [intros s Hs; apply HK; right; exact Hs | exact H].
Qed.

Lemma jtx_frame : forall s bs w r X, jtx s bs = Some (w, r) -> jtx s (bs ++ X) = Some (w, r ++ X).
Proof.
induction s as [|u| |h|kids IHk|kids IHk] using jshape_ind2; intros bs w r X H.
- cbn in H |- *. destruct bs as [|[a z] bs]; [discriminate|]. cbn [app]. destruct (z =? 48); [injection H as <- <-; reflexivity | discriminate].
- destruct u; cbn in H |- *.
+ destruct bs as [|[a z] [|[a1 z1] bs]]; try discriminate. cbn [app]. destruct (z =? 48); [injection H as <- <-; reflexivity | discriminate].
+ destruct bs as [|[a z] bs]; [discriminate|]. cbn [app]. destruct (z =? 48); [injection H as <- <-; reflexivity | discriminate].
- cbn in H |- *. destruct bs as [|[a z] bs]; [discriminate|]. cbn [app]. destruct (z =? 56); [injection H as <- <-; reflexivity | discriminate].
- destruct h; cbn in H |- *.
+ destruct bs as [|[a z] [|[a1 z1] bs]]; try discriminate. cbn [app]. destruct (z =? 56); [injection H as <- <-; reflexivity | discriminate].
+ destruct bs as [|[a z] bs]; [discriminate|]. cbn [app]. destruct (57 <=? z); [injection H as <- <-; reflexivity | discriminate].
- destruct bs as [|[a0 z0] [|[a1 z1] [|b2 r0]]]; try discriminate. cbn [app]. rewrite jtx_obj_eq in H |- *.
destruct ((snd (a0, z0) =? 48) && (snd (a1, z1) =? 56)) eqn:E1; [|discriminate]. cbn [andb] in H |- *.
destruct (Nat.leb_spec (length kids) (length r0)) as [LE|GT]; [|discriminate].
replace (length kids <=? length (r0 ++ X))%nat with true by (symmetry; apply Nat.leb_le; rewrite length_app; lia).
rewrite firstn_app, skipn_app. replace (length kids - length r0)%nat with 0%nat by lia. cbn [firstn skipn]. rewrite app_nil_r.
apply jtxk_obj_frame; [exact IHk | exact H].
- destruct bs as [|[a0 z0] [|[a1 z1] [|b2 r0]]]; try discriminate. cbn [app]. rewrite jtx_arr_eq in H |- *.
destruct ((snd (a0, z0) =? 48) && (snd (a1, z1) =? 32)); [|discriminate].
apply jtxk_arr_frame; [exact IHk | exact H].
Qed.

Definition jfresh (s : jshape) (BS : list blk) (w : Z) : Prop := jtx s BS = Some (w, []).

Lemma jtxk_arr_app : forall ks1 ks2 bs acc,
jtxk_arr (ks1 ++ ks2) bs acc = match jtxk_arr ks1 bs acc with Some (w1, bs1) => jtxk_arr ks2 bs1 w1 | None => None end.
Proof.
induction ks1 as [|[s'|] ks1 IH]; intros ks2 bs acc; cbn [app jtxk_arr]; [reflexivity| |apply IH].
destruct (jtx s' bs) as [[w bs']|]; [apply IH | reflexivity].
Qed.
Lemma jtxk_obj_app : forall ks1 ks2 keys1 keys2 bs acc, length keys1 = length ks1 ->
jtxk_obj (ks1 ++ ks2) (keys1 ++ keys2) bs acc = match jtxk_obj ks1 keys1 bs acc with Some (w1, bs1) => jtxk_obj ks2 keys2 bs1 w1 | None => None end.
Proof.
induction ks1 as [|[s'|] ks1 IH]; intros ks2 keys1 keys2 bs acc L.
- destruct keys1; [|discriminate]. reflexivity.
- destruct keys1 as [|[k kn] keys1]; [discriminate|]. cbn [app jtxk_obj]. destruct (jtx s' bs) as [[w bs']|]; [apply IH; cbn in L; lia | reflexivity].
- destruct keys1 as [|[k kn] keys1]; [discriminate|]. cbn [app jtxk_obj]. apply IH. cbn in L; lia.
Qed.

Lemma jtx_arr_add : forall kids b0 b1 b2 KB w k KBk wk,
jfresh (Sarr kids) (b0 :: b1 :: b2 :: KB) w -> jfresh k KBk wk ->
jfresh (Sarr (kids ++ [Some k])) (b0 :: b1 :: b2 :: KB ++ KBk) (w + (2 + wk)).
Proof.
intros kids b0 b1 b2 KB w k KBk wk H Hk. unfold jfresh in *. rewrite jtx_arr_eq in H |- *.
destruct ((snd b0 =? 48) && (snd b1 =? 32)); [|discriminate].
rewrite jtxk_arr_app. rewrite (jtxk_arr_frame kids (fun s _ => jtx_frame s) _ _ _ _ KBk H). cbn [app jtxk_arr]. rewrite Hk. reflexivity.
Qed.
Lemma jtx_arr_add_null : forall kids b0 b1 b2 KB w,
jfresh (Sarr kids) (b0 :: b1 :: b2 :: KB) w -> jfresh (Sarr (kids ++ [None])) (b0 :: b1 :: b2 :: KB) (w + (2 + NULL_W)).
Proof.
intros kids b0 b1 b2 KB w H. unfold jfresh in *. rewrite jtx_arr_eq in H |- *.
destruct ((snd b0 =? 48) && (snd b1 =? 32)); [|discriminate].
rewrite jtxk_arr_app, H. reflexivity.
Qed.
Lemma jtx_arr_new : forall b0 b1 b2, snd b0 = 48 -> snd b1 = 32 -> jfresh (Sarr []) [b0; b1; b2] W_CONT.
Proof. intros b0 b1 b2 H0 H1. unfold jfresh. rewrite jtx_arr_eq, H0, H1. reflexivity. Qed.

Lemma firstn_app_exact : forall {A} (l r : list A) n, length l = n -> firstn n (l ++ r) = l.
Proof. intros A l r n <-. rewrite firstn_app, Nat.sub_diag, firstn_all. cbn [firstn]. apply app_nil_r. Qed.
Lemma skipn_app_exact : forall {A} (l r : list A) n, length l = n -> skipn n (l ++ r) = r.
Proof. intros A l r n <-. rewrite skipn_app, Nat.sub_diag, skipn_all. reflexivity. Qed.

Lemma jtx_obj_add : forall kids b0 b1 b2 keys KB w kb k KBk wk, length keys = length kids ->
jfresh (Sobj kids) (b0 :: b1 :: b2 :: keys ++ KB) w -> jfresh k KBk wk ->
jfresh (Sobj (kids ++ [Some k])) (b0 :: b1 :: b2 :: (keys ++ [kb]) ++ KB ++ KBk) (w + (key_w (snd kb) + wk)).
Proof.
intros kids b0 b1 b2 keys KB w [kk kn] k KBk wk L H Hk. unfold jfresh in *. rewrite jtx_obj_eq in H |- *.
destruct ((snd b0 =? 48) && (snd b1 =? 56)); [|discriminate]. cbn [andb] in H |- *.
destruct (Nat.leb_spec (length kids) (length (keys ++ KB))) as [_|GT]; [|discriminate].
match goal with |- context [(?x <=? ?y)%nat] => destruct (Nat.leb_spec x y) as [_|GT]; [| exfalso; rewrite !length_app in GT; cbn [length] in GT; lia] end.
rewrite (firstn_app_exact keys KB) in H by exact L. rewrite (skipn_app_exact keys KB) in H by exact L.
rewrite (firstn_app_exact (keys ++ [(kk, kn)]) (KB ++ KBk)) by (rewrite !length_app; cbn [length]; lia).
rewrite (skipn_app_exact (keys ++ [(kk, kn)]) (KB ++ KBk)) by (rewrite !length_app; cbn [length]; lia).
rewrite jtxk_obj_app by exact L. rewrite (jtxk_obj_frame kids (fun s _ => jtx_frame s) _ _ _ _ _ KBk H). cbn [app jtxk_obj snd]. rewrite Hk. reflexivity.
Qed.
Lemma jtx_obj_add_null : forall kids b0 b1 b2 keys KB w kb, length keys = length kids ->
jfresh (Sobj kids) (b0 :: b1 :: b2 :: keys ++ KB) w ->
jfresh (Sobj (kids ++ [None])) (b0 :: b1 :: b2 :: (keys ++ [kb]) ++ KB) (w + (key_w (snd kb) + NULL_W)).
Proof.
intros kids b0 b1 b2 keys KB w [kk kn] L H. unfold jfresh in *. rewrite jtx_obj_eq in H |- *.
destruct ((snd b0 =? 48) && (snd b1 =? 56)); [|discriminate]. cbn [andb] in H |- *.
destruct (Nat.leb_spec (length kids) (length (keys ++ KB))) as [_|GT]; [|discriminate].
match goal with |- context [(?x <=? ?y)%nat] => destruct (Nat.leb_spec x y) as [_|GT]; [| exfalso; rewrite !length_app in GT; cbn [length] in GT; lia] end.
rewrite (firstn_app_exact keys KB) in H by exact L. rewrite (skipn_app_exact keys KB) in H by exact L.
rewrite (firstn_app_exact (keys ++ [(kk, kn)]) KB) by (rewrite !length_app; cbn [length]; lia).
rewrite (skipn_app_exact (keys ++ [(kk, kn)]) KB) by (rewrite !length_app; cbn [length]; lia).
rewrite jtxk_obj_app by exact L. rewrite H. reflexivity.
Qed.
Lemma jtx_obj_new : forall b0 b1 b2, snd b0 = 48 -> snd b1 = 56 -> jfresh (Sobj []) [b0; b1; b2] W_CONT.
Proof. intros b0 b1 b2 H0 H1. unfold jfresh. rewrite jtx_obj_eq, H0, H1. reflexivity. Qed.

Lemma jtx_dbl_ud : forall p ud udn, jfresh (Sdouble true) [(p, 48); (ud, udn)] (W_UD + Z.max 0 (udn - 1)). Proof. reflexivity. Qed.

Lemma jtx_str : forall p len, 0 <= len -> jfresh (Sstr false) [(p, str_objsize len)] (6 * Z.max len 8 + 2).
Proof.
intros p len H. unfold jfresh, str_objsize. cbn [jtx]. replace (57 <=? 49 + Z.max len 8) with true by (symmetry; apply Z.leb_le; lia).
unfold str_w. do 2 f_equal. lia.
Qed.

Definition jtx_opt (k : option jshape) (BS : list blk) : option (Z * list blk) :=
match k with None => Some (NULL_W, BS) | Some s => jtx s BS end.

Lemma jtx_arr_add_opt : forall kids b0 b1 b2 KB w k KBk wk,
jfresh (Sarr kids) (b0 :: b1 :: b2 :: KB) w -> jtx_opt k KBk = Some (wk, []) ->
jfresh (Sarr (kids ++ [k])) (b0 :: b1 :: b2 :: KB ++ KBk) (w + (2 + wk)).
Proof.
intros kids b0 b1 b2 KB w [s|] KBk wk H Hk; cbn [jtx_opt] in Hk.
- apply jtx_arr_add; assumption.
- injection Hk as <- ->. rewrite app_nil_r. apply jtx_arr_add_null. exact H.
Qed.
Lemma jtx_obj_add_opt : forall kids b0 b1 b2 keys KB w kb k KBk wk, length keys = length kids ->
jfresh (Sobj kids) (b0 :: b1 :: b2 :: keys ++ KB) w -> jtx_opt k KBk = Some (wk, []) ->
jfresh (Sobj (kids ++ [k])) (b0 :: b1 :: b2 :: (keys ++ [kb]) ++ KB ++ KBk) (w + (key_w (snd kb) + wk)).
Proof.
intros kids b0 b1 b2 keys KB w kb [s|] KBk wk L H Hk; cbn [jtx_opt] in Hk.
- apply jtx_obj_add; assumption.
- injection Hk as <- ->. rewrite app_nil_r. apply jtx_obj_add_null; assumption.
Qed.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn.
Import QSL3.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0.
Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Definition lh_delete_tail_A_entry : Z := 0xa29b4.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section S.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Definition lh_delete_costB (es : list lent) (jf : nat) : Z := 512 * (Z.of_nat (length es) - Z.of_nat jf).

Definition lh_delete_tail_A_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word)
(t tbl size : Z) (es : list lent) (jf : nat)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' svs' (B' : bud),
ret_state A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 0) m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\ stk asegs m' lo (bv_unsigned sp) /\ heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv] /\
lh_open asegs A4F m' t tbl size (firstn jf es) svs' /\
bB B - lh_delete_costB es jf <= bB B' /\ bD B <= bD B' /\
HEAPAx A' (lh_blocks t tbl size (firstn jf es) ++ LB) LM FRS B' m' md'.

Definition lh_delete_tail_A_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word)
(t tbl size : Z) (es : list lent) (svs : list slotv) (jf : nat) (ef : lent),
HEAPAx A (lh_blocks t tbl size es ++ LB) LM FRS B m md ->
lh_open asegs A4F m t tbl size es svs ->
nth_error es jf = Some ef -> (forall j x, (jf <= j)%nat -> nth_error es j = Some x -> le_v x = 0) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 144 - 16 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 (ent_addr tbl (le_ix ef)) ->
lh_delete_costB es jf <= bB B ->
(forall ms' md' A', lh_delete_tail_A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo errv t tbl size es jf ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 lh_delete_tail_A_entry) fc None m (seg_rom asegs)).
End S.
End RC__1.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek.
Import Q7UD Qhd4.
Import Qwm6.Mq0.
Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition LOCCELL_A : Z := A_TP - 48.
Definition GLOBLOC_A : Z := 0x643128.
Definition LC_GLOBAL_A : Z := 2^64 - 1.
Definition LOCALE_LOCK_A : Z := 0x6431d0.
Definition CNAME_A : Z := 0x230a0.
Definition A_USELOCALE : Z := 0xcdb2c.
Definition A_ERRNO_LOCATION : Z := 0xcc3a4.
Definition A_DUPLOCALE : Z := 0xcce40.
Definition A_NEWLOCALE : Z := 0xccf4c.
Definition A_FREELOCALE : Z := 0xcceac.

Definition usl_newA (cur nw : Z) : Z := if nw =? 0 then cur else if nw =? LC_GLOBAL_A then GLOBLOC_A else nw.
Definition usl_retA (cur : Z) : Z := if cur =? GLOBLOC_A then LC_GLOBAL_A else cur.

Section ALocaleStmt.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Definition uselocale_A_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cur nw : Z),
rw_cells asegs m LOCCELL_A [C8 (Z_to_bv 64 cur)] -> 0 <= cur < 2^64 -> 0 <= nw < 2^64 ->
tp = Z_to_bv 64 A_TP -> mem_inv asegs m ->
evt asegs (fun ms' => exists m' a1' a2' a3' a4',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (usl_retA cur)) a1' a2' a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(LOCCELL_A, LOCCELL_A + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' LOCCELL_A [C8 (Z_to_bv 64 (usl_newA cur nw))])
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 nw) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_USELOCALE) fc None m (seg_rom asegs)).

Definition errno_location_A_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
tp = Z_to_bv 64 A_TP ->
evt asegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A_ERRNO) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ERRNO_LOCATION) fc None m (seg_rom asegs)).

Definition duplocale_A_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word),
HEAPAx A LB LM FRS B m md ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 - hl_stack A4H ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 ->
Z.of_nat (length LM) < 8 ->
M2D <= bD B ->
(forall ms' m' md' A' (r : Z) (errv' : word),
ret_state A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' ->
rw_cells asegs m' A_ERRNO [C4 errv'] ->
( (r = 0 /\ errv' = Z_to_bv 64 ENOMEMv /\ HEAPAx A' LB LM FRS (charge B 0 M2D) m' md')
\/ (r <> 0 /\ (exists junk, rw_cells asegs m' r [CB 48 junk]) /\ HEAPAx A' LB ((r, 48) :: LM) FRS (charge B 0 M2D) m' md') ) ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 LC_GLOBAL_A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_DUPLOCALE) fc None m (seg_rom asegs)).

Definition newlocale_A_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo d : Z) (junk : list byte) (errv : word),
HEAPAx A LB LM FRS B m md -> In (d, 48) LM -> rw_cells asegs m d [CB 48 junk] ->
rw_cells asegs m LOCALE_LOCK_A [C4 (Z_to_bv 64 0)] ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 496 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 ->
(forall ms' m' (r : Z) (junk' : list byte),
ret_state A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (LB ++ lb_remove d LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' ->
rw_cells asegs m' d [CB 48 junk'] ->
rw_cells asegs m' LOCALE_LOCK_A [C4 (Z_to_bv 64 0)] ->
rw_cells asegs m' A_ERRNO [C4 errv] ->
HEAPAx A LB LM FRS B m' md ->
(r = d \/ r = 0) ->
AJ5 A4L HIx A T md ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 2) (Z_to_bv 64 CNAME_A) (Z_to_bv 64 d) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_NEWLOCALE) fc None m (seg_rom asegs)).

Definition freelocale_A_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo d n : Z) (errv : word),
HEAPAx A LB LM FRS B m md -> In (d, n) LM ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 - hl_stack A4H ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 ->
(forall ms' m' md' A' (r : word),
ret_state A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (LB ++ lb_remove d LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' ->
rw_cells asegs m' A_ERRNO [C4 errv] ->
HEAPAx A' LB (lb_remove d LM) FRS B m' md' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_FREELOCALE) fc None m (seg_rom asegs)).
End ALocaleStmt.

End RC__1.
End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek. Import QPZI.Mq4.
Import Q7UD Qhd4.
Import Qwm6.Mq0.
Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition put_costA (s : option jshape) (rc : Z) (BS : list blk) : Z :=
match s with None => 0 | Some _ => if rc =? 1 then 512 * Z.of_nat (length BS) else 0 end.

Section APutStmt.
Variable HIx : heap_iface_A A4L.
Variable put_entry : Z.
Variable put_stk : Z.

Definition put_postA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word)
(s : option jshape) (BS : list blk) (p rc : Z)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : word) (B' : bud),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv] /\
bB B - put_costA s rc BS <= bB B' /\ bD B <= bD B' /\
( ((s = None \/ rc = 1) /\ HEAPA A4L HIx A' LB LM FRS B' m' md')
\/ (exists s', s = Some s' /\ 2 <= rc /\ jval asegs A4F s' m' BS p (rc - 1) /\ HEAPA A4L HIx A' (BS ++ LB) LM FRS B' m' md') ).

Definition put_stmtA : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word)
(s : option jshape) (BS : list blk) (p rc : Z),
HEAPA A4L HIx A (BS ++ LB) LM FRS B m md ->
put_pre A4H A4F s m BS p rc ->
a0 = Z_to_bv 64 p ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - put_stk ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP ->
bv_unsigned ra mod 2 = 0 ->
put_costA s rc BS <= bB B ->
(forall ms' md' (A' : ASA A4L HIx),
put_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo errv s BS p rc ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 put_entry) fc None m (seg_rom asegs)).
End APutStmt.

Definition put_stk_A : Z := 112 + 64 + 96 + 96 + 4096.
Definition put_entry_A : Z := 0x9a78c.
Definition put_stmt_A (HIx : heap_iface_A A4L) : Prop := put_stmtA HIx put_entry_A put_stk_A.

End RC__1.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QHnV QCcH QfLs Qsw7 QJjn.
Import Q7UD Qwm6.Mq0.
Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Definition A_SNPRINTF_STUB : Z := 0x4f99c.
Definition A_FMT_LD : Z := 0x23700.
Definition A_FMT_LU : Z := 0x23720.
Definition A_FMT_U00CC : Z := 0x236a0.

Definition SNP_STACK_A : Z := 12256.

Definition SHJ (a : Z) : Z := a / 8 + A_SB.
Definition shadow_okJ (m : word -> option byte) (dst n : Z) : Prop :=
forall k, 0 <= k -> dst / 8 * 8 + 8 * k < dst + n ->
exists v, bytes_at asegs m (SHJ (dst / 8 * 8) + k) [Z_to_bv 8 v] /\ (v = 0 \/ (0 < v < 8 /\ dst + n <= dst / 8 * 8 + 8 * k + v)).
Definition rng_okJ (m : word -> option byte) (p n : Z) : Prop :=
0 <= p /\ p + n + 8 <= 2^47
/\ (0 < n -> shadow_okJ m p n)
/\ (64 < n -> (p + n + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= p) /\ n <= 2^43)
/\ (0 < n <= 64 -> (exists w : word, rw_cells asegs m (8 * (SHJ p / 8)) [C8 w])
/\ (exists w : word, rw_cells asegs m (8 * (SHJ (p + n - 1) / 8)) [C8 w])).

Definition dappJ (D dn : Z) : Prop := (0x645000 <= D /\ D + dn + 8 <= 0x7fff8000) \/ (0x10007fff8000 <= D /\ D + dn + 8 <= 2^47).

Definition isnp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(D : Z) (dn : nat) (junkd : list byte) (P : Z -> list byte -> Prop) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte) (r : Z) (o : list byte),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ frm0 fc'
/\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
/\ stk asegs m' lo (bv_unsigned sp)
/\ r = Z.of_nat (length o) /\ P r o
/\ rw_cells asegs m' D [CB dn (o ++ Z_to_bv 8 0 :: skipn (S (length o)) junkd)].

Section SnpStmts.
Variable PFRT : (word -> option byte) -> Prop.
Variable PFLO : Z.

Definition isnp_pre (sp a0 a1 : word) (fc : bv 32) (m : word -> option byte) (D n : Z) (dn : nat) (junkd : list byte) (need lo : Z) : Prop :=
a0 = Z_to_bv 64 D /\ a1 = Z_to_bv 64 n /\
rw_cells asegs m D [CB dn junkd] /\ PFRT m /\
need <= Z.of_nat dn /\ need <= n < 2^63 /\
stk asegs m lo (bv_unsigned sp) /\ lo <= bv_unsigned sp - SNP_STACK_A /\ PFLO <= lo /\ bv_unsigned sp + 16 <= 2^47 /\
mem_inv asegs m /\ frm0 fc /\
(D + Z.of_nat dn <= lo \/ bv_unsigned sp <= D) /\
dappJ D (Z.of_nat dn) /\ (forall k, 0 < k <= need -> rng_okJ m D k).

Definition isnprintf_l_stmt (afmt : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D n : Z) (dn : nat) (junkd : list byte) (lo : Z),
isnp_pre sp a0 a1 fc m D n dn junkd 21 lo -> a2 = Z_to_bv 64 afmt ->
evt asegs (isnp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd
(fun r o => 1 <= r <= 20 /\ ~ In (Z_to_bv 8 0) o) lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_SNPRINTF_STUB) fc None m (seg_rom asegs)).
Definition isnprintf_ld_stmt : Prop := isnprintf_l_stmt A_FMT_LD.
Definition isnprintf_lu_stmt : Prop := isnprintf_l_stmt A_FMT_LU.

Definition isnprintf_u00cc_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D n c1 c2 : Z) (dn : nat) (junkd : list byte) (lo : Z),
isnp_pre sp a0 a1 fc m D n dn junkd 7 lo -> a2 = Z_to_bv 64 A_FMT_U00CC ->
0 <= c1 < 256 -> a3 = Z_to_bv 64 c1 -> 0 <= c2 < 256 -> a4 = Z_to_bv 64 c2 ->
evt asegs (isnp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd
(fun r o => o = map (Z_to_bv 8) [92; 117; 48; 48; c1; c2]) lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_SNPRINTF_STUB) fc None m (seg_rom asegs)).
End SnpStmts.
End Mq6.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup.
Import QCcH QfLs QJjn.
Import Q7UD Qhd4.
Import Qwm6.Mq0.
Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition uw_at (hi : Z) (m : word -> option byte) (sp s0 : Z) (u : uwd) : Prop :=
match u with
| UWptr => s0 < alloc_ceiling \/ s0 mod 8 <> 0 \/ hi - 16 <= s0
| UWfp ra2 v2 => sp <= s0 - 16 /\ s0 mod 8 = 0 /\ s0 < hi - 16 /\
bytes_at asegs m (s0 - 16) (le8 (Z_to_bv 64 v2) ++ le8 (Z_to_bv 64 ra2)) /\
(v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= s0 \/ hi - 16 <= v2) /\
0 <= v2 < 2^64
| UWpaid => True
end.

Lemma uw_at_ptr : forall hi m sp s0, s0 < alloc_ceiling -> uw_at hi m sp s0 UWptr.
Proof. intros. cbn. left. assumption. Qed.

Lemma uw_at_paid : forall hi m sp s0, uw_at hi m sp s0 UWpaid.
Proof. intros. exact I. Qed.

Lemma uw_at_mono : forall hi m m' sp sp' s0 u W,
uw_at hi m sp s0 u -> munch W m m' -> Forall (fun iv => snd iv <= sp) W -> sp' <= sp ->
uw_at hi m' sp' s0 u.
Proof.
intros hi m m' sp sp' s0 u W UW MU HW Hsp. destruct u as [|ra2 v2|]; cbn in *; [exact UW | | exact I].
destruct UW as (H1 & H2 & H3 & HB & H5 & H6). split; [lia|]. split; [exact H2|]. split; [exact H3|]. split; [| split; [exact H5 | exact H6]].
eapply bytes_at_transport; [exact HB | exact MU |].
lazymatch goal with |- disjoint_from _ _ ?n => replace n with 16 by reflexivity end.
clear -HW H1. induction W as [|[lo' hi'] W IH]; cbn; [exact I|].
apply Forall_cons_iff in HW as [Hh HW]. cbn in Hh. split; [lia | apply IH; exact HW].
Qed.

Lemma uw_at_pre : forall hi m m' sp sp' s0 u W,
uw_at hi m sp s0 u -> munch W m m' -> Forall (fun iv => snd iv <= sp) W -> sp' <= sp ->
uw_pre A4L hi m' sp' s0 u.
Proof.
intros hi m m' sp sp' s0 u W UW MU HW Hsp.
pose proof (uw_at_mono hi m m' sp sp' s0 u W UW MU HW Hsp) as UW'.
destruct u as [|ra2 v2|]; cbn in *; [ | | exact I].
- destruct UW' as [H|[H|H]]; [left; exact H | right; left; exact H | right; right; exact H].
- destruct UW' as (H1 & H2 & H3 & HB & H5 & H6). split; [lia|]. split; [exact H2|]. split; [exact H3|]. split; [exact HB | split; [exact H5 | exact H6]].
Qed.

Lemma uw_at_heap_pres : forall hi m m' sp sp' s0 u LB,
uw_at hi m sp s0 u -> heap_pres A4H LB sp' m m' -> sp' <= sp -> uw_at hi m' sp s0 u.
Proof.
intros hi m m' sp sp' s0 u LB UW HPR Hsp. destruct u as [|ra2 v2|]; cbn in *; [exact UW | | exact I].
destruct UW as (H1 & H2 & H3 & HB & H5 & H6). split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [| split; [exact H5 | exact H6]].
eapply (heap_pres_bytes_at A4H); [exact HPR | exact HB | left; lia].
Qed.

Lemma uw_at_pre0 : forall hi m sp sp' s0 u, uw_at hi m sp s0 u -> sp' <= sp -> uw_pre A4L hi m sp' s0 u.
Proof.
intros hi m sp sp' s0 u UW Hsp. eapply (uw_at_pre hi m m sp sp' s0 u []); [exact UW | apply munch_refl | apply Forall_nil | exact Hsp].
Qed.
End RC__1.
End Mq7.
From Stdlib Require Permutation.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn.
Export Q7UD Qhd4 Qwm6.
Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Lemma ro_C8_of_bytes_at : forall segs m a v, bytes_at segs m a (le8 v) -> ro_cells segs m a [C8 v].
Proof. intros segs m a v H. split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact H]. Qed.

Lemma div8_add : forall p j, p mod 8 = 0 -> 0 <= j -> (p + j) / 8 = p / 8 + j / 8.
Proof. intros p j Hp Hj. Z.div_mod_to_equations. nia. Qed.

Lemma ro_cells_app : forall segs m A cs1 cs2,
ro_cells segs m A (cs1 ++ cs2) <-> ro_cells segs m A cs1 /\ ro_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
intros segs m A cs1 cs2. unfold ro_cells, cells_at.
rewrite cells_wf_app, cells_bytes_app, bytes_at_app.
split.
- intros ((W1 & W2) & (B1 & B2)). rewrite (cells_bytes_length cs1 W1) in B2. tauto.
- intros ((W1 & B1) & (W2 & B2)). rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section WithIface.
Variable L : heap_layout_A.
Variable HIx : heap_iface_A L.
Let segs := hl_segs L.

Lemma in_block_factsA : forall A LB LM FR B m md a n x,
HEAPA L HIx A LB LM FR B m md -> In (a, n) (LB ++ LM) -> a <= x < a + n ->
x < alloc_ceiling /\ ~ hl_client_static L x /\
forall a' n', In (a', n') (LB ++ LM) -> a' <> a -> ~ (a' <= x < a' + n').
Proof.
intros A LB LM FR B m md a n x HP Hb Hx.
pose proof (heapA_blk L HIx _ _ _ _ _ _ _ _ _ HP Hb) as (Hn & _ & _ & Hhi & _).
split; [lia|]. split.
- replace x with (a + (x - a)) by lia. eapply (heapA_blk_not_static L HIx); eauto. lia.
- intros a' n' Hb' Hne Hx'.
pose proof (heapA_blk_disjoint L HIx _ _ _ _ _ _ _ _ _ _ _ HP Hb Hb' ltac:(congruence)) as Hd.
pose proof (heapA_blk L HIx _ _ _ _ _ _ _ _ _ HP Hb') as (Hn' & _). lia.
Qed.

Lemma fr_size_pos : forall k, 0 <= k -> 0 < fr_size k.
Proof. intros k Hk. unfold fr_size. pose proof (Z.pow_pos_nonneg 2 k). lia. Qed.
Lemma fr_shadow_len_bnd : forall k, 0 <= k <= 3 -> 0 < fr_shadow_len k <= 64.
Proof.
intros k Hk. unfold fr_shadow_len. split; [pose proof (Z.pow_pos_nonneg 2 k); lia|].
apply (Z.le_trans _ (8 * 2^3)); [apply Z.mul_le_mono_nonneg_l; [lia | apply Z.pow_le_mono_r; lia] | cbn; lia].
Qed.
Lemma fr_size_2 : fr_size 2 = 256. Proof. reflexivity. Qed.

Lemma fr_size_shadow : forall k, 0 <= k -> fr_size k = 8 * fr_shadow_len k.
Proof. intros k Hk. unfold fr_size, fr_shadow_len. lia. Qed.

Lemma shadow_blk_apart : forall A LB LM FR B m md a n x k,
HEAPA L HIx A LB LM FR B m md -> In (a, n) (LB ++ LM) -> 0 <= x -> x < alloc_ceiling -> 0 <= k <= 2^20 ->
a + n <= shad L x \/ shad L x + k <= a.
Proof.
intros A LB LM FR B m md a n x k HP Hin Hx Hxc Hk.
pose proof (heapA_blk_appmem L HIx _ _ _ _ _ _ _ _ _ HP Hin) as AM. unfold shad.
pose proof alloc_ceiling_range. pose proof (hl_sb_range L). pose proof (heapA_blk L HIx _ _ _ _ _ _ _ _ _ HP Hin) as (Hn & _ & Ha0 & _).
destruct AM as [AM | AM]; [left | right]; Z.div_mod_to_equations; lia.
Qed.

Lemma in_fr_ivs : forall FR b, In b (fr_ivs L FR) -> exists F k, In (F, k) FR /\ (b = (F, fr_size k - 8) \/ b = (shad L F, fr_shadow_len k)).
Proof.
intros FR b H. unfold fr_ivs in H. apply in_flat_map in H as ([F k] & Hf & Hb). exists F, k. split; [exact Hf|].
cbn in Hb. destruct Hb as [<- | [<- | []]]; [left | right]; reflexivity.
Qed.
Lemma fr_ivs_frame : forall FR F k, In (F, k) FR -> In (F, fr_size k - 8) (fr_ivs L FR).
Proof. intros FR F k H. unfold fr_ivs. apply in_flat_map. exists (F, k). split; [exact H | left; reflexivity]. Qed.
Lemma fr_ivs_shadow : forall FR F k, In (F, k) FR -> In (shad L F, fr_shadow_len k) (fr_ivs L FR).
Proof. intros FR F k H. unfold fr_ivs. apply in_flat_map. exists (F, k). split; [exact H | right; left; reflexivity]. Qed.

Lemma blk_not_fr_iv : forall A LB LM FR B m md a n,
HEAPA L HIx A LB LM FR B m md -> In (a, n) (LB ++ LM) -> ~ In (a, n) (fr_ivs L FR).
Proof.
intros A LB LM FR B m md a n HP Hin Hf. apply in_fr_ivs in Hf as (F & k & HF & Hb).
pose proof (heapA_frame L HIx _ _ _ _ _ _ _ _ _ HP HF) as (Hk & _ & HF0 & HFc & _).
pose proof (fr_size_pos k ltac:(lia)) as Hsz.
assert (Hsz8 : 64 <= fr_size k) by (unfold fr_size; pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)); lia).
destruct Hb as [E | E]; injection E as E1 E2; subst a n.
- pose proof (heapA_frame_disjoint L HIx _ _ _ _ _ _ _ _ _ _ _ HP HF Hin). lia.
- pose proof alloc_ceiling_range. pose proof (fr_shadow_len_bnd k Hk).
assert (HF0' : 0 <= F) by lia. assert (HFc' : F < alloc_ceiling) by lia. assert (HSK : 0 <= fr_shadow_len k <= 2^20) by lia.
pose proof (shadow_blk_apart _ _ _ _ _ _ _ _ _ F (fr_shadow_len k) HP Hin HF0' HFc' HSK) as D.
pose proof (heapA_blk L HIx _ _ _ _ _ _ _ _ _ HP Hin) as (Hn & _). lia.
Qed.

Lemma not_in_app3 : forall (b : blk) (X Y F : list blk), ~ In b (X ++ Y) -> ~ In b F -> ~ In b (X ++ Y ++ F).
Proof.
intros b X Y F H1 H2 H. rewrite app_assoc in H. apply in_app_or in H as [H|H]; [exact (H1 H) | exact (H2 H)].
Qed.

Lemma frame_writes_okA : forall A LB LM FR B m m' md W,
HEAPA L HIx A LB LM FR B m md ->
munch W m m' ->
Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= hiA_top L HIx)
\/ (exists a n, In (a, n) (LB ++ LM) /\ a <= fst iv /\ snd iv <= a + n)
\/ (forall x, fst iv <= x < snd iv -> hl_scratch L x)) W ->
forall a, 0 <= a < 2^64 -> ~ client_addr L (LB ++ LM) alloc_ceiling a -> ~ hl_scratch L a ->
~ (exists F k, In (F, k) FR /\ (F <= a < F + fr_size k - 8 \/ shad L F <= a < shad L F + fr_shadow_len k)) ->
m' (wa a) = m (wa a).
Proof.
intros A LB LM FR B m m' md W HP MU HW a Ha Hnc Hns _.
apply MU. rewrite wa_unsigned by lia. clear MU.
induction W as [|[lo hi] W IH]; cbn; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. split; [| apply IH; exact HW]. cbn in H1.
intros Hin. destruct H1 as [H1 | [(b & n & Hb & Hlo & Hhi) | Hsc]].
- apply Hnc. left; lia.
- apply Hnc. right. right. exists (b, n). split; [exact Hb | cbn; lia].
- exact (Hns (Hsc a Hin)).
Qed.

Lemma frame_writes_okF : forall A LB LM FR B m m' md W,
HEAPA L HIx A LB LM FR B m md ->
munch W m m' ->
Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= hiA_top L HIx)
\/ (exists a n, In (a, n) (LB ++ LM) /\ a <= fst iv /\ snd iv <= a + n)
\/ (forall x, fst iv <= x < snd iv -> hl_scratch L x)
\/ (exists F k, In (F, k) FR /\ ((F <= fst iv /\ snd iv <= F + fr_size k - 8)
\/ (shad L F <= fst iv /\ snd iv <= shad L F + fr_shadow_len k)))) W ->
forall a, 0 <= a < 2^64 -> ~ client_addr L (LB ++ LM) alloc_ceiling a -> ~ hl_scratch L a ->
~ (exists F k, In (F, k) FR /\ (F <= a < F + fr_size k - 8 \/ shad L F <= a < shad L F + fr_shadow_len k)) ->
m' (wa a) = m (wa a).
Proof.
intros A LB LM FR B m m' md W HP MU HW a Ha Hnc Hns Hnf.
apply MU. rewrite wa_unsigned by lia. clear MU.
induction W as [|[lo hi] W IH]; cbn; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. split; [| apply IH; exact HW]. cbn in H1.
intros Hin. destruct H1 as [H1 | [(b & n & Hb & Hlo & Hhi) | [Hsc | (F & k & HF & HFr)]]].
- apply Hnc. left; lia.
- apply Hnc. right. right. exists (b, n). split; [exact Hb | cbn; lia].
- exact (Hns (Hsc a Hin)).
- apply Hnf. exists F, k. split; [exact HF | lia].
Qed.

Lemma client_outsideA : forall A LB LM FR B LB0 m md W SP,
HEAPA L HIx A LB LM FR B m md ->
(forall b, In b LB0 -> In b (LB ++ LM ++ fr_ivs L FR)) ->
alloc_ceiling <= SP ->
Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= SP)
\/ (exists a n, In (a, n) (LB ++ LM) /\ ~ In (a, n) LB0 /\ a <= fst iv /\ snd iv <= a + n)
\/ (forall x, fst iv <= x < snd iv -> hl_scratch L x)) W ->
forall a, 0 <= a < 2^64 -> client_addr L LB0 SP a -> outside W a.
Proof.
intros A LB LM FR B LB0 m md W SP HP Hsub HSP HW a Ha Hc. pose proof alloc_ceiling_range as ACR. pose proof (hl_sb_range L) as SBR.
induction W as [|[lo hi] W IH]; cbn; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. split; [| apply IH; exact HW]. cbn in H1.
destruct Hc as [Hc | [Hc | (b & Hb0 & Hbr)]].
- destruct H1 as [H1 | [(b & n & Hb & Hnb & Hlo & Hhi) | Hsc]]; [lia| |].
+ pose proof (heapA_blk L HIx _ _ _ _ _ _ _ _ _ HP Hb) as (_ & _ & _ & Hbhi & _). lia.
+ intros Hin. pose proof (hl_scratch_in_img L a (Hsc a Hin)). pose proof (hl_img_range L). lia.
- destruct H1 as [H1 | [(b & n & Hb & Hnb & Hlo & Hhi) | Hsc]].
+ intros Hin. pose proof (hl_static_in_img L a Hc). pose proof (hl_img_range L). lia.
+ intros Hin. destruct (in_block_factsA _ _ _ _ _ _ _ _ _ a HP Hb ltac:(lia)) as (_ & Hns & _). exact (Hns Hc).
+ intros Hin. exact (hl_scratch_not_static L a (Hsc a Hin) Hc).
- destruct b as [ba bn]. cbn in Hbr. pose proof (Hsub _ Hb0) as HbX.
rewrite app_assoc in HbX. apply in_app_or in HbX as [Hb | Hfr].
+ destruct H1 as [H1 | [(b & n & Hb' & Hnb & Hlo & Hhi) | Hsc]].
* pose proof (heapA_blk L HIx _ _ _ _ _ _ _ _ _ HP Hb) as (_ & _ & _ & Hbhi & _). lia.
* intros Hin. assert (Hne : b <> ba).
{ intros ->. apply Hnb. rewrite (nodup_addr_size (LB ++ LM) ba n bn (heapA_blk_nodup L HIx _ _ _ _ _ _ _ HP) Hb' Hb). exact Hb0. }
destruct (in_block_factsA _ _ _ _ _ _ _ _ _ a HP Hb' ltac:(lia)) as (_ & _ & Hdis).
exact (Hdis ba bn Hb ltac:(congruence) ltac:(lia)).
* intros Hin. pose proof (heapA_blk_img L HIx _ _ _ _ _ _ _ _ _ HP Hb) as Himg.
pose proof (hl_scratch_in_img L a (Hsc a Hin)). lia.
+ apply in_fr_ivs in Hfr as (G & kg & HG & [E | E]); injection E as -> ->.
*
pose proof (heapA_frame L HIx _ _ _ _ _ _ _ _ _ HP HG) as (Hkg & _ & HG0 & HGc & HGimg & _).
destruct H1 as [H1 | [(b & n & Hb' & Hnb & Hlo & Hhi) | Hsc]].
-- lia.
-- intros Hin. pose proof (heapA_frame_disjoint L HIx _ _ _ _ _ _ _ _ _ _ _ HP HG Hb'). lia.
-- intros Hin. pose proof (hl_scratch_in_img L a (Hsc a Hin)). lia.
*
pose proof (heapA_frame L HIx _ _ _ _ _ _ _ _ _ HP HG) as (Hkg & _ & HG0 & HGc & HGimg & _).
assert (HI : 0 <= a - shad L G < fr_shadow_len kg) by lia.
pose proof (heapA_frame_shadow_sep L HIx _ _ _ _ _ _ _ _ _ (a - shad L G) HP HG HI) as [Hnc Himg].
replace (shad L G + (a - shad L G)) with a in Hnc, Himg by lia.
destruct H1 as [H1 | [(b & n & Hb' & Hnb & Hlo & Hhi) | Hsc]].
-- intros Hin. apply Hnc. left. lia.
-- intros Hin. apply Hnc. right. right. exists (b, n). split; [exact Hb' | cbn; lia].
-- intros Hin. pose proof (hl_scratch_in_img L a (Hsc a Hin)). lia.
Qed.

Lemma fresh_not_inA : forall A LB LM FR B m md r n k,
HEAPA L HIx A ((r, n) :: LB) LM FR B m md -> ~ In (r, k) (LB ++ LM).
Proof.
intros A LB LM FR B m md r n k HP Hin.
pose proof (heapA_blk_nodup L HIx _ _ _ _ _ _ _ HP) as ND. cbn in ND. inversion ND as [|x l Hni Hnd]; subst.
apply Hni. exact (in_map blk_addr _ _ Hin).
Qed.

Lemma sb_cellsA : forall A LB LM FR B m md, HEAPA L HIx A LB LM FR B m md ->
ro_cells segs m (hl_got_sb L) [C8 (Z_to_bv 64 (hl_sb_cell L))] /\ ro_cells segs m (hl_sb_cell L) [C8 (Z_to_bv 64 (hl_sb L))].
Proof.
intros A LB LM FR B m md HP. destruct (heapA_sb_cells L HIx _ _ _ _ _ _ _ HP) as (H1 & H2 & _ & _).
split; apply ro_C8_of_bytes_at; assumption.
Qed.

Lemma shad_sepA : forall A LB LM FR B m md a n i b k,
HEAPA L HIx A LB LM FR B m md -> In (a, n) LB -> 0 <= i < (n + 7) / 8 -> In (b, k) (LB ++ LM) ->
a / 8 + hl_sb L + i < alloc_ceiling /\ (a / 8 + hl_sb L + i < b \/ b + k <= a / 8 + hl_sb L + i)
/\ (a / 8 + hl_sb L + i < hl_img_lo L \/ hl_img_hi L <= a / 8 + hl_sb L + i).
Proof.
intros A LB LM FR B m md a n i b k HP Hin Hi Hb.
destruct (heapA_shadow_sep L HIx _ _ _ _ _ _ _ a n i HP Hin Hi) as [Hnc Himg].
unfold shad in Hnc, Himg. unfold client_addr, in_block in Hnc.
split; [| split; [| exact Himg]].
- destruct (Z.lt_ge_cases (a / 8 + hl_sb L + i) alloc_ceiling) as [?|Hge]; [assumption|]. exfalso. apply Hnc. left. lia.
- destruct (Z.lt_ge_cases (a / 8 + hl_sb L + i) b) as [?|Hge]; [left; assumption|].
destruct (Z.lt_ge_cases (a / 8 + hl_sb L + i) (b + k)) as [Hlt|?]; [| right; lia].
exfalso. apply Hnc. right. right. exists (b, k). split; [exact Hb | cbn; lia].
Qed.
End WithIface.
End RC__1.

Ltac in_app_prefix := first [ assumption | apply in_or_app; left; first [ assumption | in_prefix ] | apply in_or_app; right; first [ assumption | in_prefix ] | in_prefix ].

Ltac blk_factsA L HIx HP a n Hal Hlo Hhi Himg :=
let Hin := fresh "Hin" in let X := fresh in
lazymatch type of HP with HEAPA _ _ _ ?LB ?LM _ _ _ _ =>
assert (Hin : In (a, n) (LB ++ LM)) by in_app_prefix end;
pose proof (heapA_blk L HIx _ _ _ _ _ _ _ _ _ HP Hin) as X;
destruct X as (_ & Hal & Hlo & Hhi & _);
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi;
pose proof (heapA_blk_img L HIx _ _ _ _ _ _ _ _ _ HP Hin) as Himg;
clear Hin.

Ltac try_blocksA LBc tac :=
lazymatch LBc with
| (?a, ?n) :: ?r => first [ exists a, n; tac | try_blocksA r tac ]
| _ => fail
end.

Ltac solve_frameW_withA HPc :=
repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd];
first [ left; split; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia
| right; left;
lazymatch type of HPc with HEAPA _ _ _ ?LBc ?LMc _ _ _ _ =>
first [ try_blocksA LBc ltac:(split; [ in_app_prefix | lia ]) | try_blocksA LMc ltac:(split; [ in_app_prefix | lia ])
|
match goal with Hb : In (?a, ?n) _ |- _ => exists a, n; split; [ in_app_prefix | lia ] end ]
end
| right; right; intros; simpl hl_scratch; lia ].

Ltac heap_nowA L HIx HP MU WM MI :=
eapply (heapA_client_frame L HIx); [ exact HP | eapply (frame_writes_okA L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | exact MI ].

Ltac alloc_sideA_with lay :=
rewrite ?unsigned_lit by lia;
lazymatch goal with
| |- forall _ : machine_state, _ => idtac
| |- uw_pre _ _ _ _ _ _ /\ uw_ok _ _ _ _ => split; alloc_sideA_with lay
| |- _ =>
cbn [uw_pre uw_ok uw_key uw_cost bB bD bM charge chargeM]; lay; rewrite ?unsigned_lit by lia;
lazymatch goal with
| |- _ -> _ /\ _ => intros _; split; alloc_sideA_with lay
| |- True => exact I
| |- _ \/ _ =>
first [ left; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia | solve [ in_prefix ] | idtac ]
| |- In _ _ => first [ solve [ in_prefix ] | idtac ]
| |- stk _ _ _ _ => eassumption
| |- rw_cells _ _ _ _ => eassumption
| |- @eq (bv _) _ _ => first [ reflexivity | eassumption | symmetry; eassumption | apply bv_eq; rewrite ?unsigned_lit by lia; lia ]
| |- _ mod 16 = 0 =>
first [ assumption
| match goal with H : bv_unsigned ?sp mod 16 = 0 |- (bv_unsigned ?sp + ?k) mod 16 = 0 =>
rewrite <- Zplus_mod_idemp_l, H; reflexivity end
| lia ]
| |- _ => first [ lia
| unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia
| destruct (Z.eqb _ 0); lia
| idtac ]
end end.

Ltac alloc_sideA := alloc_sideA_with ltac:(idtac).

Tactic Notation "alloc_callA" uconstr(SPEC) constr(L) constr(HIx) constr(HP) constr(MU) constr(WM) constr(MI) :=
evt_done5; eapply SPEC; [ heap_nowA L HIx HP MU WM MI | .. ].

Tactic Notation "alloc_callA" uconstr(SPEC) "uw" constr(U) constr(L) constr(HIx) constr(HP) constr(MU) constr(WM) constr(MI) :=
evt_done5; eapply SPEC with (u := U); [ heap_nowA L HIx HP MU WM MI | .. ].

Tactic Notation "alloc_callA" uconstr(SPEC) "blk" constr(P) "uw" constr(U) constr(L) constr(HIx) constr(HP) constr(MU) constr(WM) constr(MI) :=
evt_done5; eapply SPEC with (p := P) (u := U); [ heap_nowA L HIx HP MU WM MI | .. ].

Ltac prefix_ofA LBc LB0 :=
lazymatch LBc with
| LB0 => constr:(@nil blk)
| ?x :: ?r => let p := prefix_ofA r LB0 in constr:(x :: p)
end.

Ltac not_in_old_coreA L HIx HPc :=
lazymatch goal with |- ~ In (?a, ?k) (?LB0 ++ ?LM) =>
lazymatch type of HPc with HEAPA _ _ _ ?LBc _ _ _ _ _ =>
let P := prefix_ofA LBc LB0 in
eapply (nodup_prefix_suffix P (LB0 ++ LM) a _ k);
[ rewrite app_assoc; change (P ++ LB0) with LBc; exact (heapA_blk_nodup L HIx _ _ _ _ _ _ _ HPc) | in_prefix ]
end
end.

Ltac in_subA Hb :=
first [ exact Hb
| apply in_or_app; right; in_subA Hb | apply in_or_app; left; in_subA Hb | right; in_subA Hb
| lazymatch type of Hb with
| In _ (_ :: _) => destruct Hb as [<- | Hb]; [left; reflexivity | in_subA Hb]
| In _ (_ ++ _) => apply in_app_or in Hb; destruct Hb as [Hb | Hb]; in_subA Hb
| In _ [] => destruct Hb
end ].

Ltac strip_frA Lst :=
lazymatch Lst with
| ?X ++ fr_ivs _ _ => X
| ?X ++ ?Y => let Y' := strip_frA Y in constr:(X ++ Y')
end.

Ltac not_in_oldA L HIx HPc :=
lazymatch goal with
| |- ~ In (?a, ?k) ?Lst =>
lazymatch Lst with
| context [fr_ivs _ _] =>
let Core := strip_frA Lst in
let Hn := fresh "Hn" in
assert (Hn : ~ In (a, k) Core) by not_in_old_coreA L HIx HPc;
let H := fresh "Hi" in intro H;
repeat (apply in_app_or in H; destruct H as [H|H]);
first [ refine (blk_not_fr_iv L HIx _ _ _ _ _ _ _ _ _ HPc _ H); solve [in_app_prefix]
| apply Hn; solve [in_subA H] ]
| _ => not_in_old_coreA L HIx HPc
end
end.

Ltac solve_clientWA L HIx HPc :=
repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd];
first [ left; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia
| right; left;
lazymatch type of HPc with HEAPA _ _ _ ?LBc _ _ _ _ _ =>
try_blocksA LBc ltac:(split; [ in_app_prefix | split; [ not_in_oldA L HIx HPc | lia ] ])
end
| right; right; intros; simpl hl_scratch; lia ].

Ltac in_tailA Hb :=
let H := fresh in
pose proof Hb as H; apply in_app_or in H; apply in_or_app;
destruct H as [H|H]; [ left; cbn [In app]; repeat (first [ exact H | right ]) | right; exact H ].

Ltac extend_presA L HIx HPR MU WM HPc HPR2 :=
lazymatch type of HPR with heap_pres _ ?LB0LM ?SP ?me ?m0 =>
lazymatch type of HPR2 with heap_pres _ _ _ _ ?m2 =>
let H := fresh "HPRx" in
assert (H : heap_pres L LB0LM SP me m2);
[ eapply heap_pres_trans; [ exact HPR |];
eapply heap_pres_trans;
[ eapply (heap_pres_of_munch L LB0LM SP); [ exact MU | exact WM |];
eapply (client_outsideA _ HIx); [ exact HPc | let Hb := fresh in intros ? Hb; first [ solve [in_tailA Hb] | cbn; tauto ]
| unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia | solve_clientWA L HIx HPc ]
| eapply heap_pres_weaken; [ exact HPR2 | lia | let Hb := fresh in intros ? Hb; first [ solve [in_tailA Hb] | cbn; tauto ] ] ]
| clear HPR; rename H into HPR ]
end end.

Ltac reenterA SEGS L HIx WX HP :=
aj5_enter; change (hl_segs L) with SEGS;
try lazymatch goal with
| |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
end.

Ltac shadow_nowA L HIx HP a n SH :=
let Hin := fresh "Hin" in
lazymatch type of HP with HEAPA _ _ _ ?LB _ _ _ _ _ => assert (Hin : In (a, n) LB) by in_prefix end;
pose proof (heapA_shadow_blk L HIx _ _ _ _ _ _ _ _ _ HP Hin) as SH; clear Hin;
unfold shad in SH; apply shadow_ro_cells in SH;
lazymatch type of SH with ro_cells _ _ _ (shadow_cells ?n) =>
let cs := eval cbv in (shadow_cells n) in change (shadow_cells n) with cs in SH
end.

Ltac heap_nowA_auto L HIx HPx H :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch type of HPx with HEAPA _ _ ?Ax ?LBx ?LMx ?FRx ?Bx ?mb ?mdx =>
match goal with MUc : munch _ mb mc, WMc : wmono _ mb mc, MIc : mem_inv _ mc |- _ =>
assert (H : HEAPA L HIx Ax LBx LMx FRx Bx mc mdx);
[ eapply (heapA_client_frame L HIx);
[ exact HPx | eapply (frame_writes_okA L HIx _ _ _ _ _ _ _ _ _ HPx MUc); solve_frameW_withA HPx | exact WMc | exact MIc ] | ]
end end end.

Ltac shadow_inA L HIx HP Hin SH :=
pose proof (heapA_shadow_blk L HIx _ _ _ _ _ _ _ _ _ HP Hin) as SH;
unfold shad in SH; apply shadow_ro_cells in SH;
lazymatch type of SH with ro_cells _ _ _ (shadow_cells ?n) =>
let cs := eval cbv in (shadow_cells n) in change (shadow_cells n) with cs in SH
end.

Ltac asan_chkA :=
step; step; sh_norm;
repeat match goal with
| |- context [ (?p + ?j) / 8 ] => is_Zlit j; rewrite (div8_add p j) by lia; let k := eval vm_compute in (Z.div j 8) in change (j / 8) with k
end;
step; step; first [ if_false | if_true ]; rewrite ?sxb_zero, ?zxb_zero.
End Mq8.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi QUZl Q7S0 QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq9.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import QZAi.Mq1 QZAi.Mq2 QUZl Q7S0.Mq0.
Import QytA.
Import Q6q3.
Import ListNotations. Open Scope Z_scope.
#[global] Transparent gmap_empty.

Ltac head_of t := lazymatch t with ?f _ => head_of f | _ => t end.

Ltac wh t := eval lazy head beta iota delta -[
sbind eruns follow
queue free_meta activate_group get_meta get_nominal_size enframe_read_off enframe_full am_take am_carve am_finish am_after_brk
alloc_meta ta_fin try_avail ag_tail alloc_group alloc_slot malloc_small_ctrl malloc_core malloc rd8 rd16 rd32
brk0_answer_ok brk_answer_ok mmap_answer_ok mmap_fixed_answer_ok munmap_answer_ok mprotect_answer_ok peek_answer_ok mremap_answer_ok
brk_pages_ok is_err round_up_pg ] in t.

Ltac unf_head t := let h := head_of t in eval lazy head beta iota delta [h FUEL] in t.

Ltac flat a := eval lazy beta iota zeta delta -[
brk0_answer_ok brk_answer_ok mmap_answer_ok mmap_fixed_answer_ok munmap_answer_ok mprotect_answer_ok peek_answer_ok mremap_answer_ok
brk_pages_ok is_err ] in a.

Ltac flat_args t := lazymatch t with
| @alloc_meta ?RC ?R ?st ?k ?b => let st' := flat st in constr:(@alloc_meta RC R st' k b)
| @am_take ?R ?st ?k ?b => let st' := flat st in constr:(@am_take R st' k b)
| @am_carve ?R ?st ?p ?k ?b => let st' := flat st in let p' := flat p in constr:(@am_carve R st' p' k b)
| @am_finish ?R ?st ?nu ?k ?b => let st' := flat st in let nu' := flat nu in constr:(@am_finish R st' nu' k b)
| @am_after_brk ?RC ?R ?st ?nu ?k ?b => let st' := flat st in let nu' := flat nu in constr:(@am_after_brk RC R st' nu' k b)
| @try_avail ?R ?sc ?st ?k ?b => let st' := flat st in let sc' := flat sc in constr:(@try_avail R sc' st' k b)
| @ta_fin ?R ?st ?m ?mask ?k => let st' := flat st in let m' := flat m in let mask' := flat mask in constr:(@ta_fin R st' m' mask' k)
| @alloc_group ?RC ?R ?lay ?rc ?st ?sc ?req ?k ?b => let st' := flat st in let sc' := flat sc in let req' := flat req in constr:(@alloc_group RC R lay rc st' sc' req' k b)
| @alloc_slot ?RC ?R ?lay ?fu ?st ?sc ?req ?k ?b => let st' := flat st in let sc' := flat sc in let req' := flat req in constr:(@alloc_slot RC R lay fu st' sc' req' k b)
| @ag_tail ?R ?lay ?st ?sc ?m ?p ?cnt ?ai ?k =>
let st' := flat st in let sc' := flat sc in let m' := flat m in let p' := flat p in let cnt' := flat cnt in let ai' := flat ai in
constr:(@ag_tail R lay st' sc' m' p' cnt' ai' k)
| @queue ?R ?h ?m ?st ?k ?b => let st' := flat st in let h' := flat h in let m' := flat m in constr:(@queue R h' m' st' k b)
| @free_meta ?R ?m ?st ?k ?b => let st' := flat st in let m' := flat m in constr:(@free_meta R m' st' k b)
| @activate_group ?R ?m ?st ?k ?b => let st' := flat st in let m' := flat m in constr:(@activate_group R m' st' k b)
| @get_meta ?R ?st ?p ?k ?b => let st' := flat st in let p' := flat p in constr:(@get_meta R st' p' k b)
| @enframe_full ?R ?st ?g ?idx ?n ?ctr ?k =>
let st' := flat st in let g' := flat g in let idx' := flat idx in let n' := flat n in let ctr' := flat ctr in
constr:(@enframe_full R st' g' idx' n' ctr' k)
| @enframe_read_off ?R ?st ?g ?idx ?n ?ctr ?k =>
let st' := flat st in let g' := flat g in let idx' := flat idx in let n' := flat n in let ctr' := flat ctr in
constr:(@enframe_read_off R st' g' idx' n' ctr' k)
| @malloc_small_ctrl ?RC ?R ?lay ?st ?n ?k ?b => let st' := flat st in let n' := flat n in constr:(@malloc_small_ctrl RC R lay st' n' k b)
| @malloc_core ?RC ?lay ?st ?n => let st' := flat st in let n' := flat n in constr:(@malloc_core RC lay st' n')
| @rd8 ?R ?st ?p ?k => let st' := flat st in let p' := flat p in constr:(@rd8 R st' p' k)
| @rd16 ?R ?st ?p ?k => let st' := flat st in let p' := flat p in constr:(@rd16 R st' p' k)
| @rd32 ?R ?st ?p ?k => let st' := flat st in let p' := flat p in constr:(@rd32 R st' p' k)
| _ => t
end.

Ltac focus_set T' := lazymatch goal with
| |- follow (eruns ?s ?u ?o (sbind ?T ?F)) ?ans = ?r => change_no_check (follow (eruns s u o (sbind T' F)) ans = r)
| |- follow (eruns ?s ?u ?o ?T) ?ans = ?r => change_no_check (follow (eruns s u o T') ans = r)
end.
Ltac focus_get := lazymatch goal with
| |- follow (eruns ?s ?u ?o (sbind ?T ?F)) ?ans = ?r => T
| |- follow (eruns ?s ?u ?o ?T) ?ans = ?r => T
end.

Ltac mname st := lazymatch st with
| mkState _ _ _ _ _ _ _ _ _ _ _ => let n := fresh "st" in set (n := st)
| _ => idtac
end.

Lemma abs_k {A} (k : A) (P : A -> Prop) : (forall K, K = k -> P K) -> P k.
Proof. intros H. exact (H k eq_refl). Qed.
Ltac mabs k := tryif is_var k then idtac else
(let K := fresh "K" in let EK := fresh "EK" in pattern k; refine (abs_k k _ _); intros K EK; cbv beta).
Ltac mabs_args := let T := focus_get in lazymatch T with
| @alloc_meta ?RC ?R ?st ?k ?b => mname st; mabs k; mabs b
| @am_take ?R ?st ?k ?b => mname st; mabs k; mabs b
| @am_carve ?R ?st ?p ?k ?b => mname st; mabs k; mabs b
| @am_finish ?R ?st ?nu ?k ?b => mname st; mabs k; mabs b
| @am_after_brk ?RC ?R ?st ?nu ?k ?b => mname st; mabs k; mabs b
| @try_avail ?R ?sc ?st ?k ?b => mname st; mabs k; mabs b
| @ta_fin ?R ?st ?m ?mask ?k => mname st; mabs k
| @alloc_group ?RC ?R ?lay ?rc ?st ?sc ?req ?k ?b => mname st; mabs k; mabs b
| @alloc_slot ?RC ?R ?lay ?fu ?st ?sc ?req ?k ?b => mname st; mabs k; mabs b
| @ag_tail ?R ?lay ?st ?sc ?m ?p ?cnt ?ai ?k => mname st; mabs k
| @queue ?R ?h ?m ?st ?k ?b => mname st; mabs k; mabs b
| @free_meta ?R ?m ?st ?k ?b => mname st; mabs k; mabs b
| @activate_group ?R ?m ?st ?k ?b => mname st; mabs k; mabs b
| @get_meta ?R ?st ?p ?k ?b => mname st; mabs k; mabs b
| @enframe_full ?R ?st ?g ?idx ?n ?ctr ?k => mname st; mabs k
| @enframe_read_off ?R ?st ?g ?idx ?n ?ctr ?k => mname st; mabs k
| @malloc_small_ctrl ?RC ?R ?lay ?st ?n ?k ?b => mname st; mabs k; mabs b
| @rd8 ?R ?st ?p ?k => mname st; mabs k
| @rd16 ?R ?st ?p ?k => mname st; mabs k
| @rd32 ?R ?st ?p ?k => mname st; mabs k
| _ => idtac
end.

Section FL.
Context {RC__ : RunConsts} {O : Type} (s : O -> ev -> option Z) (u : O -> ev -> Z -> O) (o : O).
Lemma fl_eq_sb {R S} (F : R -> M S) (T T' : M R) ans r : T = T' ->
follow (eruns s u o (sbind T' F)) ans = r -> follow (eruns s u o (sbind T F)) ans = r.
Proof. intros ->. exact (fun H => H). Qed.
Lemma fl_eq {R} (T T' : M R) ans r : T = T' -> follow (eruns s u o T') ans = r -> follow (eruns s u o T) ans = r.
Proof. intros ->. exact (fun H => H). Qed.
Lemma fl_ifn_true_sb {R S} (F : R -> M S) c (A B : M R) ans r : c = true ->
follow (eruns s u o (sbind B F)) ans = r -> follow (eruns s u o (sbind (if (if c then false else true) then A else B) F)) ans = r.
Proof. intros ->. exact (fun H => H). Qed.
Lemma fl_ifn_false_sb {R S} (F : R -> M S) c (A B : M R) ans r : c = false ->
follow (eruns s u o (sbind A F)) ans = r -> follow (eruns s u o (sbind (if (if c then false else true) then A else B) F)) ans = r.
Proof. intros ->. exact (fun H => H). Qed.
Lemma fl_ifnb_true_sb {R S} (F : R -> M S) c (A B : M R) ans r : c = true ->
follow (eruns s u o (sbind B F)) ans = r -> follow (eruns s u o (sbind (if negb c then A else B) F)) ans = r.
Proof. intros ->. exact (fun H => H). Qed.
Lemma fl_ifnb_false_sb {R S} (F : R -> M S) c (A B : M R) ans r : c = false ->
follow (eruns s u o (sbind A F)) ans = r -> follow (eruns s u o (sbind (if negb c then A else B) F)) ans = r.
Proof. intros ->. exact (fun H => H). Qed.
Lemma fl_if_true_sb {R S} (F : R -> M S) c (A B : M R) ans r : c = true ->
follow (eruns s u o (sbind A F)) ans = r -> follow (eruns s u o (sbind (if c then A else B) F)) ans = r.
Proof. intros ->. exact (fun H => H). Qed.
Lemma fl_if_false_sb {R S} (F : R -> M S) c (A B : M R) ans r : c = false ->
follow (eruns s u o (sbind B F)) ans = r -> follow (eruns s u o (sbind (if c then A else B) F)) ans = r.
Proof. intros ->. exact (fun H => H). Qed.
Lemma fl_ifn_true {R} c (A B : M R) ans r : c = true ->
follow (eruns s u o B) ans = r -> follow (eruns s u o (if (if c then false else true) then A else B)) ans = r.
Proof. intros ->. exact (fun H => H). Qed.
Lemma fl_ifn_false {R} c (A B : M R) ans r : c = false ->
follow (eruns s u o A) ans = r -> follow (eruns s u o (if (if c then false else true) then A else B)) ans = r.
Proof. intros ->. exact (fun H => H). Qed.
Lemma fl_ifnb_true {R} c (A B : M R) ans r : c = true ->
follow (eruns s u o B) ans = r -> follow (eruns s u o (if negb c then A else B)) ans = r.
Proof. intros ->. exact (fun H => H). Qed.
Lemma fl_ifnb_false {R} c (A B : M R) ans r : c = false ->
follow (eruns s u o A) ans = r -> follow (eruns s u o (if negb c then A else B)) ans = r.
Proof. intros ->. exact (fun H => H). Qed.
Lemma fl_if_true {R} c (A B : M R) ans r : c = true ->
follow (eruns s u o A) ans = r -> follow (eruns s u o (if c then A else B)) ans = r.
Proof. intros ->. exact (fun H => H). Qed.
Lemma fl_if_false {R} c (A B : M R) ans r : c = false ->
follow (eruns s u o B) ans = r -> follow (eruns s u o (if c then A else B)) ans = r.
Proof. intros ->. exact (fun H => H). Qed.
End FL.

Ltac focus_rew T T' pf := lazymatch goal with
| |- follow (eruns ?s ?u ?o (sbind _ ?F)) ?ans = ?r => refine (fl_eq_sb s u o F T T' ans r pf _)
| |- follow (eruns ?s ?u ?o _) ?ans = ?r => refine (fl_eq s u o T T' ans r pf _)
end.

Ltac mret_unfold := let T := focus_get in
lazymatch T with
| ?K ?x ?y => lazymatch goal with EK : K = ?L |- _ => focus_rew (K x y) (L x y) (f_equal (fun k => k x y) EK); let T' := eval cbv beta in (L x y) in focus_set T' end
| ?K ?x => lazymatch goal with EK : K = ?L |- _ => focus_rew (K x) (L x) (f_equal (fun k => k x) EK); let T' := eval cbv beta in (L x) in focus_set T' end
| ?K => lazymatch goal with EK : K = ?L |- _ => focus_rew K L EK end
end.
Ltac mret := let T := focus_get in
lazymatch T with
| ?K ?x ?y => is_var K; let x' := flat x in let y' := flat y in focus_set (K x' y'); mname x'; mname y'; mret_unfold
| ?K ?x => is_var K; let x' := flat x in focus_set (K x'); mname x'; mret_unfold
| ?K => is_var K; mret_unfold
end.

Ltac mlet := let T := focus_get in
lazymatch T with
| (let x := ?V in @?B x) =>
lazymatch V with
| (fun _ => _) => let T' := eval cbv beta in (B V) in focus_set T'
| _ => let V' := flat V in
lazymatch V' with
| mkState _ _ _ _ _ _ _ _ _ _ _ => let n := fresh "st" in pose (n := V'); let T' := eval cbv beta in (B n) in focus_set T'
| _ => let T' := eval cbv beta in (B V') in focus_set T'
end
end
end.

Ltac mscrut := let T := focus_get in
lazymatch T with
| (if ?c then ?A else ?B) =>
let c' := flat c in lazymatch c' with true => focus_set A | false => focus_set B end
| (let '(a, b) := ?X in @?B a b) =>
let X' := flat X in lazymatch X' with (?v, ?w) => let T' := eval cbv beta in (B v w) in focus_set T' end
| (match ?X with Some y => @?S y | None => ?N end) =>
let X' := flat X in lazymatch X' with Some ?v => let T' := eval cbv beta in (S v) in focus_set T' | None => focus_set N end
| (match ?X with Known v => @?A v | Unknown h => @?B h end) =>
let X' := flat X in lazymatch X' with Known ?v => let T' := eval cbv beta in (A v) in focus_set T' | Unknown ?w => let T' := eval cbv beta in (B w) in focus_set T' end
| (match ?X with BrkUntried => ?A | BrkDead => ?B | BrkLive rid off => @?C rid off end) =>
let X' := flat X in lazymatch X' with BrkUntried => focus_set A | BrkDead => focus_set B | BrkLive ?v ?w => let T' := eval cbv beta in (C v w) in focus_set T' end
end.

Ltac menter := let T := focus_get in let T1 := unf_head T in let T3 := flat_args T1 in focus_set T3; mabs_args.
Ltac mwh := let T := focus_get in let T2 := wh T in
tryif constr_eq T T2 then fail "mwh: no progress" else (let T3 := flat_args T2 in focus_set T3; mabs_args).

Ltac mfeed := lazymatch goal with
| |- follow (eruns ?s ?u ?o (sbind (SVis ?e ?k) ?F)) ?ans = ?r =>
let e' := eval lazy head beta iota zeta delta in e in
lazymatch e' with
| EPeek ?p ?c ?h => change_no_check (follow (eruns s u o (sbind (k 0) F)) ans = r)
| EUndef _ => fail "EUndef reached"
| _ => lazymatch ans with ?a :: ?ans' => change_no_check (follow (eruns s u o (sbind (k a) F)) ans' = r) end
end;
let T := focus_get in let T' := eval cbv beta in T in focus_set T'
| |- follow (eruns ?s ?u ?o (SVis ?e ?k)) ?ans = ?r =>
let e' := eval lazy head beta iota zeta delta in e in
lazymatch e' with
| EPeek ?p ?c ?h => change_no_check (follow (eruns s u o (k 0)) ans = r)
| EUndef _ => fail "EUndef reached"
| _ => lazymatch ans with ?a :: ?ans' => change_no_check (follow (eruns s u o (k a)) ans' = r) end
end;
let T := focus_get in let T' := eval cbv beta in T in focus_set T'
| |- follow (eruns ?s ?u ?o (sbind (SRet ?x) ?F)) ?ans = ?r =>
let x' := flat x in let T' := eval cbv beta in (F x') in change_no_check (follow (eruns s u o T') ans = r)
end.

Ltac mchk H := lazymatch goal with
| |- follow (eruns ?s ?u ?o (sbind (if (if ?c then false else true) then ?A else ?B) ?F)) ?ans = ?r =>
first [ refine (fl_ifn_true_sb s u o F c A B ans r H _) | refine (fl_ifn_false_sb s u o F c A B ans r H _) ]
| |- follow (eruns ?s ?u ?o (sbind (if negb ?c then ?A else ?B) ?F)) ?ans = ?r =>
first [ refine (fl_ifnb_true_sb s u o F c A B ans r H _) | refine (fl_ifnb_false_sb s u o F c A B ans r H _) ]
| |- follow (eruns ?s ?u ?o (sbind (if ?c then ?A else ?B) ?F)) ?ans = ?r =>
first [ refine (fl_if_true_sb s u o F c A B ans r H _) | refine (fl_if_false_sb s u o F c A B ans r H _) ]
| |- follow (eruns ?s ?u ?o (if (if ?c then false else true) then ?A else ?B)) ?ans = ?r =>
first [ refine (fl_ifn_true s u o c A B ans r H _) | refine (fl_ifn_false s u o c A B ans r H _) ]
| |- follow (eruns ?s ?u ?o (if negb ?c then ?A else ?B)) ?ans = ?r =>
first [ refine (fl_ifnb_true s u o c A B ans r H _) | refine (fl_ifnb_false s u o c A B ans r H _) ]
| |- follow (eruns ?s ?u ?o (if ?c then ?A else ?B)) ?ans = ?r =>
first [ refine (fl_if_true s u o c A B ans r H _) | refine (fl_if_false s u o c A B ans r H _) ]
end.
Ltac mcond := let T := focus_get in
lazymatch T with
| (if (if ?c then false else true) then ?A else ?B) => idtac "STUCK (negated):" c
| (if negb ?c then ?A else ?B) => idtac "STUCK (negb):" c
| (if ?c then ?A else ?B) => idtac "STUCK:" c
| _ => let h := head_of T in tryif is_const h then idtac "HEAD:" h else (tryif is_constructor h then idtac "HEAD (constructor):" h else (tryif is_var h then idtac "HEAD (var):" h else idtac "HEAD: <non-constant>"))
end.
Ltac whz t := eval lazy head beta iota zeta delta -[
sbind eruns follow
queue free_meta activate_group get_meta get_nominal_size enframe_read_off enframe_full am_take am_carve am_finish am_after_brk
alloc_meta ta_fin try_avail ag_tail alloc_group alloc_slot malloc_small_ctrl malloc_core malloc rd8 rd16 rd32
brk0_answer_ok brk_answer_ok mmap_answer_ok mmap_fixed_answer_ok munmap_answer_ok mprotect_answer_ok peek_answer_ok mremap_answer_ok
brk_pages_ok is_err round_up_pg ] in t.
Ltac mwhz := let T := focus_get in let T2 := whz T in
tryif constr_eq T T2 then fail "mwhz: no progress" else (idtac "NOTE: zeta fallback used"; let T3 := flat_args T2 in focus_set T3; mabs_args).
Ltac mstep := first [ mfeed | mret | mlet | menter | mwh | mscrut | mwhz ].
Ltac mgo := repeat mstep.
End Mq9.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqa.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Import Q6q3.

Section ShadowVocab.
Variable segs : list Segment.

Lemma shadow_granule0 : forall m S nb g, 0 <= g -> 8 * g + 8 <= nb ->
bytes_at segs m S (shadow_bytes nb) -> ro_cells segs m (S + g) [C1 (Z_to_bv 8 0)].
Proof.
intros m S nb g Hg Hgn Hb.
apply (shadow_head0 segs m (S + g) (nb - 8 * g)); [lia|]. apply shadow_skip; [lia | lia | exact Hb].
Qed.

Definition unpoisoned (m : word -> option byte) (SB s n : Z) : Prop :=
0 < n /\
(forall g, s / 8 <= g < (s + n - 1) / 8 -> bytes_at segs m (g + SB) [Z_to_bv 8 0]) /\
(exists v, bytes_at segs m ((s + n - 1) / 8 + SB) [Z_to_bv 8 v] /\ (v = 0 \/ (0 < v < 8 /\ (s + n - 1) mod 8 < v))) /\
(forall w, (s / 8 + SB) / 8 <= w <= ((s + n - 1) / 8 + SB) / 8 -> exists bs, length bs = 8%nat /\ bytes_at segs m (w * 8) bs).

Definition shadow_span_lo (SB s : Z) : Z := (s / 8 + SB) / 8 * 8.
Definition shadow_span_hi (SB s n : Z) : Z := ((s + n - 1) / 8 + SB) / 8 * 8 + 8.

Lemma unpoisoned_transport : forall W m m' SB s n,
unpoisoned m SB s n -> munch W m m' ->
(forall a k, shadow_span_lo SB s <= a -> a + k <= shadow_span_hi SB s n -> disjoint_from W a k) ->
unpoisoned m' SB s n.
Proof.
unfold shadow_span_lo, shadow_span_hi.
intros W m m' SB s n (Hn & Ha & (v & Hb & Hv) & Hc) MU OUT. split; [exact Hn|]. split; [|split].
- intros g Hg. eapply bytes_at_transport; [apply Ha; exact Hg | exact MU |].
change (Z.of_nat (length [Z_to_bv 8 0])) with 1. apply OUT; Z.div_mod_to_equations; lia.
- exists v. split; [| exact Hv]. eapply bytes_at_transport; [exact Hb | exact MU |].
change (Z.of_nat (length [Z_to_bv 8 v])) with 1. apply OUT; Z.div_mod_to_equations; lia.
- intros w Hw. destruct (Hc w Hw) as (bs & Hl & Hbs). exists bs. split; [exact Hl|].
eapply bytes_at_transport; [exact Hbs | exact MU |]. rewrite Hl. change (Z.of_nat 8%nat) with 8.
apply OUT; Z.div_mod_to_equations; lia.
Qed.

Lemma shadow_outside_stack : forall {RC__ : Q6q3.RunConsts} SB s n lo hi a k,
0 <= SB <= 2^31 -> 0 <= s -> s + n <= 2^47 -> 0 < n -> alloc_ceiling <= lo ->
shadow_span_lo SB s <= a -> a + k <= shadow_span_hi SB s n -> disjoint_from [(lo, hi)] a k.
Proof.
unfold shadow_span_lo, shadow_span_hi.
intros RC SB s n lo hi a k HSB Hs Hsn Hn Hlo Ha Hk. rc_pose_range RC. unfold alloc_ceiling in Hlo. cbn. split; [|exact I]. left.
assert ((s + n - 1) / 8 <= 2^44) by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations. lia.
Qed.

Lemma unpoisoned_gran0 : forall m SB s n g, unpoisoned m SB s n -> s / 8 <= g < (s + n - 1) / 8 ->
ro_cells segs m (g + SB) [C1 (Z_to_bv 8 0)].
Proof. intros m SB s n g (_ & Ha & _ & _) Hg. split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; apply Ha; exact Hg]. Qed.

Lemma unpoisoned_last : forall m SB s n, unpoisoned m SB s n ->
exists v, ro_cells segs m ((s + n - 1) / 8 + SB) [C1 (Z_to_bv 8 v)] /\ (v = 0 \/ (0 < v < 8 /\ (s + n - 1) mod 8 < v)).
Proof.
intros m SB s n (_ & _ & (v & Hb & Hv) & _). exists v. split; [| exact Hv].
split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; exact Hb].
Qed.

Lemma unpoisoned_word : forall m SB s n x, unpoisoned m SB s n ->
(s / 8 + SB) / 8 <= x / 8 <= ((s + n - 1) / 8 + SB) / 8 ->
exists bs, length bs = 8%nat /\ ro_cells segs m (x / 8 * 8) [CB 8 bs].
Proof.
intros m SB s n x (_ & _ & _ & Hc) Hx. destruct (Hc (x / 8) Hx) as (bs & Hl & Hb). exists bs. split; [exact Hl|].
split; [cbn; rewrite Hl; split; [reflexivity | exact I] | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact Hb].
Qed.

End ShadowVocab.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition a4_rt_cells : list (Z * list byte) :=
a4_rt_consts ++ [ (A_GOT_SB, le8 (Z_to_bv 64 A_SB_CELL)); (A_SB_CELL, le8 (Z_to_bv 64 A_SB)) ].
Definition asan_rt_ok (m : word -> option byte) : Prop := Forall (fun c => bytes_at asegs m (fst c) (snd c)) a4_rt_cells.

Lemma asan_rt_ok_transport : forall W m m', asan_rt_ok m -> munch W m m' ->
(forall c, In c a4_rt_cells -> disjoint_from W (fst c) (Z.of_nat (length (snd c)))) ->
asan_rt_ok m'.
Proof.
intros W m m' H MU OUT. unfold asan_rt_ok in *. rewrite Forall_forall in *. intros c Hc.
eapply bytes_at_transport; [apply H; exact Hc | exact MU | apply OUT; exact Hc].
Qed.

Lemma a4_rt_cells_in_img : forall c, In c a4_rt_cells -> 0x10000 <= fst c /\ fst c + Z.of_nat (length (snd c)) <= 0x645000.
Proof.
intros c Hc. unfold a4_rt_cells, a4_rt_consts in Hc. cbn [app] in Hc.
repeat (destruct Hc as [<- | Hc];
[cbn [fst snd]; unfold A_GOT_SB, A_SB_CELL; rewrite ?length_le8;
repeat match goal with |- context [Z.of_nat ?k] => let v := eval vm_compute in (Z.of_nat k) in change (Z.of_nat k) with v end; lia |]).
destruct Hc.
Qed.

Definition A_MEMSET_U : Z := 0x61be0.

Definition amemset_spec_U : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (d c n lo : Z) (old : list byte)
(Q : machine_state -> Prop),
(0 < n -> unpoisoned asegs m A_SB d n) -> asan_rt_ok m ->
0 <= d -> d + n <= 2^47 -> (d + n <= lo \/ bv_unsigned sp <= d) ->
a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 c -> a2 = Z_to_bv 64 n -> 0 <= c < 256 -> 0 <= n < 2^40 -> (n <= 64 \/ app_mem d n) ->
rw_cells asegs m d [CB (Z.to_nat n) old] ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 4096 -> bv_unsigned sp mod 16 = 0 ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
munch [(d, d + n); (lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
rw_cells asegs m' d [CB (Z.to_nat n) (repeat (Z_to_bv 8 c) (Z.to_nat n))] ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 d) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_MEMSET_U) fc None m (seg_rom asegs)).

Definition A_MEMCPY_U : Z := 0x61744.
Definition real_memcpy_specZ_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (src junk : list byte),
bytes_at asegs m (bv_unsigned a1) src ->
length src = Z.to_nat (bv_unsigned a2) ->
rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
(bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1) ->
mem_inv asegs m ->
evt asegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]
/\ bytes_at asegs m' (bv_unsigned a1) src)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdb34c) fc None m (seg_rom asegs)).

Definition amemcpy_spec_U : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (d s n lo : Z) (old src : list byte)
(Q : machine_state -> Prop),
(0 < n -> unpoisoned asegs m A_SB d n) -> (0 < n -> unpoisoned asegs m A_SB s n) -> asan_rt_ok m ->
0 <= d -> d + n <= 2^47 -> 0 <= s -> s + n <= 2^47 ->
(d + n <= lo \/ bv_unsigned sp <= d) -> (s + n <= lo \/ bv_unsigned sp <= s) ->
a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 n -> 0 <= n < 2^40 -> (n <= 64 \/ (app_mem d n /\ app_mem s n)) ->
(s + n <= d \/ d + n <= s) ->
rw_cells asegs m d [CB (Z.to_nat n) old] -> bytes_at asegs m s src -> length src = Z.to_nat n ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 4096 -> bv_unsigned sp mod 16 = 0 ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
munch [(d, d + n); (lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
rw_cells asegs m' d [CB (Z.to_nat n) src] -> bytes_at asegs m' s src ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 d) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_MEMCPY_U) fc None m (seg_rom asegs)).

Definition A_STRLEN_STUB_U : Z := 0x4f950.

Definition astrlen_spec_U : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (s lo : Z) (str slack : list byte)
(Q : machine_state -> Prop),
unpoisoned asegs m A_SB s (Z.of_nat (length str) + 1) -> asan_rt_ok m ->
0 <= s -> s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= 2^47 ->
(s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo \/ bv_unsigned sp <= s) ->
a0 = Z_to_bv 64 s -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) + 1 < 2^40 ->
(Z.of_nat (length str) <= 63 \/ app_mem s (Z.of_nat (length str) + 1)) ->
bytes_at asegs m s (str ++ Z_to_bv 8 0 :: slack) ->
(- (s + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 4096 -> bv_unsigned sp mod 16 = 0 ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
munch [(lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
bytes_at asegs m' s (str ++ Z_to_bv 8 0 :: slack) ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (Z.of_nat (length str))) a1' a2' a3' a4' a5' a6' a7'
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_STRLEN_STUB_U) fc None m (seg_rom asegs)).

Definition A_REGION_IS_POISONED : Z := 0x651ac.

Definition region_is_poisoned_spec_U : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (s n lo : Z)
(Q : machine_state -> Prop),
unpoisoned asegs m A_SB s n -> asan_rt_ok m -> app_mem s n -> 0 < n < 2^40 ->
(s + n <= lo \/ bv_unsigned sp <= s) ->
a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 n ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 128 -> bv_unsigned sp mod 16 = 0 ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
munch [(lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) -> unpoisoned asegs m' A_SB s n -> asan_rt_ok m' ->
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_REGION_IS_POISONED) fc None m (seg_rom asegs)).

Section WithIface.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Lemma asan_rt_ok_of_HEAPA : forall A LB LM FRS B m md, HEAPAx A LB LM FRS B m md -> asan_rt_ok m.
Proof.
intros A LB LM FRS B m md HP. unfold asan_rt_ok, a4_rt_cells. apply Forall_app. split.
- exact (heapA_rtc A4L HIx _ _ _ _ _ _ _ HP).
- destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP) as (H1 & H2 & _ & _).
constructor; [exact H1 | constructor; [exact H2 | constructor]].
Qed.

Lemma unpoisoned_of_blk : forall A LB LM FRS B m md ab nb s n,
HEAPAx A LB LM FRS B m md -> In (ab, nb) LB -> ab <= s -> s + n <= ab + nb -> 0 < n ->
unpoisoned asegs m A_SB s n.
Proof.
intros A LB LM FRS B m md ab nb s n HP Hblk Hab Hsn Hn.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ ab nb HP ltac:(apply in_or_app; left; exact Hblk)) as (Hnb0 & Hal & _).
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ ab nb HP Hblk) as SHb. unfold shad in SHb. cbn [hl_sb A4L] in SHb.
split; [exact Hn|]. split; [|split].
- intros g Hg. destruct (shadow_granule0 asegs m (ab / 8 + A_SB) nb (g - ab / 8) ltac:(Z.div_mod_to_equations; lia)
ltac:(Z.div_mod_to_equations; lia) SHb) as [_ Hb].
cbn [cells_bytes cbytes app] in Hb. replace (g + A_SB) with (ab / 8 + A_SB + (g - ab / 8)) by lia. exact Hb.
- set (g2 := (s + n - 1) / 8 - ab / 8).
destruct (Z.eq_dec (nb mod 8) 0) as [Hm0 | Hm1].
+ exists 0. split; [| left; reflexivity].
destruct (shadow_granule0 asegs m (ab / 8 + A_SB) nb g2 ltac:(subst g2; Z.div_mod_to_equations; lia)
ltac:(subst g2; Z.div_mod_to_equations; lia) SHb) as [_ Hb].
cbn [cells_bytes cbytes app] in Hb. replace ((s + n - 1) / 8 + A_SB) with (ab / 8 + A_SB + g2) by (subst g2; lia). exact Hb.
+ destruct (Z.eq_dec g2 (nb / 8)) as [Hlast | Hwhole].
* exists (nb mod 8). split; [| right; subst g2; Z.div_mod_to_equations; lia].
destruct (shadow_tail asegs m (ab / 8 + A_SB) nb ltac:(lia) Hm1 SHb) as [_ Hb].
cbn [cells_bytes cbytes app] in Hb. replace ((s + n - 1) / 8 + A_SB) with (ab / 8 + A_SB + nb / 8) by (subst g2; lia). exact Hb.
* exists 0. split; [| left; reflexivity].
destruct (shadow_granule0 asegs m (ab / 8 + A_SB) nb g2 ltac:(subst g2; Z.div_mod_to_equations; lia)
ltac:(subst g2; Z.div_mod_to_equations; lia) SHb) as [_ Hb].
cbn [cells_bytes cbytes app] in Hb. replace ((s + n - 1) / 8 + A_SB) with (ab / 8 + A_SB + g2) by (subst g2; lia). exact Hb.
- intros w Hw.
destruct (Z.lt_ge_cases (w * 8) (ab / 8 + A_SB)) as [Hlt | Hge].
+ destruct (heapA_shadow_words A4L HIx _ _ _ _ _ _ _ ab nb 0 HP Hblk ltac:(Z.div_mod_to_equations; lia)) as (bs & Hl & Hb).
unfold shad in Hb. cbn [hl_sb A4L] in Hb. exists bs. split; [exact Hl|].
replace ((ab / 8 + A_SB + 0) / 8 * 8) with (w * 8) in Hb by (Z.div_mod_to_equations; lia). exact Hb.
+ destruct (heapA_shadow_words A4L HIx _ _ _ _ _ _ _ ab nb (w * 8 - (ab / 8 + A_SB)) HP Hblk ltac:(Z.div_mod_to_equations; lia)) as (bs & Hl & Hb).
unfold shad in Hb. cbn [hl_sb A4L] in Hb. exists bs. split; [exact Hl|].
replace ((ab / 8 + A_SB + (w * 8 - (ab / 8 + A_SB))) / 8 * 8) with (w * 8) in Hb by (Z.div_mod_to_equations; lia). exact Hb.
Qed.

Definition A_MEMSET : Z := 0x61be0.

Definition amemset_spec_A : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (ab nb d c n lo : Z) (old : list byte)
(Q : machine_state -> Prop),
HEAPAx A LB LM FRS B m md ->
In (ab, nb) LB -> ab <= d -> d + n <= ab + nb ->
a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 c -> a2 = Z_to_bv 64 n -> 0 <= c < 256 -> 0 < n <= 64 ->
rw_cells asegs m d [CB (Z.to_nat n) old] ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 4096 -> bv_unsigned sp mod 16 = 0 ->
bv_unsigned sp <= hiA_top A4L HIx ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
munch [(d, d + n); (lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
rw_cells asegs m' d [CB (Z.to_nat n) (repeat (Z_to_bv 8 c) (Z.to_nat n))] ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 d) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_MEMSET) fc None m (seg_rom asegs)).

Definition A_MEMCPY : Z := 0x61744.

Definition amemcpy_spec_A : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (ab nb d sb nsb s n lo : Z) (old src : list byte)
(Q : machine_state -> Prop),
HEAPAx A LB LM FRS B m md ->
In (ab, nb) LB -> ab <= d -> d + n <= ab + nb ->
In (sb, nsb) LB -> sb <= s -> s + n <= sb + nsb ->
a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 n -> 0 < n <= 64 -> (s + n <= d \/ d + n <= s) ->
rw_cells asegs m d [CB (Z.to_nat n) old] -> bytes_at asegs m s src -> length src = Z.to_nat n ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 4096 -> bv_unsigned sp mod 16 = 0 ->
bv_unsigned sp <= hiA_top A4L HIx ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
munch [(d, d + n); (lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
rw_cells asegs m' d [CB (Z.to_nat n) src] -> bytes_at asegs m' s src ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 d) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_MEMCPY) fc None m (seg_rom asegs)).

Definition amemset_any_spec_A : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (ab nb d c n lo : Z) (old : list byte)
(Q : machine_state -> Prop),
HEAPAx A LB LM FRS B m md ->
In (ab, nb) LB -> ab <= d -> d + n <= ab + nb ->
a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 c -> a2 = Z_to_bv 64 n -> 0 <= c < 256 -> 0 <= n < 2^40 ->
rw_cells asegs m d [CB (Z.to_nat n) old] ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 4096 -> bv_unsigned sp mod 16 = 0 ->
bv_unsigned sp <= hiA_top A4L HIx ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
munch [(d, d + n); (lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
rw_cells asegs m' d [CB (Z.to_nat n) (repeat (Z_to_bv 8 c) (Z.to_nat n))] ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 d) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_MEMSET) fc None m (seg_rom asegs)).

Definition amemcpy_any_spec_A : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (ab nb d sb nsb s n lo : Z) (old src : list byte)
(Q : machine_state -> Prop),
HEAPAx A LB LM FRS B m md ->
In (ab, nb) LB -> ab <= d -> d + n <= ab + nb ->
In (sb, nsb) LB -> sb <= s -> s + n <= sb + nsb ->
a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 n -> 0 <= n < 2^40 -> (s + n <= d \/ d + n <= s) ->
rw_cells asegs m d [CB (Z.to_nat n) old] -> bytes_at asegs m s src -> length src = Z.to_nat n ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 4096 -> bv_unsigned sp mod 16 = 0 ->
bv_unsigned sp <= hiA_top A4L HIx ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
munch [(d, d + n); (lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
rw_cells asegs m' d [CB (Z.to_nat n) src] -> bytes_at asegs m' s src ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 d) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_MEMCPY) fc None m (seg_rom asegs)).

Definition astrlen_any_spec_A : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (sb nsb s lo : Z) (str slack : list byte)
(Q : machine_state -> Prop),
HEAPAx A LB LM FRS B m md ->
In (sb, nsb) LB -> sb <= s -> s + Z.of_nat (length str) + 1 <= sb + nsb ->
a0 = Z_to_bv 64 s -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) + 1 < 2^40 ->
bytes_at asegs m s (str ++ Z_to_bv 8 0 :: slack) ->
(- (s + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= alloc_ceiling ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 4096 -> bv_unsigned sp mod 16 = 0 ->
bv_unsigned sp <= hiA_top A4L HIx ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
munch [(lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
bytes_at asegs m' s (str ++ Z_to_bv 8 0 :: slack) ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (Z.of_nat (length str))) a1' a2' a3' a4' a5' a6' a7'
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x4f950) fc None m (seg_rom asegs)).

Definition real_memcpy_spec_A : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (src junk : list byte),
bytes_at asegs m (bv_unsigned a1) src ->
length src = Z.to_nat (bv_unsigned a2) ->
rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
(bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1) ->
mem_inv asegs m ->
evt asegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]
/\ bytes_at asegs m' (bv_unsigned a1) src)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdb34c) fc None m (seg_rom asegs)).

Definition A_STRLEN_STUB : Z := 0x4f950.

Definition astrlen_spec_A : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (sb nsb s lo : Z) (str slack : list byte)
(Q : machine_state -> Prop),
HEAPAx A LB LM FRS B m md ->
In (sb, nsb) LB -> sb <= s -> s + Z.of_nat (length str) + 1 <= sb + nsb ->
a0 = Z_to_bv 64 s -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) <= 63 ->
bytes_at asegs m s (str ++ Z_to_bv 8 0 :: slack) ->
(- (s + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= alloc_ceiling ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 4096 -> bv_unsigned sp mod 16 = 0 ->
bv_unsigned sp <= hiA_top A4L HIx ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
munch [(lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
bytes_at asegs m' s (str ++ Z_to_bv 8 0 :: slack) ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (Z.of_nat (length str))) a1' a2' a3' a4' a5' a6' a7'
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_STRLEN_STUB) fc None m (seg_rom asegs)).

Definition A_MEMCHR_THUNK : Z := 0x4f974.

Definition amemchr_spec_A : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (sb nsb s c n lo : Z) (buf : list byte)
(Q : machine_state -> Prop),
HEAPAx A LB LM FRS B m md ->
In (sb, nsb) LB -> sb <= s -> s + n <= sb + nsb ->
a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 c -> a2 = Z_to_bv 64 n -> 0 <= c < 2^64 -> 0 < n <= 64 ->
bytes_at asegs m s buf -> memchr_ok s (c mod 256) n buf ->
s + Z.of_nat (length buf) <= alloc_ceiling ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 4096 -> bv_unsigned sp mod 16 = 0 ->
bv_unsigned sp <= hiA_top A4L HIx ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
munch [(lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
bytes_at asegs m' s buf ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (memchr_res s (c mod 256) n buf)) a1' a2' a3' a4' a5' a6' a7'
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_MEMCHR_THUNK) fc None m (seg_rom asegs)).
End WithIface.
End RC__1.
End Mqa.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqb.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes Qfw3_c1.Mq2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QbFI. Import QRBl.
Import Qsw7 QJjn.
Import QgoP.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Definition reserve_entry : Z := 0xc403c.
Definition pushb_entry : Z := 0xc40a8.

Lemma le1_w : forall v : word, le1 v = [Z_to_bv 8 (bv_unsigned v)].
Proof. intros v. unfold le1, word_to_le_bytes. cbn. reflexivity. Qed.

Lemma land1_even : forall n, Z.land (2 * n) 1 = 0.
Proof. intros n. rewrite Z.land_comm. change 1 with (Z.ones 1). rewrite Z.land_comm, Z.land_ones by lia. change (2 ^ 1) with 2. rewrite Z.mul_comm, Z.mod_mul; lia. Qed.

Lemma shiftr1_double : forall n, 0 <= n -> Z.shiftr (2 * n) 1 = n.
Proof. intros n Hn. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. rewrite Z.mul_comm, Z.div_mul; lia. Qed.

Definition reserve_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists a2',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs)
/\ munch [] m m /\ wmono asegs m m /\ mem_inv asegs m.

Definition reserve_stmt : Prop :=
forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (S n r : Z) (szb : byte) (rest : list cell),
a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 r -> 0 <= r <= 22 ->
bv_unsigned szb = 2 * n -> 0 <= n ->
rw_cells asegs m S (C1 szb :: rest) ->
mem_inv asegs m ->
evt asegs (reserve_post ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 reserve_entry) fc None m (seg_rom asegs)).

Lemma reserve_spec : reserve_stmt.
Proof.
unfold reserve_stmt. intros until rest. intros A0 A1 Hr Hsz Hn OBJ MI. subst a0 a1.
pose proof (bv_unsigned_in_range 8 szb) as SR. unfold bv_modulus in SR. cbn in SR.
pose proof (rw_cells_bound _ _ _ _ OBJ) as OB. cbn [cells_size csize] in OB.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold reserve_entry.
bstep. bstep. if_falsex.
bstep. change (zxb szb) with (Z_to_bv 64 (bv_unsigned szb)). rewrite Hsz.
bstep. rewrite (unsigned_lit (2 * n)) by lia. rewrite land1_even.
bstep. if_false.
bstep. bstep. if_falsex.
bstep.
finish.
Qed.

Definition pushb_W (sp S n : Z) : list (Z * Z) := [(sp - 64, sp); (S, S + 1); (S + n + 1, S + n + 3)].

Definition pushb_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a1 : word) (S n lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0' a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (szb' : byte),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch (pushb_W (bv_unsigned sp) S n) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ bv_unsigned szb' = 2 * (n + 1)
/\ rw_cells asegs m' S [C1 szb']
/\ rw_cells asegs m' (S + n + 1) [C1 (Z_to_bv 8 (bv_unsigned a1)); C1 b0]
/\ stk asegs m' lo (bv_unsigned sp).

Definition pushb_stmt : Prop :=
forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (S n lo : Z) (szb x y : byte),
a0 = Z_to_bv 64 S ->
bv_unsigned szb = 2 * n -> 0 <= n <= 21 ->
rw_cells asegs m S [C1 szb] ->
rw_cells asegs m (S + n + 1) [C1 x; C1 y] ->
stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 ->
(S + 24 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= S) ->
mem_inv asegs m ->
evt asegs (pushb_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a1 S n lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pushb_entry) fc None m (seg_rom asegs)).

Lemma pushb_spec : pushb_stmt.
Proof.
unfold pushb_stmt. intros until y. intros A0 Hsz Hn SZ WIN ST LO SEP MI. subst a0.
pose proof (bv_unsigned_in_range 8 szb) as SR. unfold bv_modulus in SR. cbn in SR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof (bv_unsigned_in_range 64 a1) as CR. unfold bv_modulus in CR. cbn in CR.
pose proof (rw_cells_bound _ _ _ _ SZ) as OB1. cbn [cells_size csize Nat.add] in OB1.
pose proof (rw_cells_bound _ _ _ _ WIN) as OB2. cbn [cells_size csize Nat.add] in OB2.
pose proof (munch_refl (pushb_W (bv_unsigned sp) S n) m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold pushb_W in MU. unfold pushb_entry.
carve_frame 64%nat ST.
do 9 bstep.

bstep. bstep. change (zxb szb) with (Z_to_bv 64 (bv_unsigned szb)). rewrite Hsz.
bstep. rewrite (unsigned_lit (2 * n)) by lia. rewrite land1_even.
bstep. bstep. if_false.

bstep. bstep. if_truex.

bstep. rewrite (unsigned_lit (2 * n)) by lia. rewrite shiftr1_double by lia.
bstep. bstep.
bstep. rewrite le1_w. rewrite (unsigned_lit (2 * n + 2)) by lia. mem_after_store.
bstep.

bstep. replace (S + 1 + n) with (S + n + 1) by lia.
bstep. rewrite le1_w. mem_after_store.
bstep. rewrite le1_w. rewrite (unsigned_lit 0) by lia. change (Z_to_bv 8 0) with b0. mem_after_store.

do 10 bstep.
lazymatch goal with H : rw_cells asegs ?mx (bv_unsigned sp + -64) _ |- _ => rename H into FR2 end.
lazymatch goal with H : stk asegs ?mx lo _ |- _ => rename H into ST2 end.
release_frame FR2 ST2 (bv_unsigned sp).
finish.
2: eassumption.
rewrite Z_to_bv_unsigned. change (bv_wrap 8 (2 * n + 2)) with ((2 * n + 2) mod 2 ^ 8). rewrite Z.mod_small; lia.
Qed.
End Mqb.

Module Mqc.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Definition jo_get_A_entry : Z := 0x9bd5c.

Lemma div8_off : forall p j, p mod 8 = 0 -> 0 <= j < 8 -> (p + j) / 8 = p / 8.
Proof. intros p j Hp Hj. Z.div_mod_to_equations. lia. Qed.

Ltac asan_chk0_off p j :=
bstep; bstep; sh_norm; rewrite (div8_off p j) by lia;
bstep; bstep; first [ if_false | if_true ]; rewrite ?sxb_zero, ?zxb_zero.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section Regs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).

Definition ret4x (v : word) (m' : word -> option byte) : machine_state -> Prop :=
fun ms' => exists w x y, ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 v w x y a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs).

Lemma jo_get_null_A : forall m lo,
mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 ->
evt asegs (fun ms' => exists m', ret4x (Z_to_bv 64 0) m' ms' /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 jo_get_A_entry) fc None m (seg_rom asegs)).
Proof.
intros m lo MI ST LOS. unfold jo_get_A_entry.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
carve_frame 16%nat ST.
bstep. bstep. bstep. if_true. bstep. bstep. bstep.
apply evt_done. eexists. split; [eexists _, _, _; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
release_frame FR ST (bv_unsigned sp). exact ST.
Qed.

Lemma jo_get_A : forall m lo p ty rc tojs pb udel ud sbcell n,
rw_cells asegs m p (jhdr_cells ty rc tojs pb udel ud) ->
0 < p -> p + 40 <= 2^64 -> p mod 16 = 0 -> 0 <= rc -> rc + 1 < 2^31 -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> alloc_ceiling <= lo -> p + 40 <= alloc_ceiling ->

ro_cells asegs m A_GOT_SB [C8 (Z_to_bv 64 sbcell)] -> ro_cells asegs m sbcell [C8 (Z_to_bv 64 A_SB)] ->
0 < sbcell -> sbcell + 8 <= alloc_ceiling -> (sbcell + 8 <= p \/ p + 40 <= sbcell) -> p / 8 + A_SB + (n + 7) / 8 <= alloc_ceiling ->

8 <= n -> bytes_at asegs m (p / 8 + A_SB) (shadow_bytes n) ->
evt asegs (fun ms' => exists m', ret4x (Z_to_bv 64 p) m' ms' /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (p + 4, p + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' p (jhdr_cells ty (rc + 1) tojs pb udel ud) /\ stk asegs m' lo (bv_unsigned sp))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 jo_get_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until n. intros HDR Hp Hph Hal Hrc Hrc1 MI ST LOS LO PHI GOT CELL Hc0 Hc8 Hcp HSBhi Hn SH.
unfold jhdr_cells in HDR. unfold jo_get_A_entry, A_GOT_SB, A_SB in *.
unfold alloc_ceiling, sp_window_lo, stack_max_size in LO, PHI, Hc8, HSBhi.
assert (SHn : 1 <= (n + 7) / 8) by (apply Z.div_le_lower_bound; lia).
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (p + 4, p + 8)] m) as MU.
pose proof (shadow_head0 asegs m _ n Hn SH) as SH0. clear SH.
carve_frame 16%nat ST.
bstep. bstep. bstep. if_falsex.
bstep. bstep. bstep. bstep.
asan_chk0_off p 4.
bstep. bstep. norm_w32. bstepz. bstep. bstep. bstep.
apply evt_done. eexists. split; [eexists _, _, _; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
split. { unfold jhdr_cells. assumption. }
release_frame FR ST (bv_unsigned sp). exact ST.
Qed.
End Regs.
End RC__1.
End Mqc.

Module Mqd.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn.
Import QSL3.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Definition lh_delete_tail_A_entry : Z := 0xa528c.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section S.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Definition lh_delete_costB (es : list lent) (jf : nat) : Z := 512 * (Z.of_nat (length es) - Z.of_nat jf).

Definition lh_delete_tail_A_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word)
(t tbl size : Z) (es : list lent) (jf : nat)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' svs' (B' : bud),
ret_state A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 0) m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\ stk asegs m' lo (bv_unsigned sp) /\ heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv] /\
lh_open asegs A4F m' t tbl size (firstn jf es) svs' /\
bB B - lh_delete_costB es jf <= bB B' /\ bD B <= bD B' /\
HEAPAx A' (lh_blocks t tbl size (firstn jf es) ++ LB) LM FRS B' m' md'.

Definition lh_delete_tail_A_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word)
(t tbl size : Z) (es : list lent) (svs : list slotv) (jf : nat) (ef : lent),
HEAPAx A (lh_blocks t tbl size es ++ LB) LM FRS B m md ->
lh_open asegs A4F m t tbl size es svs ->
nth_error es jf = Some ef -> (forall j x, (jf <= j)%nat -> nth_error es j = Some x -> le_v x = 0) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 144 - 16 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 (ent_addr tbl (le_ix ef)) ->
lh_delete_costB es jf <= bB B ->
(forall ms' md' A', lh_delete_tail_A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo errv t tbl size es jf ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 lh_delete_tail_A_entry) fc None m (seg_rom asegs)).
End S.
End RC__1.
End Mqd.

Module Mqe.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek.
Import QbFI. Import Qhd4.
Import Qwm6.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition LOCCELL_A : Z := A_TP - 48.
Definition GLOBLOC_A : Z := 0x6457e8.
Definition LC_GLOBAL_A : Z := 2^64 - 1.
Definition LOCALE_LOCK_A : Z := 0x645890.
Definition CNAME_A : Z := 0x23100.
Definition A_USELOCALE : Z := 0xd01f0.
Definition A_ERRNO_LOCATION : Z := 0xcea68.
Definition A_DUPLOCALE : Z := 0xcf504.
Definition A_NEWLOCALE : Z := 0xcf610.
Definition A_FREELOCALE : Z := 0xcf570.

Definition usl_newA (cur nw : Z) : Z := if nw =? 0 then cur else if nw =? LC_GLOBAL_A then GLOBLOC_A else nw.
Definition usl_retA (cur : Z) : Z := if cur =? GLOBLOC_A then LC_GLOBAL_A else cur.

Section ALocaleStmt.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Definition uselocale_A_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cur nw : Z),
rw_cells asegs m LOCCELL_A [C8 (Z_to_bv 64 cur)] -> 0 <= cur < 2^64 -> 0 <= nw < 2^64 ->
tp = Z_to_bv 64 A_TP -> mem_inv asegs m ->
evt asegs (fun ms' => exists m' a1' a2' a3' a4',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (usl_retA cur)) a1' a2' a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(LOCCELL_A, LOCCELL_A + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' LOCCELL_A [C8 (Z_to_bv 64 (usl_newA cur nw))])
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 nw) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_USELOCALE) fc None m (seg_rom asegs)).

Definition errno_location_A_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
tp = Z_to_bv 64 A_TP ->
evt asegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A_ERRNO) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ERRNO_LOCATION) fc None m (seg_rom asegs)).

Definition duplocale_A_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word),
HEAPAx A LB LM FRS B m md ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 - hl_stack A4H ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 ->
Z.of_nat (length LM) < 8 ->
M2D <= bD B ->
(forall ms' m' md' A' (r : Z) (errv' : word),
ret_state A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' ->
rw_cells asegs m' A_ERRNO [C4 errv'] ->
( (r = 0 /\ errv' = Z_to_bv 64 ENOMEMv /\ HEAPAx A' LB LM FRS (charge B 0 M2D) m' md')
\/ (r <> 0 /\ (exists junk, rw_cells asegs m' r [CB 48 junk]) /\ HEAPAx A' LB ((r, 48) :: LM) FRS (charge B 0 M2D) m' md') ) ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 LC_GLOBAL_A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_DUPLOCALE) fc None m (seg_rom asegs)).

Definition newlocale_A_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo d : Z) (junk : list byte) (errv : word),
HEAPAx A LB LM FRS B m md -> In (d, 48) LM -> rw_cells asegs m d [CB 48 junk] ->
rw_cells asegs m LOCALE_LOCK_A [C4 (Z_to_bv 64 0)] ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 496 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 ->
(forall ms' m' (r : Z) (junk' : list byte),
ret_state A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (LB ++ lb_remove d LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' ->
rw_cells asegs m' d [CB 48 junk'] ->
rw_cells asegs m' LOCALE_LOCK_A [C4 (Z_to_bv 64 0)] ->
rw_cells asegs m' A_ERRNO [C4 errv] ->
HEAPAx A LB LM FRS B m' md ->
(r = d \/ r = 0) ->
AJ5 A4L HIx A T md ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 2) (Z_to_bv 64 CNAME_A) (Z_to_bv 64 d) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_NEWLOCALE) fc None m (seg_rom asegs)).

Definition freelocale_A_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo d n : Z) (errv : word),
HEAPAx A LB LM FRS B m md -> In (d, n) LM ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 - hl_stack A4H ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 ->
(forall ms' m' md' A' (r : word),
ret_state A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (LB ++ lb_remove d LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' ->
rw_cells asegs m' A_ERRNO [C4 errv] ->
HEAPAx A' LB (lb_remove d LM) FRS B m' md' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_FREELOCALE) fc None m (seg_rom asegs)).
End ALocaleStmt.

End RC__1.
End Mqe.

Module Mqf.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek. Import QPZI.Mq4.
Import QbFI. Import Qhd4.
Import Qwm6.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition put_costA (s : option jshape) (rc : Z) (BS : list blk) : Z :=
match s with None => 0 | Some _ => if rc =? 1 then 512 * Z.of_nat (length BS) else 0 end.

Section APutStmt.
Variable HIx : heap_iface_A A4L.
Variable put_entry : Z.
Variable put_stk : Z.

Definition put_postA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word)
(s : option jshape) (BS : list blk) (p rc : Z)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : word) (B' : bud),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv] /\
bB B - put_costA s rc BS <= bB B' /\ bD B <= bD B' /\
( ((s = None \/ rc = 1) /\ HEAPA A4L HIx A' LB LM FRS B' m' md')
\/ (exists s', s = Some s' /\ 2 <= rc /\ jval asegs A4F s' m' BS p (rc - 1) /\ HEAPA A4L HIx A' (BS ++ LB) LM FRS B' m' md') ).

Definition put_stmtA : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word)
(s : option jshape) (BS : list blk) (p rc : Z),
HEAPA A4L HIx A (BS ++ LB) LM FRS B m md ->
put_pre A4H A4F s m BS p rc ->
a0 = Z_to_bv 64 p ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - put_stk ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP ->
bv_unsigned ra mod 2 = 0 ->
put_costA s rc BS <= bB B ->
(forall ms' md' (A' : ASA A4L HIx),
put_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo errv s BS p rc ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 put_entry) fc None m (seg_rom asegs)).
End APutStmt.

Definition put_stk_A : Z := 112 + 64 + 96 + 96 + 4096.
Definition put_entry_A : Z := 0x9bdc0.
Definition put_stmt_A (HIx : heap_iface_A A4L) : Prop := put_stmtA HIx put_entry_A put_stk_A.

End RC__1.
End Mqf.

Module Mqg.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QHnV QCcH QfLs Qsw7 QJjn.
Import QbFI Qwm6.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Definition A_SNPRINTF_STUB : Z := 0x4fd74.
Definition A_FMT_LD : Z := 0x23760.
Definition A_FMT_LU : Z := 0x23780.
Definition A_FMT_U00CC : Z := 0x23700.

Definition SNP_STACK_A : Z := 12256.

Definition SHJ (a : Z) : Z := a / 8 + A_SB.
Definition shadow_okJ (m : word -> option byte) (dst n : Z) : Prop :=
forall k, 0 <= k -> dst / 8 * 8 + 8 * k < dst + n ->
exists v, bytes_at asegs m (SHJ (dst / 8 * 8) + k) [Z_to_bv 8 v] /\ (v = 0 \/ (0 < v < 8 /\ dst + n <= dst / 8 * 8 + 8 * k + v)).
Definition rng_okJ (m : word -> option byte) (p n : Z) : Prop :=
0 <= p /\ p + n + 8 <= 2^47
/\ (0 < n -> shadow_okJ m p n)
/\ (64 < n -> (p + n + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= p) /\ n <= 2^43)
/\ (0 < n <= 64 -> (exists w : word, rw_cells asegs m (8 * (SHJ p / 8)) [C8 w])
/\ (exists w : word, rw_cells asegs m (8 * (SHJ (p + n - 1) / 8)) [C8 w])).

Definition dappJ (D dn : Z) : Prop := (0x647000 <= D /\ D + dn + 8 <= 0x7fff8000) \/ (0x10007fff8000 <= D /\ D + dn + 8 <= 2^47).

Definition isnp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(D : Z) (dn : nat) (junkd : list byte) (P : Z -> list byte -> Prop) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte) (r : Z) (o : list byte),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ frm0 fc'
/\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
/\ stk asegs m' lo (bv_unsigned sp)
/\ r = Z.of_nat (length o) /\ P r o
/\ rw_cells asegs m' D [CB dn (o ++ Z_to_bv 8 0 :: skipn (S (length o)) junkd)].

Section SnpStmts.
Variable PFRT : (word -> option byte) -> Prop.
Variable PFLO : Z.

Definition isnp_pre (sp a0 a1 : word) (fc : bv 32) (m : word -> option byte) (D n : Z) (dn : nat) (junkd : list byte) (need lo : Z) : Prop :=
a0 = Z_to_bv 64 D /\ a1 = Z_to_bv 64 n /\
rw_cells asegs m D [CB dn junkd] /\ PFRT m /\
need <= Z.of_nat dn /\ need <= n < 2^63 /\
stk asegs m lo (bv_unsigned sp) /\ lo <= bv_unsigned sp - SNP_STACK_A /\ PFLO <= lo /\ bv_unsigned sp + 16 <= 2^47 /\
mem_inv asegs m /\ frm0 fc /\
(D + Z.of_nat dn <= lo \/ bv_unsigned sp <= D) /\
dappJ D (Z.of_nat dn) /\ (forall k, 0 < k <= need -> rng_okJ m D k).

Definition isnprintf_l_stmt (afmt : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D n : Z) (dn : nat) (junkd : list byte) (lo : Z),
isnp_pre sp a0 a1 fc m D n dn junkd 21 lo -> a2 = Z_to_bv 64 afmt ->
evt asegs (isnp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd
(fun r o => 1 <= r <= 20 /\ ~ In (Z_to_bv 8 0) o) lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_SNPRINTF_STUB) fc None m (seg_rom asegs)).
Definition isnprintf_ld_stmt : Prop := isnprintf_l_stmt A_FMT_LD.
Definition isnprintf_lu_stmt : Prop := isnprintf_l_stmt A_FMT_LU.

Definition isnprintf_u00cc_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D n c1 c2 : Z) (dn : nat) (junkd : list byte) (lo : Z),
isnp_pre sp a0 a1 fc m D n dn junkd 7 lo -> a2 = Z_to_bv 64 A_FMT_U00CC ->
0 <= c1 < 256 -> a3 = Z_to_bv 64 c1 -> 0 <= c2 < 256 -> a4 = Z_to_bv 64 c2 ->
evt asegs (isnp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd
(fun r o => o = map (Z_to_bv 8) [92; 117; 48; 48; c1; c2]) lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_SNPRINTF_STUB) fc None m (seg_rom asegs)).
End SnpStmts.
End Mqg.

Module Mqh.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup.
Import QCcH QfLs QJjn.
Import QbFI. Import Qhd4.
Import Qwm6.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition uw_at (hi : Z) (m : word -> option byte) (sp s0 : Z) (u : uwd) : Prop :=
match u with
| UWptr => s0 < alloc_ceiling \/ s0 mod 8 <> 0 \/ hi - 16 <= s0
| UWfp ra2 v2 => sp <= s0 - 16 /\ s0 mod 8 = 0 /\ s0 < hi - 16 /\
bytes_at asegs m (s0 - 16) (le8 (Z_to_bv 64 v2) ++ le8 (Z_to_bv 64 ra2)) /\
(v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= s0 \/ hi - 16 <= v2) /\
0 <= v2 < 2^64
| UWpaid => True
end.

Lemma uw_at_ptr : forall hi m sp s0, s0 < alloc_ceiling -> uw_at hi m sp s0 UWptr.
Proof. intros. cbn. left. assumption. Qed.

Lemma uw_at_paid : forall hi m sp s0, uw_at hi m sp s0 UWpaid.
Proof. intros. exact I. Qed.

Lemma uw_at_mono : forall hi m m' sp sp' s0 u W,
uw_at hi m sp s0 u -> munch W m m' -> Forall (fun iv => snd iv <= sp) W -> sp' <= sp ->
uw_at hi m' sp' s0 u.
Proof.
intros hi m m' sp sp' s0 u W UW MU HW Hsp. destruct u as [|ra2 v2|]; cbn in *; [exact UW | | exact I].
destruct UW as (H1 & H2 & H3 & HB & H5 & H6). split; [lia|]. split; [exact H2|]. split; [exact H3|]. split; [| split; [exact H5 | exact H6]].
eapply bytes_at_transport; [exact HB | exact MU |].
lazymatch goal with |- disjoint_from _ _ ?n => replace n with 16 by reflexivity end.
clear -HW H1. induction W as [|[lo' hi'] W IH]; cbn; [exact I|].
apply Forall_cons_iff in HW as [Hh HW]. cbn in Hh. split; [lia | apply IH; exact HW].
Qed.

Lemma uw_at_pre : forall hi m m' sp sp' s0 u W,
uw_at hi m sp s0 u -> munch W m m' -> Forall (fun iv => snd iv <= sp) W -> sp' <= sp ->
uw_pre A4L hi m' sp' s0 u.
Proof.
intros hi m m' sp sp' s0 u W UW MU HW Hsp.
pose proof (uw_at_mono hi m m' sp sp' s0 u W UW MU HW Hsp) as UW'.
destruct u as [|ra2 v2|]; cbn in *; [ | | exact I].
- destruct UW' as [H|[H|H]]; [left; exact H | right; left; exact H | right; right; exact H].
- destruct UW' as (H1 & H2 & H3 & HB & H5 & H6). split; [lia|]. split; [exact H2|]. split; [exact H3|]. split; [exact HB | split; [exact H5 | exact H6]].
Qed.

Lemma uw_at_heap_pres : forall hi m m' sp sp' s0 u LB,
uw_at hi m sp s0 u -> heap_pres A4H LB sp' m m' -> sp' <= sp -> uw_at hi m' sp s0 u.
Proof.
intros hi m m' sp sp' s0 u LB UW HPR Hsp. destruct u as [|ra2 v2|]; cbn in *; [exact UW | | exact I].
destruct UW as (H1 & H2 & H3 & HB & H5 & H6). split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [| split; [exact H5 | exact H6]].
eapply (heap_pres_bytes_at A4H); [exact HPR | exact HB | left; lia].
Qed.

Lemma uw_at_pre0 : forall hi m sp sp' s0 u, uw_at hi m sp s0 u -> sp' <= sp -> uw_pre A4L hi m sp' s0 u.
Proof.
intros hi m sp sp' s0 u UW Hsp. eapply (uw_at_pre hi m m sp sp' s0 u []); [exact UW | apply munch_refl | apply Forall_nil | exact Hsp].
Qed.
End RC__1.
End Mqh.

Module Mqi.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn.
Export QbFI. Export Qhd4 Qwm6.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Lemma ro_C8_of_bytes_at : forall segs m a v, bytes_at segs m a (le8 v) -> ro_cells segs m a [C8 v].
Proof. intros segs m a v H. split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact H]. Qed.

Lemma div8_add : forall p j, p mod 8 = 0 -> 0 <= j -> (p + j) / 8 = p / 8 + j / 8.
Proof. intros p j Hp Hj. Z.div_mod_to_equations. nia. Qed.

Lemma ro_cells_app : forall segs m A cs1 cs2,
ro_cells segs m A (cs1 ++ cs2) <-> ro_cells segs m A cs1 /\ ro_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
intros segs m A cs1 cs2. unfold ro_cells, cells_at.
rewrite cells_wf_app, cells_bytes_app, bytes_at_app.
split.
- intros ((W1 & W2) & (B1 & B2)). rewrite (cells_bytes_length cs1 W1) in B2. tauto.
- intros ((W1 & B1) & (W2 & B2)). rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

Import QRBl.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section WithIface.
Variable L : heap_layout_A.
Variable HIx : heap_iface_A L.
Let segs := hl_segs L.

Lemma in_block_factsA : forall A LB LM FR B m md a n x,
HEAPA L HIx A LB LM FR B m md -> In (a, n) (LB ++ LM) -> a <= x < a + n ->
x < alloc_ceiling /\ ~ hl_client_static L x /\
forall a' n', In (a', n') (LB ++ LM) -> a' <> a -> ~ (a' <= x < a' + n').
Proof.
intros A LB LM FR B m md a n x HP Hb Hx.
pose proof (heapA_blk L HIx _ _ _ _ _ _ _ _ _ HP Hb) as (Hn & _ & _ & Hhi & _).
split; [lia|]. split.
- replace x with (a + (x - a)) by lia. eapply (heapA_blk_not_static L HIx); eauto. lia.
- intros a' n' Hb' Hne Hx'.
pose proof (heapA_blk_disjoint L HIx _ _ _ _ _ _ _ _ _ _ _ HP Hb Hb' ltac:(congruence)) as Hd.
pose proof (heapA_blk L HIx _ _ _ _ _ _ _ _ _ HP Hb') as (Hn' & _). lia.
Qed.

Lemma fr_size_pos : forall k, 0 <= k -> 0 < fr_size k.
Proof. intros k Hk. unfold fr_size. pose proof (Z.pow_pos_nonneg 2 k). lia. Qed.
Lemma fr_shadow_len_bnd : forall k, 0 <= k <= 3 -> 0 < fr_shadow_len k <= 64.
Proof.
intros k Hk. unfold fr_shadow_len. split; [pose proof (Z.pow_pos_nonneg 2 k); lia|].
apply (Z.le_trans _ (8 * 2^3)); [apply Z.mul_le_mono_nonneg_l; [lia | apply Z.pow_le_mono_r; lia] | cbn; lia].
Qed.
Lemma fr_size_2 : fr_size 2 = 256. Proof. reflexivity. Qed.

Lemma fr_size_shadow : forall k, 0 <= k -> fr_size k = 8 * fr_shadow_len k.
Proof. intros k Hk. unfold fr_size, fr_shadow_len. lia. Qed.

Lemma shadow_blk_apart : forall A LB LM FR B m md a n x k,
HEAPA L HIx A LB LM FR B m md -> In (a, n) (LB ++ LM) -> 0 <= x -> x < alloc_ceiling -> 0 <= k <= 2^20 ->
a + n <= shad L x \/ shad L x + k <= a.
Proof.
intros A LB LM FR B m md a n x k HP Hin Hx Hxc Hk.
pose proof (heapA_blk_appmem L HIx _ _ _ _ _ _ _ _ _ HP Hin) as AM. unfold shad.
pose proof alloc_ceiling_range. pose proof (hl_sb_range L). pose proof (heapA_blk L HIx _ _ _ _ _ _ _ _ _ HP Hin) as (Hn & _ & Ha0 & _).
destruct AM as [AM | AM]; [left | right]; Z.div_mod_to_equations; lia.
Qed.

Lemma in_fr_ivs : forall FR b, In b (fr_ivs L FR) -> exists F k, In (F, k) FR /\ (b = (F, fr_size k - 8) \/ b = (shad L F, fr_shadow_len k)).
Proof.
intros FR b H. unfold fr_ivs in H. apply in_flat_map in H as ([F k] & Hf & Hb). exists F, k. split; [exact Hf|].
cbn in Hb. destruct Hb as [<- | [<- | []]]; [left | right]; reflexivity.
Qed.
Lemma fr_ivs_frame : forall FR F k, In (F, k) FR -> In (F, fr_size k - 8) (fr_ivs L FR).
Proof. intros FR F k H. unfold fr_ivs. apply in_flat_map. exists (F, k). split; [exact H | left; reflexivity]. Qed.
Lemma fr_ivs_shadow : forall FR F k, In (F, k) FR -> In (shad L F, fr_shadow_len k) (fr_ivs L FR).
Proof. intros FR F k H. unfold fr_ivs. apply in_flat_map. exists (F, k). split; [exact H | right; left; reflexivity]. Qed.

Lemma blk_not_fr_iv : forall A LB LM FR B m md a n,
HEAPA L HIx A LB LM FR B m md -> In (a, n) (LB ++ LM) -> ~ In (a, n) (fr_ivs L FR).
Proof.
intros A LB LM FR B m md a n HP Hin Hf. apply in_fr_ivs in Hf as (F & k & HF & Hb).
pose proof (heapA_frame L HIx _ _ _ _ _ _ _ _ _ HP HF) as (Hk & _ & HF0 & HFc & _).
pose proof (fr_size_pos k ltac:(lia)) as Hsz.
assert (Hsz8 : 64 <= fr_size k) by (unfold fr_size; pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)); lia).
destruct Hb as [E | E]; injection E as E1 E2; subst a n.
- pose proof (heapA_frame_disjoint L HIx _ _ _ _ _ _ _ _ _ _ _ HP HF Hin). lia.
- pose proof alloc_ceiling_range. pose proof (fr_shadow_len_bnd k Hk).
assert (HF0' : 0 <= F) by lia. assert (HFc' : F < alloc_ceiling) by lia. assert (HSK : 0 <= fr_shadow_len k <= 2^20) by lia.
pose proof (shadow_blk_apart _ _ _ _ _ _ _ _ _ F (fr_shadow_len k) HP Hin HF0' HFc' HSK) as D.
pose proof (heapA_blk L HIx _ _ _ _ _ _ _ _ _ HP Hin) as (Hn & _). lia.
Qed.

Lemma not_in_app3 : forall (b : blk) (X Y F : list blk), ~ In b (X ++ Y) -> ~ In b F -> ~ In b (X ++ Y ++ F).
Proof.
intros b X Y F H1 H2 H. rewrite app_assoc in H. apply in_app_or in H as [H|H]; [exact (H1 H) | exact (H2 H)].
Qed.

Lemma frame_writes_okA : forall A LB LM FR B m m' md W,
HEAPA L HIx A LB LM FR B m md ->
munch W m m' ->
Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= hiA_top L HIx)
\/ (exists a n, In (a, n) (LB ++ LM) /\ a <= fst iv /\ snd iv <= a + n)
\/ (forall x, fst iv <= x < snd iv -> hl_scratch L x)) W ->
forall a, 0 <= a < 2^64 -> ~ client_addr L (LB ++ LM) alloc_ceiling a -> ~ hl_scratch L a ->
~ (exists F k, In (F, k) FR /\ (F <= a < F + fr_size k - 8 \/ shad L F <= a < shad L F + fr_shadow_len k)) ->
m' (wa a) = m (wa a).
Proof.
intros A LB LM FR B m m' md W HP MU HW a Ha Hnc Hns _.
apply MU. rewrite wa_unsigned by lia. clear MU.
induction W as [|[lo hi] W IH]; cbn; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. split; [| apply IH; exact HW]. cbn in H1.
intros Hin. destruct H1 as [H1 | [(b & n & Hb & Hlo & Hhi) | Hsc]].
- apply Hnc. left; lia.
- apply Hnc. right. right. exists (b, n). split; [exact Hb | cbn; lia].
- exact (Hns (Hsc a Hin)).
Qed.

Lemma frame_writes_okF : forall A LB LM FR B m m' md W,
HEAPA L HIx A LB LM FR B m md ->
munch W m m' ->
Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= hiA_top L HIx)
\/ (exists a n, In (a, n) (LB ++ LM) /\ a <= fst iv /\ snd iv <= a + n)
\/ (forall x, fst iv <= x < snd iv -> hl_scratch L x)
\/ (exists F k, In (F, k) FR /\ ((F <= fst iv /\ snd iv <= F + fr_size k - 8)
\/ (shad L F <= fst iv /\ snd iv <= shad L F + fr_shadow_len k)))) W ->
forall a, 0 <= a < 2^64 -> ~ client_addr L (LB ++ LM) alloc_ceiling a -> ~ hl_scratch L a ->
~ (exists F k, In (F, k) FR /\ (F <= a < F + fr_size k - 8 \/ shad L F <= a < shad L F + fr_shadow_len k)) ->
m' (wa a) = m (wa a).
Proof.
intros A LB LM FR B m m' md W HP MU HW a Ha Hnc Hns Hnf.
apply MU. rewrite wa_unsigned by lia. clear MU.
induction W as [|[lo hi] W IH]; cbn; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. split; [| apply IH; exact HW]. cbn in H1.
intros Hin. destruct H1 as [H1 | [(b & n & Hb & Hlo & Hhi) | [Hsc | (F & k & HF & HFr)]]].
- apply Hnc. left; lia.
- apply Hnc. right. right. exists (b, n). split; [exact Hb | cbn; lia].
- exact (Hns (Hsc a Hin)).
- apply Hnf. exists F, k. split; [exact HF | lia].
Qed.

Lemma client_outsideA : forall A LB LM FR B LB0 m md W SP,
HEAPA L HIx A LB LM FR B m md ->
(forall b, In b LB0 -> In b (LB ++ LM ++ fr_ivs L FR)) ->
alloc_ceiling <= SP ->
Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= SP)
\/ (exists a n, In (a, n) (LB ++ LM) /\ ~ In (a, n) LB0 /\ a <= fst iv /\ snd iv <= a + n)
\/ (forall x, fst iv <= x < snd iv -> hl_scratch L x)) W ->
forall a, 0 <= a < 2^64 -> client_addr L LB0 SP a -> outside W a.
Proof.
intros A LB LM FR B LB0 m md W SP HP Hsub HSP HW a Ha Hc. pose proof alloc_ceiling_range as ACR. pose proof (hl_sb_range L) as SBR.
induction W as [|[lo hi] W IH]; cbn; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. split; [| apply IH; exact HW]. cbn in H1.
destruct Hc as [Hc | [Hc | (b & Hb0 & Hbr)]].
- destruct H1 as [H1 | [(b & n & Hb & Hnb & Hlo & Hhi) | Hsc]]; [lia| |].
+ pose proof (heapA_blk L HIx _ _ _ _ _ _ _ _ _ HP Hb) as (_ & _ & _ & Hbhi & _). lia.
+ intros Hin. pose proof (hl_scratch_in_img L a (Hsc a Hin)). pose proof (hl_img_range L). lia.
- destruct H1 as [H1 | [(b & n & Hb & Hnb & Hlo & Hhi) | Hsc]].
+ intros Hin. pose proof (hl_static_in_img L a Hc). pose proof (hl_img_range L). lia.
+ intros Hin. destruct (in_block_factsA _ _ _ _ _ _ _ _ _ a HP Hb ltac:(lia)) as (_ & Hns & _). exact (Hns Hc).
+ intros Hin. exact (hl_scratch_not_static L a (Hsc a Hin) Hc).
- destruct b as [ba bn]. cbn in Hbr. pose proof (Hsub _ Hb0) as HbX.
rewrite app_assoc in HbX. apply in_app_or in HbX as [Hb | Hfr].
+ destruct H1 as [H1 | [(b & n & Hb' & Hnb & Hlo & Hhi) | Hsc]].
* pose proof (heapA_blk L HIx _ _ _ _ _ _ _ _ _ HP Hb) as (_ & _ & _ & Hbhi & _). lia.
* intros Hin. assert (Hne : b <> ba).
{ intros ->. apply Hnb. rewrite (nodup_addr_size (LB ++ LM) ba n bn (heapA_blk_nodup L HIx _ _ _ _ _ _ _ HP) Hb' Hb). exact Hb0. }
destruct (in_block_factsA _ _ _ _ _ _ _ _ _ a HP Hb' ltac:(lia)) as (_ & _ & Hdis).
exact (Hdis ba bn Hb ltac:(congruence) ltac:(lia)).
* intros Hin. pose proof (heapA_blk_img L HIx _ _ _ _ _ _ _ _ _ HP Hb) as Himg.
pose proof (hl_scratch_in_img L a (Hsc a Hin)). lia.
+ apply in_fr_ivs in Hfr as (G & kg & HG & [E | E]); injection E as -> ->.
*
pose proof (heapA_frame L HIx _ _ _ _ _ _ _ _ _ HP HG) as (Hkg & _ & HG0 & HGc & HGimg & _).
destruct H1 as [H1 | [(b & n & Hb' & Hnb & Hlo & Hhi) | Hsc]].
-- lia.
-- intros Hin. pose proof (heapA_frame_disjoint L HIx _ _ _ _ _ _ _ _ _ _ _ HP HG Hb'). lia.
-- intros Hin. pose proof (hl_scratch_in_img L a (Hsc a Hin)). lia.
*
pose proof (heapA_frame L HIx _ _ _ _ _ _ _ _ _ HP HG) as (Hkg & _ & HG0 & HGc & HGimg & _).
assert (HI : 0 <= a - shad L G < fr_shadow_len kg) by lia.
pose proof (heapA_frame_shadow_sep L HIx _ _ _ _ _ _ _ _ _ (a - shad L G) HP HG HI) as [Hnc Himg].
replace (shad L G + (a - shad L G)) with a in Hnc, Himg by lia.
destruct H1 as [H1 | [(b & n & Hb' & Hnb & Hlo & Hhi) | Hsc]].
-- intros Hin. apply Hnc. left. lia.
-- intros Hin. apply Hnc. right. right. exists (b, n). split; [exact Hb' | cbn; lia].
-- intros Hin. pose proof (hl_scratch_in_img L a (Hsc a Hin)). lia.
Qed.

Lemma fresh_not_inA : forall A LB LM FR B m md r n k,
HEAPA L HIx A ((r, n) :: LB) LM FR B m md -> ~ In (r, k) (LB ++ LM).
Proof.
intros A LB LM FR B m md r n k HP Hin.
pose proof (heapA_blk_nodup L HIx _ _ _ _ _ _ _ HP) as ND. cbn in ND. inversion ND as [|x l Hni Hnd]; subst.
apply Hni. exact (in_map blk_addr _ _ Hin).
Qed.

Lemma sb_cellsA : forall A LB LM FR B m md, HEAPA L HIx A LB LM FR B m md ->
ro_cells segs m (hl_got_sb L) [C8 (Z_to_bv 64 (hl_sb_cell L))] /\ ro_cells segs m (hl_sb_cell L) [C8 (Z_to_bv 64 (hl_sb L))].
Proof.
intros A LB LM FR B m md HP. destruct (heapA_sb_cells L HIx _ _ _ _ _ _ _ HP) as (H1 & H2 & _ & _).
split; apply ro_C8_of_bytes_at; assumption.
Qed.

Lemma shad_sepA : forall A LB LM FR B m md a n i b k,
HEAPA L HIx A LB LM FR B m md -> In (a, n) LB -> 0 <= i < (n + 7) / 8 -> In (b, k) (LB ++ LM) ->
a / 8 + hl_sb L + i < alloc_ceiling /\ (a / 8 + hl_sb L + i < b \/ b + k <= a / 8 + hl_sb L + i)
/\ (a / 8 + hl_sb L + i < hl_img_lo L \/ hl_img_hi L <= a / 8 + hl_sb L + i).
Proof.
intros A LB LM FR B m md a n i b k HP Hin Hi Hb.
destruct (heapA_shadow_sep L HIx _ _ _ _ _ _ _ a n i HP Hin Hi) as [Hnc Himg].
unfold shad in Hnc, Himg. unfold client_addr, in_block in Hnc.
split; [| split; [| exact Himg]].
- destruct (Z.lt_ge_cases (a / 8 + hl_sb L + i) alloc_ceiling) as [?|Hge]; [assumption|]. exfalso. apply Hnc. left. lia.
- destruct (Z.lt_ge_cases (a / 8 + hl_sb L + i) b) as [?|Hge]; [left; assumption|].
destruct (Z.lt_ge_cases (a / 8 + hl_sb L + i) (b + k)) as [Hlt|?]; [| right; lia].
exfalso. apply Hnc. right. right. exists (b, k). split; [exact Hb | cbn; lia].
Qed.
End WithIface.
End RC__1.

Ltac in_app_prefix := first [ assumption | apply in_or_app; left; first [ assumption | in_prefix ] | apply in_or_app; right; first [ assumption | in_prefix ] | in_prefix ].

Ltac blk_factsA L HIx HP a n Hal Hlo Hhi Himg :=
let Hin := fresh "Hin" in let X := fresh in
lazymatch type of HP with HEAPA _ _ _ ?LB ?LM _ _ _ _ =>
assert (Hin : In (a, n) (LB ++ LM)) by in_app_prefix end;
pose proof (heapA_blk L HIx _ _ _ _ _ _ _ _ _ HP Hin) as X;
destruct X as (_ & Hal & Hlo & Hhi & _);
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi;
pose proof (heapA_blk_img L HIx _ _ _ _ _ _ _ _ _ HP Hin) as Himg;
clear Hin.

Ltac try_blocksA LBc tac :=
lazymatch LBc with
| (?a, ?n) :: ?r => first [ exists a, n; tac | try_blocksA r tac ]
| _ => fail
end.

Ltac solve_frameW_withA HPc :=
repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd];
first [ left; split; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia
| right; left;
lazymatch type of HPc with HEAPA _ _ _ ?LBc ?LMc _ _ _ _ =>
first [ try_blocksA LBc ltac:(split; [ in_app_prefix | lia ]) | try_blocksA LMc ltac:(split; [ in_app_prefix | lia ])
|
match goal with Hb : In (?a, ?n) _ |- _ => exists a, n; split; [ in_app_prefix | lia ] end ]
end
| right; right; intros; simpl hl_scratch; lia ].

Ltac heap_nowA L HIx HP MU WM MI :=
eapply (heapA_client_frame L HIx); [ exact HP | eapply (frame_writes_okA L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | exact MI ].

Ltac alloc_sideA_with lay :=
rewrite ?unsigned_lit by lia;
lazymatch goal with
| |- forall _ : machine_state, _ => idtac
| |- uw_pre _ _ _ _ _ _ /\ uw_ok _ _ _ _ => split; alloc_sideA_with lay
| |- _ =>
cbn [uw_pre uw_ok uw_key uw_cost bB bD bM charge chargeM]; lay; rewrite ?unsigned_lit by lia;
lazymatch goal with
| |- _ -> _ /\ _ => intros _; split; alloc_sideA_with lay
| |- True => exact I
| |- _ \/ _ =>
first [ left; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia | solve [ in_prefix ] | idtac ]
| |- In _ _ => first [ solve [ in_prefix ] | idtac ]
| |- stk _ _ _ _ => eassumption
| |- rw_cells _ _ _ _ => eassumption
| |- @eq (bv _) _ _ => first [ reflexivity | eassumption | symmetry; eassumption | apply bv_eq; rewrite ?unsigned_lit by lia; lia ]
| |- _ mod 16 = 0 =>
first [ assumption
| match goal with H : bv_unsigned ?sp mod 16 = 0 |- (bv_unsigned ?sp + ?k) mod 16 = 0 =>
rewrite <- Zplus_mod_idemp_l, H; reflexivity end
| lia ]
| |- _ => first [ lia
| unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia
| destruct (Z.eqb _ 0); lia
| idtac ]
end end.

Ltac alloc_sideA := alloc_sideA_with ltac:(idtac).

Tactic Notation "alloc_callA" uconstr(SPEC) constr(L) constr(HIx) constr(HP) constr(MU) constr(WM) constr(MI) :=
evt_done5; eapply SPEC; [ heap_nowA L HIx HP MU WM MI | .. ].

Tactic Notation "alloc_callA" uconstr(SPEC) "uw" constr(U) constr(L) constr(HIx) constr(HP) constr(MU) constr(WM) constr(MI) :=
evt_done5; eapply SPEC with (u := U); [ heap_nowA L HIx HP MU WM MI | .. ].

Tactic Notation "alloc_callA" uconstr(SPEC) "blk" constr(P) "uw" constr(U) constr(L) constr(HIx) constr(HP) constr(MU) constr(WM) constr(MI) :=
evt_done5; eapply SPEC with (p := P) (u := U); [ heap_nowA L HIx HP MU WM MI | .. ].

Ltac prefix_ofA LBc LB0 :=
lazymatch LBc with
| LB0 => constr:(@nil blk)
| ?x :: ?r => let p := prefix_ofA r LB0 in constr:(x :: p)
end.

Ltac not_in_old_coreA L HIx HPc :=
lazymatch goal with |- ~ In (?a, ?k) (?LB0 ++ ?LM) =>
lazymatch type of HPc with HEAPA _ _ _ ?LBc _ _ _ _ _ =>
let P := prefix_ofA LBc LB0 in
eapply (nodup_prefix_suffix P (LB0 ++ LM) a _ k);
[ rewrite app_assoc; change (P ++ LB0) with LBc; exact (heapA_blk_nodup L HIx _ _ _ _ _ _ _ HPc) | in_prefix ]
end
end.

Ltac in_subA Hb :=
first [ exact Hb
| apply in_or_app; right; in_subA Hb | apply in_or_app; left; in_subA Hb | right; in_subA Hb
| lazymatch type of Hb with
| In _ (_ :: _) => destruct Hb as [<- | Hb]; [left; reflexivity | in_subA Hb]
| In _ (_ ++ _) => apply in_app_or in Hb; destruct Hb as [Hb | Hb]; in_subA Hb
| In _ [] => destruct Hb
end ].

Ltac strip_frA Lst :=
lazymatch Lst with
| ?X ++ fr_ivs _ _ => X
| ?X ++ ?Y => let Y' := strip_frA Y in constr:(X ++ Y')
end.

Ltac not_in_oldA L HIx HPc :=
lazymatch goal with
| |- ~ In (?a, ?k) ?Lst =>
lazymatch Lst with
| context [fr_ivs _ _] =>
let Core := strip_frA Lst in
let Hn := fresh "Hn" in
assert (Hn : ~ In (a, k) Core) by not_in_old_coreA L HIx HPc;
let H := fresh "Hi" in intro H;
repeat (apply in_app_or in H; destruct H as [H|H]);
first [ refine (blk_not_fr_iv L HIx _ _ _ _ _ _ _ _ _ HPc _ H); solve [in_app_prefix]
| apply Hn; solve [in_subA H] ]
| _ => not_in_old_coreA L HIx HPc
end
end.

Ltac solve_clientWA L HIx HPc :=
repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd];
first [ left; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia
| right; left;
lazymatch type of HPc with HEAPA _ _ _ ?LBc _ _ _ _ _ =>
try_blocksA LBc ltac:(split; [ in_app_prefix | split; [ not_in_oldA L HIx HPc | lia ] ])
end
| right; right; intros; simpl hl_scratch; lia ].

Ltac in_tailA Hb :=
let H := fresh in
pose proof Hb as H; apply in_app_or in H; apply in_or_app;
destruct H as [H|H]; [ left; cbn [In app]; repeat (first [ exact H | right ]) | right; exact H ].

Ltac extend_presA L HIx HPR MU WM HPc HPR2 :=
lazymatch type of HPR with heap_pres _ ?LB0LM ?SP ?me ?m0 =>
lazymatch type of HPR2 with heap_pres _ _ _ _ ?m2 =>
let H := fresh "HPRx" in
assert (H : heap_pres L LB0LM SP me m2);
[ eapply heap_pres_trans; [ exact HPR |];
eapply heap_pres_trans;
[ eapply (heap_pres_of_munch L LB0LM SP); [ exact MU | exact WM |];
eapply (client_outsideA _ HIx); [ exact HPc | let Hb := fresh in intros ? Hb; first [ solve [in_tailA Hb] | cbn; tauto ]
| unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia | solve_clientWA L HIx HPc ]
| eapply heap_pres_weaken; [ exact HPR2 | lia | let Hb := fresh in intros ? Hb; first [ solve [in_tailA Hb] | cbn; tauto ] ] ]
| clear HPR; rename H into HPR ]
end end.

Ltac reenterA SEGS L HIx WX HP :=
aj5_enter; change (hl_segs L) with SEGS;
try lazymatch goal with
| |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
end.

Ltac shadow_nowA L HIx HP a n SH :=
let Hin := fresh "Hin" in
lazymatch type of HP with HEAPA _ _ _ ?LB _ _ _ _ _ => assert (Hin : In (a, n) LB) by in_prefix end;
pose proof (heapA_shadow_blk L HIx _ _ _ _ _ _ _ _ _ HP Hin) as SH; clear Hin;
unfold shad in SH; apply shadow_ro_cells in SH;
lazymatch type of SH with ro_cells _ _ _ (shadow_cells ?n) =>
let cs := eval cbv in (shadow_cells n) in change (shadow_cells n) with cs in SH
end.

Ltac heap_nowA_auto L HIx HPx H :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch type of HPx with HEAPA _ _ ?Ax ?LBx ?LMx ?FRx ?Bx ?mb ?mdx =>
match goal with MUc : munch _ mb mc, WMc : wmono _ mb mc, MIc : mem_inv _ mc |- _ =>
assert (H : HEAPA L HIx Ax LBx LMx FRx Bx mc mdx);
[ eapply (heapA_client_frame L HIx);
[ exact HPx | eapply (frame_writes_okA L HIx _ _ _ _ _ _ _ _ _ HPx MUc); solve_frameW_withA HPx | exact WMc | exact MIc ] | ]
end end end.

Ltac shadow_inA L HIx HP Hin SH :=
pose proof (heapA_shadow_blk L HIx _ _ _ _ _ _ _ _ _ HP Hin) as SH;
unfold shad in SH; apply shadow_ro_cells in SH;
lazymatch type of SH with ro_cells _ _ _ (shadow_cells ?n) =>
let cs := eval cbv in (shadow_cells n) in change (shadow_cells n) with cs in SH
end.

Ltac asan_chkA :=
bstep; step; sh_norm;
repeat match goal with
| |- context [ (?p + ?j) / 8 ] => is_Zlit j; rewrite (div8_add p j) by lia; let k := eval vm_compute in (Z.div j 8) in change (j / 8) with k
end;
step; step; first [ if_false | if_true ]; rewrite ?sxb_zero, ?zxb_zero.
End Mqi.

Module Mqj.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Import Q6q3.

Section ShadowVocab.
Variable segs : list Segment.

Lemma shadow_granule0 : forall m S nb g, 0 <= g -> 8 * g + 8 <= nb ->
bytes_at segs m S (shadow_bytes nb) -> ro_cells segs m (S + g) [C1 (Z_to_bv 8 0)].
Proof.
intros m S nb g Hg Hgn Hb.
apply (shadow_head0 segs m (S + g) (nb - 8 * g)); [lia|]. apply shadow_skip; [lia | lia | exact Hb].
Qed.

Definition unpoisoned (m : word -> option byte) (SB s n : Z) : Prop :=
0 < n /\
(forall g, s / 8 <= g < (s + n - 1) / 8 -> bytes_at segs m (g + SB) [Z_to_bv 8 0]) /\
(exists v, bytes_at segs m ((s + n - 1) / 8 + SB) [Z_to_bv 8 v] /\ (v = 0 \/ (0 < v < 8 /\ (s + n - 1) mod 8 < v))) /\
(forall w, (s / 8 + SB) / 8 <= w <= ((s + n - 1) / 8 + SB) / 8 -> exists bs, length bs = 8%nat /\ bytes_at segs m (w * 8) bs).

Definition shadow_span_lo (SB s : Z) : Z := (s / 8 + SB) / 8 * 8.
Definition shadow_span_hi (SB s n : Z) : Z := ((s + n - 1) / 8 + SB) / 8 * 8 + 8.

Lemma unpoisoned_transport : forall W m m' SB s n,
unpoisoned m SB s n -> munch W m m' ->
(forall a k, shadow_span_lo SB s <= a -> a + k <= shadow_span_hi SB s n -> disjoint_from W a k) ->
unpoisoned m' SB s n.
Proof.
unfold shadow_span_lo, shadow_span_hi.
intros W m m' SB s n (Hn & Ha & (v & Hb & Hv) & Hc) MU OUT. split; [exact Hn|]. split; [|split].
- intros g Hg. eapply bytes_at_transport; [apply Ha; exact Hg | exact MU |].
change (Z.of_nat (length [Z_to_bv 8 0])) with 1. apply OUT; Z.div_mod_to_equations; lia.
- exists v. split; [| exact Hv]. eapply bytes_at_transport; [exact Hb | exact MU |].
change (Z.of_nat (length [Z_to_bv 8 v])) with 1. apply OUT; Z.div_mod_to_equations; lia.
- intros w Hw. destruct (Hc w Hw) as (bs & Hl & Hbs). exists bs. split; [exact Hl|].
eapply bytes_at_transport; [exact Hbs | exact MU |]. rewrite Hl. change (Z.of_nat 8%nat) with 8.
apply OUT; Z.div_mod_to_equations; lia.
Qed.

Lemma shadow_outside_stack : forall {RC__ : Q6q3.RunConsts} SB s n lo hi a k,
0 <= SB <= 2^31 -> 0 <= s -> s + n <= 2^47 -> 0 < n -> alloc_ceiling <= lo ->
shadow_span_lo SB s <= a -> a + k <= shadow_span_hi SB s n -> disjoint_from [(lo, hi)] a k.
Proof.
unfold shadow_span_lo, shadow_span_hi.
intros RC SB s n lo hi a k HSB Hs Hsn Hn Hlo Ha Hk. rc_pose_range RC. unfold alloc_ceiling in Hlo. cbn. split; [|exact I]. left.
assert ((s + n - 1) / 8 <= 2^44) by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations. lia.
Qed.

Lemma unpoisoned_gran0 : forall m SB s n g, unpoisoned m SB s n -> s / 8 <= g < (s + n - 1) / 8 ->
ro_cells segs m (g + SB) [C1 (Z_to_bv 8 0)].
Proof. intros m SB s n g (_ & Ha & _ & _) Hg. split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; apply Ha; exact Hg]. Qed.

Lemma unpoisoned_last : forall m SB s n, unpoisoned m SB s n ->
exists v, ro_cells segs m ((s + n - 1) / 8 + SB) [C1 (Z_to_bv 8 v)] /\ (v = 0 \/ (0 < v < 8 /\ (s + n - 1) mod 8 < v)).
Proof.
intros m SB s n (_ & _ & (v & Hb & Hv) & _). exists v. split; [| exact Hv].
split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; exact Hb].
Qed.

Lemma unpoisoned_word : forall m SB s n x, unpoisoned m SB s n ->
(s / 8 + SB) / 8 <= x / 8 <= ((s + n - 1) / 8 + SB) / 8 ->
exists bs, length bs = 8%nat /\ ro_cells segs m (x / 8 * 8) [CB 8 bs].
Proof.
intros m SB s n x (_ & _ & _ & Hc) Hx. destruct (Hc (x / 8) Hx) as (bs & Hl & Hb). exists bs. split; [exact Hl|].
split; [cbn; rewrite Hl; split; [reflexivity | exact I] | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact Hb].
Qed.

End ShadowVocab.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition a4_rt_cells : list (Z * list byte) :=
a4_rt_consts ++ [ (A_GOT_SB, le8 (Z_to_bv 64 A_SB_CELL)); (A_SB_CELL, le8 (Z_to_bv 64 A_SB)) ].
Definition asan_rt_ok (m : word -> option byte) : Prop := Forall (fun c => bytes_at asegs m (fst c) (snd c)) a4_rt_cells.

Lemma asan_rt_ok_transport : forall W m m', asan_rt_ok m -> munch W m m' ->
(forall c, In c a4_rt_cells -> disjoint_from W (fst c) (Z.of_nat (length (snd c)))) ->
asan_rt_ok m'.
Proof.
intros W m m' H MU OUT. unfold asan_rt_ok in *. rewrite Forall_forall in *. intros c Hc.
eapply bytes_at_transport; [apply H; exact Hc | exact MU | apply OUT; exact Hc].
Qed.

Lemma a4_rt_cells_in_img : forall c, In c a4_rt_cells -> 0x10000 <= fst c /\ fst c + Z.of_nat (length (snd c)) <= 0x647000.
Proof.
intros c Hc. unfold a4_rt_cells, a4_rt_consts in Hc. cbn [app] in Hc.
repeat (destruct Hc as [<- | Hc];
[cbn [fst snd]; unfold A_GOT_SB, A_SB_CELL; rewrite ?length_le8;
repeat match goal with |- context [Z.of_nat ?k] => let v := eval vm_compute in (Z.of_nat k) in change (Z.of_nat k) with v end; lia |]).
destruct Hc.
Qed.

Definition A_MEMSET_U : Z := 0x61fb8.

Definition amemset_spec_U : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (d c n lo : Z) (old : list byte)
(Q : machine_state -> Prop),
(0 < n -> unpoisoned asegs m A_SB d n) -> asan_rt_ok m ->
0 <= d -> d + n <= 2^47 -> (d + n <= lo \/ bv_unsigned sp <= d) ->
a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 c -> a2 = Z_to_bv 64 n -> 0 <= c < 256 -> 0 <= n < 2^40 -> (n <= 64 \/ app_mem d n) ->
rw_cells asegs m d [CB (Z.to_nat n) old] ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 4096 -> bv_unsigned sp mod 16 = 0 ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
munch [(d, d + n); (lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
rw_cells asegs m' d [CB (Z.to_nat n) (repeat (Z_to_bv 8 c) (Z.to_nat n))] ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 d) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_MEMSET_U) fc None m (seg_rom asegs)).

Definition A_MEMCPY_U : Z := 0x61b1c.
Definition real_memcpy_specZ_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (src junk : list byte),
bytes_at asegs m (bv_unsigned a1) src ->
length src = Z.to_nat (bv_unsigned a2) ->
rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
(bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1) ->
mem_inv asegs m ->
evt asegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]
/\ bytes_at asegs m' (bv_unsigned a1) src)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdda10) fc None m (seg_rom asegs)).

Definition amemcpy_spec_U : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (d s n lo : Z) (old src : list byte)
(Q : machine_state -> Prop),
(0 < n -> unpoisoned asegs m A_SB d n) -> (0 < n -> unpoisoned asegs m A_SB s n) -> asan_rt_ok m ->
0 <= d -> d + n <= 2^47 -> 0 <= s -> s + n <= 2^47 ->
(d + n <= lo \/ bv_unsigned sp <= d) -> (s + n <= lo \/ bv_unsigned sp <= s) ->
a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 n -> 0 <= n < 2^40 -> (n <= 64 \/ (app_mem d n /\ app_mem s n)) ->
(s + n <= d \/ d + n <= s) ->
rw_cells asegs m d [CB (Z.to_nat n) old] -> bytes_at asegs m s src -> length src = Z.to_nat n ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 4096 -> bv_unsigned sp mod 16 = 0 ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
munch [(d, d + n); (lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
rw_cells asegs m' d [CB (Z.to_nat n) src] -> bytes_at asegs m' s src ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 d) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_MEMCPY_U) fc None m (seg_rom asegs)).

Definition A_STRLEN_STUB_U : Z := 0x4fd28.

Definition astrlen_spec_U : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (s lo : Z) (str slack : list byte)
(Q : machine_state -> Prop),
unpoisoned asegs m A_SB s (Z.of_nat (length str) + 1) -> asan_rt_ok m ->
0 <= s -> s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= 2^47 ->
(s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo \/ bv_unsigned sp <= s) ->
a0 = Z_to_bv 64 s -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) + 1 < 2^40 ->
(Z.of_nat (length str) <= 63 \/ app_mem s (Z.of_nat (length str) + 1)) ->
bytes_at asegs m s (str ++ Z_to_bv 8 0 :: slack) ->
(- (s + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 4096 -> bv_unsigned sp mod 16 = 0 ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
munch [(lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
bytes_at asegs m' s (str ++ Z_to_bv 8 0 :: slack) ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (Z.of_nat (length str))) a1' a2' a3' a4' a5' a6' a7'
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_STRLEN_STUB_U) fc None m (seg_rom asegs)).

Definition A_REGION_IS_POISONED : Z := 0x65584.

Definition region_is_poisoned_spec_U : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (s n lo : Z)
(Q : machine_state -> Prop),
unpoisoned asegs m A_SB s n -> asan_rt_ok m -> app_mem s n -> 0 < n < 2^40 ->
(s + n <= lo \/ bv_unsigned sp <= s) ->
a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 n ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 128 -> bv_unsigned sp mod 16 = 0 ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
munch [(lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) -> unpoisoned asegs m' A_SB s n -> asan_rt_ok m' ->
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_REGION_IS_POISONED) fc None m (seg_rom asegs)).

Section WithIface.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Lemma asan_rt_ok_of_HEAPA : forall A LB LM FRS B m md, HEAPAx A LB LM FRS B m md -> asan_rt_ok m.
Proof.
intros A LB LM FRS B m md HP. unfold asan_rt_ok, a4_rt_cells. apply Forall_app. split.
- exact (heapA_rtc A4L HIx _ _ _ _ _ _ _ HP).
- destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP) as (H1 & H2 & _ & _).
constructor; [exact H1 | constructor; [exact H2 | constructor]].
Qed.

Lemma unpoisoned_of_blk : forall A LB LM FRS B m md ab nb s n,
HEAPAx A LB LM FRS B m md -> In (ab, nb) LB -> ab <= s -> s + n <= ab + nb -> 0 < n ->
unpoisoned asegs m A_SB s n.
Proof.
intros A LB LM FRS B m md ab nb s n HP Hblk Hab Hsn Hn.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ ab nb HP ltac:(apply in_or_app; left; exact Hblk)) as (Hnb0 & Hal & _).
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ ab nb HP Hblk) as SHb. unfold shad in SHb. cbn [hl_sb A4L] in SHb.
split; [exact Hn|]. split; [|split].
- intros g Hg. destruct (shadow_granule0 asegs m (ab / 8 + A_SB) nb (g - ab / 8) ltac:(Z.div_mod_to_equations; lia)
ltac:(Z.div_mod_to_equations; lia) SHb) as [_ Hb].
cbn [cells_bytes cbytes app] in Hb. replace (g + A_SB) with (ab / 8 + A_SB + (g - ab / 8)) by lia. exact Hb.
- set (g2 := (s + n - 1) / 8 - ab / 8).
destruct (Z.eq_dec (nb mod 8) 0) as [Hm0 | Hm1].
+ exists 0. split; [| left; reflexivity].
destruct (shadow_granule0 asegs m (ab / 8 + A_SB) nb g2 ltac:(subst g2; Z.div_mod_to_equations; lia)
ltac:(subst g2; Z.div_mod_to_equations; lia) SHb) as [_ Hb].
cbn [cells_bytes cbytes app] in Hb. replace ((s + n - 1) / 8 + A_SB) with (ab / 8 + A_SB + g2) by (subst g2; lia). exact Hb.
+ destruct (Z.eq_dec g2 (nb / 8)) as [Hlast | Hwhole].
* exists (nb mod 8). split; [| right; subst g2; Z.div_mod_to_equations; lia].
destruct (shadow_tail asegs m (ab / 8 + A_SB) nb ltac:(lia) Hm1 SHb) as [_ Hb].
cbn [cells_bytes cbytes app] in Hb. replace ((s + n - 1) / 8 + A_SB) with (ab / 8 + A_SB + nb / 8) by (subst g2; lia). exact Hb.
* exists 0. split; [| left; reflexivity].
destruct (shadow_granule0 asegs m (ab / 8 + A_SB) nb g2 ltac:(subst g2; Z.div_mod_to_equations; lia)
ltac:(subst g2; Z.div_mod_to_equations; lia) SHb) as [_ Hb].
cbn [cells_bytes cbytes app] in Hb. replace ((s + n - 1) / 8 + A_SB) with (ab / 8 + A_SB + g2) by (subst g2; lia). exact Hb.
- intros w Hw.
destruct (Z.lt_ge_cases (w * 8) (ab / 8 + A_SB)) as [Hlt | Hge].
+ destruct (heapA_shadow_words A4L HIx _ _ _ _ _ _ _ ab nb 0 HP Hblk ltac:(Z.div_mod_to_equations; lia)) as (bs & Hl & Hb).
unfold shad in Hb. cbn [hl_sb A4L] in Hb. exists bs. split; [exact Hl|].
replace ((ab / 8 + A_SB + 0) / 8 * 8) with (w * 8) in Hb by (Z.div_mod_to_equations; lia). exact Hb.
+ destruct (heapA_shadow_words A4L HIx _ _ _ _ _ _ _ ab nb (w * 8 - (ab / 8 + A_SB)) HP Hblk ltac:(Z.div_mod_to_equations; lia)) as (bs & Hl & Hb).
unfold shad in Hb. cbn [hl_sb A4L] in Hb. exists bs. split; [exact Hl|].
replace ((ab / 8 + A_SB + (w * 8 - (ab / 8 + A_SB))) / 8 * 8) with (w * 8) in Hb by (Z.div_mod_to_equations; lia). exact Hb.
Qed.

Definition A_MEMSET : Z := 0x61fb8.

Definition amemset_spec_A : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (ab nb d c n lo : Z) (old : list byte)
(Q : machine_state -> Prop),
HEAPAx A LB LM FRS B m md ->
In (ab, nb) LB -> ab <= d -> d + n <= ab + nb ->
a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 c -> a2 = Z_to_bv 64 n -> 0 <= c < 256 -> 0 < n <= 64 ->
rw_cells asegs m d [CB (Z.to_nat n) old] ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 4096 -> bv_unsigned sp mod 16 = 0 ->
bv_unsigned sp <= hiA_top A4L HIx ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
munch [(d, d + n); (lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
rw_cells asegs m' d [CB (Z.to_nat n) (repeat (Z_to_bv 8 c) (Z.to_nat n))] ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 d) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_MEMSET) fc None m (seg_rom asegs)).

Definition A_MEMCPY : Z := 0x61b1c.

Definition amemcpy_spec_A : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (ab nb d sb nsb s n lo : Z) (old src : list byte)
(Q : machine_state -> Prop),
HEAPAx A LB LM FRS B m md ->
In (ab, nb) LB -> ab <= d -> d + n <= ab + nb ->
In (sb, nsb) LB -> sb <= s -> s + n <= sb + nsb ->
a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 n -> 0 < n <= 64 -> (s + n <= d \/ d + n <= s) ->
rw_cells asegs m d [CB (Z.to_nat n) old] -> bytes_at asegs m s src -> length src = Z.to_nat n ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 4096 -> bv_unsigned sp mod 16 = 0 ->
bv_unsigned sp <= hiA_top A4L HIx ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
munch [(d, d + n); (lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
rw_cells asegs m' d [CB (Z.to_nat n) src] -> bytes_at asegs m' s src ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 d) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_MEMCPY) fc None m (seg_rom asegs)).

Definition amemset_any_spec_A : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (ab nb d c n lo : Z) (old : list byte)
(Q : machine_state -> Prop),
HEAPAx A LB LM FRS B m md ->
In (ab, nb) LB -> ab <= d -> d + n <= ab + nb ->
a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 c -> a2 = Z_to_bv 64 n -> 0 <= c < 256 -> 0 <= n < 2^40 ->
rw_cells asegs m d [CB (Z.to_nat n) old] ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 4096 -> bv_unsigned sp mod 16 = 0 ->
bv_unsigned sp <= hiA_top A4L HIx ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
munch [(d, d + n); (lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
rw_cells asegs m' d [CB (Z.to_nat n) (repeat (Z_to_bv 8 c) (Z.to_nat n))] ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 d) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_MEMSET) fc None m (seg_rom asegs)).

Definition amemcpy_any_spec_A : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (ab nb d sb nsb s n lo : Z) (old src : list byte)
(Q : machine_state -> Prop),
HEAPAx A LB LM FRS B m md ->
In (ab, nb) LB -> ab <= d -> d + n <= ab + nb ->
In (sb, nsb) LB -> sb <= s -> s + n <= sb + nsb ->
a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 n -> 0 <= n < 2^40 -> (s + n <= d \/ d + n <= s) ->
rw_cells asegs m d [CB (Z.to_nat n) old] -> bytes_at asegs m s src -> length src = Z.to_nat n ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 4096 -> bv_unsigned sp mod 16 = 0 ->
bv_unsigned sp <= hiA_top A4L HIx ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
munch [(d, d + n); (lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
rw_cells asegs m' d [CB (Z.to_nat n) src] -> bytes_at asegs m' s src ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 d) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_MEMCPY) fc None m (seg_rom asegs)).

Definition astrlen_any_spec_A : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (sb nsb s lo : Z) (str slack : list byte)
(Q : machine_state -> Prop),
HEAPAx A LB LM FRS B m md ->
In (sb, nsb) LB -> sb <= s -> s + Z.of_nat (length str) + 1 <= sb + nsb ->
a0 = Z_to_bv 64 s -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) + 1 < 2^40 ->
bytes_at asegs m s (str ++ Z_to_bv 8 0 :: slack) ->
(- (s + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= alloc_ceiling ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 4096 -> bv_unsigned sp mod 16 = 0 ->
bv_unsigned sp <= hiA_top A4L HIx ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
munch [(lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
bytes_at asegs m' s (str ++ Z_to_bv 8 0 :: slack) ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (Z.of_nat (length str))) a1' a2' a3' a4' a5' a6' a7'
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x4fd28) fc None m (seg_rom asegs)).

Definition real_memcpy_spec_A : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (src junk : list byte),
bytes_at asegs m (bv_unsigned a1) src ->
length src = Z.to_nat (bv_unsigned a2) ->
rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
(bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1) ->
mem_inv asegs m ->
evt asegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]
/\ bytes_at asegs m' (bv_unsigned a1) src)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdda10) fc None m (seg_rom asegs)).

Definition A_STRLEN_STUB : Z := 0x4fd28.

Definition astrlen_spec_A : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (sb nsb s lo : Z) (str slack : list byte)
(Q : machine_state -> Prop),
HEAPAx A LB LM FRS B m md ->
In (sb, nsb) LB -> sb <= s -> s + Z.of_nat (length str) + 1 <= sb + nsb ->
a0 = Z_to_bv 64 s -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) <= 63 ->
bytes_at asegs m s (str ++ Z_to_bv 8 0 :: slack) ->
(- (s + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= alloc_ceiling ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 4096 -> bv_unsigned sp mod 16 = 0 ->
bv_unsigned sp <= hiA_top A4L HIx ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
munch [(lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
bytes_at asegs m' s (str ++ Z_to_bv 8 0 :: slack) ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (Z.of_nat (length str))) a1' a2' a3' a4' a5' a6' a7'
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_STRLEN_STUB) fc None m (seg_rom asegs)).

Definition A_MEMCHR_THUNK : Z := 0x4fd4c.

Definition amemchr_spec_A : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (sb nsb s c n lo : Z) (buf : list byte)
(Q : machine_state -> Prop),
HEAPAx A LB LM FRS B m md ->
In (sb, nsb) LB -> sb <= s -> s + n <= sb + nsb ->
a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 c -> a2 = Z_to_bv 64 n -> 0 <= c < 2^64 -> 0 < n <= 64 ->
bytes_at asegs m s buf -> memchr_ok s (c mod 256) n buf ->
s + Z.of_nat (length buf) <= alloc_ceiling ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 4096 -> bv_unsigned sp mod 16 = 0 ->
bv_unsigned sp <= hiA_top A4L HIx ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
munch [(lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
bytes_at asegs m' s buf ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (memchr_res s (c mod 256) n buf)) a1' a2' a3' a4' a5' a6' a7'
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_MEMCHR_THUNK) fc None m (seg_rom asegs)).
End WithIface.
End RC__1.
End Mqj.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qtgi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qtgi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
Record oent := OE { oe_a : Z; oe_k : Z; oe_kn : Z; oe_ks : list byte; oe_v : Z }.
Definition ohd (es : list oent) : Z := match es with [] => 0 | e :: _ => oe_a e end.

Lemma ohd_skipn_map : forall (A : Type) (f : A -> oent) (l : list A) j,
ohd (skipn j (map f l)) = match nth_error l j with Some x => oe_a (f x) | None => 0 end.
Proof. intros A f l. induction l as [|x l IH]; intros [|j]; cbn; try reflexivity. apply IH. Qed.
Lemma ohd_skipn : forall l n, ohd (skipn n l) = match nth_error l n with Some x => oe_a x | None => 0 end.
Proof. intros l. induction l as [|x l IH]; intros [|n]; cbn; try reflexivity. apply IH. Qed.

Section WithSegs.
Variable segs : list Segment.
Variable fn : fnaddrs.
Notation rw_cells := (rw_cells segs).

Definition otab (m : word -> option byte) (BS : list blk) (t : Z) (es : list oent) : Prop :=
inside_blocks BS t 16 /\ rw_cells m (t + 8) [C8 (wz (ohd es))] /\
forall j e, nth_error es j = Some e ->
0 < oe_a e /\ oe_a e mod 8 = 0 /\ inside_blocks BS (oe_a e) 32 /\
(exists pad : word, rw_cells m (oe_a e) [C8 (wz (oe_k e)); C4 (wz 0); C4 pad; C8 (wz (oe_v e)); C8 (wz (ohd (skipn (S j) es)))]) /\
cstr segs m (oe_k e) (oe_kn e) (oe_ks e) /\ In (oe_k e, oe_kn e) BS /\ oe_kn e <= 2^31.

Lemma otab_agree : forall m m' BS BS' t es,
otab m BS t es -> agree_on segs BS' m m' -> incl BS BS' -> otab m' BS t es.
Proof.
intros m m' BS BS' t es (IB & HD & ENT) AG INCL. split; [exact IB|]. split.
- eapply (rw_cells_agree segs); [exact HD | exact AG |]. destruct IB as (a & k & Hin & H1 & H2). exists a, k. split; [apply INCL; exact Hin | cbn; lia].
- intros j e Hj. destruct (ENT j e Hj) as (A0 & AL8 & IBe & (pad & RW) & CS & INk & KN).
split; [exact A0|]. split; [exact AL8|]. split; [exact IBe|]. split; [| split; [| split; [exact INk | exact KN]]].
+ exists pad. eapply (rw_cells_agree segs); [exact RW | exact AG | eapply inside_blocks_incl; [exact IBe | exact INCL]].
+ eapply (cstr_agree segs); [exact CS | exact AG | apply INCL; exact INk | destruct CS as (L & _); lia].
Qed.

Lemma lhtab_otab : forall m TBS t kvs,
lhtab2 segs fn m TBS t kvs -> (forall a n, In (a, n) TBS -> 0 < a /\ a mod 16 = 0) ->
exists es, otab m TBS t es /\ kvs = map (fun e => (oe_k e, oe_v e)) es /\
exists tbl size, TBS = (t, 56) :: (tbl, 40 * size) :: map (fun e => (oe_k e, oe_kn e)) es.
Proof.
intros m TBS t kvs (tbl & size & es & svs & Hkvs & E & OPEN) POS.
destruct OPEN as (HDR & SL & (LK1 & LK2 & ND & LK4) & KEYS & _ & _ & Hlen).
set (f := fun e : lent => OE (ent_addr tbl (le_ix e)) (le_k e) (le_kn e) (le_ks e) (le_v e)).
exists (map f es). split; [| split; [rewrite Hkvs, map_map; apply map_ext; intros e; reflexivity |
exists tbl, size; rewrite E; unfold lh_blocks; rewrite map_map; reflexivity]].
assert (Htbl : 0 < tbl /\ tbl mod 16 = 0) by (apply (POS tbl (40 * size)); rewrite E; right; left; reflexivity).
split; [| split].
- exists t, 56. split; [rewrite E; left; reflexivity | lia].
- unfold lh_hdrf in HDR.
apply (proj1 (rw_cells_app segs m t [C4 (Z_to_bv 64 size); C4 (Z_to_bv 64 (Z.of_nat (length es)))] _)) in HDR as [_ H].
apply (proj1 (rw_cells_app segs m _ [C8 (Z_to_bv 64 (hd_of tbl es))] _)) in H as [H _]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H.
replace (ohd (map f es)) with (hd_of tbl es) by (destruct es; reflexivity). exact H.
- intros j e Hj. rewrite nth_error_map in Hj. destruct (nth_error es j) as [e0|] eqn:Hj0; [| discriminate Hj]. cbn in Hj. injection Hj as <-.
cbn [oe_a oe_k oe_kn oe_ks oe_v f].
assert (Hin : In e0 es) by (eapply nth_error_In; exact Hj0).
destruct (LK1 j e0 Hj0) as (sv & Hsv & Ek & Ekc & Ev & Enx & Epv).
pose proof (nth_error_lt _ _ _ Hsv) as Hix.
destruct (LK4 e0 Hin) as (Hk0 & _ & Hkn & _).
split; [unfold ent_addr; lia|]. split.
{ unfold ent_addr. destruct Htbl as [_ Hal]. apply Z.mod_divide in Hal; [|lia]. destruct Hal as [q Hq].
replace (tbl + 40 * Z.of_nat (le_ix e0)) with ((q * 2 + 5 * Z.of_nat (le_ix e0)) * 8) by lia. apply Z.mod_mul. lia. }
split.
{ exists tbl, (40 * size). split; [rewrite E; right; left; reflexivity | unfold ent_addr; rewrite <- Hlen; split; [lia | nia]]. }
split.
{ exists (Z_to_bv 64 (sv_pad sv)). pose proof (SL (le_ix e0) sv Hsv) as H. unfold slot_cells in H.
rewrite Ek, Ekc, Ev, Enx in H.
apply (proj1 (rw_cells_app segs m _ [C8 (wz (le_k e0)); C4 (wz 0); C4 (wz (sv_pad sv)); C8 (wz (le_v e0)); C8 (wz (nx_of tbl es j))] [C8 (wz (sv_pv sv))])) in H as [H _].
unfold nx_of in H.
replace (ohd (skipn (S j) (map f es))) with (match nth_error es (S j) with Some e' => ent_addr tbl (le_ix e') | None => 0 end); [exact H|].
rewrite (ohd_skipn_map lent f es (S j)). destruct (nth_error es (S j)); reflexivity. }
split; [exact (proj1 (Forall_forall _ _) KEYS e0 Hin)|].
split; [| exact Hkn].
rewrite E. right. right. rewrite in_map_iff. exists e0. split; [reflexivity | exact Hin].
Qed.

End WithSegs.
