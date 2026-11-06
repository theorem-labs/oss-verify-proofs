(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QWxq_c1 QRjH QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw Qwm6 QlKV QsKa QJZd Q3Gm QGm2 QhtD QbKA Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq7 QJZd.Mq8.
Import Q3Gm.Mq0.
Import QGm2.Mq0 QhtD.Mq0 QbKA.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition ODR_A : Z := 0x6221a0.

Lemma munch_join : forall W1 W2 W m m1 m2,
munch W1 m m1 -> munch W2 m1 m2 -> sub_fp W1 W -> sub_fp W2 W -> munch W m m2.
Proof. intros W1 W2 W m m1 m2 M1 M2 S1 S2 x Hx. rewrite (M2 x (S2 _ Hx)). apply M1, S1, Hx. Qed.

Ltac fold_closed_bv :=
repeat match goal with
| |- evt _ _ (MS ?R _ _ _ _ _ _) =>
match R with context [Z_to_bv 64 ?e] =>
lazymatch e with
| Z.land _ _ => idtac | Z.lor _ _ => idtac | Z.add _ _ => idtac | bv_unsigned _ => idtac | Z.shiftr _ _ => idtac | Z.shiftl _ _ => idtac | Z.sub _ _ => idtac | Z.mul _ _ => idtac | Z.modulo _ _ => idtac
end;
let v := eval vm_compute in e in
lazymatch v with
| Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac
end;
change (Z_to_bv 64 e) with (Z_to_bv 64 v)
end
end.

Section Body2.
Context {RC__ : Q6q3.RunConsts}.

Lemma unreg_body_odr : forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s8 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
(p beg sz szrz nm mo dyn loc k : Z) (junk : list byte) (ob : byte),
mem_inv asegs m ->
ro_cells asegs m 0xf07d8 [C1 (Z_to_bv 8 1)] ->
ro_cells asegs m 0xed310 [C4 (Z_to_bv 64 1)] ->
ro_cells asegs m 0xefaf8 [C8 (Z_to_bv 64 0x7fff8000)] ->
ro_cells asegs m 0xef35c [C1 (Z_to_bv 8 1)] ->
ro_cells asegs m 0x1816a0 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
ro_cells asegs m 0xe7db0 [C8 (Z_to_bv 64 0xdb750)] ->
ro_cells asegs m p [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 sz); CB 8 (le8 (Z_to_bv 64 szrz)); C8 (Z_to_bv 64 nm);
C8 (Z_to_bv 64 mo); C8 (Z_to_bv 64 dyn); C8 (Z_to_bv 64 loc); C8 (Z_to_bv 64 ODR_A)] ->
0xea960 <= p -> p + 64 <= 0xec420 -> p mod 8 = 0 ->
0x10000 <= beg -> beg mod 8 = 0 -> szrz mod 8 = 0 -> 8 <= szrz <= 4096 -> beg + szrz <= 0x645000 ->
rw_cells asegs m (0x7fff8000 + beg / 8) [CB (Z.to_nat (szrz / 8)) junk] ->
rw_cells asegs m ODR_A [C1 ob] ->
1 <= k < 2^32 ->
(forall (ra' a0' a1' a2' a3' a4' a5' a6' a7' s0' t0' t1' t2' t3' t4' t5' t6' : word) (m' : word -> option byte),
munch [(0x7fff8000 + beg / 8, 0x7fff8000 + beg / 8 + szrz / 8); (ODR_A, ODR_A + 1)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
rw_cells asegs m' (0x7fff8000 + beg / 8) [CB (Z.to_nat (szrz / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (szrz / 8)))] ->
rw_cells asegs m' ODR_A [C1 (Z_to_bv 8 0)] ->
evt asegs Q (MS (mkR ra' sp gp tp t0' t1' t2' s0' (Z_to_bv 64 0x181628) a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 2) s3 (Z_to_bv 64 (p + 64)) s5 s6 (Z_to_bv 64 0xe7db0) s8 (Z_to_bv 64 0xed2f8) (Z_to_bv 64 0xefaf8) (Z_to_bv 64 (k - 1)) t3' t4' t5' t6')
F (Z_to_bv 64 (if Z.eqb k 1 then 0x4d680 else 0x4d47c)) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0x181628) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 2) s3 (Z_to_bv 64 p) s5 s6 (Z_to_bv 64 0xe7db0) s8 (Z_to_bv 64 0xed2f8) (Z_to_bv 64 0xefaf8) (Z_to_bv 64 k) t3 t4 t5 t6)
F (Z_to_bv 64 0x4d47c) fc None m (seg_rom asegs)).
Proof.
unfold ODR_A.
intros until ob. intros MI INITED RG SB CP THR RM REC Hp1 Hp2 Hp8 Hb1 Hb8 Hz8 Hz1 Hbe SH ODRB Hk K.
step.
eapply asan_inited_spec; [exact MI | exact INITED |].
replace (ret_pc (Z_to_bv 64 316544)) with (Z_to_bv 64 316544 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step. rewrite ?sxb_small by lia.
if_falsex.
step.
match goal with |- context [sx32 (Z_to_bv 64 1)] => replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (apply bv_eq; vm_compute; reflexivity) end.
step. if_truex.
step. if_falsex.
step. step. step. step. step. step.
fold_closed_bv.
step. if_truex.
step.
replace (Z.land (bv_unsigned (Z_to_bv 64 beg)) 7) with 0 by (rewrite unsigned_lit by lia; change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; lia).
step. if_falsex.
step. rewrite lbu_le8_z by lia.
step. replace (Z.land (bv_unsigned (Z_to_bv 64 (szrz mod 256))) 7) with 0 by (rewrite unsigned_lit by lia; change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; lia).
step. if_falsex.
step.
eapply can_poison_spec; [exact MI | exact CP |].
replace (ret_pc (Z_to_bv 64 316852)) with (Z_to_bv 64 316852 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step. if_falsex.
do 12 step.
rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
rewrite !(unsigned_lit beg) by lia.
rewrite !(unsigned_lit (beg + szrz + -8)) by lia.
replace ((beg + szrz + -8) / 8) with (beg / 8 + szrz / 8 - 1) by lia.
rewrite !unsigned_lit by lia.
replace (2147450880 + (beg / 8 + szrz / 8 - 1) + 1 - (2147450880 + beg / 8)) with (szrz / 8) by lia.
step. if_truex.
step. step. step.
eapply evt_cut; [eapply Q3Gm.Mq0.memset_spec; [rewrite !unsigned_lit by lia; exact SH | exact MI] |].
intros ms' PO. unfold memset_post in PO.
destruct PO as (u0 & u1 & u2 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m1 & E & MU & WM & MI1 & SH1). subst ms'.
rewrite !unsigned_lit in MU by lia. rewrite !unsigned_lit in SH1 by lia.
replace (ret_pc (Z_to_bv 64 0x4d464)) with (Z_to_bv 64 0x4d464 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
assert (DJ : forall A n, A + n <= 0x7fffa000 -> disjoint_from [(2147450880 + beg / 8, 2147450880 + beg / 8 + szrz / 8)] A n).
{ intros A n HA. cbn [disjoint_from]. split; [|exact I]. left. lia. }
pose proof (ro_cells_transport rsegs _ m m1 _ _ REC MU ltac:(apply DJ; cbn; lia)) as REC1.
clear REC. rename REC1 into REC.
pose proof (rw_cells_transport rsegs _ m m1 _ _ ODRB MU WM ltac:(apply DJ; cbn; lia)) as ODRB1.
clear ODRB. rename ODRB1 into ODRB.
step. step. step.
if_truex.
apply (munch_weaken _ [(2147450880 + beg / 8, 2147450880 + beg / 8 + szrz / 8); (0x6221a0, 0x6221a1)]) in MU;
[| intros x Hx; cbn [outside] in Hx |- *; tauto].
stepz.
step. step.
replace (Z_to_bv 64 (k + -1) : word) with (Z_to_bv 64 (k - 1) : word) by (f_equal; lia).
change (0 mod 256) with 0 in SH1.
step.
destruct (Z.eqb_spec k 1) as [Hk1|Hk1].
- subst k. if_falsex. step. cbn [Z.eqb Pos.eqb] in K.
eapply K; [exact MU | exact WM | exact MI1 | exact SH1 | exact ODRB].
- if_truex.
try rewrite (proj2 (Z.eqb_neq k 1) Hk1) in K.
eapply K; [exact MU | exact WM | exact MI1 | exact SH1 | exact ODRB].
Qed.
End Body2.

Definition g_ok2 (r : list Z) : Prop :=
0x10000 <= g_beg r /\ g_beg r mod 8 = 0 /\ g_szrz r mod 8 = 0 /\ 8 <= g_szrz r <= 4096 /\ g_beg r + g_szrz r <= 0x645000
/\ (g_odr r = 0 \/ g_odr r = 2^64 - 1 \/ g_odr r = ODR_A).
Definition W_ODR : Z * Z := (ODR_A, ODR_A + 1).

Section Loop2.
Context {RC__ : Q6q3.RunConsts}.

Lemma shadows_rw_transport2 : forall l r W m m',
shadows_rw m l -> munch (g_sh r :: W) m m' -> wmono asegs m m' ->
(forall A n, 0x7fffa000 <= A -> disjoint_from W A n) ->
Forall (fun r' => g_beg r + g_szrz r <= g_beg r') l -> Forall g_ok2 l -> g_ok2 r ->
shadows_rw m' l.
Proof.
intros l r W m m' H MU WM HW CH OK OKr. unfold shadows_rw in *.
apply Forall_forall. intros r' Hin.
pose proof (proj1 (Forall_forall _ _) H r' Hin) as (junk & RW).
pose proof (proj1 (Forall_forall _ _) CH r' Hin) as LE.
pose proof (proj1 (Forall_forall _ _) OK r' Hin) as OK'. unfold g_ok2 in OK', OKr.
exists junk. eapply rw_cells_transport; [exact RW | exact MU | exact WM |].
unfold g_sh. cbn [disjoint_from fst cells_size csize Nat.add]. split.
- rewrite Nat.add_0_r, Z2Nat.id by lia. right. lia.
- apply HW. unfold g_sh; cbn [fst]. lia.
Qed.

Lemma unreg_loop2 : forall (l : list (list Z)) (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s8 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (p k : Z) (ob : byte),
k = Z.of_nat (length l) -> 1 <= k < 2^32 ->
0xea960 <= p -> p + 64 * k <= 0xec420 -> p mod 8 = 0 ->
mem_inv asegs m ->
ro_cells asegs m 0xf07d8 [C1 (Z_to_bv 8 1)] ->
ro_cells asegs m 0xed310 [C4 (Z_to_bv 64 1)] ->
ro_cells asegs m 0xefaf8 [C8 (Z_to_bv 64 0x7fff8000)] ->
ro_cells asegs m 0xef35c [C1 (Z_to_bv 8 1)] ->
ro_cells asegs m 0x1816a0 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
ro_cells asegs m 0xe7db0 [C8 (Z_to_bv 64 0xdb750)] ->
recs_ro m p l -> Forall g_ok2 l -> chained l -> shadows_rw m l ->
rw_cells asegs m ODR_A [C1 ob] ->
(forall (ra' a0' a1' a2' a3' a4' a5' a6' a7' s0' t0' t1' t2' t3' t4' t5' t6' : word) (m' : word -> option byte) (ob' : byte),
munch (W_ODR :: map g_sh l) m m' -> wmono asegs m m' -> mem_inv asegs m' -> rw_cells asegs m' ODR_A [C1 ob'] ->
evt asegs Q (MS (mkR ra' sp gp tp t0' t1' t2' s0' (Z_to_bv 64 0x181628) a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 2) s3 (Z_to_bv 64 (p + 64 * k)) s5 s6 (Z_to_bv 64 0xe7db0) s8 (Z_to_bv 64 0xed2f8) (Z_to_bv 64 0xefaf8) (Z_to_bv 64 0) t3' t4' t5' t6')
F (Z_to_bv 64 0x4d680) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0x181628) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 2) s3 (Z_to_bv 64 p) s5 s6 (Z_to_bv 64 0xe7db0) s8 (Z_to_bv 64 0xed2f8) (Z_to_bv 64 0xefaf8) (Z_to_bv 64 k) t3 t4 t5 t6)
F (Z_to_bv 64 0x4d47c) fc None m (seg_rom asegs)).
Proof.
induction l as [|r l IH]; intros until ob; intros Hk Hk1 Hp1 Hp2 Hp8 MI INITED RG SB CP THR RM RR OK CH SW ODRB K.
{ cbn [length] in Hk. lia. }
cbn [recs_ro] in RR. destruct RR as [REC RR]. cbn [chained] in CH. destruct CH as [CHr CH].
apply Forall_cons_iff in OK as [OKr OK]. unfold shadows_rw in SW. apply Forall_cons_iff in SW as [[junk SH] SW].
pose proof OKr as OKr'. unfold g_ok2, g_beg, g_szrz, g_odr in OKr'. destruct OKr' as (O1 & O2 & O3 & O4 & O5 & O6).
unfold g_sh, g_beg, g_szrz in SH. cbn [fst] in SH.
cbn [length] in Hk.
assert (DJ : forall A n, A + n <= 0x7fffa000 -> disjoint_from [(2147450880 + nth 0 r 0 / 8, 2147450880 + nth 0 r 0 / 8 + nth 2 r 0 / 8)] A n).
{ intros A n HA. cbn [disjoint_from]. split; [|exact I]. left. lia. }
assert (DJ2 : forall A n, A + n <= ODR_A -> disjoint_from [(2147450880 + nth 0 r 0 / 8, 2147450880 + nth 0 r 0 / 8 + nth 2 r 0 / 8); (ODR_A, ODR_A + 1)] A n).
{ intros A n HA. unfold ODR_A in *. cbn [disjoint_from]. split; [left; lia|]. split; [left; lia | exact I]. }

assert (TAIL : forall (W : list (Z * Z)) (ra' a0' a1' a2' a3' a4' a5' a6' a7' s0' t0' t1' t2' t3' t4' t5' t6' : word) (m1 : word -> option byte) (ob1 : byte),
(W = [] \/ W = [W_ODR]) ->
munch ((2147450880 + nth 0 r 0 / 8, 2147450880 + nth 0 r 0 / 8 + nth 2 r 0 / 8) :: W) m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
rw_cells asegs m1 ODR_A [C1 ob1] ->
evt asegs Q (MS (mkR ra' sp gp tp t0' t1' t2' s0' (Z_to_bv 64 0x181628) a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 2) s3 (Z_to_bv 64 (p + 64)) s5 s6 (Z_to_bv 64 0xe7db0) s8 (Z_to_bv 64 0xed2f8) (Z_to_bv 64 0xefaf8) (Z_to_bv 64 (k - 1)) t3' t4' t5' t6')
F (Z_to_bv 64 (if Z.eqb k 1 then 0x4d680 else 0x4d47c)) fc None m1 (seg_rom asegs))).
{ intros W ra' a0' a1' a2' a3' a4' a5' a6' a7' s0' t0' t1' t2' t3' t4' t5' t6' m1 ob1 HWc MU WM MI1 ODRB1.
assert (HW : forall A n, 0x7fffa000 <= A -> disjoint_from W A n).
{ intros A n HA. destruct HWc as [-> | ->]; cbn [disjoint_from W_ODR]; [exact I|]. unfold W_ODR, ODR_A. split; [right; lia | exact I]. }
assert (HWlo : forall A n, A + n <= ODR_A -> disjoint_from ((2147450880 + nth 0 r 0 / 8, 2147450880 + nth 0 r 0 / 8 + nth 2 r 0 / 8) :: W) A n).
{ intros A n HA. destruct HWc as [-> | ->]; [apply DJ; unfold ODR_A in HA; lia | apply DJ2; exact HA]. }
assert (SUB1 : sub_fp ((2147450880 + nth 0 r 0 / 8, 2147450880 + nth 0 r 0 / 8 + nth 2 r 0 / 8) :: W) (W_ODR :: map g_sh (r :: l))).
{ intros x Hx. cbn [map outside W_ODR] in Hx. unfold g_sh at 1 in Hx. unfold g_beg, g_szrz in Hx.
destruct HWc as [-> | ->]; cbn [outside W_ODR]; tauto. }
destruct (Z.eqb_spec k 1) as [Hk0|Hk0].
-
destruct l; [|cbn [length] in Hk; lia].
rewrite Hk0 in *.
replace (p + 64 * 1) with (p + 64) in K by lia.
eapply K; [| exact WM | exact MI1 | exact ODRB1].
eapply munch_join; [exact MU | apply munch_refl | exact SUB1 | intros x Hx; exact Hx].
-
eapply (IH ra' sp gp tp t0' t1' t2' s0' a0' a1' a2' a3' a4' a5' a6' a7' s3 s5 s6 s8 t3' t4' t5' t6' F fc m1 Q (p + 64) (k - 1) ob1);
try lia.
+ exact MI1.
+ eapply ro_cells_transport; [exact INITED | exact MU | apply HWlo; cbn; unfold ODR_A; lia].
+ eapply ro_cells_transport; [exact RG | exact MU | apply HWlo; cbn; unfold ODR_A; lia].
+ eapply ro_cells_transport; [exact SB | exact MU | apply HWlo; cbn; unfold ODR_A; lia].
+ eapply ro_cells_transport; [exact CP | exact MU | apply HWlo; cbn; unfold ODR_A; lia].
+ eapply ro_cells_transport; [exact THR | exact MU | apply HWlo; cbn; unfold ODR_A; lia].
+ eapply ro_cells_transport; [exact RM | exact MU | apply HWlo; cbn; unfold ODR_A; lia].
+ eapply recs_ro_transport; [exact RR | exact MU |]. intros q Hq1 Hq2. apply HWlo. unfold ODR_A. lia.
+ exact OK.
+ exact CH.
+ eapply (shadows_rw_transport2 l r W m m1); [exact SW | unfold g_sh, g_beg, g_szrz; exact MU | exact WM | exact HW | exact CHr | exact OK | exact OKr].
+ exact ODRB1.
+ intros ra'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' s0'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' m2 ob2 MU2 WM2 MI2 ODRB2.
replace (p + 64 + 64 * (k - 1)) with (p + 64 * k) by lia.
eapply K; [| eapply wmono_trans; [exact WM | exact WM2] | exact MI2 | exact ODRB2].
eapply munch_join; [exact MU | exact MU2 | exact SUB1 |].
intros x Hx. cbn [map outside W_ODR] in Hx |- *. unfold g_sh at 1 in Hx. cbn iota beta in Hx. tauto. }
destruct O6 as [O6 | [O6 | O6]].
1,2: eapply (unreg_body ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s8 t3 t4 t5 t6 F fc m Q
p (nth 0 r 0) (nth 1 r 0) (nth 2 r 0) (nth 3 r 0) (nth 4 r 0) (nth 5 r 0) (nth 6 r 0) (nth 7 r 0) k junk
MI INITED RG SB CP THR RM REC); try lia; try exact SH;
intros ra' a0' a1' a2' a3' a4' a5' a6' a7' s0' t0' t1' t2' t3' t4' t5' t6' m1 MU WM MI1 SH1;
eapply (TAIL []); [left; reflexivity | exact MU | exact WM | exact MI1 |];
eapply rw_cells_transport; [exact ODRB | exact MU | exact WM | apply DJ; cbn; unfold ODR_A; lia].
-
unfold g_cells in REC. rewrite O6 in REC.
eapply (unreg_body_odr ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s8 t3 t4 t5 t6 F fc m Q
p (nth 0 r 0) (nth 1 r 0) (nth 2 r 0) (nth 3 r 0) (nth 4 r 0) (nth 5 r 0) (nth 6 r 0) k junk ob
MI INITED RG SB CP THR RM REC); try lia; try exact SH; try exact ODRB.
intros ra' a0' a1' a2' a3' a4' a5' a6' a7' s0' t0' t1' t2' t3' t4' t5' t6' m1 MU WM MI1 SH1 ODRB1.
eapply (TAIL [W_ODR]); [right; reflexivity | exact MU | exact WM | exact MI1 | exact ODRB1].
Qed.
End Loop2.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJZd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJZd.Mqg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3Gm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3Gm.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGm2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGm2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QhtD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QhtD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbKA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbKA.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition ODR_A : Z := 0x624860.

Lemma munch_join : forall W1 W2 W m m1 m2,
munch W1 m m1 -> munch W2 m1 m2 -> sub_fp W1 W -> sub_fp W2 W -> munch W m m2.
Proof. intros W1 W2 W m m1 m2 M1 M2 S1 S2 x Hx. rewrite (M2 x (S2 _ Hx)). apply M1, S1, Hx. Qed.

Ltac fold_closed_bv :=
repeat match goal with
| |- evt _ _ (MS ?R _ _ _ _ _ _) =>
match R with context [Z_to_bv 64 ?e] =>
lazymatch e with
| Z.land _ _ => idtac | Z.lor _ _ => idtac | Z.add _ _ => idtac | bv_unsigned _ => idtac | Z.shiftr _ _ => idtac | Z.shiftl _ _ => idtac | Z.sub _ _ => idtac | Z.mul _ _ => idtac | Z.modulo _ _ => idtac
end;
let v := eval vm_compute in e in
lazymatch v with
| Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac
end;
change (Z_to_bv 64 e) with (Z_to_bv 64 v)
end
end.

Section Body2.
Context {RC__ : Q6q3.RunConsts}.

Lemma unreg_body_odr : forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s8 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
(p beg sz szrz nm mo dyn loc k : Z) (junk : list byte) (ob : byte),
mem_inv asegs m ->
ro_cells asegs m 0xf2e98 [C1 (Z_to_bv 8 1)] ->
ro_cells asegs m 0xef9d0 [C4 (Z_to_bv 64 1)] ->
ro_cells asegs m 0xf21b8 [C8 (Z_to_bv 64 0x7fff8000)] ->
ro_cells asegs m 0xf1a1c [C1 (Z_to_bv 8 1)] ->
ro_cells asegs m 0x183d60 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
ro_cells asegs m 0xea1d0 [C8 (Z_to_bv 64 0xdde14)] ->
ro_cells asegs m p [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 sz); CB 8 (le8 (Z_to_bv 64 szrz)); C8 (Z_to_bv 64 nm);
C8 (Z_to_bv 64 mo); C8 (Z_to_bv 64 dyn); C8 (Z_to_bv 64 loc); C8 (Z_to_bv 64 ODR_A)] ->
0xed040 <= p -> p + 64 <= 0xeeb00 -> p mod 8 = 0 ->
0x10000 <= beg -> beg mod 8 = 0 -> szrz mod 8 = 0 -> 8 <= szrz <= 4096 -> beg + szrz <= 0x647000 ->
rw_cells asegs m (0x7fff8000 + beg / 8) [CB (Z.to_nat (szrz / 8)) junk] ->
rw_cells asegs m ODR_A [C1 ob] ->
1 <= k < 2^32 ->
(forall (ra' a0' a1' a2' a3' a4' a5' a6' a7' s0' t0' t1' t2' t3' t4' t5' t6' : word) (m' : word -> option byte),
munch [(0x7fff8000 + beg / 8, 0x7fff8000 + beg / 8 + szrz / 8); (ODR_A, ODR_A + 1)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
rw_cells asegs m' (0x7fff8000 + beg / 8) [CB (Z.to_nat (szrz / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (szrz / 8)))] ->
rw_cells asegs m' ODR_A [C1 (Z_to_bv 8 0)] ->
evt asegs Q (MS (mkR ra' sp gp tp t0' t1' t2' s0' (Z_to_bv 64 0x183ce8) a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 2) s3 (Z_to_bv 64 (p + 64)) s5 s6 (Z_to_bv 64 0xea1d0) s8 (Z_to_bv 64 0xef9b8) (Z_to_bv 64 0xf21b8) (Z_to_bv 64 (k - 1)) t3' t4' t5' t6')
F (Z_to_bv 64 (if Z.eqb k 1 then 0x4da58 else 0x4d854)) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0x183ce8) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 2) s3 (Z_to_bv 64 p) s5 s6 (Z_to_bv 64 0xea1d0) s8 (Z_to_bv 64 0xef9b8) (Z_to_bv 64 0xf21b8) (Z_to_bv 64 k) t3 t4 t5 t6)
F (Z_to_bv 64 0x4d854) fc None m (seg_rom asegs)).
Proof.
unfold ODR_A.
intros until ob. intros MI INITED RG SB CP THR RM REC Hp1 Hp2 Hp8 Hb1 Hb8 Hz8 Hz1 Hbe SH ODRB Hk K.
step.
eapply asan_inited_spec; [exact MI | exact INITED |].
replace (ret_pc (Z_to_bv 64 317528)) with (Z_to_bv 64 317528 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step. rewrite ?sxb_small by lia.
if_falsex.
step.
match goal with |- context [sx32 (Z_to_bv 64 1)] => replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (apply bv_eq; vm_compute; reflexivity) end.
step. if_truex.
step. if_falsex.
step. step. step. step. step. step.
fold_closed_bv.
step. if_truex.
step.
replace (Z.land (bv_unsigned (Z_to_bv 64 beg)) 7) with 0 by (rewrite unsigned_lit by lia; change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; lia).
step. if_falsex.
step. rewrite lbu_le8_z by lia.
step. replace (Z.land (bv_unsigned (Z_to_bv 64 (szrz mod 256))) 7) with 0 by (rewrite unsigned_lit by lia; change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; lia).
step. if_falsex.
step.
eapply can_poison_spec; [exact MI | exact CP |].
replace (ret_pc (Z_to_bv 64 317836)) with (Z_to_bv 64 317836 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step. if_falsex.
do 12 step.
rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
rewrite !(unsigned_lit beg) by lia.
rewrite !(unsigned_lit (beg + szrz + -8)) by lia.
replace ((beg + szrz + -8) / 8) with (beg / 8 + szrz / 8 - 1) by lia.
rewrite !unsigned_lit by lia.
replace (2147450880 + (beg / 8 + szrz / 8 - 1) + 1 - (2147450880 + beg / 8)) with (szrz / 8) by lia.
step. if_truex.
step. step. step.
eapply evt_cut; [eapply Q3Gm.memset_spec; [rewrite !unsigned_lit by lia; exact SH | exact MI] |].
intros ms' PO. unfold memset_post in PO.
destruct PO as (u0 & u1 & u2 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m1 & E & MU & WM & MI1 & SH1). subst ms'.
rewrite !unsigned_lit in MU by lia. rewrite !unsigned_lit in SH1 by lia.
replace (ret_pc (Z_to_bv 64 0x4d83c)) with (Z_to_bv 64 0x4d83c : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
assert (DJ : forall A n, A + n <= 0x7fffa000 -> disjoint_from [(2147450880 + beg / 8, 2147450880 + beg / 8 + szrz / 8)] A n).
{ intros A n HA. cbn [disjoint_from]. split; [|exact I]. left. lia. }
pose proof (ro_cells_transport rsegs _ m m1 _ _ REC MU ltac:(apply DJ; cbn; lia)) as REC1.
clear REC. rename REC1 into REC.
pose proof (rw_cells_transport rsegs _ m m1 _ _ ODRB MU WM ltac:(apply DJ; cbn; lia)) as ODRB1.
clear ODRB. rename ODRB1 into ODRB.
step. step. step.
if_truex.
apply (munch_weaken _ [(2147450880 + beg / 8, 2147450880 + beg / 8 + szrz / 8); (0x624860, 0x624861)]) in MU;
[| intros x Hx; cbn [outside] in Hx |- *; tauto].
stepz.
step. step.
replace (Z_to_bv 64 (k + -1) : word) with (Z_to_bv 64 (k - 1) : word) by (f_equal; lia).
change (0 mod 256) with 0 in SH1.
step.
destruct (Z.eqb_spec k 1) as [Hk1|Hk1].
- subst k. if_falsex. step. cbn [Z.eqb Pos.eqb] in K.
eapply K; [exact MU | exact WM | exact MI1 | exact SH1 | exact ODRB].
- if_truex.
try rewrite (proj2 (Z.eqb_neq k 1) Hk1) in K.
eapply K; [exact MU | exact WM | exact MI1 | exact SH1 | exact ODRB].
Qed.
End Body2.

Definition g_ok2 (r : list Z) : Prop :=
0x10000 <= g_beg r /\ g_beg r mod 8 = 0 /\ g_szrz r mod 8 = 0 /\ 8 <= g_szrz r <= 4096 /\ g_beg r + g_szrz r <= 0x647000
/\ (g_odr r = 0 \/ g_odr r = 2^64 - 1 \/ g_odr r = ODR_A).
Definition W_ODR : Z * Z := (ODR_A, ODR_A + 1).

Section Loop2.
Context {RC__ : Q6q3.RunConsts}.

Lemma shadows_rw_transport2 : forall l r W m m',
shadows_rw m l -> munch (g_sh r :: W) m m' -> wmono asegs m m' ->
(forall A n, 0x7fffa000 <= A -> disjoint_from W A n) ->
Forall (fun r' => g_beg r + g_szrz r <= g_beg r') l -> Forall g_ok2 l -> g_ok2 r ->
shadows_rw m' l.
Proof.
intros l r W m m' H MU WM HW CH OK OKr. unfold shadows_rw in *.
apply Forall_forall. intros r' Hin.
pose proof (proj1 (Forall_forall _ _) H r' Hin) as (junk & RW).
pose proof (proj1 (Forall_forall _ _) CH r' Hin) as LE.
pose proof (proj1 (Forall_forall _ _) OK r' Hin) as OK'. unfold g_ok2 in OK', OKr.
exists junk. eapply rw_cells_transport; [exact RW | exact MU | exact WM |].
unfold g_sh. cbn [disjoint_from fst cells_size csize Nat.add]. split.
- rewrite Nat.add_0_r, Z2Nat.id by lia. right. lia.
- apply HW. unfold g_sh; cbn [fst]. lia.
Qed.

Lemma unreg_loop2 : forall (l : list (list Z)) (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s8 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (p k : Z) (ob : byte),
k = Z.of_nat (length l) -> 1 <= k < 2^32 ->
0xed040 <= p -> p + 64 * k <= 0xeeb00 -> p mod 8 = 0 ->
mem_inv asegs m ->
ro_cells asegs m 0xf2e98 [C1 (Z_to_bv 8 1)] ->
ro_cells asegs m 0xef9d0 [C4 (Z_to_bv 64 1)] ->
ro_cells asegs m 0xf21b8 [C8 (Z_to_bv 64 0x7fff8000)] ->
ro_cells asegs m 0xf1a1c [C1 (Z_to_bv 8 1)] ->
ro_cells asegs m 0x183d60 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
ro_cells asegs m 0xea1d0 [C8 (Z_to_bv 64 0xdde14)] ->
recs_ro m p l -> Forall g_ok2 l -> chained l -> shadows_rw m l ->
rw_cells asegs m ODR_A [C1 ob] ->
(forall (ra' a0' a1' a2' a3' a4' a5' a6' a7' s0' t0' t1' t2' t3' t4' t5' t6' : word) (m' : word -> option byte) (ob' : byte),
munch (W_ODR :: map g_sh l) m m' -> wmono asegs m m' -> mem_inv asegs m' -> rw_cells asegs m' ODR_A [C1 ob'] ->
evt asegs Q (MS (mkR ra' sp gp tp t0' t1' t2' s0' (Z_to_bv 64 0x183ce8) a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 2) s3 (Z_to_bv 64 (p + 64 * k)) s5 s6 (Z_to_bv 64 0xea1d0) s8 (Z_to_bv 64 0xef9b8) (Z_to_bv 64 0xf21b8) (Z_to_bv 64 0) t3' t4' t5' t6')
F (Z_to_bv 64 0x4da58) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0x183ce8) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 2) s3 (Z_to_bv 64 p) s5 s6 (Z_to_bv 64 0xea1d0) s8 (Z_to_bv 64 0xef9b8) (Z_to_bv 64 0xf21b8) (Z_to_bv 64 k) t3 t4 t5 t6)
F (Z_to_bv 64 0x4d854) fc None m (seg_rom asegs)).
Proof.
induction l as [|r l IH]; intros until ob; intros Hk Hk1 Hp1 Hp2 Hp8 MI INITED RG SB CP THR RM RR OK CH SW ODRB K.
{ cbn [length] in Hk. lia. }
cbn [recs_ro] in RR. destruct RR as [REC RR]. cbn [chained] in CH. destruct CH as [CHr CH].
apply Forall_cons_iff in OK as [OKr OK]. unfold shadows_rw in SW. apply Forall_cons_iff in SW as [[junk SH] SW].
pose proof OKr as OKr'. unfold g_ok2, g_beg, g_szrz, g_odr in OKr'. destruct OKr' as (O1 & O2 & O3 & O4 & O5 & O6).
unfold g_sh, g_beg, g_szrz in SH. cbn [fst] in SH.
cbn [length] in Hk.
assert (DJ : forall A n, A + n <= 0x7fffa000 -> disjoint_from [(2147450880 + nth 0 r 0 / 8, 2147450880 + nth 0 r 0 / 8 + nth 2 r 0 / 8)] A n).
{ intros A n HA. cbn [disjoint_from]. split; [|exact I]. left. lia. }
assert (DJ2 : forall A n, A + n <= ODR_A -> disjoint_from [(2147450880 + nth 0 r 0 / 8, 2147450880 + nth 0 r 0 / 8 + nth 2 r 0 / 8); (ODR_A, ODR_A + 1)] A n).
{ intros A n HA. unfold ODR_A in *. cbn [disjoint_from]. split; [left; lia|]. split; [left; lia | exact I]. }

assert (TAIL : forall (W : list (Z * Z)) (ra' a0' a1' a2' a3' a4' a5' a6' a7' s0' t0' t1' t2' t3' t4' t5' t6' : word) (m1 : word -> option byte) (ob1 : byte),
(W = [] \/ W = [W_ODR]) ->
munch ((2147450880 + nth 0 r 0 / 8, 2147450880 + nth 0 r 0 / 8 + nth 2 r 0 / 8) :: W) m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
rw_cells asegs m1 ODR_A [C1 ob1] ->
evt asegs Q (MS (mkR ra' sp gp tp t0' t1' t2' s0' (Z_to_bv 64 0x183ce8) a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 2) s3 (Z_to_bv 64 (p + 64)) s5 s6 (Z_to_bv 64 0xea1d0) s8 (Z_to_bv 64 0xef9b8) (Z_to_bv 64 0xf21b8) (Z_to_bv 64 (k - 1)) t3' t4' t5' t6')
F (Z_to_bv 64 (if Z.eqb k 1 then 0x4da58 else 0x4d854)) fc None m1 (seg_rom asegs))).
{ intros W ra' a0' a1' a2' a3' a4' a5' a6' a7' s0' t0' t1' t2' t3' t4' t5' t6' m1 ob1 HWc MU WM MI1 ODRB1.
assert (HW : forall A n, 0x7fffa000 <= A -> disjoint_from W A n).
{ intros A n HA. destruct HWc as [-> | ->]; cbn [disjoint_from W_ODR]; [exact I|]. unfold W_ODR, ODR_A. split; [right; lia | exact I]. }
assert (HWlo : forall A n, A + n <= ODR_A -> disjoint_from ((2147450880 + nth 0 r 0 / 8, 2147450880 + nth 0 r 0 / 8 + nth 2 r 0 / 8) :: W) A n).
{ intros A n HA. destruct HWc as [-> | ->]; [apply DJ; unfold ODR_A in HA; lia | apply DJ2; exact HA]. }
assert (SUB1 : sub_fp ((2147450880 + nth 0 r 0 / 8, 2147450880 + nth 0 r 0 / 8 + nth 2 r 0 / 8) :: W) (W_ODR :: map g_sh (r :: l))).
{ intros x Hx. cbn [map outside W_ODR] in Hx. unfold g_sh at 1 in Hx. unfold g_beg, g_szrz in Hx.
destruct HWc as [-> | ->]; cbn [outside W_ODR]; tauto. }
destruct (Z.eqb_spec k 1) as [Hk0|Hk0].
-
destruct l; [|cbn [length] in Hk; lia].
rewrite Hk0 in *.
replace (p + 64 * 1) with (p + 64) in K by lia.
eapply K; [| exact WM | exact MI1 | exact ODRB1].
eapply munch_join; [exact MU | apply munch_refl | exact SUB1 | intros x Hx; exact Hx].
-
eapply (IH ra' sp gp tp t0' t1' t2' s0' a0' a1' a2' a3' a4' a5' a6' a7' s3 s5 s6 s8 t3' t4' t5' t6' F fc m1 Q (p + 64) (k - 1) ob1);
try lia.
+ exact MI1.
+ eapply ro_cells_transport; [exact INITED | exact MU | apply HWlo; cbn; unfold ODR_A; lia].
+ eapply ro_cells_transport; [exact RG | exact MU | apply HWlo; cbn; unfold ODR_A; lia].
+ eapply ro_cells_transport; [exact SB | exact MU | apply HWlo; cbn; unfold ODR_A; lia].
+ eapply ro_cells_transport; [exact CP | exact MU | apply HWlo; cbn; unfold ODR_A; lia].
+ eapply ro_cells_transport; [exact THR | exact MU | apply HWlo; cbn; unfold ODR_A; lia].
+ eapply ro_cells_transport; [exact RM | exact MU | apply HWlo; cbn; unfold ODR_A; lia].
+ eapply recs_ro_transport; [exact RR | exact MU |]. intros q Hq1 Hq2. apply HWlo. unfold ODR_A. lia.
+ exact OK.
+ exact CH.
+ eapply (shadows_rw_transport2 l r W m m1); [exact SW | unfold g_sh, g_beg, g_szrz; exact MU | exact WM | exact HW | exact CHr | exact OK | exact OKr].
+ exact ODRB1.
+ intros ra'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' s0'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' m2 ob2 MU2 WM2 MI2 ODRB2.
replace (p + 64 + 64 * (k - 1)) with (p + 64 * k) by lia.
eapply K; [| eapply wmono_trans; [exact WM | exact WM2] | exact MI2 | exact ODRB2].
eapply munch_join; [exact MU | exact MU2 | exact SUB1 |].
intros x Hx. cbn [map outside W_ODR] in Hx |- *. unfold g_sh at 1 in Hx. cbn iota beta in Hx. tauto. }
destruct O6 as [O6 | [O6 | O6]].
1,2: eapply (unreg_body ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s8 t3 t4 t5 t6 F fc m Q
p (nth 0 r 0) (nth 1 r 0) (nth 2 r 0) (nth 3 r 0) (nth 4 r 0) (nth 5 r 0) (nth 6 r 0) (nth 7 r 0) k junk
MI INITED RG SB CP THR RM REC); try lia; try exact SH;
intros ra' a0' a1' a2' a3' a4' a5' a6' a7' s0' t0' t1' t2' t3' t4' t5' t6' m1 MU WM MI1 SH1;
eapply (TAIL []); [left; reflexivity | exact MU | exact WM | exact MI1 |];
eapply rw_cells_transport; [exact ODRB | exact MU | exact WM | apply DJ; cbn; unfold ODR_A; lia].
-
unfold g_cells in REC. rewrite O6 in REC.
eapply (unreg_body_odr ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s8 t3 t4 t5 t6 F fc m Q
p (nth 0 r 0) (nth 1 r 0) (nth 2 r 0) (nth 3 r 0) (nth 4 r 0) (nth 5 r 0) (nth 6 r 0) k junk ob
MI INITED RG SB CP THR RM REC); try lia; try exact SH; try exact ODRB.
intros ra' a0' a1' a2' a3' a4' a5' a6' a7' s0' t0' t1' t2' t3' t4' t5' t6' m1 MU WM MI1 SH1 ODRB1.
eapply (TAIL [W_ODR]); [right; reflexivity | exact MU | exact WM | exact MI1 | exact ODRB1].
Qed.
End Loop2.
