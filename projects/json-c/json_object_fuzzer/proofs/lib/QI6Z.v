(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Q5Rg Lib.GwApply QRjH QHnV QCcH QfLs Q0Ek QTEu Qsw7 QJjn QRUw QnCn QZCq QSK8 Q7UD Qhd4 Qwm6 QlKV QsKa QgoM Q30W Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek. Import QTEu. Import Qsw7 QJjn QRUw.
Import QnCn.Mq0. Import QZCq QSK8.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq7 QgoM.Mq1 QsKa.Mq3 Q30W.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Definition array_list_del_idx_A_entry : Z := 0xa0a18.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma al_del_loopA :
forall (k : nat) (i : Z) (x1 x2 gp tp t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 x19 x20 x21 x24 x26 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a arr len size stop : Z) (qs : list Z) (idx : Z),
Z.of_nat k = stop - 1 - i -> idx <= i < stop -> stop = Z.of_nat (length qs) -> stop <= len -> len <= size -> 8 * size < 2^64 ->
0 <= idx -> (forall j, idx <= j < stop -> al_nth qs j = 0) ->
mem_inv asegs m -> 0 < a -> a mod 8 = 0 -> a + AL_SZ <= alloc_ceiling -> 0 < arr -> arr mod 8 = 0 -> arr + 8 * size <= alloc_ceiling ->
rw_cells asegs m a [C8 (Z_to_bv 64 arr); C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 (fn_arr_entry_free A4F))] ->
u64arr asegs m arr (wl qs) ->
ro_cells asegs m (a / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
bytes_at asegs m (arr / 8 + A_SB) (shadow_bytes (8 * size)) ->
evt asegs (eq (MS (mkR x1 x2 gp tp t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 (a + 8)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 len) a3 a4 a5 a6 a7
(Z_to_bv 64 a) x19 x20 x21 (Z_to_bv 64 A_SB) (Z_to_bv 64 stop) x24 (Z_to_bv 64 (a / 8 + A_SB)) x26 (Z_to_bv 64 (8 * stop)) t3 t4 t5 t6)
F (Z_to_bv 64 0xa0b08) fc None m (seg_rom asegs)))
(MS (mkR x1 x2 gp tp t0 t1 t2 (Z_to_bv 64 (stop - i)) (Z_to_bv 64 (a + 8)) a0 a1 (Z_to_bv 64 len) a3 a4 a5 a6 a7
(Z_to_bv 64 a) x19 x20 x21 (Z_to_bv 64 A_SB) (Z_to_bv 64 stop) x24 (Z_to_bv 64 (a / 8 + A_SB)) x26 (Z_to_bv 64 (8 * i)) t3 t4 t5 t6)
F (Z_to_bv 64 0xa0acc) fc None m (seg_rom asegs)).
Proof.
induction k as [|k IH]; intros until idx; intros Hk Hi Hstop Hsl Hls H64 Hidx NUL MI Ha0 Ha8 Hah Hr0 Hr8 Hrh HDR ARR SHa SHr; unfold A_SB in *;
pose proof (u64arr_bound asegs m arr (wl qs) ARR) as AB; rewrite wl_length in AB;
pose proof (munch_refl [] m) as MU; pose proof (wmono_refl asegs m) as WM;
pose proof (ov_read1_of_ro asegs _ _ _ (shadow_granule0 asegs m (arr / 8 + 2147450880) (8 * size) i ltac:(lia) ltac:(lia) SHr)) as HR.
- step. rewrite ?zxb_zero. step. if_false.
step. step.
step. step. sh_norm.
replace ((arr + 8 * i) / 8 + 2147450880) with (arr / 8 + 2147450880 + i) by (Z.div_mod_to_equations; lia).
step. rewrite ?zxb_zero. clear HR. step. if_false.
pose proof (al_slot_read asegs m arr qs i (wa (arr + 8 * i)) ARR ltac:(lia) eq_refl) as RD.
rewrite (NUL i) in RD by lia.
step. step. if_true.
step. step. step. if_truex.
apply evt_done. replace (stop - i + -1) with 0 by lia. replace (8 * i + 8) with (8 * stop) by lia. reflexivity.
- step. rewrite ?zxb_zero. step. if_false.
step. step.
step. step. sh_norm.
replace ((arr + 8 * i) / 8 + 2147450880) with (arr / 8 + 2147450880 + i) by (Z.div_mod_to_equations; lia).
step. rewrite ?zxb_zero. clear HR. step. if_false.
pose proof (al_slot_read asegs m arr qs i (wa (arr + 8 * i)) ARR ltac:(lia) eq_refl) as RD.
rewrite (NUL i) in RD by lia.
step. step. if_true.
step. step. step. if_falsex.
replace (stop - i + -1) with (stop - (i + 1)) by lia. replace (8 * i + 8) with (8 * (i + 1)) by lia.
eapply (IH (i + 1)); [ | | exact Hstop | exact Hsl | exact Hls | exact H64 | exact Hidx | exact NUL | exact MI | | | | | | | exact HDR | exact ARR | exact SHa | exact SHr]; lia.
Qed.

Section Regs.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).

Definition array_list_del_idx_A_post (a arr size : Z) (ps zs : list Z) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (match zs with [] => 2^64 - 1 | _ => 0 end)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp); (a, a + AL_SZ); (arr, arr + 8 * size)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ alist asegs A4F m' [(a, AL_SZ); (arr, 8 * size)] a ps.

Lemma array_list_del_idx_A :
forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
(m : word -> option byte) (lo sbcell a arr size : Z) (ps zs : list Z),
small_pre sp m lo sbcell -> lo <= bv_unsigned sp - 112 - 4096 -> asan_rt_ok m ->
alist asegs A4F m [(a, AL_SZ); (arr, 8 * size)] a (ps ++ zs) ->
Forall (fun p => p = 0) zs ->
(a + AL_SZ <= arr \/ arr + 8 * size <= a) ->
al_blkA a arr size ->
ro_cells asegs m (a / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
bytes_at asegs m (arr / 8 + A_SB) (shadow_bytes (8 * size)) ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 (Z.of_nat (length ps)) -> a2 = Z_to_bv 64 (Z.of_nat (length zs)) ->
evt asegs (array_list_del_idx_A_post a arr size ps zs lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 array_list_del_idx_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until zs. intros (MI & ST & LOS16 & LO & GOT & CELL & Hc0 & Hc8) LOS RT AL NUL SEP (Ha0 & Ha8 & Hah & Hr0 & Hr8 & Hrh) SHa SHr SPA RA A0 A1 A2.
destruct (alist_openx asegs A4F m a arr size (ps ++ zs) AL) as (junk & HDR & ARR & JK & Hlen & Hsz).
unfold al_hdr in HDR. unfold al_tail in JK.
pose proof (length_app ps zs) as LA. apply (f_equal Z.of_nat) in LA. rewrite Nat2Z.inj_add in LA. rewrite LA in HDR.
pose proof (u64arr_bound asegs m arr (wl (ps ++ zs)) ARR) as AB. rewrite wl_length in AB.
pose proof (wl_length (ps ++ zs)) as WL.
unfold array_list_del_idx_A_entry, array_list_del_idx_A_post, A_GOT_SB, A_SB in *.
unfold alloc_ceiling, sp_window_lo, stack_max_size in LO, Hc8, Hah, Hrh. word_range sp SPR. subst a0 a1 a2.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU.
apply slots_of_u64arr in ARR. stash SHr. stash ARR. stash JK. stash RT.
carve_frame 112%nat ST.
do 14 step.
step. step. step.
unfold v_xori. rewrite (unsigned_lit (Z.of_nat (length zs))) by lia. change (bv_wrap 64 (-1)) with 18446744073709551615.
rewrite lxor_ones64 by lia.
step. step. if_falsex.
step. step. step.
step.
asan_chkA.
step.
destruct zs as [|z zs'].
-
change (Z.of_nat (@length Z [])) with 0 in *. rewrite app_nil_r in *. rewrite Z.add_0_r in *. clear LA.
step. if_truex.
do 15 step.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
unstash ARR. unstash JK.
apply evt_done. do 15 eexists. split; [reflexivity|].
split. { eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia. }
split; [exact WM|]. split; [assumption|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|].
lazymatch goal with |- alist _ _ ?mf _ _ _ =>
eapply (rw_cells_transport asegs _ m mf) in ARR; [| exact MU | exact WM | cbn [disjoint_from]; rewrite slots_size; lia];
eapply (rw_cells_transport asegs _ m mf) in JK; [| exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; lia] end.
eapply alist_close. split; [| split; [apply u64arr_of_slots; exact ARR | split; [exact JK | lia]]]. unfold al_hdr. assumption.
- assert (LZ : 1 <= Z.of_nat (length (z :: zs'))) by (cbn [length]; lia).
step. if_falsex.
step. step. if_falsex.
step. rewrite (unsigned_lit (Z.of_nat (length ps))) by lia. rewrite (Z.shiftl_mul_pow2 (Z.of_nat (length ps)) 3) by lia. change (2^3) with 8.
step.
step. sh_norm.
step. if_falsex.
step. step. step. step. sh_norm. step. step. step.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
assert (LEN2 : length (ps ++ z :: zs') = (length ps + S (length zs'))%nat) by (rewrite length_app; reflexivity).
unstash ARR. unstash JK. unstash SHr. unstash RT.
eapply (rw_cells_transport asegs _ m m1) in ARR; [| exact MU | exact WM | cbn [disjoint_from]; rewrite slots_size; lia].
eapply (rw_cells_transport asegs _ m m1) in JK; [| exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; rewrite <- ?LEN2; lia].
eapply (bytes_at_transport asegs _ m m1) in SHr; [| exact MU | cbn [disjoint_from]; rewrite shadow_bytes_length8 by lia; lia].
eapply (asan_rt_ok_transport _ m m1) in RT; [| exact MU | intros c Hc; pose proof (a4_rt_cells_in_img c Hc); cbn [disjoint_from]; lia].
apply u64arr_of_slots in ARR.
replace (Z.of_nat (length ps) * 8) with (8 * Z.of_nat (length ps)) by lia.
replace (Z_to_bv 64 (Z.of_nat (length (z :: zs')))) with (Z_to_bv 64 (Z.of_nat (length (z :: zs')) + Z.of_nat (length ps) - Z.of_nat (length ps))) at 1 by (f_equal; lia).
eapply evt_cut.
{ eapply al_del_loopA with (k := Z.to_nat (Z.of_nat (length (z :: zs')) - 1)) (i := Z.of_nat (length ps))
(a := a) (arr := arr) (len := Z.of_nat (length ps) + Z.of_nat (length (z :: zs'))) (size := size)
(stop := Z.of_nat (length (z :: zs')) + Z.of_nat (length ps)) (qs := ps ++ z :: zs') (idx := Z.of_nat (length ps));
[ | | | | | | | | assumption | | | | | | | exact HDR | exact ARR | unfold A_SB; eassumption | unfold A_SB; exact SHr ]; try lia.
intros j Hj. apply al_nth_app_r; [lia | exact NUL]. }
intros ms' <-. unfold A_SB.

destruct (al_tail_absorb asegs m1 arr size ps (z :: zs') junk ARR JK ltac:(lia)) as [ARR1 TL]. clear ARR JK.
unfold al_tail in TL.
pose proof (wl_length ps) as WL1.
step.
step. rewrite ?zxb_zero. step. if_false.
step. rewrite ?zxb_zero. step. if_false.
step. step.
step. rewrite (unsigned_lit (Z.of_nat (length (z :: zs')) + Z.of_nat (length ps))) by lia.
rewrite (Z.shiftl_mul_pow2 (Z.of_nat (length (z :: zs')) + Z.of_nat (length ps)) 3) by lia. change (2^3) with 8.
step.
step. step.
step. rewrite !unsigned_lit by lia.
replace (Z.of_nat (length ps) + Z.of_nat (length (z :: zs')) - (Z.of_nat (length (z :: zs')) + Z.of_nat (length ps))) with 0 by lia.
step.
step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (DST : rw_cells asegs mc (arr + 8 * Z.of_nat (length ps)) [CB 0%nat []])
by (split; [split; [cbn; auto | cbn; apply bytes_at_nil; lia] | cbn; split; [lia | split; [lia | intros i Hi; lia]]]);
assert (MU2 : munch [(lo, bv_unsigned sp); (a, a + 32); (arr, arr + 8 * size)] m mc)
by (eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia)
end.
clear MU. rename MU2 into MU.
eapply amemmove_sound_U with (d := arr + 8 * Z.of_nat (length ps)) (s := arr + 8 * (Z.of_nat (length (z :: zs')) + Z.of_nat (length ps))) (n := 0) (lo := lo) (old := []) (src := []);
first [ exact DST | exact RT | assumption | reflexivity | idtac ].
all: rewrite ?unsigned_lit by lia.
all: lazymatch goal with
| |- 0 < 0 -> _ => intros H00; lia
| |- bytes_at _ _ _ [] => apply bytes_at_nil; lia
| |- _ = Z_to_bv 64 _ => f_equal; lia
| |- stk _ _ _ _ => assumption
| |- mem_inv _ _ => assumption
| |- _ mod 16 = 0 => replace (bv_unsigned sp + -112) with (bv_unsigned sp - 112) by lia; rewrite Zminus_mod, SPA; reflexivity
| |- forall _, _ => idtac
| |- _ => first [lia | unfold A_SB; Z.div_mod_to_equations; lia]
end.
intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m4 MU4 WM4 MI4 DST4 SRC4 ST4.
lazymatch type of MU4 with munch _ ?mc _ =>
transport_after_call asegs mc m4 MU4 WM4; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU4 WM4 end.
replace (ret_pc (Z_to_bv 64 0xa0b40)) with (Z_to_bv 64 0xa0b40) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step.
step.
step. rewrite !unsigned_lit by lia.
replace (Z.of_nat (length ps) + Z.of_nat (length (z :: zs')) - Z.of_nat (length (z :: zs'))) with (Z.of_nat (length ps)) by lia.
step.
do 15 step.
apply evt_done. do 15 eexists. split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split. { lazymatch goal with |- stk _ ?mf _ _ => match goal with FRx : rw_cells asegs mf (bv_unsigned sp + -112) _, STx : stk asegs mf _ _ |- _ =>
release_frame FRx STx (bv_unsigned sp); exact STx end end. }
eapply alist_close. split; [| split; [eassumption | split; [eassumption | lia]]]. unfold al_hdr. eassumption.
Qed.
End Regs.
End RC__1.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH QmZZ QKQo Q6WR QrPc QpNt QJZd QW22 QFZX QnDr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ. Import QTEu. Import Qsw7 QJjn QRUw QKQo.
Import Q6WR Q6WR.Mq0 QrPc.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mq7 QlKV.Mqa QsKa.Mq7 QpNt.Mq4 QJZd.Mq4 QW22 QFZX.Mq1 QnDr.Mq1.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma nodup_blk_size : forall (BS : list blk) a n k, List.NoDup (map blk_addr BS) -> In (a, n) BS -> In (a, k) BS -> n = k.
Proof.
induction BS as [|[b0 n0] BS IH]; intros a n k ND Hn Hk; [destruct Hn|].
cbn in ND. inversion ND as [|y l Hni Hnd]; subst.
destruct Hn as [Hn|Hn]; destruct Hk as [Hk|Hk].
- congruence.
- exfalso. apply Hni. apply in_map_iff. exists (a, k). injection Hn as -> ->. split; [reflexivity | exact Hk].
- exfalso. apply Hni. apply in_map_iff. exists (a, n). injection Hk as -> ->. split; [reflexivity | exact Hn].
- eapply IH; [exact Hnd | exact Hn | exact Hk].
Qed.

Section MF4.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Definition mf_objA_stmt : Prop :=
forall (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud) (lo : Z) (errv : word)
(s : jshape) (BS : list blk) (x rc : Z) (T : TSet) (kids : list (option jshape))
(x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (junk8 : list byte),
s = Sobj kids ->
HEAPAx A (BS ++ LB) LM FRS B m md ->
jval asegs A4F s m BS x 0 ->
mf_frameA ra sp s0 s1 s2 s3 m junk8 ->
stk asegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -48 - 96 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> bv_unsigned ra mod 2 = 0 ->
model_vm_only (cfg_model md0) (cfg_model md) -> heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m -> fsaved F F1 -> (frm0 fc -> frm0 fc1) -> rc = 1 ->
bD B0 <= bD B -> bB B0 <= bB B -> 512 * Z.of_nat (length BS) <= bB B ->
KPOSTA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo errv s BS x rc T ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 x) x9 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 A_SB) (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x9ac74) fc1 None m (seg_rom asegs)).
Hypothesis MF_OBJ : mf_objA_stmt.

Lemma maybe_free_A_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word) (s : jshape) (BS : list blk) (x rc : Z),
HEAPAx A (BS ++ LB) LM FRS B m md ->
x <> 0 -> 1 <= rc < 2^31 -> jval asegs A4F s m BS x rc ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 - 96 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 x -> a1 = Z_to_bv 64 0 ->
(rc = 1 -> 512 * Z.of_nat (length BS) <= bB B) ->
(forall ms1 md1 A1, mf_postA HIx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo errv s BS x rc ms1 md1 A1 ->
AJ5 A4L HIx A1 T md1 ms1) ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9abd0) fc None m (seg_rom asegs)).
Proof.
intros until rc. intros HP Hx Hrc J ST LO LOS SPA HT ERR TP RA A0 A1 BB K.
unfold_consts. unfold A_SB, A_TP, A_ERRNO in *. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP) as [HB00 HD00].
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (nodup_app_l' BS LB (nodup_app_l' (BS ++ LB) LM (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP))) as ND.
destruct (jval_hdr asegs A4F s m BS x rc J ND) as (n & tojs & pb & udel & ud & rest & INx & SZ & N48 & HDR & CLOSE).
assert (INx2 : In (x, n) ((BS ++ LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; left; exact INx).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ x n HP INx2) as (_ & Hxal & Hxlo & Hxhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ x n HP INx2) as Hximg.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ x n HP ltac:(apply in_or_app; left; exact INx)) as SHx. unfold shad in SHx.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ x n 0 x n HP ltac:(apply in_or_app; left; exact INx) ltac:(lia) INx2) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ x n 5 x n HP ltac:(apply in_or_app; left; exact INx) ltac:(Z.div_mod_to_equations; lia) INx2) as SEP5.
a4l.
assert (SH : ro_cells asegs m (x / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
{ rewrite (shadow_bytes_split n 6) in SHx by lia.
apply bytes_at_app in SHx as [SH6 _]. split; [cbn; repeat split; exact I | cbn [cells_bytes cbytes app]; exact SH6]. }
clear SHx.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (x + 4, x + 8)] m) as MU.
pose proof SZ as RSZ. rewrite cells_size_app in RSZ. cbn [cells_size csize jhdr_cells Nat.add] in RSZ.
unfold jhdr_cells in HDR. cbn [app] in HDR.
reenterA asegs A4L HIx asegs_wx HP. subst a0 a1 tp.
carve_frame 48%nat ST.
do 6 step.
step. step. step.
step. step.
asan_chkA.
step. norm_w32. step. norm_w32. stepz.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.

assert (AG1 : agree_on asegs (others x BS) m m1).
{ eapply (agree_others_gen asegs); [exact MU | exact WM |].
intros a k Hin Hne.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin)) as (Hk & _ & _ & Hahi & _).
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ x n a k HP INx2 ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin) ltac:(congruence)) as D.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hahi. cbn. lia. }
assert (HP1 : HEAPAx A (BS ++ LB) LM FRS B m1 md) by heap_nowA A4L HIx HP MU WM MI.
assert (HPR1 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m1).
{ eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; rewrite <- app_assoc; apply in_or_app; right; exact Hb | clia |].
apply Forall_cons; [cbn [fst snd]; left; clia |].
apply Forall_cons; [cbn [fst snd] | apply Forall_nil]. right; left. exists x, n. split; [exact INx2|]. split; [| lia].
exact (not_in_app3 _ _ _ _ (nodup_prefix_suffix BS (LB ++ LM) x n n ltac:(pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as NDx; rewrite <- app_assoc in NDx; exact NDx) INx) (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP INx2)). }
step.
destruct (Z.eq_dec rc 1) as [Hrc1 | Hrc2].
-
subst rc. specialize (BB eq_refl). if_true.
assert (J1 : jval asegs A4F s m1 BS x 0).
{ apply (CLOSE m1 0); [| exact AG1]. unfold jhdr_cells. cbn [app]. replace (1 + -1) with 0 in HDR by lia. exact HDR. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (ZERO : forall (ty tojs' pb' udel' ud' : Z) (rest' : list cell) (BS' : list blk) (m2 : word -> option byte) (md2 : config) (A2 : ASA A4L HIx) (B2 : bud)
(xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt0 xt1 xt2 xt3 xt4 xt5 xt6 xra : word),
HEAPAx A2 (BS' ++ LB) LM FRS B2 m2 md2 -> In (x, n) BS' ->
rw_cells asegs m2 x (jhdr_cells ty 0 tojs' pb' udel' ud' ++ rest') -> Z.of_nat (cells_size (jhdr_cells ty 0 tojs' pb' udel' ud' ++ rest')) = n ->
mf_frameA ra sp s0 s1 s2 s3 m2 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 junk))))) ->
stk asegs m2 lo (bv_unsigned sp + -48) ->
rw_cells asegs m2 (6434400 - 164) [C4 errv] ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m2 ->
bD B <= bD B2 ->
(forall m3 (ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 yt5 yt6 : word),
HEAPAx A2 (BS' ++ LB) LM FRS B2 m3 md2 ->
rw_cells asegs m3 x (jhdr_cells ty 0 tojs' pb' 0 0 ++ rest') ->
mf_frameA ra sp s0 s1 s2 s3 m3 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 junk))))) ->
stk asegs m3 lo (bv_unsigned sp + -48) ->
rw_cells asegs m3 (6434400 - 164) [C4 errv] ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m3 ->
agree_on asegs (others x BS') m2 m3 ->
evt asegs (AJ5e A4L HIx A2 T md2)
(MS (mkR yt0 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 6434400) yt1 yt2 ya7 (Z_to_bv 64 x) (Z_to_bv 64 (x + 24))
(Z_to_bv 64 (x + 24)) ya0 ya1 ya2 ya3 ya4 ya5 ya6 (Z_to_bv 64 2147450880) (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 yt3 yt4 yt5 yt6)
F (Z_to_bv 64 0x9ac74) fc None m3 (seg_rom asegs))) ->
evt asegs (AJ5e A4L HIx A2 T md2)
(MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 6434400) xt0 xt1 xt2 (Z_to_bv 64 x) (Z_to_bv 64 (x + 24))
xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 2147450880) (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
F (Z_to_bv 64 0x9ac64) fc None m2 (seg_rom asegs)))
end.
{ intros ty tojs' pb' udel' ud' rest' BS' m2 md2 A2 B2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt0 xt1 xt2 xt3 xt4 xt5 xt6 xra HP2 INx' HDR2 SZ2 FR2 ST2 ERR2 HPR2 BD2 KZ.
clear MU WM AG1 HP1 HPR1 J1 CLOSE HDR J.
unfold mf_frameA in FR2.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI2.
assert (INx3 : In (x, n) ((BS' ++ LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; left; exact INx').
pose proof (wmono_refl asegs m2) as WM. pose proof (munch_refl [(x + 24, x + 40); (lo, bv_unsigned sp + -48)] m2) as MU.
pose proof SZ2 as RSZ2. rewrite cells_size_app in RSZ2. cbn [cells_size csize jhdr_cells Nat.add] in RSZ2.
unfold jhdr_cells in HDR2. cbn [app] in HDR2.
step. step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch type of HDR2 with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?rr) =>
apply (rw_cells_recast asegs mc x _ ([c1; c2; c3; c4] ++ ([CB 16 (cells_bytes [c5; c6])] ++ rr))) in HDR2;
[| apply cells_wf_app; split; [cbn; repeat split; exact I | apply cells_wf_app; split; [cbn; repeat split; reflexivity | ]];
match type of HDR2 with _ => idtac end; destruct HDR2 as [[Hwf _] _]; repeat (apply cells_wf_app in Hwf as [_ Hwf] || destruct Hwf as [_ Hwf]); exact Hwf
| rewrite !cells_bytes_app; reflexivity | rewrite !cells_size_app; reflexivity ]
end;
destruct (proj1 (rw_cells_app asegs mc x _ _) HDR2) as [HD4 REST]; clear HDR2;
cbn [cells_size csize Nat.add] in REST; replace (x + Z.of_nat 24) with (x + 24) in REST by lia;
destruct (proj1 (rw_cells_app asegs mc (x + 24) _ _) REST) as [DST TL]; clear REST;
cbn [cells_size csize Nat.add] in TL; replace (x + 24 + Z.of_nat 16) with (x + 40) in TL by lia;
assert (HPc : HEAPAx A2 (BS' ++ LB) LM FRS B2 mc md2) by heap_nowA A4L HIx HP2 MU WM MI2
end.
eapply (amemset_A HIx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x n (x + 24) 0 16 lo);
[ exact HPc | .. ]; a4l_goal; rewrite ?unsigned_lit by lia;
try first [ exact INx3 | exact DST | exact ST2 | exact MI2 | reflexivity | lia
| replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) by lia; rewrite Zminus_mod, SPA; reflexivity ].
all: try (apply in_or_app; left; exact INx').
intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m4 MU4 WM4 MI4 DST4 ST4.
lazymatch type of MU4 with munch _ ?mc _ =>
transport_after_call asegs mc m4 MU4 WM4; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU4 WM4 HPc end.
replace (ret_pc (Z_to_bv 64 0x9ac74)) with (Z_to_bv 64 0x9ac74) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
assert (AG4 : agree_on asegs (others x BS') m2 m4).
{ eapply (agree_others_gen asegs); [exact MU | exact WM |]. intros a k Hin Hne.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP2 ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin)) as (Hk & _ & _ & Hahi & _).
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ x n a k HP2 INx3 ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin) ltac:(congruence)) as D.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hahi. cbn. lia. }
eapply KZ.
- heap_nowA A4L HIx HP2 MU WM MI4.
- unfold jhdr_cells. cbn [app].
lazymatch goal with H4 : rw_cells asegs m4 x _, D4 : rw_cells asegs m4 (x + 24) _, T4 : rw_cells asegs m4 (x + 40) _ |- rw_cells _ m4 x ?cs =>
lazymatch cs with ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?rr => change cs with ([c1; c2; c3; c4] ++ ([c5; c6] ++ rr)) end;
apply (proj2 (rw_cells_app asegs m4 x _ _)); cbn [cells_size csize Nat.add]; split; [exact H4|];
replace (x + Z.of_nat 24) with (x + 24) by lia;
apply (proj2 (rw_cells_app asegs m4 (x + 24) _ _)); cbn [cells_size csize Nat.add];
replace (x + 24 + Z.of_nat 16) with (x + 40) by lia; split; [| exact T4];
eapply rw_cells_recast; [exact D4 | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity]
end.
- unfold mf_frameA. assumption.
- exact ST4.
- assumption.
- eapply heap_pres_trans; [exact HPR2|].
eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP2 | intros b Hb; rewrite <- app_assoc; apply in_or_app; right; exact Hb | clia |].
apply Forall_cons; [cbn [fst snd] |]. { right; left. exists x, n. split; [exact INx3|]. split; [| lia].
exact (not_in_app3 _ _ _ _ (nodup_prefix_suffix BS' (LB ++ LM) x n n ltac:(pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP2) as NDx; rewrite <- app_assoc in NDx; exact NDx) INx') (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP2 INx3)). }
apply Forall_cons; [cbn [fst snd]; left; clia | apply Forall_nil].
- exact AG4. }
clear MU WM J.

assert (C8F : forall mq aq cs1 cs2 k v1 v2, rw_cells asegs mq aq cs1 -> rw_cells asegs mq aq cs2 ->
cell_at cs1 k = Some (C8 v1) -> cell_at cs2 k = Some (C8 v2) -> v1 = v2).
{ clear. intros mq aq cs1 cs2 k v1 v2 R1 R2 E1 E2.
pose proof (rw_cells_read asegs _ _ _ _ _ R1 E1) as Q1. pose proof (rw_cells_read asegs _ _ _ _ _ R2 E2) as Q2.
cbn [csize cbytes] in Q1, Q2. rewrite Q1 in Q2. apply (f_equal (option_map le_bytes_to_word)) in Q2.
cbn [option_map] in Q2. rewrite !le_bytes_to_word_le8 in Q2. injection Q2 as E. exact E. }
pose proof (wmono_refl asegs m1) as WM. pose proof (munch_refl [] m1) as MU.

assert (INCLo : forall b, In b BS -> blk_addr b <> x -> In b (others x BS)) by (intros [ba bn] Hb Hne; apply in_others; [exact Hb | exact Hne]).

Ltac udel_steps := step; asan_chkA; step; step.
destruct s as [|u| |h|kids|kids].
+
clear HDR AG1 CLOSE C8F.
pose proof J1 as J2. destruct J2 as (pb1 & PBS & REST & EBS & OPB & b & junkb & ER & HDR1). subst REST.
assert (n = 48) by (eapply (nodup_blk_size BS x); [exact ND | exact INx | subst BS; left; reflexivity]). subst n.
unfold jhdr_cells in HDR1. cbn [app] in HDR1.
udel_steps. step. if_true.
eapply (ZERO JT_BOOLEAN _ pb1 0 0 ([C4 (Z_to_bv 64 b); CB 4 junkb]) BS m1 md A B);
[ exact HP1 | exact INx | unfold jhdr_cells; cbn [app]; exact HDR1 | subst BS; cbn; lia | unfold mf_frameA; exact FR | exact ST | assumption | exact HPR1 | lia |].
intros m3 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 yt5 yt6 HP3 HDR3 FR3 ST3 ERR3 HPR3 AG3.
evt_done5.
eapply (mf_scalarA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo errv Sbool BS x 1 T) with (n := 48) (PBS := PBS);
[ subst BS; cbn [app] in HP3 |- *; exact HP3 | lia | exact HDR3 | left; reflexivity
| eapply opt_pbuf_agree; [exact OPB | exact AG3 | intros bb Hbb; apply INCLo; [subst BS; in_sub Hbb | ]]
| exact FR3 | exact ST3 | clia | clia | exact SPA | exact HT | exact ERR3 | exact RA | apply model_vm_only_refl | exact HPR3
| apply fsaved_refl | intros Hf; exact Hf | reflexivity | lia | subst BS; cbn [length app] in *; lia | subst BS; cbn [length app] in *; lia | exact K ].
subst BS. intros E. cbn in E.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP1) as NDx. cbn in NDx. inversion NDx as [|z l Hni Hnd]. apply Hni.
rewrite map_app. apply in_or_app. left. rewrite map_app. apply in_or_app. left. rewrite <- E. apply in_map_iff. exists bb. split; [reflexivity | exact Hbb].
+ clear HDR AG1 CLOSE C8F. destruct u.
*
pose proof J1 as J2. destruct J2 as (pb1 & PBS & REST & EBS & OPB & bits & ud1 & udn & uds & ER & HU & HDR1 & HC). subst REST.
assert (n = 48) by (eapply (nodup_blk_size BS x); [exact ND | exact INx | subst BS; left; reflexivity]). subst n.
assert (INud : In (ud1, udn) ((BS ++ LB) ++ LM)) by (subst BS; apply in_or_app; left; apply in_or_app; left; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ ud1 udn HP1 INud) as (Hudn & Hual & Hulo & Huhi & _).
assert (Hxud : x <> ud1).
{ intros E. subst BS. pose proof ND as NDx. cbn in NDx. inversion NDx as [|z l Hni Hnd]. apply Hni. left. symmetry. exact E. }
unfold jhdr_cells in HDR1. cbn [app fn_ud_to_json_string fn_free_userdata A4F] in HDR1. a4l.
udel_steps. step. if_falsex.
step.
asan_chkA.
step. step.
step.
step. step.

alloc_callA (hiA_free A4L HIx) blk ud1 uw UWptr A4L HIx HP1 MU WM ltac:(pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MIq; exact MIq).
all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists udn. subst BS. apply in_or_app. left. right. left. reflexivity. }
all: try (cbn [uw_pre uw_ok uw_key uw_cost]; intros _; split; [left; lia | unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (destruct (Z.eqb_spec ud1 0); cbn [bB bD charge uw_cost] in *; subst BS; cbn [length app] in BB; lia).
intros ms2 m2 md2 A2 r2 RS2 VM2 ST2 HPR2 ERR2 HP2. open_ret RS2. a4l.
rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in ST2 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in HPR2 by lia.
replace (if ud1 =? 0 then 0 else uw_cost UWptr) with 0 in HP2 by (destruct (Z.eqb_spec ud1 0); reflexivity).
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia].
assert (EREM : lb_remove ud1 (BS ++ LB) = ((x, 48) :: PBS) ++ LB).
{ subst BS. cbn [app]. rewrite lb_remove_other by (cbn; lia). rewrite lb_remove_head. reflexivity. }
rewrite EREM in HP2, HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in HDR1; [| eapply (client_range_block A4H _ _ _ _ x 48); [apply in_or_app; left; left; reflexivity | lia | cbn; lia]].
assert (OPB2 : opt_pbuf asegs m2 PBS pb1).
{ eapply opt_pbuf_agree; [exact OPB | | apply incl_refl].
eapply (agree_of_heap_pres asegs A4H); [exact HPR2 | reflexivity | intros bb Hbb; cbn; right; apply in_or_app; left; apply in_or_app; left; exact Hbb]. }
assert (HPR12 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m2).
{ eapply heap_pres_trans; [exact HPR1|]. eapply heap_pres_weaken; [exact HPR2 | lia | intros bb Hbb; cbn; right; apply in_or_app; apply in_app_or in Hbb; destruct Hbb; [left; apply in_or_app; right; assumption | right; assumption]]. }
clear MU WM.
reenterA asegs A4L HIx asegs_wx HP2.
eapply (ZERO JT_DOUBLE _ pb1 _ _ ([C8 bits]) ((x, 48) :: PBS) m2 md2 A2 _);
[ exact HP2 | left; apply (f_equal2 pair); [reflexivity | cbn; lia] | unfold jhdr_cells; cbn [app]; exact HDR1 | cbn; lia | unfold mf_frameA; exact FR | exact ST2 | exact ERR2 | exact HPR12
| cbn [bD charge]; lia |].
intros m3 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 yt5 yt6 HP3 HDR3 FR3 ST3 ERR3 HPR3 AG3.
evt_done5.
eapply (mf_scalarA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo errv (Sdouble true) BS x 1 T) with (n := 48) (PBS := PBS);
[ exact HP3 | lia | exact HDR3 | right; left; reflexivity
| eapply opt_pbuf_agree; [exact OPB2 | exact AG3 | intros [ba bn] Hbb; apply in_others; [right; exact Hbb |]]
| exact FR3 | exact ST3 | clia | clia | exact SPA | exact HT | exact ERR3 | exact RA | exact VM2 | exact HPR3
| apply fsaved_refl | intros Hf; exact Hf | reflexivity | cbn [bD charge] in *; lia
| subst BS; cbn [bB charge length app] in *; lia | subst BS; cbn [bB charge length app] in *; lia | exact K ].
intros E. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP2) as NDx. cbn in NDx. inversion NDx as [|z l Hni Hnd]. apply Hni.
rewrite map_app. apply in_or_app. left. rewrite map_app. apply in_or_app. left. rewrite <- E. apply in_map_iff. exists (ba, bn). split; [reflexivity | exact Hbb].
*
pose proof J1 as J2. destruct J2 as (pb1 & PBS & REST & EBS & OPB & bits & ER & HSP & HDR1). subst REST.
assert (n = 48) by (eapply (nodup_blk_size BS x); [exact ND | exact INx | subst BS; left; reflexivity]). subst n.
unfold jhdr_cells in HDR1. cbn [app] in HDR1.
udel_steps. step. if_true.
eapply (ZERO JT_DOUBLE _ pb1 0 0 ([C8 bits]) BS m1 md A B);
[ exact HP1 | exact INx | unfold jhdr_cells; cbn [app]; exact HDR1 | subst BS; cbn; lia | unfold mf_frameA; exact FR | exact ST | assumption | exact HPR1 | lia |].
intros m3 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 yt5 yt6 HP3 HDR3 FR3 ST3 ERR3 HPR3 AG3.
evt_done5.
eapply (mf_scalarA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo errv (Sdouble false) BS x 1 T) with (n := 48) (PBS := PBS);
[ subst BS; cbn [app] in HP3 |- *; exact HP3 | lia | exact HDR3 | right; left; reflexivity
| eapply opt_pbuf_agree; [exact OPB | exact AG3 | intros bb Hbb; apply INCLo; [subst BS; in_sub Hbb | ]]
| exact FR3 | exact ST3 | clia | clia | exact SPA | exact HT | exact ERR3 | exact RA | apply model_vm_only_refl | exact HPR3
| apply fsaved_refl | intros Hf; exact Hf | reflexivity | lia | subst BS; cbn [length app] in *; lia | subst BS; cbn [length app] in *; lia | exact K ].
subst BS. intros E. cbn in E.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP1) as NDx. cbn in NDx. inversion NDx as [|z l Hni Hnd]. apply Hni.
rewrite map_app. apply in_or_app. left. rewrite map_app. apply in_or_app. left. rewrite <- E. apply in_map_iff. exists bb. split; [reflexivity | exact Hbb].
+
clear HDR AG1 CLOSE C8F.
pose proof J1 as J2. destruct J2 as (pb1 & PBS & REST & EBS & OPB & cty & v & junki & ER & HCT & HDR1). subst REST.
assert (n = 56) by (eapply (nodup_blk_size BS x); [exact ND | exact INx | subst BS; left; reflexivity]). subst n.
unfold jhdr_cells in HDR1. cbn [app] in HDR1.
udel_steps. step. if_true.
eapply (ZERO JT_INT _ pb1 0 0 ([C4 (Z_to_bv 64 cty); CB 4 junki; C8 v]) BS m1 md A B);
[ exact HP1 | exact INx | unfold jhdr_cells; cbn [app]; exact HDR1 | subst BS; cbn; lia | unfold mf_frameA; exact FR | exact ST | assumption | exact HPR1 | lia |].
intros m3 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 yt5 yt6 HP3 HDR3 FR3 ST3 ERR3 HPR3 AG3.
evt_done5.
eapply (mf_scalarA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo errv Sint BS x 1 T) with (n := 56) (PBS := PBS);
[ subst BS; cbn [app] in HP3 |- *; exact HP3 | lia | exact HDR3 | right; right; reflexivity
| eapply opt_pbuf_agree; [exact OPB | exact AG3 | intros bb Hbb; apply INCLo; [subst BS; in_sub Hbb | ]]
| exact FR3 | exact ST3 | clia | clia | exact SPA | exact HT | exact ERR3 | exact RA | apply model_vm_only_refl | exact HPR3
| apply fsaved_refl | intros Hf; exact Hf | reflexivity | lia | subst BS; cbn [length app] in *; lia | subst BS; cbn [length app] in *; lia | exact K ].
subst BS. intros E. cbn in E.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP1) as NDx. cbn in NDx. inversion NDx as [|z l Hni Hnd]. apply Hni.
rewrite map_app. apply in_or_app. left. rewrite map_app. apply in_or_app. left. rewrite <- E. apply in_map_iff. exists bb. split; [reflexivity | exact Hbb].
+
assert (EU : Z_to_bv 64 udel = Z_to_bv 64 0 /\ Z_to_bv 64 ud = Z_to_bv 64 0).
{ pose proof J1 as J2. destruct h.
- destruct J2 as (pb1 & PBS & REST & EBS & OPB & len & pd & pdn & str & junk2 & ER & HL & HS & HPD & HDR1 & HD).
unfold jhdr_cells in HDR1. cbn [app] in HDR1.
split; [ eapply (C8F m1 x _ _ 24%nat); [exact HDR | exact HDR1 | reflexivity | reflexivity]
| eapply (C8F m1 x _ _ 32%nat); [exact HDR | exact HDR1 | reflexivity | reflexivity] ].
- destruct J2 as (pb1 & PBS & REST & EBS & OPB & len & str & junks & ER & HL & HS & HDR1).
unfold jhdr_cells in HDR1. cbn [app] in HDR1.
split; [ eapply (C8F m1 x _ _ 24%nat); [exact HDR | exact HDR1 | reflexivity | reflexivity]
| eapply (C8F m1 x _ _ 32%nat); [exact HDR | exact HDR1 | reflexivity | reflexivity] ]. }
destruct EU as [EU1 EU2]. rewrite EU1, EU2 in HDR. replace (1 + -1) with 0 in HDR by lia.
unfold jhdr_cells in CLOSE. rewrite EU1, EU2 in CLOSE.
udel_steps. step. if_true.
eapply (ZERO (jtype (Sstr h)) tojs pb 0 0 rest BS m1 md A B);
[ exact HP1 | exact INx | unfold jhdr_cells; cbn [app]; exact HDR
| rewrite cells_size_app; cbn [cells_size csize jhdr_cells Nat.add]; exact RSZ
| unfold mf_frameA; exact FR | exact ST | assumption | exact HPR1 | lia |].
intros m3 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 yt5 yt6 HP3 HDR3 FR3 ST3 ERR3 HPR3 AG3.
evt_done5.
assert (J3 : jval asegs A4F (Sstr h) m3 BS x 0)
by (apply (CLOSE m3 0); [cbn [app]; unfold jhdr_cells in HDR3; cbn [app] in HDR3; exact HDR3 | eapply agree_on_trans; [exact AG1 | exact AG3]]).
eapply (mf_strA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo errv (Sstr h) BS x 1 T h);
[ reflexivity | exact HP3 | exact J3 | exact FR3 | exact ST3 | clia | clia | exact SPA | exact HT | exact ERR3 | exact RA
| apply model_vm_only_refl | exact HPR3 | apply fsaved_refl | intros Hf; exact Hf | reflexivity | lia | lia | exact BB | exact K ].
+
assert (EU : Z_to_bv 64 udel = Z_to_bv 64 0 /\ Z_to_bv 64 ud = Z_to_bv 64 0).
{ destruct (jval_obj_open asegs A4F kids m1 BS x 0 J1) as (pb1 & PBS & t & TBS & kvs & KBS & EBS & OPB & HDR1 & LT & OK).
unfold jhdr_cells in HDR1. cbn [app] in HDR1.
split; [ eapply (C8F m1 x _ _ 24%nat); [exact HDR | exact HDR1 | reflexivity | reflexivity]
| eapply (C8F m1 x _ _ 32%nat); [exact HDR | exact HDR1 | reflexivity | reflexivity] ]. }
destruct EU as [EU1 EU2]. rewrite EU1, EU2 in HDR. replace (1 + -1) with 0 in HDR by lia.
unfold jhdr_cells in CLOSE. rewrite EU1, EU2 in CLOSE.
udel_steps. step. if_true.
eapply (ZERO (jtype (Sobj kids)) tojs pb 0 0 rest BS m1 md A B);
[ exact HP1 | exact INx | unfold jhdr_cells; cbn [app]; exact HDR
| rewrite cells_size_app; cbn [cells_size csize jhdr_cells Nat.add]; exact RSZ
| unfold mf_frameA; exact FR | exact ST | assumption | exact HPR1 | lia |].
intros m3 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 yt5 yt6 HP3 HDR3 FR3 ST3 ERR3 HPR3 AG3.
evt_done5.
assert (J3 : jval asegs A4F (Sobj kids) m3 BS x 0)
by (apply (CLOSE m3 0); [cbn [app]; unfold jhdr_cells in HDR3; cbn [app] in HDR3; exact HDR3 | eapply agree_on_trans; [exact AG1 | exact AG3]]).
pose proof MF_OBJ as MFO. unfold mf_objA_stmt in MFO.
eapply (MFO ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo errv (Sobj kids) BS x 1 T kids);
[ reflexivity | exact HP3 | exact J3 | exact FR3 | exact ST3 | clia | clia | exact SPA | exact HT | exact ERR3 | exact RA
| apply model_vm_only_refl | exact HPR3 | apply fsaved_refl | intros Hf; exact Hf | reflexivity | lia | lia | exact BB | exact K ].
+
assert (EU : Z_to_bv 64 udel = Z_to_bv 64 0 /\ Z_to_bv 64 ud = Z_to_bv 64 0).
{ destruct (jval_arr_open asegs A4F kids m1 BS x 0 J1) as (pb1 & PBS & a & ABS & ps & KBS & EBS & OPB & HDR1 & AL & OK).
unfold jhdr_cells in HDR1. cbn [app] in HDR1.
split; [ eapply (C8F m1 x _ _ 24%nat); [exact HDR | exact HDR1 | reflexivity | reflexivity]
| eapply (C8F m1 x _ _ 32%nat); [exact HDR | exact HDR1 | reflexivity | reflexivity] ]. }
destruct EU as [EU1 EU2]. rewrite EU1, EU2 in HDR. replace (1 + -1) with 0 in HDR by lia.
unfold jhdr_cells in CLOSE. rewrite EU1, EU2 in CLOSE.
udel_steps. step. if_true.
eapply (ZERO (jtype (Sarr kids)) tojs pb 0 0 rest BS m1 md A B);
[ exact HP1 | exact INx | unfold jhdr_cells; cbn [app]; exact HDR
| rewrite cells_size_app; cbn [cells_size csize jhdr_cells Nat.add]; exact RSZ
| unfold mf_frameA; exact FR | exact ST | assumption | exact HPR1 | lia |].
intros m3 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 yt5 yt6 HP3 HDR3 FR3 ST3 ERR3 HPR3 AG3.
evt_done5.
assert (J3 : jval asegs A4F (Sarr kids) m3 BS x 0)
by (apply (CLOSE m3 0); [cbn [app]; unfold jhdr_cells in HDR3; cbn [app] in HDR3; exact HDR3 | eapply agree_on_trans; [exact AG1 | exact AG3]]).
eapply (mf_arrA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo errv (Sarr kids) BS x 1 T kids);
[ reflexivity | exact HP3 | exact J3 | exact FR3 | exact ST3 | clia | clia | exact SPA | exact HT | exact ERR3 | exact RA
| apply model_vm_only_refl | exact HPR3 | apply fsaved_refl | intros Hf; exact Hf | reflexivity | lia | lia | exact BB | exact K ].
-
if_falsex. step. step.
do 6 step. release_frame FR ST (bv_unsigned sp). step.
evt_done5. apply K. unfold mf_postA.
exists m1, 0, B.
split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|]. split; [exact ST|]. split; [exact HPR1|]. split; [assumption|]. split; [lia|].
left. split; [reflexivity|]. split; [lia|]. split; [| split; [lia | exact HP1]].
apply (CLOSE m1 (rc - 1)); [| exact AG1]. unfold jhdr_cells. cbn [app]. replace (rc + -1) with (rc - 1) in HDR by lia. exact HDR.
Qed.
End MF4.
End RC__1.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qtgi QPZI QlCE QhHQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 Qtgi Qsw7 QJjn QKQo. Import QPZI.Mq4 QlCE.Mq1 QhHQ.
Import Q6WR.Mq0 QrPc.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mq7 Q30W.Mq3 QlKV.Mq5.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Definition tokfree_loop_A_pc : Z := 0x92e18.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section TokFreeA.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis PUT : put_stmt_A HIx.

Lemma lvl_shadowA : forall A LB LM FR B m md q i,
HEAPAx A LB LM FR B m md -> In (q, 1024) LB -> q mod 8 = 0 -> (i < 32)%nat ->
ro_cells asegs m ((q + 32 * Z.of_nat i) / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof.
intros A LB LM FR B m md q i HP Hin Hal Hi.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ _ _ HP Hin) as SH. unfold shad in SH. cbn [hl_sb hl_segs hla_base A4L A4H] in SH.
change (shadow_bytes 1024) with (shadow_bytes (8 * 128)) in SH. rewrite shadow_bytes_mul8 in SH by lia.
apply (bytes_at_repeat_sub asegs m _ _ _ (4 * i) 4) in SH; [| cbn; lia].
replace ((q + 32 * Z.of_nat i) / 8 + A_SB) with (q / 8 + A_SB + Z.of_nat (4 * i)) by (unfold A_SB; Z.div_mod_to_equations; nia).
exact (ro_cells_of_repeat asegs m _ _ 4 SH).
Qed.

Definition tf_frameA (m : word -> option byte) (sp : Z) (s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) : Prop :=
rw_cells asegs m (sp - 80) [C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].

Definition tf_body_postA (x2 gp s0 s1 s2 s3 s4 s7 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(md : config) (REST LB0 P LM : list blk) (FRS : list frame) (B : bud) (SP : Z) (me mpre : word -> option byte) (lo : Z) (errv : word)
(q r pb depth : Z) (x : tscal) (levels : list tlevel) (i : nat) (l : tlevel) (s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (B' : bud) F' fc' x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
ms' = MS (mkR x1 x2 gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 (Z_to_bv 64 1) (Z_to_bv 64 (32 * Z.of_nat i + 16 - 32)) s7 (Z_to_bv 64 (-16)) s9 s10 s11 t3 t4 t5 t6) F' (Z_to_bv 64 0x92edc) fc' None m' (seg_rom asegs) /\
fsaved F F' /\ (frm0 fc -> frm0 fc') /\
model_vm_only (cfg_model md) (cfg_model md') /\
HEAPAx A' REST LM FRS B' m' md' /\
tstack asegs m' q (lupd levels i lvl_reset) /\
rw_cells asegs m' r (tok_cells pb depth q x) /\
tf_frameA m' SP s8v s7v s6v s5v s4v s3v s2v s1v s0v rav /\
stk asegs m' lo (SP - 80) /\
heap_pres A4H (LB0 ++ LM ++ fr_ivs A4L FRS) SP me m' /\
rw_cells asegs m' A_ERRNO [C4 errv] /\
agree_on asegs P mpre m' /\
bB B - 512 * (Z.of_nat (length (lvl_blocks l)) + 1) <= bB B' /\ bD B <= bD B'.

Lemma tokfree_bodyA :
forall (i : nat) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m me : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (REST LB0 P LM : list blk) (FRS : list frame) (B : bud) (SP lo : Z) (errv : word)
(q r pb depth : Z) (x : tscal) (levels : list tlevel) (l : tlevel) (s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word),
nth_error levels i = Some l -> (i < 32)%nat -> length levels = 32%nat ->
HEAPAx A (lvl_blocks l ++ REST) LM FRS B m md ->
REST = P ++ (r, 72) :: (q, 1024) :: LB0 ->
lvl_ok asegs A4F m l ->
tstack asegs m q levels ->
rw_cells asegs m r (tok_cells pb depth q x) ->
tf_frameA m SP s8v s7v s6v s5v s4v s3v s2v s1v s0v rav ->
stk asegs m lo (SP - 80) -> alloc_ceiling <= lo -> lo <= SP - 80 - put_stk_A ->
SP mod 16 = 0 -> SP <= hiA_top A4L HIx -> 0 <= SP < 2^64 ->
heap_pres A4H (LB0 ++ LM ++ fr_ivs A4L FRS) SP me m ->
rw_cells asegs m A_ERRNO [C4 errv] ->
512 * (Z.of_nat (length (lvl_blocks l)) + 1) <= bB B ->
(forall ms' md' A', tf_body_postA (Z_to_bv 64 (SP - 80)) gp (Z_to_bv 64 r) (Z_to_bv 64 (r + 56)) (Z_to_bv 64 (r + 20)) (Z_to_bv 64 A_SB)
(Z_to_bv 64 (r / 8 + 2147450882)) (Z_to_bv 64 (r / 8 + 2147450887)) s9 s10 s11
F fc md REST LB0 P LM FRS B SP me m lo errv q r pb depth x levels i l s8v s7v s6v s5v s4v s3v s2v s1v s0v rav ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (SP - 80)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 r) (Z_to_bv 64 (r + 56)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (r + 20)) (Z_to_bv 64 A_SB) (Z_to_bv 64 (r / 8 + 2147450882)) (Z_to_bv 64 1) (Z_to_bv 64 (32 * Z.of_nat i + 16))
(Z_to_bv 64 (r / 8 + 2147450887)) (Z_to_bv 64 (-16)) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 tokfree_loop_A_pc) fc None m (seg_rom asegs)).
Proof.
intros until rav. intros Hl Hi LEN HP EREST LOK TS BLK FR ST LO LOS SPA HT SPR HPR ERR BB K.
unfold put_stk_A in LOS. unfold_consts. unfold A_SB, A_TP, A_ERRNO, tokfree_loop_A_pc in *.
assert (INrR : In (r, 72) REST) by (rewrite EREST; apply in_or_app; right; left; reflexivity).
assert (INqR : In (q, 1024) REST) by (rewrite EREST; apply in_or_app; right; right; left; reflexivity).
assert (INr : In (r, 72) (lvl_blocks l ++ REST)) by (apply in_or_app; right; exact INrR).
assert (INq : In (q, 1024) (lvl_blocks l ++ REST)) by (apply in_or_app; right; exact INqR).
assert (INr2 : In (r, 72) ((lvl_blocks l ++ REST) ++ LM)) by (apply in_or_app; left; exact INr).
assert (INq2 : In (q, 1024) ((lvl_blocks l ++ REST) ++ LM)) by (apply in_or_app; left; exact INq).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r 72 HP INr2) as (_ & Hral & Hrlo & Hrhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ r 72 HP INr2) as Himg_r.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ q 1024 HP INq2) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ q 1024 HP INq2) as Himg_q.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hrhi, Hqhi.
assert (Hqr : q <> r).
{ intros ->. pose proof (nodup_app_l' _ _ (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP)) as ND. rewrite EREST, !map_app in ND. cbn [map blk_addr fst] in ND.
apply NoDup_app_remove_l in ND. apply NoDup_app_remove_l in ND. apply List.NoDup_cons_iff in ND as [Hni _]. apply Hni. left. reflexivity. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ q 1024 r 72 HP INq2 INr2 Hqr) as Hdqr.

pose proof (TS i l Hl) as LV. unfold srec_cells in LV.
remember (q + 32 * Z.of_nat i) as bse eqn:Hbse in LV.
pose proof (nth_error_Some_length Hl) as HiL.
unfold tf_frameA in FR. unfold tok_cells in BLK.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bse, bse + 32)] m) as MU.

assert (SHAD : forall Ax LBx Bx mdx mc, HEAPAx Ax LBx LM FRS Bx mc mdx -> In (r, 72) LBx -> In (q, 1024) LBx ->
ro_cells asegs mc (r / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
/\ ro_cells asegs mc (bse / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
{ intros Ax LBx Bx mdx mc HPc Ir Iq. split.
- pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ r 72 HPc Ir) as SH. unfold shad in SH. apply shadow_ro_cells in SH.
let cs := eval cbv in (shadow_cells 72) in change (shadow_cells 72) with cs in SH. a4l. exact SH.
- pose proof (lvl_shadowA _ _ _ _ _ _ _ q i HPc Iq ltac:(lia) Hi) as SH. unfold A_SB in SH. rewrite <- Hbse in SH. exact SH. }
destruct (SHAD _ _ _ _ m HP INr INq) as [SHr SHl].
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. step. if_false. rewrite ?sxb_zero, ?zxb_zero.
step. step.
replace (q + (32 * Z.of_nat i + 16)) with (bse + 16) by lia.
step.
replace (bse + 16 + -16) with bse by lia.
asan_chkA.
stepz.
step. replace (bse + 16 + -12) with (bse + 4) by lia.
asan_chkA.
step.
asan_chkA.
step. step.
try clear SHr; try clear SHl.
set (l1 := TL 0 1 (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TS1 : tstack asegs mc q (lupd levels i l1)) end.
{ subst bse. eapply (tstack_put asegs m _ q levels i l1 []); [exact TS | lia | exact MU | exact WM | intros; exact I | unfold srec_cells; cbn [tl_st tl_ss tl_cur tl_name l1]; assumption]. }
lazymatch goal with H : rw_cells asegs _ bse _ |- _ => rename H into LV1 end.
clear TS.
assert (PDJ : forall a n, In (a, n) P -> a + n <= q \/ q + 1024 <= a).
{ intros a n Hin.
assert (Haq : a <> q) by (eapply (nodup_P_notq (lvl_blocks l)); [rewrite <- EREST; exact (nodup_app_l' _ _ (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP)) | exact Hin]).
exact (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ a n q 1024 HP ltac:(apply in_or_app; left; apply in_or_app; right; rewrite EREST; apply in_or_app; left; exact Hin) INq2 Haq). }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (AGP : agree_on asegs P m mc) by (eapply (agree_of_munch asegs); [exact MU | exact WM | intros a n Hin; cbn; split; [pose proof (PDJ a n Hin); lia | exact I]]) end.

destruct LOK as [JO NM].
unfold lvl_blocks in HP. rewrite <- app_assoc in HP.
evt_done5.
assert (INq3 : In (q, 1024) (tl_cbs l ++ tl_nbs l ++ REST)) by (apply in_or_app; right; apply in_or_app; right; exact INqR).
assert (INq4 : In (q, 1024) ((tl_cbs l ++ tl_nbs l ++ REST) ++ LM)) by (apply in_or_app; left; exact INq3).
pose proof PUT as PUTx. unfold put_stmt_A, put_stmtA in PUTx.
eapply PUTx with (s := tl_cs l) (BS := tl_cbs l) (LB := tl_nbs l ++ REST) (p := tl_cur l) (rc := 1) (lo := lo) (errv := errv);
[ heap_nowA A4L HIx HP MU WM MI | .. ]; a4l_goal; rewrite ?unsigned_lit by lia; try first [reflexivity | lia].
{ lazymatch goal with |- put_pre _ _ _ ?mc _ _ _ => assert (AG : agree_on asegs (tl_cbs l) m mc) end.
{ eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros a n Hin. cbn. split; [|exact I].
assert (Haq : a <> q).
{ intros ->. refine (nodup_prefix_suffix (tl_cbs l) (tl_nbs l ++ REST) q n 1024 (nodup_app_l' _ _ (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP)) Hin _).
apply in_or_app; right. exact INqR. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ a n q 1024 HP ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin) ltac:(apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; exact INqR) Haq). lia. }
unfold put_pre. destruct (tl_cs l) as [s'|]; [|exact JO].
destruct JO as [Hc J]. split; [exact Hc|]. split; [lia|]. eapply jval_agree; [exact J | exact AG | apply incl_refl]. }
all: try eassumption.
all: try (unfold put_stk_A; lia).
all: try (rewrite Zminus_mod, SPA; reflexivity).
all: try (unfold put_costA; destruct (tl_cs l); [rewrite Z.eqb_refl; unfold lvl_blocks in BB; rewrite length_app in BB|]; lia).
intros ms2 md2 A2 (m2 & r2 & B2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & BB2 & BD2 & OUT2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
a4l. rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR2 by lia.
destruct OUT2 as [[_ HP2] | (s2 & _ & Habs & _)]; [| lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
assert (INrN : In (r, 72) (tl_nbs l ++ REST)) by (apply in_or_app; right; exact INrR).
assert (INqN : In (q, 1024) (tl_nbs l ++ REST)) by (apply in_or_app; right; exact INqR).
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in BLK; [| eapply client_range_block; [apply in_or_app; left; exact INrN | lia | cbn; lia]]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in LV1; [| eapply client_range_block; [apply in_or_app; left; exact INqN | lia | cbn; lia]]. a4l.
apply (tstack_pres A4H _ _ _ _ _ _ HPR2 ltac:(apply in_or_app; left; exact INqN)) in TS1; [| rewrite lupd_length; exact LEN]. a4l.
assert (NQ0 : ~ In (q, 1024) LB0).
{ pose proof (nodup_app_l' _ _ (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP)) as ND. rewrite EREST in ND. exact (nodup_mid_notin _ _ _ _ _ _ _ _ 1024 ND). }
assert (NQM : ~ In (q, 1024) (LB0 ++ LM ++ fr_ivs A4L FRS)).
{ apply not_in_app3; [| exact (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP INq4)].
intros Hx. apply in_app_or in Hx. destruct Hx as [Hx|Hx]; [exact (NQ0 Hx)|].
exact (nodup_prefix_suffix _ LM q 1024 1024 (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) INq3 Hx). }
assert (HPRa : heap_pres A4H (LB0 ++ LM ++ fr_ivs A4L FRS) SP me m2).
{ eapply heap_pres_trans; [exact HPR|]. eapply heap_pres_trans.
- eapply (heap_pres_of_munch A4H (LB0 ++ LM ++ fr_ivs A4L FRS) SP); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros bb Hbb; apply in_or_app; apply in_app_or in Hbb; destruct Hbb as [Hbb|Hbb]; [left; apply in_or_app; right; apply in_or_app; right; rewrite EREST; apply in_or_app; right; right; right; exact Hbb | right; exact Hbb] | clia |].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; left. exists q, 1024. split; [exact INq4|]. split; [exact NQM | lia].
- eapply heap_pres_weaken; [exact HPR2 | lia | intros bb Hbb; apply in_or_app; apply in_app_or in Hbb; destruct Hbb as [Hbb|Hbb]; [left; apply in_or_app; right; rewrite EREST; apply in_or_app; right; right; right; exact Hbb | right; exact Hbb]]. }
assert (AGP2 : agree_on asegs P m m2).
{ eapply agree_on_trans; [exact AGP|]. eapply (agree_of_heap_pres asegs A4H); [exact HPR2 | reflexivity | intros b Hb; apply in_or_app; left; apply in_or_app; right; rewrite EREST; apply in_or_app; left; exact Hb]. }
clear MU WM MI HPR AGP PUTx.
pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP2) as [HB2 HD2].

pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. a4l.
pose proof (wmono_refl asegs m2) as WM. pose proof (munch_refl [(bse, bse + 32)] m2) as MU.
destruct (SHAD _ _ _ _ m2 HP2 INrN INqN) as [SHr SHl].
reenterA asegs A4L HIx asegs_wx HP2.
step. step. if_false. rewrite ?sxb_zero, ?zxb_zero.
step. step.
replace (q + (32 * Z.of_nat i + 16)) with (bse + 16) by lia.
asan_chkA.
stepz.
try clear SHr; try clear SHl.
destruct (SHAD _ _ _ _ _ ltac:(heap_nowA A4L HIx HP2 MU WM MI) INrN INqN) as [SHr SHl].
step. asan_chkA.
step. step.
try clear SHr; try clear SHl.
set (l2 := TL 0 1 0 None [] (tl_name l) (tl_nbs l)).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TS2 : tstack asegs mc q (lupd levels i l2)) end.
{ rewrite <- (lupd_lupd levels i l1 l2). subst bse.
eapply (tstack_put asegs m2 _ q (lupd levels i l1) i l2 []); [exact TS1 | rewrite lupd_length; lia | exact MU | exact WM | intros; exact I | unfold srec_cells; cbn [tl_st tl_ss tl_cur tl_name l2]; assumption]. }
clear TS1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (AGP3 : agree_on asegs P m mc) by (eapply agree_on_trans; [exact AGP2|]; eapply (agree_of_munch asegs); [exact MU | exact WM | intros a n Hin; cbn; split; [pose proof (PDJ a n Hin); lia | exact I]]) end.
alloc_callA (hiA_free A4L HIx) blk (tl_name l) uw UWptr A4L HIx HP2 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ destruct NM as [[Hn0 _] | [Hn0 [nn Hnbs]]]; [left; exact Hn0 | right; exists nn; rewrite Hnbs; left; reflexivity]. }
all: try (cbn [uw_pre uw_ok uw_key uw_cost]; intros _; split; [left; lia | unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (clear - BB BB2 BD2 HB2 HD2; unfold put_costA in *; unfold lvl_blocks in *; rewrite ?length_app in *; destruct (tl_cs l); rewrite ?Z.eqb_refl in *; destruct (Z.eqb_spec (tl_name l) 0); cbn [bB bD charge uw_cost] in *; lia).
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3. a4l.
rewrite ?unsigned_lit in ST3 by lia. rewrite ?unsigned_lit in HPR3 by lia.
assert (ELB : lb_remove (tl_name l) (tl_nbs l ++ REST) = REST).
{ destruct NM as [[Hn0 Hnbs] | [Hn0 [nn Hnbs]]].
- rewrite Hn0, Hnbs. cbn [app]. apply lb_remove_notin. intros nn Hin.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ 0 nn HP2 ltac:(apply in_or_app; left; rewrite Hnbs; exact Hin)) as (_ & _ & H0 & _). lia.
- rewrite Hnbs. cbn [app]. apply lb_remove_head. }
rewrite ELB in HPR3, HP3.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in BLK; [| eapply client_range_block; [apply in_or_app; left; exact INrR | lia | cbn; lia]]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in LV1; [| eapply client_range_block; [apply in_or_app; left; exact INqR | lia | cbn; lia]]. a4l.
apply (tstack_pres A4H _ _ _ _ _ _ HPR3 ltac:(apply in_or_app; left; exact INqR)) in TS2; [| rewrite lupd_length; exact LEN]. a4l.
assert (HPRb : heap_pres A4H (LB0 ++ LM ++ fr_ivs A4L FRS) SP me m3).
{ eapply heap_pres_trans; [exact HPRa|]. eapply heap_pres_trans.
- eapply (heap_pres_of_munch A4H (LB0 ++ LM ++ fr_ivs A4L FRS) SP); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP2 | intros bb Hbb; apply in_or_app; apply in_app_or in Hbb; destruct Hbb as [Hbb|Hbb]; [left; apply in_or_app; right; rewrite EREST; apply in_or_app; right; right; right; exact Hbb | right; exact Hbb] | clia |].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; left. exists q, 1024. split; [apply in_or_app; left; exact INqN|]. split; [exact NQM | lia].
- eapply heap_pres_weaken; [exact HPR3 | lia | intros bb Hbb; apply in_or_app; apply in_app_or in Hbb; destruct Hbb as [Hbb|Hbb]; [left; rewrite EREST; apply in_or_app; right; right; right; exact Hbb | right; exact Hbb]]. }
assert (AGP4 : agree_on asegs P m m3).
{ eapply agree_on_trans; [exact AGP3|]. eapply (agree_of_heap_pres asegs A4H); [exact HPR3 | reflexivity |].
intros b Hb. apply in_or_app; left. rewrite EREST. apply in_or_app; left; exact Hb. }
clear MU WM MI HPRa AGP3.

pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI. a4l.
pose proof (wmono_refl asegs m3) as WM. pose proof (munch_refl [(bse, bse + 32)] m3) as MU.
destruct (SHAD _ _ _ _ m3 HP3 INrR INqR) as [SHr SHl].
reenterA asegs A4L HIx asegs_wx HP3.
step. step. if_false. rewrite ?sxb_zero, ?zxb_zero.
step. step.
replace (q + (32 * Z.of_nat i + 16)) with (bse + 16) by lia.
step. asan_chkA.
step. stepz.
try clear SHr; try clear SHl.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TS3 : tstack asegs mc q (lupd levels i lvl_reset)) end.
{ rewrite <- (lupd_lupd levels i l2 lvl_reset). subst bse.
eapply (tstack_put asegs m3 _ q (lupd levels i l2) i lvl_reset []); [exact TS2 | rewrite lupd_length; lia | exact MU | exact WM | intros; exact I | unfold srec_cells; cbn [tl_st tl_ss tl_cur tl_name lvl_reset]; assumption]. }
evt_done5. apply K. unfold tf_body_postA.
replace (32 * Z.of_nat i + -16) with (32 * Z.of_nat i + 16 - 32) by (f_equal; lia).
do 20 eexists.
split; [reflexivity|].
split; [exact FS2|]. split; [exact FRM2|].
split; [eapply model_vm_only_trans; [exact VM2 | exact VM3]|].
split; [heap_nowA A4L HIx HP3 MU WM MI |].
split; [exact TS3|]. split; [unfold tok_cells; exact BLK|]. split; [unfold tf_frameA; exact FR|]. split; [assumption|].
split.
{ eapply heap_pres_trans; [exact HPRb|].
eapply (heap_pres_of_munch A4H (LB0 ++ LM ++ fr_ivs A4L FRS) SP); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP3 | intros bb Hbb; apply in_or_app; apply in_app_or in Hbb; destruct Hbb as [Hbb|Hbb]; [left; rewrite EREST; apply in_or_app; right; right; right; exact Hbb | right; exact Hbb] | clia |].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; left. exists q, 1024. split; [apply in_or_app; left; exact INqR|]. split; [exact NQM | lia]. }
split; [assumption|].
split; [eapply agree_on_trans; [exact AGP4|]; eapply (agree_of_munch asegs); [exact MU | exact WM | intros a n Hin; cbn; split; [pose proof (PDJ a n Hin); lia | exact I]] |].
clear - BB BB2 BD2 HB2 HD2. unfold put_costA in BB2. unfold lvl_blocks in *. rewrite ?length_app in *.
destruct (tl_cs l); rewrite ?Z.eqb_refl in BB2; destruct (tl_name l =? 0); cbn [bB bD charge uw_cost] in *; lia.
Qed.
End TokFreeA.
End RC__1.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek. Import QTEu. Import Qsw7 QJjn QRUw.
Import QnCn.Mq0. Import QZCq QSK8.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqg QgoM QsKa.Mqc Q30W.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Definition array_list_del_idx_A_entry : Z := 0xa2a10.

Lemma lor_land7 : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> x mod 8 = 0 -> y mod 8 = 0 ->
Z.land (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 x)) (bv_unsigned (Z_to_bv 64 y))))) 7 = 0.
Proof.
intros x y Hx Hy Mx My. rewrite (unsigned_lit x), (unsigned_lit y) by lia.
rewrite unsigned_lit by (pose proof (zr_lor x y ltac:(unfold inr64; lia) ltac:(unfold inr64; lia)) as R; unfold inr64 in R; lia).
rewrite Z.land_lor_distr_l, (ub_land7 x Mx), (ub_land7 y My). reflexivity.
Qed.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma al_del_loopA :
forall (k : nat) (i : Z) (x1 x2 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x24 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a arr len size stop : Z) (qs : list Z) (idx : Z),
Z.of_nat k = stop - 1 - i -> idx <= i < stop -> stop = Z.of_nat (length qs) -> stop <= len -> len <= size -> 8 * size < 2^64 ->
0 <= idx -> (forall j, idx <= j < stop -> al_nth qs j = 0) ->
mem_inv asegs m -> 0 < a -> a mod 8 = 0 -> a + AL_SZ <= alloc_ceiling -> 0 < arr -> arr mod 8 = 0 -> arr + 8 * size <= alloc_ceiling ->
rw_cells asegs m a [C8 (Z_to_bv 64 arr); C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 (fn_arr_entry_free A4F))] ->
u64arr asegs m arr (wl qs) ->
ro_cells asegs m (a / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
bytes_at asegs m (arr / 8 + A_SB) (shadow_bytes (8 * size)) ->
evt asegs (eq (MS (mkR x1 x2 gp tp t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 (a + 8)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) a4 a5 a6 a7
(Z_to_bv 64 a) x19 x20 x21 (Z_to_bv 64 (8 * stop)) (Z_to_bv 64 A_SB) x24 (Z_to_bv 64 (stop + 1152921504606846976)) (Z_to_bv 64 stop) (Z_to_bv 64 (a / 8 + A_SB)) t3 t4 t5 t6)
F (Z_to_bv 64 0xa2b58) fc None m (seg_rom asegs)))
(MS (mkR x1 x2 gp tp t0 t1 t2 (Z_to_bv 64 (stop - i)) (Z_to_bv 64 (a + 8)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 a) x19 x20 x21 (Z_to_bv 64 (8 * i)) (Z_to_bv 64 A_SB) x24 (Z_to_bv 64 (i + 1152921504606846976)) (Z_to_bv 64 stop) (Z_to_bv 64 (a / 8 + A_SB)) t3 t4 t5 t6)
F (Z_to_bv 64 0xa2af4) fc None m (seg_rom asegs)).
Proof.
induction k as [|k IH]; intros until idx; intros Hk Hi Hstop Hsl Hls H64 Hidx NUL MI Ha0 Ha8 Hah Hr0 Hr8 Hrh HDR ARR SHa SHr; unfold A_SB in *;
pose proof (u64arr_bound asegs m arr (wl qs) ARR) as AB; rewrite wl_length in AB;
pose proof (munch_refl [] m) as MU; pose proof (wmono_refl asegs m) as WM;
pose proof (ov_read1_of_ro asegs _ _ _ (shadow_granule0 asegs m (arr / 8 + 2147450880) (8 * size) i ltac:(lia) ltac:(lia) SHr)) as HR;
pose proof (al_slot_read asegs m arr qs i (wa (arr + 8 * i)) ARR ltac:(lia) eq_refl) as RD; rewrite (NUL i) in RD by lia.
- step. rewrite ?zxb_zero. step. if_false.
step. step.
step. step. step. ub_resolve.
step. step. ub_resolve.
step. ub_resolve.
step. ub_resolve.
step. step. step. ub_resolve.
step. step. sh_norm.
replace ((arr + 8 * i) / 8 + 2147450880) with (arr / 8 + 2147450880 + i) by (Z.div_mod_to_equations; lia).
step. rewrite ?zxb_zero. clear HR. step. if_false.
step. step. if_true.
step. step. step. step. if_truex.
ub_cmp_norm.
apply evt_done. replace (stop - i + -1) with 0 by lia. replace (8 * i + 8) with (8 * stop) by lia.
replace (i + 1152921504606846977) with (stop + 1152921504606846976) by lia. reflexivity.
- step. rewrite ?zxb_zero. step. if_false.
step. step.
step. step. step. ub_resolve.
step. step. ub_resolve.
step. ub_resolve.
step. ub_resolve.
step. step. step. ub_resolve.
step. step. sh_norm.
replace ((arr + 8 * i) / 8 + 2147450880) with (arr / 8 + 2147450880 + i) by (Z.div_mod_to_equations; lia).
step. rewrite ?zxb_zero. clear HR. step. if_false.
step. step. if_true.
step. step. step. step. if_falsex.
replace (stop - i + -1) with (stop - (i + 1)) by lia. replace (8 * i + 8) with (8 * (i + 1)) by lia.
replace (i + 1152921504606846977) with ((i + 1) + 1152921504606846976) by lia.
eapply (IH (i + 1)); [ | | exact Hstop | exact Hsl | exact Hls | exact H64 | exact Hidx | exact NUL | exact MI | | | | | | | exact HDR | exact ARR | exact SHa | exact SHr]; lia.
Qed.

Section Regs.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).

Definition array_list_del_idx_A_post (a arr size : Z) (ps zs : list Z) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (match zs with [] => 2^64 - 1 | _ => 0 end)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp); (a, a + AL_SZ); (arr, arr + 8 * size)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ alist asegs A4F m' [(a, AL_SZ); (arr, 8 * size)] a ps.

Lemma array_list_del_idx_A :
forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
(m : word -> option byte) (lo sbcell a arr size : Z) (ps zs : list Z),
small_pre sp m lo sbcell -> lo <= bv_unsigned sp - 144 - 4096 -> asan_rt_ok m ->
alist asegs A4F m [(a, AL_SZ); (arr, 8 * size)] a (ps ++ zs) ->
Forall (fun p => p = 0) zs ->
(a + AL_SZ <= arr \/ arr + 8 * size <= a) ->
al_blkA a arr size ->
ro_cells asegs m (a / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
bytes_at asegs m (arr / 8 + A_SB) (shadow_bytes (8 * size)) ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 (Z.of_nat (length ps)) -> a2 = Z_to_bv 64 (Z.of_nat (length zs)) ->
evt asegs (array_list_del_idx_A_post a arr size ps zs lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 array_list_del_idx_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until zs. intros (MI & ST & LOS16 & LO & GOT & CELL & Hc0 & Hc8) LOS RT AL NUL SEP (Ha0 & Ha8 & Hah & Hr0 & Hr8 & Hrh) SHa SHr SPA RA A0 A1 A2.
destruct (alist_openx asegs A4F m a arr size (ps ++ zs) AL) as (junk & HDR & ARR & JK & Hlen & Hsz).
unfold al_hdr in HDR. unfold al_tail in JK.
pose proof (length_app ps zs) as LA. apply (f_equal Z.of_nat) in LA. rewrite Nat2Z.inj_add in LA. rewrite LA in HDR.
pose proof (u64arr_bound asegs m arr (wl (ps ++ zs)) ARR) as AB. rewrite wl_length in AB.
pose proof (wl_length (ps ++ zs)) as WL.
unfold array_list_del_idx_A_entry, array_list_del_idx_A_post, A_GOT_SB, A_SB in *.
unfold alloc_ceiling, sp_window_lo, stack_max_size in LO, Hc8, Hah, Hrh. word_range sp SPR. subst a0 a1 a2.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)] m) as MU.
apply slots_of_u64arr in ARR. stash SHr. stash ARR. stash JK. stash RT.
carve_frame 144%nat ST.
do 14 step.

apply (rw_cells_split_CB asegs _ _ [] 40%nat _ _ [8;8;8;8;8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
step. step. step.
unfold v_xori. rewrite (unsigned_lit (Z.of_nat (length zs))) by lia. change (bv_wrap 64 (-1)) with 18446744073709551615.
rewrite lxor_ones64 by lia.
step. step. if_falsex.
step. ub_resolve.
step. step. ub_resolve.
step. step. step.
step.
asan_chkA.
step.
destruct zs as [|z zs'].
-
change (Z.of_nat (@length Z [])) with 0 in *. rewrite app_nil_r in *. rewrite Z.add_0_r in *. clear LA.
step. if_truex.
do 15 step.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
unstash ARR. unstash JK.
apply evt_done. do 15 eexists. split; [reflexivity|].
split. { eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia. }
split; [exact WM|]. split; [assumption|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|].
lazymatch goal with |- alist _ _ ?mf _ _ _ =>
eapply (rw_cells_transport asegs _ m mf) in ARR; [| exact MU | exact WM | cbn [disjoint_from]; rewrite slots_size; lia];
eapply (rw_cells_transport asegs _ m mf) in JK; [| exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; lia] end.
eapply alist_close. split; [| split; [apply u64arr_of_slots; exact ARR | split; [exact JK | lia]]]. unfold al_hdr. assumption.
- assert (LZ : 1 <= Z.of_nat (length (z :: zs'))) by (cbn [length]; lia).
step. if_falsex.
step. step. if_falsex.
step.
step. rewrite (unsigned_lit (Z.of_nat (length ps))) by lia. rewrite (Z.shiftl_mul_pow2 (Z.of_nat (length ps)) 3) by lia. change (2^3) with 8.
stepz.
step.
stepz.
step.
stepz.
step. sh_norm.
stepz.
step. if_falsex.
step.
step. step.
step. step. sh_norm.
step. step. step. step.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
assert (LEN2 : length (ps ++ z :: zs') = (length ps + S (length zs'))%nat) by (rewrite length_app; reflexivity).
unstash ARR. unstash JK. unstash SHr. unstash RT.
eapply (rw_cells_transport asegs _ m m1) in ARR; [| exact MU | exact WM | cbn [disjoint_from]; rewrite slots_size; lia].
eapply (rw_cells_transport asegs _ m m1) in JK; [| exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; rewrite <- ?LEN2; lia].
eapply (bytes_at_transport asegs _ m m1) in SHr; [| exact MU | cbn [disjoint_from]; rewrite shadow_bytes_length8 by lia; lia].
eapply (asan_rt_ok_transport _ m m1) in RT; [| exact MU | intros c Hc; pose proof (a4_rt_cells_in_img c Hc); cbn [disjoint_from]; lia].
apply u64arr_of_slots in ARR.
replace (Z.of_nat (length ps) * 8) with (8 * Z.of_nat (length ps)) by lia.
replace (Z_to_bv 64 (Z.of_nat (length (z :: zs')))) with (Z_to_bv 64 (Z.of_nat (length (z :: zs')) + Z.of_nat (length ps) - Z.of_nat (length ps))) by (f_equal; lia).
eapply evt_cut.
{ eapply al_del_loopA with (k := Z.to_nat (Z.of_nat (length (z :: zs')) - 1)) (i := Z.of_nat (length ps))
(a := a) (arr := arr) (len := Z.of_nat (length ps) + Z.of_nat (length (z :: zs'))) (size := size)
(stop := Z.of_nat (length (z :: zs')) + Z.of_nat (length ps)) (qs := ps ++ z :: zs') (idx := Z.of_nat (length ps));
[ | | | | | | | | assumption | | | | | | | exact HDR | exact ARR | unfold A_SB; eassumption | unfold A_SB; exact SHr ]; try lia.
intros j Hj. apply al_nth_app_r; [lia | exact NUL]. }
intros ms' <-. unfold A_SB.

destruct (al_tail_absorb asegs m1 arr size ps (z :: zs') junk ARR JK ltac:(lia)) as [ARR1 TL]. clear ARR JK.
unfold al_tail in TL.
pose proof (wl_length ps) as WL1.
step. step.
step. rewrite ?zxb_zero. step. if_false.
step.
step.
step.
step. step. step. ub_resolve.
step. step. step. ub_resolve.
step. ub_resolve.
step. rewrite (unsigned_lit (Z.of_nat (length (z :: zs')) + Z.of_nat (length ps))) by lia.
rewrite (Z.shiftl_mul_pow2 (Z.of_nat (length (z :: zs')) + Z.of_nat (length ps)) 3) by lia. change (2^3) with 8.
step.
step. step. ub_resolve.
step. step. step. step. ub_resolve.
step. ub_resolve.
step. step.
step. rewrite lor_land7 by (Z.div_mod_to_equations; lia). if_false.
step. rewrite ?zxb_zero. step. if_false.
step.
step. rewrite !unsigned_lit by lia.
replace (Z.of_nat (length ps) + Z.of_nat (length (z :: zs')) - (Z.of_nat (length (z :: zs')) + Z.of_nat (length ps))) with 0 by lia.
step.
step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (DST : rw_cells asegs mc (arr + 8 * Z.of_nat (length ps)) [CB 0%nat []])
by (split; [split; [cbn; auto | cbn; apply bytes_at_nil; lia] | cbn; split; [lia | split; [lia | intros i Hi; lia]]]);
assert (MU2 : munch [(lo, bv_unsigned sp); (a, a + 32); (arr, arr + 8 * size)] m mc)
by (eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia)
end.
clear MU. rename MU2 into MU.
eapply amemmove_sound_U with (d := arr + 8 * Z.of_nat (length ps)) (s := arr + 8 * (Z.of_nat (length (z :: zs')) + Z.of_nat (length ps))) (n := 0) (lo := lo) (old := []) (src := []);
first [ exact DST | exact RT | assumption | reflexivity | idtac ].
all: rewrite ?unsigned_lit by lia.
all: lazymatch goal with
| |- 0 < 0 -> _ => intros H00; lia
| |- bytes_at _ _ _ [] => apply bytes_at_nil; lia
| |- _ = Z_to_bv 64 _ => f_equal; lia
| |- stk _ _ _ _ => assumption
| |- mem_inv _ _ => assumption
| |- _ mod 16 = 0 => replace (bv_unsigned sp + -144) with (bv_unsigned sp - 144) by lia; rewrite Zminus_mod, SPA; reflexivity
| |- forall _, _ => idtac
| |- _ => first [lia | unfold A_SB; Z.div_mod_to_equations; lia]
end.
intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m4 MU4 WM4 MI4 DST4 SRC4 ST4.
lazymatch type of MU4 with munch _ ?mc _ =>
transport_after_call asegs mc m4 MU4 WM4; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU4 WM4 end.
replace (ret_pc (Z_to_bv 64 0xa2bd8)) with (Z_to_bv 64 0xa2bd8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step.
step.
step. rewrite !unsigned_lit by lia.
replace (Z.of_nat (length ps) + Z.of_nat (length (z :: zs')) - (Z.of_nat (length (z :: zs')) + Z.of_nat (length ps) - Z.of_nat (length ps))) with (Z.of_nat (length ps)) by lia.
step.
do 15 step.
apply evt_done. do 15 eexists. split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split. { lazymatch goal with |- stk _ ?mf _ _ => match goal with FRx : rw_cells asegs mf (bv_unsigned sp + -144) _, STx : stk asegs mf _ _ |- _ =>
release_frame FRx STx (bv_unsigned sp); exact STx end end. }
eapply alist_close. split; [| split; [eassumption | split; [eassumption | lia]]]. unfold al_hdr. eassumption.
Qed.
End Regs.
End RC__1.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ. Import QTEu. Import Qsw7 QJjn QRUw QKQo.
Import Q6WR Q6WR.Mq0 QrPc.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqh QlKV.Mqj QsKa.Mqg QpNt.Mq8 QJZd.Mqd QW22.Mq6 QFZX.Mq6 QnDr.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma nodup_blk_size : forall (BS : list blk) a n k, List.NoDup (map blk_addr BS) -> In (a, n) BS -> In (a, k) BS -> n = k.
Proof.
induction BS as [|[b0 n0] BS IH]; intros a n k ND Hn Hk; [destruct Hn|].
cbn in ND. inversion ND as [|y l Hni Hnd]; subst.
destruct Hn as [Hn|Hn]; destruct Hk as [Hk|Hk].
- congruence.
- exfalso. apply Hni. apply in_map_iff. exists (a, k). injection Hn as -> ->. split; [reflexivity | exact Hk].
- exfalso. apply Hni. apply in_map_iff. exists (a, n). injection Hk as -> ->. split; [reflexivity | exact Hn].
- eapply IH; [exact Hnd | exact Hn | exact Hk].
Qed.

Section MF4.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Definition mf_objA_stmt : Prop :=
forall (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud) (lo : Z) (errv : word)
(s : jshape) (BS : list blk) (x rc : Z) (T : TSet) (kids : list (option jshape))
(x1 t0 t1 t2 x9 a0 a2 a3 a4 a5 a6 a7 x18 x20 x21 x22 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud),
s = Sobj kids ->
HEAPAx A (BS ++ LB) LM FRS B m md ->
jval asegs A4F s m BS x 0 ->
mf_frameA ra sp s0 s1 s2 s3 s4 s5 s6 m ->
stk asegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -64 - 96 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> bv_unsigned ra mod 2 = 0 ->
model_vm_only (cfg_model md0) (cfg_model md) -> heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m -> fsaved F F1 -> (frm0 fc -> frm0 fc1) -> rc = 1 ->
bD B0 <= bD B -> bB B0 <= bB B -> 512 * Z.of_nat (length BS) <= bB B ->
KPOSTA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo errv s BS x rc T ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 x) x9 a0 (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7
x18 (Z_to_bv 64 A_SB) x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x9c30c) fc1 None m (seg_rom asegs)).
Hypothesis MF_OBJ : mf_objA_stmt.

Lemma maybe_free_A_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word) (s : jshape) (BS : list blk) (x rc : Z),
HEAPAx A (BS ++ LB) LM FRS B m md ->
x <> 0 -> 1 <= rc < 2^31 -> jval asegs A4F s m BS x rc ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 - 96 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 x -> a1 = Z_to_bv 64 0 ->
(rc = 1 -> 512 * Z.of_nat (length BS) <= bB B) ->
(forall ms1 md1 A1, mf_postA HIx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo errv s BS x rc ms1 md1 A1 ->
AJ5 A4L HIx A1 T md1 ms1) ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9c240) fc None m (seg_rom asegs)).
Proof.
intros until rc. intros HP Hx Hrc J ST LO LOS SPA HT ERR TP RA A0 A1 BB K.
unfold_consts. unfold A_SB, A_TP, A_ERRNO in *. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP) as [HB00 HD00].
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (nodup_app_l' BS LB (nodup_app_l' (BS ++ LB) LM (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP))) as ND.
destruct (jval_hdr asegs A4F s m BS x rc J ND) as (n & tojs & pb & udel & ud & rest & INx & SZ & N48 & HDR & CLOSE).
assert (INx2 : In (x, n) ((BS ++ LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; left; exact INx).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ x n HP INx2) as (_ & Hxal & Hxlo & Hxhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ x n HP INx2) as Hximg.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ x n HP ltac:(apply in_or_app; left; exact INx)) as SHx. unfold shad in SHx.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ x n 0 x n HP ltac:(apply in_or_app; left; exact INx) ltac:(lia) INx2) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ x n 5 x n HP ltac:(apply in_or_app; left; exact INx) ltac:(Z.div_mod_to_equations; lia) INx2) as SEP5.
a4l.
assert (SH : ro_cells asegs m (x / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
{ rewrite (shadow_bytes_split n 6) in SHx by lia.
apply bytes_at_app in SHx as [SH6 _]. split; [cbn; repeat split; exact I | cbn [cells_bytes cbytes app]; exact SH6]. }
clear SHx.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (x + 4, x + 8)] m) as MU.
pose proof SZ as RSZ. rewrite cells_size_app in RSZ. cbn [cells_size csize jhdr_cells Nat.add] in RSZ.
unfold jhdr_cells in HDR. cbn [app] in HDR.
reenterA asegs A4L HIx asegs_wx HP. subst a0 a1 tp.
carve_frame 64%nat ST.
do 9 bstep.
bstep. bstep. ub_resolve.
bstep.
bstep. bstep. bstep.
bstep.
asan_chkA.
bstep. norm_w32. bstep. norm_w32. bstepz.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.

assert (AG1 : agree_on asegs (others x BS) m m1).
{ eapply (agree_others_gen asegs); [exact MU | exact WM |].
intros a k Hin Hne.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin)) as (Hk & _ & _ & Hahi & _).
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ x n a k HP INx2 ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin) ltac:(congruence)) as D.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hahi. cbn. lia. }
assert (HP1 : HEAPAx A (BS ++ LB) LM FRS B m1 md) by heap_nowA A4L HIx HP MU WM MI.
assert (HPR1 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m1).
{ eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; rewrite <- app_assoc; apply in_or_app; right; exact Hb | clia |].
apply Forall_cons; [cbn [fst snd]; left; clia |].
apply Forall_cons; [cbn [fst snd] | apply Forall_nil]. right; left. exists x, n. split; [exact INx2|]. split; [| lia].
exact (not_in_app3 _ _ _ _ (nodup_prefix_suffix BS (LB ++ LM) x n n ltac:(pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as NDx; rewrite <- app_assoc in NDx; exact NDx) INx) (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP INx2)). }
bstep.
destruct (Z.eq_dec rc 1) as [Hrc1 | Hrc2].
-
subst rc. specialize (BB eq_refl). if_true.
assert (J1 : jval asegs A4F s m1 BS x 0).
{ apply (CLOSE m1 0); [| exact AG1]. unfold jhdr_cells. cbn [app]. replace (1 + -1) with 0 in HDR by lia. exact HDR. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (ZERO : forall (ty tojs' pb' udel' ud' : Z) (rest' : list cell) (BS' : list blk) (m2 : word -> option byte) (md2 : config) (A2 : ASA A4L HIx) (B2 : bud)
(xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt0 xt1 xt2 xt3 xt4 xt5 xt6 xra xs4 xs6 : word),
HEAPAx A2 (BS' ++ LB) LM FRS B2 m2 md2 -> In (x, n) BS' ->
rw_cells asegs m2 x (jhdr_cells ty 0 tojs' pb' udel' ud' ++ rest') -> Z.of_nat (cells_size (jhdr_cells ty 0 tojs' pb' udel' ud' ++ rest')) = n ->
mf_frameA ra sp s0 s1 s2 s3 s4 s5 s6 m2 ->
stk asegs m2 lo (bv_unsigned sp + -64) ->
rw_cells asegs m2 (6444320 - 164) [C4 errv] ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m2 ->
bD B <= bD B2 ->
(forall m3 (ya0 ya2 ya3 ya4 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 yt5 yt6 yra ys2 ys4 ys5 ys6 : word),
HEAPAx A2 (BS' ++ LB) LM FRS B2 m3 md2 ->
rw_cells asegs m3 x (jhdr_cells ty 0 tojs' pb' 0 0 ++ rest') ->
mf_frameA ra sp s0 s1 s2 s3 s4 s5 s6 m3 ->
stk asegs m3 lo (bv_unsigned sp + -64) ->
rw_cells asegs m3 (6444320 - 164) [C4 errv] ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m3 ->
agree_on asegs (others x BS') m2 m3 ->
evt asegs (AJ5e A4L HIx A2 T md2)
(MS (mkR yra (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 6444320) yt0 yt1 yt2 (Z_to_bv 64 x) (Z_to_bv 64 (x + 24))
ya0 (Z_to_bv 64 0) ya2 ya3 ya4 ya5 ya6 ya7 ys2 (Z_to_bv 64 2147450880) ys4 ys5 ys6 s7 s8 s9 s10 s11 yt3 yt4 yt5 yt6)
F (Z_to_bv 64 0x9c30c) fc None m3 (seg_rom asegs))) ->
evt asegs (AJ5e A4L HIx A2 T md2)
(MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 6444320) xt0 xt1 xt2 (Z_to_bv 64 x) (Z_to_bv 64 (x + 24))
xa0 (Z_to_bv 64 0) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (x + 32)) (Z_to_bv 64 2147450880) xs4 (Z_to_bv 64 (x / 8 + 2147450883)) xs6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
F (Z_to_bv 64 0x9c2ec) fc None m2 (seg_rom asegs)))
end.
{ intros ty tojs' pb' udel' ud' rest' BS' m2 md2 A2 B2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt0 xt1 xt2 xt3 xt4 xt5 xt6 xra xs4 xs6 HP2 INx' HDR2 SZ2 FR2 ST2 ERR2 HPR2 BD2 KZ.
clear MU WM AG1 HP1 HPR1 J1 CLOSE HDR J SH.
unfold mf_frameA in FR2.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI2.
assert (INx3 : In (x, n) ((BS' ++ LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; left; exact INx').
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ x n HP2 ltac:(apply in_or_app; left; exact INx')) as SHx2. unfold shad in SHx2. a4l.
pose proof (shadow_granule0 asegs m2 (x / 8 + 2147450880) n 3 ltac:(lia) ltac:(lia) SHx2) as SH3.
pose proof (shadow_granule0 asegs m2 (x / 8 + 2147450880) n 4 ltac:(lia) ltac:(lia) SHx2) as SH4.
replace (x / 8 + 2147450880 + 3) with (x / 8 + 2147450883) in SH3 by lia.
replace (x / 8 + 2147450880 + 4) with (x / 8 + 2147450884) in SH4 by lia. clear SHx2.
pose proof (wmono_refl asegs m2) as WM. pose proof (munch_refl [(x + 24, x + 40)] m2) as MU.
pose proof SZ2 as RSZ2. rewrite cells_size_app in RSZ2. cbn [cells_size csize jhdr_cells Nat.add] in RSZ2.
unfold jhdr_cells in HDR2. cbn [app] in HDR2.
bstep. rewrite ?zxb_zero. bstep. if_false.
bstepz.
bstep. bstep. sh_norm. rewrite (div8_add x 32) by lia. change (32 / 8) with 4.
bstep. rewrite ?zxb_zero. bstep. if_false.
bstepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (AG4 : agree_on asegs (others x BS') m2 mc);
[ eapply (agree_others_gen asegs); [exact MU | exact WM |]; intros a k Hin Hne;
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP2 ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin)) as (Hk & _ & _ & Hahi & _);
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ x n a k HP2 INx3 ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin) ltac:(congruence)) as D;
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hahi; cbn; lia |]
end.
eapply KZ.
- lazymatch goal with Hmi : mem_inv asegs ?mc |- HEAPA _ _ _ _ _ _ _ ?mc _ => heap_nowA A4L HIx HP2 MU WM Hmi end.
- unfold jhdr_cells. cbn [app]. exact HDR2.
- unfold mf_frameA. first [ exact FR2 | lazymatch goal with |- rw_cells _ ?mc _ _ => eapply (rw_cells_transport asegs _ m2 mc) in FR2; [exact FR2 | exact MU | exact WM | cbn [disjoint_from]; lia] end ].
- exact ST2.
- first [ exact ERR2 | lazymatch goal with |- rw_cells _ ?mc _ _ => eapply (rw_cells_transport asegs _ m2 mc) in ERR2; [exact ERR2 | exact MU | exact WM | cbn [disjoint_from]; lia] end ].
- eapply heap_pres_trans; [exact HPR2|].
eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP2 | intros b Hb; rewrite <- app_assoc; apply in_or_app; right; exact Hb | clia |].
apply Forall_cons; [cbn [fst snd] | apply Forall_nil]. right; left. exists x, n. split; [exact INx3|]. split; [| lia].
exact (not_in_app3 _ _ _ _ (nodup_prefix_suffix BS' (LB ++ LM) x n n ltac:(pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP2) as NDx; rewrite <- app_assoc in NDx; exact NDx) INx') (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP2 INx3)).
- exact AG4. }
clear MU WM J.

assert (C8F : forall mq aq cs1 cs2 k v1 v2, rw_cells asegs mq aq cs1 -> rw_cells asegs mq aq cs2 ->
cell_at cs1 k = Some (C8 v1) -> cell_at cs2 k = Some (C8 v2) -> v1 = v2).
{ clear. intros mq aq cs1 cs2 k v1 v2 R1 R2 E1 E2.
pose proof (rw_cells_read asegs _ _ _ _ _ R1 E1) as Q1. pose proof (rw_cells_read asegs _ _ _ _ _ R2 E2) as Q2.
cbn [csize cbytes] in Q1, Q2. rewrite Q1 in Q2. apply (f_equal (option_map le_bytes_to_word)) in Q2.
cbn [option_map] in Q2. rewrite !le_bytes_to_word_le8 in Q2. injection Q2 as E. exact E. }
pose proof (wmono_refl asegs m1) as WM. pose proof (munch_refl [] m1) as MU.

assert (INCLo : forall b, In b BS -> blk_addr b <> x -> In b (others x BS)) by (intros [ba bn] Hb Hne; apply in_others; [exact Hb | exact Hne]).

Ltac udel_steps := bstep; asan_chkA; bstep; bstep.
destruct s as [|u| |h|kids|kids].
+
clear HDR AG1 CLOSE C8F.
pose proof J1 as J2. destruct J2 as (pb1 & PBS & REST & EBS & OPB & b & junkb & ER & HDR1). subst REST.
assert (n = 48) by (eapply (nodup_blk_size BS x); [exact ND | exact INx | subst BS; left; reflexivity]). subst n.
unfold jhdr_cells in HDR1. cbn [app] in HDR1.
udel_steps. bstep. if_true.
eapply (ZERO JT_BOOLEAN _ pb1 0 0 ([C4 (Z_to_bv 64 b); CB 4 junkb]) BS m1 md A B);
[ exact HP1 | exact INx | unfold jhdr_cells; cbn [app]; exact HDR1 | subst BS; cbn; lia | unfold mf_frameA; exact FR | exact ST | assumption | exact HPR1 | lia |].
intros m3 ya0 ya2 ya3 ya4 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 yt5 yt6 yra ys2 ys4 ys5 ys6 HP3 HDR3 FR3 ST3 ERR3 HPR3 AG3.
evt_done5.
eapply (mf_scalarA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo errv Sbool BS x 1 T) with (n := 48) (PBS := PBS);
[ subst BS; cbn [app] in HP3 |- *; exact HP3 | lia | exact HDR3 | left; reflexivity
| eapply opt_pbuf_agree; [exact OPB | exact AG3 | intros bb Hbb; apply INCLo; [subst BS; in_sub Hbb | ]]
| exact FR3 | exact ST3 | clia | clia | exact SPA | exact HT | exact ERR3 | exact RA | apply model_vm_only_refl | exact HPR3
| apply fsaved_refl | intros Hf; exact Hf | reflexivity | lia | subst BS; cbn [length app] in *; lia | subst BS; cbn [length app] in *; lia | exact K ].
subst BS. intros E. cbn in E.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP1) as NDx. cbn in NDx. inversion NDx as [|z l Hni Hnd]. apply Hni.
rewrite map_app. apply in_or_app. left. rewrite map_app. apply in_or_app. left. rewrite <- E. apply in_map_iff. exists bb. split; [reflexivity | exact Hbb].
+ clear HDR AG1 CLOSE C8F. destruct u.
*
pose proof J1 as J2. destruct J2 as (pb1 & PBS & REST & EBS & OPB & bits & ud1 & udn & uds & ER & HU & HDR1 & HC). subst REST.
assert (n = 48) by (eapply (nodup_blk_size BS x); [exact ND | exact INx | subst BS; left; reflexivity]). subst n.
assert (INud : In (ud1, udn) ((BS ++ LB) ++ LM)) by (subst BS; apply in_or_app; left; apply in_or_app; left; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ ud1 udn HP1 INud) as (Hudn & Hual & Hulo & Huhi & _).
assert (Hxud : x <> ud1).
{ intros E. subst BS. pose proof ND as NDx. cbn in NDx. inversion NDx as [|z l Hni Hnd]. apply Hni. left. symmetry. exact E. }
unfold jhdr_cells in HDR1. cbn [app fn_ud_to_json_string fn_free_userdata A4F] in HDR1. a4l.
udel_steps. bstep. if_falsex.
asan_chkA.
bstep. bstep. bstep.
bstep.
bstep. bstep.

alloc_callA (hiA_free A4L HIx) blk ud1 uw UWptr A4L HIx HP1 MU WM ltac:(pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MIq; exact MIq).
all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists udn. subst BS. apply in_or_app. left. right. left. reflexivity. }
all: try (cbn [uw_pre uw_ok uw_key uw_cost]; intros _; split; [left; lia | unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (destruct (Z.eqb_spec ud1 0); cbn [bB bD charge uw_cost] in *; subst BS; cbn [length app] in BB; lia).
intros ms2 m2 md2 A2 r2 RS2 VM2 ST2 HPR2 ERR2 HP2. open_ret RS2. a4l.
rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in ST2 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in HPR2 by lia.
replace (if ud1 =? 0 then 0 else uw_cost UWptr) with 0 in HP2 by (destruct (Z.eqb_spec ud1 0); reflexivity).
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia].
assert (EREM : lb_remove ud1 (BS ++ LB) = ((x, 48) :: PBS) ++ LB).
{ subst BS. cbn [app]. rewrite lb_remove_other by (cbn; lia). rewrite lb_remove_head. reflexivity. }
rewrite EREM in HP2, HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in HDR1; [| eapply (client_range_block A4H _ _ _ _ x 48); [apply in_or_app; left; left; reflexivity | lia | cbn; lia]].
assert (OPB2 : opt_pbuf asegs m2 PBS pb1).
{ eapply opt_pbuf_agree; [exact OPB | | apply incl_refl].
eapply (agree_of_heap_pres asegs A4H); [exact HPR2 | reflexivity | intros bb Hbb; cbn; right; apply in_or_app; left; apply in_or_app; left; exact Hbb]. }
assert (HPR12 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m2).
{ eapply heap_pres_trans; [exact HPR1|]. eapply heap_pres_weaken; [exact HPR2 | lia | intros bb Hbb; cbn; right; apply in_or_app; apply in_app_or in Hbb; destruct Hbb; [left; apply in_or_app; right; assumption | right; assumption]]. }
clear MU WM.
reenterA asegs A4L HIx asegs_wx HP2.
bstep.
eapply (ZERO JT_DOUBLE _ pb1 _ _ ([C8 bits]) ((x, 48) :: PBS) m2 md2 A2 _);
[ exact HP2 | left; apply (f_equal2 pair); [reflexivity | cbn; lia] | unfold jhdr_cells; cbn [app]; exact HDR1 | cbn; lia | unfold mf_frameA; exact FR | exact ST2 | exact ERR2 | exact HPR12
| cbn [bD charge]; lia |].
intros m3 ya0 ya2 ya3 ya4 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 yt5 yt6 yra ys2 ys4 ys5 ys6 HP3 HDR3 FR3 ST3 ERR3 HPR3 AG3.
evt_done5.
eapply (mf_scalarA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo errv (Sdouble true) BS x 1 T) with (n := 48) (PBS := PBS);
[ exact HP3 | lia | exact HDR3 | right; left; reflexivity
| eapply opt_pbuf_agree; [exact OPB2 | exact AG3 | intros [ba bn] Hbb; apply in_others; [right; exact Hbb |]]
| exact FR3 | exact ST3 | clia | clia | exact SPA | exact HT | exact ERR3 | exact RA | exact VM2 | exact HPR3
| apply fsaved_refl | intros Hf; exact Hf | reflexivity | cbn [bD charge] in *; lia
| subst BS; cbn [bB charge length app] in *; lia | subst BS; cbn [bB charge length app] in *; lia | exact K ].
intros E. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP2) as NDx. cbn in NDx. inversion NDx as [|z l Hni Hnd]. apply Hni.
rewrite map_app. apply in_or_app. left. rewrite map_app. apply in_or_app. left. rewrite <- E. apply in_map_iff. exists (ba, bn). split; [reflexivity | exact Hbb].
*
pose proof J1 as J2. destruct J2 as (pb1 & PBS & REST & EBS & OPB & bits & ER & HSP & HDR1). subst REST.
assert (n = 48) by (eapply (nodup_blk_size BS x); [exact ND | exact INx | subst BS; left; reflexivity]). subst n.
unfold jhdr_cells in HDR1. cbn [app] in HDR1.
udel_steps. bstep. if_true.
eapply (ZERO JT_DOUBLE _ pb1 0 0 ([C8 bits]) BS m1 md A B);
[ exact HP1 | exact INx | unfold jhdr_cells; cbn [app]; exact HDR1 | subst BS; cbn; lia | unfold mf_frameA; exact FR | exact ST | assumption | exact HPR1 | lia |].
intros m3 ya0 ya2 ya3 ya4 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 yt5 yt6 yra ys2 ys4 ys5 ys6 HP3 HDR3 FR3 ST3 ERR3 HPR3 AG3.
evt_done5.
eapply (mf_scalarA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo errv (Sdouble false) BS x 1 T) with (n := 48) (PBS := PBS);
[ subst BS; cbn [app] in HP3 |- *; exact HP3 | lia | exact HDR3 | right; left; reflexivity
| eapply opt_pbuf_agree; [exact OPB | exact AG3 | intros bb Hbb; apply INCLo; [subst BS; in_sub Hbb | ]]
| exact FR3 | exact ST3 | clia | clia | exact SPA | exact HT | exact ERR3 | exact RA | apply model_vm_only_refl | exact HPR3
| apply fsaved_refl | intros Hf; exact Hf | reflexivity | lia | subst BS; cbn [length app] in *; lia | subst BS; cbn [length app] in *; lia | exact K ].
subst BS. intros E. cbn in E.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP1) as NDx. cbn in NDx. inversion NDx as [|z l Hni Hnd]. apply Hni.
rewrite map_app. apply in_or_app. left. rewrite map_app. apply in_or_app. left. rewrite <- E. apply in_map_iff. exists bb. split; [reflexivity | exact Hbb].
+
clear HDR AG1 CLOSE C8F.
pose proof J1 as J2. destruct J2 as (pb1 & PBS & REST & EBS & OPB & cty & v & junki & ER & HCT & HDR1). subst REST.
assert (n = 56) by (eapply (nodup_blk_size BS x); [exact ND | exact INx | subst BS; left; reflexivity]). subst n.
unfold jhdr_cells in HDR1. cbn [app] in HDR1.
udel_steps. bstep. if_true.
eapply (ZERO JT_INT _ pb1 0 0 ([C4 (Z_to_bv 64 cty); CB 4 junki; C8 v]) BS m1 md A B);
[ exact HP1 | exact INx | unfold jhdr_cells; cbn [app]; exact HDR1 | subst BS; cbn; lia | unfold mf_frameA; exact FR | exact ST | assumption | exact HPR1 | lia |].
intros m3 ya0 ya2 ya3 ya4 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 yt5 yt6 yra ys2 ys4 ys5 ys6 HP3 HDR3 FR3 ST3 ERR3 HPR3 AG3.
evt_done5.
eapply (mf_scalarA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo errv Sint BS x 1 T) with (n := 56) (PBS := PBS);
[ subst BS; cbn [app] in HP3 |- *; exact HP3 | lia | exact HDR3 | right; right; reflexivity
| eapply opt_pbuf_agree; [exact OPB | exact AG3 | intros bb Hbb; apply INCLo; [subst BS; in_sub Hbb | ]]
| exact FR3 | exact ST3 | clia | clia | exact SPA | exact HT | exact ERR3 | exact RA | apply model_vm_only_refl | exact HPR3
| apply fsaved_refl | intros Hf; exact Hf | reflexivity | lia | subst BS; cbn [length app] in *; lia | subst BS; cbn [length app] in *; lia | exact K ].
subst BS. intros E. cbn in E.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP1) as NDx. cbn in NDx. inversion NDx as [|z l Hni Hnd]. apply Hni.
rewrite map_app. apply in_or_app. left. rewrite map_app. apply in_or_app. left. rewrite <- E. apply in_map_iff. exists bb. split; [reflexivity | exact Hbb].
+
assert (EU : Z_to_bv 64 udel = Z_to_bv 64 0 /\ Z_to_bv 64 ud = Z_to_bv 64 0).
{ pose proof J1 as J2. destruct h.
- destruct J2 as (pb1 & PBS & REST & EBS & OPB & len & pd & pdn & str & junk2 & ER & HL & HS & HPD & HDR1 & HD).
unfold jhdr_cells in HDR1. cbn [app] in HDR1.
split; [ eapply (C8F m1 x _ _ 24%nat); [exact HDR | exact HDR1 | reflexivity | reflexivity]
| eapply (C8F m1 x _ _ 32%nat); [exact HDR | exact HDR1 | reflexivity | reflexivity] ].
- destruct J2 as (pb1 & PBS & REST & EBS & OPB & len & str & junks & ER & HL & HS & HDR1).
unfold jhdr_cells in HDR1. cbn [app] in HDR1.
split; [ eapply (C8F m1 x _ _ 24%nat); [exact HDR | exact HDR1 | reflexivity | reflexivity]
| eapply (C8F m1 x _ _ 32%nat); [exact HDR | exact HDR1 | reflexivity | reflexivity] ]. }
destruct EU as [EU1 EU2]. rewrite EU1, EU2 in HDR. replace (1 + -1) with 0 in HDR by lia.
unfold jhdr_cells in CLOSE. rewrite EU1, EU2 in CLOSE.
udel_steps. bstep. if_true.
eapply (ZERO (jtype (Sstr h)) tojs pb 0 0 rest BS m1 md A B);
[ exact HP1 | exact INx | unfold jhdr_cells; cbn [app]; exact HDR
| rewrite cells_size_app; cbn [cells_size csize jhdr_cells Nat.add]; exact RSZ
| unfold mf_frameA; exact FR | exact ST | assumption | exact HPR1 | lia |].
intros m3 ya0 ya2 ya3 ya4 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 yt5 yt6 yra ys2 ys4 ys5 ys6 HP3 HDR3 FR3 ST3 ERR3 HPR3 AG3.
evt_done5.
assert (J3 : jval asegs A4F (Sstr h) m3 BS x 0)
by (apply (CLOSE m3 0); [cbn [app]; unfold jhdr_cells in HDR3; cbn [app] in HDR3; exact HDR3 | eapply agree_on_trans; [exact AG1 | exact AG3]]).
eapply (mf_strA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo errv (Sstr h) BS x 1 T h);
[ reflexivity | exact HP3 | exact J3 | exact FR3 | exact ST3 | clia | clia | exact SPA | exact HT | exact ERR3 | exact RA
| apply model_vm_only_refl | exact HPR3 | apply fsaved_refl | intros Hf; exact Hf | reflexivity | lia | lia | exact BB | exact K ].
+
assert (EU : Z_to_bv 64 udel = Z_to_bv 64 0 /\ Z_to_bv 64 ud = Z_to_bv 64 0).
{ destruct (jval_obj_open asegs A4F kids m1 BS x 0 J1) as (pb1 & PBS & t & TBS & kvs & KBS & EBS & OPB & HDR1 & LT & OK).
unfold jhdr_cells in HDR1. cbn [app] in HDR1.
split; [ eapply (C8F m1 x _ _ 24%nat); [exact HDR | exact HDR1 | reflexivity | reflexivity]
| eapply (C8F m1 x _ _ 32%nat); [exact HDR | exact HDR1 | reflexivity | reflexivity] ]. }
destruct EU as [EU1 EU2]. rewrite EU1, EU2 in HDR. replace (1 + -1) with 0 in HDR by lia.
unfold jhdr_cells in CLOSE. rewrite EU1, EU2 in CLOSE.
udel_steps. bstep. if_true.
eapply (ZERO (jtype (Sobj kids)) tojs pb 0 0 rest BS m1 md A B);
[ exact HP1 | exact INx | unfold jhdr_cells; cbn [app]; exact HDR
| rewrite cells_size_app; cbn [cells_size csize jhdr_cells Nat.add]; exact RSZ
| unfold mf_frameA; exact FR | exact ST | assumption | exact HPR1 | lia |].
intros m3 ya0 ya2 ya3 ya4 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 yt5 yt6 yra ys2 ys4 ys5 ys6 HP3 HDR3 FR3 ST3 ERR3 HPR3 AG3.
evt_done5.
assert (J3 : jval asegs A4F (Sobj kids) m3 BS x 0)
by (apply (CLOSE m3 0); [cbn [app]; unfold jhdr_cells in HDR3; cbn [app] in HDR3; exact HDR3 | eapply agree_on_trans; [exact AG1 | exact AG3]]).
pose proof MF_OBJ as MFO. unfold mf_objA_stmt in MFO.
eapply (MFO ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo errv (Sobj kids) BS x 1 T kids);
[ reflexivity | exact HP3 | exact J3 | exact FR3 | exact ST3 | clia | clia | exact SPA | exact HT | exact ERR3 | exact RA
| apply model_vm_only_refl | exact HPR3 | apply fsaved_refl | intros Hf; exact Hf | reflexivity | lia | lia | exact BB | exact K ].
+
assert (EU : Z_to_bv 64 udel = Z_to_bv 64 0 /\ Z_to_bv 64 ud = Z_to_bv 64 0).
{ destruct (jval_arr_open asegs A4F kids m1 BS x 0 J1) as (pb1 & PBS & a & ABS & ps & KBS & EBS & OPB & HDR1 & AL & OK).
unfold jhdr_cells in HDR1. cbn [app] in HDR1.
split; [ eapply (C8F m1 x _ _ 24%nat); [exact HDR | exact HDR1 | reflexivity | reflexivity]
| eapply (C8F m1 x _ _ 32%nat); [exact HDR | exact HDR1 | reflexivity | reflexivity] ]. }
destruct EU as [EU1 EU2]. rewrite EU1, EU2 in HDR. replace (1 + -1) with 0 in HDR by lia.
unfold jhdr_cells in CLOSE. rewrite EU1, EU2 in CLOSE.
udel_steps. bstep. if_true.
eapply (ZERO (jtype (Sarr kids)) tojs pb 0 0 rest BS m1 md A B);
[ exact HP1 | exact INx | unfold jhdr_cells; cbn [app]; exact HDR
| rewrite cells_size_app; cbn [cells_size csize jhdr_cells Nat.add]; exact RSZ
| unfold mf_frameA; exact FR | exact ST | assumption | exact HPR1 | lia |].
intros m3 ya0 ya2 ya3 ya4 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 yt5 yt6 yra ys2 ys4 ys5 ys6 HP3 HDR3 FR3 ST3 ERR3 HPR3 AG3.
evt_done5.
assert (J3 : jval asegs A4F (Sarr kids) m3 BS x 0)
by (apply (CLOSE m3 0); [cbn [app]; unfold jhdr_cells in HDR3; cbn [app] in HDR3; exact HDR3 | eapply agree_on_trans; [exact AG1 | exact AG3]]).
eapply (mf_arrA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo errv (Sarr kids) BS x 1 T kids);
[ reflexivity | exact HP3 | exact J3 | exact FR3 | exact ST3 | clia | clia | exact SPA | exact HT | exact ERR3 | exact RA
| apply model_vm_only_refl | exact HPR3 | apply fsaved_refl | intros Hf; exact Hf | reflexivity | lia | lia | exact BB | exact K ].
-
if_falsex. bstep. bstep.
do 9 bstep. release_frame FR ST (bv_unsigned sp). bstep.
evt_done5. apply K. unfold mf_postA.
exists m1, 0, B.
split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|]. split; [exact ST|]. split; [exact HPR1|]. split; [assumption|]. split; [lia|].
left. split; [reflexivity|]. split; [lia|]. split; [| split; [lia | exact HP1]].
apply (CLOSE m1 (rc - 1)); [| exact AG1]. unfold jhdr_cells. cbn [app]. replace (rc + -1) with (rc - 1) in HDR by lia. exact HDR.
Qed.
End MF4.
End RC__1.
End Mq4.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qtgi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qtgi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKQo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKQo. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPZI.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlCE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlCE.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QhHQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QhHQ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Ki.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Ki. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkMG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkMG.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6WR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6WR.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrPc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrPc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXUB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXUB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q30W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q30W.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqf.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc5u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc5u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZUC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZUC.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition tokfree_loop_B_pc : Z := 0x938d0.
Definition tokfree_ret_B_pc : Z := 0x938dc.
Definition tokfree_exit_B_pc : Z := 0x938e4.

Definition tfv_frame (m : word -> option byte) (spv : Z) (s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) : Prop :=
rw_cells asegs m spv [C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].

Section TokFree1B.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis PUT : put_stmt_A HIx.

Definition tf_body_postB (spv r : Z) (gp s1 s2 s4 s5 s6 s7 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(md : config) (REST LB0 P LM : list blk) (FRS : list frame) (B : bud) (me mpre : word -> option byte) (lo : Z) (errv : word)
(q pb depth : Z) (x : tscal) (levels : list tlevel) (i : nat) (l : tlevel) (s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (B' : bud) F' fc' x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
ms' = MS (mkR x1 (Z_to_bv 64 spv) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 r) s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 (Z.of_nat i)) s4 s5 s6 s7 (Z_to_bv 64 (-1)) s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 tokfree_ret_B_pc) fc' None m' (seg_rom asegs) /\
fsaved F F' /\ (frm0 fc -> frm0 fc') /\
model_vm_only (cfg_model md) (cfg_model md') /\
HEAPAx A' REST LM FRS B' m' md' /\
tstack asegs m' q (lupd levels i lvl_reset) /\
rw_cells asegs m' r (tok_cells_g 32 0 pb depth q x) /\
tfv_frame m' spv s8v s7v s6v s5v s4v s3v s2v s1v s0v rav /\
stk asegs m' lo spv /\
heap_pres A4H (LB0 ++ LM ++ fr_ivs A4L FRS) spv me m' /\
rw_cells asegs m' A_ERRNO [C4 errv] /\
agree_on asegs P mpre m' /\
bB B - 512 * (Z.of_nat (length (lvl_blocks l)) + 1) <= bB B' /\ bD B <= bD B'.

Lemma tf_bodyB :
forall (spv r : Z) (i : nat) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s2 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m me : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (REST LB0 P LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word)
(q pb depth : Z) (x : tscal) (levels : list tlevel) (l : tlevel) (s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word),
alloc_ceiling <= lo -> lo <= spv - 64 - put_stk_A -> spv mod 16 = 0 -> spv <= hiA_top A4L HIx -> 0 <= spv < 2^64 ->
nth_error levels i = Some l -> (i < 32)%nat -> length levels = 32%nat ->
HEAPAx A (lvl_blocks l ++ REST) LM FRS B m md ->
REST = P ++ (r, 72) :: (q, 1024) :: LB0 ->
lvl_ok asegs A4F m l ->
tstack asegs m q levels ->
rw_cells asegs m r (tok_cells_g 32 0 pb depth q x) ->
tfv_frame m spv s8v s7v s6v s5v s4v s3v s2v s1v s0v rav ->
stk asegs m lo spv ->
heap_pres A4H (LB0 ++ LM ++ fr_ivs A4L FRS) spv me m ->
rw_cells asegs m A_ERRNO [C4 errv] ->
512 * (Z.of_nat (length (lvl_blocks l)) + 1) <= bB B ->
(forall ms' md' A', tf_body_postB spv r gp s1 s2 s4 s5 s6 s7 s9 s10 s11 F fc md REST LB0 P LM FRS B me m lo errv q pb depth x levels i l s8v s7v s6v s5v s4v s3v s2v s1v s0v rav ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md (MS (mkR x1 (Z_to_bv 64 spv) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 r) s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 (Z.of_nat i)) s4 s5 s6 s7 (Z_to_bv 64 (-1)) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 tokfree_loop_B_pc) fc None m (seg_rom asegs)).
Proof.
intros until rav. intros LO LOS SPA HT SPR Hl Hi LEN HP EREST LOK TS BLK FR ST HPR ERR BB K.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [] m) as MU.
destruct LOK as [JO NM].
unfold tokfree_loop_B_pc. unfold_consts. unfold put_stk_A in LOS.
reenterA asegs A4L HIx asegs_wx HP.
step. step. step.
evt_done5.
eapply (tok_reset_level_B_cps HIx PUT) with (i := i) (l := l) (levels := levels) (P := P) (LB0 := LB0) (LM := LM) (REST := REST)
(FRS := FRS) (B := B) (lo := lo) (errv := errv) (q := q) (r := r) (pb := pb) (depth := depth) (mxd := 32) (fl := 0)
(x := x) (rc := 1) (me := m);
[ exact Hl | lia | lia | exact LEN | exact HP | exact EREST
| unfold put_pre; destruct (tl_cs l) as [s'|]; [destruct JO as [Hp J]; split; [exact Hp | split; [lia | exact J]] | exact JO]
| exact NM | exact TS | exact BLK
| rewrite unsigned_lit by lia; exact ST | unfold_consts_goal; lia | rewrite unsigned_lit by lia; unfold put_stk_A; clear - LOS; lia
| rewrite unsigned_lit by lia; exact SPA | rewrite unsigned_lit by lia; exact HT
| apply heap_pres_refl | exact ERR
| unfold put_costA; destruct (tl_cs l); [rewrite Z.eqb_refl; unfold lvl_blocks in BB; rewrite length_app, Nat2Z.inj_add in BB; lia | lia]
| rewrite unsigned_lit by lia; reflexivity | ].
intros ms2 md2 A2 (m2 & B2 & rv & RS2 & VM2 & OUT2 & TS2 & TOK2 & ST2 & HPR2 & ERR2 & AG2 & BB2 & BD2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR2 by lia.
lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end.
apply K. unfold tf_body_postB, tokfree_ret_B_pc.
exists m2, B2, F2, fc2. do 16 eexists.
split; [reflexivity|]. split; [exact FS2|]. split; [exact FRM2|]. split; [exact VM2|].
split.
{ destruct OUT2 as [(_ & H) | (s' & _ & Hrc & _)]; [exact H | exfalso; lia]. }
split; [exact TS2|]. split; [exact TOK2|].
split; [unfold tfv_frame in *; apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [exact FR | left; cbn; lia] |].
split; [exact ST2|]. split; [eapply heap_pres_trans; [exact HPR | exact HPR2]|]. split; [exact ERR2|]. split; [exact AG2|].
unfold put_costA in BB2. destruct (tl_cs l); [rewrite Z.eqb_refl in BB2; unfold lvl_blocks; rewrite length_app, Nat2Z.inj_add; lia | unfold lvl_blocks in *; cbn [length] in *; lia].
Qed.

Definition tf_loop_postB (spv r : Z) (gp s1 s2 s4 s5 s6 s7 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(md : config) (BASE LB0 PBS LM : list blk) (FRS : list frame) (B : bud) (me mpre : word -> option byte) (lo : Z) (errv : word)
(q pb depth : Z) (x : tscal) (levels : list tlevel) (i : nat) (s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (B' : bud) F' fc' levels' x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s3',
ms' = MS (mkR x1 (Z_to_bv 64 spv) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 r) s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 s3' s4 s5 s6 s7 (Z_to_bv 64 (-1)) s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 tokfree_exit_B_pc) fc' None m' (seg_rom asegs) /\
fsaved F F' /\ (frm0 fc -> frm0 fc') /\
model_vm_only (cfg_model md) (cfg_model md') /\
HEAPAx A' BASE LM FRS B' m' md' /\
length levels' = 32%nat /\
(forall j, (j <= i)%nat -> nth_error levels' j = Some lvl_reset) /\
(forall j, (i < j)%nat -> nth_error levels' j = nth_error levels j) /\
tstack asegs m' q levels' /\
rw_cells asegs m' r (tok_cells_g 32 0 pb depth q x) /\
tfv_frame m' spv s8v s7v s6v s5v s4v s3v s2v s1v s0v rav /\
stk asegs m' lo spv /\
heap_pres A4H (LB0 ++ LM ++ fr_ivs A4L FRS) spv me m' /\
rw_cells asegs m' A_ERRNO [C4 errv] /\
agree_on asegs PBS mpre m' /\
bB B - 512 * (Z.of_nat (length (lvblocks levels (S i))) + Z.of_nat (S i)) <= bB B' /\ bD B <= bD B'.

Lemma tf_loopB :
forall (i : nat) (spv r : Z) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s2 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m me : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (PBS LB0 LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word)
(q pb depth : Z) (x : tscal) (levels : list tlevel) (s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word),
alloc_ceiling <= lo -> lo <= spv - 64 - put_stk_A -> spv mod 16 = 0 -> spv <= hiA_top A4L HIx -> 0 <= spv < 2^64 ->
(i < 32)%nat -> length levels = 32%nat ->
HEAPAx A (lvblocks levels (S i) ++ PBS ++ (r, 72) :: (q, 1024) :: LB0) LM FRS B m md ->
(forall j l, nth_error levels j = Some l -> (j <= i)%nat -> lvl_ok asegs A4F m l) ->
tstack asegs m q levels ->
rw_cells asegs m r (tok_cells_g 32 0 pb depth q x) ->
tfv_frame m spv s8v s7v s6v s5v s4v s3v s2v s1v s0v rav ->
stk asegs m lo spv ->
heap_pres A4H (LB0 ++ LM ++ fr_ivs A4L FRS) spv me m ->
rw_cells asegs m A_ERRNO [C4 errv] ->
512 * (Z.of_nat (length (lvblocks levels (S i))) + Z.of_nat (S i)) <= bB B ->
(forall ms' md' A', tf_loop_postB spv r gp s1 s2 s4 s5 s6 s7 s9 s10 s11 F fc md (PBS ++ (r, 72) :: (q, 1024) :: LB0) LB0 PBS LM FRS B me m lo errv q pb depth x levels i s8v s7v s6v s5v s4v s3v s2v s1v s0v rav ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md (MS (mkR x1 (Z_to_bv 64 spv) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 r) s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 (Z.of_nat i)) s4 s5 s6 s7 (Z_to_bv 64 (-1)) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 tokfree_loop_B_pc) fc None m (seg_rom asegs)).
Proof.
induction i as [|i IH]; intros until rav; intros LO LOS SPA HT SPR Hi LEN HP LOK TS BLK FR ST HPR ERR BB K.
-
destruct (nth_error levels 0) as [l|] eqn:Hl; [| apply nth_error_None in Hl; lia].
rewrite (lvblocks_S _ _ _ Hl) in HP, BB. rewrite <- app_assoc in HP. rewrite lvblocks_0, app_nil_r in BB.
eapply (tf_bodyB spv r 0) with (P := PBS); [exact LO | exact LOS | exact SPA | exact HT | exact SPR | exact Hl | lia | exact LEN | exact HP | rewrite lvblocks_0; reflexivity
| eapply LOK; [exact Hl | lia] | exact TS | exact BLK | exact FR | exact ST | exact HPR | exact ERR | cbn [Z.of_nat length] in BB |- *; lia |].
intros ms1 md1 A1 (m1 & B1 & F1 & fc1 & y1 & u0 & u1 & u2 & w0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & -> & FS1 & FRM1 & VM1 & HP1 & TS1 & BLK1 & FR1 & ST1 & HPR1 & ERR1 & AG1 & BB1 & BD1).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI1.
pose proof (wmono_refl asegs m1) as WM. pose proof (munch_refl [] m1) as MU.
unfold tokfree_ret_B_pc. unfold_consts. reenterA asegs A4L HIx asegs_wx HP1.
step.
step. if_false.
evt_done5. apply K. unfold tf_loop_postB, tokfree_exit_B_pc.
exists m1, B1, F1, fc1, (lupd levels 0 lvl_reset). do 17 eexists.
split; [reflexivity|]. split; [exact FS1|]. split; [exact FRM1|]. split; [exact VM1|].
split; [rewrite lvblocks_0 in HP1; heap_nowA A4L HIx HP1 MU WM MI1|].
split; [rewrite lupd_length; exact LEN|].
split; [intros j Hj; replace j with 0%nat by lia; apply nth_error_lupd_eq; lia|].
split; [intros j Hj; apply nth_error_lupd_neq; lia|].
split; [exact TS1|]. split; [exact BLK1|]. split; [exact FR1|]. split; [exact ST1|]. split; [exact HPR1 |]. split; [exact ERR1|]. split; [exact AG1|].
rewrite (lvblocks_S _ _ _ Hl), lvblocks_0, app_nil_r. change (Z.of_nat 1) with 1. lia.
-
destruct (nth_error levels (S i)) as [l|] eqn:Hl; [| apply nth_error_None in Hl; lia].
rewrite (lvblocks_S _ _ _ Hl) in HP, BB. rewrite <- app_assoc in HP. rewrite length_app, Nat2Z.inj_add in BB.
eapply (tf_bodyB spv r (S i)) with (P := lvblocks levels (S i) ++ PBS); [exact LO | exact LOS | exact SPA | exact HT | exact SPR | exact Hl | lia | exact LEN | exact HP | rewrite <- app_assoc; reflexivity
| eapply LOK; [exact Hl | lia] | exact TS | exact BLK | exact FR | exact ST | exact HPR | exact ERR | lia |].
intros ms1 md1 A1 (m1 & B1 & F1 & fc1 & y1 & u0 & u1 & u2 & w0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & -> & FS1 & FRM1 & VM1 & HP1 & TS1 & BLK1 & FR1 & ST1 & HPR1 & ERR1 & AG1 & BB1 & BD1).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI1.
pose proof (wmono_refl asegs m1) as WM. pose proof (munch_refl [] m1) as MU.
unfold tokfree_ret_B_pc. unfold_consts. reenterA asegs A4L HIx asegs_wx HP1.
step.
norm_w32.
step. if_truex.
replace (Z.of_nat (S i) + -1) with (Z.of_nat i) by lia.
evt_done5.
eapply (IH spv r _ gp _ _ _ _ _ _ _ _ _ _ _ s1 s2 s4 s5 s6 s7 s9 s10 s11 _ _ _ _ F1 fc1 m1 me md1 T A1 PBS LB0 LM FRS B1 lo errv q pb depth x (lupd levels (S i) lvl_reset) s8v s7v s6v s5v s4v s3v s2v s1v s0v rav);
[exact LO | exact LOS | exact SPA | exact HT | exact SPR | lia | rewrite lupd_length; exact LEN | rewrite lvblocks_lupd_ge by lia; heap_nowA A4L HIx HP1 MU WM MI1 | | exact TS1 | exact BLK1 | exact FR1 | exact ST1 | exact HPR1 | exact ERR1 | rewrite lvblocks_lupd_ge by lia; lia |].
+ intros j l' Hj Hji. rewrite nth_error_lupd_neq in Hj by lia.
eapply lvl_ok_agree; [eapply LOK; [exact Hj | lia] | exact AG1 | apply incl_appl; eapply incl_tran; [| eapply lvblocks_incl; [exact Hj | lia]]; unfold lvl_blocks; apply incl_appl; apply incl_refl].
+ intros ms2 md2 A2 (m2 & B2 & F2 & fc2 & levels2 & y1' & u0' & u1' & u2' & w0' & v1' & v2' & v3' & v4' & v5' & v6' & v7' & u3' & u4' & u5' & u6' & s3' & -> & FS2 & FRM2 & VM2 & HP2 & LEN2 & RES2 & SAME2 & TS2 & BLK2 & FR2 & ST2 & HPR2 & ERR2 & AG2 & BB2 & BD2).
apply K. unfold tf_loop_postB.
exists m2, B2, F2, fc2, levels2. do 17 eexists.
split; [reflexivity|]. split; [eapply fsaved_trans; [exact FS1 | exact FS2]|]. split; [intros Hf; apply FRM2, FRM1, Hf|].
split; [eapply model_vm_only_trans; [exact VM1 | exact VM2]|].
split; [exact HP2|]. split; [exact LEN2|].
split. { intros j Hj. destruct (PeanoNat.Nat.eq_dec j (S i)) as [->|NE]; [| apply RES2; lia]. rewrite SAME2 by lia. apply nth_error_lupd_eq. lia. }
split. { intros j Hj. rewrite SAME2 by lia. apply nth_error_lupd_neq. lia. }
split; [exact TS2|]. split; [exact BLK2|]. split; [exact FR2|]. split; [exact ST2|]. split; [exact HPR2 |]. split; [exact ERR2|].
split; [eapply agree_on_trans; [eapply agree_on_incl; [exact AG1 | apply incl_appr; apply incl_refl] | exact AG2] |].
rewrite (lvblocks_S _ _ _ Hl), length_app. rewrite lvblocks_lupd_ge in BB2 by lia. rewrite ?Nat2Z.inj_add, ?Nat2Z.inj_succ in *. lia.
Qed.
End TokFree1B.
End RC__1.
