(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Q5Rg Lib.GwApply QRjH QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw QnCn Q7UD Qhd4 Qwm6 QlKV QsKa Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.
Import QnCn.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq7 QsKa.Mq3.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Definition array_list_length_A_entry : Z := 0xa09dc.
Definition array_list_get_idx_A_entry : Z := 0xa05c8.

Lemma shadow_bytes_length8 : forall k, 0 <= k -> length (shadow_bytes (8 * k)) = Z.to_nat k.
Proof.
intros k Hk. unfold shadow_bytes. rewrite (Z.mul_comm 8 k), Z.div_mul, Z.mod_mul by lia.
cbn [Z.eqb]. rewrite app_nil_r, repeat_length. reflexivity.
Qed.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section Regs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).

Definition al_blkA (a arr size : Z) : Prop :=
0 < a /\ a mod 8 = 0 /\ a + AL_SZ <= alloc_ceiling /\ 0 < arr /\ arr mod 8 = 0 /\ arr + 8 * size <= alloc_ceiling.

Definition array_list_length_A_post (a3 a4 : word) (ps : list Z) (m : word -> option byte) (lo : Z) : machine_state -> Prop :=
fun ms' => exists (a1 a2 : word) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length ps))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma array_list_length_A : forall (a0 a1 a2 a3 a4 : word) (m : word -> option byte) (lo sbcell a arr size : Z) (ps : list Z),
small_pre sp m lo sbcell ->
alist asegs A4F m [(a, AL_SZ); (arr, 8 * size)] a ps ->
a0 = Z_to_bv 64 a ->
al_blkA a arr size ->
ro_cells asegs m (a / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
evt asegs (array_list_length_A_post a3 a4 ps m lo)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 array_list_length_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until ps. intros (MI & ST & LOS & LO & GOT & CELL & Hc0 & Hc8) AL A0 (Ha0 & Ha8 & Hah & Hr0 & Hr8 & Hrh) SHa.
destruct (alist_openx asegs A4F m a arr size ps AL) as (junk & HDR & ARR & JK & Hlen & Hsz). unfold al_hdr in HDR.
unfold array_list_length_A_entry, array_list_length_A_post, A_GOT_SB, A_SB in *.
unfold alloc_ceiling, sp_window_lo, stack_max_size in LO, Hc8, Hah, Hrh. word_range sp SPR. subst a0.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
clear ARR JK.
carve_frame 16%nat ST.
step. step.
step. step. step.
step.
asan_chkA.
step.
step. step. step.
apply evt_done. eexists _, _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
release_frame FR ST (bv_unsigned sp). exact ST.
Qed.

Definition array_list_get_idx_A_post (ps : list Z) (i : Z) (m : word -> option byte) (lo : Z) : machine_state -> Prop :=
fun ms' => exists (a1 a2 a3 a4 : word) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if i <? Z.of_nat (length ps) then al_nth ps i else 0)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma array_list_get_idx_A : forall (a0 a1 a2 a3 a4 : word) (m : word -> option byte) (lo sbcell a arr size : Z) (ps : list Z) (i : Z),
small_pre sp m lo sbcell ->
alist asegs A4F m [(a, AL_SZ); (arr, 8 * size)] a ps ->
a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 i -> 0 <= i < 2^64 ->
al_blkA a arr size ->
ro_cells asegs m (a / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
bytes_at asegs m (arr / 8 + A_SB) (shadow_bytes (8 * size)) ->
evt asegs (array_list_get_idx_A_post ps i m lo)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 array_list_get_idx_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until i. intros (MI & ST & LOS & LO & GOT & CELL & Hc0 & Hc8) AL A0 A1 Hi (Ha0 & Ha8 & Hah & Hr0 & Hr8 & Hrh) SHa SHr.
destruct (alist_openx asegs A4F m a arr size ps AL) as (junk & HDR & ARR & JK & Hlen & Hsz). unfold al_hdr in HDR.
pose proof (u64arr_bound asegs m arr (wl ps) ARR) as AB. rewrite wl_length in AB.
unfold array_list_get_idx_A_entry, array_list_get_idx_A_post, A_GOT_SB, A_SB in *.
unfold alloc_ceiling, sp_window_lo, stack_max_size in LO, Hc8, Hah, Hrh. word_range sp SPR. subst a0 a1.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
clear JK.
apply slots_of_u64arr in ARR. stash SHr. stash ARR.
carve_frame 16%nat ST.
step. step.
step. step. step.
step.
asan_chkA.
step.
step.
destruct (Z.ltb_spec i (Z.of_nat (length ps))) as [LT|GE].
- if_falsex.
asan_chk0.
step.
step. step.
rewrite (unsigned_lit i) by lia. rewrite (Z.shiftl_mul_pow2 i 3) by lia. change (2^3) with 8.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (HR : ov_read_bytes asegs mc (Z_to_bv 64 (arr / 8 + 2147450880 + i)) 1 = Some [Z_to_bv 8 0])
by (unstash SHr; apply ov_read1_of_ro; eapply (ro_cells_transport asegs _ m mc); [| exact MU | cbn; lia];
apply (shadow_granule0 asegs m (arr / 8 + 2147450880) (8 * size) i); [lia | lia | exact SHr])
end.
step. step. sh_norm.
replace ((arr + i * 8) / 8 + 2147450880) with (arr / 8 + 2147450880 + i) by (Z.div_mod_to_equations; lia).
step. rewrite ?zxb_zero. clear HR.
step. if_false.
unstash ARR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (rw_cells_transport asegs _ m mc) in ARR; [| exact MU | exact WM | cbn [disjoint_from]; rewrite slots_size; lia];
pose proof (al_slot_read asegs mc arr ps i (wa (arr + i * 8)) ltac:(apply u64arr_of_slots; exact ARR) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD
end.
step. step.
step. step. step.
apply evt_done. eexists _, _, _, _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
release_frame FR ST (bv_unsigned sp). exact ST.
- if_truex.
step.
step. step. step.
apply evt_done. eexists _, _, _, _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
release_frame FR ST (bv_unsigned sp). exact ST.
Qed.
End Regs.
End RC__1.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn.
Import QSL3.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QsKa.Mq5.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Definition lh_char_hash_A_entry : Z := 0xa0bb8.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section S.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Variable MREL : config -> config -> Prop.

Definition lh_hash_A_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (h : Z) (errv' : word),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 h) m' ms' /\ 0 <= h < 2^64 /\
MREL md md' /\ stk asegs m' lo (bv_unsigned sp) /\ heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\ lh_globA m' /\ HEAPAx A' LB LM FRS B m' md'.

Definition lh_char_hash_A_stmt (HD : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word) (kp kn : Z) (ks : list byte),
HEAPAx A LB LM FRS B m md -> In (kp, kn) LB -> cstr asegs m kp kn ks -> lh_globA m ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - HD ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 -> frm0 fc ->
Z.of_nat (length FRS) < 4096 ->
a0 = Z_to_bv 64 kp ->
(forall ms' md' A', lh_hash_A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 lh_char_hash_A_entry) fc None m (seg_rom asegs)).
End S.
End RC__1.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache Q8tj QgoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw Q8tj.
Import QgoP.
Import Q7UD Qhd4 Qwm6.
Import QsKa.Mq0.
Import Qwm6.Mq0 QlKV.Mqa QlKV.Mq1 QsKa.Mq3.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Definition lh_table_length_A_entry : Z := 0xa2d54.
Definition lh_char_equal_A_entry : Z := 0xa1d2c.

Lemma icmp_walk_cstr_zero : forall ls rs fuel k v,
~ In b0 ls -> ~ In b0 rs -> (length ls < fuel)%nat ->
icmp_walk cmp_stop cmp_sign (ls ++ [b0]) (rs ++ [b0]) fuel = Some (k, v) -> (v = 0 <-> ls = rs).
Proof.
induction ls as [|a ls IH]; intros rs fuel k v NL NR Hf H.
- destruct fuel as [|fuel]; [cbn in Hf; lia|]. cbn [app] in H. cbn [icmp_walk] in H.
destruct rs as [|b rs]; cbn [app] in H.
+ unfold cmp_stop in H at 1. change (bv_unsigned b0) with 0 in H. cbn [Z.eqb negb orb] in H. injection H as _ <-. unfold cmp_sign. change (bv_unsigned b0) with 0. cbn. split; [reflexivity | intros _; reflexivity].
+ assert (Hb : bv_unsigned b <> 0) by (apply (notin0_nth (b :: rs) 0 b NR); reflexivity).
unfold cmp_stop in H at 1. change (bv_unsigned b0) with 0 in H.
replace (0 =? bv_unsigned b) with false in H by (symmetry; apply Z.eqb_neq; lia). cbn [negb orb] in H.
injection H as _ <-. unfold cmp_sign. change (bv_unsigned b0) with 0. pose proof (byte_range8 b).
split; [intros Hs; exfalso; lia | intros E; discriminate].
- destruct fuel as [|fuel]; [cbn in Hf; lia|]. cbn [app] in H. cbn [icmp_walk] in H.
assert (Ha : bv_unsigned a <> 0) by (apply (notin0_nth (a :: ls) 0 a NL); reflexivity).
pose proof (byte_range8 a) as Ra.
destruct rs as [|b rs]; cbn [app] in H.
+ unfold cmp_stop in H at 1. change (bv_unsigned b0) with 0 in H.
replace (bv_unsigned a =? 0) with false in H by (symmetry; apply Z.eqb_neq; lia). cbn [negb orb] in H.
injection H as _ <-. unfold cmp_sign. change (bv_unsigned b0) with 0.
split; [intros Hs; exfalso; lia | intros E; discriminate].
+ pose proof (byte_range8 b) as Rb.
unfold cmp_stop in H at 1.
destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [Eab | Nab].
* assert (a = b) by (apply bv_eq; exact Eab). subst b.
replace (bv_unsigned a =? 0) with false in H by (symmetry; apply Z.eqb_neq; lia). cbn [negb orb] in H.
destruct (icmp_walk cmp_stop cmp_sign (ls ++ [b0]) (rs ++ [b0]) fuel) as [[j w]|] eqn:E; [|discriminate].
injection H as _ <-.
rewrite (IH rs fuel j w ltac:(intros K; apply NL; right; exact K) ltac:(intros K; apply NR; right; exact K) ltac:(cbn in Hf; lia) E).
split; [intros ->; reflexivity | intros E2; injection E2; auto].
* cbn [negb orb] in H. injection H as _ <-. unfold cmp_sign.
split; [intros Hs; exfalso; lia | intros E2; injection E2 as -> ->; lia].
Qed.

Lemma istrcmp_model_zero : forall ls rs k v, ~ In b0 ls -> ~ In b0 rs ->
istrcmp_model ls rs = Some (k, v) -> (v = 0 <-> ls = rs).
Proof. intros ls rs k v NL NR H. eapply icmp_walk_cstr_zero; [exact NL | exact NR | | exact H]. lia. Qed.

Lemma cmp_stop_nul : forall a, cmp_stop a b0 = true.
Proof. intros a. unfold cmp_stop. change (bv_unsigned b0) with 0. destruct (bv_unsigned a =? 0); reflexivity. Qed.

Lemma icmp_walk_cstr_total : forall ls rs fuel, (length ls < fuel)%nat ->
exists k v, icmp_walk cmp_stop cmp_sign (ls ++ [b0]) (rs ++ [b0]) fuel = Some (k, v).
Proof.
induction ls as [|a ls IH]; intros rs fuel Hf.
- destruct fuel as [|fuel]; [cbn in Hf; lia|]. cbn [app icmp_walk].
destruct rs as [|b rs]; cbn [app]; unfold cmp_stop at 1; change (bv_unsigned b0) with 0; rewrite Z.eqb_refl, orb_true_r; eauto.
- destruct fuel as [|fuel]; [cbn in Hf; lia|]. cbn [app icmp_walk].
destruct rs as [|b rs]; cbn [app].
+ rewrite cmp_stop_nul. eauto.
+ destruct (cmp_stop a b); [eauto|].
destruct (IH rs fuel ltac:(cbn in Hf; lia)) as (k & v & E). rewrite E. eauto.
Qed.

Lemma istrcmp_model_total : forall ls rs, exists k v, istrcmp_model ls rs = Some (k, v).
Proof. intros. apply icmp_walk_cstr_total. lia. Qed.

Lemma seqz_of_model : forall v, -255 <= v <= 255 -> v_sltiu (Z_to_bv 64 v) 1 = Z_to_bv 64 (if v =? 0 then 1 else 0).
Proof.
intros v Hv. unfold v_sltiu. change (bv_wrap 64 1) with 1. rewrite Z_to_bv_unsigned.
change (bv_modulus 64) with 18446744073709551616.
destruct (Z.eqb_spec v 0) as [->|NE].
- reflexivity.
- destruct (Z.ltb_spec (bv_wrap 64 v) 1) as [LT|GE]; [|reflexivity].
exfalso. unfold bv_wrap, bv_modulus in LT. change (2 ^ Z.of_N 64) with 18446744073709551616 in LT.
destruct (Z.lt_ge_cases v 0).
+ rewrite <- (Z.mod_add v 1) in LT by lia. rewrite Z.mod_small in LT by lia. lia.
+ rewrite Z.mod_small in LT by lia. lia.
Qed.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section Regs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).

Lemma lh_table_length_A : forall m lo sbcell (BS : list blk) (t : Z) (kvs : list (Z * Z)),
small_pre sp m lo sbcell ->
lhtab2 asegs A4F m BS t kvs -> 0 < t -> t + 56 <= alloc_ceiling -> t mod 8 = 0 ->
ro_cells asegs m (t / 8 + A_SB) [C1 (Z_to_bv 8 0)] -> t / 8 + A_SB + 1 <= alloc_ceiling ->
evt asegs (small_post ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo (Z_to_bv 64 (Z.of_nat (length kvs))))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 t) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 lh_table_length_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until kvs. intros (MI & ST & LOS & LO & GOT & CELL & Hc0 & Hc8) LH Ht Hth Hal SH0 HSH.
destruct LH as (tbl & size & es & svs & -> & _ & HDR & _ & _ & _ & Hsz & Hcnt & _).
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
unfold lh_hdr, lh_hdrf in HDR.
unfold lh_table_length_A_entry, A_GOT_SB, A_SB in *.
unfold alloc_ceiling, sp_window_lo, stack_max_size in LO, Hth, Hc8, HSH. word_range sp SPR.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
rewrite length_map.
carve_frame 16%nat ST.
step. step.
step. step. step. step.
asan_chk0_off t 4.
step. norm_sx32.
step. step. step.
apply evt_done. eexists. split; [eexists _, _, _; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
release_frame FR ST (bv_unsigned sp). exact ST.
Qed.
End Regs.

Section CharEqual.
Hypothesis OBL_ISTRCMP : istrcmp_spec_U.

Lemma lh_char_equal_A :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a b lo : Z) (ls rs : list byte) (k : nat) (v : Z)
(Q : machine_state -> Prop),
istrcmp_model ls rs = Some (k, v) ->
unpoisoned asegs m A_SB a (Z.of_nat k) -> unpoisoned asegs m A_SB b (Z.of_nat k) -> asan_rt_ok m ->
0 <= a -> a + Z.of_nat (length ls) + 1 <= 2^47 -> Z.of_nat (length ls) + 1 < 2^40 -> 0 <= b -> b + Z.of_nat (length rs) + 1 <= 2^47 ->
(64 < Z.of_nat k -> app_mem a (Z.of_nat k) /\ app_mem b (Z.of_nat k)) ->
(a + Z.of_nat (length ls) + 1 <= lo \/ bv_unsigned sp <= a) -> (b + Z.of_nat (length rs) + 1 <= lo \/ bv_unsigned sp <= b) ->
a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 b -> ~ In b0 ls -> ~ In b0 rs ->
bytes_at asegs m a (ls ++ [b0]) -> bytes_at asegs m b (rs ++ [b0]) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 - 4096 -> bv_unsigned sp mod 16 = 0 ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
munch [(lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
bytes_at asegs m' a (ls ++ [b0]) -> bytes_at asegs m' b (rs ++ [b0]) ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (if strcmp_model ls rs =? 0 then 1 else 0)) a1' a2' a3' a4' a5' a6' a7'
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 lh_char_equal_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until Q. intros MODEL UPa UPb RT Ha Han Hl40 Hb Hbn APP SEPa SEPb Ha0 Ha1 NL NR STRa STRb ST LO LOS SPA MI RA K.
subst a0 a1. word_range sp SPR. pose proof alloc_ceiling_ge as ACG.
pose proof (bytes_at_bound _ _ _ _ STRa) as BDa. rewrite length_app in BDa. cbn [length] in BDa.
pose proof (bytes_at_bound _ _ _ _ STRb) as BDb. rewrite length_app in BDb. cbn [length] in BDb.

assert (RES : (if v =? 0 then 1 else 0) = (if strcmp_model ls rs =? 0 then 1 else 0)).
{ pose proof (istrcmp_model_zero ls rs k v NL NR MODEL) as Z1. pose proof (strcmp_model_zero ls rs NL NR) as Z2.
destruct (Z.eqb_spec v 0) as [Hv | Hv]; destruct (Z.eqb_spec (strcmp_model ls rs) 0) as [Hm | Hm]; try reflexivity; exfalso; tauto. }
pose proof (icmp_walk_nread _ _ _ _ _ _ _ MODEL) as (Kf & Kl & Kr). rewrite length_app in Kl, Kr. cbn [length] in Kl, Kr.
pose proof (icmp_walk_pos _ _ _ _ _ _ _ MODEL ltac:(lia)) as K1.
unfold lh_char_equal_A_entry.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
stash STRa. stash STRb.
carve_frame 16%nat ST.
step. stepz.
step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RT1 : asan_rt_ok mc) by (eapply (asan_rt_ok_transport [(lo, bv_unsigned sp)] m mc); [exact RT | exact MU
| intros c Hc; pose proof (a4_rt_cells_in_img c Hc); cbn [disjoint_from]; split; [left; lia | exact I]]);
assert (UPa1 : unpoisoned asegs mc A_SB a (Z.of_nat k))
by (eapply unpoisoned_transport; [exact UPa | exact MU | intros u w Hu Hw; eapply (shadow_outside_stack A_SB a (Z.of_nat k)); try eassumption; unfold A_SB; lia]);
assert (UPb1 : unpoisoned asegs mc A_SB b (Z.of_nat k))
by (eapply unpoisoned_transport; [exact UPb | exact MU | intros u w Hu Hw; eapply (shadow_outside_stack A_SB b (Z.of_nat k)); try eassumption; unfold A_SB; lia]);
assert (STRa1 : bytes_at asegs mc a (ls ++ [b0]))
by (pose proof STRa as S0; unstash S0; eapply bytes_at_transport; [exact S0 | exact MU | cbn [disjoint_from]; rewrite length_app; cbn [length]; lia]);
assert (STRb1 : bytes_at asegs mc b (rs ++ [b0]))
by (pose proof STRb as S0; unstash S0; eapply bytes_at_transport; [exact S0 | exact MU | cbn [disjoint_from]; rewrite length_app; cbn [length]; lia])
end.
clear UPa UPb RT.
eapply (OBL_ISTRCMP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a b lo ls rs k v);
[ exact MODEL | exact UPa1 | exact UPb1 | exact RT1 | lia | lia | lia | lia | lia | exact APP
| rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | reflexivity | reflexivity | exact NL | exact NR
| exact STRa1 | exact STRb1 | rewrite unsigned_lit by lia; exact ST | exact LO | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia | assumption | rewrite unsigned_lit by lia; reflexivity |].
rewrite ?unsigned_lit by lia.
clear UPa1 UPb1 RT1 STRa1 STRb1.
intros x0 x1 x2 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 m2 MU2 WM2 MI2 STRa2 STRb2 ST2.
stash STRa2. stash STRb2.
lazymatch type of MU2 with munch _ ?mc _ =>
transport_after_call asegs mc m2 MU2 WM2; try match goal with H : mem_inv asegs mc |- _ => clear H end end.
clear MU2 WM2.
replace (ret_pc (Z_to_bv 64 0xa1d38)) with (Z_to_bv 64 0xa1d38) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
pose proof (icmp_walk_last _ _ _ _ _ _ _ MODEL ltac:(eapply icmp_walk_pos; [exact MODEL | lia])) as (ca & cb & _ & _ & Hlast).
assert (Rv : -1 <= v <= 1).
{ destruct Hlast as [[_ ->] | (_ & _ & ->)]; [| lia]. unfold cmp_sign. pose proof (byte_range8 ca). pose proof (byte_range8 cb). lia. }
step.
rewrite (seqz_of_model v) by lia. rewrite RES.
step. step. step.
unstash STRa2. unstash STRb2.
eapply K; [exact MU | exact WM | exact MI2 | exact STRa2 | exact STRb2 |].
release_frame FR ST2 (bv_unsigned sp). exact ST2.
Qed.
End CharEqual.
End RC__1.
End Mq2.
From Stdlib Require Permutation.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn Q8tj.
Import QSL3.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QsKa.Mq5.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Lemma bytes_at_repeat_sub : forall segs m a v n k j,
bytes_at segs m a (repeat v n) -> (k + j <= n)%nat -> bytes_at segs m (a + Z.of_nat k) (repeat v j).
Proof.
intros segs m a v n k j H Hk.
replace n with (k + (j + (n - k - j)))%nat in H by lia. rewrite 2!repeat_app in H.
apply bytes_at_app in H as [_ H]. rewrite repeat_length in H. apply bytes_at_app in H as [H _]. exact H.
Qed.

Lemma ro_cells_of_repeat : forall segs m a v j,
bytes_at segs m a (repeat v j) -> ro_cells segs m a (map C1 (repeat v j)).
Proof. intros segs m a v j H. split; [apply cells_wf_map_C1 | rewrite cells_bytes_map_C1; exact H]. Qed.

Lemma shadow_bytes_mul8 : forall n, 0 <= n -> shadow_bytes (8 * n) = repeat (Z_to_bv 8 0) (Z.to_nat n).
Proof.
intros n Hn. unfold shadow_bytes.
replace (8 * n / 8) with n by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
replace ((8 * n) mod 8) with 0 by (rewrite Z.mul_comm, Z.mod_mul by lia; reflexivity).
cbn [Z.eqb]. rewrite app_nil_r. reflexivity.
Qed.

Lemma ent_addr_div8 : forall tbl i, tbl mod 8 = 0 -> ent_addr tbl i / 8 = tbl / 8 + 5 * Z.of_nat i.
Proof. intros tbl i H. unfold ent_addr. Z.div_mod_to_equations. nia. Qed.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section WithHI.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Lemma tbl_shadowA : forall A LB LM FR B m md tbl size,
HEAPAx A LB LM FR B m md -> In (tbl, 40 * size) LB -> 0 <= size ->
bytes_at asegs m (tbl / 8 + A_SB) (repeat (Z_to_bv 8 0) (Z.to_nat (5 * size))).
Proof.
intros A LB LM FR B m md tbl size HP Hin Hsz.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ _ _ HP Hin) as SH. unfold shad in SH. cbn [hl_sb hl_segs hla_base A4L A4H] in SH.
replace (40 * size) with (8 * (5 * size)) in SH by lia. rewrite shadow_bytes_mul8 in SH by lia. exact SH.
Qed.

Lemma ent_shadowA : forall A LB LM FR B m md tbl size i,
HEAPAx A LB LM FR B m md -> In (tbl, 40 * size) LB -> tbl mod 8 = 0 -> Z.of_nat i < size ->
ro_cells asegs m (ent_addr tbl i / 8 + A_SB)
[C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof.
intros A LB LM FR B m md tbl size i HP Hin Hal Hi.
pose proof (tbl_shadowA _ _ _ _ _ _ _ tbl size HP Hin ltac:(lia)) as SH.
apply (bytes_at_repeat_sub asegs m _ _ _ (5 * i) 5) in SH; [|lia].
rewrite ent_addr_div8 by exact Hal.
replace (tbl / 8 + 5 * Z.of_nat i + A_SB) with (tbl / 8 + A_SB + Z.of_nat (5 * i)) by lia.
exact (ro_cells_of_repeat asegs m _ _ 5 SH).
Qed.

Lemma ent_shadow_sepA : forall A LB LM FR B m md tbl size i g b k,
HEAPAx A LB LM FR B m md -> In (tbl, 40 * size) LB -> tbl mod 8 = 0 -> Z.of_nat i < size -> 0 <= g < 5 -> In (b, k) (LB ++ LM) ->
ent_addr tbl i / 8 + A_SB + g < alloc_ceiling
/\ (ent_addr tbl i / 8 + A_SB + g < b \/ b + k <= ent_addr tbl i / 8 + A_SB + g)
/\ (ent_addr tbl i / 8 + A_SB + g < 0x10000 \/ 0x645000 <= ent_addr tbl i / 8 + A_SB + g).
Proof.
intros A LB LM FR B m md tbl size i g b k HP Hin Hal Hi Hg Hb.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tbl (40 * size) (5 * Z.of_nat i + g) b k HP Hin ltac:(Z.div_mod_to_equations; nia) Hb) as X.
cbn [hl_sb hl_img_lo hl_img_hi hla_base A4L A4H] in X. rewrite ent_addr_div8 by exact Hal.
replace (tbl / 8 + 5 * Z.of_nat i + A_SB + g) with (tbl / 8 + A_SB + (5 * Z.of_nat i + g)) by lia. exact X.
Qed.
End WithHI.
End RC__1.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.
Import QnCn.Mq0.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqg QsKa.Mqc.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Definition array_list_length_A_entry : Z := 0xa29c4.
Definition array_list_get_idx_A_entry : Z := 0xa24e0.

Lemma shadow_bytes_length8 : forall k, 0 <= k -> length (shadow_bytes (8 * k)) = Z.to_nat k.
Proof.
intros k Hk. unfold shadow_bytes. rewrite (Z.mul_comm 8 k), Z.div_mul, Z.mod_mul by lia.
cbn [Z.eqb]. rewrite app_nil_r, repeat_length. reflexivity.
Qed.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section Regs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).

Definition al_blkA (a arr size : Z) : Prop :=
0 < a /\ a mod 8 = 0 /\ a + AL_SZ <= alloc_ceiling /\ 0 < arr /\ arr mod 8 = 0 /\ arr + 8 * size <= alloc_ceiling.

Definition array_list_length_A_post (a3 a4 : word) (ps : list Z) (m : word -> option byte) (lo : Z) : machine_state -> Prop :=
fun ms' => exists (a1 a2 : word) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length ps))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma array_list_length_A : forall (a0 a1 a2 a3 a4 : word) (m : word -> option byte) (lo sbcell a arr size : Z) (ps : list Z),
small_pre sp m lo sbcell ->
alist asegs A4F m [(a, AL_SZ); (arr, 8 * size)] a ps ->
a0 = Z_to_bv 64 a ->
al_blkA a arr size ->
ro_cells asegs m (a / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
evt asegs (array_list_length_A_post a3 a4 ps m lo)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 array_list_length_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until ps. intros (MI & ST & LOS & LO & GOT & CELL & Hc0 & Hc8) AL A0 (Ha0 & Ha8 & Hah & Hr0 & Hr8 & Hrh) SHa.
destruct (alist_openx asegs A4F m a arr size ps AL) as (junk & HDR & ARR & JK & Hlen & Hsz). unfold al_hdr in HDR.
unfold array_list_length_A_entry, array_list_length_A_post, A_GOT_SB, A_SB in *.
unfold alloc_ceiling, sp_window_lo, stack_max_size in LO, Hc8, Hah, Hrh. word_range sp SPR. subst a0.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
clear ARR JK.
carve_frame 16%nat ST.
bstep. bstep.
bstep. bstep. bstep.
bstep.
asan_chkA.
bstep.
bstep. bstep. bstep.
apply evt_done. eexists _, _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
release_frame FR ST (bv_unsigned sp). exact ST.
Qed.

Definition array_list_get_idx_A_post (ps : list Z) (i : Z) (m : word -> option byte) (lo : Z) : machine_state -> Prop :=
fun ms' => exists (a1 a2 a3 a4 a5' : word) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if i <? Z.of_nat (length ps) then al_nth ps i else 0)) a1 a2 a3 a4 a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma array_list_get_idx_A : forall (a0 a1 a2 a3 a4 : word) (m : word -> option byte) (lo sbcell a arr size : Z) (ps : list Z) (i : Z),
small_pre sp m lo sbcell ->
alist asegs A4F m [(a, AL_SZ); (arr, 8 * size)] a ps ->
a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 i -> 0 <= i < 2^64 ->
al_blkA a arr size ->
ro_cells asegs m (a / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
bytes_at asegs m (arr / 8 + A_SB) (shadow_bytes (8 * size)) ->
evt asegs (array_list_get_idx_A_post ps i m lo)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 array_list_get_idx_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until i. intros (MI & ST & LOS & LO & GOT & CELL & Hc0 & Hc8) AL A0 A1 Hi (Ha0 & Ha8 & Hah & Hr0 & Hr8 & Hrh) SHa SHr.
destruct (alist_openx asegs A4F m a arr size ps AL) as (junk & HDR & ARR & JK & Hlen & Hsz). unfold al_hdr in HDR.
pose proof (u64arr_bound asegs m arr (wl ps) ARR) as AB. rewrite wl_length in AB.
unfold array_list_get_idx_A_entry, array_list_get_idx_A_post, A_GOT_SB, A_SB in *.
unfold alloc_ceiling, sp_window_lo, stack_max_size in LO, Hc8, Hah, Hrh. word_range sp SPR. subst a0 a1.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
clear JK.
apply slots_of_u64arr in ARR. stash SHr. stash ARR.
carve_frame 16%nat ST.
bstep. bstep.
bstep. bstep. bstep.
bstep.
asan_chkA.
bstep.
bstep.
destruct (Z.ltb_spec i (Z.of_nat (length ps))) as [LT|GE].
- if_falsex.
asan_chk0.
bstep.
bstep. bstep.
rewrite (unsigned_lit i) by lia. rewrite (Z.shiftl_mul_pow2 i 3) by lia. change (2^3) with 8.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (HR : ov_read_bytes asegs mc (Z_to_bv 64 (arr / 8 + 2147450880 + i)) 1 = Some [Z_to_bv 8 0])
by (unstash SHr; apply ov_read1_of_ro; eapply (ro_cells_transport asegs _ m mc); [| exact MU | cbn; lia];
apply (shadow_granule0 asegs m (arr / 8 + 2147450880) (8 * size) i); [lia | lia | exact SHr])
end.
bstep. bstep. sh_norm.
replace ((arr + i * 8) / 8 + 2147450880) with (arr / 8 + 2147450880 + i) by (Z.div_mod_to_equations; lia).
bstep. rewrite ?zxb_zero. clear HR.
bstep. if_false.
unstash ARR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (rw_cells_transport asegs _ m mc) in ARR; [| exact MU | exact WM | cbn [disjoint_from]; rewrite slots_size; lia];
pose proof (al_slot_read asegs mc arr ps i (wa (arr + i * 8)) ltac:(apply u64arr_of_slots; exact ARR) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD
end.
bstep. bstep.
bstep. bstep. bstep.
apply evt_done. eexists _, _, _, _, _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
release_frame FR ST (bv_unsigned sp). exact ST.
- if_truex.
bstep.
bstep. bstep. bstep.
apply evt_done. eexists _, _, _, _, _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
release_frame FR ST (bv_unsigned sp). exact ST.
Qed.
End Regs.
End RC__1.
End Mq4.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw Q8tj.
Import QgoP.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import QsKa.Mq9.
Import Qwm6.Mq4 QlKV.Mqj QlKV.Mqc QsKa.Mqc.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Definition lh_table_length_A_entry : Z := 0xa539c.
Definition lh_char_equal_A_entry : Z := 0xa4110.

Lemma icmp_walk_cstr_zero : forall ls rs fuel k v,
~ In b0 ls -> ~ In b0 rs -> (length ls < fuel)%nat ->
icmp_walk cmp_stop cmp_sign (ls ++ [b0]) (rs ++ [b0]) fuel = Some (k, v) -> (v = 0 <-> ls = rs).
Proof.
induction ls as [|a ls IH]; intros rs fuel k v NL NR Hf H.
- destruct fuel as [|fuel]; [cbn in Hf; lia|]. cbn [app] in H. cbn [icmp_walk] in H.
destruct rs as [|b rs]; cbn [app] in H.
+ unfold cmp_stop in H at 1. change (bv_unsigned b0) with 0 in H. cbn [Z.eqb negb orb] in H. injection H as _ <-. unfold cmp_sign. change (bv_unsigned b0) with 0. cbn. split; [reflexivity | intros _; reflexivity].
+ assert (Hb : bv_unsigned b <> 0) by (apply (notin0_nth (b :: rs) 0 b NR); reflexivity).
unfold cmp_stop in H at 1. change (bv_unsigned b0) with 0 in H.
replace (0 =? bv_unsigned b) with false in H by (symmetry; apply Z.eqb_neq; lia). cbn [negb orb] in H.
injection H as _ <-. unfold cmp_sign. change (bv_unsigned b0) with 0. pose proof (byte_range8 b).
split; [intros Hs; exfalso; lia | intros E; discriminate].
- destruct fuel as [|fuel]; [cbn in Hf; lia|]. cbn [app] in H. cbn [icmp_walk] in H.
assert (Ha : bv_unsigned a <> 0) by (apply (notin0_nth (a :: ls) 0 a NL); reflexivity).
pose proof (byte_range8 a) as Ra.
destruct rs as [|b rs]; cbn [app] in H.
+ unfold cmp_stop in H at 1. change (bv_unsigned b0) with 0 in H.
replace (bv_unsigned a =? 0) with false in H by (symmetry; apply Z.eqb_neq; lia). cbn [negb orb] in H.
injection H as _ <-. unfold cmp_sign. change (bv_unsigned b0) with 0.
split; [intros Hs; exfalso; lia | intros E; discriminate].
+ pose proof (byte_range8 b) as Rb.
unfold cmp_stop in H at 1.
destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [Eab | Nab].
* assert (a = b) by (apply bv_eq; exact Eab). subst b.
replace (bv_unsigned a =? 0) with false in H by (symmetry; apply Z.eqb_neq; lia). cbn [negb orb] in H.
destruct (icmp_walk cmp_stop cmp_sign (ls ++ [b0]) (rs ++ [b0]) fuel) as [[j w]|] eqn:E; [|discriminate].
injection H as _ <-.
rewrite (IH rs fuel j w ltac:(intros K; apply NL; right; exact K) ltac:(intros K; apply NR; right; exact K) ltac:(cbn in Hf; lia) E).
split; [intros ->; reflexivity | intros E2; injection E2; auto].
* cbn [negb orb] in H. injection H as _ <-. unfold cmp_sign.
split; [intros Hs; exfalso; lia | intros E2; injection E2 as -> ->; lia].
Qed.

Lemma istrcmp_model_zero : forall ls rs k v, ~ In b0 ls -> ~ In b0 rs ->
istrcmp_model ls rs = Some (k, v) -> (v = 0 <-> ls = rs).
Proof. intros ls rs k v NL NR H. eapply icmp_walk_cstr_zero; [exact NL | exact NR | | exact H]. lia. Qed.

Lemma cmp_stop_nul : forall a, cmp_stop a b0 = true.
Proof. intros a. unfold cmp_stop. change (bv_unsigned b0) with 0. destruct (bv_unsigned a =? 0); reflexivity. Qed.

Lemma icmp_walk_cstr_total : forall ls rs fuel, (length ls < fuel)%nat ->
exists k v, icmp_walk cmp_stop cmp_sign (ls ++ [b0]) (rs ++ [b0]) fuel = Some (k, v).
Proof.
induction ls as [|a ls IH]; intros rs fuel Hf.
- destruct fuel as [|fuel]; [cbn in Hf; lia|]. cbn [app icmp_walk].
destruct rs as [|b rs]; cbn [app]; unfold cmp_stop at 1; change (bv_unsigned b0) with 0; rewrite Z.eqb_refl, orb_true_r; eauto.
- destruct fuel as [|fuel]; [cbn in Hf; lia|]. cbn [app icmp_walk].
destruct rs as [|b rs]; cbn [app].
+ rewrite cmp_stop_nul. eauto.
+ destruct (cmp_stop a b); [eauto|].
destruct (IH rs fuel ltac:(cbn in Hf; lia)) as (k & v & E). rewrite E. eauto.
Qed.

Lemma istrcmp_model_total : forall ls rs, exists k v, istrcmp_model ls rs = Some (k, v).
Proof. intros. apply icmp_walk_cstr_total. lia. Qed.

Lemma seqz_of_model : forall v, -255 <= v <= 255 -> v_sltiu (Z_to_bv 64 v) 1 = Z_to_bv 64 (if v =? 0 then 1 else 0).
Proof.
intros v Hv. unfold v_sltiu. change (bv_wrap 64 1) with 1. rewrite Z_to_bv_unsigned.
change (bv_modulus 64) with 18446744073709551616.
destruct (Z.eqb_spec v 0) as [->|NE].
- reflexivity.
- destruct (Z.ltb_spec (bv_wrap 64 v) 1) as [LT|GE]; [|reflexivity].
exfalso. unfold bv_wrap, bv_modulus in LT. change (2 ^ Z.of_N 64) with 18446744073709551616 in LT.
destruct (Z.lt_ge_cases v 0).
+ rewrite <- (Z.mod_add v 1) in LT by lia. rewrite Z.mod_small in LT by lia. lia.
+ rewrite Z.mod_small in LT by lia. lia.
Qed.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section Regs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).

Lemma lh_table_length_A : forall m lo sbcell (BS : list blk) (t : Z) (kvs : list (Z * Z)),
small_pre sp m lo sbcell ->
lhtab2 asegs A4F m BS t kvs -> 0 < t -> t + 56 <= alloc_ceiling -> t mod 8 = 0 ->
ro_cells asegs m (t / 8 + A_SB) [C1 (Z_to_bv 8 0)] -> t / 8 + A_SB + 1 <= alloc_ceiling ->
evt asegs (small_post ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo (Z_to_bv 64 (Z.of_nat (length kvs))))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 t) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 lh_table_length_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until kvs. intros (MI & ST & LOS & LO & GOT & CELL & Hc0 & Hc8) LH Ht Hth Hal SH0 HSH.
destruct LH as (tbl & size & es & svs & -> & _ & HDR & _ & _ & _ & Hsz & Hcnt & _).
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
unfold lh_hdr, lh_hdrf in HDR.
unfold lh_table_length_A_entry, A_GOT_SB, A_SB in *.
unfold alloc_ceiling, sp_window_lo, stack_max_size in LO, Hth, Hc8, HSH. word_range sp SPR.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
rewrite length_map.
carve_frame 16%nat ST.
bstep. bstep.
bstep. bstep. bstep. bstep.
asan_chk0_off t 4.
bstep. norm_sx32.
bstep. bstep. bstep.
apply evt_done. eexists. split; [eexists _, _, _; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
release_frame FR ST (bv_unsigned sp). exact ST.
Qed.
End Regs.

Section CharEqual.
Hypothesis OBL_ISTRCMP : istrcmp_spec_U.

Lemma lh_char_equal_A :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a b lo : Z) (ls rs : list byte) (k : nat) (v : Z)
(Q : machine_state -> Prop),
istrcmp_model ls rs = Some (k, v) ->
unpoisoned asegs m A_SB a (Z.of_nat k) -> unpoisoned asegs m A_SB b (Z.of_nat k) -> asan_rt_ok m ->
0 <= a -> a + Z.of_nat (length ls) + 1 <= 2^47 -> Z.of_nat (length ls) + 1 < 2^40 -> 0 <= b -> b + Z.of_nat (length rs) + 1 <= 2^47 ->
(64 < Z.of_nat k -> app_mem a (Z.of_nat k) /\ app_mem b (Z.of_nat k)) ->
(a + Z.of_nat (length ls) + 1 <= lo \/ bv_unsigned sp <= a) -> (b + Z.of_nat (length rs) + 1 <= lo \/ bv_unsigned sp <= b) ->
a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 b -> ~ In b0 ls -> ~ In b0 rs ->
bytes_at asegs m a (ls ++ [b0]) -> bytes_at asegs m b (rs ++ [b0]) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 - 4096 -> bv_unsigned sp mod 16 = 0 ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
munch [(lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
bytes_at asegs m' a (ls ++ [b0]) -> bytes_at asegs m' b (rs ++ [b0]) ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (if strcmp_model ls rs =? 0 then 1 else 0)) a1' a2' a3' a4' a5' a6' a7'
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 lh_char_equal_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until Q. intros MODEL UPa UPb RT Ha Han Hl40 Hb Hbn APP SEPa SEPb Ha0 Ha1 NL NR STRa STRb ST LO LOS SPA MI RA K.
subst a0 a1. word_range sp SPR. pose proof alloc_ceiling_ge as ACG.
pose proof (bytes_at_bound _ _ _ _ STRa) as BDa. rewrite length_app in BDa. cbn [length] in BDa.
pose proof (bytes_at_bound _ _ _ _ STRb) as BDb. rewrite length_app in BDb. cbn [length] in BDb.

assert (RES : (if v =? 0 then 1 else 0) = (if strcmp_model ls rs =? 0 then 1 else 0)).
{ pose proof (istrcmp_model_zero ls rs k v NL NR MODEL) as Z1. pose proof (strcmp_model_zero ls rs NL NR) as Z2.
destruct (Z.eqb_spec v 0) as [Hv | Hv]; destruct (Z.eqb_spec (strcmp_model ls rs) 0) as [Hm | Hm]; try reflexivity; exfalso; tauto. }
pose proof (icmp_walk_nread _ _ _ _ _ _ _ MODEL) as (Kf & Kl & Kr). rewrite length_app in Kl, Kr. cbn [length] in Kl, Kr.
pose proof (icmp_walk_pos _ _ _ _ _ _ _ MODEL ltac:(lia)) as K1.
unfold lh_char_equal_A_entry.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
stash STRa. stash STRb.
carve_frame 16%nat ST.
bstep. bstepz.
bstep.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RT1 : asan_rt_ok mc) by (eapply (asan_rt_ok_transport [(lo, bv_unsigned sp)] m mc); [exact RT | exact MU
| intros c Hc; pose proof (a4_rt_cells_in_img c Hc); cbn [disjoint_from]; split; [left; lia | exact I]]);
assert (UPa1 : unpoisoned asegs mc A_SB a (Z.of_nat k))
by (eapply unpoisoned_transport; [exact UPa | exact MU | intros u w Hu Hw; eapply (shadow_outside_stack A_SB a (Z.of_nat k)); try eassumption; unfold A_SB; lia]);
assert (UPb1 : unpoisoned asegs mc A_SB b (Z.of_nat k))
by (eapply unpoisoned_transport; [exact UPb | exact MU | intros u w Hu Hw; eapply (shadow_outside_stack A_SB b (Z.of_nat k)); try eassumption; unfold A_SB; lia]);
assert (STRa1 : bytes_at asegs mc a (ls ++ [b0]))
by (pose proof STRa as S0; unstash S0; eapply bytes_at_transport; [exact S0 | exact MU | cbn [disjoint_from]; rewrite length_app; cbn [length]; lia]);
assert (STRb1 : bytes_at asegs mc b (rs ++ [b0]))
by (pose proof STRb as S0; unstash S0; eapply bytes_at_transport; [exact S0 | exact MU | cbn [disjoint_from]; rewrite length_app; cbn [length]; lia])
end.
clear UPa UPb RT.
eapply (OBL_ISTRCMP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a b lo ls rs k v);
[ exact MODEL | exact UPa1 | exact UPb1 | exact RT1 | lia | lia | lia | lia | lia | exact APP
| rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | reflexivity | reflexivity | exact NL | exact NR
| exact STRa1 | exact STRb1 | rewrite unsigned_lit by lia; exact ST | exact LO | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia | assumption | rewrite unsigned_lit by lia; reflexivity |].
rewrite ?unsigned_lit by lia.
clear UPa1 UPb1 RT1 STRa1 STRb1.
intros x0 x1 x2 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 m2 MU2 WM2 MI2 STRa2 STRb2 ST2.
stash STRa2. stash STRb2.
lazymatch type of MU2 with munch _ ?mc _ =>
transport_after_call asegs mc m2 MU2 WM2; try match goal with H : mem_inv asegs mc |- _ => clear H end end.
clear MU2 WM2.
replace (ret_pc (Z_to_bv 64 0xa411c)) with (Z_to_bv 64 0xa411c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
pose proof (icmp_walk_last _ _ _ _ _ _ _ MODEL ltac:(eapply icmp_walk_pos; [exact MODEL | lia])) as (ca & cb & _ & _ & Hlast).
assert (Rv : -1 <= v <= 1).
{ destruct Hlast as [[_ ->] | (_ & _ & ->)]; [| lia]. unfold cmp_sign. pose proof (byte_range8 ca). pose proof (byte_range8 cb). lia. }
bstep.
rewrite (seqz_of_model v) by lia. rewrite RES.
bstep. bstep. bstep.
unstash STRa2. unstash STRb2.
eapply K; [exact MU | exact WM | exact MI2 | exact STRa2 | exact STRb2 |].
release_frame FR ST2 (bv_unsigned sp). exact ST2.
Qed.
End CharEqual.
End RC__1.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn Q8tj.
Import QSL3.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QsKa.Mqe.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Lemma bytes_at_repeat_sub : forall segs m a v n k j,
bytes_at segs m a (repeat v n) -> (k + j <= n)%nat -> bytes_at segs m (a + Z.of_nat k) (repeat v j).
Proof.
intros segs m a v n k j H Hk.
replace n with (k + (j + (n - k - j)))%nat in H by lia. rewrite 2!repeat_app in H.
apply bytes_at_app in H as [_ H]. rewrite repeat_length in H. apply bytes_at_app in H as [H _]. exact H.
Qed.

Lemma ro_cells_of_repeat : forall segs m a v j,
bytes_at segs m a (repeat v j) -> ro_cells segs m a (map C1 (repeat v j)).
Proof. intros segs m a v j H. split; [apply cells_wf_map_C1 | rewrite cells_bytes_map_C1; exact H]. Qed.

Lemma shadow_bytes_mul8 : forall n, 0 <= n -> shadow_bytes (8 * n) = repeat (Z_to_bv 8 0) (Z.to_nat n).
Proof.
intros n Hn. unfold shadow_bytes.
replace (8 * n / 8) with n by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
replace ((8 * n) mod 8) with 0 by (rewrite Z.mul_comm, Z.mod_mul by lia; reflexivity).
cbn [Z.eqb]. rewrite app_nil_r. reflexivity.
Qed.

Lemma ent_addr_div8 : forall tbl i, tbl mod 8 = 0 -> ent_addr tbl i / 8 = tbl / 8 + 5 * Z.of_nat i.
Proof. intros tbl i H. unfold ent_addr. Z.div_mod_to_equations. nia. Qed.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section WithHI.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Lemma tbl_shadowA : forall A LB LM FR B m md tbl size,
HEAPAx A LB LM FR B m md -> In (tbl, 40 * size) LB -> 0 <= size ->
bytes_at asegs m (tbl / 8 + A_SB) (repeat (Z_to_bv 8 0) (Z.to_nat (5 * size))).
Proof.
intros A LB LM FR B m md tbl size HP Hin Hsz.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ _ _ HP Hin) as SH. unfold shad in SH. cbn [hl_sb hl_segs hla_base A4L A4H] in SH.
replace (40 * size) with (8 * (5 * size)) in SH by lia. rewrite shadow_bytes_mul8 in SH by lia. exact SH.
Qed.

Lemma ent_shadowA : forall A LB LM FR B m md tbl size i,
HEAPAx A LB LM FR B m md -> In (tbl, 40 * size) LB -> tbl mod 8 = 0 -> Z.of_nat i < size ->
ro_cells asegs m (ent_addr tbl i / 8 + A_SB)
[C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof.
intros A LB LM FR B m md tbl size i HP Hin Hal Hi.
pose proof (tbl_shadowA _ _ _ _ _ _ _ tbl size HP Hin ltac:(lia)) as SH.
apply (bytes_at_repeat_sub asegs m _ _ _ (5 * i) 5) in SH; [|lia].
rewrite ent_addr_div8 by exact Hal.
replace (tbl / 8 + 5 * Z.of_nat i + A_SB) with (tbl / 8 + A_SB + Z.of_nat (5 * i)) by lia.
exact (ro_cells_of_repeat asegs m _ _ 5 SH).
Qed.

Lemma ent_shadow_sepA : forall A LB LM FR B m md tbl size i g b k,
HEAPAx A LB LM FR B m md -> In (tbl, 40 * size) LB -> tbl mod 8 = 0 -> Z.of_nat i < size -> 0 <= g < 5 -> In (b, k) (LB ++ LM) ->
ent_addr tbl i / 8 + A_SB + g < alloc_ceiling
/\ (ent_addr tbl i / 8 + A_SB + g < b \/ b + k <= ent_addr tbl i / 8 + A_SB + g)
/\ (ent_addr tbl i / 8 + A_SB + g < 0x10000 \/ 0x647000 <= ent_addr tbl i / 8 + A_SB + g).
Proof.
intros A LB LM FR B m md tbl size i g b k HP Hin Hal Hi Hg Hb.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tbl (40 * size) (5 * Z.of_nat i + g) b k HP Hin ltac:(Z.div_mod_to_equations; nia) Hb) as X.
cbn [hl_sb hl_img_lo hl_img_hi hla_base A4L A4H] in X. rewrite ent_addr_div8 by exact Hal.
replace (tbl / 8 + 5 * Z.of_nat i + A_SB + g) with (tbl / 8 + A_SB + (5 * Z.of_nat i + g)) by lia. exact X.
Qed.
End WithHI.
End RC__1.
End Mq6.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqe.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Definition lh_char_hash_A_entry : Z := 0xa2c54.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section S.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Variable MREL : config -> config -> Prop.

Definition lh_hash_A_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (h : Z) (errv' : word),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 h) m' ms' /\ 0 <= h < 2^64 /\
MREL md md' /\ stk asegs m' lo (bv_unsigned sp) /\ heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\ lh_globA m' /\ HEAPAx A' LB LM FRS B m' md'.

Definition lh_char_hash_A_stmt (HD : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word) (kp kn : Z) (ks : list byte),
HEAPAx A LB LM FRS B m md -> In (kp, kn) LB -> cstr asegs m kp kn ks -> lh_globA m ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - HD ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 -> frm0 fc ->
Z.of_nat (length FRS) < 4096 ->
a0 = Z_to_bv 64 kp ->
(forall ms' md' A', lh_hash_A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 lh_char_hash_A_entry) fc None m (seg_rom asegs)).
End S.
End RC__1.
