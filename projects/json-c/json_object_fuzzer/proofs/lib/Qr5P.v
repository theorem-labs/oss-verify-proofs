(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply Q5Rg QRjH QHnV QCcH QfLs Q0Ek Qsw7 QJjn Q8tj QSL3 Q7UD Qhd4 Qwm6 QlKV QsKa Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn Q8tj.
Import QSL3.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QsKa.Mq5 QlKV.Mq7.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Definition lh_kchar_table_new_A_entry : Z := 0xa1d48.

Lemma ro_C1_of_repeat : forall segs m a v n k,
bytes_at segs m a (repeat v n) -> (k < n)%nat -> ro_cells segs m (a + Z.of_nat k) [C1 v].
Proof.
intros segs m a v n k H Hk.
replace n with (k + (1 + (n - k - 1)))%nat in H by lia. rewrite 2!repeat_app in H.
apply bytes_at_app in H as [_ H]. rewrite repeat_length in H. apply bytes_at_app in H as [H _].
split; [cbn; split; exact I | cbn [cells_bytes cbytes app repeat]; exact H].
Qed.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma lh_init_loopA :
forall (k i n : nat) (x1 x2 gp tp t0 t1 t2 x8 a3 a4 a5 a6 a7 x18 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (tbl sh : Z),
(k = n - 1 - i)%nat -> (i < n)%nat -> 0 <= tbl -> tbl + 40 * Z.of_nat n < 2^64 -> 0 <= sh -> sh + 5 * Z.of_nat n < 2^64 ->
mem_inv asegs m ->
lh_slots asegs m tbl (init_svs i n) ->
(forall j, (j < n)%nat -> ro_cells asegs m (sh + 5 * Z.of_nat j) [C1 (Z_to_bv 8 0)]) ->
(forall j, (j < n)%nat -> sh + 5 * Z.of_nat j + 1 <= tbl \/ tbl + 40 * Z.of_nat n <= sh + 5 * Z.of_nat j) ->
evt asegs (fun ms' => exists m',
ms' = MS (mkR x1 x2 gp tp t0 t1 t2 x8 (Z_to_bv 64 0) (Z_to_bv 64 (tbl + 40 * Z.of_nat n)) (Z_to_bv 64 (tbl + 40 * Z.of_nat n)) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) a4 a5 a6 a7 x18 (Z_to_bv 64 (sh + 5 * Z.of_nat n)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa1e7c) fc None m' (seg_rom asegs)
/\ munch [(tbl, tbl + 40 * Z.of_nat n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ lh_slots asegs m' tbl (init_svs n n)
/\ (forall j, (j < n)%nat -> ro_cells asegs m' (sh + 5 * Z.of_nat j) [C1 (Z_to_bv 8 0)]))
(MS (mkR x1 x2 gp tp t0 t1 t2 x8 (Z_to_bv 64 (Z.of_nat (n - i))) (Z_to_bv 64 (tbl + 40 * Z.of_nat i)) (Z_to_bv 64 (tbl + 40 * Z.of_nat i)) (Z_to_bv 64 (-1)) a3 a4 a5 a6 a7 x18 (Z_to_bv 64 (sh + 5 * Z.of_nat i)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa1e4c) fc None m (seg_rom asegs)).
Proof.
induction k as [|k IH]; intros until sh; intros Hk Hi Ht0 Htn Hs0 Hsn MI SL SH DJ.
- pose proof (SL i ZSLOT (init_svs_nth_ge i n i ltac:(lia))) as C. unfold ent_addr, slot_cells, ZSLOT in C. cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv] in C.
pose proof (SH i Hi) as SHi. pose proof (DJ i Hi) as DJi.
pose proof (munch_refl [(tbl, tbl + 40 * Z.of_nat n)] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(tbl + 40 * Z.of_nat i, tbl + 40 * Z.of_nat i + 40)] m) as MU2.
remember (tbl + 40 * Z.of_nat i) as B eqn:EB.
remember (sh + 5 * Z.of_nat i) as SA eqn:ESA.
step. rewrite ?zxb_zero.
step. if_false.
stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (SL' : lh_slots asegs mx tbl (init_svs (S i) n)) end.
{ rewrite <- init_svs_step by lia. eapply (lh_slots_write_slot asegs m _ tbl (init_svs i n) i ESLOT SL);
[rewrite init_svs_length; lia | unfold ent_addr; rewrite <- EB; exact MU2 | exact WM |].
unfold ent_addr, slot_cells, ESLOT. cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv]. rewrite <- EB.
replace (Z_to_bv 64 LH_EMPTYv) with (Z_to_bv 64 18446744073709551615) by reflexivity. exact C. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (SH' : forall j, (j < n)%nat -> ro_cells asegs mx (sh + 5 * Z.of_nat j) [C1 (Z_to_bv 8 0)]) end.
{ intros j Hj. eapply (ro_cells_transport asegs _ m); [exact (SH j Hj) | exact MU2 |]. cbn. pose proof (DJ j Hj). split; [nia | exact I]. }
clear C MU2 SL SHi.
step. step. step. step.
step. subst B SA. if_falsex.
step.
apply evt_done. eexists. split; [|split; [exact MU | split; [exact WM | split; [exact MI | split; [| exact SH']]]]].
+ replace (Z.of_nat (n - i) + -1) with 0 by lia.
replace (tbl + 40 * Z.of_nat i + 40) with (tbl + 40 * Z.of_nat n) by lia.
replace (sh + 5 * Z.of_nat i + 5) with (sh + 5 * Z.of_nat n) by lia. reflexivity.
+ replace n with (S i) at 1 by lia. exact SL'.
- pose proof (SL i ZSLOT (init_svs_nth_ge i n i ltac:(lia))) as C. unfold ent_addr, slot_cells, ZSLOT in C. cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv] in C.
pose proof (SH i Hi) as SHi. pose proof (DJ i Hi) as DJi.
pose proof (munch_refl [(tbl, tbl + 40 * Z.of_nat n)] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(tbl + 40 * Z.of_nat i, tbl + 40 * Z.of_nat i + 40)] m) as MU2.
remember (tbl + 40 * Z.of_nat i) as B eqn:EB.
remember (sh + 5 * Z.of_nat i) as SA eqn:ESA.
step. rewrite ?zxb_zero.
step. if_false.
stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (SL' : lh_slots asegs mx tbl (init_svs (S i) n)) end.
{ rewrite <- init_svs_step by lia. eapply (lh_slots_write_slot asegs m _ tbl (init_svs i n) i ESLOT SL);
[rewrite init_svs_length; lia | unfold ent_addr; rewrite <- EB; exact MU2 | exact WM |].
unfold ent_addr, slot_cells, ESLOT. cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv]. rewrite <- EB.
replace (Z_to_bv 64 LH_EMPTYv) with (Z_to_bv 64 18446744073709551615) by reflexivity. exact C. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (SH' : forall j, (j < n)%nat -> ro_cells asegs mx (sh + 5 * Z.of_nat j) [C1 (Z_to_bv 8 0)]) end.
{ intros j Hj. eapply (ro_cells_transport asegs _ m); [exact (SH j Hj) | exact MU2 |]. cbn. pose proof (DJ j Hj). split; [nia | exact I]. }
clear C MU2 SL SHi.
step. step. step. step.
step. subst B SA. if_truex.
replace (Z.of_nat (n - i) + -1) with (Z.of_nat (n - S i)) by lia.
replace (tbl + 40 * Z.of_nat i + 40) with (tbl + 40 * Z.of_nat (S i)) by lia.
replace (sh + 5 * Z.of_nat i + 5) with (sh + 5 * Z.of_nat (S i)) by lia.
eapply evt_cut.
{ eapply (IH (S i) n); [lia | lia | exact Ht0 | exact Htn | exact Hs0 | exact Hsn | | exact SL' | exact SH' | exact DJ]. assumption. }
cbv beta. intros ms' (m' & -> & MU' & WM' & MI' & SLn & SHn).
apply evt_done. exists m'. split; [reflexivity|]. split; [|split; [|split; [exact MI' | split; [exact SLn | exact SHn]]]].
+ eapply munch_trans; [exact MU | exact MU'].
+ eapply wmono_trans; [exact WM | exact WM'].
Qed.

Section ALhNew.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Hypothesis OBL_RTC_LHEQ : rtc_lheq_stmt HIx.

Definition lhnew_costB : Z := (16 * (1 * 56) + 512) + (16 * (16 * 40) + 512) + 512.

Definition lh_table_new_A_post (u : uwd) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : Z) (errv' : word) (B' : bud),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\
lh_globA m' /\
bB B - lhnew_costB <= bB B' /\ bD B - uw_cost u <= bD B' /\
( (r = 0 /\ HEAPAx A' LB LM FRS B' m' md')
\/ (r <> 0 /\ exists BS, lhtab2 asegs A4F m' BS r [] /\ HEAPAx A' (BS ++ LB) LM FRS B' m' md') ).

End ALhNew.
End RC__1.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRBl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqe. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqh.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Definition lh_kchar_table_new_A_entry : Z := 0xa412c.

Lemma ro_C1_of_repeat : forall segs m a v n k,
bytes_at segs m a (repeat v n) -> (k < n)%nat -> ro_cells segs m (a + Z.of_nat k) [C1 v].
Proof.
intros segs m a v n k H Hk.
replace n with (k + (1 + (n - k - 1)))%nat in H by lia. rewrite 2!repeat_app in H.
apply bytes_at_app in H as [_ H]. rewrite repeat_length in H. apply bytes_at_app in H as [H _].
split; [cbn; split; exact I | cbn [cells_bytes cbytes app repeat]; exact H].
Qed.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma lh_init_loopA :
forall (k i n : nat) (x1 x2 gp tp t0 t1 t2 x8 x9 a1v a3v a7v x18 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (tbl sh : Z),
(k = n - 1 - i)%nat -> (i < n)%nat -> 0 <= tbl -> tbl + 40 * Z.of_nat n < 2^64 -> 0 <= sh -> sh + 5 * Z.of_nat n < 2^64 ->
tbl mod 8 = 0 -> sh = tbl / 8 + 2147450880 -> bv_unsigned a3v = 2^64 - 1 - tbl ->
mem_inv asegs m ->
lh_slots asegs m tbl (init_svs i n) ->
(forall j, (j < n)%nat -> ro_cells asegs m (sh + 5 * Z.of_nat j) [C1 (Z_to_bv 8 0)]) ->
(forall j, (j < n)%nat -> sh + 5 * Z.of_nat j + 1 <= tbl \/ tbl + 40 * Z.of_nat n <= sh + 5 * Z.of_nat j) ->
evt asegs (fun ms' => exists m' (a1' a7' : word),
ms' = MS (mkR x1 x2 gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 tbl) a1' (Z_to_bv 64 (40 * Z.of_nat n)) a3v (Z_to_bv 64 0) (Z_to_bv 64 (40 * Z.of_nat n)) (Z_to_bv 64 (-1)) a7' x18 (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa4278) fc None m' (seg_rom asegs)
/\ munch [(tbl, tbl + 40 * Z.of_nat n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ lh_slots asegs m' tbl (init_svs n n)
/\ (forall j, (j < n)%nat -> ro_cells asegs m' (sh + 5 * Z.of_nat j) [C1 (Z_to_bv 8 0)]))
(MS (mkR x1 x2 gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 tbl) a1v (Z_to_bv 64 (40 * Z.of_nat i)) a3v (Z_to_bv 64 0) (Z_to_bv 64 (40 * Z.of_nat n)) (Z_to_bv 64 (-1)) a7v x18 (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa4240) fc None m (seg_rom asegs)).
Proof.
induction k as [|k IH]; intros until sh; intros Hk Hi Ht0 Htn Hs0 Hsn Hal Hsh Ha3 MI SL SH DJ.
-
pose proof (SL i ZSLOT (init_svs_nth_ge i n i ltac:(lia))) as C. unfold ent_addr, slot_cells, ZSLOT in C. cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv] in C.
pose proof (SH i Hi) as SHi. pose proof (DJ i Hi) as DJi.
pose proof (munch_refl [(tbl, tbl + 40 * Z.of_nat n)] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(tbl + 40 * Z.of_nat i, tbl + 40 * Z.of_nat i + 40)] m) as MU2.
step.
replace (bv_ltu a3v (Z_to_bv 64 (40 * Z.of_nat i))) with false by (symmetry; unfold bv_ltu; rewrite Ha3, unsigned_lit by lia; apply Z.ltb_ge; lia). cbv iota.
step. ub_if_lit.
step.
step. step. sh_norm.
replace ((tbl + 40 * Z.of_nat i) / 8 + 2147450880) with (sh + 5 * Z.of_nat i) by (subst sh; clear - Hal; Z.div_mod_to_equations; lia).
remember (sh + 5 * Z.of_nat i) as SA eqn:ESA.
step. rewrite ?zxb_zero.
step. if_false.
step.
remember (tbl + 40 * Z.of_nat i) as B eqn:EB.
stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (SL' : lh_slots asegs mx tbl (init_svs (S i) n)) end.
{ rewrite <- init_svs_step by lia. eapply (lh_slots_write_slot asegs m _ tbl (init_svs i n) i ESLOT SL);
[rewrite init_svs_length; lia | unfold ent_addr; rewrite <- EB; exact MU2 | exact WM |].
unfold ent_addr, slot_cells, ESLOT. cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv]. rewrite <- EB.
replace (Z_to_bv 64 LH_EMPTYv) with (Z_to_bv 64 18446744073709551615) by reflexivity. exact C. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (SH' : forall j, (j < n)%nat -> ro_cells asegs mx (sh + 5 * Z.of_nat j) [C1 (Z_to_bv 8 0)]) end.
{ intros j Hj. eapply (ro_cells_transport asegs _ m); [exact (SH j Hj) | exact MU2 |]. cbn. pose proof (DJ j Hj). split; [nia | exact I]. }
clear C MU2 SL SHi.
step. subst B SA. if_falsex.
step.
apply evt_done. eexists _, _, _. split; [|split; [exact MU | split; [exact WM | split; [exact MI | split; [| exact SH']]]]].
+ replace (40 * Z.of_nat i + 40) with (40 * Z.of_nat n) by lia. reflexivity.
+ replace n with (S i) at 1 by lia. exact SL'.
-
pose proof (SL i ZSLOT (init_svs_nth_ge i n i ltac:(lia))) as C. unfold ent_addr, slot_cells, ZSLOT in C. cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv] in C.
pose proof (SH i Hi) as SHi. pose proof (DJ i Hi) as DJi.
pose proof (munch_refl [(tbl, tbl + 40 * Z.of_nat n)] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(tbl + 40 * Z.of_nat i, tbl + 40 * Z.of_nat i + 40)] m) as MU2.
step.
replace (bv_ltu a3v (Z_to_bv 64 (40 * Z.of_nat i))) with false by (symmetry; unfold bv_ltu; rewrite Ha3, unsigned_lit by lia; apply Z.ltb_ge; lia). cbv iota.
step. ub_if_lit.
step.
step. step. sh_norm.
replace ((tbl + 40 * Z.of_nat i) / 8 + 2147450880) with (sh + 5 * Z.of_nat i) by (subst sh; clear - Hal; Z.div_mod_to_equations; lia).
remember (sh + 5 * Z.of_nat i) as SA eqn:ESA.
step. rewrite ?zxb_zero.
step. if_false.
step.
remember (tbl + 40 * Z.of_nat i) as B eqn:EB.
stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (SL' : lh_slots asegs mx tbl (init_svs (S i) n)) end.
{ rewrite <- init_svs_step by lia. eapply (lh_slots_write_slot asegs m _ tbl (init_svs i n) i ESLOT SL);
[rewrite init_svs_length; lia | unfold ent_addr; rewrite <- EB; exact MU2 | exact WM |].
unfold ent_addr, slot_cells, ESLOT. cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv]. rewrite <- EB.
replace (Z_to_bv 64 LH_EMPTYv) with (Z_to_bv 64 18446744073709551615) by reflexivity. exact C. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (SH' : forall j, (j < n)%nat -> ro_cells asegs mx (sh + 5 * Z.of_nat j) [C1 (Z_to_bv 8 0)]) end.
{ intros j Hj. eapply (ro_cells_transport asegs _ m); [exact (SH j Hj) | exact MU2 |]. cbn. pose proof (DJ j Hj). split; [nia | exact I]. }
clear C MU2 SL SHi.
step. subst B SA. if_truex.
replace (40 * Z.of_nat i + 40) with (40 * Z.of_nat (S i)) by lia.
eapply evt_cut.
{ eapply (IH (S i) n); [lia | lia | exact Ht0 | exact Htn | exact Hs0 | exact Hsn | exact Hal | exact Hsh | exact Ha3 | | exact SL' | exact SH' | exact DJ]. assumption. }
cbv beta. intros ms' (m' & a1' & a7' & -> & MU' & WM' & MI' & SLn & SHn).
apply evt_done. exists m', a1', a7'. split; [reflexivity|]. split; [|split; [|split; [exact MI' | split; [exact SLn | exact SHn]]]].
+ eapply munch_trans; [exact MU | exact MU'].
+ eapply wmono_trans; [exact WM | exact WM'].
Qed.

Section ALhNew.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Hypothesis OBL_RTC_LHEQ : rtc_lheq_stmt HIx.

Definition lhnew_costB : Z := (16 * (1 * 56) + 512) + (16 * (16 * 40) + 512) + 512.

Definition lh_table_new_A_post (u : uwd) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : Z) (errv' : word) (B' : bud),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\
lh_globA m' /\
bB B - lhnew_costB <= bB B' /\ bD B - uw_cost u <= bD B' /\
( (r = 0 /\ HEAPAx A' LB LM FRS B' m' md')
\/ (r <> 0 /\ exists BS, lhtab2 asegs A4F m' BS r [] /\ HEAPAx A' (BS ++ LB) LM FRS B' m' md') ).

End ALhNew.
End RC__1.
