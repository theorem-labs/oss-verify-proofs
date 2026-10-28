(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup QRjH QHnV QCcH QfLs Q0Ek Q6q3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup.
Import UEQM.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek.
Import UC8c.Mq0 UC8c.
Import Q6q3.
Import ListNotations.
Open Scope Z_scope.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition JG_HASH_P : Z := 0x66a38.  Definition JG_GOT_P : Z := 0x658e0.  Definition JG_VDSO_P : Z := 0x66f20.  Definition JG_CGT_P : Z := 0x61050.
Definition jc_glob_P (m : word -> option byte) : Prop :=
(exists seed : word, rw_cells rsegs m 0x66a38 [C8 (Z_to_bv 64 (fn_lh_char_hash S4F)); C4 seed])
/\ rw_cells rsegs m 0x658e0 [C8 (Z_to_bv 64 (fn_lh_char_equal S4F))]
/\ (exists vf : Z, rw_cells rsegs m 0x66f20 [C8 (Z_to_bv 64 vf)] /\ (vf = 0x61050 \/ vf = 0)).

#[using="Type"] Lemma disjoint_from_Forall : forall W A n,
Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) W -> disjoint_from W A n.
Proof.
induction W as [|[lo hi] W IH]; intros A n H; [exact I|].
apply Forall_cons_iff in H as [H1 H]. cbn [fst snd] in H1. split; [exact H1 | apply IH; exact H].
Qed.

#[using="Type"] Lemma jc_glob_P_pres : forall LB SP m m', heap_pres S4L LB SP m m' -> jc_glob_P m -> jc_glob_P m'.
Proof.
intros LB SP m m' HPR ([seed G1] & G2 & (vf & G3 & VF)). split; [| split].
- exists seed. eapply (heap_pres_rw_cells S4L); [exact HPR | exact G1 |]. right; left. intros a Ha. cbn in Ha. cbn. unfold s4_client_static. lia.
- eapply (heap_pres_rw_cells S4L); [exact HPR | exact G2 |]. right; left. intros a Ha. cbn in Ha. cbn. unfold s4_client_static. lia.
- exists vf. split; [| exact VF]. eapply (heap_pres_rw_cells S4L); [exact HPR | exact G3 |]. right; left. intros a Ha. cbn in Ha. cbn. unfold s4_client_static. lia.
Qed.

#[using="Type"] Lemma jc_glob_P_munch : forall m m' W,
jc_glob_P m -> munch W m m' -> wmono rsegs m m' ->
Forall (fun iv => (0x66a38 + 12 <= fst iv \/ snd iv <= 0x66a38) /\ (0x658e0 + 8 <= fst iv \/ snd iv <= 0x658e0) /\ (0x66f20 + 8 <= fst iv \/ snd iv <= 0x66f20)) W ->
jc_glob_P m'.
Proof.
intros m m' W ([seed G1] & G2 & (vf & G3 & VF)) MU WM DJ.
split; [| split].
- exists seed. eapply (rw_cells_transport rsegs W m m'); [exact G1 | exact MU | exact WM |]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add].
apply disjoint_from_Forall. eapply Forall_impl; [| exact DJ]. intros [lo hi] H. cbn [fst snd] in H |- *. pose proof (proj1 H). lia.
- eapply (rw_cells_transport rsegs W m m'); [exact G2 | exact MU | exact WM |]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add].
apply disjoint_from_Forall. eapply Forall_impl; [| exact DJ]. intros [lo hi] H. cbn [fst snd] in H |- *. pose proof (proj1 (proj2 H)). lia.
- exists vf. split; [| exact VF]. eapply (rw_cells_transport rsegs W m m'); [exact G3 | exact MU | exact WM |]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add].
apply disjoint_from_Forall. eapply Forall_impl; [| exact DJ]. intros [lo hi] H. cbn [fst snd] in H |- *. pose proof (proj2 (proj2 H)). lia.
Qed.

#[using="Type"] Lemma jc_glob_P_outside : forall m m' W,
jc_glob_P m -> munch W m m' -> wmono rsegs m m' ->
Forall (fun iv => snd iv <= 0x62000 \/ 0x99000 <= fst iv) W -> jc_glob_P m'.
Proof.
intros m m' W G MU WM HW. eapply jc_glob_P_munch; [exact G | exact MU | exact WM |].
eapply Forall_impl; [| exact HW]. intros [lo hi] H. cbn [fst snd] in *. lia.
Qed.
End RC__1.
End Mq0.
From Stdlib Require NArith.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply Qsw7 QJjn QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import UEQM.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek.
Import UC8c.Mq0 UC8c.
Import Qsw7 QJjn QRUw.
Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Section Regs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).

Definition ret2 (segs : list Segment) (v w : word) (m' : word -> option byte) : machine_state -> Prop :=
fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 v w a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs).
Definition ret2x (segs : list Segment) (v : word) (m' : word -> option byte) : machine_state -> Prop :=
fun ms' => exists w, ret2 segs v w m' ms'.
Definition ret3x (segs : list Segment) (v : word) (m' : word -> option byte) : machine_state -> Prop :=
fun ms' => exists w x, ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 v w x a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs).

#[using="Type"] Lemma jo_get_null_P : forall a1 m,
evt rsegs (ret2 rsegs (Z_to_bv 64 0) a1 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x24634) fc None m (seg_rom rsegs)).
Proof. intros. step. if_true. step. apply evt_done. reflexivity. Qed.
#[using="Type"] Lemma jo_get_P : forall a1 m p ty rc tojs pb udel ud rest,
rw_cells rsegs m p (jhdr_cells ty rc tojs pb udel ud ++ rest) ->
0 < p -> p + 40 <= 2^64 -> p mod 16 = 0 -> 0 <= rc -> rc + 1 < 2^31 -> mem_inv rsegs m ->
evt rsegs (fun ms' => exists m', ret2x rsegs (Z_to_bv 64 p) m' ms' /\ munch [(p + 4, p + 8)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' p (jhdr_cells ty (rc + 1) tojs pb udel ud ++ rest))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x24634) fc None m (seg_rom rsegs)).
Proof.
intros until rest. intros HDR Hp Hph Hal Hrc Hrc1 MI. unfold jhdr_cells in HDR. cbn [app] in HDR.
pose proof (wmono_refl rsegs m) as WM. pose proof (munch_refl [(p + 4, p + 8)] m) as MU.
step. if_falsex. step. step. ubsan_align Hal. step. step. norm_w32. stepz. step.
apply evt_done. eexists. split; [eexists; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
unfold jhdr_cells. cbn [app]. assumption.
Qed.
#[using="Type"] Lemma jo_get_type_null_P : forall a1 m,
evt rsegs (ret2 rsegs (Z_to_bv 64 0) a1 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2496c) fc None m (seg_rom rsegs)).
Proof. intros. step. if_true. step. apply evt_done. reflexivity. Qed.
#[using="Type"] Lemma jo_get_type_P : forall a1 m p ty rc tojs pb udel ud rest,
rw_cells rsegs m p (jhdr_cells ty rc tojs pb udel ud ++ rest) -> 0 < p -> p + 40 <= 2^64 -> p mod 16 = 0 -> 0 <= ty < 2^31 -> mem_inv rsegs m ->
evt rsegs (ret2x rsegs (Z_to_bv 64 ty) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2496c) fc None m (seg_rom rsegs)).
Proof.
intros until rest. intros HDR Hp Hph Hal Hty MI. unfold jhdr_cells in HDR. cbn [app] in HDR.
step. if_falsex. step. step. ubsan_align Hal. step. norm_w32. step. apply evt_done. eexists. reflexivity.
Qed.
Definition is_type_res (ty ty' : Z) : Z := if Z.eqb ty ty' then 1 else 0.

#[using="Type"] Lemma jo_get_object_P : forall a1 m p rc tojs pb udel ud t rest,
rw_cells rsegs m p (jhdr_cells JT_OBJECT rc tojs pb udel ud ++ [C8 (Z_to_bv 64 t)] ++ rest) -> 0 < p -> p + 48 <= 2^64 -> p mod 16 = 0 -> mem_inv rsegs m ->
evt rsegs (ret3x rsegs (Z_to_bv 64 t) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x254cc) fc None m (seg_rom rsegs)).
Proof.
intros until rest. intros HDR Hp Hph Hal MI. unfold jhdr_cells, JT_OBJECT in HDR. cbn [app] in HDR.
step. if_falsex. step. step. ubsan_align Hal. step. step. step. if_falsex. step. step. apply evt_done. do 2 eexists. reflexivity.
Qed.
End Regs.
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import UEQM.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek.
Import UC8c.Mq0 UC8c.
Import Qsw7 QJjn QRUw.
Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Definition printbuf_reset_post (segs : list Segment)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (pb buf cap : Z) (content : list byte) : machine_state -> Prop :=
fun ms' => exists m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 buf) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(buf, buf + 1); (pb + 8, pb + 12)] m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ pbuf_core segs m' pb buf 0 cap ([Z_to_bv 8 0] ++ skipn 1 content).

Lemma printbuf_reset_P :
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (pb buf bpos cap : Z) (content : list byte),
pbuf_core rsegs m pb buf bpos cap content ->
0 < pb -> pb + 16 <= 2^64 -> pb mod 16 = 0 -> 0 < buf -> buf + cap <= 2^64 -> (pb + 16 <= buf \/ buf + cap <= pb) ->
mem_inv rsegs m ->
evt rsegs (printbuf_reset_post rsegs ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 pb) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m pb buf cap content)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 pb) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x245cc) fc None m (seg_rom rsegs)).
Proof.
intros until content. intros (Hbp & Hcap & Hlen & PBS & PBUF) Hpb Hpbh Hal Hbuf Hbufh Hdisj MI.
pose proof (wmono_refl rsegs m) as WM.
pose proof (munch_refl [(buf, buf + 1); (pb + 8, pb + 12)] m) as MU.
destruct content as [|c0 content']; [cbn in Hlen; lia|].
destruct (rw_cells_CB_cut rsegs _ _ _ _ 1%nat PBUF ltac:(lia)) as [PB0 PB1]. clear PBUF. cbn [firstn skipn] in PB0, PB1.
apply (rw_cells_recast rsegs _ _ _ [C1 c0]) in PB0; [| cbn; auto | reflexivity | reflexivity].
step. if_falsex. step. step. ubsan_align Hal.
step. step. if_falsex. stepz. stepz. step.
apply evt_done. unfold printbuf_reset_post. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
unfold pbuf_core. split; [lia|]. split; [lia|]. split; [cbn [length app skipn] in *; rewrite ?skipn_O; lia|]. split; [eassumption|].
match goal with P0 : rw_cells rsegs ?mf buf [C1 _], P1 : rw_cells rsegs _ (buf + _) [CB _ _] |- _ =>
apply (rw_cells_recast rsegs _ _ _ [CB 1 [Z_to_bv 8 0]]) in P0; [| cbn; auto | reflexivity | reflexivity];
pose proof (rw_cells_CB_join rsegs _ _ _ _ _ _ P0 P1) as J end.
replace (1 + (Z.to_nat cap - 1))%nat with (Z.to_nat cap) in J by lia. exact J.
Qed.

End Mq2.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import UEQM.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV Qsw7 QJjn QRUw.
Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Definition validate_utf8_entry_P : Z := 0x240ac.
Section Regs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).

Definition vutf8_post (segs : list Segment) (a1 : word) (A : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (r : Z) (a2' a3' nv' : word) (m' : word -> option byte),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ ((r = 0 /\ m' = m) \/ r = 1)
/\ rw_cells segs m' A [C4 nv'] /\ munch [(A, A + 4)] m m' /\ wmono segs m m' /\ mem_inv segs m'.

Local Ltac if_any := lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd; cbv iota end.

Local Ltac vdone MU WM :=
apply evt_done; unfold vutf8_post; cbv beta;
eexists; eexists; eexists; eexists; eexists; split; [reflexivity|];
split; [first [right; reflexivity | left; split; reflexivity] |];
split; [eassumption|]; split; [exact MU|]; split; [exact WM | assumption].

#[using="Type"] Lemma land3_of_mod4 : forall p, p mod 4 = 0 -> Z.land p 3 = 0.
Proof. intros p Hp. change 3 with (2^2 - 1). rewrite zb_land_mask by lia. exact Hp. Qed.

#[using="Type"] Lemma validate_utf8_P : forall (c : byte) (a2 a3 : word) (A : Z) (nv : word) (m : word -> option byte),
rw_cells rsegs m A [C4 nv] -> 0 < A -> A + 4 <= 2^64 -> A mod 4 = 0 -> mem_inv rsegs m ->
evt rsegs (vutf8_post rsegs (Z_to_bv 64 A) A m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (zxb c) (Z_to_bv 64 A) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 validate_utf8_entry_P) fc None m (seg_rom rsegs)).
Proof.
intros c a2 a3 A nv m NB HA HA4 HAL MI. unfold validate_utf8_entry_P.
pose proof (wmono_refl rsegs m) as WM. pose proof (munch_refl [(A, A + 4)] m) as MU.
pose proof (bv_unsigned_in_range 8 c) as CBR; unfold bv_modulus in CBR; cbn in CBR.
step. step. rewrite (unsigned_lit A) by lia. rewrite (land3_of_mod4 A HAL). if_false.
step.
step. if_any.
-
step. step. if_any.
+
step. step. step. if_any.
* step. step. step. if_any.
-- step. step. step. if_any.
++  step. step. vdone MU WM.
++ step. step. step. step. step. vdone MU WM.
-- step. step. step. step. step. vdone MU WM.
* step. step. step. step. step. vdone MU WM.
+  step. step. vdone MU WM.
-
step. step. step. step. if_any.
+  step. step. vdone MU WM.
+ step. step. step. step. vdone MU WM.
Qed.

Definition vutf8_postF (segs : list Segment) (a1 : word) (A B : Z) (pre post : list cell) (m : word -> option byte)
: machine_state -> Prop :=
fun ms' => exists (r : Z) (a2' a3' nv' : word) (m' : word -> option byte),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ ((r = 0 /\ m' = m) \/ r = 1)
/\ rw_cells segs m' B (pre ++ C4 nv' :: post) /\ munch [(A, A + 4)] m m' /\ wmono segs m m' /\ mem_inv segs m'.

#[using="Type"] Lemma vutf8_frame : forall segs a1 A B pre nv post m ms',
rw_cells segs m B (pre ++ C4 nv :: post) -> A = B + Z.of_nat (cells_size pre) ->
vutf8_post segs a1 A m ms' -> vutf8_postF segs a1 A B pre post m ms'.
Proof.
intros segs a1 A B pre nv post m ms' FR HA (r & a2' & a3' & nv' & m' & E & Hr & NB' & MU & WM & MI').
exists r, a2', a3', nv', m'. split; [exact E|]. split; [exact Hr|]. split; [| split; [exact MU | split; [exact WM | exact MI']]].
apply rw_cells_app in FR as [FR1 FR2]. change (C4 nv :: post) with ([C4 nv] ++ post) in FR2. apply rw_cells_app in FR2 as [_ FR3].
cbn [cells_size csize Nat.add] in FR3.
apply rw_cells_app. split.
- eapply rw_cells_transport; [exact FR1 | exact MU | exact WM | cbn; lia].
- change (C4 nv' :: post) with ([C4 nv'] ++ post). apply rw_cells_app. split; [rewrite <- HA; exact NB'|].
cbn [cells_size csize Nat.add]. eapply rw_cells_transport; [exact FR3 | exact MU | exact WM | cbn; lia].
Qed.

#[using="Type"] Lemma validate_utf8_frame_P : forall (c : byte) (a2 a3 : word) (A B : Z) (pre : list cell) (nv : word) (post : list cell) (m : word -> option byte),
rw_cells rsegs m B (pre ++ C4 nv :: post) -> A = B + Z.of_nat (cells_size pre) -> 0 < B -> A + 4 <= 2^64 -> A mod 4 = 0 -> mem_inv rsegs m ->
evt rsegs (vutf8_postF rsegs (Z_to_bv 64 A) A B pre post m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (zxb c) (Z_to_bv 64 A) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 validate_utf8_entry_P) fc None m (seg_rom rsegs)).
Proof.
intros c a2 a3 A B pre nv post m FR HA HB HA4 HAL MI.
assert (NB : rw_cells rsegs m A [C4 nv]).
{ apply rw_cells_app in FR as [_ FR2]. change (C4 nv :: post) with ([C4 nv] ++ post) in FR2. apply rw_cells_app in FR2 as [FR2 _]. rewrite HA. exact FR2. }
eapply evt_mono; [apply (validate_utf8_P c a2 a3 A nv m NB ltac:(lia) HA4 HAL MI) |].
intros ms' P. eapply vutf8_frame; [exact FR | exact HA | exact P].
Qed.

End Regs.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek.
Import UC8c.Mq0 UC8c.
Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PutStmt.
Variable L : heap_layout.
Variable HIx : heap_iface L.
Variable fn : fnaddrs.
Variable put_entry : Z.
Variable put_stk : Z.
Notation segs := (hl_segs L).

Definition put_pre (s : option jshape) (m : word -> option byte) (BS : list blk) (p rc : Z) : Prop :=
match s with
| None => p = 0 /\ BS = []
| Some s' => p <> 0 /\ 1 <= rc < 2^31 /\ jval segs fn s' m BS p rc
end.

Definition put_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z) (errv : word)
(s : option jshape) (BS : list blk) (p rc : Z)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS L HIx) (r : word),
ret_statew L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' /\
model_vm_only md md' /\
stk segs m' lo (bv_unsigned sp) /\
heap_pres L LB (bv_unsigned sp) m m' /\
rw_cells segs m' (hl_tp L - 164) [C4 errv] /\
( ((s = None \/ rc = 1) /\ HEAP L HIx A' LB m' md')
\/ (exists s', s = Some s' /\ 2 <= rc /\ jval segs fn s' m' BS p (rc - 1) /\ HEAP L HIx A' (BS ++ LB) m' md') ).

Definition put_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS L HIx) (LB : list blk) (lo : Z) (errv : word)
(s : option jshape) (BS : list blk) (p rc : Z),
HEAP L HIx A (BS ++ LB) m md ->
put_pre s m BS p rc ->
a0 = Z_to_bv 64 p ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - put_stk ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top L HIx ->
rw_cells segs m (hl_tp L - 164) [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) ->
bv_unsigned ra mod 2 = 0 ->
(forall ms' md', put_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo errv s BS p rc ms' md' ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 put_entry) fc None m (seg_rom segs)) md) T.
End PutStmt.

Definition put_stk_P : Z := 112 + 48 + 48 + 32 + 32 + 8256.
Definition put_entry_P : Z := 0x24654.
Definition put_stmt_P (HIx : heap_iface S4L) : Prop := put_stmt S4L HIx S4F put_entry_P put_stk_P.

End RC__1.
End Mq4.
