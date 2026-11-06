(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia Bool.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH Q0Ek Qtgi QkMG QsKa Q4v2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import QCcH Q0Ek Qtgi QkMG.
Import QsKa.Mq4 Q4v2.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Definition obj_capA (BS : list blk) : Z := snd (nth 2 BS (0, 0)) / 40.

Definition K_arr : Z := 1280.
Definition RA : Z := 1024.
Definition K_open_arr : Z := 8960.
Definition K_obj : Z := 3904.
Definition K_open_obj : Z := 15488.
Definition K_pb : Z := 48.
Definition K_free : Z := 512.
Definition K_tot : Z := 6656.
Definition K0 : Z := 332968.
Definition K_exit : Z := 20480.

Definition PhiA (cap len : Z) : Z := 768 * len - 256 * cap + 8192.
Definition PhiO (cap cnt : Z) : Z := 3904 * cnt - 1280 * cap + 20480.

Definition PhiPB (len cap : Z) : Z := 48 * (2 * len + 50) + 512 - 48 * cap.
Definition pb_inv (cap co : Z) : Prop := 32 <= cap /\ (cap = 32 \/ cap <= 2 * co + 18).

Definition phi_level (l : tlevel) : Z :=
match tl_cs l with
| Some (Sarr kids) => PhiA (arr_capA (tl_cbs l)) (Z.of_nat (length kids)) + RA
| Some (Sobj kids) => PhiO (obj_capA (tl_cbs l)) (Z.of_nat (length kids))
| _ => 0
end.

Fixpoint ledger_levels (levels : list tlevel) (n : nat) : Z :=
match n, levels with
| O, _ => 0
| S n', l :: rest => phi_level l + ledger_levels rest n'
| S _, [] => 0
end.

Definition pb_capA (pbs : list blk) : Z := snd (nth 1 pbs (0, 0)).

Definition pe_needB (len rem : Z) (levels : list tlevel) (depth : nat) (pbs : list blk) (nblk : Z) : Z :=
K_tot * rem + ledger_levels levels (S depth) + PhiPB len (pb_capA pbs) + K_free * nblk + K_exit.

Definition pe_needD (rem : Z) : Z := rem.

Definition arr_inv (cap len : Z) : Prop := 32 <= cap /\ 0 <= len <= cap /\ (cap = 32 \/ cap <= 2 * len).

Lemma potential_step_arr_add : forall cap len cap',
arr_inv cap len -> arr_grownA cap len cap' ->
PhiA cap len + RA + K_arr >= arr_add_costA cap len + (PhiA cap' (len + 1) + RA) /\ arr_inv cap' (len + 1).
Proof.
intros cap len cap' (H32 & Hl & Hi) G. unfold PhiA, RA, K_arr, arr_add_costA, arr_grownA, arr_inv in *.
destruct G as [[-> Hlt] | [-> Hge]].
- replace (len + 1 <? cap) with true by (symmetry; apply Z.ltb_lt; lia). lia.
- replace (len + 1 <? cap) with false by (symmetry; apply Z.ltb_ge; lia). lia.
Qed.

Lemma potential_step_arr_close : forall cap len,
arr_inv cap len -> PhiA cap len + RA >= arr_shrink_costA cap len.
Proof.
intros cap len (H32 & Hl & Hcap). unfold PhiA, RA, arr_shrink_costA.
destruct (len =? cap) eqn:E; [lia|]. apply Z.eqb_neq in E.
destruct (Z.max_spec len 1) as [[_ ->] | [_ ->]]; lia.
Qed.

Lemma arr_inv_new : arr_inv 32 0.
Proof. unfold arr_inv. lia. Qed.

Lemma pb_inv_mono : forall cap co co', pb_inv cap co -> co <= co' -> pb_inv cap co'.
Proof. intros cap co co' [A B] H. split; lia. Qed.

End Mq0.
From Stdlib Require NArith.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply Q5Rg QRjH QHnV QfLs Qsw7 QJjn QRUw Q8tj QSL3 Q22i Q6us Q7UD Qhd4 Qwm6 QlKV Q30W Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw Q8tj.
Import QSL3. Import Q22i Q6us.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QsKa.Mq5 Q30W.Mq3.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section ProbeA.
Variables (sp gp tp : word) (s2 s3 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (t tbl size k v opts : Z) (svs : list slotv).
Notation SB0 := 2147450880.

Definition ins_regsA (x1 x6 x7 : word) (a1 : word) (a3 : Z) (n : Z) (t0v : Z) :=
mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp (Z_to_bv 64 t0v) x6 x7 (Z_to_bv 64 (t + 4)) (Z_to_bv 64 k)
(Z_to_bv 64 t) a1 (Z_to_bv 64 v) (Z_to_bv 64 a3) (Z_to_bv 64 opts) (Z_to_bv 64 tbl) (Z_to_bv 64 n) (Z_to_bv 64 size)
s2 s3 (Z_to_bv 64 SB0) (Z_to_bv 64 (t / 8 + SB0)) (Z_to_bv 64 (t / 8 + SB0)) s7 s8 s9 s10 s11.

Lemma lh_probe_loopA :
forall (d : nat) (n f : Z) (x1 x6 x7 a1 x28 x29 x30 x31 : word) (m : word -> option byte) (sf : slotv),
Z.of_nat d = (f - n) mod size ->
0 <= n < size -> 0 <= f < size -> In size lf_sizes -> Z.of_nat (length svs) = size ->
nth_error svs (Z.to_nat f) = Some sf -> is_free sf ->
(forall i s, nth_error svs i = Some s -> ~ is_free s -> 0 <= sv_k s < LH_FREEDv) ->
(exists sn, nth_error svs (Z.to_nat n) = Some sn /\ ~ is_free sn) ->
0 <= tbl -> tbl + 40 * size <= alloc_ceiling -> tbl mod 8 = 0 ->
bytes_at asegs m (tbl / 8 + A_SB) (repeat (Z_to_bv 8 0) (Z.to_nat (5 * size))) -> tbl / 8 + A_SB + 5 * size <= alloc_ceiling ->
mem_inv asegs m -> lh_slots asegs m tbl svs ->
evt asegs (fun ms' => exists (g : Z) (sg : slotv),
0 <= g < size /\ nth_error svs (Z.to_nat g) = Some sg /\ is_free sg /\
ms' = MS (ins_regsA x1 (Z_to_bv 64 (sv_k sg)) x7 (Z_to_bv 64 (tbl + g * 40)) 40 g (-2) x28 x29 x30 x31)
F (Z_to_bv 64 0xa2488) fc None m (seg_rom asegs))
(MS (ins_regsA x1 x6 x7 a1 40 n (-2) x28 x29 x30 x31)
F (Z_to_bv 64 0xa2450) fc None m (seg_rom asegs)).
Proof.
induction d as [|d IH]; intros until sf; intros Hd Hn Hf Hsz Hlen Esf FREE LIVEK (sn & Esn & NSN) Ht0 Htb Hal TSH TSHhi MI SL.
- exfalso. assert (f = n) by (apply (moddist_zero n f size); lia). subst f.
rewrite Esf in Esn. injection Esn as ->. exact (NSN FREE).
- assert (NE : n <> f) by (intros ->; rewrite Esf in Esn; injection Esn as ->; exact (NSN FREE)).
pose proof (moddist_step n f size Hn Hf NE) as STEP.
pose proof (lf_size_range size Hsz) as HSR. word_range sp SPR. unfold_consts. unfold A_SB in *.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold ins_regsA.
step. step. norm_w32. step. rewrite ?(unsigned_lit size), ?(unsigned_lit (n + 1)) by lia.

eapply evt_cut with (P := eq (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp (Z_to_bv 64 (-2)) x6 x7 (Z_to_bv 64 (t + 4)) (Z_to_bv 64 k)
(Z_to_bv 64 t) (Z_to_bv 64 (n + 1)) (Z_to_bv 64 v) (Z_to_bv 64 40) (Z_to_bv 64 opts) (Z_to_bv 64 tbl) (Z_to_bv 64 (next_ix size n)) (Z_to_bv 64 size)
s2 s3 (Z_to_bv 64 SB0) (Z_to_bv 64 (t / 8 + SB0)) (Z_to_bv 64 (t / 8 + SB0)) s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 0xa2468) fc None m (seg_rom asegs))).
{ unfold next_ix. destruct (Z.eqb_spec (n + 1) size) as [EQ|NEQ].
- rewrite <- EQ, Z.lxor_nilpotent. step. rewrite (v_sltiu_1 (Z_to_bv 64 0) 1) by (rewrite ?unsigned_lit by lia; lia).
step. step. rewrite (unsigned_lit (n + 1)) by lia. rewrite Z.land_0_l. apply evt_done. reflexivity.
- pose proof (lxor_bound size (n + 1) 31 ltac:(lia) ltac:(lia) ltac:(lia)) as LB.
assert (LNZ : Z.lxor size (n + 1) <> 0) by (intros X; apply Z.lxor_eq in X; lia).
step. rewrite (v_sltiu_0 (Z_to_bv 64 (Z.lxor size (n + 1))) 1) by (rewrite ?unsigned_lit by lia; lia).
step. step. change (bv_unsigned (Z_to_bv 64 (0 + -1))) with 18446744073709551615.
rewrite (unsigned_lit (n + 1)) by lia. rewrite land_ones64_l by lia. apply evt_done. reflexivity. }
intros ms' <-.
assert (Hn' : 0 <= next_ix size n < size) by (unfold next_ix; destruct (Z.eqb_spec (n + 1) size); lia).
destruct (nth_error svs (Z.to_nat (next_ix size n))) as [sn'|] eqn:Esn'.
2:{ exfalso. apply nth_error_None in Esn'. lia. }
pose proof (SL _ _ Esn') as C. unfold ent_addr, slot_cells in C. rewrite Z2Nat.id in C by lia.

pose proof (bytes_at_repeat_sub asegs m _ _ _ (Z.to_nat (5 * next_ix size n)) 1 TSH ltac:(lia)) as SH1.
apply ro_cells_of_repeat in SH1. cbn [map repeat] in SH1. rewrite Z2Nat.id in SH1 by lia.
step. rewrite (unsigned_lit (next_ix size n)) by lia. step.
replace (tbl + next_ix size n * 40) with (tbl + 40 * next_ix size n) by lia.
remember (tbl + 40 * next_ix size n) as B eqn:EB.
assert (EB8 : B mod 8 = 0) by (subst B; Z.div_mod_to_equations; lia).
replace (tbl / 8 + SB0 + 5 * next_ix size n) with (B / 8 + SB0) in SH1 by (subst B; Z.div_mod_to_equations; lia).
step. step. sh_norm. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false.
step. subst B.
step. unfold bv_ltu. change (bv_unsigned (Z_to_bv 64 (-2))) with 18446744073709551614.
assert (FD : is_free sn' \/ ~ is_free sn').
{ unfold is_free. destruct (Z.eq_dec (sv_k sn') LH_EMPTYv); [left; left; assumption|].
destruct (Z.eq_dec (sv_k sn') LH_FREEDv); [left; right; assumption|]. right. intros [X|X]; contradiction. }
destruct FD as [FR' | NF].
+
assert (HK : sv_k sn' = LH_EMPTYv \/ sv_k sn' = LH_FREEDv) by exact FR'. unfold LH_EMPTYv, LH_FREEDv in HK.
rewrite (unsigned_lit (sv_k sn')) by lia. if_false.
apply evt_done. exists (next_ix size n), sn'. split; [exact Hn'|]. split; [exact Esn'|]. split; [exact FR'|].
unfold ins_regsA. replace (tbl + 40 * next_ix size n) with (tbl + next_ix size n * 40) by lia. reflexivity.
+
pose proof (LIVEK _ _ Esn' NF) as HK. unfold LH_FREEDv in HK.
rewrite (unsigned_lit (sv_k sn')) by lia. if_true.
eapply (IH (next_ix size n) f); first [exact Esf | exact FREE | exact LIVEK | exact MI | exact SL | exact Hsz | exact Hlen | exact TSH | lia | idtac].
exists sn'. split; [exact Esn' | exact NF].
Qed.
End ProbeA.
End RC__1.
End Mq1.
From Stdlib Require Permutation.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH QmZZ QTEu QKQo Q6WR QnDr QJZd QW22 QI6Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ. Import QTEu. Import Qsw7 QJjn QRUw QKQo Q8tj.
Import QSL3.
Import Q6WR Q6WR.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mq7 QlKV.Mqa QsKa.Mq7 QsKa.Mq3 QsKa.Mq5 Q30W.Mq2 QnDr.Mq0 QJZd.Mq4 QW22 QnDr.Mq1 QI6Z.Mq1.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Ltac post_callS segs m :=
let ms' := fresh "ms'" in let PO := fresh "POST" in
intros ms' PO;
destruct_exs PO;
let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
destruct PO as [E [MUc [WMc PO]]];
first [ destruct PO as [MIc PO] | rename PO into MIc ];
destruct_exs E;
subst ms';
rewrite ?unsigned_lit in MUc by lia; try rewrite ?unsigned_lit in PO by lia;
lazymatch type of MUc with
| munch _ m ?m' =>
transport_after_call segs m m' MUc WMc;
clear MUc WMc;
try match goal with H : mem_inv segs m |- _ => clear H end;
try clear m
end;
try destruct_ands PO;
try (lazymatch goal with
| |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
end).
Tactic Notation "callS" uconstr(SPEC) :=
lazymatch goal with
| |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | post_callS segs m ]
end.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section MF5.
Variable HIx : heap_iface_A A4L.

Lemma mf_objA : mf_objA_stmt HIx.
Proof.
unfold mf_objA_stmt.
intros ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo errv s BS x rc T kids.
intros until junk8. intros Hs HP J FR ST LO LOS SPA HT ERR RA VM0 HPR FS FRM Hrc BD BB0 BB K.
pose proof FR as FR0. unfold mf_frameA in FR. unfold_consts. unfold A_SB, A_TP, A_ERRNO in *. word_range sp SPR. subst s.
destruct (jval_obj_open asegs A4F kids m BS x 0 J) as (pb & PBS & t & TBS & kvs & KBS & EBS & OPB & HDR & LT & OK). clear J.
pose proof LT as (tbl & size & es & svs & Ekvs & ETBS & OPEN). subst TBS.
pose proof OPEN as (_ & _ & _ & _ & Hsz & Hcnt & Hlen).
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
rewrite EBS, <- app_assoc in HP. unfold lh_blocks in HP. cbn [app] in HP. rewrite <- app_assoc in HP. cbn [app] in HP.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP) as [HB00 HD00].
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
blk_factsA A4L HIx HP x 48 Hxal Hxlo Hxhi Hximg.
blk_factsA A4L HIx HP t 56 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP tbl (40 * size) Hbal Hblo Hbhi Himg_b.
shadow_nowA A4L HIx HP x 48 SHx.
shadow_nowA A4L HIx HP t 56 SHt.
a4l.
destruct (proj1 (ro_cells_app asegs m (t / 8 + 2147450880) [C1 (Z_to_bv 8 0)] _) SHt) as [SHt0 _]. clear SHt.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(lo, bv_unsigned sp + -48)] m) as MU.
pose proof HDR as HDR0. unfold jhdr_cells in HDR. cbn [app fn_obj_to_json_string A4F] in HDR.
pose proof (okids_len _ _ _ _ _ _ OK) as [L1 L2]. rewrite length_map in L1.
assert (LK : length kvs = length es) by (rewrite Ekvs; apply length_map).
rewrite EBS in BB. unfold lh_blocks in BB. cbn [concat app] in BB. rewrite ?length_app in BB. cbn [length] in BB.
rewrite ?length_app, ?length_map in BB. rewrite ?Nat2Z.inj_succ, ?Nat2Z.inj_add in BB.
stash OPB. stash OK. stash HDR0. stash OPEN.
reenterA asegs A4L HIx asegs_wx HP.
asan_chk0.
step. norm_w32. step. step. if_falsex. step. step. if_falsex. step. step. if_falsex.
step. step. if_true.
asan_chkA.
step. step.

unstash OPEN.
callS (lh_table_length_A _ (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 6434400) t0 t1 t2 (Z_to_bv 64 x) (Z_to_bv 64 (x + 40)) (Z_to_bv 64 4) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 2147450880) (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F1 fc1
m lo _ (lh_blocks t tbl size es) t kvs).
all: try (unfold small_pre; rewrite ?unsigned_lit by lia; split; [exact MI|]; split; [exact ST|]; split; [lia|]; split; [lia|]; split; [exact GOT|]; split; [exact CELL|]; lia).
all: try (exists tbl, size, es, svs; split; [exact Ekvs|]; split; [reflexivity | exact OPEN]).
all: try first [exact SHt0 | reflexivity | lia].
all: try (unfold A_SB; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia).
stash OPEN.
step.
destruct kids as [|k0 kids1].
- destruct kvs as [|kv kvs1]; [| cbn in L1; discriminate]. destruct KBS as [|bs KBS1]; [| cbn in L2; discriminate].
destruct es as [|e0 es1]; [| cbn in LK; discriminate].
cbn [length Z.of_nat]. if_true.
asan_chkA.
step. step.
cbn [concat app map] in HP.
unstash OPB. unstash OK. unstash HDR0. unstash OPEN.

evt_done5.
lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (lh_table_free_A_cps HIx _ gp s5 s6 s7 s8 s9 s10 s11 F1 fc1 mc md ((x, 48) :: PBS ++ LB) LM FRS B lo t tbl size [] svs T)
with (u := UWptr)
end.
all: a4l_goal; rewrite ?unsigned_lit by lia.
all: try (lazymatch goal with Hmi : mem_inv asegs ?mc |- HEAPA _ _ _ _ _ _ _ ?mc _ =>
eapply (heapA_perm A4L HIx); [heap_nowA A4L HIx HP MU WM Hmi | unfold lh_blocks; cbn [map app]; perm | apply Permutation_refl | apply Permutation_refl] end).
all: try (apply uw_at_ptr; lia).
all: try (cbn [uw_ok uw_key]; unfold a4_straces; repeat first [left; reflexivity | right]).
all: try (eapply (lh_open_agree asegs A4F); [exact OPEN | eapply (agree_of_munch asegs); [exact MU | exact WM |] | apply incl_refl];
intros b k Hb; unfold lh_blocks in Hb; cbn in Hb; cbn; destruct Hb as [Hb | [Hb | Hb]]; [injection Hb as <- <- | injection Hb as <- <- | destruct Hb]; lia).
all: try (lazymatch goal with |- forall e, In e [] -> _ => intros e He; destruct He end).
all: try (replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) by lia; rewrite Zminus_mod, SPA; reflexivity).
all: try (cbn [uw_cost length Z.of_nat Z.add]; lia).
all: try first [eassumption | reflexivity | lia].
intros ms4 md4 A4 (m4 & r4 & B4 & RS4 & VM4 & ST4 & HPR4 & ERR4 & BB4 & BD4 & HP4).
destruct RS4 as (w0 & w1 & w2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & w3 & w4 & w5 & w6 & F4 & fc4 & -> & FS4 & FRM4).
a4l. rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in ST4 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in HPR4 by lia.
lazymatch type of MU with munch _ m ?mc =>
assert (HPRc : heap_pres A4H (((x, 48) :: PBS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -48) m mc)
by (eapply (heap_pres_of_munch A4H _ (bv_unsigned sp + -48)); [exact MU | exact WM |];
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; cbn in Hb |- *; destruct Hb as [Hb|Hb]; [left; exact Hb | right; right; right; exact Hb] | clia | apply Forall_cons; [cbn; left; lia | apply Forall_nil]]);
pose proof (heap_pres_trans _ _ _ _ _ _ HPRc HPR4) as HPR4m
end.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in FR; [| left; cbn; lia].
first [ apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in HDR0; [| eapply client_range_block; [apply in_or_app; left; left; reflexivity | lia | cbn; lia]]
| apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4m) in HDR0; [| eapply client_range_block; [apply in_or_app; left; left; reflexivity | lia | cbn; lia]] ].
assert (OPB4 : opt_pbuf asegs m4 PBS pb).
{ eapply opt_pbuf_agree; [exact OPB | | apply incl_refl].
eapply (agree_of_heap_pres asegs A4H); [exact HPR4m | reflexivity | intros b Hb; apply in_or_app; left; right; apply in_or_app; left; exact Hb]. }
assert (HPRb : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m4).
{ eapply heap_pres_trans; [exact HPR|].
eapply heap_pres_weaken; [exact HPR4m | lia | intros b Hb; cbn; right; apply in_or_app; apply in_app_or in Hb; destruct Hb; [left; apply in_or_app; right; assumption | right; assumption]]. }
clear MU WM.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI4. a4l.
pose proof (munch_refl [] m4) as MU. pose proof (wmono_refl asegs m4) as WM.
reenterA asegs A4L HIx asegs_wx HP4.
step.
evt_done5.
eapply (mf_genA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo errv (Sobj []) BS x rc T);
[ exact HP4 | lia | exact HDR0 | exact OPB4 | exact FR | exact ST4 | clia | clia | exact SPA | exact HT
| exact ERR4 | exact RA | eapply model_vm_only_trans; [exact VM0 | exact VM4] | exact HPRb
| eapply fsaved_trans; [exact FS | exact FS4] | intros Hf; exact (FRM4 (FRM Hf)) | exact Hrc
| cbn [bD charge uw_cost] in *; lia
| clear - EBS BB BB0 BB4 HB00; subst BS; cbn [concat app length map lh_blocks] in *; unfold blk in *; lia
| clear - BB BB4 HB00; cbn [length Z.of_nat Z.add concat] in *; unfold blk in *; lia | exact K ].
- cbn [length] in L1. rewrite L1. if_falsex.
step. step.
do 6 step. lazymatch goal with STx : stk asegs _ lo (bv_unsigned sp + -48) |- _ => release_frame FR STx (bv_unsigned sp) end. step.
unstash OPB. unstash OK. unstash HDR0. unstash OPEN.
evt_done5. apply K. unfold mf_postA.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, 2, B end.
lazymatch goal with MUx : munch _ m ?mf, WMx : wmono asegs m ?mf |- _ =>
assert (AG : agree_on asegs BS m mf)
by (eapply (agree_of_munch asegs); [exact MUx | exact WMx |]; intros b k Hb; cbn;
rewrite EBS in Hb; unfold lh_blocks in Hb;
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ b k HP ltac:(in_sub Hb)) as (Hk & _ & Hqlo & Hqhi & _);
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hqhi; lia)
end.
split; [apply ret_statew_intro; [exact FS | exact FRM] |].
split; [exact VM0|]. split; [assumption|].
split.
{ eapply heap_pres_trans; [exact HPR |]. lazymatch goal with MUx : munch _ m ?mf, WMx : wmono asegs m ?mf |- _ =>
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MUx | exact WMx |] end.
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; in_sub Hb | clia | apply Forall_cons; [cbn; left; lia | apply Forall_nil]]. }
split; [assumption|]. split; [lia|].
right; right. split; [reflexivity|]. split; [exact Hrc|]. split; [| split; [lia|]].
+ split; [discriminate|]. exists t, tbl, size, es, svs. exists pb, PBS, KBS, es, (@nil lent).
split; [rewrite app_nil_r; reflexivity|]. split; [reflexivity|]. split; [apply Forall_nil|].
split; [rewrite EBS; reflexivity|]. split; [eapply opt_pbuf_agree; [exact OPB | exact AG | rewrite EBS; unfold lh_blocks; intros b Hb; in_sub Hb]|].
split; [eapply (rw_cells_agree asegs); [exact HDR0 | exact AG | exists x, 48; split; [rewrite EBS; left; reflexivity | cbn; lia]]|].
split; [eapply (lh_open_agree asegs A4F); [exact OPEN | exact AG | rewrite EBS; unfold lh_blocks; intros b Hb; in_sub Hb]|].
replace (map le_v es) with (map snd kvs); [eapply okids_agree; [exact OK | exact AG | rewrite EBS; intros b Hb; in_sub Hb]|].
rewrite Ekvs, map_map. reflexivity.
+ rewrite EBS, <- app_assoc in *. unfold lh_blocks in *. cbn [app] in *. rewrite <- app_assoc in *. cbn [app] in *.
eapply (heapA_client_frame A4L HIx); [exact HP | | assumption | assumption].
lazymatch goal with MUx : munch _ m ?mf |- _ => eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MUx); apply Forall_cons; [cbn; left; lia | apply Forall_nil] end.
Qed.

Definition maybe_free_A_closed := maybe_free_A_cps HIx mf_objA.
End MF5.
End RC__1.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QT7i QpNt QgoM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0. Import QT7i.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq7 QpNt.Mq4 QgoM.Mq1 Q4v2.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section APbMemappendMain.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud) (lo : Z) (pb n : Z) (T : TSet).

Lemma memappend_A_rebase :
forall (buf0 bpos0 cap0 : Z) (content0 : list byte) (xra t0 t1 t2 a3 a4 a5 a6 a7 x18 x19 x25 x26 x27 t3 t4 t5 t6 : word)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(obuf ocap buf bpos cap b : Z) (content src : list byte) (errv : word) (fjunk : list byte),
HEAPAx A ((pb, PB_SZ) :: (buf, cap) :: LB) LM FRS B m md ->
pbufx m pb buf bpos cap content ->
bpos + n + 1 <= cap -> 0 <= n < 2^31 ->
bytes_at asegs m b src -> Z.of_nat (length src) = n -> 0 <= b -> b + n <= alloc_ceiling ->
(0 < n -> unpoisoned asegs m A_SB b n) -> (n <= 64 \/ app_mem b n) ->
(b + n <= buf \/ buf + cap <= b) ->
(b + n <= obuf \/ obuf + ocap <= b) -> 0 <= obuf -> obuf + ocap <= 2^64 -> 0 < ocap < 2^31 ->
stk asegs m lo (bv_unsigned sp + -112) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -112 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m (bv_unsigned sp + -112) [CB 8 fjunk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs m A_ERRNO [C4 errv] ->
bv_unsigned ra mod 2 = 0 ->
model_vm_only (cfg_model md0) (cfg_model md) -> heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m ->
bB B0 - memappend_costX2 cap0 bpos0 n <= bB B -> bD B0 <= bD B ->
cap = memappend_cap2 cap0 bpos0 n ->
bpos = bpos0 -> firstn (Z.to_nat bpos) content = firstn (Z.to_nat bpos0) content0 ->
(forall ms' md' A', memappend_A_post_c HIx ra sp gp (Z_to_bv 64 A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 pb buf0 bpos0 cap0 content0 src n lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pb + 8)) (Z_to_bv 64 (pb + 12))
(Z_to_bv 64 pb) (Z_to_bv 64 b) (Z_to_bv 64 n) a3 a4 a5 a6 a7
(Z_to_bv 64 obuf) x19 (Z_to_bv 64 A_SB) (Z_to_bv 64 (pb / 8 + 1 + A_SB)) (Z_to_bv 64 (pb / 8)) (Z_to_bv 64 (pb / 8 + A_SB)) (Z_to_bv 64 ocap) x25 x26 x27 t3 t4 t5 t6)
F (Z_to_bv 64 0x9a218) fc None m (seg_rom asegs)).
Proof.
intros buf0 bpos0 cap0 content0. intros until fjunk.
intros HP PBX ROOM Hn SRC SRCL Hb0 Hbn UPS AMS BSEP OSEP Ob0 Obn Ocap ST LO LOS SPA HT FR ERR RA VM0 HPR BB BD CAPE Ebpos Epre K.
unfold_consts. unfold A_SB, A_TP, A_ERRNO in *. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
reenterA asegs A4L HIx asegs_wx HP.
step. step. step. step. step. step. step. step.
rewrite (unsigned_lit b) by lia. rewrite (unsigned_lit obuf) by lia.
destruct PBX as (Hbp & Hcap & Hlen & PBS & PBUF).
destruct (Z.eq_dec b obuf) as [Eb|Nb].
-
assert (Hn0 : n = 0) by lia. subst b.
rewrite (v_sltu_0 (Z_to_bv 64 obuf) (Z_to_bv 64 obuf)) by lia.
replace (obuf - obuf) with 0 by lia.
rewrite (v_sltu_1 (Z_to_bv 64 0) (Z_to_bv 64 ocap)) by (rewrite !unsigned_lit by lia; lia).
match goal with |- context [Z_to_bv 64 (bv_swrap 32 ?e)] => let v := eval vm_compute in (bv_swrap 32 e) in change (bv_swrap 32 e) with v end.
step. if_falsex.
blk_factsA A4L HIx HP pb 16 Hal Hlo Hhi Himg.
shadow_nowA A4L HIx HP pb 16 SHpb. a4l.
step. step. if_false. rewrite ?zxb_zero.
clear SHpb.
step. step.
try replace (buf + 0) with buf by lia.
assert (src = []) as -> by (destruct src; [reflexivity | cbn in SRCL; lia]).
blk_factsA A4L HIx HP buf cap Hbal Hblo Hbhi Hbimg.
evt_done5.
replace (Z_to_bv 64 (pb / 8 + 2147450881)) with (Z_to_bv 64 (pb / 8 + 1 + 2147450880)) by (f_equal; lia).
eapply (memappend_A_tail HIx ra sp gp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo pb buf0 bpos0 cap0 n content0 T s0
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m md A B buf bpos cap buf content [] errv fjunk);
first [ reflexivity | eassumption | lia | idtac ].
all: try (unfold pbufx, pbuf_core; repeat (split; [first [lia | eassumption] |]); eassumption).
all: try (apply bytes_at_nil; unfold_consts; lia).
all: try (intros Hpos; exfalso; lia).
all: try (left; lia).
all: try (unfold_consts; lia).
-
match goal with |- context [Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 ?v) + 0))] =>
replace (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 v) + 0))) with (Z_to_bv 64 (-1)) end.
2:{ assert (Hv : forall v, v = 18446744073709551615 -> Z_to_bv 64 (-1) = Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 v) + 0))).
{ intros v ->. rewrite (unsigned_lit 18446744073709551615) by lia.
replace (18446744073709551615 + 0) with (-1 + 4294967296 * 4294967296) by lia.
rewrite swrap32_shift, swrap32_id by lia. reflexivity. }
apply Hv. clear Hv.
pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 (b - obuf))) as R1. unfold bv_modulus in R1. cbn in R1.
destruct (Z.lt_ge_cases b obuf) as [Hlt|Hge].
- rewrite (v_sltu_1 (Z_to_bv 64 b) (Z_to_bv 64 obuf)) by (rewrite (unsigned_lit b) by lia; rewrite (unsigned_lit obuf) by lia; lia).
rewrite (unsigned_lit 1) by lia. rewrite (swrap32_id (0 - 1)) by lia. change (0 - 1) with (-1). rewrite unsigned_m1.
rewrite lor_ones64_l by lia. rewrite (unsigned_lit 18446744073709551615) by lia.
rewrite lor_ones64_l; [reflexivity|].
match goal with |- 0 <= bv_unsigned ?w < _ => pose proof (bv_unsigned_in_range 64 w) as R2; unfold bv_modulus in R2; cbn in R2; lia end.
- assert (obuf + ocap <= b) by lia.
rewrite (v_sltu_0 (Z_to_bv 64 b) (Z_to_bv 64 obuf)) by (rewrite (unsigned_lit b) by lia; rewrite (unsigned_lit obuf) by lia; lia).
rewrite (unsigned_lit 0) by lia. rewrite (swrap32_id (0 - 0)) by lia. change (0 - 0) with 0. rewrite (unsigned_lit 0) by lia.
rewrite (unsigned_lit (b - obuf)) by lia. rewrite Z.lor_0_l.
rewrite (v_sltu_0 (Z_to_bv 64 (b - obuf)) (Z_to_bv 64 ocap)) by (rewrite (unsigned_lit (b - obuf)) by lia; rewrite (unsigned_lit ocap) by lia; lia).
rewrite (unsigned_lit 0) by lia. change (0 + -1) with (-1). rewrite unsigned_m1.
rewrite (unsigned_lit (b - obuf)) by lia. rewrite lor_ones64_r by lia. reflexivity. }
step. if_truex.
blk_factsA A4L HIx HP buf cap Hbal Hblo Hbhi Hbimg.
replace (Z_to_bv 64 (pb / 8 + 2147450881)) with (Z_to_bv 64 (pb / 8 + 1 + 2147450880)) by (f_equal; lia).
evt_done5.
eapply (memappend_A_tail HIx ra sp gp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo pb buf0 bpos0 cap0 n content0 T s0
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m md A B buf bpos cap b content src errv fjunk);
first [ reflexivity | eassumption | lia | idtac ].
all: first [ unfold pbufx, pbuf_core; repeat (split; [first [lia | eassumption] |]); eassumption | unfold_consts; lia ].
Qed.
End APbMemappendMain.
End RC__1.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrPc QeuE QkXq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn QKQo Q8tj.
Import QSL3.
Import Q6WR Q6WR.Mq0 QrPc. Import QeuE.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QkXq.Mq3.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section Loop2A.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Variables (sp gp : word) (lo : Z) (errv : word) (LM : list blk) (FRS : list frame).

Notation SPR := (Z_to_bv 64 (bv_unsigned sp + -112)).
Notation TP := (Z_to_bv 64 6434400).
Notation SBR := (Z_to_bv 64 2147450880).
Notation CM1 := (Z_to_bv 64 18446744073709551615).
Notation ERRNO := (6434400 - 164).
Notation NEXT := (next_postA HIx sp gp lo errv LM FRS).

Definition tyof (isobj : bool) : Z := if isobj then 4 else 5.

Definition zhead (isobj : bool) (m : word -> option byte) (x q : Z) (kids : list (option jshape)) (XBS : list blk) : Prop :=
if isobj then zobjc asegs A4F m x q kids XBS else zarrc asegs A4F m x q kids XBS.

Definition head_stmtA (isobj : bool) (kids : list (option jshape)) : Prop :=
forall (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x25 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (LB XBS : list blk) (x q : Z) (T : TSet),
HEAPAx A (XBS ++ LB) LM FRS B m md ->
zhead isobj m x q kids XBS ->
stk asegs m lo (bv_unsigned sp + -112) -> rw_cells asegs m ERRNO [C4 errv] ->
512 * Z.of_nat (length XBS) <= bB B ->
(forall ms' md' A', NEXT q F1 fc1 m md LB B (512 * Z.of_nat (length XBS)) ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR x1 SPR gp TP t0 t1 t2 (Z_to_bv 64 x) x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 SBR (Z_to_bv 64 4) x25 (Z_to_bv 64 5) CM1 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x9a810) fc1 None m (seg_rom asegs)).

Definition desc_stmtA (c : jshape) : Prop :=
match c with Sobj kids => head_stmtA true kids | Sarr kids => head_stmtA false kids | _ => True end.
Definition desc_optA (k : option jshape) : Prop := match k with Some c => desc_stmtA c | None => True end.
Definition kids_descA (kids : list (option jshape)) : Prop := forall k, In k kids -> desc_optA k.

Definition zcont (isobj : bool) (m : word -> option byte) (x q : Z) (kids : list (option jshape)) (nz : nat) (cur : Z) (XBS : list blk) : Prop :=
if isobj then exists t tbl size es svs, zobj asegs A4F m x q kids nz t tbl size es svs XBS /\
(forall kids1 kl, kids = kids1 ++ [kl] -> exists e, nth_error es (length kids1) = Some e /\ cur = ent_addr tbl (le_ix e))
else exists a arr size, zarr asegs A4F m x q kids nz a arr size XBS.

Definition cont_stmtA (isobj : bool) (kids : list (option jshape)) : Prop :=
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (LB XBS : list blk) (x q : Z) (T : TSet) (nz : nat) (cur : Z),
HEAPAx A (XBS ++ LB) LM FRS B m md ->
zcont isobj m x q kids nz cur XBS ->
stk asegs m lo (bv_unsigned sp + -112) -> rw_cells asegs m ERRNO [C4 errv] ->
512 * Z.of_nat (length XBS) <= bB B ->
(forall ms' md' A', NEXT q F1 fc1 m md LB B (512 * Z.of_nat (length XBS)) ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR x1 SPR gp TP t0 t1 t2 (Z_to_bv 64 x) (Z_to_bv 64 (x + 40)) a0 a1 a2 a3 a4 a5 a6 a7
x18 (Z_to_bv 64 cur) (Z_to_bv 64 (Z.of_nat (length kids))) (Z_to_bv 64 (Z.of_nat nz))
(Z_to_bv 64 (x / 8 + 2147450885)) SBR (Z_to_bv 64 4) (Z_to_bv 64 (x / 8 + 2147450880)) (Z_to_bv 64 5) CM1 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x9a888) fc1 None m (seg_rom asegs)).

Definition zbodyp (isobj : bool) (m : word -> option byte) (x q : Z) (kids : list (option jshape)) (k : option jshape) (nz : nat) (cur : Z) (XBS : list blk) : Prop :=
if isobj then exists t tbl size es svs e, zobj asegs A4F m x q (kids ++ [k]) nz t tbl size es svs XBS /\
nth_error es (length kids) = Some e /\ cur = ent_addr tbl (le_ix e)
else exists a arr size, zarr asegs A4F m x q (kids ++ [k]) nz a arr size XBS.

Definition body_stmtA (isobj : bool) (kids : list (option jshape)) (k : option jshape) : Prop :=
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (LB XBS : list blk) (x q : Z) (T : TSet) (nz : nat) (cur : Z),
HEAPAx A (XBS ++ LB) LM FRS B m md ->
zbodyp isobj m x q kids k nz cur XBS ->
stk asegs m lo (bv_unsigned sp + -112) -> rw_cells asegs m ERRNO [C4 errv] ->
512 * Z.of_nat (length XBS) <= bB B ->
(forall ms' md' A', NEXT q F1 fc1 m md LB B (512 * Z.of_nat (length XBS)) ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR x1 SPR gp TP t0 t1 t2 (Z_to_bv 64 x) (Z_to_bv 64 (x + 40)) a0 a1 a2 a3 a4 a5 a6 a7
x18 (Z_to_bv 64 cur) (Z_to_bv 64 (Z.of_nat (length kids))) (Z_to_bv 64 (Z.of_nat nz + 1))
(Z_to_bv 64 (x / 8 + 2147450885)) SBR (Z_to_bv 64 4) (Z_to_bv 64 (x / 8 + 2147450880)) (Z_to_bv 64 5) CM1 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x9a894) fc1 None m (seg_rom asegs)).

Definition tojs_of (isobj : bool) : Z := if isobj then fn_obj_to_json_string A4F else fn_arr_to_json_string A4F.

Lemma zhead_hdr : forall isobj m x q kids XBS,
zhead isobj m x q kids XBS -> List.NoDup (map blk_addr XBS) ->
exists pb cf, In (x, 48) XBS /\
rw_cells asegs m x (jhdr_cells (tyof isobj) 0 (tojs_of isobj) pb 0 q ++ [C8 (Z_to_bv 64 cf)]) /\
(forall m' q', rw_cells asegs m' x (jhdr_cells (tyof isobj) 0 (tojs_of isobj) pb 0 q' ++ [C8 (Z_to_bv 64 cf)]) ->
agree_on asegs (others x XBS) m m' -> zhead isobj m' x q' kids XBS).
Proof. intros isobj. destruct isobj; [apply zobjc_hdr | apply zarrc_hdr]. Qed.

Lemma zhead_agree : forall isobj BS m m' x q kids XBS,
zhead isobj m x q kids XBS -> agree_on asegs BS m m' -> incl XBS BS -> zhead isobj m' x q kids XBS.
Proof. intros isobj. destruct isobj; [apply zobjc_agree | apply zarrc_agree]. Qed.

Lemma zomb_zhead : forall c m v bs, zomb asegs A4F c m v bs -> desc_stmtA c ->
exists isobj ck, zhead isobj m v 0 ck bs /\ head_stmtA isobj ck.
Proof.
intros c m v bs ZC KD. destruct c as [| | | |ck|ck]; cbn in ZC; try contradiction.
- exists true, ck. split; [exact (proj2 ZC) | exact KD].
- exists false, ck. split; [exact (proj2 ZC) | exact KD].
Qed.
End Loop2A.
End RC__1.
End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPZI QlCE QhHQ Q5Ki.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 Qtgi Qsw7 QJjn QKQo. Import QPZI.Mq4 QlCE.Mq1 QhHQ Q5Ki.
Import Q6WR.Mq0 QrPc.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mq7 Q30W.Mq3 QJZd.Mq4 QlKV.Mq5 QI6Z.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Definition json_tokener_free_A_entry : Z := 0x92da0.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section TokFree2A.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis PUT : put_stmt_A HIx.

Definition tf_loop_postA (x2 gp s0 s1 s2 s3 s4 s7 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(md : config) (BASE LB0 PBS LM : list blk) (FRS : list frame) (B : bud) (SP : Z) (me mpre : word -> option byte) (lo : Z) (errv : word)
(q r pb depth : Z) (x : tscal) (levels : list tlevel) (i : nat) (s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (B' : bud) F' fc' levels' x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s6',
ms' = MS (mkR x1 x2 gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 (Z_to_bv 64 1) s6' s7 (Z_to_bv 64 (-16)) s9 s10 s11 t3 t4 t5 t6) F' (Z_to_bv 64 0x92ee0) fc' None m' (seg_rom asegs) /\
fsaved F F' /\ (frm0 fc -> frm0 fc') /\
model_vm_only (cfg_model md) (cfg_model md') /\
HEAPAx A' BASE LM FRS B' m' md' /\
length levels' = 32%nat /\
(forall j, (j <= i)%nat -> nth_error levels' j = Some lvl_reset) /\
(forall j, (i < j)%nat -> nth_error levels' j = nth_error levels j) /\
tstack asegs m' q levels' /\
rw_cells asegs m' r (tok_cells pb depth q x) /\
tf_frameA m' SP s8v s7v s6v s5v s4v s3v s2v s1v s0v rav /\
stk asegs m' lo (SP - 80) /\
heap_pres A4H (LB0 ++ LM ++ fr_ivs A4L FRS) SP me m' /\
rw_cells asegs m' A_ERRNO [C4 errv] /\
agree_on asegs PBS mpre m' /\
bB B - 512 * (Z.of_nat (length (lvblocks levels (S i))) + Z.of_nat (S i)) <= bB B' /\ bD B <= bD B'.

Lemma tokfree_loopA :
forall (i : nat) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m me : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (PBS LB0 LM : list blk) (FRS : list frame) (B : bud) (SP lo : Z) (errv : word)
(q r pb depth : Z) (x : tscal) (levels : list tlevel) (s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word),
(i < 32)%nat -> length levels = 32%nat ->
HEAPAx A (lvblocks levels (S i) ++ PBS ++ (r, 72) :: (q, 1024) :: LB0) LM FRS B m md ->
(forall j l, nth_error levels j = Some l -> (j <= i)%nat -> lvl_ok asegs A4F m l) ->
tstack asegs m q levels ->
rw_cells asegs m r (tok_cells pb depth q x) ->
tf_frameA m SP s8v s7v s6v s5v s4v s3v s2v s1v s0v rav ->
stk asegs m lo (SP - 80) -> alloc_ceiling <= lo -> lo <= SP - 80 - put_stk_A ->
SP mod 16 = 0 -> SP <= hiA_top A4L HIx -> 0 <= SP < 2^64 ->
heap_pres A4H (LB0 ++ LM ++ fr_ivs A4L FRS) SP me m ->
rw_cells asegs m A_ERRNO [C4 errv] ->
512 * (Z.of_nat (length (lvblocks levels (S i))) + Z.of_nat (S i)) <= bB B ->
(forall ms' md' A', tf_loop_postA (Z_to_bv 64 (SP - 80)) gp (Z_to_bv 64 r) (Z_to_bv 64 (r + 56)) (Z_to_bv 64 (r + 20)) (Z_to_bv 64 A_SB)
(Z_to_bv 64 (r / 8 + 2147450882)) (Z_to_bv 64 (r / 8 + 2147450887)) s9 s10 s11
F fc md (PBS ++ (r, 72) :: (q, 1024) :: LB0) LB0 PBS LM FRS B SP me m lo errv q r pb depth x levels i s8v s7v s6v s5v s4v s3v s2v s1v s0v rav ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (SP - 80)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 r) (Z_to_bv 64 (r + 56)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (r + 20)) (Z_to_bv 64 A_SB) (Z_to_bv 64 (r / 8 + 2147450882)) (Z_to_bv 64 1) (Z_to_bv 64 (32 * Z.of_nat i + 16))
(Z_to_bv 64 (r / 8 + 2147450887)) (Z_to_bv 64 (-16)) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 tokfree_loop_A_pc) fc None m (seg_rom asegs)).
Proof.
induction i as [|i IH]; intros until rav; intros Hi LEN HP LOK TS BLK FR ST LO LOS SPA HT SPR HPR ERR BB K.
-
destruct (nth_error levels 0) as [l|] eqn:Hl; [| apply nth_error_None in Hl; lia].
rewrite (lvblocks_S _ _ _ Hl) in HP, BB. rewrite <- app_assoc in HP. rewrite lvblocks_0, app_nil_r in BB.
eapply (tokfree_bodyA HIx PUT 0) with (P := PBS); [exact Hl | lia | exact LEN | exact HP | rewrite lvblocks_0; reflexivity
| eapply LOK; [exact Hl | lia] | exact TS | exact BLK | exact FR | exact ST | exact LO | exact LOS | exact SPA | exact HT | exact SPR | exact HPR | exact ERR | cbn [Z.of_nat length] in BB |- *; lia |].
intros ms1 md1 A1 (m1 & B1 & F1 & fc1 & y1 & u0 & u1 & u2 & w0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & -> & FS1 & FRM1 & VM1 & HP1 & TS1 & BLK1 & FR1 & ST1 & HPR1 & ERR1 & AG1 & BB1 & BD1).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI1.
pose proof (wmono_refl asegs m1) as WM. pose proof (munch_refl [] m1) as MU.
unfold_consts. reenterA asegs A4L HIx asegs_wx HP1.
step. if_false.
evt_done5. apply K. unfold tf_loop_postA.
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
eapply (tokfree_bodyA HIx PUT (S i)) with (P := lvblocks levels (S i) ++ PBS); [exact Hl | lia | exact LEN | exact HP | rewrite <- app_assoc; reflexivity
| eapply LOK; [exact Hl | lia] | exact TS | exact BLK | exact FR | exact ST | exact LO | exact LOS | exact SPA | exact HT | exact SPR | exact HPR | exact ERR | lia |].
intros ms1 md1 A1 (m1 & B1 & F1 & fc1 & y1 & u0 & u1 & u2 & w0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & -> & FS1 & FRM1 & VM1 & HP1 & TS1 & BLK1 & FR1 & ST1 & HPR1 & ERR1 & AG1 & BB1 & BD1).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI1.
pose proof (wmono_refl asegs m1) as WM. pose proof (munch_refl [] m1) as MU.
unfold_consts. reenterA asegs A4L HIx asegs_wx HP1.
step. if_truex.
replace (32 * Z.of_nat (S i) + 16 - 32) with (32 * Z.of_nat i + 16) by lia.
evt_done5.
eapply (IH _ gp _ _ _ _ _ _ _ _ _ _ _ s9 s10 s11 _ _ _ _ F1 fc1 m1 me md1 T A1 PBS LB0 LM FRS B1 SP lo errv q r pb depth x (lupd levels (S i) lvl_reset));
[lia | rewrite lupd_length; exact LEN | rewrite lvblocks_lupd_ge by lia; heap_nowA A4L HIx HP1 MU WM MI1 | | exact TS1 | exact BLK1 | exact FR1 | exact ST1 | exact LO | exact LOS | exact SPA | exact HT | exact SPR | exact HPR1 | exact ERR1 | rewrite lvblocks_lupd_ge by lia; lia |].
+ intros j l' Hj Hji. rewrite nth_error_lupd_neq in Hj by lia.
eapply lvl_ok_agree; [eapply LOK; [exact Hj | lia] | exact AG1 | apply incl_appl; eapply incl_tran; [| eapply lvblocks_incl; [exact Hj | lia]]; unfold lvl_blocks; apply incl_appl; apply incl_refl].
+ intros ms2 md2 A2 (m2 & B2 & F2 & fc2 & levels2 & y1' & u0' & u1' & u2' & w0' & v1' & v2' & v3' & v4' & v5' & v6' & v7' & u3' & u4' & u5' & u6' & s6' & -> & FS2 & FRM2 & VM2 & HP2 & LEN2 & RES2 & SAME2 & TS2 & BLK2 & FR2 & ST2 & HPR2 & ERR2 & AG2 & BB2 & BD2).
apply K. unfold tf_loop_postA.
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

Definition tokfree_costB (BS : list blk) : Z := 512 * (Z.of_nat (length BS) + 34).

Definition tokfree_postA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (BS : list blk) (lo : Z) (errv : word) (u : uwd)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (rv : word) (B' : bud),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc rv m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv] /\
bB B - tokfree_costB BS <= bB B' /\ bD B - uw_cost u <= bD B' /\
HEAPAx A' LB LM FRS B' m' md'.

Lemma json_tokener_free_A_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM BS : list blk) (FRS : list frame) (B : bud) (tk lo : Z) (errv : word) (u : uwd),
HEAPAx A (BS ++ LB) LM FRS B m md ->
tokrep asegs A4F m BS tk -> tk <> 0 ->
uw_at (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok A4L (hl_free A4H) ra u ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 80 - put_stk_A ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 tk ->
tokfree_costB BS <= bB B -> uw_cost u <= bD B ->
(forall ms' md' A', tokfree_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B BS lo errv u ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 json_tokener_free_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until u. intros HP TOKR Htk UW UWK ST LO LOS SPA HT ERR TP RA A0 BB BD K.
destruct TOKR as (q & pb & depth & PBS & levels & x & EBS & LEN & Hd & TOK & PB & Hpb & TS & LOK & CLEAN).
pose proof BB as BB0. unfold tokfree_costB in BB. rewrite EBS in BB. cbn [length] in BB. rewrite length_app, ?Nat2Z.inj_succ, Nat2Z.inj_add in BB.
subst BS a0 tp. unfold put_stk_A in LOS. unfold_consts. unfold A_SB, A_TP, A_ERRNO, json_tokener_free_A_entry in *. word_range sp SPR.

set (dn := Z.to_nat depth).
assert (PCV : Permutation (concat (map lvl_blocks levels)) (lvblocks levels (S dn))).
{ rewrite <- (lvblocks_trunc levels (S dn) ltac:(intros jj ll Hj Hkj; eapply CLEAN; [exact Hj | lia]) 32) by lia.
apply lvblocks_all. lia. }
pose proof (Permutation_length PCV) as LCV.
assert (HP0 : HEAPAx A (lvblocks levels (S dn) ++ PBS ++ (tk, 72) :: (q, 1024) :: LB) LM FRS B m md).
{ eapply (heapA_perm A4L HIx); [exact HP | | apply Permutation_refl | apply Permutation_refl].
replace (lvblocks levels (S dn) ++ PBS ++ (tk, 72) :: (q, 1024) :: LB)
with ((lvblocks levels (S dn) ++ PBS ++ [(tk, 72); (q, 1024)]) ++ LB) by (rewrite <- !app_assoc; reflexivity).
apply Permutation_app_tail.
apply (Permutation_trans (l' := (PBS ++ concat (map lvl_blocks levels)) ++ [(tk, 72); (q, 1024)])).
- apply (Permutation_app_comm [(tk, 72); (q, 1024)] (PBS ++ concat (map lvl_blocks levels))).
- replace (lvblocks levels (S dn) ++ PBS ++ [(tk, 72); (q, 1024)]) with ((lvblocks levels (S dn) ++ PBS) ++ [(tk, 72); (q, 1024)])
by (rewrite <- app_assoc; reflexivity).
apply Permutation_app_tail.
apply (Permutation_trans (l' := concat (map lvl_blocks levels) ++ PBS)); [apply Permutation_app_comm | apply Permutation_app_tail; exact PCV]. }
clear HP.
assert (INtk : In (tk, 72) (lvblocks levels (S dn) ++ PBS ++ (tk, 72) :: (q, 1024) :: LB)) by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 1024) (lvblocks levels (S dn) ++ PBS ++ (tk, 72) :: (q, 1024) :: LB)) by (apply in_or_app; right; apply in_or_app; right; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ tk 72 HP0 ltac:(apply in_or_app; left; exact INtk)) as (_ & Htal & Htlo & Hthi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ tk 72 HP0 ltac:(apply in_or_app; left; exact INtk)) as Himg_t.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ q 1024 HP0 ltac:(apply in_or_app; left; exact INq)) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ q 1024 HP0 ltac:(apply in_or_app; left; exact INq)) as Himg_q.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hqhi.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP0) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP0) as [GOT CELL].
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU.
unfold tok_cells in TOK.
pose proof PB as PB'. destruct PB' as (buf & bpos & size & pre & post & EPBS & _). stash PB.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ tk 72 HP0 INtk) as SHt. unfold shad in SHt. apply shadow_ro_cells in SHt.
let cs := eval cbv in (shadow_cells 72) in change (shadow_cells 72) with cs in SHt.
a4l. reenterA asegs A4L HIx asegs_wx HP0.
carve_frame 80%nat ST.
do 11 step.
step. if_falsex.
step. step. step. step.
step. asan_chkA.
step. norm_sx32.
step. step. if_falsex.
step. step. step. step. step. step.
sh_norm. rewrite (div8_add tk 56) by lia. change (56 / 8) with 7.
replace (tk / 8 + 7 + 2147450880) with (tk / 8 + 2147450887) by lia.
rewrite (unsigned_lit depth) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
replace (depth * 32 + 16) with (32 * Z.of_nat dn + 16) by lia.
replace (bv_unsigned sp + -80) with (bv_unsigned sp - 80) in * by lia.
clear SHt.
evt_done5.
lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ _ _ _ ?mc _) =>
assert (HPc : HEAPAx A (lvblocks levels (S dn) ++ PBS ++ (tk, 72) :: (q, 1024) :: LB) LM FRS B mc md) by heap_nowA A4L HIx HP0 MU WM MI;
assert (TSc : tstack asegs mc q levels)
by (eapply (tstack_transport asegs); [exact TS | exact MU | exact WM | intros j Hj; cbn; split; [lia | exact I]]);
assert (AGc : agree_on asegs (lvblocks levels (S dn) ++ PBS ++ (tk, 72) :: (q, 1024) :: LB) m mc)
by (eapply (agree_of_munch asegs); [exact MU | exact WM | intros a n Hin; cbn; split; [| exact I];
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a n HP0 ltac:(apply in_or_app; left; exact Hin)) as (_ & _ & _ & Hhi' & _); unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi'; lia]);
assert (HPRc : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mc)
by (eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |];
eapply (client_outsideA A4L HIx); [exact HP0 | intros bb Hbb; apply in_or_app; apply in_app_or in Hbb; destruct Hbb as [Hbb|Hbb]; [left; apply in_or_app; right; apply in_or_app; right; right; right; exact Hbb | right; exact Hbb] | clia | ];
apply Forall_cons; [left; cbn [fst snd]; clia | apply Forall_nil])
end.
eapply (tokfree_loopA dn _ gp _ _ _ _ _ _ _ _ _ _ _ s9 s10 s11 _ _ _ _ F fc _ m md T A PBS LB LM FRS B (bv_unsigned sp) lo errv q tk pb depth x levels);
[ lia | lia | exact HPc | intros j l Hj Hji; eapply lvl_ok_agree; [eapply LOK; [exact Hj | lia] | exact AGc | apply incl_appl; eapply incl_tran; [| eapply lvblocks_incl; [exact Hj | lia]]; unfold lvl_blocks; apply incl_appl; apply incl_refl]
| exact TSc | unfold tok_cells; exact TOK | unfold tf_frameA; exact FR | exact ST | clia | unfold put_stk_A; clia | exact SPA | exact HT | lia
| exact HPRc | exact ERR | rewrite <- LCV; lia | ].
intros ms1 md1 A1 (mq1 & B1 & F1 & fc1 & levels1 & y1 & u0 & u1 & u2 & w0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & s6' & -> & FS1 & FRM1 & VM1 & HP1 & LEN1 & RES1 & SAME1 & TS1 & TOK1 & FR1 & ST1 & HPR1 & ERR1 & AG1 & BB1 & BD1).
clear TSc TOK FR ST MU WM MI HPc.
unfold tok_cells in TOK1. unfold tf_frameA in FR1.
assert (INp : In (pb, 16) (PBS ++ (tk, 72) :: (q, 1024) :: LB)) by (rewrite EPBS; left; reflexivity).
assert (INtk1 : In (tk, 72) (PBS ++ (tk, 72) :: (q, 1024) :: LB)) by (apply in_or_app; right; left; reflexivity).
assert (INq1 : In (q, 1024) (PBS ++ (tk, 72) :: (q, 1024) :: LB)) by (apply in_or_app; right; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ pb 16 HP1 ltac:(apply in_or_app; left; exact INp)) as (_ & Hpal & Hplo & Hphi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
assert (Htq : tk <> q).
{ intros ->. pose proof (nodup_app_l' _ _ (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP1)) as ND. rewrite map_app in ND. apply NoDup_app_remove_l in ND.
cbn [map blk_addr fst] in ND. apply List.NoDup_cons_iff in ND as [Hni _]. apply Hni. left. reflexivity. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q 1024 HP1 ltac:(apply in_or_app; left; exact INtk1) ltac:(apply in_or_app; left; exact INq1) Htq) as Hdtq.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI. a4l.
pose proof (wmono_refl asegs mq1) as WM.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (tk, tk + 72)] mq1) as MU.

assert (SHT : forall Ax LBx Bx mdx mc, HEAPAx Ax LBx LM FRS Bx mc mdx -> In (tk, 72) LBx ->
ro_cells asegs mc (tk / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
{ intros Ax LBx Bx mdx mc HPx Itk. pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ tk 72 HPx Itk) as SH. unfold shad in SH. apply shadow_ro_cells in SH.
let cs := eval cbv in (shadow_cells 72) in change (shadow_cells 72) with cs in SH. a4l. exact SH. }
pose proof (SHT _ _ _ _ mq1 HP1 INtk1) as SHt.
reenterA asegs A4L HIx asegs_wx HP1.
step.
step. step. if_false. rewrite ?sxb_zero, ?zxb_zero.
stepz.
try clear SHt. pose proof (SHT _ _ _ _ _ ltac:(heap_nowA A4L HIx HP1 MU WM MI) INtk1) as SHt.
step. asan_chkA.
stepz.
try clear SHt. pose proof (SHT _ _ _ _ _ ltac:(heap_nowA A4L HIx HP1 MU WM MI) INtk1) as SHt.
step. asan_chkA.
step. step. if_falsex. step.
try clear SHt.

unstash PB.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (PBc : pbuf asegs mc PBS pb)
by (eapply (pbuf_agree asegs); [exact PB | | apply incl_refl];
eapply agree_on_trans; [eapply agree_on_incl; [exact AGc | rewrite EPBS; intros b Hb; apply in_or_app; right; apply in_or_app; left; exact Hb] |];
eapply agree_on_trans; [exact AG1 |];
eapply (agree_of_munch asegs); [exact MU | exact WM | intros a n Hin; cbn; split; [| split; [| exact I]];
[ pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a n HP1 ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin)) as (_ & _ & _ & Hhi' & _); unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi'; lia
| refine (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ a n tk 72 HP1 ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin) ltac:(apply in_or_app; left; exact INtk1) _);
intros ->; exact (nodup_prefix_suffix PBS ((tk, 72) :: (q, 1024) :: LB) tk n 72 (nodup_app_l' _ _ (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP1)) Hin ltac:(left; reflexivity)) ]])
end.
evt_done5.
eapply (printbuf_free_A_cps HIx) with (LB := (tk, 72) :: (q, 1024) :: LB) (BS := PBS) (p := pb) (lo := lo) (u := UWptr);
[ heap_nowA A4L HIx HP1 MU WM MI
| intros _; apply uw_at_ptr; rewrite ?unsigned_lit by lia; lia
| intros _; cbn [uw_ok uw_key]; unfold a4_straces; repeat first [left; reflexivity | right]
| right; split; [exact Hpb | apply pbuf_pbufw; exact PBc] | .. ];
a4l_goal; rewrite ?unsigned_lit by lia; try first [reflexivity | lia].
all: try (replace (bv_unsigned sp - 80) with (bv_unsigned sp - 80) by lia; rewrite Zminus_mod, SPA; reflexivity).
all: try eassumption.
all: try (rewrite EPBS; cbn [length Z.of_nat]; cbn [bB charge] in *; lia).
all: try (pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP1) as [? ?]; destruct (pb =? 0); cbn [uw_cost bD charge] in *; lia).
intros ms2 md2 A2 (mq2 & r2 & B2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & BB2 & BD2 & HP2).
destruct RS2 as (w0' & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
a4l. rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR2 by lia.
replace (if pb =? 0 then 0 else uw_cost UWptr) with 0 in BD2 by (destruct (pb =? 0); reflexivity).
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR1; [| left; cbn; lia]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in TOK1; [| eapply (client_range_block A4H _ _ _ _ tk 72); [apply in_or_app; left; left; reflexivity | lia | cbn; lia]]. a4l.
assert (NTL : forall nn, ~ In (tk, nn) (LB ++ LM)).
{ intros nn Hin0. exact (nodup_prefix_suffix (PBS ++ [(tk, 72); (q, 1024)]) (LB ++ LM) tk 72 nn
ltac:(pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP1) as ND; rewrite <- !app_assoc in ND |- *; cbn [app] in ND |- *; exact ND)
ltac:(apply in_or_app; right; left; reflexivity) Hin0). }
assert (NTL72 : ~ In (tk, 72) (LB ++ LM ++ fr_ivs A4L FRS)).
{ apply not_in_app3; [exact (NTL 72)|]. eapply (blk_not_fr_iv A4L HIx); [exact HP1 | apply in_or_app; left; apply in_or_app; right; left; reflexivity]. }
assert (HPRb : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mq2).
{ eapply heap_pres_trans; [exact HPR1|]. eapply heap_pres_trans.
- eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP1 | intros bb Hbb; apply in_or_app; apply in_app_or in Hbb; destruct Hbb as [Hbb|Hbb]; [left; apply in_or_app; right; right; right; exact Hbb | right; exact Hbb] | clia |].
apply Forall_cons; [left; cbn [fst snd]; clia | apply Forall_cons; [| apply Forall_nil]]. cbn [fst snd].
right; left. exists tk, 72. split; [apply in_or_app; left; exact INtk1|]. split; [exact NTL72 | lia].
- eapply heap_pres_weaken; [exact HPR2 | lia | intros bb Hbb; apply in_or_app; apply in_app_or in Hbb; destruct Hbb as [Hbb|Hbb]; [left; right; right; exact Hbb | right; exact Hbb]]. }
clear MU WM MI HPR1.

pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. a4l.
pose proof (wmono_refl asegs mq2) as WM. pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] mq2) as MU.
pose proof (SHT _ _ _ _ mq2 HP2 ltac:(left; reflexivity)) as SHt.
reenterA asegs A4L HIx asegs_wx HP2.
asan_chkA.
step. step.
try clear SHt.
alloc_callA (hiA_free A4L HIx) blk q uw UWptr A4L HIx HP2 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists 1024. right. left. reflexivity. }
all: try (cbn [uw_pre uw_ok uw_key uw_cost]; intros _; split; [left; lia | unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP2) as [? ?]; destruct (Z.eqb_spec q 0); cbn [bB bD charge uw_cost] in *; rewrite ?EPBS in *; cbn [length Z.of_nat] in *; lia).
intros ms3 mx3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3. a4l.
rewrite ?unsigned_lit in ST3 by lia. rewrite ?unsigned_lit in HPR3 by lia.
rewrite (lb_remove_other q (tk, 72)) in HPR3, HP3 by (cbn; lia). rewrite lb_remove_head in HPR3, HP3.
replace (if q =? 0 then 0 else uw_cost UWptr) with 0 in HP3 by (destruct (Z.eqb_spec q 0); reflexivity).
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FR1; [| left; cbn; lia]. a4l.
assert (HPRd : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mx3).
{ eapply heap_pres_trans; [exact HPRb|]. eapply heap_pres_trans.
- eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP2 | intros bb Hbb; apply in_or_app; apply in_app_or in Hbb; destruct Hbb as [Hbb|Hbb]; [left; right; right; exact Hbb | right; exact Hbb] | clia |].
apply Forall_cons; [left; cbn [fst snd]; clia | apply Forall_nil].
- eapply heap_pres_weaken; [exact HPR3 | lia | intros bb Hbb; apply in_or_app; apply in_app_or in Hbb; destruct Hbb as [Hbb|Hbb]; [left; right; exact Hbb | right; exact Hbb]]. }
clear MU WM MI HPRb TOK1.

pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI. a4l.
pose proof (wmono_refl asegs mx3) as WM. pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] mx3) as MU.
reenterA asegs A4L HIx asegs_wx HP3.
do 12 step.
replace (Z_to_bv 64 (bv_unsigned sp - 80 + 80)) with sp by (apply bv_eq; rewrite unsigned_lit by lia; lia).
release_frame FR1 ST3 (bv_unsigned sp).
step.
assert (UW3 : uw_at (hiA_top A4L HIx) mx3 (bv_unsigned sp) (bv_unsigned s0) u) by (eapply uw_at_heap_pres; [exact UW | exact HPRd | lia]).
alloc_callA (hiA_free A4L HIx) blk tk uw u A4L HIx HP3 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists 72. left. reflexivity. }
all: try (intros _; split; [eapply uw_at_pre0; [exact UW3 | lia] | exact UWK]).
all: try (eapply uw_at_pre0; [exact UW3 | lia]). all: try exact UWK.
all: try (pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP3) as [? ?]; destruct (Z.eqb_spec tk 0); [lia|]; destruct u; cbn [bB bD charge uw_cost] in *; rewrite ?EPBS in *; cbn [length Z.of_nat] in *; lia).
intros ms4 m4 md4 A4 r4 RS4 VM4 ST4 HPR4 ERR4 HP4. open_ret RS4. a4l.
rewrite lb_remove_head in HPR4, HP4.
replace (if tk =? 0 then 0 else uw_cost u) with (uw_cost u) in HP4 by (destruct (Z.eqb_spec tk 0); [lia|reflexivity]).
apply K. unfold tokfree_postA.
exists m4, r4, (charge (charge B2 512 0) 512 (uw_cost u)).
split; [| split; [| split; [exact ST4 | split; [| split; [exact ERR4 | split; [| split; [| exact HP4]]]]]]].
- eapply ret_statew_intro; [eapply fsaved_trans; [exact FS1 | exact FS2] | intros Hf; apply FRM2, FRM1, Hf].
- eapply model_vm_only_trans; [exact VM1|]. eapply model_vm_only_trans; [exact VM2|]. eapply model_vm_only_trans; [exact VM3| exact VM4].
- eapply heap_pres_trans; [exact HPRd|]. eapply heap_pres_trans.
+ eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP3 | intros bb Hbb; apply in_or_app; apply in_app_or in Hbb; destruct Hbb as [Hbb|Hbb]; [left; right; exact Hbb | right; exact Hbb] | clia |].
apply Forall_cons; [left; cbn [fst snd]; clia | apply Forall_nil].
+ eapply heap_pres_weaken; [exact HPR4 | lia | intros bb Hbb; exact Hbb].
- clear - BB0 BB1 BB2 LCV EPBS Hd. unfold tokfree_costB in *. cbn [bB charge] in *. unfold dn in *. rewrite ?Z2Nat.id in BB1 by lia.
rewrite <- LCV in BB1. rewrite EPBS in *. cbn [length app] in *. rewrite ?length_app in *. cbn [length] in *. lia.
- cbn [bD charge uw_cost] in *. lia.
Qed.
End TokFree2A.
End RC__1.
End Mq5.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache QWxq_c1 Qfw3_c1 Qc3B QYIF QrIB Q6Vi QXUB Qw5U Qekr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun QWxq_c1.Mq0 Qfw3_c1.Mq2 Qc3B.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn.
Import Q6WR Q6WR.Mq0 QrPc.
Import QYIF.

Import Q7UD QXUB.Mq0 Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QsKa.Mq4 QlKV.Mqa QsKa.Mq0 QJZd.Mq0 QsKa.Mq8 Qw5U.Mq0 Qekr.Mq0 QsKa.Mq6.

Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma neg_word_negvalA : forall z, -2^63 <= z < 2^63 -> Z_to_bv 64 (0 - bv_unsigned (Z_to_bv 64 z)) = Z_to_bv 64 (- z).
Proof.
intros z Hz. rewrite Z_to_bv_unsigned. rewrite <- (Z_to_bv_mod64 (0 - _)), <- (Z_to_bv_mod64 (- z)). f_equal.
change (bv_wrap 64 z) with (z mod 2^64).
destruct (Z.lt_ge_cases z 0).
- rewrite <- (Z.mod_unique z (2^64) (-1) (z + 2^64)) by lia.
rewrite <- (Z.mod_unique (0 - (z + 2^64)) (2^64) (-1) (-z)) by lia.
rewrite <- (Z.mod_unique (- z) (2^64) 0 (-z)) by lia. reflexivity.
- rewrite (Z.mod_small z) by lia. f_equal; lia.
Qed.

Lemma str_lenA_of_cell : forall m p n (newlen : word) (len : Z),
rw_cells asegs m (p + 40) [C8 newlen] -> newlen = Z_to_bv 64 len -> - 2^31 < len < 2^31 -> Z.abs len <= n -> str_lenA m p n.
Proof.
intros m p n newlen len H E R B. subst newlen. exists len. split; [| split; [exact R | exact B]].
pose proof (rw_cells_bytes_at asegs _ _ _ H) as BY. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY. exact BY.
Qed.
Lemma string_root_true : forall r, set_string_root r = JRstrx -> is_string_root r = true.
Proof.
intros [|sx|?|] H; cbn in H |- *; try discriminate; try reflexivity.
destruct sx; cbn in H |- *; first [reflexivity | discriminate].
Qed.

Section MJoSetString.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Notation jroot_repA := (jroot_rep A4H A4F).
Notation wz := (Z_to_bv 64).
Hypothesis OBL_AMEMCPY_U : amemcpy_spec_U.
Hypothesis OBL_ASTRLEN_U : astrlen_spec_U.

Definition SS_STK_A : Z := 80 + 4096.
Definition ss_costB (n : Z) : Z := 16 * (n + 1) + 1024.

Lemma src_pres : forall A LBa LM FRS B m0 md LBX SP m m' Fs ks S (sb : list byte),
HEAPAx A LBa LM FRS B m0 md -> In (Fs, ks) FRS -> Fs <= S -> S + Z.of_nat (length sb) <= Fs + fr_size ks - 8 ->
heap_pres A4H (LBX ++ LM ++ fr_ivs A4L FRS) SP m m' ->
bytes_at asegs m S sb /\ (sb <> [] -> unpoisoned asegs m A_SB S (Z.of_nat (length sb))) ->
bytes_at asegs m' S sb /\ (sb <> [] -> unpoisoned asegs m' A_SB S (Z.of_nat (length sb))).
Proof.
intros A LBa LM FRS B m0 md LBX SP m m' Fs ks S sb HP HFs H1 H2 HPR [BY UN]. split.
- eapply (heap_pres_bytes_at A4H); [exact HPR | exact BY |].
eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact HFs | cbn; lia | cbn; lia].
- intros NE. eapply (unpoisoned_pres_frame HIx); [exact HP | exact HFs | exact H1 | exact H2 | exact (UN NE) | exact HPR].
Qed.

Lemma jroot_str_casesA : forall r m BS p,
jroot_repA r m BS p -> r <> JRnull -> List.NoDup (map blk_addr BS) ->
p <> 0 /\
( (xstr A4H A4F m BS p 1 /\ set_string_root r = JRstrx)
\/ (set_string_root r = r /\ is_string_root r = false /\
exists n ty tojs pb udel ud rest,
In (p, n) BS /\ Z.of_nat (cells_size (jhdr_cells ty 1 tojs pb udel ud ++ rest)) = n /\ 48 <= n /\ 0 <= ty <= 6 /\ ty <> JT_STRING /\
rw_cells asegs m p (jhdr_cells ty 1 tojs pb udel ud ++ rest)) ).
Proof.
intros r m BS p RR NN ND.
assert (Hp : p <> 0) by (destruct r; [exfalso; exact (NN eq_refl) | exact (proj1 RR) ..]). split; [exact Hp|].
destruct r as [|s|tojs|]; [exfalso; exact (NN eq_refl)| | |].
- destruct RR as [_ J].
assert (SPLIT : (exists h, s = Sstr h) \/ jtype s <> JT_STRING).
{ destruct s as [|u| |h|kids|kids]; cbn [jtype]; unfold JT_BOOLEAN, JT_DOUBLE, JT_INT, JT_STRING, JT_OBJECT, JT_ARRAY;
first [left; eexists; reflexivity | right; lia]. }
destruct SPLIT as [[h ->] | NS]; [left; split; [eapply (Q6Vi.Mq1.jval_sstr_xstr A4H); exact J | reflexivity]|].
right. split; [destruct s as [|u| |h|kids|kids]; try reflexivity; cbn [jtype] in NS; exfalso; exact (NS eq_refl)|].
split; [destruct s as [|u| |h|kids|kids]; try reflexivity; cbn [jtype] in NS; exfalso; exact (NS eq_refl)|].
destruct (jval_hdr asegs A4F s m BS p 1 J ND) as (n & tojs & pb & udel & ud & rest & INp & SZ & N48 & HDR & _).
exists n, (jtype s), tojs, pb, udel, ud, rest. split; [exact INp|]. split; [exact SZ|]. split; [exact N48|].
split; [apply jtype_range|]. split; [exact NS| exact HDR].
- right. split; [reflexivity|]. split; [reflexivity|]. destruct RR as (_ & Htojs & pb & PBS & bits & EBS & OPB & HDR).
exists 48, JT_DOUBLE, tojs, pb, 0, 0, [C8 bits]. split; [rewrite EBS; left; reflexivity|]. split; [reflexivity|]. split; [lia|].
split; [unfold JT_DOUBLE; lia|]. split; [unfold JT_DOUBLE, JT_STRING; lia|]. exact HDR.
- left. split; [exact (proj2 RR) | reflexivity].
Qed.
Section BodyC.
Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB BS LM : list blk) (FRS : list frame) (B0 : bud) (lo p S : Z) (sb : list byte) (r : jroot) (T : TSet) (errv : word).
Variables (Fs ks : Z).
Let n := Z.of_nat (length sb).
Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp - SS_STK_A.
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hiA_top A4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis HFS : In (Fs, ks) FRS.
Hypothesis HS1 : Fs <= S.
Hypothesis HS2 : S + n <= Fs + fr_size ks - 8.
Hypothesis LSB : n <= 63.
Hypothesis BB0 : ss_costB n <= bB B0.
Hypothesis BD0 : 2 <= bD B0.
Hypothesis K : set_string_postA HIx ra sp gp (wz 6434400) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB BS LM FRS B0 (ss_costB n) 2 lo p n r T.

Lemma sc_exit : forall (m1 : word -> option byte) (md1 : config) (A1 : ASA A4L HIx) (B1 : bud) (BS' : list blk) (fj : list byte) (rv : Z) (e1 : word)
(xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xt3 xt4 xt5 xt6 : word),
rw_cells asegs m1 (bv_unsigned sp + -80) [CB 8 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk asegs m1 lo (bv_unsigned sp + -80) -> model_vm_only (cfg_model md0) (cfg_model md1) ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m1 ->
rw_cells asegs m1 6434236 [C4 e1] ->
HEAPAx A1 (BS' ++ LB) LM FRS B1 m1 md1 -> jo_chargeA (ss_costB n) 2 B0 B1 ->
jroot_repA (set_string_root r) m1 BS' p ->
(is_string_root r = true -> str_lenA m1 p n) -> (is_string_root r = false -> BS' = BS) ->
AJ5 A4L HIx A1 T md1
(MS (mkR xra (wz (bv_unsigned sp + -80)) gp (wz 6434400) xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 (wz rv) xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
F (wz 0x9ea98) fc None m1 (seg_rom asegs)).
Proof.
intros until xt6. intros FR1 ST1 VM1 HPR1 ERR1 HP1 CH1 ROOT KSL KBS.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
unfold SS_STK_A in LOS.
a4l. reenterA asegs A4L HIx asegs_wx HP1.
do 10 step.
release_frame FR1 ST1 (bv_unsigned sp).
step. step.
evt_done5.
eapply (K _ md1 m1 rv A1 B1 BS').
- unfold jo_post_frameA. split; [apply ret_statew_same|]. split; [exact VM1|]. split; [exact ST1|]. split; [exact HPR1 | exists e1; exact ERR1].
- exact CH1.
- exact ROOT.
- exact HP1.
- exact KSL.
- exact KBS.
Qed.

Lemma blk_not_pres : forall A1 BS1 B1 m1 md1 a k, HEAPAx A1 (BS1 ++ LB) LM FRS B1 m1 md1 -> In (a, k) BS1 -> ~ In (a, k) (LB ++ LM ++ fr_ivs A4L FRS).
Proof.
intros A1 BS1 B1 m1 md1 a k HP1 Hin Hi.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP1) as ND.
apply in_app_or in Hi as [Hi|Hi]; [| apply in_app_or in Hi as [Hi|Hi]].
- exact (nodup_prefix_suffix BS1 LB a k k (nodup_app_l' _ _ ND) Hin Hi).
- exact (nodup_prefix_suffix (BS1 ++ LB) LM a k k ND ltac:(apply in_or_app; left; exact Hin) Hi).
- refine (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP1 _ Hi). apply in_or_app; left. apply in_or_app; left. exact Hin.
Qed.

Lemma sc_tail : forall (m1 : word -> option byte) (md1 : config) (A1 : ASA A4L HIx) (B1 : bud) (BS1 : list blk) (fj : list byte) (e1 : word)
(D : Z) (k : nat) (junk : list byte) (newlen lenw : word) (bD szD pn : Z)
(xra xt0 xt1 xt2 xs1 xa0 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xt3 xt4 xt5 xt6 : word),
rw_cells asegs m1 (bv_unsigned sp + -80) [CB 8 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk asegs m1 lo (bv_unsigned sp + -80) -> model_vm_only (cfg_model md0) (cfg_model md1) ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m1 ->
rw_cells asegs m1 6434236 [C4 e1] ->
HEAPAx A1 (BS1 ++ LB) LM FRS B1 m1 md1 -> jo_chargeA (ss_costB n) 2 B0 B1 ->
bytes_at asegs m1 S sb -> (sb <> [] -> unpoisoned asegs m1 A_SB S n) ->
rw_cells asegs m1 D [CB k junk] -> n + 1 <= Z.of_nat k -> In (bD, szD) BS1 -> bD <= D -> D + Z.of_nat k <= bD + szD ->
rw_cells asegs m1 (p + 40) [C8 lenw] -> In (p, pn) BS1 -> 48 <= pn ->
(p + 48 <= D \/ D + Z.of_nat k <= p) ->
set_string_root r = JRstrx ->
(exists len, newlen = wz len /\ - 2^31 < len < 2^31 /\ Z.abs len <= n) ->
(forall m2, munch [(lo, bv_unsigned sp); (D, D + Z.of_nat k); (p + 40, p + 48)] m1 m2 -> wmono asegs m1 m2 -> mem_inv asegs m2 ->
rw_cells asegs m2 D [CB k (sb ++ [Z_to_bv 8 0] ++ skipn (Z.to_nat (n + 1)) junk)] ->
rw_cells asegs m2 (p + 40) [C8 newlen] ->
exists BS', Permutation BS1 BS' /\ jroot_repA JRstrx m2 BS' p) ->
AJ5 A4L HIx A1 T md1
(MS (mkR xra (wz (bv_unsigned sp + -80)) gp (wz 6434400) xt0 xt1 xt2 (wz (p + 40)) xs1 xa0 (wz S) (wz n) xa3 xa4 xa5 xa6 xa7
(wz D) (wz 2147450880) (wz (p / 8 + 2147450885)) newlen xs6 xs7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
F (wz 0x9ea64) fc None m1 (seg_rom asegs)).
Proof.
intros until xt6. intros FR1 ST1 VM1 HPR1 ERR1 HP1 CH1 SB1 UN1 DST Hk INd HbD HDk LEN INp Hpn SEP SR NL FIN.
unfold SS_STK_A in LOS.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof alloc_ceiling_range as ACR.
assert (INdA : In (bD, szD) ((BS1 ++ LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; left; exact INd).
assert (INpA : In (p, pn) ((BS1 ++ LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; left; exact INp).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ bD szD HP1 INdA) as (_ & _ & HdLO & HdHI & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p pn HP1 INpA) as (_ & Hpal & HpLO & HpHI & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ bD szD HP1 INdA) as HdIMG. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in HdIMG.
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ p pn HP1 INpA) as HpIMG. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in HpIMG.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP1 HFS) as (_ & _ & HF0 & HFc & _).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP1 HFS INdA) as DFd.
pose proof (fr_size_pos ks) as FSP.
assert (Hn0 : 0 <= n) by (subst n; lia).
assert (LJ : length junk = k) by (destruct DST as [[[Hwf _] _] _]; exact Hwf).
pose proof (asan_rt_ok_of_HEAPA HIx _ _ _ _ _ _ _ HP1) as RT1.
assert (UND : 0 < n -> unpoisoned asegs m1 A_SB D n).
{ intros Hn. eapply (unpoisoned_of_blk HIx _ _ _ _ _ _ _ bD szD D n HP1); [apply in_or_app; left; exact INd | lia | lia | lia]. }
assert (UNS : 0 < n -> unpoisoned asegs m1 A_SB S n).
{ intros Hn. apply UN1. intros ->. subst n. cbn in Hn. lia. }

destruct (rw_cells_CB_cut asegs _ _ _ _ (Z.to_nat n) DST ltac:(lia)) as [DATA REST1].
destruct (rw_cells_CB_cut asegs _ _ _ _ 1%nat REST1 ltac:(lia)) as [NUL REST2]. clear DST REST1.
replace (D + Z.of_nat (Z.to_nat n)) with (D + n) in NUL, REST2 by lia.
replace (D + n + Z.of_nat 1) with (D + n + 1) in REST2 by lia.
pose proof (munch_refl [(lo, bv_unsigned sp); (D, D + Z.of_nat k); (p + 40, p + 48)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
a4l. reenterA asegs A4L HIx asegs_wx HP1.
step. step. step.
eapply OBL_AMEMCPY_U with (d := D) (s := S) (n := n) (lo := lo) (old := firstn (Z.to_nat n) junk) (src := sb);
[ exact UND | exact UNS | exact RT1 | lia | lia | lia | lia
| left; rewrite ?unsigned_lit by lia; lia | left; rewrite ?unsigned_lit by lia; lia
| reflexivity | reflexivity | reflexivity | lia | left; lia | lia
| exact DATA | exact SB1 | subst n; rewrite Nat2Z.id; reflexivity
| rewrite ?unsigned_lit by lia; eassumption | exact LO | rewrite ?unsigned_lit by lia; lia
| rewrite ?unsigned_lit by lia; clear - SPA; Z.div_mod_to_equations; lia | exact MI | rewrite ?unsigned_lit by lia; reflexivity | ].
rewrite ?unsigned_lit by lia.
intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 MU2 WM2 MI2 DATA2 SB2 ST2.
lazymatch type of MU2 with munch _ ?mq _ =>
transport_after_call asegs mq m2 MU2 WM2; try match goal with H : mem_inv asegs mq |- _ => clear H end; clear MU2 WM2 end.
replace (ret_pc (wz 0x9ea70)) with (wz 0x9ea70) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step.
assert (FW : forall mX, munch [(lo, bv_unsigned sp); (D, D + Z.of_nat k); (p + 40, p + 48)] m1 mX -> wmono asegs m1 mX -> mem_inv asegs mX ->
HEAPAx A1 (BS1 ++ LB) LM FRS B1 mX md1).
{ intros mX MUX WMX MIX. eapply (heapA_client_frame A4L HIx); [exact HP1 | | exact WMX | exact MIX].
eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP1 MUX).
apply Forall_cons; [left; cbn [fst snd]; lia |].
apply Forall_cons; [right; left; exists bD, szD; cbn [fst snd]; split; [exact INdA | lia] |].
apply Forall_cons; [right; left; exists p, pn; cbn [fst snd]; split; [exact INpA | lia] | apply Forall_nil]. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m1 mc, WMc : wmono asegs m1 mc, MIc : mem_inv asegs mc |- _ =>
pose proof (FW mc MUc WMc MIc) as HPc end end.
assert (UNk : unpoisoned asegs m2 A_SB (D + n) 1)
by (eapply (unpoisoned_of_blk HIx _ _ _ _ _ _ _ bD szD (D + n) 1 HPc); [apply in_or_app; left; exact INd | lia | lia | lia]).
destruct (unpoisoned_last asegs _ _ _ _ UNk) as (v & SHk & Hv).
replace (D + n + 1 - 1) with (D + n) in SHk, Hv by lia. unfold A_SB in SHk.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p pn 5 HPc ltac:(apply in_or_app; left; exact INp) ltac:(lia) ltac:(lia)) as SH5.
replace (p / 8 + 2147450880 + 5) with (p / 8 + 2147450885) in SH5 by lia.
clear HPc.
lazymatch goal with |- evt _ ?Q (MS ?rg ?Fx ?pc ?fcx None ?mc ?rom) =>
let r' := open_constr:(mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in unify rg r';
lazymatch r' with mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31 =>
assert (CONT : forall ya1 ya2 : word, evt asegs Q
(MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ya1 ya2 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Fx (wz 0x9ea84) fcx None mc rom))
end end.
2:{ step. step. sh_norm. step. step.
destruct Hv as [-> | [Hv8 Hvm]].
- rewrite sxb_zero. if_false. apply CONT.
- rewrite (QsKa.Mq1.sxb_small v) by lia. if_truex. step. step.
rewrite (unsigned_lit (D + n)) by lia. rewrite QsKa.Mq1.land7_mod8 by lia. if_truex. apply CONT. }
intros ya1 ya2.
set (ez := D + n) in *. stepz. subst ez.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m1 mc, WMc : wmono asegs m1 mc, MIc : mem_inv asegs mc |- _ =>
pose proof (FW mc MUc WMc MIc) as HPc end end.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p pn 5 HPc ltac:(apply in_or_app; left; exact INp) ltac:(lia) ltac:(lia)) as SH5.
replace (p / 8 + 2147450880 + 5) with (p / 8 + 2147450885) in SH5 by lia. clear HPc.
step. rewrite ?zxb_zero. step. if_false.
step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m1 mc, WMc : wmono asegs m1 mc, MIc : mem_inv asegs mc |- _ =>
pose proof (FW mc MUc WMc MIc) as HP3;
assert (HPR3 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 mc);
[ eapply heap_pres_trans; [exact HPR1|];
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MUc | exact WMc |];
eapply (client_outsideA A4L HIx);
[ exact HP1
| intros ? Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb]
| clia | ];
apply Forall_cons; [left; cbn [fst snd]; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia |];
apply Forall_cons; [right; left; exists bD, szD; cbn [fst snd]; split; [exact INdA | split; [exact (blk_not_pres _ _ _ _ _ _ _ HP1 INd) | lia]] |];
apply Forall_cons; [right; left; exists p, pn; cbn [fst snd]; split; [exact INpA | split; [exact (blk_not_pres _ _ _ _ _ _ _ HP1 INp) | lia]] | apply Forall_nil]
|];
destruct (FIN mc MUc WMc MIc) as (BS' & PERM & ROOT') end end.
{
lazymatch goal with H : rw_cells asegs _ (D + n) [C1 _] |- _ =>
apply (rw_cells_recast asegs _ _ _ [CB 1 [Z_to_bv 8 0]]) in H; [| cbn; auto | reflexivity | reflexivity] end.
lazymatch goal with H1 : rw_cells asegs ?mc D [CB _ sb], H2 : rw_cells asegs ?mc (D + n) [CB 1 _], H3 : rw_cells asegs ?mc (D + n + 1) _ |- _ =>
pose proof (rw_cells_CB_join asegs _ _ _ _ _ _ H1 ltac:(replace (D + Z.of_nat (Z.to_nat n)) with (D + n) by lia; exact H2)) as J1;
pose proof (rw_cells_CB_join asegs _ _ _ _ _ _ J1 ltac:(replace (D + Z.of_nat (Z.to_nat n + 1)) with (D + n + 1) by lia; exact H3)) as J2 end.
rewrite <- app_assoc in J2. replace (Z.to_nat n + 1 + (k - Z.to_nat n - 1))%nat with k in J2 by lia.
rewrite skipn_skipn in J2. replace (1 + Z.to_nat n)%nat with (Z.to_nat (n + 1)) in J2 by lia. exact J2. }
{ assumption. }
evt_done5.
eapply (sc_exit _ md1 A1 B1 BS' fj 1 e1); [eassumption | eassumption | exact VM1 | exact HPR3 | eassumption | | exact CH1 | rewrite SR; exact ROOT' | |].
- eapply (heapA_perm A4L HIx); [exact HP3 | | apply Permutation_refl | apply Permutation_refl]. apply Permutation_app_tail. exact PERM.
- intros _. destruct NL as (len & EQ & R1 & R2).
lazymatch goal with |- str_lenA ?mX _ _ => lazymatch goal with H : rw_cells asegs mX (p + 40) [C8 _] |- _ => exact (str_lenA_of_cell _ _ _ _ _ H EQ R1 R2) end end.
- intros Hf. exfalso. rewrite (string_root_true r SR) in Hf. discriminate.
Qed.

Lemma sc_grow2 : forall (m1 : word -> option byte) (md1 : config) (A1 : ASA A4L HIx) (B1 : bud) (fj : list byte) (e1 : word)
(PBS : list blk) (q cap pb : Z) (junk0 junk : list byte) (lenw x : word)
(xra xt0 xt1 xt2 xa0 xa3 xa4 xa5 xa6 xa7 xs5 xt3 xt4 xt5 xt6 : word),
rw_cells asegs m1 (bv_unsigned sp + -80) [CB 8 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk asegs m1 lo (bv_unsigned sp + -80) -> model_vm_only (cfg_model md0) (cfg_model md1) ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m1 ->
rw_cells asegs m1 6434236 [C4 e1] ->
HEAPAx A1 (((q, n + 1) :: (p, 48 + cap) :: PBS) ++ LB) LM FRS B1 m1 md1 -> jo_chargeA (ss_costB n) 2 B0 B1 ->
bytes_at asegs m1 S sb -> (sb <> [] -> unpoisoned asegs m1 A_SB S n) ->
rw_cells asegs m1 q [CB (Z.to_nat (n + 1)) junk0] ->
rw_cells asegs m1 p (jhdr_cells JT_STRING 1 (fn_str_to_json_string A4F) pb 0 0 ++ [C8 lenw; C8 x; CB (Z.to_nat (cap - 8)) junk]) ->
opt_pbuf asegs m1 PBS pb -> 8 <= cap -> 1 <= n ->
set_string_root r = JRstrx ->
AJ5 A4L HIx A1 T md1
(MS (mkR xra (wz (bv_unsigned sp + -80)) gp (wz 6434400) xt0 xt1 xt2 (wz (p + 40)) (wz (p + 48)) xa0 (wz S) (wz n) xa3 xa4 xa5 xa6 xa7
(wz q) (wz 2147450880) (wz (p / 8 + 2147450885)) xs5 (wz n) (wz ((p + 48) / 8)) s8 s9 s10 s11 xt3 xt4 xt5 xt6)
F (wz 0x9e9b0) fc None m1 (seg_rom asegs)).
Proof.
intros until xt6. intros FR1 ST1 VM1 HPR1 ERR1 HP1 CH1 SB1 UN1 QB HDR OPB Hcap Hn SR.
unfold SS_STK_A in LOS.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof alloc_ceiling_range as ACR.
assert (INq : In (q, n + 1) ((((q, n + 1) :: (p, 48 + cap) :: PBS) ++ LB) ++ LM)) by (apply in_or_app; left; left; reflexivity).
assert (INp : In (p, 48 + cap) ((((q, n + 1) :: (p, 48 + cap) :: PBS) ++ LB) ++ LM)) by (apply in_or_app; left; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP1 INq) as (_ & _ & HqLO & HqHI & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP1 INp) as (_ & Hpal & HpLO & HpHI & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HP1 INq) as HqIMG. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in HqIMG.
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HP1 INp) as HpIMG. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in HpIMG.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP1) as ND1.
assert (Hqp : q <> p).
{ intros ->. cbn in ND1. inversion ND1 as [|x_ l_ Hni Hnd]; subst. apply Hni. left. reflexivity. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ q (n + 1) p (48 + cap) HP1 INq INp Hqp) as DISJ.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p (48 + cap) 6 HP1 ltac:(right; left; reflexivity) ltac:(lia) ltac:(lia)) as SH6.
replace (p / 8 + 2147450880 + 6) with ((p + 48) / 8 + 2147450880) in SH6 by (rewrite (div8_add p 48) by lia; change (48 / 8) with 6; lia).
unfold jhdr_cells in HDR. cbn [app hl_segs hla_base A4L A4H] in HDR.
pose proof (munch_refl [(p + 48, p + 56)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
stash SB1.
a4l. reenterA asegs A4L HIx asegs_wx HP1.
step.
step. rewrite ?zxb_zero. step. if_false.
step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m2 end.
assert (HP2 : HEAPAx A1 (((q, n + 1) :: (p, 48 + cap) :: PBS) ++ LB) LM FRS B1 m2 md1).
{ eapply (heapA_client_frame A4L HIx); [exact HP1 | | exact WM | assumption].
eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP1 MU).
apply Forall_cons; [right; left; exists p, (48 + cap); cbn [fst snd]; split; [exact INp | lia] | apply Forall_nil]. }
assert (HPR12 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m1 m2).
{ eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx);
[ exact HP1 | intros ? Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb] | clia | ].
apply Forall_cons; [right; left; exists p, (48 + cap); cbn [fst snd]; split; [exact INp | split; [| lia]] | apply Forall_nil].
exact (blk_not_pres _ _ _ _ _ _ _ HP1 ltac:(right; left; reflexivity)). }
unstash SB1.
destruct (src_pres _ _ _ _ _ _ _ LB (bv_unsigned sp) m1 m2 Fs ks S sb HP1 HFS HS1 HS2 HPR12 (conj SB1 UN1)) as [SB2 UN2].

lazymatch type of HDR with rw_cells _ _ _ [?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9] =>
change [c1; c2; c3; c4; c5; c6; c7; c8; c9] with ([c1; c2; c3; c4; c5; c6] ++ ([c7] ++ [c8; c9])) in HDR end.
destruct (proj1 (rw_cells_app asegs m2 p _ _) HDR) as [HDRa HDRr]. cbn [cells_size csize Nat.add] in HDRr. replace (p + Z.of_nat 40) with (p + 40) in HDRr by lia.
destruct (proj1 (rw_cells_app asegs m2 (p + 40) _ _) HDRr) as [LEN2 HDRt]. cbn [cells_size csize Nat.add] in HDRt. replace (p + 40 + Z.of_nat 8) with (p + 48) in HDRt by lia.
evt_done5.
eapply (sc_tail m2 md1 A1 B1 ((q, n + 1) :: (p, 48 + cap) :: PBS) fj e1 q (Z.to_nat (n + 1)) junk0 _ lenw q (n + 1) (48 + cap));
[ eassumption | eassumption | exact VM1 | eapply heap_pres_trans; [exact HPR1 | exact HPR12] | eassumption | exact HP2 | exact CH1 | exact SB2 | exact UN2
| eassumption | lia | left; reflexivity | lia | lia | exact LEN2 | right; left; reflexivity | lia | lia | exact SR
| exists (- n); split; [apply neg_word_negvalA; lia | lia] | ].
intros m3 MU3 WM3 MI3 QB3 LEN3.
assert (LJ0 : length junk0 = Z.to_nat (n + 1)) by (destruct QB as [[[Hwf _] _] _]; exact Hwf).
exists ((p, 48 + cap) :: [(q, n + 1)] ++ PBS). split; [cbn [app]; apply perm_swap|].
cbn [jroot_rep]. split; [lia|].
exists pb, PBS, [(q, n + 1)], cap, (- n), sb. split; [reflexivity|]. split.
{ eapply opt_pbuf_agree; [exact OPB | | apply incl_refl].
eapply agree_on_trans.
- eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros a k Hin. cbn.
assert (INa : In (a, k) ((((q, n + 1) :: (p, 48 + cap) :: PBS) ++ LB) ++ LM)) by (apply in_or_app; left; right; right; apply in_or_app; left; exact Hin).
assert (NEa : p <> a).
{ intros <-. cbn in ND1. inversion ND1 as [|x_ l_ Hni Hnd]; subst. inversion Hnd as [|x2 l2 Hni2 Hnd2]; subst. apply Hni2.
rewrite !map_app. apply in_or_app; left. apply in_or_app; left. exact (in_map blk_addr _ _ Hin). }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ p (48 + cap) a k HP1 INp INa NEa). split; [lia | exact I].
- eapply (agree_of_munch asegs); [exact MU3 | exact WM3 |]. intros a k Hin. cbn.
assert (INa : In (a, k) ((((q, n + 1) :: (p, 48 + cap) :: PBS) ++ LB) ++ LM)) by (apply in_or_app; left; right; right; apply in_or_app; left; exact Hin).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP1 INa) as (_ & _ & _ & Hh & _).
assert (NEa : p <> a).
{ intros <-. cbn in ND1. inversion ND1 as [|x_ l_ Hni Hnd]; subst. inversion Hnd as [|x2 l2 Hni2 Hnd2]; subst. apply Hni2.
rewrite !map_app. apply in_or_app; left. apply in_or_app; left. exact (in_map blk_addr _ _ Hin). }
assert (NEq : q <> a).
{ intros <-. cbn in ND1. inversion ND1 as [|x_ l_ Hni Hnd]; subst. apply Hni. right.
rewrite !map_app. apply in_or_app; left. apply in_or_app; left. exact (in_map blk_addr _ _ Hin). }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ p (48 + cap) a k HP1 INp INa NEa).
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ q (n + 1) a k HP1 INq INa NEq).
split; [lia | split; [lia | split; [lia | exact I]]]. }
split; [exact Hcap|]. split; [lia|]. split; [subst n; lia|].
right. split; [lia|]. exists q, (n + 1), junk, (skipn (Z.to_nat (n + 1)) junk0). split; [reflexivity|]. split; [lia|]. split.
- unfold jhdr_cells. cbn [app hl_segs hla_base A4L A4H].
lazymatch goal with |- rw_cells _ _ _ [?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9] =>
change [c1; c2; c3; c4; c5; c6; c7; c8; c9] with ([c1; c2; c3; c4; c5; c6] ++ ([c7] ++ [c8; c9])) end.
apply (proj2 (rw_cells_app asegs m3 p _ _)). cbn [cells_size csize Nat.add]. replace (p + Z.of_nat 40) with (p + 40) by lia. split.
+ eapply (rw_cells_transport asegs _ m2 m3); [exact HDRa | exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize Nat.add]; lia].
+ apply (proj2 (rw_cells_app asegs m3 (p + 40) _ _)). cbn [cells_size csize Nat.add]. replace (p + 40 + Z.of_nat 8) with (p + 48) by lia. split.
* rewrite <- (neg_word_negvalA n) by lia. exact LEN3.
* eapply (rw_cells_transport asegs _ m2 m3); [exact HDRt | exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize Nat.add]; lia].
- replace (Z.to_nat (n + 1)) with (Z.to_nat (n + 1)) by reflexivity. cbn [hl_segs hla_base A4L A4H]. exact QB3.
Qed.

Lemma sc_grow : forall (m1 : word -> option byte) (md1 : config) (A1 : ASA A4L HIx) (fj : list byte) (e1 : word)
(PBS DBS : list blk) (cap pb len0 : Z) (junk : list byte) (x : word)
(xra xt0 xt1 xt2 xa0 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs7 xt3 xt4 xt5 xt6 : word),
rw_cells asegs m1 (bv_unsigned sp + -80) [CB 8 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk asegs m1 lo (bv_unsigned sp + -80) -> model_vm_only (cfg_model md0) (cfg_model md1) ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m1 ->
rw_cells asegs m1 6434236 [C4 e1] ->
HEAPAx A1 (((p, 48 + cap) :: DBS ++ PBS) ++ LB) LM FRS B0 m1 md1 ->
bytes_at asegs m1 S sb -> (sb <> [] -> unpoisoned asegs m1 A_SB S n) ->
rw_cells asegs m1 p (jhdr_cells JT_STRING 1 (fn_str_to_json_string A4F) pb 0 0 ++ [C8 (wz len0); C8 x; CB (Z.to_nat (cap - 8)) junk]) ->
opt_pbuf asegs m1 PBS pb -> 8 <= cap -> 1 <= n ->
xstr A4H A4F m1 ((p, 48 + cap) :: DBS ++ PBS) p 1 ->
-2^63 <= len0 < 2^63 -> Z.abs len0 <= n ->
((0 <= len0 /\ DBS = []) \/ (len0 < 0 /\ exists pd pdn, DBS = [(pd, pdn)] /\ x = wz pd)) ->
set_string_root r = JRstrx ->
AJ5 A4L HIx A1 T md1
(MS (mkR xra (wz (bv_unsigned sp + -80)) gp (wz 6434400) xt0 xt1 xt2 (wz (p + 40)) (wz (p + 48)) xa0 (wz S) (wz n) xa3 xa4 xa5 xa6 xa7
xs2 (wz 2147450880) (wz (p / 8 + 2147450885)) xs5 xs6 xs7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
F (wz 0x9e960) fc None m1 (seg_rom asegs)).
Proof.
intros until xt6. intros FR1 ST1 VM1 HPR1 ERR1 HP1 SB1 UN1 HDR OPB Hcap Hn ROOT LEN0R LABS FLAG SR.
unfold SS_STK_A in LOS. unfold ss_costB in BB0.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof alloc_ceiling_range as ACR.
assert (INp1 : In (p, 48 + cap) ((((p, 48 + cap) :: DBS ++ PBS) ++ LB) ++ LM)) by (apply in_or_app; left; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP1 INp1) as (_ & Hpal & HpLO & HpHI & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HP1 INp1) as HpIMG. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in HpIMG.
unfold jhdr_cells in HDR. cbn [app hl_segs hla_base A4L A4H] in HDR.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
stash SB1.
a4l. reenterA asegs A4L HIx asegs_wx HP1.
step. step. step. step.

evt_done5.
eapply (hiA_malloc A4L HIx) with (n := n + 1) (u := UWpaid) (lo := lo) (errv := e1);
[ heap_nowA A4L HIx HP1 MU WM MI | .. ].
all: rewrite ?unsigned_lit by lia.
1: eassumption.
1: exact LO.
1: cbn [hl_stack_A A4L]; lia.
1: clear - SPA; Z.div_mod_to_equations; lia.
1: lia.
1: cbn [hl_segs hl_tp hla_base A4L A4H]; unfold A_TP; eassumption.
1: reflexivity.
1: reflexivity.
1: lia.
1: cbn; exact I.
1: cbn; exact I.
1: lia.
1: cbn [uw_cost]; lia.
intros ms2 m2 md2 A2 q e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS.
cbn [hl_segs hl_tp hla_base A4L A4H] in ST2, HPR2, ERR2, OUT2. unfold A_TP in ERR2. change (6434400 - 164) with 6434236 in ERR2.
rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in ST2, HPR2 by lia.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR1; [| left; cbn; lia]. cbn [hl_segs hla_base A4L A4H] in FR1.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in HDR; [| eapply client_range_block; [apply in_or_app; left; apply in_or_app; left; left; reflexivity | lia | cbn; lia]]. cbn [hl_segs hla_base A4L A4H] in HDR.
unstash SB1.
destruct (src_pres _ _ _ _ _ _ _ (((p, 48 + cap) :: DBS ++ PBS) ++ LB) (bv_unsigned sp + -80) m1 m2 Fs ks S sb HP1 HFS HS1 HS2 HPR2 (conj SB1 UN1)) as [SB2 UN2].
assert (AG2 : agree_on asegs ((p, 48 + cap) :: DBS ++ PBS) m1 m2).
{ eapply (agree_of_heap_pres asegs A4H); [exact HPR2 | reflexivity | intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb]. }
assert (HPR02 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m2).
{ eapply heap_pres_trans; [exact HPR1|]. eapply heap_pres_weaken; [exact HPR2 | lia |].
intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb]. }
pose proof (model_vm_only_trans _ _ _ VM1 VM2) as VM02.
assert (CH2 : jo_chargeA (ss_costB n) 2 B0 (charge B0 (16 * (n + 1) + 512) (uw_cost UWpaid))) by (unfold jo_chargeA, ss_costB, charge; cbn [bB bD uw_cost]; split; lia).
clear MU WM MI.
destruct OUT2 as [(-> & _ & HP2) | (Hq & [junk0 QB] & HP2)].
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
replace (ret_pc (wz 0x9e970)) with (wz 0x9e970) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
reenterA asegs A4L HIx asegs_wx HP2.
step. if_lit. step. step.
evt_done5.
eapply (sc_exit m2 md2 A2 _ ((p, 48 + cap) :: DBS ++ PBS) fj 0 e2); [exact FR1 | exact ST2 | exact VM02 | exact HPR02 | exact ERR2 | exact HP2 | exact CH2 | | |].
+ rewrite SR. split; [lia|]. eapply (QrIB.Mq0.xstr_agree A4H A4F); [exact ROOT | exact AG2 | apply incl_refl].
+ intros _. apply rw_cells_app with (cs1 := [_;_;_;_;_;_]) in HDR as [_ LEN1]. cbn [cells_size csize Nat.add] in LEN1.
apply rw_cells_app with (cs1 := [_]) in LEN1 as [LEN1 _]. replace (p + Z.of_nat 40) with (p + 40) in LEN1 by lia.
refine (str_lenA_of_cell _ _ _ _ len0 LEN1 eq_refl _ LABS). clear - LABS LSB. subst n. lia.
+ intros Hf. exfalso. rewrite (string_root_true r SR) in Hf. discriminate.
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP2) as ND2.
assert (INp2 : In (p, 48 + cap) ((q, n + 1) :: ((p, 48 + cap) :: DBS ++ PBS) ++ LB)) by (right; left; reflexivity).
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p (48 + cap) 5 HP2 INp2 ltac:(lia) ltac:(lia)) as SH5.
replace (p / 8 + 2147450880 + 5) with (p / 8 + 2147450885) in SH5 by lia.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p (48 + cap) 6 HP2 INp2 ltac:(lia) ltac:(lia)) as SH6.
replace (p / 8 + 2147450880 + 6) with ((p + 48) / 8 + 2147450880) in SH6 by (rewrite (div8_add p 48) by lia; change (48 / 8) with 6; lia).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ q (n + 1) HP2 ltac:(apply in_or_app; left; left; reflexivity)) as (_ & _ & HqLO & HqHI & _).
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
replace (ret_pc (wz 0x9e970)) with (wz 0x9e970) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
stash SB2.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_falsex. step.
step. rewrite ?zxb_zero. step. if_false.
step. step. step.
rewrite (unsigned_lit (p + 48)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
step. step.
destruct FLAG as [(Hl0 & ->) | (Hl0 & pd & pdn & -> & ->)].
+
if_truex. cbn [app] in HP2, OPB, AG2.
unstash SB2.
evt_done5.
eapply (sc_grow2 m2 md2 A2 _ fj e2 PBS q cap pb junk0 junk (wz len0) x);
[ exact FR1 | exact ST2 | exact VM02 | exact HPR02 | exact ERR2 | exact HP2 | exact CH2 | exact SB2 | exact UN2 | exact QB
| unfold jhdr_cells; cbn [app]; exact HDR | | exact Hcap | exact Hn | exact SR ].
eapply opt_pbuf_agree; [exact OPB | exact AG2 | intros b Hb; right; exact Hb].
+
if_falsex. cbn [app] in HP2, AG2, ND2, INp2.
assert (Hqpd : q <> pd). { intros Eq. cbn in ND2. inversion ND2 as [|x_ l_ Hni Hnd]; subst x_ l_. apply Hni. cbn. right; left. symmetry; exact Eq. }
assert (Hppd : p <> pd). { intros Epd. cbn in ND2. inversion ND2 as [|x_ l_ Hni Hnd]; subst x_ l_. inversion Hnd as [|x2 l2 Hni2 Hnd2]; subst x2 l2. apply Hni2. cbn. left. symmetry; exact Epd. }
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ pd pdn HP2 ltac:(apply in_or_app; left; right; right; left; reflexivity)) as (_ & _ & Hpd0 & _).
step. step. rewrite ?zxb_zero. step. if_false.
step. step.
evt_done5.
eapply (hiA_free A4L HIx) with (p := pd) (u := UWpaid) (lo := lo) (errv := e2);
[ heap_nowA A4L HIx HP2 MU WM MI | right; exists pdn; right; right; left; reflexivity | .. ].
all: rewrite ?unsigned_lit by lia.
1: eassumption.
1: exact LO.
1: cbn [hl_stack_A A4L]; lia.
1: clear - SPA; Z.div_mod_to_equations; lia.
1: lia.
1: cbn [hl_segs hl_tp hla_base A4L A4H]; unfold A_TP; eassumption.
1: reflexivity.
1: reflexivity.
1: split; cbn; exact I.
1: cbn [charge bB uw_cost]; lia.
1: destruct (Z.eqb pd 0); cbn [charge bD uw_cost]; lia.
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3.
cbn [hl_segs hl_tp hla_base A4L A4H] in ST3, HPR3, ERR3, HP3. unfold A_TP in ERR3. change (6434400 - 164) with 6434236 in ERR3.
rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in ST3, HPR3 by lia.
rewrite (lb_remove_other pd) in HPR3, HP3 by (cbn; lia). rewrite (lb_remove_other pd) in HPR3, HP3 by (cbn; lia). rewrite lb_remove_head in HPR3, HP3.
replace (if pd =? 0 then 0 else uw_cost UWpaid) with 1 in HP3 by (destruct (Z.eqb_spec pd 0); [lia | reflexivity]).
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FR1; [| left; cbn; lia]. cbn [hl_segs hla_base A4L A4H] in FR1.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in HDR; [| eapply client_range_block; [right; left; reflexivity | lia | cbn; lia]]. cbn [hl_segs hla_base A4L A4H] in HDR.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in QB; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs hla_base A4L A4H] in QB.
unstash SB2.
lazymatch type of HPR3 with heap_pres _ (?LX ++ LM ++ _) _ ?ma _ =>
destruct (src_pres _ _ _ _ _ _ _ LX (bv_unsigned sp + -80) ma m3 Fs ks S sb HP2 HFS HS1 HS2 HPR3) as [SB3 UN3] end.
{ exact (conj SB2 UN2). }
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI3. cbn [hl_segs hla_base A4L A4H] in MI3.
clear MU WM. pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m3) as MU. pose proof (wmono_refl asegs m3) as WM.
replace (ret_pc (wz 649640)) with (wz 649640) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
stash SB3.
reenterA asegs A4L HIx asegs_wx HP3.
step. step.
unstash SB3.
evt_done5.
eapply (sc_grow2 m3 md3 A3 _ fj e2 PBS q cap pb junk0 junk (wz len0) (wz pd));
[ exact FR1 | exact ST3 | exact (model_vm_only_trans _ _ _ VM02 VM3) | | exact ERR3 | exact HP3 | | exact SB3 | exact UN3 | exact QB
| unfold jhdr_cells; cbn [app]; exact HDR | | exact Hcap | exact Hn | exact SR ].
* eapply heap_pres_trans; [exact HPR02|]. eapply heap_pres_weaken; [exact HPR3 | lia |].
intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; right; right; apply in_or_app; right; exact Hb | right; exact Hb].
* unfold jo_chargeA, ss_costB, charge; cbn [bB bD uw_cost]; split; lia.
* eapply opt_pbuf_agree; [exact OPB | | apply incl_refl]. eapply agree_on_trans.
-- eapply agree_on_incl; [exact AG2 | intros b Hb; right; right; exact Hb].
-- eapply (agree_of_heap_pres asegs A4H); [exact HPR3 | reflexivity | intros b Hb; apply in_or_app; left; right; right; apply in_or_app; left; exact Hb].
Qed.

Lemma sc_main : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (A : ASA A4L HIx),
HEAPAx A (BS ++ LB) LM FRS B0 m0 md0 -> stk asegs m0 lo (bv_unsigned sp) -> rw_cells asegs m0 6434236 [C4 errv] ->
jroot_repA r m0 BS p ->
bytes_at asegs m0 S sb -> (sb <> [] -> unpoisoned asegs m0 A_SB S n) ->
AJ5 A4L HIx A T md0
(MS (mkR ra sp gp (wz 6434400) t0 t1 t2 s0 s1 (wz p) (wz S) (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x9e8d0) fc None m0 (seg_rom asegs)).
Proof.
intros until A. intros HP ST ERR RR SB UN.
unfold SS_STK_A in LOS.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (wmono_refl asegs m0) as WM.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND0.
assert (ND : List.NoDup (map blk_addr BS)) by exact (nodup_app_l' _ _ (nodup_app_l' _ _ ND0)).
pose proof alloc_ceiling_range as ACR.
assert (Hn0 : 0 <= n) by (subst n; lia).
assert (CH0 : jo_chargeA (ss_costB n) 2 B0 B0) by (unfold jo_chargeA, ss_costB; split; lia).
carve_frame 80%nat ST.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m0) as MU.
stash SB.
a4l. reenterA asegs A4L HIx asegs_wx HP.
do 10 step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => rename mX into m2 end.
unstash SB.

assert (XHP : HEAPAx A (BS ++ LB) LM FRS B0 m2 md0) by (heap_nowA A4L HIx HP MU WM MI).
assert (XHPR : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m2).
{ eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb] | clia | solve_clientWA A4L HIx HP]. }
assert (XAG : agree_on asegs BS m0 m2).
{ eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros bb kk Hb. cbn.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ bb kk HP ltac:(apply in_or_app; left; apply in_or_app; left; exact Hb)) as (_ & _ & _ & Hh & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hh. split; [lia | exact I]. }
destruct (src_pres _ _ _ _ _ _ _ LB (bv_unsigned sp) m0 m2 Fs ks S sb HP HFS HS1 HS2 XHPR (conj SB UN)) as [SB2 UN2].
destruct (jroot_null_decA r) as [Er | NN].
{
rewrite Er in RR. destruct RR as [Ep EB]. rewrite Ep. if_lit. step. step.
evt_done5.
eapply (sc_exit m2 md0 A B0 [] _ 0 errv); [eassumption | eassumption | apply model_vm_only_refl | exact XHPR | eassumption | rewrite EB in XHP; exact XHP | exact CH0 | | |].
- rewrite Er. split; [exact Ep | reflexivity].
- intros Hs. exfalso. rewrite Er in Hs. discriminate.
- intros _. symmetry. exact EB. }
destruct (jroot_str_casesA r m0 BS p RR NN ND) as (Hp & CASES).
assert (PB : exists pn, In (p, pn) BS).
{ destruct CASES as [((pb & PBS & DBS & cap & len0 & str & EBS & _) & _) | (_ & _ & n0 & ty & tojs & pb & udel & ud & rest & INp & _)];
[exists (48 + cap); rewrite EBS; left; reflexivity | exists n0; exact INp]. }
destruct PB as (pn & INp).
assert (INpA : In (p, pn) (BS ++ LB)) by (apply in_or_app; left; exact INp).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p pn XHP ltac:(apply in_or_app; left; exact INpA)) as (Hpn0 & Hpal & Hplo & Hphi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ p pn XHP ltac:(apply in_or_app; left; exact INpA)) as Hpimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hpimg.
assert (N48 : 48 <= pn).
{ destruct CASES as [((pb & PBS & DBS & cap & len0 & str & EBS & _ & Hc & _) & _) | (_ & _ & n0 & ty & tojs & pb & udel & ud & rest & INp' & _ & N48' & _)].
- rewrite (nodup_addr_size BS p pn (48 + cap) ND INp ltac:(rewrite EBS; left; reflexivity)). lia.
- rewrite (nodup_addr_size BS p pn n0 ND INp INp'). exact N48'. }
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p pn 0 XHP INpA ltac:(lia) ltac:(lia)) as SH0. rewrite Z.add_0_r in SH0.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p pn 5 XHP INpA ltac:(lia) ltac:(lia)) as SH5. replace (p / 8 + 2147450880 + 5) with (p / 8 + 2147450885) in SH5 by lia.
if_falsex.
do 3 step.
asan_chkA.
step. step. step. step. if_falsex.
destruct CASES as [(X & SR) | (SR & NSR & n0 & ty & tojs & pb & udel & ud & rest & INp' & SZ & N48' & TY & NS & HDR)].
2:{
rewrite (nodup_addr_size BS p pn n0 ND INp INp') in *.
unfold jhdr_cells in HDR, SZ. cbn [app hl_segs hla_base A4L A4H] in HDR, SZ.
apply (rw_cells_agree asegs BS m0 m2) in HDR; [| exact XAG | exists p, n0; split; [exact INp' | cbn [cells_size csize Nat.add app] in SZ |- *; rewrite <- SZ; lia]].
unfold JT_STRING in NS. step. rewrite sx32_small by lia. step. step. if_truex.
evt_done5.
eapply (sc_exit m2 md0 A B0 BS _ 0 errv); [eassumption | eassumption | apply model_vm_only_refl | exact XHPR | eassumption | exact XHP | exact CH0 | | |].
- rewrite SR. eapply (QrIB.Mq0.jroot_rep_agree A4H A4F); [exact RR | exact XAG | apply incl_refl].
- intros Hs. exfalso. rewrite NSR in Hs. discriminate.
- intros _. reflexivity. }

pose proof (QrIB.Mq0.xstr_agree A4H A4F _ _ _ _ _ _ X XAG (incl_refl _)) as X2.
destruct X as (pb & PBS & DBS & cap & len0 & str & EBS & OPB & Hcap & Hlen0 & Hstr & ALT).
rewrite (nodup_addr_size BS p pn (48 + cap) ND INp ltac:(rewrite EBS; left; reflexivity)) in *.
assert (OPB2 : opt_pbuf asegs m2 PBS pb).
{ eapply opt_pbuf_agree; [exact OPB | exact XAG | rewrite EBS; intros b Hb; right; apply in_or_app; right; exact Hb]. }
assert (HDRX : exists tl, rw_cells asegs m0 p (jhdr_cells JT_STRING 1 (fn_str_to_json_string A4F) pb 0 0 ++ C8 (wz len0) :: tl)
/\ Z.of_nat (cells_size (jhdr_cells JT_STRING 1 (fn_str_to_json_string A4F) pb 0 0 ++ C8 (wz len0) :: tl)) = 48 + cap).
{ destruct ALT as [(_ & _ & _ & jk & H) | (_ & pd & pdn & jk & jk2 & _ & _ & H & _)]; eexists; (split; [exact H|]);
unfold jhdr_cells; rewrite cells_size_app; cbn [cells_size csize Nat.add app]; lia. }
destruct HDRX as (tl & HDR & SZ). unfold jhdr_cells in HDR, SZ. cbn [app hl_segs hla_base A4L A4H] in HDR, SZ.
apply (rw_cells_agree asegs BS m0 m2) in HDR; [| exact XAG | exists p, (48 + cap); split; [rewrite EBS; left; reflexivity | rewrite SZ; lia]].
step. rewrite sx32_small by (unfold JT_STRING; lia). step. step. unfold JT_STRING. if_lit.
step. asan_chkA.
step. step.
clear HDR.
destruct ALT as [(Hl0 & EDBS & Hfit & jk & CELLS) | (Hl0 & pd & pdn & jk & jk2 & EDBS & Hpdn & CELLS & PD)].
-
subst DBS. cbn [app] in EBS.
if_falsex.
step. step. step. step.
unfold jhdr_cells in CELLS. cbn [app hl_segs hla_base A4L A4H] in CELLS.
apply (rw_cells_agree asegs BS m0 m2) in CELLS; [| exact XAG | exists p, (48 + cap); split; [rewrite EBS; left; reflexivity | cbn [cells_size csize Nat.add app]; lia]].
apply rw_cells_app with (cs1 := [_;_;_;_;_;_]) in CELLS as [HD LEN]. cbn [cells_size csize Nat.add] in LEN. change (p + Z.of_nat 40) with (p + 40) in LEN.
apply rw_cells_app with (cs1 := [_]) in LEN as [LEN DATA]. cbn [cells_size csize Nat.add] in DATA. change (p + 40 + Z.of_nat 8) with (p + 40 + 8) in DATA.
replace (p + 40 + 8) with (p + 48) in DATA by lia.
destruct (Z.lt_ge_cases len0 n) as [GROW | FIT].
+
if_falsex.
pose proof (Q6Vi.Mq1.rw_cells_CB_word asegs _ _ _ _ DATA ltac:(lia)) as DATA'.
assert (HDRG : rw_cells asegs m2 p (jhdr_cells JT_STRING 1 (fn_str_to_json_string A4F) pb 0 0 ++
[C8 (wz len0); C8 (le_bytes_to_word (firstn 8 (str ++ [Z_to_bv 8 0] ++ jk))); CB (Z.to_nat (cap - 8)) (skipn 8 (str ++ [Z_to_bv 8 0] ++ jk))])).
{ unfold jhdr_cells. cbn [app]. replace (Z.to_nat (cap - 8)) with (Z.to_nat cap - 8)%nat by lia. Q6Vi.Mq1.hdr_join HD LEN DATA'. }
evt_done5.
eapply sc_grow with (A1 := A) (PBS := PBS) (DBS := []) (cap := cap) (pb := pb);
[ eassumption | eassumption | apply model_vm_only_refl | exact XHPR | eassumption | rewrite EBS in XHP; exact XHP | exact SB2 | exact UN2 | exact HDRG
| exact OPB2 | exact Hcap | lia | rewrite EBS in X2; exact X2 | lia | lia | left; split; [lia | reflexivity] | exact SR ].
+
if_truex.
step. if_lit. step. step.
evt_done5.
eapply sc_tail with (A1 := A) (BS1 := BS) (D := p + 48) (k := Z.to_nat cap) (junk := str ++ [Z_to_bv 8 0] ++ jk) (lenw := wz len0) (bD := p) (szD := 48 + cap) (pn := 48 + cap);
[ eassumption | eassumption | apply model_vm_only_refl | exact XHPR | eassumption | exact XHP | exact CH0 | exact SB2 | exact UN2 | exact DATA | lia
| rewrite EBS; left; reflexivity | lia | lia | exact LEN | rewrite EBS; left; reflexivity | lia | left; lia | exact SR
| exists n; split; [reflexivity | lia] |].
intros m3 MU3 WM3 MI3 DST3 LEN3.
exists BS. split; [apply Permutation_refl|]. split; [exact Hp|].
exists pb, PBS, (@nil blk), cap, n, sb. split; [exact EBS|]. split.
{ eapply opt_pbuf_agree; [exact OPB2 | | apply incl_refl]. eapply (agree_of_munch asegs); [exact MU3 | exact WM3 |].
intros a k' Hin.
assert (INa : In (a, k') ((BS ++ LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; left; rewrite EBS; right; exact Hin).
assert (Hpa : p <> a).
{ intros <-. pose proof ND as NDB. rewrite EBS in NDB. cbn in NDB. inversion NDB as [|x_ l_ Hni Hnd]; subst x_ l_. apply Hni. exact (in_map blk_addr _ _ Hin). }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ p (48 + cap) a k' XHP ltac:(apply in_or_app; left; exact INpA) INa Hpa) as D1.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k' XHP INa) as (Hk' & _ & _ & Hh & _).
cbn. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
split; [lia|]. split; [lia|]. split; [subst n; lia|].
left. split; [lia|]. split; [reflexivity|]. split; [lia|]. exists (skipn (Z.to_nat (n + 1)) (str ++ [Z_to_bv 8 0] ++ jk)).
unfold jhdr_cells. cbn [app hl_segs hla_base A4L A4H].
lazymatch type of MU3 with munch ?W _ _ =>
apply (rw_cells_transport asegs W m2 m3) in HD; [| exact MU3 | exact WM3 | cbn [disjoint_from]; cbn; lia] end.
Q6Vi.Mq1.hdr_join HD LEN3 DST3.
-
subst DBS. cbn [app] in EBS.
if_truex.
unfold jhdr_cells in CELLS. cbn [app hl_segs hla_base A4L A4H] in CELLS.
apply (rw_cells_agree asegs BS m0 m2) in CELLS; [| exact XAG | exists p, (48 + cap); split; [rewrite EBS; left; reflexivity | cbn [cells_size csize Nat.add app]; lia]].
assert (INpdA : In (pd, pdn) ((BS ++ LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; left; rewrite EBS; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ pd pdn XHP INpdA) as (Hpdn0 & Hpdal & Hpdlo & Hpdhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ pd pdn XHP INpdA) as Hpdimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hpdimg.
assert (Hppd : p <> pd).
{ intros E. pose proof ND as NDB. rewrite EBS in NDB. cbn in NDB. inversion NDB as [|x_ l_ Hni Hnd]; subst x_ l_. apply Hni. left. symmetry. exact E. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ p (48 + cap) pd pdn XHP ltac:(apply in_or_app; left; exact INpA) INpdA Hppd) as DPD.
apply (rw_cells_agree asegs BS m0 m2) in PD; [| exact XAG | exists pd, pdn; split; [rewrite EBS; right; left; reflexivity | cbn; lia]].
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p (48 + cap) 6 XHP INpA ltac:(lia) ltac:(lia)) as SH6.
replace (p / 8 + 2147450880 + 6) with ((p + 48) / 8 + 2147450880) in SH6 by (rewrite (div8_add p 48) by lia; change (48 / 8) with 6; lia).
step.
destruct (Z.eq_dec n 0) as [N0 | N1].
2:{
if_falsex.
step. rewrite ?zxb_zero. step. if_false.
step. step. rewrite Q6Vi.Mq1.neg_word_negval by lia. step. step. if_truex.
step. rewrite (unsigned_lit (p + 48)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
step. step. rewrite ?zxb_zero. step. if_false.
apply rw_cells_app with (cs1 := [_;_;_;_;_;_]) in CELLS as [HD LEN]. cbn [cells_size csize Nat.add] in LEN. change (p + Z.of_nat 40) with (p + 40) in LEN.
apply rw_cells_app with (cs1 := [_]) in LEN as [LEN PDC]. cbn [cells_size csize Nat.add] in PDC. change (p + 40 + Z.of_nat 8) with (p + 40 + 8) in PDC.
replace (p + 40 + 8) with (p + 48) in PDC by lia.
step. step. step.
destruct (Z.lt_ge_cases (- len0) n) as [GROW | FIT].
*
if_truex.
evt_done5.
eapply sc_grow with (A1 := A) (PBS := PBS) (DBS := [(pd, pdn)]) (cap := cap) (pb := pb);
[ eassumption | eassumption | apply model_vm_only_refl | exact XHPR | eassumption | rewrite EBS in XHP; exact XHP | exact SB2 | exact UN2
| unfold jhdr_cells; cbn [app]; Q6Vi.Mq1.hdr_join HD LEN PDC
| exact OPB2 | exact Hcap | lia | rewrite EBS in X2; exact X2 | lia | lia | right; split; [lia | exists pd, pdn; split; reflexivity] | exact SR ].
*
if_falsex.
step. if_lit. step.
evt_done5.
eapply sc_tail with (A1 := A) (BS1 := BS) (D := pd) (k := Z.to_nat pdn) (junk := str ++ [Z_to_bv 8 0] ++ jk2) (lenw := wz len0) (bD := pd) (szD := pdn) (pn := 48 + cap);
[ eassumption | eassumption | apply model_vm_only_refl | exact XHPR | eassumption | exact XHP | exact CH0 | exact SB2 | exact UN2 | exact PD | lia
| rewrite EBS; right; left; reflexivity | lia | lia | exact LEN | rewrite EBS; left; reflexivity | lia | lia | exact SR
| exists (- n); split; [apply neg_word_negvalA; lia | lia] |].
intros m3 MU3 WM3 MI3 DST3 LEN3.
exists BS. split; [apply Permutation_refl|]. split; [exact Hp|].
exists pb, PBS, [(pd, pdn)], cap, (- n), sb. split; [exact EBS|]. split.
{ eapply opt_pbuf_agree; [exact OPB2 | | apply incl_refl]. eapply (agree_of_munch asegs); [exact MU3 | exact WM3 |].
intros a k' Hin.
pose proof ND as NDB. rewrite EBS in NDB.
assert (INa : In (a, k') ((BS ++ LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; left; rewrite EBS; right; right; exact Hin).
assert (Hpa : p <> a).
{ intros <-. cbn in NDB. inversion NDB as [|x_ l_ Hni Hnd]; subst x_ l_. apply Hni. right. exact (in_map blk_addr _ _ Hin). }
assert (Hpda : pd <> a).
{ intros <-. cbn in NDB. inversion NDB as [|x_ l_ Hni Hnd]; subst x_ l_. inversion Hnd as [|x2_ l2_ Hni2 Hnd2]; subst x2_ l2_. apply Hni2. exact (in_map blk_addr _ _ Hin). }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ p (48 + cap) a k' XHP ltac:(apply in_or_app; left; exact INpA) INa Hpa) as D1.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ pd pdn a k' XHP INpdA INa Hpda) as D2.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k' XHP INa) as (Hk' & _ & _ & Hh & _).
cbn. split; [lia|]. split; [(clear - Hpdn FIT D2 Hpdn0; lia)|]. split; [(clear - Hcap D1; lia) | exact I]. }
split; [lia|]. split; [lia|]. split; [subst n; lia|].
right. split; [lia|]. exists pd, pdn, jk, (skipn (Z.to_nat (n + 1)) (str ++ [Z_to_bv 8 0] ++ jk2)). split; [reflexivity|]. split; [lia|]. split; [| exact DST3].
unfold jhdr_cells. cbn [app hl_segs hla_base A4L A4H].
lazymatch type of MU3 with munch ?W _ _ =>
apply (rw_cells_transport asegs W m2 m3) in HD; [| exact MU3 | exact WM3 | cbn [disjoint_from]; cbn; (clear - Hcap Hpdn0 DPD Hphi LO Hplo; lia)];
apply (rw_cells_transport asegs W m2 m3) in PDC; [| exact MU3 | exact WM3 | cbn [disjoint_from]; cbn [cells_size csize Nat.add]; (clear - Hcap Hl0 Hpdn DPD Hphi LO Hplo; lia)] end.
rewrite Q6Vi.Mq1.neg_word_negval in LEN3 by lia.
Q6Vi.Mq1.hdr_join HD LEN3 PDC. }

if_truex.
step. step. step. step. step.
rewrite (unsigned_lit (p + 48)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
step. rewrite ?zxb_zero. step. if_false.
step. step. step.
evt_done5.
eapply (hiA_free A4L HIx) with (p := pd) (u := UWpaid) (lo := lo) (errv := errv);
[ exact XHP | right; exists pdn; apply in_or_app; left; rewrite EBS; right; left; reflexivity | .. ].
all: rewrite ?unsigned_lit by lia.
1: eassumption.
1: exact LO.
1: cbn [hl_stack_A A4L]; lia.
1: clear - SPA; Z.div_mod_to_equations; lia.
1: lia.
1: cbn [hl_segs hl_tp hla_base A4L A4H]; unfold A_TP; eassumption.
1: reflexivity.
1: reflexivity.
1: split; cbn; exact I.
1: unfold ss_costB in BB0; lia.
1: destruct (Z.eqb pd 0); cbn [uw_cost]; lia.
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3.
cbn [hl_segs hl_tp hla_base A4L A4H] in ST3, HPR3, ERR3, HP3. unfold A_TP in ERR3. change (6434400 - 164) with 6434236 in ERR3.
rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in ST3, HPR3 by lia.
rewrite EBS in HPR3, HP3. cbn [app] in HPR3, HP3.
rewrite (lb_remove_other pd) in HPR3, HP3 by (cbn; lia). rewrite lb_remove_head in HPR3, HP3.
replace (if pd =? 0 then 0 else uw_cost UWpaid) with 1 in HP3 by (destruct (Z.eqb_spec pd 0); [lia | reflexivity]).
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. cbn [hl_segs hla_base A4L A4H] in FR.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in CELLS; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs hla_base A4L A4H] in CELLS.
lazymatch type of HPR3 with heap_pres _ (?LX ++ LM ++ _) _ ?ma _ =>
destruct (src_pres _ _ _ _ _ _ _ LX (bv_unsigned sp + -80) ma m3 Fs ks S sb XHP HFS HS1 HS2 HPR3 (conj SB2 UN2)) as [SB3 UN3] end.
assert (OPB3 : opt_pbuf asegs m3 PBS pb).
{ eapply opt_pbuf_agree; [exact OPB2 | | apply incl_refl].
eapply (agree_of_heap_pres asegs A4H); [exact HPR3 | reflexivity | intros b Hb; apply in_or_app; left; right; apply in_or_app; left; exact Hb]. }
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI3. cbn [hl_segs hla_base A4L A4H] in MI3.
assert (INp3 : In (p, 48 + cap) (((p, 48 + cap) :: PBS ++ LB))) by (left; reflexivity).
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p (48 + cap) 5 HP3 INp3 ltac:(lia) ltac:(lia)) as SH5c.
replace (p / 8 + 2147450880 + 5) with (p / 8 + 2147450885) in SH5c by lia.
clear MU WM. pose proof (munch_refl [(p + 40, p + 48)] m3) as MU. pose proof (wmono_refl asegs m3) as WM.
replace (ret_pc (wz 0x9ea18)) with (wz 0x9ea18) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
stash SB3.
reenterA asegs A4L HIx asegs_wx HP3.
step. rewrite ?zxb_zero. step. if_false.
step. stepz. step. step. step. step.
step. step. step. step.
if_truex. step. if_lit. step. step.
unstash SB3.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => rename mX into m4 end.
lazymatch goal with H : rw_cells asegs m4 p ?cs |- _ => rename H into CELLS4 end.
assert (HP4 : HEAPAx A3 (((p, 48 + cap) :: PBS) ++ LB) LM FRS (charge B0 512 1) m4 md3).
{ eapply (heapA_client_frame A4L HIx); [exact HP3 | | exact WM | assumption].
eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP3 MU).
apply Forall_cons; [right; left; exists p, (48 + cap); cbn [fst snd]; split; [apply in_or_app; left; left; reflexivity | lia] | apply Forall_nil]. }
assert (HPR34 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m3 m4).
{ eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx);
[ exact HP3 | intros ? Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; right; apply in_or_app; right; exact Hb | right; exact Hb] | clia | ].
apply Forall_cons; [right; left; exists p, (48 + cap); cbn [fst snd]; split; [apply in_or_app; left; left; reflexivity | split; [| lia]] | apply Forall_nil].
exact (blk_not_pres A3 ((p, 48 + cap) :: PBS) _ _ _ _ _ HP3 ltac:(left; reflexivity)). }
assert (HPR04 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m4).
{ eapply heap_pres_trans; [exact XHPR|]. eapply heap_pres_trans; [| exact HPR34].
eapply heap_pres_weaken; [exact HPR3 | lia |].
intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; right; apply in_or_app; right; exact Hb | right; exact Hb]. }
destruct (src_pres _ _ _ _ _ _ _ LB (bv_unsigned sp) m3 m4 Fs ks S sb HP3 HFS HS1 HS2 HPR34 (conj SB3 UN3)) as [SB4 UN4].
apply rw_cells_app with (cs1 := [_;_;_;_;_;_]) in CELLS4 as [HD LEN]. cbn [cells_size csize Nat.add] in LEN. change (p + Z.of_nat 40) with (p + 40) in LEN.
apply rw_cells_app with (cs1 := [_]) in LEN as [LEN DATA]. cbn [cells_size csize Nat.add] in DATA. change (p + 40 + Z.of_nat 8) with (p + 40 + 8) in DATA.
replace (p + 40 + 8) with (p + 48) in DATA by lia.
apply (rw_cells_recast asegs _ _ _ [CB (Z.to_nat cap) (le8 (wz pd) ++ jk)]) in DATA;
[| split; [| exact I]; cbn [cell_wf]; rewrite length_app, length_le8; destruct DATA as [[[_ [Hw _]] _] _]; cbn [cell_wf] in Hw; lia
| cbn [cells_bytes cbytes app]; rewrite <- app_assoc; reflexivity | cbn; lia].
evt_done5.
eapply sc_tail with (A1 := A3) (BS1 := (p, 48 + cap) :: PBS) (D := p + 48) (k := Z.to_nat cap) (junk := le8 (wz pd) ++ jk) (bD := p) (szD := 48 + cap) (pn := 48 + cap);
[ eassumption | eassumption | exact VM3 | exact HPR04 | eassumption | exact HP4 | unfold jo_chargeA, ss_costB, charge; cbn [bB bD]; split; lia
| exact SB4 | exact UN4 | exact DATA | lia
| left; reflexivity | lia | lia | exact LEN | left; reflexivity | lia | left; lia | exact SR
| exists n; split; [reflexivity | lia] |].
intros m5 MU5 WM5 MI5 DST5 LEN5.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP3) as ND3.
exists ((p, 48 + cap) :: PBS). split; [apply Permutation_refl|]. split; [exact Hp|].
exists pb, PBS, (@nil blk), cap, 0, (@nil byte). split; [reflexivity|]. split.
{ eapply opt_pbuf_agree; [exact OPB3 | | apply incl_refl].
eapply agree_on_trans; (eapply (agree_of_munch asegs); [eassumption | eassumption |]); intros a k' Hin;
(assert (INa : In (a, k') (((p, 48 + cap) :: PBS ++ LB) ++ LM)) by (apply in_or_app; left; right; apply in_or_app; left; exact Hin));
(assert (Hpa : p <> a) by (intros <-; cbn in ND3; inversion ND3 as [|x_ l_ Hni Hnd]; subst x_ l_; apply Hni; rewrite !map_app; apply in_or_app; left; apply in_or_app; left; exact (in_map blk_addr _ _ Hin)));
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ p (48 + cap) a k' HP3 ltac:(apply in_or_app; left; left; reflexivity) INa Hpa) as D1;
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k' HP3 INa) as (Hk' & _ & _ & Hh & _); cbn; [split; [lia | exact I] | split; [lia|]; split; [lia|]; split; [lia | exact I]]. }
split; [lia|]. split; [lia|]. split; [cbn; lia|].
left. split; [lia|]. split; [reflexivity|]. split; [lia|]. exists (skipn (Z.to_nat (n + 1)) (le8 (wz pd) ++ jk)).
unfold jhdr_cells. cbn [app hl_segs hla_base A4L A4H].
lazymatch type of MU5 with munch ?W _ _ =>
apply (rw_cells_transport asegs W m4 m5) in HD; [| exact MU5 | exact WM5 | cbn [disjoint_from]; cbn; lia] end.
assert (Esb : sb = []) by (destruct sb; [reflexivity | exfalso; subst n; cbn [length] in N0; lia]).
rewrite Esb in DST5. cbn [app] in DST5 |- *. rewrite N0 in LEN5.
Q6Vi.Mq1.hdr_join HD LEN5 DST5.
Qed.
End BodyC.

Theorem set_string_len_A : jo_set_string_len_A_stmt HIx 0x9eb28 SS_STK_A 2 ss_costB.
Proof.
unfold jo_set_string_len_A_stmt. intros until errv. intros (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA) RR (SB & (Fs & ks & HFS & HS1 & HS2) & UN) LSB BB BD A0 A1 A2 K.
subst a0 a1 a2 tp. word_range sp SPR. unfold A_ERRNO, A_TP in *. change (6434400 - 164) with 6434236 in ERR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU.
stash SB.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step.
unstash SB.
evt_done5.
eapply (sc_main ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB BS LM FRS B lo p S sb r T errv Fs ks); try eassumption.
Qed.

Theorem set_string_A : jo_set_string_A_stmt HIx 0x9e890 SS_STK_A 2 ss_costB.
Proof.
unfold jo_set_string_A_stmt. intros until errv. intros (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA) RR (SB & NZ & PAD & (Fs & ks & HFS & HS1 & HS2) & UN) LSB BB BD A0 A1 K.
subst a0 a1 tp. word_range sp SPR. unfold A_ERRNO, A_TP in *. change (6434400 - 164) with 6434236 in ERR. unfold SS_STK_A in LOS.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof alloc_ceiling_range as ACR.
pose proof (hiA_top_le A4L HIx) as HT47.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP HFS) as (_ & _ & HF0 & HFc & _).
pose proof (asan_rt_ok_of_HEAPA HIx _ _ _ _ _ _ _ HP) as RT.
assert (NONUL : ~ In (Z_to_bv 8 0) sb) by (intros Hin; exact (proj1 (Forall_forall _ _) NZ _ Hin eq_refl)).
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
pose proof ST as ST0. carve_frame 32%nat ST.
stash SB.
a4l. reenterA asegs A4L HIx asegs_wx HP.
do 4 step. step. step. step. step.
unstash SB.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (SBc : bytes_at asegs mc S (sb ++ Z_to_bv 8 0 :: slack));
[ eapply (bytes_at_transport asegs); [exact SB | exact MU | cbn [disjoint_from]; rewrite length_app; cbn [length]; lia] |];
assert (UNc : unpoisoned asegs mc A_SB S (Z.of_nat (length sb) + 1));
[ eapply unpoisoned_transport; [exact UN | exact MU |]; intros a kk Ha Hkk; cbn [disjoint_from]; unfold shadow_span_lo, A_SB in Ha; unfold shadow_span_hi, A_SB in Hkk; repeat split; Z.div_mod_to_equations; lia |];
assert (RTc : asan_rt_ok mc)
end.
{ eapply (asan_rt_ok_of_HEAPA HIx). heap_nowA A4L HIx HP MU WM MI. }
eapply OBL_ASTRLEN_U with (s := S) (lo := lo) (str := sb) (slack := slack);
[ exact UNc | exact RTc | lia | lia | left; rewrite ?unsigned_lit by lia; lia | reflexivity | exact NONUL | lia | left; lia
| exact SBc | exact PAD | rewrite ?unsigned_lit by lia; eassumption | exact LO | rewrite ?unsigned_lit by lia; lia
| rewrite ?unsigned_lit by lia; clear - SPA; Z.div_mod_to_equations; lia | assumption | rewrite ?unsigned_lit by lia; reflexivity | ].
rewrite ?unsigned_lit by lia.
intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m3 MU3 WM3 MI3 SB3 ST3.
lazymatch type of MU3 with munch _ ?mq _ =>
transport_after_call asegs mq m3 MU3 WM3; try match goal with H : mem_inv asegs mq |- _ => clear H end; clear MU3 WM3 end.
replace (ret_pc (wz 0x9e8b0)) with (wz 0x9e8b0) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
do 6 step.
release_frame FR ST3 (bv_unsigned sp).
step. step.
assert (HP3 : HEAPAx A (BS ++ LB) LM FRS B m3 md) by (heap_nowA A4L HIx HP MU WM MI3).
assert (HPR3 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m3).
{ eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb] | clia | solve_clientWA A4L HIx HP]. }
assert (AG3 : agree_on asegs BS m m3).
{ eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros bb kk Hb. cbn.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ bb kk HP ltac:(apply in_or_app; left; apply in_or_app; left; exact Hb)) as (_ & _ & _ & Hh & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hh. split; [lia | exact I]. }
assert (BY0 : bytes_at asegs m S sb) by (apply bytes_at_app in SB as [BYa _]; exact BYa).
assert (UN0 : sb <> [] -> unpoisoned asegs m A_SB S (Z.of_nat (length sb))).
{ intros NE. eapply (QsKa.Mq1.unpoisoned_sub_any asegs _ A_SB S (Z.of_nat (length sb) + 1)); [exact UN | lia | lia |]. destruct sb; [exfalso; exact (NE eq_refl) | cbn [length]; lia]. }
destruct (src_pres _ _ _ _ _ _ _ LB (bv_unsigned sp) m m3 Fs ks S sb HP HFS HS1 ltac:(lia) HPR3 (conj BY0 UN0)) as [BY3 UN3].
evt_done5.
eapply (sc_main ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m3 md LB BS LM FRS B lo p S sb r T errv Fs ks);
[ exact SPR | exact LO | unfold SS_STK_A; exact LOS | exact SPA | exact HT | exact HFS | exact HS1 | lia | exact LSB | exact BB | exact BD
| | exact HP3 | eassumption | eassumption | eapply (QrIB.Mq0.jroot_rep_agree A4H A4F); [exact RR | exact AG3 | apply incl_refl] | exact BY3 | exact UN3 ].
intros ms' md' m' rv A' B' BS' PF CH ROOT HPf KSL KBS. eapply K; [| exact CH | exact ROOT | exact HPf | exact KSL | exact KBS].
destruct PF as (RS & VM & STf & HPRf & ERRf). split; [exact RS|]. split; [exact VM|]. split; [exact STf|]. split; [eapply heap_pres_trans; [exact HPR3 | exact HPRf] | exact ERRf].
Qed.
End MJoSetString.
End RC__1.
End Mq6.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ. Import QTEu. Import Qsw7 QJjn QRUw QKQo.
Import Q6WR Q6WR.Mq0 QrPc.
Import QYIF.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mq7 QlKV.Mqa QsKa.Mq7 QJZd.Mq4 QpNt.Mq4 QW22 QI6Z.Mq1 QlKV.Mq5 QJZd.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section PutX.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud) (lo : Z) (errv : word)
(BS : list blk) (x : Z) (T : TSet).

Lemma mf_xstrA :
forall (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x19 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (junk8 : list byte),
HEAPAx A (BS ++ LB) LM FRS B m md ->
xstr A4H A4F m BS x 0 ->
mf_frameA ra sp s0 s1 s2 s3 m junk8 ->
stk asegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -48 - 16 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> bv_unsigned ra mod 2 = 0 ->
model_vm_only (cfg_model md0) (cfg_model md) -> heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m -> fsaved F F1 -> (frm0 fc -> frm0 fc1) ->
bD B0 <= bD B -> bB B0 <= bB B -> 512 * Z.of_nat (length BS) <= bB B ->
KPOSTA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo errv Sbool BS x 1 T ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 x) x9 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 A_SB) x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x9ac74) fc1 None m (seg_rom asegs)).
Proof.
intros until junk8. intros HP J FR ST LO LOS SPA HT ERR RA VM0 HPR FS FRM BD BB0 BB K.
pose proof FR as FR0. unfold mf_frameA in FR. unfold_consts. unfold A_SB, A_TP, A_ERRNO in *. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP) as [HB00 HD00].
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [] m) as MU.
destruct J as (pb & PBS & DBS & cap & len & str & EBS & OPB & Hcap & Hlen & Hsl & CASES).
destruct CASES as [(Hl0 & EDBS & Hfit & junk & HDR) | (Hl0 & pd & pdn & junk & junk2 & EDBS & HPD & HDR & HD)]; subst DBS BS.
-
cbn [app] in HP.
blk_factsA A4L HIx HP x (48 + cap) Hxal Hxlo Hxhi Hximg.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ x (48 + cap) HP ltac:(left; reflexivity)) as SHx. unfold shad in SHx. a4l.
assert (SH : ro_cells asegs m (x / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
{ rewrite (shadow_bytes_split (48 + cap) 6) in SHx by lia.
apply bytes_at_app in SHx as [SH6 _]. split; [cbn; repeat split; exact I | cbn [cells_bytes cbytes app]; exact SH6]. }
clear SHx.
pose proof HDR as HDR0. unfold jhdr_cells in HDR. cbn [app] in HDR.
cbn [length app] in BB. rewrite ?Nat2Z.inj_succ in BB.
reenterA asegs A4L HIx asegs_wx HP.
asan_chk0.
step. norm_w32. step. step. if_truex.
step.
asan_chkA.
step.
step. if_truex.
evt_done5.
eapply (mf_genA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo errv Sbool ((x, 48 + cap) :: [] ++ PBS) x 1 T);
[ exact HP | lia | exact HDR0 | exact OPB | exact FR0 | exact ST | clia | clia | exact SPA | exact HT
| exact ERR | exact RA | exact VM0 | exact HPR | exact FS | exact FRM | reflexivity
| exact BD | cbn [length app] in *; rewrite ?Nat2Z.inj_succ in *; lia | cbn [length app] in *; rewrite ?Nat2Z.inj_succ in *; lia | exact K ].
-
cbn [app] in HP.
blk_factsA A4L HIx HP x (48 + cap) Hxal Hxlo Hxhi Hximg.
blk_factsA A4L HIx HP pd pdn Hpal Hplo Hphi Hpimg.
assert (Hxpd : x <> pd).
{ intros E. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. cbn in ND. inversion ND as [|y l Hni Hnd]. apply Hni. left. symmetry. exact E. }
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ x (48 + cap) HP ltac:(left; reflexivity)) as SHx. unfold shad in SHx. a4l.
assert (SH : ro_cells asegs m (x / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
{ rewrite (shadow_bytes_split (48 + cap) 7) in SHx by lia.
apply bytes_at_app in SHx as [SH7 _]. split; [cbn; repeat split; exact I | cbn [cells_bytes cbytes app]; exact SH7]. }
clear SHx HD.
unfold jhdr_cells in HDR. cbn [app] in HDR.
cbn [length app] in BB. rewrite ?Nat2Z.inj_succ in BB.
reenterA asegs A4L HIx asegs_wx HP.
asan_chk0.
step. norm_w32. step. step. if_truex.
step.
asan_chkA.
step.
step. if_falsex.
step.
asan_chkA.
step. step.

alloc_callA (hiA_free A4L HIx) blk pd uw UWptr A4L HIx HP MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists pdn. right; left. reflexivity. }
all: try (cbn [uw_pre uw_ok uw_key uw_cost]; intros _; split; [left; lia | unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (destruct (Z.eqb_spec pd 0); cbn [bB bD charge uw_cost] in *; lia).
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3. a4l.
rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in HPR3 by lia.
rewrite lb_remove_other in HPR3, HP3 by (cbn; lia). rewrite lb_remove_head in HPR3, HP3.
replace (if pd =? 0 then 0 else uw_cost UWptr) with 0 in HP3 by (destruct (Z.eqb_spec pd 0); reflexivity).
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in HDR; [| eapply client_range_block; [left; reflexivity | lia | cbn [cells_size csize Nat.add]; lia]].
assert (OPB3 : opt_pbuf asegs m3 PBS pb).
{ eapply opt_pbuf_agree; [exact OPB | | apply incl_refl].
eapply (agree_of_heap_pres asegs A4H); [exact HPR3 | reflexivity | intros b Hb; apply in_or_app; left; right; apply in_or_app; left; exact Hb]. }
assert (HPRb : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m3).
{ eapply heap_pres_trans; [exact HPR|].
eapply heap_pres_weaken; [exact HPR3 | lia | intros b Hb; cbn; right; apply in_or_app; apply in_app_or in Hb; destruct Hb; [left; apply in_or_app; right; assumption | right; assumption]]. }
replace (ret_pc (Z_to_bv 64 0x9ad20)) with (Z_to_bv 64 0x9ad20) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
a4l.
eapply (mf_genA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo errv Sbool ((x, 48 + cap) :: [(pd, pdn)] ++ PBS) x 1 T);
[ exact HP3 | lia | unfold jhdr_cells; cbn [app]; exact HDR | exact OPB3 | unfold mf_frameA; exact FR | exact ST3 | clia | clia | exact SPA | exact HT
| exact ERR3 | exact RA | eapply model_vm_only_trans; [exact VM0 | exact VM3] | exact HPRb | exact FS | exact FRM | reflexivity
| cbn [bD charge] in *; lia | cbn [bB charge length app] in *; rewrite ?Nat2Z.inj_succ in *; lia | cbn [bB charge length app] in *; rewrite ?Nat2Z.inj_succ in *; lia | exact K ].
Qed.

Lemma mfx_entryA :
forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (n ty tojs pb : Z) (rest : list cell),
HEAPAx A (BS ++ LB) LM FRS B m md ->
In (x, n) BS -> 48 <= n ->
rw_cells asegs m x (jhdr_cells ty 1 tojs pb 0 0 ++ rest) -> Z.of_nat (cells_size (jhdr_cells ty 1 tojs pb 0 0 ++ rest)) = n ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 - 96 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 x -> a1 = Z_to_bv 64 0 ->
(forall m3 junk8 (y1 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 yt5 yt6 y9 y19 : word),
HEAPAx A (BS ++ LB) LM FRS B m3 md ->
rw_cells asegs m3 x (jhdr_cells ty 0 tojs pb 0 0 ++ rest) ->
mf_frameA ra sp s0 s1 s2 s3 m3 junk8 ->
stk asegs m3 lo (bv_unsigned sp + -48) ->
rw_cells asegs m3 A_ERRNO [C4 errv] ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m3 ->
agree_on asegs (others x BS) m m3 ->
AJ5 A4L HIx A T md
(MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 A_TP) yt0 yt1 yt2 (Z_to_bv 64 x) y9 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7
(Z_to_bv 64 A_SB) y19 s4 s5 s6 s7 s8 s9 s10 s11 yt3 yt4 yt5 yt6)
F (Z_to_bv 64 0x9ac74) fc None m3 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9abd0) fc None m (seg_rom asegs)).
Proof.
intros until rest. intros HP INx N48 HDR SZ ST LO LOS SPA HT ERR RA A0 A1 KZ.
unfold_consts. unfold A_SB, A_TP, A_ERRNO in *. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP) as [HB00 HD00].
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
assert (INx2 : In (x, n) ((BS ++ LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; left; exact INx).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ x n HP INx2) as (_ & Hxal & Hxlo & Hxhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ x n HP INx2) as Hximg.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ x n HP ltac:(apply in_or_app; left; exact INx)) as SHx. unfold shad in SHx.
a4l.
assert (SH : ro_cells asegs m (x / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
{ rewrite (shadow_bytes_split n 6) in SHx by lia.
apply bytes_at_app in SHx as [SH6 _]. split; [cbn; repeat split; exact I | cbn [cells_bytes cbytes app]; exact SH6]. }
clear SHx.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (x + 4, x + 8)] m) as MU.
pose proof SZ as RSZ. rewrite cells_size_app in RSZ. cbn [cells_size csize jhdr_cells Nat.add] in RSZ.
unfold jhdr_cells in HDR. cbn [app] in HDR.
reenterA asegs A4L HIx asegs_wx HP. subst a0 a1.
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
if_true.
replace (1 + -1) with 0 in HDR by lia.
step; asan_chkA; step; step.
step. if_true.

clear MU WM.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI2.
pose proof (wmono_refl asegs m1) as WM. pose proof (munch_refl [(x + 24, x + 40); (lo, bv_unsigned sp + -48)] m1) as MU.
step. step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch type of HDR with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?rr) =>
apply (rw_cells_recast asegs mc x _ ([c1; c2; c3; c4] ++ ([CB 16 (cells_bytes [c5; c6])] ++ rr))) in HDR;
[| apply cells_wf_app; split; [cbn; repeat split; exact I | apply cells_wf_app; split; [cbn; repeat split; reflexivity | ]];
match type of HDR with _ => idtac end; destruct HDR as [[Hwf _] _]; repeat (apply cells_wf_app in Hwf as [_ Hwf] || destruct Hwf as [_ Hwf]); exact Hwf
| rewrite !cells_bytes_app; reflexivity | rewrite !cells_size_app; reflexivity ]
end;
destruct (proj1 (rw_cells_app asegs mc x _ _) HDR) as [HD4 REST]; clear HDR;
cbn [cells_size csize Nat.add] in REST; replace (x + Z.of_nat 24) with (x + 24) in REST by lia;
destruct (proj1 (rw_cells_app asegs mc (x + 24) _ _) REST) as [DST TL]; clear REST;
cbn [cells_size csize Nat.add] in TL; replace (x + 24 + Z.of_nat 16) with (x + 40) in TL by lia;
assert (HPc : HEAPAx A (BS ++ LB) LM FRS B mc md) by heap_nowA A4L HIx HP1 MU WM MI2
end.
eapply (QpNt.Mq4.amemset_A HIx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x n (x + 24) 0 16 lo);
[ exact HPc | .. ]; a4l_goal; rewrite ?unsigned_lit by lia;
try first [ exact INx2 | exact DST | exact ST | exact MI2 | reflexivity | lia
| replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) by lia; rewrite Zminus_mod, SPA; reflexivity ].
all: try (apply in_or_app; left; exact INx).
intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m4 MU4 WM4 MI4 DST4 ST4.
lazymatch type of MU4 with munch _ ?mc _ =>
transport_after_call asegs mc m4 MU4 WM4; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU4 WM4 HPc end.
replace (ret_pc (Z_to_bv 64 0x9ac74)) with (Z_to_bv 64 0x9ac74) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
assert (AG4 : agree_on asegs (others x BS) m1 m4).
{ eapply (agree_others_gen asegs); [exact MU | exact WM |]. intros a k Hin Hne.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP1 ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin)) as (Hk & _ & _ & Hahi & _).
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ x n a k HP1 INx2 ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin) ltac:(congruence)) as D.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hahi. cbn. lia. }
evt_done5.
eapply KZ.
- heap_nowA A4L HIx HP1 MU WM MI4.
- unfold jhdr_cells. cbn [app].
lazymatch goal with H4 : rw_cells asegs m4 x _, D4 : rw_cells asegs m4 (x + 24) _, T4 : rw_cells asegs m4 (x + 40) _ |- rw_cells _ m4 x ?cs =>
lazymatch cs with ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?rr => change cs with ([c1; c2; c3; c4] ++ ([c5; c6] ++ rr)) end;
apply (proj2 (rw_cells_app asegs m4 x _ _)); cbn [cells_size csize Nat.add]; split; [exact H4|];
replace (x + Z.of_nat 24) with (x + 24) by lia;
apply (proj2 (rw_cells_app asegs m4 (x + 24) _ _)); cbn [cells_size csize Nat.add];
replace (x + 24 + Z.of_nat 16) with (x + 40) by lia; split; [| exact T4];
eapply rw_cells_recast; [exact D4 | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity]
end.
- unfold mf_frameA. eassumption.
- exact ST4.
- assumption.
- eapply heap_pres_trans; [exact HPR1|].
eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP1 | intros b Hb; rewrite <- app_assoc; apply in_or_app; right; exact Hb | clia |].
apply Forall_cons; [cbn [fst snd] |]. { right; left. exists x, n. split; [exact INx2|]. split; [| lia].
exact (not_in_app3 _ _ _ _ (nodup_prefix_suffix BS (LB ++ LM) x n n ltac:(pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP1) as NDx; rewrite <- app_assoc in NDx; exact NDx) INx) (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP1 INx2)). }
apply Forall_cons; [cbn [fst snd]; left; clia | apply Forall_nil].
- eapply agree_on_trans; [exact AG1 | exact AG4].
Qed.

Lemma maybe_free_x_A :
forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (A : ASA A4L HIx) (r : jroot),
HEAPAx A (BS ++ LB) LM FRS B0 m0 md0 ->
jroot_rep A4H A4F r m0 BS x -> match r with JRdblx _ | JRstrx => True | _ => False end ->
stk asegs m0 lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 - 96 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m0 A_ERRNO [C4 errv] -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 x -> a1 = Z_to_bv 64 0 ->
512 * Z.of_nat (length BS) <= bB B0 ->
KPOSTA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo errv Sbool BS x 1 T ->
AJ5 A4L HIx A T md0
(MS (mkR ra sp gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9abd0) fc None m0 (seg_rom asegs)).
Proof.
intros until r. intros HP J XL ST LO LOS SPA HT ERR RA A0 A1 BB K.
pose proof (nodup_app_l' BS LB (nodup_app_l' (BS ++ LB) LM (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP))) as ND.
pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP) as [HB00 HD00].
destruct r as [|s|tojs|]; try contradiction.
-
destruct J as (Hx & Htojs & pb & PBS & bits & EBS & OPB & HDR).
assert (INx : In (x, 48) BS) by (rewrite EBS; left; reflexivity).
eapply (mfx_entryA t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m0 md0 A B0 48 JT_DOUBLE tojs pb [C8 bits]);
[ exact HP | exact INx | lia | exact HDR | reflexivity | exact ST | exact LO | exact LOS | exact SPA | exact HT | exact ERR | exact RA | exact A0 | exact A1 | ].
intros m3 junk8 y1 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 yt5 yt6 y9 y19 HP3 HDR3 FR3 ST3 ERR3 HPR3 AG3.
assert (AGT : agree_on asegs PBS m0 m3).
{ eapply agree_on_incl; [exact AG3|]. rewrite EBS. apply (incl_others_tail x 48 [] PBS PBS); [rewrite EBS in ND; exact ND | intros b Hb; exact Hb]. }
rewrite EBS in HP3. cbn [app] in HP3.
eapply (mf_scalarA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo errv Sbool BS x 1 T
y1 yt0 yt1 yt2 y9 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y19 yt3 yt4 yt5 yt6 F fc m3 md0 A B0 48 JT_DOUBLE tojs pb [C8 bits] PBS junk8);
[ exact HP3 | lia | exact HDR3 | right; left; reflexivity | eapply opt_pbuf_agree; [exact OPB | exact AGT | apply incl_refl]
| exact FR3 | exact ST3 | exact LO | clear - LOS; lia | exact SPA | exact HT | exact ERR3 | exact RA | apply model_vm_only_refl | exact HPR3
| apply fsaved_refl | intros Hf; exact Hf | reflexivity | lia
| rewrite EBS; cbn [length app]; lia | rewrite EBS in BB; cbn [length app] in BB; lia | exact K ].
-
destruct J as (Hx & pb & PBS & DBS & cap & len & str & EBS & OPB & Hcap & Hlen & Hsl & CASES).
assert (INx : In (x, 48 + cap) BS) by (rewrite EBS; left; reflexivity).
destruct CASES as [(Hl0 & EDBS & Hfit & junk & HDR) | (Hl0 & pd & pdn & junk & junk2 & EDBS & HPD & HDR & HD)]; subst DBS.
+
eapply (mfx_entryA t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m0 md0 A B0 (48 + cap) JT_STRING (fn_str_to_json_string A4F) pb
[C8 (wz len); CB (Z.to_nat cap) (str ++ [Z_to_bv 8 0] ++ junk)]);
[ exact HP | exact INx | lia | exact HDR
| rewrite cells_size_app; cbn [cells_size csize jhdr_cells Nat.add]; lia
| exact ST | exact LO | exact LOS | exact SPA | exact HT | exact ERR | exact RA | exact A0 | exact A1 | ].
intros m3 junk8 y1 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 yt5 yt6 y9 y19 HP3 HDR3 FR3 ST3 ERR3 HPR3 AG3.
assert (AGT : agree_on asegs PBS m0 m3).
{ eapply agree_on_incl; [exact AG3|]. rewrite EBS. apply (incl_others_tail x (48 + cap) [] PBS PBS); [rewrite EBS in ND; exact ND | intros b Hb; exact Hb]. }
eapply (mf_xstrA y1 yt0 yt1 yt2 y9 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y19 yt3 yt4 yt5 yt6 F fc m3 md0 A B0 junk8);
[ exact HP3 | | exact FR3 | exact ST3 | exact LO | clear - LOS; lia | exact SPA | exact HT | exact ERR3 | exact RA
| apply model_vm_only_refl | exact HPR3 | apply fsaved_refl | intros Hf; exact Hf | lia | lia | exact BB | exact K ].
exists pb, PBS, [], cap, len, str. split; [exact EBS|].
split; [eapply opt_pbuf_agree; [exact OPB | exact AGT | apply incl_refl]|].
split; [exact Hcap|]. split; [exact Hlen|]. split; [exact Hsl|]. left.
split; [exact Hl0|]. split; [reflexivity|]. split; [exact Hfit|]. exists junk. exact HDR3.
+
eapply (mfx_entryA t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m0 md0 A B0 (48 + cap) JT_STRING (fn_str_to_json_string A4F) pb
[C8 (wz len); C8 (wz pd); CB (Z.to_nat (cap - 8)) junk]);
[ exact HP | exact INx | lia | exact HDR
| rewrite cells_size_app; cbn [cells_size csize jhdr_cells Nat.add]; lia
| exact ST | exact LO | exact LOS | exact SPA | exact HT | exact ERR | exact RA | exact A0 | exact A1 | ].
intros m3 junk8 y1 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 yt5 yt6 y9 y19 HP3 HDR3 FR3 ST3 ERR3 HPR3 AG3.
assert (AGT : agree_on asegs ([(pd, pdn)] ++ PBS) m0 m3).
{ eapply agree_on_incl; [exact AG3|]. rewrite EBS.
apply (incl_others_tail x (48 + cap) [] ([(pd, pdn)] ++ PBS) ([(pd, pdn)] ++ PBS)); [rewrite EBS in ND; exact ND | intros b Hb; exact Hb]. }
eapply (mf_xstrA y1 yt0 yt1 yt2 y9 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y19 yt3 yt4 yt5 yt6 F fc m3 md0 A B0 junk8);
[ exact HP3 | | exact FR3 | exact ST3 | exact LO | clear - LOS; lia | exact SPA | exact HT | exact ERR3 | exact RA
| apply model_vm_only_refl | exact HPR3 | apply fsaved_refl | intros Hf; exact Hf | lia | lia | exact BB | exact K ].
exists pb, PBS, [(pd, pdn)], cap, len, str. split; [exact EBS|].
split; [eapply opt_pbuf_agree; [exact OPB | eapply agree_on_incl; [exact AGT | intros b Hb; right; exact Hb] | apply incl_refl]|].
split; [exact Hcap|]. split; [exact Hlen|]. split; [exact Hsl|]. right.
split; [exact Hl0|]. exists pd, pdn, junk, junk2. split; [reflexivity|]. split; [exact HPD|].
split; [exact HDR3|].
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ pd pdn HP ltac:(apply in_or_app; left; apply in_or_app; left; rewrite EBS; right; left; reflexivity)) as (Hpdn & _).
eapply rw_cells_agree; [exact HD | exact AGT | exists pd, pdn; split; [left; reflexivity | cbn; lia]].
Qed.
End PutX.

Lemma xleaf_len : forall (m : word -> option byte) BS p r,
jroot_rep A4H A4F r m BS p -> match r with JRdblx _ | JRstrx => True | _ => False end -> Z.of_nat (length BS) <= 4.
Proof.
intros m BS p r J XL. destruct r as [|s|tojs|]; try contradiction.
- destruct J as (_ & _ & pb & PBS & bits & -> & OPB & _).
destruct OPB as [[_ ->]|[_ (buf & bpos & size & content & -> & _)]]; cbn; lia.
- destruct J as (_ & pb & PBS & DBS & cap & len & str & -> & OPB & _ & _ & _ & CASES).
assert (LD : (length DBS <= 1)%nat) by (destruct CASES as [(_ & -> & _)|(_ & pd & pdn & _ & _ & -> & _)]; cbn; lia).
destruct OPB as [[_ ->]|[_ (buf & bpos & size & content & -> & _)]]; cbn [length]; rewrite length_app; cbn [length]; lia.
Qed.

Theorem put_xleaf_A : forall HIx : heap_iface_A A4L, jo_put_xleaf_A_stmt HIx put_entry_A put_stk_A 2048 2.
Proof.
intros HIx. unfold jo_put_xleaf_A_stmt. intros until errv. intros (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA) J XL CB CD A0 K.
unfold put_stk_A in LOS. unfold put_entry_A.
unfold_consts. unfold A_SB, A_TP, A_ERRNO in *. word_range sp SPW.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP) as [HB0 HD0].
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL]. a4l.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU.
pose proof (xleaf_len m BS p r J XL) as LEN.

assert (XB : p <> 0 /\ exists n, In (p, n) BS /\ 48 <= n).
{ destruct r as [|s|tojs|]; try contradiction.
- destruct J as (Hx & _ & pb & PBS & bits & EBS & _). split; [exact Hx|]. exists 48. split; [rewrite EBS; left; reflexivity | lia].
- destruct J as (Hx & pb & PBS & DBS & cap & len & str & EBS & _ & Hcap & _). split; [exact Hx|]. exists (48 + cap). split; [rewrite EBS; left; reflexivity | lia]. }
destruct XB as (Hp & n & INp & N48).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p n HP ltac:(apply in_or_app; left; apply in_or_app; left; exact INp)) as (_ & Hpal & Hplo & Hphi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
reenterA asegs A4L HIx asegs_wx HP. subst a0 tp.
carve_frame 112%nat ST.
do 14 step.
step. if_falsex.
step. step. step. step. step. step. step.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
assert (AG : agree_on asegs BS m m1).
{ eapply (agree_of_munch asegs); [exact MU | exact WM |].
intros a k Hin. pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin)) as (Hk & _ & _ & Hahi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hahi. cbn. lia. }
assert (J1 : jroot_rep A4H A4F r m1 BS p).
{ destruct r as [|s|tojs|]; try contradiction.
- destruct J as (Hx & Htojs & pb & PBS & bits & EBS & OPB & HDR). split; [exact Hx|]. split; [exact Htojs|].
exists pb, PBS, bits. split; [exact EBS|]. split.
+ eapply opt_pbuf_agree; [exact OPB | eapply agree_on_incl; [exact AG | intros b Hb; rewrite EBS; right; exact Hb] | apply incl_refl].
+ eapply rw_cells_agree; [exact HDR | exact AG | exists p, 48; split; [rewrite EBS; left; reflexivity | cbn; lia]].
- destruct J as (Hx & pb & PBS & DBS & cap & len & str & EBS & OPB & Hcap & Hlen & Hsl & CASES). split; [exact Hx|].
exists pb, PBS, DBS, cap, len, str. split; [exact EBS|]. split.
{ eapply opt_pbuf_agree; [exact OPB | eapply agree_on_incl; [exact AG | intros b Hb; rewrite EBS; right; apply in_or_app; right; exact Hb] | apply incl_refl]. }
split; [exact Hcap|]. split; [exact Hlen|]. split; [exact Hsl|].
destruct CASES as [(Hl0 & EDBS & Hfit & junkx & HDR) | (Hl0 & pd & pdn & junkx & junkx2 & EDBS & HPD & HDR & HD)].
+ left. split; [exact Hl0|]. split; [exact EDBS|]. split; [exact Hfit|]. exists junkx.
eapply rw_cells_agree; [exact HDR | exact AG | exists p, (48 + cap); split; [rewrite EBS; left; reflexivity | rewrite cells_size_app; cbn [cells_size csize jhdr_cells Nat.add length app]; rewrite ?length_app; cbn [length]; lia]].
+ right. split; [exact Hl0|]. exists pd, pdn, junkx, junkx2. split; [exact EDBS|]. split; [exact HPD|].
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ pd pdn HP ltac:(apply in_or_app; left; apply in_or_app; left; rewrite EBS, EDBS; right; left; reflexivity)) as (Hpdn & _).
split.
* eapply rw_cells_agree; [exact HDR | exact AG | exists p, (48 + cap); split; [rewrite EBS; left; reflexivity | rewrite cells_size_app; cbn [cells_size csize jhdr_cells Nat.add]; lia]].
* eapply rw_cells_agree; [exact HD | exact AG | exists pd, pdn; split; [rewrite EBS, EDBS; right; left; reflexivity | cbn; lia]]. }
assert (HPR1 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m1).
{ eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; rewrite <- app_assoc; apply in_or_app; right; exact Hb | clia |].
apply Forall_cons; [cbn [fst snd]; left; clia | apply Forall_nil]. }
evt_done5.
eapply (maybe_free_x_A HIx) with (BS := BS) (LB := LB) (x := p) (lo := lo) (r := r);
[ heap_nowA A4L HIx HP MU WM MI | exact J1 | exact XL | .. ]; a4l_goal; rewrite ?unsigned_lit by lia; try first [reflexivity | lia].
all: try (replace (bv_unsigned sp + -112) with (bv_unsigned sp - 112) by lia; rewrite Zminus_mod, SPA; reflexivity).
all: try exact ERR. all: try assumption.
intros ms2 md2 A2 (m2 & rr & B2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & BD2 & OUT2).
destruct RS2 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F2 & fc2 & -> & FS2 & FRM2).
a4l. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in ST2 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in HPR2 by lia.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
assert (HPR12 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m2).
{ eapply heap_pres_trans; [exact HPR1 | eapply heap_pres_weaken; [exact HPR2 | lia | intros b Hb; exact Hb]]. }
clear MU WM MI J J1.
destruct OUT2 as [(Er & Hrc2 & _ & _ & _) | [(Er & _ & BB2 & HP2) | (Er & _ & ZM & _ & _)]]; [lia | subst rr | exfalso; cbn in ZM; exact ZM].
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
pose proof (wmono_refl asegs m2) as WM. pose proof (munch_refl [] m2) as MU.
reenterA asegs A4L HIx asegs_wx HP2. step. step. if_truex.
do 14 step. release_frame FR ST2 (bv_unsigned sp). step.
evt_done5. eapply (K _ md2 m2 1 A2 B2).
- split; [apply ret_statew_intro; [exact FS2 | exact FRM2] |]. split; [exact VM2|]. split; [exact ST2|].
split; [exact HPR12|]. exists errv. exact ERR2.
- split; lia.
- reflexivity.
- exact ERR2.
- exact HP2.
Qed.
End RC__1.
End Mq7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QT7b QqWD QrIP QbFI QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw Q8tj.
Import QSL3. Import Q22i Q6us QT7b QqWD QrIP.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QsKa.Mqe Q30W.Mq6.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section ProbeA.
Variables (sp gp tp : word) (s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (t tbl size k v opts : Z) (svs : list slotv).
Notation SB0 := 2147450880.

Definition ins_regsA (x1 x7 x9 a3 : word) (n : Z) (x20 x22 x23 x24 x25 x28 x29 x30 x31 : word) :=
mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp (Z_to_bv 64 40) (Z_to_bv 64 (-3)) x7 (Z_to_bv 64 (t + 4)) x9
(Z_to_bv 64 t) (Z_to_bv 64 k) (Z_to_bv 64 v) a3 (Z_to_bv 64 opts) (Z_to_bv 64 tbl) (Z_to_bv 64 size) (Z_to_bv 64 n)
(Z_to_bv 64 SB0) (Z_to_bv 64 (t / 8 + SB0)) x20 (Z_to_bv 64 (t / 8 + SB0)) x22 x23 x24 x25 s10 s11 x28 x29 x30 x31.

Lemma lh_probe_loopA :
forall (d : nat) (n f : Z) (x1 x9 a3 x20 x22 x23 x24 x25 x28 x29 x30 x31 : word) (m : word -> option byte) (sf : slotv),
Z.of_nat d = (f - n) mod size ->
0 <= n < size -> 0 <= f < size -> In size lf_sizes -> Z.of_nat (length svs) = size ->
nth_error svs (Z.to_nat f) = Some sf -> is_free sf ->
(forall i s, nth_error svs i = Some s -> ~ is_free s -> 0 <= sv_k s < LH_FREEDv) ->
0 < tbl -> tbl + 40 * size <= alloc_ceiling -> tbl mod 16 = 0 ->
bytes_at asegs m (tbl / 8 + A_SB) (repeat (Z_to_bv 8 0) (Z.to_nat (5 * size))) -> tbl / 8 + A_SB + 5 * size <= alloc_ceiling ->
mem_inv asegs m -> lh_slots asegs m tbl svs ->
evt asegs (fun ms' => exists (g : Z) (sg : slotv),
0 <= g < size /\ nth_error svs (Z.to_nat g) = Some sg /\ is_free sg /\
ms' = MS (ins_regsA x1 (Z_to_bv 64 0) x9 (Z_to_bv 64 (tbl + g * 40)) g x20 x22 x23 x24 x25
(Z_to_bv 64 ((tbl + 40 * g) / 8 + SB0)) (Z_to_bv 64 (sv_k sg)) x30 x31)
F (Z_to_bv 64 0xa4958) fc None m (seg_rom asegs))
(MS (ins_regsA x1 (Z_to_bv 64 0) x9 a3 n x20 x22 x23 x24 x25 x28 x29 x30 x31)
F (Z_to_bv 64 0xa48e8) fc None m (seg_rom asegs)).
Proof.
induction d as [d IH] using lt_wf_ind; intros until sf; intros Hd Hn Hf Hsz Hlen Esf FREE LIVEK Ht0 Htb Hal TSH TSHhi MI SL.
pose proof (lf_size_range size Hsz) as HSR. word_range sp SPR. unfold_consts. unfold A_SB in *.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
destruct (nth_error svs (Z.to_nat n)) as [sn|] eqn:Esn.
2:{ exfalso. apply nth_error_None in Esn. lia. }
pose proof (SL _ _ Esn) as C. unfold ent_addr, slot_cells in C. rewrite Z2Nat.id in C by lia.

pose proof (bytes_at_repeat_sub asegs m _ _ _ (Z.to_nat (5 * n)) 1 TSH ltac:(lia)) as SH1.
apply ro_cells_of_repeat in SH1. cbn [map repeat] in SH1. rewrite Z2Nat.id in SH1 by lia.
replace (tbl / 8 + SB0 + 5 * n) with ((tbl + 40 * n) / 8 + SB0) in SH1 by (Z.div_mod_to_equations; lia).
unfold ins_regsA.
step. if_falsex.
step. rewrite (unsigned_lit n) by lia. step.
step. rewrite (unsigned_lit (tbl + n * 40)) by lia.
rewrite (ub_land7 (tbl + n * 40)) by (replace (tbl + n * 40) with (tbl + 40 * Z.of_nat (Z.to_nat n)) by lia; apply ent_addr_mod8; exact Hal).
step. if_false.
replace (tbl + n * 40) with (tbl + 40 * n) by lia. remember (tbl + 40 * n) as B eqn:EB.
assert (EB8 : B mod 8 = 0) by (subst B; Z.div_mod_to_equations; lia).
step. step. sh_norm. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false.
step. subst B.
step. unfold bv_ltu. change (bv_unsigned (Z_to_bv 64 (-3))) with 18446744073709551613.
assert (FD : is_free sn \/ ~ is_free sn).
{ unfold is_free. destruct (Z.eq_dec (sv_k sn) LH_EMPTYv); [left; left; assumption|].
destruct (Z.eq_dec (sv_k sn) LH_FREEDv); [left; right; assumption|]. right. intros [X|X]; contradiction. }
destruct FD as [FR' | NF].
-
assert (HK : sv_k sn = LH_EMPTYv \/ sv_k sn = LH_FREEDv) by exact FR'. unfold LH_EMPTYv, LH_FREEDv in HK.
rewrite (unsigned_lit (sv_k sn)) by lia. if_true.
ub_cmp_norm.
apply evt_done. exists n, sn. split; [lia|]. split; [exact Esn|]. split; [exact FR'|].
replace (tbl + 40 * n) with (tbl + n * 40) by lia. reflexivity.
-
assert (NE : n <> f) by (intros ->; rewrite Esf in Esn; injection Esn as ->; exact (NF FREE)).
pose proof (moddist_step n f size Hn Hf NE) as STEP.
pose proof (LIVEK _ _ Esn NF) as HK. unfold LH_FREEDv in HK.
rewrite (unsigned_lit (sv_k sn)) by lia. if_false.
step. if_falsex.
step. step. norm_w32. step. rewrite (unsigned_lit size), (unsigned_lit (n + 1)) by lia.
eapply evt_cut with (P := eq (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp (Z_to_bv 64 40) (Z_to_bv 64 (-3)) (Z_to_bv 64 0) (Z_to_bv 64 (t + 4)) x9
(Z_to_bv 64 t) (Z_to_bv 64 k) (Z_to_bv 64 v) (Z_to_bv 64 (n + 1)) (Z_to_bv 64 opts) (Z_to_bv 64 tbl) (Z_to_bv 64 size) (Z_to_bv 64 (next_ix size n))
(Z_to_bv 64 SB0) (Z_to_bv 64 (t / 8 + SB0)) x20 (Z_to_bv 64 (t / 8 + SB0)) x22 x23 x24 x25 s10 s11
(Z_to_bv 64 ((tbl + 40 * n) / 8 + SB0)) (Z_to_bv 64 (sv_k sn)) x30 x31) F (Z_to_bv 64 0xa4930) fc None m (seg_rom asegs))).
{ unfold next_ix. destruct (Z.eqb_spec (n + 1) size) as [EQ|NEQ].
- rewrite <- EQ, Z.lxor_nilpotent. step. rewrite (v_sltiu_1 (Z_to_bv 64 0) 1) by (rewrite ?unsigned_lit by lia; lia).
step. step. rewrite (unsigned_lit (n + 1)) by lia. change (bv_unsigned (Z_to_bv 64 (1 + -1))) with 0. rewrite Z.land_0_l. apply evt_done. reflexivity.
- pose proof (lxor_bound size (n + 1) 31 ltac:(lia) ltac:(lia) ltac:(lia)) as LB.
assert (LNZ : Z.lxor size (n + 1) <> 0) by (intros X; apply Z.lxor_eq in X; lia).
step. rewrite (v_sltiu_0 (Z_to_bv 64 (Z.lxor size (n + 1))) 1) by (rewrite ?unsigned_lit by lia; lia).
step. step. change (bv_unsigned (Z_to_bv 64 (0 + -1))) with 18446744073709551615.
rewrite (unsigned_lit (n + 1)) by lia. rewrite land_ones64_l by lia. apply evt_done. reflexivity. }
intros ms' <-.
assert (Hn' : 0 <= next_ix size n < size) by (unfold next_ix; destruct (Z.eqb_spec (n + 1) size); lia).
step. rewrite (unsigned_lit (next_ix size n)) by lia. step.
step. if_falsex.
step. step. step. step. rewrite (mul40_chk (next_ix size n)) by lia.
step. rewrite (v_sltiu_0 (Z_to_bv 64 (next_ix size n * 40 + tbl)) 1) by (rewrite ?unsigned_lit by lia; lia).
step. if_true.
eapply (IH (Z.to_nat ((f - next_ix size n) mod size)) ltac:(lia) (next_ix size n) f);
first [exact Esf | exact FREE | exact LIVEK | exact MI | exact SL | exact Hsz | exact Hlen | exact Hal | exact TSH | lia | idtac].
Qed.
End ProbeA.
End RC__1.
End Mq8.

Module Mq9.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ. Import QTEu. Import Qsw7 QJjn QRUw QKQo Q8tj.
Import QSL3.
Import Q6WR Q6WR.Mq0.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqh QlKV.Mqj QsKa.Mqg QsKa.Mqc QsKa.Mqe Q30W.Mq5 QnDr QJZd.Mqd QW22.Mq6 QnDr.Mq4 QI6Z.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Ltac post_callS segs m :=
let ms' := fresh "ms'" in let PO := fresh "POST" in
intros ms' PO;
destruct_exs PO;
let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
destruct PO as [E [MUc [WMc PO]]];
first [ destruct PO as [MIc PO] | rename PO into MIc ];
destruct_exs E;
subst ms';
rewrite ?unsigned_lit in MUc by lia; try rewrite ?unsigned_lit in PO by lia;
lazymatch type of MUc with
| munch _ m ?m' =>
transport_after_call segs m m' MUc WMc;
clear MUc WMc;
try match goal with H : mem_inv segs m |- _ => clear H end;
try clear m
end;
try destruct_ands PO;
try (lazymatch goal with
| |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
end).
Tactic Notation "callS" uconstr(SPEC) :=
lazymatch goal with
| |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | post_callS segs m ]
end.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section MF5.
Variable HIx : heap_iface_A A4L.

Lemma mf_objA : mf_objA_stmt HIx.
Proof.
unfold mf_objA_stmt.
intros ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo errv s BS x rc T kids.
intros until B. intros Hs HP J FR ST LO LOS SPA HT ERR RA VM0 HPR FS FRM Hrc BD BB0 BB K.
pose proof FR as FR0. unfold mf_frameA in FR. unfold_consts. unfold A_SB, A_TP, A_ERRNO in *. word_range sp SPR. subst s.
destruct (jval_obj_open asegs A4F kids m BS x 0 J) as (pb & PBS & t & TBS & kvs & KBS & EBS & OPB & HDR & LT & OK). clear J.
pose proof LT as (tbl & size & es & svs & Ekvs & ETBS & OPEN). subst TBS.
pose proof OPEN as (_ & _ & _ & _ & Hsz & Hcnt & Hlen).
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
rewrite EBS, <- app_assoc in HP. unfold lh_blocks in HP. cbn [app] in HP. rewrite <- app_assoc in HP. cbn [app] in HP.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP) as [HB00 HD00].
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
blk_factsA A4L HIx HP x 48 Hxal Hxlo Hxhi Hximg.
blk_factsA A4L HIx HP t 56 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP tbl (40 * size) Hbal Hblo Hbhi Himg_b.
shadow_nowA A4L HIx HP x 48 SHx.
shadow_nowA A4L HIx HP t 56 SHt.
a4l.
destruct (proj1 (ro_cells_app asegs m (t / 8 + 2147450880) [C1 (Z_to_bv 8 0)] _) SHt) as [SHt0 _]. clear SHt.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(lo, bv_unsigned sp + -64)] m) as MU.
pose proof HDR as HDR0. unfold jhdr_cells in HDR. cbn [app fn_obj_to_json_string A4F] in HDR.
pose proof (okids_len _ _ _ _ _ _ OK) as [L1 L2]. rewrite length_map in L1.
assert (LK : length kvs = length es) by (rewrite Ekvs; apply length_map).
rewrite EBS in BB. unfold lh_blocks in BB. cbn [concat app] in BB. rewrite ?length_app in BB. cbn [length] in BB.
rewrite ?length_app, ?length_map in BB. rewrite ?Nat2Z.inj_succ, ?Nat2Z.inj_add in BB.
stash OPB. stash OK. stash HDR0. stash OPEN.
reenterA asegs A4L HIx asegs_wx HP.
asan_chk0.
bstep. norm_w32. bstep. bstep. if_falsex. bstep. bstep. if_falsex. bstep. bstep. if_falsex.
bstep. bstep. if_true.
asan_chkA.
bstep. bstep.

unstash OPEN.
callS (lh_table_length_A _ (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 6444320) t0 t1 t2 (Z_to_bv 64 x) (Z_to_bv 64 (x + 40)) (Z_to_bv 64 0) (Z_to_bv 64 4) a3 a4 a5 a6 a7 x18 (Z_to_bv 64 2147450880) x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6 F1 fc1
m lo _ (lh_blocks t tbl size es) t kvs).
all: try (unfold small_pre; rewrite ?unsigned_lit by lia; split; [exact MI|]; split; [exact ST|]; split; [lia|]; split; [lia|]; split; [exact GOT|]; split; [exact CELL|]; lia).
all: try (exists tbl, size, es, svs; split; [exact Ekvs|]; split; [reflexivity | exact OPEN]).
all: try first [exact SHt0 | reflexivity | lia].
all: try (unfold A_SB; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia).
stash OPEN.
bstep.
destruct kids as [|k0 kids1].
- destruct kvs as [|kv kvs1]; [| cbn in L1; discriminate]. destruct KBS as [|bs KBS1]; [| cbn in L2; discriminate].
destruct es as [|e0 es1]; [| cbn in LK; discriminate].
cbn [length Z.of_nat]. if_true.
asan_chkA.
bstep. bstep.
cbn [concat app map] in HP.
unstash OPB. unstash OK. unstash HDR0. unstash OPEN.

evt_done5.
lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (lh_table_free_A_cps HIx _ gp x21 x22 s7 s8 s9 s10 s11 F1 fc1 mc md ((x, 48) :: PBS ++ LB) LM FRS B lo t tbl size [] svs T)
with (u := UWptr)
end.
all: a4l_goal; rewrite ?unsigned_lit by lia.
all: try (lazymatch goal with Hmi : mem_inv asegs ?mc |- HEAPA _ _ _ _ _ _ _ ?mc _ =>
eapply (heapA_perm A4L HIx); [heap_nowA A4L HIx HP MU WM Hmi | unfold lh_blocks; cbn [map app]; perm | apply Permutation_refl | apply Permutation_refl] end).
all: try (apply uw_at_ptr; lia).
all: try (cbn [uw_ok uw_key]; unfold a4_straces; repeat first [left; reflexivity | right]).
all: try (eapply (lh_open_agree asegs A4F); [exact OPEN | eapply (agree_of_munch asegs); [exact MU | exact WM |] | apply incl_refl];
intros b k Hb; unfold lh_blocks in Hb; cbn in Hb; cbn; destruct Hb as [Hb | [Hb | Hb]]; [injection Hb as <- <- | injection Hb as <- <- | destruct Hb]; lia).
all: try (lazymatch goal with |- forall e, In e [] -> _ => intros e He; destruct He end).
all: try (replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) by lia; rewrite Zminus_mod, SPA; reflexivity).
all: try (cbn [uw_cost length Z.of_nat Z.add]; lia).
all: try first [eassumption | reflexivity | lia].
intros ms4 md4 A4 (m4 & r4 & B4 & RS4 & VM4 & ST4 & HPR4 & ERR4 & BB4 & BD4 & HP4).
destruct RS4 as (w0 & w1 & w2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & w3 & w4 & w5 & w6 & F4 & fc4 & -> & FS4 & FRM4).
a4l. rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in ST4 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in HPR4 by lia.
lazymatch type of MU with munch _ m ?mc =>
assert (HPRc : heap_pres A4H (((x, 48) :: PBS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -64) m mc)
by (eapply (heap_pres_of_munch A4H _ (bv_unsigned sp + -64)); [exact MU | exact WM |];
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; cbn in Hb |- *; destruct Hb as [Hb|Hb]; [left; exact Hb | right; right; right; exact Hb] | clia | apply Forall_cons; [cbn; left; lia | apply Forall_nil]]);
pose proof (heap_pres_trans _ _ _ _ _ _ HPRc HPR4) as HPR4m
end.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in FR; [| left; cbn; lia].
first [ apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in HDR0; [| eapply client_range_block; [apply in_or_app; left; left; reflexivity | lia | cbn; lia]]
| apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4m) in HDR0; [| eapply client_range_block; [apply in_or_app; left; left; reflexivity | lia | cbn; lia]] ].
assert (OPB4 : opt_pbuf asegs m4 PBS pb).
{ eapply opt_pbuf_agree; [exact OPB | | apply incl_refl].
eapply (agree_of_heap_pres asegs A4H); [exact HPR4m | reflexivity | intros b Hb; apply in_or_app; left; right; apply in_or_app; left; exact Hb]. }
assert (HPRb : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m4).
{ eapply heap_pres_trans; [exact HPR|].
eapply heap_pres_weaken; [exact HPR4m | lia | intros b Hb; cbn; right; apply in_or_app; apply in_app_or in Hb; destruct Hb; [left; apply in_or_app; right; assumption | right; assumption]]. }
clear MU WM.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI4. a4l.
pose proof (munch_refl [] m4) as MU. pose proof (wmono_refl asegs m4) as WM.
reenterA asegs A4L HIx asegs_wx HP4.
bstep.
evt_done5.
eapply (mf_genA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo errv (Sobj []) BS x rc T);
[ exact HP4 | lia | exact HDR0 | exact OPB4 | exact FR | exact ST4 | clia | clia | exact SPA | exact HT
| exact ERR4 | exact RA | eapply model_vm_only_trans; [exact VM0 | exact VM4] | exact HPRb
| eapply fsaved_trans; [exact FS | exact FS4] | intros Hf; exact (FRM4 (FRM Hf)) | exact Hrc
| cbn [bD charge uw_cost] in *; lia
| clear - EBS BB BB0 BB4 HB00; subst BS; cbn [concat app length map lh_blocks] in *; unfold blk in *; lia
| clear - BB BB4 HB00; cbn [length Z.of_nat Z.add concat] in *; unfold blk in *; lia | exact K ].
- cbn [length] in L1. rewrite L1. if_falsex.
bstep. bstep.
do 9 bstep. lazymatch goal with STx : stk asegs _ lo (bv_unsigned sp + -64) |- _ => release_frame FR STx (bv_unsigned sp) end. bstep.
unstash OPB. unstash OK. unstash HDR0. unstash OPEN.
evt_done5. apply K. unfold mf_postA.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, 2, B end.
lazymatch goal with MUx : munch _ m ?mf, WMx : wmono asegs m ?mf |- _ =>
assert (AG : agree_on asegs BS m mf)
by (eapply (agree_of_munch asegs); [exact MUx | exact WMx |]; intros b k Hb; cbn;
rewrite EBS in Hb; unfold lh_blocks in Hb;
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ b k HP ltac:(in_sub Hb)) as (Hk & _ & Hqlo & Hqhi & _);
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hqhi; lia)
end.
split; [apply ret_statew_intro; [exact FS | exact FRM] |].
split; [exact VM0|]. split; [assumption|].
split.
{ eapply heap_pres_trans; [exact HPR |]. lazymatch goal with MUx : munch _ m ?mf, WMx : wmono asegs m ?mf |- _ =>
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MUx | exact WMx |] end.
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; in_sub Hb | clia | apply Forall_cons; [cbn; left; lia | apply Forall_nil]]. }
split; [assumption|]. split; [lia|].
right; right. split; [reflexivity|]. split; [exact Hrc|]. split; [| split; [lia|]].
+ split; [discriminate|]. exists t, tbl, size, es, svs. exists pb, PBS, KBS, es, (@nil lent).
split; [rewrite app_nil_r; reflexivity|]. split; [reflexivity|]. split; [apply Forall_nil|].
split; [rewrite EBS; reflexivity|]. split; [eapply opt_pbuf_agree; [exact OPB | exact AG | rewrite EBS; unfold lh_blocks; intros b Hb; in_sub Hb]|].
split; [eapply (rw_cells_agree asegs); [exact HDR0 | exact AG | exists x, 48; split; [rewrite EBS; left; reflexivity | cbn; lia]]|].
split; [eapply (lh_open_agree asegs A4F); [exact OPEN | exact AG | rewrite EBS; unfold lh_blocks; intros b Hb; in_sub Hb]|].
replace (map le_v es) with (map snd kvs); [eapply okids_agree; [exact OK | exact AG | rewrite EBS; intros b Hb; in_sub Hb]|].
rewrite Ekvs, map_map. reflexivity.
+ rewrite EBS, <- app_assoc in *. unfold lh_blocks in *. cbn [app] in *. rewrite <- app_assoc in *. cbn [app] in *.
eapply (heapA_client_frame A4L HIx); [exact HP | | assumption | assumption].
lazymatch goal with MUx : munch _ m ?mf |- _ => eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MUx); apply Forall_cons; [cbn; left; lia | apply Forall_nil] end.
Qed.

Definition maybe_free_A_closed := maybe_free_A_cps HIx mf_objA.
End MF5.
End RC__1.
End Mq9.

Module Mqa.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0. Import QT7i.
Import QbFI. Import QRUw.    Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqg QpNt.Mq8 QgoM Q4v2.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section APbMemappendMain.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud) (lo : Z) (pb n : Z) (T : TSet).

Lemma memappend_A_rebase :
forall (buf0 bpos0 cap0 : Z) (content0 : list byte) (xra t0 t1 t2 a3 a4 a5 a6 a7 x18 x19 x25 x26 x27 t3 t4 t5 t6 : word)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(obuf ocap buf bpos cap b : Z) (content src : list byte) (errv : word) (fjunk : list byte),
HEAPAx A ((pb, PB_SZ) :: (buf, cap) :: LB) LM FRS B m md ->
pbufx m pb buf bpos cap content ->
bpos + n + 1 <= cap -> 0 <= n < 2^31 ->
bytes_at asegs m b src -> Z.of_nat (length src) = n -> 0 <= b -> b + n <= alloc_ceiling ->
(0 < n -> unpoisoned asegs m A_SB b n) -> (n <= 64 \/ app_mem b n) ->
(b + n <= buf \/ buf + cap <= b) ->
(b + n <= obuf \/ obuf + ocap <= b) -> 0 <= obuf -> obuf + ocap <= 2^64 -> 0 < ocap < 2^31 ->
stk asegs m lo (bv_unsigned sp + -112) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -112 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m (bv_unsigned sp + -112) [CB 8 fjunk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs m A_ERRNO [C4 errv] ->
bv_unsigned ra mod 2 = 0 ->
model_vm_only (cfg_model md0) (cfg_model md) -> heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m ->
bB B0 - memappend_costX2 cap0 bpos0 n <= bB B -> bD B0 <= bD B ->
cap = memappend_cap2 cap0 bpos0 n ->
bpos = bpos0 -> firstn (Z.to_nat bpos) content = firstn (Z.to_nat bpos0) content0 ->
(forall ms' md' A', memappend_A_post_c HIx ra sp gp (Z_to_bv 64 A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 pb buf0 bpos0 cap0 content0 src n lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pb + 8)) (Z_to_bv 64 (pb + 12))
(Z_to_bv 64 pb) (Z_to_bv 64 b) (Z_to_bv 64 n) a3 a4 a5 a6 a7
(Z_to_bv 64 obuf) x19 (Z_to_bv 64 A_SB) (Z_to_bv 64 (pb / 8 + 1 + A_SB)) (Z_to_bv 64 (pb / 8)) (Z_to_bv 64 (pb / 8 + A_SB)) (Z_to_bv 64 ocap) x25 x26 x27 t3 t4 t5 t6)
F (Z_to_bv 64 0x9b6bc) fc None m (seg_rom asegs)).
Proof.
intros buf0 bpos0 cap0 content0. intros until fjunk.
intros HP PBX ROOM Hn SRC SRCL Hb0 Hbn UPS AMS BSEP OSEP Ob0 Obn Ocap ST LO LOS SPA HT FR ERR RA VM0 HPR BB BD CAPE Ebpos Epre K.
unfold_consts. unfold A_SB, A_TP, A_ERRNO in *. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
reenterA asegs A4L HIx asegs_wx HP.
step. step. step. step. step. step. step. step.
rewrite (unsigned_lit b) by lia. rewrite (unsigned_lit obuf) by lia.
destruct PBX as (Hbp & Hcap & Hlen & PBS & PBUF).
destruct (Z.eq_dec b obuf) as [Eb|Nb].
-
assert (Hn0 : n = 0) by lia. subst b.
rewrite (v_sltu_0 (Z_to_bv 64 obuf) (Z_to_bv 64 obuf)) by lia.
replace (obuf - obuf) with 0 by lia.
rewrite (v_sltu_1 (Z_to_bv 64 0) (Z_to_bv 64 ocap)) by (rewrite !unsigned_lit by lia; lia).
match goal with |- context [Z_to_bv 64 (bv_swrap 32 ?e)] => let v := eval vm_compute in (bv_swrap 32 e) in change (bv_swrap 32 e) with v end.
step. if_falsex.
blk_factsA A4L HIx HP pb 16 Hal Hlo Hhi Himg.
shadow_nowA A4L HIx HP pb 16 SHpb. a4l.
step. step. if_false. rewrite ?zxb_zero.
clear SHpb.
step. step.
try replace (buf + 0) with buf by lia.
blk_factsA A4L HIx HP buf cap Hbal0 Hblo0 Hbhi0 Hbimg0.
step. if_falsex.
step. step. ub_nzpair buf buf.
step. rewrite ?unsigned_lit by lia. change (Z.lxor 1 0) with 1.
step. if_falsex.
assert (src = []) as -> by (destruct src; [reflexivity | cbn in SRCL; lia]).
blk_factsA A4L HIx HP buf cap Hbal Hblo Hbhi Hbimg.
evt_done5.
replace (Z_to_bv 64 (pb / 8 + 2147450881)) with (Z_to_bv 64 (pb / 8 + 1 + 2147450880)) by (f_equal; lia).
eapply (memappend_A_tail HIx ra sp gp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo pb buf0 bpos0 cap0 n content0 T s0
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m md A B buf bpos cap buf content [] errv fjunk);
first [ reflexivity | eassumption | lia | idtac ].
all: try (unfold pbufx, pbuf_core; repeat (split; [first [lia | eassumption] |]); eassumption).
all: try (apply bytes_at_nil; unfold_consts; lia).
all: try (intros Hpos; exfalso; lia).
all: try (left; lia).
all: try (unfold_consts; lia).
-
match goal with |- context [Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 ?v) + 0))] =>
replace (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 v) + 0))) with (Z_to_bv 64 (-1)) end.
2:{ assert (Hv : forall v, v = 18446744073709551615 -> Z_to_bv 64 (-1) = Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 v) + 0))).
{ intros v ->. rewrite (unsigned_lit 18446744073709551615) by lia.
replace (18446744073709551615 + 0) with (-1 + 4294967296 * 4294967296) by lia.
rewrite swrap32_shift, swrap32_id by lia. reflexivity. }
apply Hv. clear Hv.
pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 (b - obuf))) as R1. unfold bv_modulus in R1. cbn in R1.
destruct (Z.lt_ge_cases b obuf) as [Hlt|Hge].
- rewrite (v_sltu_1 (Z_to_bv 64 b) (Z_to_bv 64 obuf)) by (rewrite (unsigned_lit b) by lia; rewrite (unsigned_lit obuf) by lia; lia).
rewrite (unsigned_lit 1) by lia. rewrite (swrap32_id (0 - 1)) by lia. change (0 - 1) with (-1). rewrite unsigned_m1.
rewrite lor_ones64_l by lia. rewrite (unsigned_lit 18446744073709551615) by lia.
rewrite lor_ones64_l; [reflexivity|].
match goal with |- 0 <= bv_unsigned ?w < _ => pose proof (bv_unsigned_in_range 64 w) as R2; unfold bv_modulus in R2; cbn in R2; lia end.
- assert (obuf + ocap <= b) by lia.
rewrite (v_sltu_0 (Z_to_bv 64 b) (Z_to_bv 64 obuf)) by (rewrite (unsigned_lit b) by lia; rewrite (unsigned_lit obuf) by lia; lia).
rewrite (unsigned_lit 0) by lia. rewrite (swrap32_id (0 - 0)) by lia. change (0 - 0) with 0. rewrite (unsigned_lit 0) by lia.
rewrite (unsigned_lit (b - obuf)) by lia. rewrite Z.lor_0_l.
rewrite (v_sltu_0 (Z_to_bv 64 (b - obuf)) (Z_to_bv 64 ocap)) by (rewrite (unsigned_lit (b - obuf)) by lia; rewrite (unsigned_lit ocap) by lia; lia).
rewrite (unsigned_lit 0) by lia. change (0 + -1) with (-1). rewrite unsigned_m1.
rewrite (unsigned_lit (b - obuf)) by lia. rewrite lor_ones64_r by lia. reflexivity. }
step. if_truex.
blk_factsA A4L HIx HP buf cap Hbal Hblo Hbhi Hbimg.
replace (Z_to_bv 64 (pb / 8 + 2147450881)) with (Z_to_bv 64 (pb / 8 + 1 + 2147450880)) by (f_equal; lia).
evt_done5.
eapply (memappend_A_tail HIx ra sp gp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo pb buf0 bpos0 cap0 n content0 T s0
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m md A B buf bpos cap b content src errv fjunk);
first [ reflexivity | eassumption | lia | idtac ].
all: first [ unfold pbufx, pbuf_core; repeat (split; [first [lia | eassumption] |]); eassumption | unfold_consts; lia ].
Qed.
End APbMemappendMain.
End RC__1.
End Mqa.

Module Mqb.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn QKQo Q8tj.
Import QSL3.
Import Q6WR Q6WR.Mq0 QrPc. Import QeuE.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QkXq.Mq7.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section Loop2A.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Variables (sp gp : word) (lo : Z) (errv : word) (LM : list blk) (FRS : list frame).

Notation SPR := (Z_to_bv 64 (bv_unsigned sp + -112)).
Notation TP := (Z_to_bv 64 6444320).
Notation SBR := (Z_to_bv 64 2147450880).
Notation CM1 := (Z_to_bv 64 18446744073709551615).
Notation ERRNO := (6444320 - 164).
Notation NEXT := (next_postA HIx sp gp lo errv LM FRS).
Notation spill' := (spillA sp).

Definition tyof (isobj : bool) : Z := if isobj then 4 else 5.

Definition zhead (isobj : bool) (m : word -> option byte) (x q : Z) (kids : list (option jshape)) (XBS : list blk) : Prop :=
if isobj then zobjc asegs A4F m x q kids XBS else zarrc asegs A4F m x q kids XBS.

Definition head_stmtA (isobj : bool) (kids : list (option jshape)) : Prop :=
forall (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x25 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (LB XBS : list blk) (x q : Z) (T : TSet),
HEAPAx A (XBS ++ LB) LM FRS B m md ->
zhead isobj m x q kids XBS ->
stk asegs m lo (bv_unsigned sp + -112) -> rw_cells asegs m ERRNO [C4 errv] ->
512 * Z.of_nat (length XBS) <= bB B ->
spill' m ->
(forall ms' md' A', NEXT q F1 fc1 m md LB B (512 * Z.of_nat (length XBS)) ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR x1 SPR gp TP t0 t1 t2 (Z_to_bv 64 x) x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 SBR (Z_to_bv 64 4) x25 (Z_to_bv 64 5) CM1 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x9be44) fc1 None m (seg_rom asegs)).

Definition desc_stmtA (c : jshape) : Prop :=
match c with Sobj kids => head_stmtA true kids | Sarr kids => head_stmtA false kids | _ => True end.
Definition desc_optA (k : option jshape) : Prop := match k with Some c => desc_stmtA c | None => True end.
Definition kids_descA (kids : list (option jshape)) : Prop := forall k, In k kids -> desc_optA k.

Definition zcont (isobj : bool) (m : word -> option byte) (x q : Z) (kids : list (option jshape)) (nz : nat) (cur : Z) (XBS : list blk) : Prop :=
if isobj then exists t tbl size es svs, zobj asegs A4F m x q kids nz t tbl size es svs XBS /\
(forall kids1 kl, kids = kids1 ++ [kl] -> exists e, nth_error es (length kids1) = Some e /\ cur = ent_addr tbl (le_ix e))
else exists a arr size, zarr asegs A4F m x q kids nz a arr size XBS.

Definition cont_stmtA (isobj : bool) (kids : list (option jshape)) : Prop :=
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (LB XBS : list blk) (x q : Z) (T : TSet) (nz : nat) (cur : Z),
HEAPAx A (XBS ++ LB) LM FRS B m md ->
zcont isobj m x q kids nz cur XBS ->
stk asegs m lo (bv_unsigned sp + -112) -> rw_cells asegs m ERRNO [C4 errv] ->
512 * Z.of_nat (length XBS) <= bB B ->
spill' m ->
(forall ms' md' A', NEXT q F1 fc1 m md LB B (512 * Z.of_nat (length XBS)) ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR x1 SPR gp TP t0 t1 t2 (Z_to_bv 64 x) (Z_to_bv 64 (x + 40)) a0 a1 a2 a3 a4 a5 a6 a7
x18 (Z_to_bv 64 cur) (Z_to_bv 64 (Z.of_nat (length kids))) (Z_to_bv 64 (Z.of_nat nz))
(Z_to_bv 64 (x / 8 + 2147450885)) SBR (Z_to_bv 64 4) (Z_to_bv 64 (x / 8 + 2147450880)) (Z_to_bv 64 5) CM1 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x9bed4) fc1 None m (seg_rom asegs)).

Definition zbodyp (isobj : bool) (m : word -> option byte) (x q : Z) (kids : list (option jshape)) (k : option jshape) (nz : nat) (cur : Z) (XBS : list blk) : Prop :=
if isobj then exists t tbl size es svs e, zobj asegs A4F m x q (kids ++ [k]) nz t tbl size es svs XBS /\
nth_error es (length kids) = Some e /\ cur = ent_addr tbl (le_ix e)
else exists a arr size, zarr asegs A4F m x q (kids ++ [k]) nz a arr size XBS.

Definition body_stmtA (isobj : bool) (kids : list (option jshape)) (k : option jshape) : Prop :=
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (LB XBS : list blk) (x q : Z) (T : TSet) (nz : nat) (cur : Z),
HEAPAx A (XBS ++ LB) LM FRS B m md ->
zbodyp isobj m x q kids k nz cur XBS ->
stk asegs m lo (bv_unsigned sp + -112) -> rw_cells asegs m ERRNO [C4 errv] ->
512 * Z.of_nat (length XBS) <= bB B ->
spill' m ->
(forall ms' md' A', NEXT q F1 fc1 m md LB B (512 * Z.of_nat (length XBS)) ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR x1 SPR gp TP t0 t1 t2 (Z_to_bv 64 x) (Z_to_bv 64 (x + 40)) a0 a1 a2 a3 a4 a5 a6 a7
x18 (Z_to_bv 64 cur) (Z_to_bv 64 (Z.of_nat (length kids))) (Z_to_bv 64 (Z.of_nat nz + 1))
(Z_to_bv 64 (x / 8 + 2147450885)) SBR (Z_to_bv 64 4) (Z_to_bv 64 (x / 8 + 2147450880)) (Z_to_bv 64 5) CM1 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x9bee0) fc1 None m (seg_rom asegs)).

Definition tojs_of (isobj : bool) : Z := if isobj then fn_obj_to_json_string A4F else fn_arr_to_json_string A4F.

Lemma zhead_hdr : forall isobj m x q kids XBS,
zhead isobj m x q kids XBS -> List.NoDup (map blk_addr XBS) ->
exists pb cf, In (x, 48) XBS /\
rw_cells asegs m x (jhdr_cells (tyof isobj) 0 (tojs_of isobj) pb 0 q ++ [C8 (Z_to_bv 64 cf)]) /\
(forall m' q', rw_cells asegs m' x (jhdr_cells (tyof isobj) 0 (tojs_of isobj) pb 0 q' ++ [C8 (Z_to_bv 64 cf)]) ->
agree_on asegs (others x XBS) m m' -> zhead isobj m' x q' kids XBS).
Proof. intros isobj. destruct isobj; [apply zobjc_hdr | apply zarrc_hdr]. Qed.

Lemma zhead_agree : forall isobj BS m m' x q kids XBS,
zhead isobj m x q kids XBS -> agree_on asegs BS m m' -> incl XBS BS -> zhead isobj m' x q kids XBS.
Proof. intros isobj. destruct isobj; [apply zobjc_agree | apply zarrc_agree]. Qed.

Lemma zomb_zhead : forall c m v bs, zomb asegs A4F c m v bs -> desc_stmtA c ->
exists isobj ck, zhead isobj m v 0 ck bs /\ head_stmtA isobj ck.
Proof.
intros c m v bs ZC KD. destruct c as [| | | |ck|ck]; cbn in ZC; try contradiction.
- exists true, ck. split; [exact (proj2 ZC) | exact KD].
- exists false, ck. split; [exact (proj2 ZC) | exact KD].
Qed.
End Loop2A.
End RC__1.
End Mqb.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc5u QZUC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqc.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 Qtgi QjDH Qsw7 QJjn QRUw.Mq0. Import QPZI.Mq4 QlCE.Mq1 QhHQ Q5Ki. Import QKQo.
Import Q6WR.Mq0 QrPc.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqh Q30W.Mq6 QJZd.Mqd QlKV.Mqf Qc5u QZUC QI6Z.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Definition tokfree_seg_B_pc : Z := 0x938b0.
Definition tokfree_done_B_pc : Z := 0x93940.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section TokFree2B.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis PUT : put_stmt_A HIx.

Definition tokfree_costB (BS : list blk) : Z := 512 * (Z.of_nat (length BS) + 34).

Definition tokfree_seg_postB (spv tk : Z) (gp s4 s6 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (BS : list blk) (lo : Z) (errv : word)
(s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (B' : bud) F' fc' x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s1' s2' s3' s5' s7' s8',
ms' = MS (mkR x1 (Z_to_bv 64 spv) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 tk) s1' a0 a1 a2 a3 a4 a5 a6 a7
s2' s3' s4 s5' s6 s7' s8' s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 tokfree_done_B_pc) fc' None m' (seg_rom asegs) /\
fsaved F F' /\ (frm0 fc -> frm0 fc') /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo spv /\
tfv_frame m' spv s8v s7v s6v s5v s4v s3v s2v s1v s0v rav /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) spv m m' /\
rw_cells asegs m' A_ERRNO [C4 errv] /\
bB B - tokfree_costB BS <= bB B' /\ bD B - 1 <= bD B' /\
HEAPAx A' LB LM FRS B' m' md'.

Lemma tokfree_segB :
forall (spv tk : Z) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM BS : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word)
(s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word),
HEAPAx A (BS ++ LB) LM FRS B m md ->
tokrep asegs A4F m BS tk -> tk <> 0 ->
tfv_frame m spv s8v s7v s6v s5v s4v s3v s2v s1v s0v rav ->
stk asegs m lo spv -> alloc_ceiling <= lo -> lo <= spv - 64 - put_stk_A ->
spv mod 16 = 0 -> spv + 80 <= hiA_top A4L HIx -> 0 <= spv < 2^64 ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tokfree_costB BS <= bB B -> 1 <= bD B ->
(forall ms' md' A', tokfree_seg_postB spv tk gp (Z_to_bv 64 A_SB) s6 s9 s10 s11 F fc m md LB LM FRS B BS lo errv s8v s7v s6v s5v s4v s3v s2v s1v s0v rav ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 spv) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 tk) s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 (Z_to_bv 64 A_SB) (Z_to_bv 64 (tk / 8 + 2147450884)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 tokfree_seg_B_pc) fc None m (seg_rom asegs)).
Proof.
intros until rav. intros HP TOKR Htk FR ST LO LOS SPA HT SPR ERR BB BD K.
destruct TOKR as (q & pb & depth & PBS & levels & x & EBS & LEN & Hd & TOK & PB & Hpb & TS & LOK & CLEAN).
pose proof BB as BB0. unfold tokfree_costB in BB. rewrite EBS in BB. cbn [length] in BB. rewrite length_app, ?Nat2Z.inj_succ, Nat2Z.inj_add in BB.
subst BS. unfold put_stk_A in LOS. unfold_consts. unfold A_SB, A_TP, A_ERRNO, tokfree_seg_B_pc in *. unfold tfv_frame in FR.

set (dn := Z.to_nat depth).
assert (PCV : Permutation (concat (map lvl_blocks levels)) (lvblocks levels (S dn))).
{ rewrite <- (lvblocks_trunc levels (S dn) ltac:(intros jj ll Hj Hkj; eapply CLEAN; [exact Hj | lia]) 32) by lia.
apply lvblocks_all. lia. }
pose proof (Permutation_length PCV) as LCV.
assert (HP0 : HEAPAx A (lvblocks levels (S dn) ++ PBS ++ (tk, 72) :: (q, 1024) :: LB) LM FRS B m md).
{ eapply (heapA_perm A4L HIx); [exact HP | | apply Permutation_refl | apply Permutation_refl].
replace (lvblocks levels (S dn) ++ PBS ++ (tk, 72) :: (q, 1024) :: LB)
with ((lvblocks levels (S dn) ++ PBS ++ [(tk, 72); (q, 1024)]) ++ LB) by (rewrite <- !app_assoc; reflexivity).
apply Permutation_app_tail.
apply (Permutation_trans (l' := (PBS ++ concat (map lvl_blocks levels)) ++ [(tk, 72); (q, 1024)])).
- apply (Permutation_app_comm [(tk, 72); (q, 1024)] (PBS ++ concat (map lvl_blocks levels))).
- replace (lvblocks levels (S dn) ++ PBS ++ [(tk, 72); (q, 1024)]) with ((lvblocks levels (S dn) ++ PBS) ++ [(tk, 72); (q, 1024)])
by (rewrite <- app_assoc; reflexivity).
apply Permutation_app_tail.
apply (Permutation_trans (l' := concat (map lvl_blocks levels) ++ PBS)); [apply Permutation_app_comm | apply Permutation_app_tail; exact PCV]. }
clear HP.
assert (INtk : In (tk, 72) (lvblocks levels (S dn) ++ PBS ++ (tk, 72) :: (q, 1024) :: LB)) by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 1024) (lvblocks levels (S dn) ++ PBS ++ (tk, 72) :: (q, 1024) :: LB)) by (apply in_or_app; right; apply in_or_app; right; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ tk 72 HP0 ltac:(apply in_or_app; left; exact INtk)) as (_ & Htal & Htlo & Hthi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ tk 72 HP0 ltac:(apply in_or_app; left; exact INtk)) as Himg_t.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ q 1024 HP0 ltac:(apply in_or_app; left; exact INq)) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ q 1024 HP0 ltac:(apply in_or_app; left; exact INq)) as Himg_q.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hqhi.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP0) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP0) as [GOT CELL].
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [] m) as MU.
unfold tok_cells in TOK.
pose proof PB as PB'. destruct PB' as (buf & bpos & size & pre & post & EPBS & _). stash PB.

assert (SHT : forall Ax LBx Bx mdx mc, HEAPAx Ax LBx LM FRS Bx mc mdx -> In (tk, 72) LBx ->
ro_cells asegs mc (tk / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
{ intros Ax LBx Bx mdx mc HPx Itk. pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ tk 72 HPx Itk) as SH. unfold shad in SH. apply shadow_ro_cells in SH.
let cs := eval cbv in (shadow_cells 72) in change (shadow_cells 72) with cs in SH. a4l. exact SH. }
pose proof (SHT _ _ _ _ m HP0 INtk) as SHt.
replace (tk / 8 + 2147450884) with (tk / 8 + 4 + 2147450880) by lia.
a4l. reenterA asegs A4L HIx asegs_wx HP0.
step. asan_chkB.
step. norm_sx32.
step. if_falsex.
step.
replace (Z_to_bv 64 depth) with (Z_to_bv 64 (Z.of_nat dn)) by (f_equal; lia).
clear SHt.
evt_done5.
lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ _ _ _ ?mc _) =>
assert (HPc : HEAPAx A (lvblocks levels (S dn) ++ PBS ++ (tk, 72) :: (q, 1024) :: LB) LM FRS B mc md) by heap_nowA A4L HIx HP0 MU WM MI;
assert (TSc : tstack asegs mc q levels)
by (eapply (tstack_transport asegs); [exact TS | exact MU | exact WM | intros j Hj; cbn; exact I]);
assert (AGc : agree_on asegs (lvblocks levels (S dn) ++ PBS ++ (tk, 72) :: (q, 1024) :: LB) m mc)
by (eapply (agree_of_munch asegs); [exact MU | exact WM | intros a n Hin; cbn; exact I]);
assert (HPRc : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) spv m mc)
by (eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) spv); [exact MU | exact WM |];
eapply (client_outsideA A4L HIx); [exact HP0 | intros bb Hbb; apply in_or_app; apply in_app_or in Hbb; destruct Hbb as [Hbb|Hbb]; [left; apply in_or_app; right; apply in_or_app; right; right; right; exact Hbb | right; exact Hbb] | clia | ];
apply Forall_nil)
end.
eapply (tf_loopB HIx PUT dn spv tk _ gp _ _ _ _ _ _ _ _ _ _ _ s1 _ _ _ s6 _ s9 s10 s11 _ _ _ _ F fc _ m md T A PBS LB LM FRS B lo errv q pb depth x levels s8v s7v s6v s5v s4v s3v s2v s1v s0v rav);
[ clia | unfold put_stk_A; clia | exact SPA | clear - HT; lia | lia | lia | lia | exact HPc
| intros j l Hj Hji; eapply lvl_ok_agree; [eapply LOK; [exact Hj | lia] | exact AGc | apply incl_appl; eapply incl_tran; [| eapply lvblocks_incl; [exact Hj | lia]]; unfold lvl_blocks; apply incl_appl; apply incl_refl]
| exact TSc | unfold tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote]; eassumption | unfold tfv_frame; eassumption | eassumption
| exact HPRc | eassumption | rewrite <- LCV; lia | ].
intros ms1 md1 A1 (mq1 & B1 & F1 & fc1 & levels1 & y1 & u0 & u1 & u2 & w0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & s3' & -> & FS1 & FRM1 & VM1 & HP1 & LEN1 & RES1 & SAME1 & TS1 & TOK1 & FR1 & ST1 & HPR1 & ERR1 & AG1 & BB1 & BD1).
clear TSc TOK FR ST MU WM MI HPc.
unfold tok_cells_g in TOK1. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK1. unfold tfv_frame in FR1.
assert (INp : In (pb, 16) (PBS ++ (tk, 72) :: (q, 1024) :: LB)) by (rewrite EPBS; left; reflexivity).
assert (INtk1 : In (tk, 72) (PBS ++ (tk, 72) :: (q, 1024) :: LB)) by (apply in_or_app; right; left; reflexivity).
assert (INq1 : In (q, 1024) (PBS ++ (tk, 72) :: (q, 1024) :: LB)) by (apply in_or_app; right; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ pb 16 HP1 ltac:(apply in_or_app; left; exact INp)) as (_ & Hpal & Hplo & Hphi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
assert (Htq : tk <> q).
{ intros ->. pose proof (nodup_app_l' _ _ (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP1)) as ND. rewrite map_app in ND. apply NoDup_app_remove_l in ND.
cbn [map blk_addr fst] in ND. apply List.NoDup_cons_iff in ND as [Hni _]. apply Hni. left. reflexivity. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q 1024 HP1 ltac:(apply in_or_app; left; exact INtk1) ltac:(apply in_or_app; left; exact INq1) Htq) as Hdtq.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI. a4l.
pose proof (wmono_refl asegs mq1) as WM.
pose proof (munch_refl [(tk, tk + 72)] mq1) as MU.
pose proof (SHT _ _ _ _ mq1 HP1 INtk1) as SHt.
unfold tokfree_exit_B_pc. reenterA asegs A4L HIx asegs_wx HP1.
step. rewrite ?sxb_zero, ?zxb_zero. step. if_false.
stepz.
try clear SHt. pose proof (SHT _ _ _ _ _ ltac:(heap_nowA A4L HIx HP1 MU WM MI) INtk1) as SHt.
step. rewrite ?sxb_zero, ?zxb_zero. step. if_false.
stepz.
try clear SHt. pose proof (SHT _ _ _ _ _ ltac:(heap_nowA A4L HIx HP1 MU WM MI) INtk1) as SHt.
step. asan_chkB.
step. step. if_falsex. step.
try clear SHt.

unstash PB.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (PBc : pbuf asegs mc PBS pb)
by (eapply (pbuf_agree asegs); [exact PB | | apply incl_refl];
eapply agree_on_trans; [eapply agree_on_incl; [exact AGc | rewrite EPBS; intros b Hb; apply in_or_app; right; apply in_or_app; left; exact Hb] |];
eapply agree_on_trans; [exact AG1 |];
eapply (agree_of_munch asegs); [exact MU | exact WM | intros a n Hin; cbn; split; [| exact I];
refine (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ a n tk 72 HP1 ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin) ltac:(apply in_or_app; left; exact INtk1) _);
intros ->; exact (nodup_prefix_suffix PBS ((tk, 72) :: (q, 1024) :: LB) tk n 72 (nodup_app_l' _ _ (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP1)) Hin ltac:(left; reflexivity)) ])
end.
evt_done5.
eapply (printbuf_free_A_cps HIx) with (LB := (tk, 72) :: (q, 1024) :: LB) (BS := PBS) (p := pb) (lo := lo) (u := UWpaid);
[ heap_nowA A4L HIx HP1 MU WM MI
| intros _; apply uw_at_paid
| intros _; cbn [uw_ok uw_key]; exact I
| right; split; [exact Hpb | apply pbuf_pbufw; exact PBc] | .. ];
a4l_goal; rewrite ?unsigned_lit by lia; try first [reflexivity | lia].
all: try (clear - SPA SPR; Z.div_mod_to_equations; lia).
all: try eassumption.
all: try (rewrite EPBS; cbn [length Z.of_nat]; cbn [bB charge] in *; lia).
all: try (pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP1) as [? ?]; destruct (pb =? 0); cbn [uw_cost bD charge] in *; lia).
intros ms2 md2 A2 (mq2 & r2 & B2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & BB2 & BD2 & HP2).
destruct RS2 as (w0' & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
a4l. rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR2 by lia.
replace (if pb =? 0 then 0 else uw_cost UWpaid) with 1 in BD2 by (destruct (Z.eqb_spec pb 0); [lia | reflexivity]).
lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR1; [| left; cbn; lia]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in TOK1; [| eapply (client_range_block A4H _ _ _ _ tk 72); [apply in_or_app; left; left; reflexivity | lia | cbn; lia]]. a4l.
assert (NTL : forall nn, ~ In (tk, nn) (LB ++ LM)).
{ intros nn Hin0. exact (nodup_prefix_suffix (PBS ++ [(tk, 72); (q, 1024)]) (LB ++ LM) tk 72 nn
ltac:(pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP1) as ND; rewrite <- !app_assoc in ND |- *; cbn [app] in ND |- *; exact ND)
ltac:(apply in_or_app; right; left; reflexivity) Hin0). }
assert (NTL72 : ~ In (tk, 72) (LB ++ LM ++ fr_ivs A4L FRS)).
{ apply not_in_app3; [exact (NTL 72)|]. eapply (blk_not_fr_iv A4L HIx); [exact HP1 | apply in_or_app; left; apply in_or_app; right; left; reflexivity]. }
assert (HPRb : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) spv m mq2).
{ eapply heap_pres_trans; [exact HPR1|]. eapply heap_pres_trans.
- eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) spv); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP1 | intros bb Hbb; apply in_or_app; apply in_app_or in Hbb; destruct Hbb as [Hbb|Hbb]; [left; apply in_or_app; right; right; right; exact Hbb | right; exact Hbb] | clia |].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
right; left. exists tk, 72. split; [apply in_or_app; left; exact INtk1|]. split; [exact NTL72 | lia].
- eapply heap_pres_weaken; [exact HPR2 | lia | intros bb Hbb; apply in_or_app; apply in_app_or in Hbb; destruct Hbb as [Hbb|Hbb]; [left; right; right; exact Hbb | right; exact Hbb]]. }
clear MU WM MI HPR1.

pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. a4l.
pose proof (wmono_refl asegs mq2) as WM. pose proof (munch_refl [] mq2) as MU.
pose proof (SHT _ _ _ _ mq2 HP2 ltac:(left; reflexivity)) as SHt.
reenterA asegs A4L HIx asegs_wx HP2.
step. asan_chkB.
step. step.
try clear SHt.
alloc_callA (hiA_free A4L HIx) blk q uw UWptr A4L HIx HP2 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists 1024. right. left. reflexivity. }
all: try (cbn [uw_pre uw_ok uw_key uw_cost]; intros _; split; [left; lia | unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (clear - SPA SPR; Z.div_mod_to_equations; lia).
all: try (pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP2) as [? ?]; destruct (Z.eqb_spec q 0); cbn [bB bD charge uw_cost] in *; rewrite ?EPBS in *; cbn [length Z.of_nat] in *; lia).
intros ms3 mx3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3. a4l.
rewrite ?unsigned_lit in ST3 by lia. rewrite ?unsigned_lit in HPR3 by lia.
rewrite (lb_remove_other q (tk, 72)) in HPR3, HP3 by (cbn; lia). rewrite lb_remove_head in HPR3, HP3.
replace (if q =? 0 then 0 else uw_cost UWptr) with 0 in HP3 by (destruct (Z.eqb_spec q 0); reflexivity).
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FR1; [| left; cbn; lia]. a4l.
assert (HPRd : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) spv m mx3).
{ eapply heap_pres_trans; [exact HPRb|]. eapply heap_pres_trans.
- eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) spv); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP2 | intros bb Hbb; apply in_or_app; apply in_app_or in Hbb; destruct Hbb as [Hbb|Hbb]; [left; right; right; exact Hbb | right; exact Hbb] | clia |].
apply Forall_nil.
- eapply heap_pres_weaken; [exact HPR3 | lia | intros bb Hbb; apply in_or_app; apply in_app_or in Hbb; destruct Hbb as [Hbb|Hbb]; [left; right; exact Hbb | right; exact Hbb]]. }
clear MU WM MI HPRb TOK1.

pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI. a4l.
pose proof (wmono_refl asegs mx3) as WM. pose proof (munch_refl [] mx3) as MU.
reenterA asegs A4L HIx asegs_wx HP3.
step. step.
alloc_callA (hiA_free A4L HIx) blk tk uw UWptr A4L HIx HP3 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists 72. left. reflexivity. }
all: try (cbn [uw_pre uw_ok uw_key uw_cost]; intros _; split; [left; lia | unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (clear - SPA SPR; Z.div_mod_to_equations; lia).
all: try (pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP3) as [? ?]; destruct (Z.eqb_spec tk 0); [lia|]; cbn [bB bD charge uw_cost] in *; rewrite ?EPBS in *; cbn [length Z.of_nat] in *; lia).
intros ms4 m4 md4 A4 r4 RS4 VM4 ST4 HPR4 ERR4 HP4. open_ret RS4. a4l.
rewrite ?unsigned_lit in ST4 by lia. rewrite ?unsigned_lit in HPR4 by lia.
rewrite lb_remove_head in HPR4, HP4.
replace (if tk =? 0 then 0 else uw_cost UWptr) with 0 in HP4 by (destruct (Z.eqb_spec tk 0); [lia|reflexivity]).
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in FR1; [| left; cbn; lia]. a4l.
lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end.
apply K. unfold tokfree_seg_postB, tokfree_done_B_pc.
exists m4, (charge (charge B2 512 0) 512 0), F2, fc2. do 22 eexists.
split; [reflexivity|].
split; [eapply fsaved_trans; [exact FS1 | exact FS2]|]. split; [intros Hf; apply FRM2, FRM1, Hf|].
split; [eapply model_vm_only_trans; [exact VM1|]; eapply model_vm_only_trans; [exact VM2|]; eapply model_vm_only_trans; [exact VM3| exact VM4]|].
split; [exact ST4|]. split; [unfold tfv_frame; exact FR1|].
split.
- eapply heap_pres_trans; [exact HPRd|]. eapply heap_pres_trans.
+ eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) spv); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP3 | intros bb Hbb; apply in_or_app; apply in_app_or in Hbb; destruct Hbb as [Hbb|Hbb]; [left; right; exact Hbb | right; exact Hbb] | clia |].
apply Forall_nil.
+ eapply heap_pres_weaken; [exact HPR4 | lia | intros bb Hbb; exact Hbb].
- split; [exact ERR4|]. split; [| split; [cbn [bD charge uw_cost] in *; lia | exact HP4]].
clear - BB0 BB1 BB2 LCV EPBS Hd. unfold tokfree_costB in *. cbn [bB charge] in *. unfold dn in *. rewrite ?Z2Nat.id in BB1 by lia.
rewrite <- LCV in BB1. rewrite EPBS in *. cbn [length app] in *. rewrite ?length_app in *. cbn [length] in *. lia.
Qed.
End TokFree2B.
End RC__1.
End Mqc.

Module Mqd.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun QWxq_c1.Mq0 Qfw3_c1.Mq2 Qc3B.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn QRUw.
Import Q6WR Q6WR.Mq0 QrPc.
Import QYIF.

Import QbFI QXUB. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QsKa.Mqd QlKV.Mqj QsKa.Mq9 QJZd.Mq9 QsKa.Mqh Qw5U.Mq5 Qekr QsKa.Mqf.

Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma neg_word_negvalA : forall z, -2^63 <= z < 2^63 -> Z_to_bv 64 (0 - bv_unsigned (Z_to_bv 64 z)) = Z_to_bv 64 (- z).
Proof.
intros z Hz. rewrite Z_to_bv_unsigned. rewrite <- (Z_to_bv_mod64 (0 - _)), <- (Z_to_bv_mod64 (- z)). f_equal.
change (bv_wrap 64 z) with (z mod 2^64).
destruct (Z.lt_ge_cases z 0).
- rewrite <- (Z.mod_unique z (2^64) (-1) (z + 2^64)) by lia.
rewrite <- (Z.mod_unique (0 - (z + 2^64)) (2^64) (-1) (-z)) by lia.
rewrite <- (Z.mod_unique (- z) (2^64) 0 (-z)) by lia. reflexivity.
- rewrite (Z.mod_small z) by lia. f_equal; lia.
Qed.

Lemma str_lenA_of_cell : forall m p n (newlen : word) (len : Z),
rw_cells asegs m (p + 40) [C8 newlen] -> newlen = Z_to_bv 64 len -> - 2^31 < len < 2^31 -> Z.abs len <= n -> str_lenA m p n.
Proof.
intros m p n newlen len H E R B. subst newlen. exists len. split; [| split; [exact R | exact B]].
pose proof (rw_cells_bytes_at asegs _ _ _ H) as BY. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY. exact BY.
Qed.
Lemma string_root_true : forall r, set_string_root r = JRstrx -> is_string_root r = true.
Proof.
intros [|sx|?|] H; cbn in H |- *; try discriminate; try reflexivity.
destruct sx; cbn in H |- *; first [reflexivity | discriminate].
Qed.

Section MJoSetString.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Notation jroot_repA := (jroot_rep A4H A4F).
Notation wz := (Z_to_bv 64).
Hypothesis OBL_AMEMCPY_U : amemcpy_spec_U.
Hypothesis OBL_ASTRLEN_U : astrlen_spec_U.

Definition SS_STK_A : Z := 80 + 4096.
Definition ss_costB (n : Z) : Z := 16 * (n + 1) + 1024.

Lemma src_pres : forall A LBa LM FRS B m0 md LBX SP m m' Fs ks S (sb : list byte),
HEAPAx A LBa LM FRS B m0 md -> In (Fs, ks) FRS -> Fs <= S -> S + Z.of_nat (length sb) <= Fs + fr_size ks - 8 ->
heap_pres A4H (LBX ++ LM ++ fr_ivs A4L FRS) SP m m' ->
bytes_at asegs m S sb /\ (sb <> [] -> unpoisoned asegs m A_SB S (Z.of_nat (length sb))) ->
bytes_at asegs m' S sb /\ (sb <> [] -> unpoisoned asegs m' A_SB S (Z.of_nat (length sb))).
Proof.
intros A LBa LM FRS B m0 md LBX SP m m' Fs ks S sb HP HFs H1 H2 HPR [BY UN]. split.
- eapply (heap_pres_bytes_at A4H); [exact HPR | exact BY |].
eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact HFs | cbn; lia | cbn; lia].
- intros NE. eapply (unpoisoned_pres_frame HIx); [exact HP | exact HFs | exact H1 | exact H2 | exact (UN NE) | exact HPR].
Qed.

Lemma jroot_str_casesA : forall r m BS p,
jroot_repA r m BS p -> r <> JRnull -> List.NoDup (map blk_addr BS) ->
p <> 0 /\
( (xstr A4H A4F m BS p 1 /\ set_string_root r = JRstrx)
\/ (set_string_root r = r /\ is_string_root r = false /\
exists n ty tojs pb udel ud rest,
In (p, n) BS /\ Z.of_nat (cells_size (jhdr_cells ty 1 tojs pb udel ud ++ rest)) = n /\ 48 <= n /\ 0 <= ty <= 6 /\ ty <> JT_STRING /\
rw_cells asegs m p (jhdr_cells ty 1 tojs pb udel ud ++ rest)) ).
Proof.
intros r m BS p RR NN ND.
assert (Hp : p <> 0) by (destruct r; [exfalso; exact (NN eq_refl) | exact (proj1 RR) ..]). split; [exact Hp|].
destruct r as [|s|tojs|]; [exfalso; exact (NN eq_refl)| | |].
- destruct RR as [_ J].
assert (SPLIT : (exists h, s = Sstr h) \/ jtype s <> JT_STRING).
{ destruct s as [|u| |h|kids|kids]; cbn [jtype]; unfold JT_BOOLEAN, JT_DOUBLE, JT_INT, JT_STRING, JT_OBJECT, JT_ARRAY;
first [left; eexists; reflexivity | right; lia]. }
destruct SPLIT as [[h ->] | NS]; [left; split; [eapply (Q6Vi.Mq1.jval_sstr_xstr A4H); exact J | reflexivity]|].
right. split; [destruct s as [|u| |h|kids|kids]; try reflexivity; cbn [jtype] in NS; exfalso; exact (NS eq_refl)|].
split; [destruct s as [|u| |h|kids|kids]; try reflexivity; cbn [jtype] in NS; exfalso; exact (NS eq_refl)|].
destruct (jval_hdr asegs A4F s m BS p 1 J ND) as (n & tojs & pb & udel & ud & rest & INp & SZ & N48 & HDR & _).
exists n, (jtype s), tojs, pb, udel, ud, rest. split; [exact INp|]. split; [exact SZ|]. split; [exact N48|].
split; [apply jtype_range|]. split; [exact NS| exact HDR].
- right. split; [reflexivity|]. split; [reflexivity|]. destruct RR as (_ & Htojs & pb & PBS & bits & EBS & OPB & HDR).
exists 48, JT_DOUBLE, tojs, pb, 0, 0, [C8 bits]. split; [rewrite EBS; left; reflexivity|]. split; [reflexivity|]. split; [lia|].
split; [unfold JT_DOUBLE; lia|]. split; [unfold JT_DOUBLE, JT_STRING; lia|]. exact HDR.
- left. split; [exact (proj2 RR) | reflexivity].
Qed.
Section BodyC.
Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB BS LM : list blk) (FRS : list frame) (B0 : bud) (lo p S : Z) (sb : list byte) (r : jroot) (T : TSet) (errv : word).
Variables (Fs ks : Z).
Let n := Z.of_nat (length sb).
Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp - SS_STK_A.
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hiA_top A4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis HFS : In (Fs, ks) FRS.
Hypothesis HS1 : Fs <= S.
Hypothesis HS2 : S + n <= Fs + fr_size ks - 8.
Hypothesis LSB : n <= 63.
Hypothesis BB0 : ss_costB n <= bB B0.
Hypothesis BD0 : 2 <= bD B0.
Hypothesis K : set_string_postA HIx ra sp gp (wz 6444320) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB BS LM FRS B0 (ss_costB n) 2 lo p n r T.

Lemma sc_exit : forall (m1 : word -> option byte) (md1 : config) (A1 : ASA A4L HIx) (B1 : bud) (BS' : list blk) (fj : list byte) (rv : Z) (e1 : word)
(xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xt3 xt4 xt5 xt6 : word),
rw_cells asegs m1 (bv_unsigned sp + -80) [CB 8 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk asegs m1 lo (bv_unsigned sp + -80) -> model_vm_only (cfg_model md0) (cfg_model md1) ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m1 ->
rw_cells asegs m1 6444156 [C4 e1] ->
HEAPAx A1 (BS' ++ LB) LM FRS B1 m1 md1 -> jo_chargeA (ss_costB n) 2 B0 B1 ->
jroot_repA (set_string_root r) m1 BS' p ->
(is_string_root r = true -> str_lenA m1 p n) -> (is_string_root r = false -> BS' = BS) ->
AJ5 A4L HIx A1 T md1
(MS (mkR xra (wz (bv_unsigned sp + -80)) gp (wz 6444320) xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 (wz rv) xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
F (wz 0xa06b8) fc None m1 (seg_rom asegs)).
Proof.
intros until xt6. intros FR1 ST1 VM1 HPR1 ERR1 HP1 CH1 ROOT KSL KBS.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
unfold SS_STK_A in LOS.
a4l. reenterA asegs A4L HIx asegs_wx HP1.
do 10 bstep.
release_frame FR1 ST1 (bv_unsigned sp).
bstep. bstep.
evt_done5.
eapply (K _ md1 m1 rv A1 B1 BS').
- unfold jo_post_frameA. split; [apply ret_statew_same|]. split; [exact VM1|]. split; [exact ST1|]. split; [exact HPR1 | exists e1; exact ERR1].
- exact CH1.
- exact ROOT.
- exact HP1.
- exact KSL.
- exact KBS.
Qed.

Lemma blk_not_pres : forall A1 BS1 B1 m1 md1 a k, HEAPAx A1 (BS1 ++ LB) LM FRS B1 m1 md1 -> In (a, k) BS1 -> ~ In (a, k) (LB ++ LM ++ fr_ivs A4L FRS).
Proof.
intros A1 BS1 B1 m1 md1 a k HP1 Hin Hi.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP1) as ND.
apply in_app_or in Hi as [Hi|Hi]; [| apply in_app_or in Hi as [Hi|Hi]].
- exact (nodup_prefix_suffix BS1 LB a k k (nodup_app_l' _ _ ND) Hin Hi).
- exact (nodup_prefix_suffix (BS1 ++ LB) LM a k k ND ltac:(apply in_or_app; left; exact Hin) Hi).
- refine (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP1 _ Hi). apply in_or_app; left. apply in_or_app; left. exact Hin.
Qed.

Lemma sc_tail : forall (m1 : word -> option byte) (md1 : config) (A1 : ASA A4L HIx) (B1 : bud) (BS1 : list blk) (fj : list byte) (e1 : word)
(D : Z) (k : nat) (junk : list byte) (newlen lenw : word) (bD szD pn : Z)
(xra xt0 xt1 xt2 xs2 xa0 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xt3 xt4 xt5 xt6 : word),
rw_cells asegs m1 (bv_unsigned sp + -80) [CB 8 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk asegs m1 lo (bv_unsigned sp + -80) -> model_vm_only (cfg_model md0) (cfg_model md1) ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m1 ->
rw_cells asegs m1 6444156 [C4 e1] ->
HEAPAx A1 (BS1 ++ LB) LM FRS B1 m1 md1 -> jo_chargeA (ss_costB n) 2 B0 B1 ->
bytes_at asegs m1 S sb -> (sb <> [] -> unpoisoned asegs m1 A_SB S n) ->
rw_cells asegs m1 D [CB k junk] -> n + 1 <= Z.of_nat k -> In (bD, szD) BS1 -> bD <= D -> D + Z.of_nat k <= bD + szD ->
rw_cells asegs m1 (p + 40) [C8 lenw] -> In (p, pn) BS1 -> 48 <= pn ->
(p + 48 <= D \/ D + Z.of_nat k <= p) ->
set_string_root r = JRstrx ->
(exists len, newlen = wz len /\ - 2^31 < len < 2^31 /\ Z.abs len <= n) ->
(forall m2, munch [(lo, bv_unsigned sp); (D, D + Z.of_nat k); (p + 40, p + 48)] m1 m2 -> wmono asegs m1 m2 -> mem_inv asegs m2 ->
rw_cells asegs m2 D [CB k (sb ++ [Z_to_bv 8 0] ++ skipn (Z.to_nat (n + 1)) junk)] ->
rw_cells asegs m2 (p + 40) [C8 newlen] ->
exists BS', Permutation BS1 BS' /\ jroot_repA JRstrx m2 BS' p) ->
AJ5 A4L HIx A1 T md1
(MS (mkR xra (wz (bv_unsigned sp + -80)) gp (wz 6444320) xt0 xt1 xt2 (wz (p + 40)) (wz D) xa0 (wz S) (wz n) xa3 xa4 xa5 xa6 xa7
xs2 (wz 2147450880) (wz (p / 8 + 2147450885)) newlen xs6 xs7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
F (wz 0xa066c) fc None m1 (seg_rom asegs)).
Proof.
intros until xt6. intros FR1 ST1 VM1 HPR1 ERR1 HP1 CH1 SB1 UN1 DST Hk INd HbD HDk LEN INp Hpn SEP SR NL FIN.
unfold SS_STK_A in LOS.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof alloc_ceiling_range as ACR.
assert (INdA : In (bD, szD) ((BS1 ++ LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; left; exact INd).
assert (INpA : In (p, pn) ((BS1 ++ LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; left; exact INp).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ bD szD HP1 INdA) as (_ & _ & HdLO & HdHI & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p pn HP1 INpA) as (_ & Hpal & HpLO & HpHI & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ bD szD HP1 INdA) as HdIMG. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in HdIMG.
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ p pn HP1 INpA) as HpIMG. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in HpIMG.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP1 HFS) as (_ & _ & HF0 & HFc & _).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP1 HFS INdA) as DFd.
pose proof (fr_size_pos ks) as FSP.
assert (Hn0 : 0 <= n) by (subst n; lia).
assert (LJ : length junk = k) by (destruct DST as [[[Hwf _] _] _]; exact Hwf).
pose proof (asan_rt_ok_of_HEAPA HIx _ _ _ _ _ _ _ HP1) as RT1.
assert (UND : 0 < n -> unpoisoned asegs m1 A_SB D n).
{ intros Hn. eapply (unpoisoned_of_blk HIx _ _ _ _ _ _ _ bD szD D n HP1); [apply in_or_app; left; exact INd | lia | lia | lia]. }
assert (UNS : 0 < n -> unpoisoned asegs m1 A_SB S n).
{ intros Hn. apply UN1. intros ->. subst n. cbn in Hn. lia. }

destruct (rw_cells_CB_cut asegs _ _ _ _ (Z.to_nat n) DST ltac:(lia)) as [DATA REST1].
destruct (rw_cells_CB_cut asegs _ _ _ _ 1%nat REST1 ltac:(lia)) as [NUL REST2]. clear DST REST1.
replace (D + Z.of_nat (Z.to_nat n)) with (D + n) in NUL, REST2 by lia.
replace (D + n + Z.of_nat 1) with (D + n + 1) in REST2 by lia.
pose proof (munch_refl [(lo, bv_unsigned sp); (D, D + Z.of_nat k); (p + 40, p + 48)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
a4l. reenterA asegs A4L HIx asegs_wx HP1.
bstep. bstep. bstep.
eapply OBL_AMEMCPY_U with (d := D) (s := S) (n := n) (lo := lo) (old := firstn (Z.to_nat n) junk) (src := sb);
[ exact UND | exact UNS | exact RT1 | lia | lia | lia | lia
| left; rewrite ?unsigned_lit by lia; lia | left; rewrite ?unsigned_lit by lia; lia
| reflexivity | reflexivity | reflexivity | lia | left; lia | lia
| exact DATA | exact SB1 | subst n; rewrite Nat2Z.id; reflexivity
| rewrite ?unsigned_lit by lia; eassumption | exact LO | rewrite ?unsigned_lit by lia; lia
| rewrite ?unsigned_lit by lia; clear - SPA; Z.div_mod_to_equations; lia | exact MI | rewrite ?unsigned_lit by lia; reflexivity | ].
rewrite ?unsigned_lit by lia.
intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 MU2 WM2 MI2 DATA2 SB2 ST2.
lazymatch type of MU2 with munch _ ?mq _ =>
transport_after_call asegs mq m2 MU2 WM2; try match goal with H : mem_inv asegs mq |- _ => clear H end; clear MU2 WM2 end.
replace (ret_pc (wz 0xa0678)) with (wz 0xa0678) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
bstep.
assert (FW : forall mX, munch [(lo, bv_unsigned sp); (D, D + Z.of_nat k); (p + 40, p + 48)] m1 mX -> wmono asegs m1 mX -> mem_inv asegs mX ->
HEAPAx A1 (BS1 ++ LB) LM FRS B1 mX md1).
{ intros mX MUX WMX MIX. eapply (heapA_client_frame A4L HIx); [exact HP1 | | exact WMX | exact MIX].
eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP1 MUX).
apply Forall_cons; [left; cbn [fst snd]; lia |].
apply Forall_cons; [right; left; exists bD, szD; cbn [fst snd]; split; [exact INdA | lia] |].
apply Forall_cons; [right; left; exists p, pn; cbn [fst snd]; split; [exact INpA | lia] | apply Forall_nil]. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m1 mc, WMc : wmono asegs m1 mc, MIc : mem_inv asegs mc |- _ =>
pose proof (FW mc MUc WMc MIc) as HPc end end.
assert (UNk : unpoisoned asegs m2 A_SB (D + n) 1)
by (eapply (unpoisoned_of_blk HIx _ _ _ _ _ _ _ bD szD (D + n) 1 HPc); [apply in_or_app; left; exact INd | lia | lia | lia]).
destruct (unpoisoned_last asegs _ _ _ _ UNk) as (v & SHk & Hv).
replace (D + n + 1 - 1) with (D + n) in SHk, Hv by lia. unfold A_SB in SHk.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p pn 5 HPc ltac:(apply in_or_app; left; exact INp) ltac:(lia) ltac:(lia)) as SH5.
replace (p / 8 + 2147450880 + 5) with (p / 8 + 2147450885) in SH5 by lia.
clear HPc.
lazymatch goal with |- evt _ ?Q (MS ?rg ?Fx ?pc ?fcx None ?mc ?rom) =>
let r' := open_constr:(mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in unify rg r';
lazymatch r' with mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31 =>
assert (CONT : forall ya1 ya2 : word, evt asegs Q
(MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ya1 ya2 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Fx (wz 0xa06a4) fcx None mc rom))
end end.
2:{ bstep. bstep. sh_norm. bstep. bstep.
destruct Hv as [-> | [Hv8 Hvm]].
- rewrite sxb_zero. if_false. apply CONT.
- rewrite (QsKa.Mqa.sxb_small v) by lia. if_truex. bstep. bstep.
rewrite (unsigned_lit (D + n)) by lia. rewrite QsKa.Mqa.land7_mod8 by lia. if_truex. apply CONT. }
intros ya1 ya2.
set (ez := D + n) in *. bstepz. subst ez.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m1 mc, WMc : wmono asegs m1 mc, MIc : mem_inv asegs mc |- _ =>
pose proof (FW mc MUc WMc MIc) as HPc end end.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p pn 5 HPc ltac:(apply in_or_app; left; exact INp) ltac:(lia) ltac:(lia)) as SH5.
replace (p / 8 + 2147450880 + 5) with (p / 8 + 2147450885) in SH5 by lia. clear HPc.
bstep. rewrite ?zxb_zero. bstep. if_false.
bstep. bstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m1 mc, WMc : wmono asegs m1 mc, MIc : mem_inv asegs mc |- _ =>
pose proof (FW mc MUc WMc MIc) as HP3;
assert (HPR3 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 mc);
[ eapply heap_pres_trans; [exact HPR1|];
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MUc | exact WMc |];
eapply (client_outsideA A4L HIx);
[ exact HP1
| intros ? Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb]
| clia | ];
apply Forall_cons; [left; cbn [fst snd]; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia |];
apply Forall_cons; [right; left; exists bD, szD; cbn [fst snd]; split; [exact INdA | split; [exact (blk_not_pres _ _ _ _ _ _ _ HP1 INd) | lia]] |];
apply Forall_cons; [right; left; exists p, pn; cbn [fst snd]; split; [exact INpA | split; [exact (blk_not_pres _ _ _ _ _ _ _ HP1 INp) | lia]] | apply Forall_nil]
|];
destruct (FIN mc MUc WMc MIc) as (BS' & PERM & ROOT') end end.
{
lazymatch goal with H : rw_cells asegs _ (D + n) [C1 _] |- _ =>
apply (rw_cells_recast asegs _ _ _ [CB 1 [Z_to_bv 8 0]]) in H; [| cbn; auto | reflexivity | reflexivity] end.
lazymatch goal with H1 : rw_cells asegs ?mc D [CB _ sb], H2 : rw_cells asegs ?mc (D + n) [CB 1 _], H3 : rw_cells asegs ?mc (D + n + 1) _ |- _ =>
pose proof (rw_cells_CB_join asegs _ _ _ _ _ _ H1 ltac:(replace (D + Z.of_nat (Z.to_nat n)) with (D + n) by lia; exact H2)) as J1;
pose proof (rw_cells_CB_join asegs _ _ _ _ _ _ J1 ltac:(replace (D + Z.of_nat (Z.to_nat n + 1)) with (D + n + 1) by lia; exact H3)) as J2 end.
rewrite <- app_assoc in J2. replace (Z.to_nat n + 1 + (k - Z.to_nat n - 1))%nat with k in J2 by lia.
rewrite skipn_skipn in J2. replace (1 + Z.to_nat n)%nat with (Z.to_nat (n + 1)) in J2 by lia. exact J2. }
{ assumption. }
evt_done5.
eapply (sc_exit _ md1 A1 B1 BS' fj 1 e1); [eassumption | eassumption | exact VM1 | exact HPR3 | eassumption | | exact CH1 | rewrite SR; exact ROOT' | |].
- eapply (heapA_perm A4L HIx); [exact HP3 | | apply Permutation_refl | apply Permutation_refl]. apply Permutation_app_tail. exact PERM.
- intros _. destruct NL as (len & EQ & R1 & R2).
lazymatch goal with |- str_lenA ?mX _ _ => lazymatch goal with H : rw_cells asegs mX (p + 40) [C8 _] |- _ => exact (str_lenA_of_cell _ _ _ _ _ H EQ R1 R2) end end.
- intros Hf. exfalso. rewrite (string_root_true r SR) in Hf. discriminate.
Qed.

Lemma sc_grow2 : forall (m1 : word -> option byte) (md1 : config) (A1 : ASA A4L HIx) (B1 : bud) (fj : list byte) (e1 : word)
(PBS : list blk) (q cap pb : Z) (junk0 junk : list byte) (lenw x : word)
(xra xt0 xt1 xt2 xa0 xa3 xa4 xa5 xa6 xa7 xs5 xt3 xt4 xt5 xt6 : word),
rw_cells asegs m1 (bv_unsigned sp + -80) [CB 8 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk asegs m1 lo (bv_unsigned sp + -80) -> model_vm_only (cfg_model md0) (cfg_model md1) ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m1 ->
rw_cells asegs m1 6444156 [C4 e1] ->
HEAPAx A1 (((q, n + 1) :: (p, 48 + cap) :: PBS) ++ LB) LM FRS B1 m1 md1 -> jo_chargeA (ss_costB n) 2 B0 B1 ->
bytes_at asegs m1 S sb -> (sb <> [] -> unpoisoned asegs m1 A_SB S n) ->
rw_cells asegs m1 q [CB (Z.to_nat (n + 1)) junk0] ->
rw_cells asegs m1 p (jhdr_cells JT_STRING 1 (fn_str_to_json_string A4F) pb 0 0 ++ [C8 lenw; C8 x; CB (Z.to_nat (cap - 8)) junk]) ->
opt_pbuf asegs m1 PBS pb -> 8 <= cap -> 1 <= n ->
set_string_root r = JRstrx ->
AJ5 A4L HIx A1 T md1
(MS (mkR xra (wz (bv_unsigned sp + -80)) gp (wz 6444320) xt0 xt1 xt2 (wz (p + 40)) (wz q) xa0 (wz S) (wz n) xa3 xa4 xa5 xa6 xa7
(wz (p + 48)) (wz 2147450880) (wz (p / 8 + 2147450885)) xs5 (wz n) (wz ((p + 48) / 8)) s8 s9 s10 s11 xt3 xt4 xt5 xt6)
F (wz 0xa05ac) fc None m1 (seg_rom asegs)).
Proof.
intros until xt6. intros FR1 ST1 VM1 HPR1 ERR1 HP1 CH1 SB1 UN1 QB HDR OPB Hcap Hn SR.
unfold SS_STK_A in LOS.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof alloc_ceiling_range as ACR.
assert (INq : In (q, n + 1) ((((q, n + 1) :: (p, 48 + cap) :: PBS) ++ LB) ++ LM)) by (apply in_or_app; left; left; reflexivity).
assert (INp : In (p, 48 + cap) ((((q, n + 1) :: (p, 48 + cap) :: PBS) ++ LB) ++ LM)) by (apply in_or_app; left; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP1 INq) as (_ & _ & HqLO & HqHI & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP1 INp) as (_ & Hpal & HpLO & HpHI & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HP1 INq) as HqIMG. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in HqIMG.
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HP1 INp) as HpIMG. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in HpIMG.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP1) as ND1.
assert (Hqp : q <> p).
{ intros ->. cbn in ND1. inversion ND1 as [|x_ l_ Hni Hnd]; subst. apply Hni. left. reflexivity. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ q (n + 1) p (48 + cap) HP1 INq INp Hqp) as DISJ.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p (48 + cap) 6 HP1 ltac:(right; left; reflexivity) ltac:(lia) ltac:(lia)) as SH6.
replace (p / 8 + 2147450880 + 6) with ((p + 48) / 8 + 2147450880) in SH6 by (rewrite (div8_add p 48) by lia; change (48 / 8) with 6; lia).
unfold jhdr_cells in HDR. cbn [app hl_segs hla_base A4L A4H] in HDR.
pose proof (munch_refl [(p + 48, p + 56)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
stash SB1.
a4l. reenterA asegs A4L HIx asegs_wx HP1.
bstep.
bstep. rewrite ?zxb_zero. bstep. if_false.
bstep. bstep. bstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m2 end.
assert (HP2 : HEAPAx A1 (((q, n + 1) :: (p, 48 + cap) :: PBS) ++ LB) LM FRS B1 m2 md1).
{ eapply (heapA_client_frame A4L HIx); [exact HP1 | | exact WM | assumption].
eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP1 MU).
apply Forall_cons; [right; left; exists p, (48 + cap); cbn [fst snd]; split; [exact INp | lia] | apply Forall_nil]. }
assert (HPR12 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m1 m2).
{ eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx);
[ exact HP1 | intros ? Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb] | clia | ].
apply Forall_cons; [right; left; exists p, (48 + cap); cbn [fst snd]; split; [exact INp | split; [| lia]] | apply Forall_nil].
exact (blk_not_pres _ _ _ _ _ _ _ HP1 ltac:(right; left; reflexivity)). }
unstash SB1.
destruct (src_pres _ _ _ _ _ _ _ LB (bv_unsigned sp) m1 m2 Fs ks S sb HP1 HFS HS1 HS2 HPR12 (conj SB1 UN1)) as [SB2 UN2].

lazymatch type of HDR with rw_cells _ _ _ [?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9] =>
change [c1; c2; c3; c4; c5; c6; c7; c8; c9] with ([c1; c2; c3; c4; c5; c6] ++ ([c7] ++ [c8; c9])) in HDR end.
destruct (proj1 (rw_cells_app asegs m2 p _ _) HDR) as [HDRa HDRr]. cbn [cells_size csize Nat.add] in HDRr. replace (p + Z.of_nat 40) with (p + 40) in HDRr by lia.
destruct (proj1 (rw_cells_app asegs m2 (p + 40) _ _) HDRr) as [LEN2 HDRt]. cbn [cells_size csize Nat.add] in HDRt. replace (p + 40 + Z.of_nat 8) with (p + 48) in HDRt by lia.
evt_done5.
eapply (sc_tail m2 md1 A1 B1 ((q, n + 1) :: (p, 48 + cap) :: PBS) fj e1 q (Z.to_nat (n + 1)) junk0 _ lenw q (n + 1) (48 + cap));
[ eassumption | eassumption | exact VM1 | eapply heap_pres_trans; [exact HPR1 | exact HPR12] | eassumption | exact HP2 | exact CH1 | exact SB2 | exact UN2
| eassumption | lia | left; reflexivity | lia | lia | exact LEN2 | right; left; reflexivity | lia | lia | exact SR
| exists (- n); split; [apply neg_word_negvalA; lia | lia] | ].
intros m3 MU3 WM3 MI3 QB3 LEN3.
assert (LJ0 : length junk0 = Z.to_nat (n + 1)) by (destruct QB as [[[Hwf _] _] _]; exact Hwf).
exists ((p, 48 + cap) :: [(q, n + 1)] ++ PBS). split; [cbn [app]; apply perm_swap|].
cbn [jroot_rep]. split; [lia|].
exists pb, PBS, [(q, n + 1)], cap, (- n), sb. split; [reflexivity|]. split.
{ eapply opt_pbuf_agree; [exact OPB | | apply incl_refl].
eapply agree_on_trans.
- eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros a k Hin. cbn.
assert (INa : In (a, k) ((((q, n + 1) :: (p, 48 + cap) :: PBS) ++ LB) ++ LM)) by (apply in_or_app; left; right; right; apply in_or_app; left; exact Hin).
assert (NEa : p <> a).
{ intros <-. cbn in ND1. inversion ND1 as [|x_ l_ Hni Hnd]; subst. inversion Hnd as [|x2 l2 Hni2 Hnd2]; subst. apply Hni2.
rewrite !map_app. apply in_or_app; left. apply in_or_app; left. exact (in_map blk_addr _ _ Hin). }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ p (48 + cap) a k HP1 INp INa NEa). split; [lia | exact I].
- eapply (agree_of_munch asegs); [exact MU3 | exact WM3 |]. intros a k Hin. cbn.
assert (INa : In (a, k) ((((q, n + 1) :: (p, 48 + cap) :: PBS) ++ LB) ++ LM)) by (apply in_or_app; left; right; right; apply in_or_app; left; exact Hin).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP1 INa) as (_ & _ & _ & Hh & _).
assert (NEa : p <> a).
{ intros <-. cbn in ND1. inversion ND1 as [|x_ l_ Hni Hnd]; subst. inversion Hnd as [|x2 l2 Hni2 Hnd2]; subst. apply Hni2.
rewrite !map_app. apply in_or_app; left. apply in_or_app; left. exact (in_map blk_addr _ _ Hin). }
assert (NEq : q <> a).
{ intros <-. cbn in ND1. inversion ND1 as [|x_ l_ Hni Hnd]; subst. apply Hni. right.
rewrite !map_app. apply in_or_app; left. apply in_or_app; left. exact (in_map blk_addr _ _ Hin). }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ p (48 + cap) a k HP1 INp INa NEa).
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ q (n + 1) a k HP1 INq INa NEq).
split; [lia | split; [lia | split; [lia | exact I]]]. }
split; [exact Hcap|]. split; [lia|]. split; [subst n; lia|].
right. split; [lia|]. exists q, (n + 1), junk, (skipn (Z.to_nat (n + 1)) junk0). split; [reflexivity|]. split; [lia|]. split.
- unfold jhdr_cells. cbn [app hl_segs hla_base A4L A4H].
lazymatch goal with |- rw_cells _ _ _ [?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9] =>
change [c1; c2; c3; c4; c5; c6; c7; c8; c9] with ([c1; c2; c3; c4; c5; c6] ++ ([c7] ++ [c8; c9])) end.
apply (proj2 (rw_cells_app asegs m3 p _ _)). cbn [cells_size csize Nat.add]. replace (p + Z.of_nat 40) with (p + 40) by lia. split.
+ eapply (rw_cells_transport asegs _ m2 m3); [exact HDRa | exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize Nat.add]; lia].
+ apply (proj2 (rw_cells_app asegs m3 (p + 40) _ _)). cbn [cells_size csize Nat.add]. replace (p + 40 + Z.of_nat 8) with (p + 48) by lia. split.
* rewrite <- (neg_word_negvalA n) by lia. exact LEN3.
* eapply (rw_cells_transport asegs _ m2 m3); [exact HDRt | exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize Nat.add]; lia].
- replace (Z.to_nat (n + 1)) with (Z.to_nat (n + 1)) by reflexivity. cbn [hl_segs hla_base A4L A4H]. exact QB3.
Qed.

Lemma sc_grow : forall (m1 : word -> option byte) (md1 : config) (A1 : ASA A4L HIx) (fj : list byte) (e1 : word)
(PBS DBS : list blk) (cap pb len0 : Z) (junk : list byte) (x : word)
(xra xt0 xt1 xt2 xa0 xa3 xa4 xa5 xa6 xa7 xs1 xs5 xs6 xs7 xt3 xt4 xt5 xt6 : word),
rw_cells asegs m1 (bv_unsigned sp + -80) [CB 8 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk asegs m1 lo (bv_unsigned sp + -80) -> model_vm_only (cfg_model md0) (cfg_model md1) ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m1 ->
rw_cells asegs m1 6444156 [C4 e1] ->
HEAPAx A1 (((p, 48 + cap) :: DBS ++ PBS) ++ LB) LM FRS B0 m1 md1 ->
bytes_at asegs m1 S sb -> (sb <> [] -> unpoisoned asegs m1 A_SB S n) ->
rw_cells asegs m1 p (jhdr_cells JT_STRING 1 (fn_str_to_json_string A4F) pb 0 0 ++ [C8 (wz len0); C8 x; CB (Z.to_nat (cap - 8)) junk]) ->
opt_pbuf asegs m1 PBS pb -> 8 <= cap -> 1 <= n ->
xstr A4H A4F m1 ((p, 48 + cap) :: DBS ++ PBS) p 1 ->
-2^63 <= len0 < 2^63 -> Z.abs len0 <= n ->
((0 <= len0 /\ DBS = []) \/ (len0 < 0 /\ exists pd pdn, DBS = [(pd, pdn)] /\ x = wz pd)) ->
set_string_root r = JRstrx ->
AJ5 A4L HIx A1 T md1
(MS (mkR xra (wz (bv_unsigned sp + -80)) gp (wz 6444320) xt0 xt1 xt2 (wz (p + 40)) xs1 xa0 (wz S) (wz n) xa3 xa4 xa5 xa6 xa7
(wz (p + 48)) (wz 2147450880) (wz (p / 8 + 2147450885)) xs5 xs6 xs7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
F (wz 0xa055c) fc None m1 (seg_rom asegs)).
Proof.
intros until xt6. intros FR1 ST1 VM1 HPR1 ERR1 HP1 SB1 UN1 HDR OPB Hcap Hn ROOT LEN0R LABS FLAG SR.
unfold SS_STK_A in LOS. unfold ss_costB in BB0.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof alloc_ceiling_range as ACR.
assert (INp1 : In (p, 48 + cap) ((((p, 48 + cap) :: DBS ++ PBS) ++ LB) ++ LM)) by (apply in_or_app; left; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP1 INp1) as (_ & Hpal & HpLO & HpHI & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HP1 INp1) as HpIMG. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in HpIMG.
unfold jhdr_cells in HDR. cbn [app hl_segs hla_base A4L A4H] in HDR.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
stash SB1.
a4l. reenterA asegs A4L HIx asegs_wx HP1.
bstep. bstep. bstep. bstep.

evt_done5.
eapply (hiA_malloc A4L HIx) with (n := n + 1) (u := UWpaid) (lo := lo) (errv := e1);
[ heap_nowA A4L HIx HP1 MU WM MI | .. ].
all: rewrite ?unsigned_lit by lia.
1: eassumption.
1: exact LO.
1: cbn [hl_stack_A A4L]; lia.
1: clear - SPA; Z.div_mod_to_equations; lia.
1: lia.
1: cbn [hl_segs hl_tp hla_base A4L A4H]; unfold A_TP; eassumption.
1: reflexivity.
1: reflexivity.
1: lia.
1: cbn; exact I.
1: cbn; exact I.
1: lia.
1: cbn [uw_cost]; lia.
intros ms2 m2 md2 A2 q e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS.
cbn [hl_segs hl_tp hla_base A4L A4H] in ST2, HPR2, ERR2, OUT2. unfold A_TP in ERR2. change (6444320 - 164) with 6444156 in ERR2.
rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in ST2, HPR2 by lia.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR1; [| left; cbn; lia]. cbn [hl_segs hla_base A4L A4H] in FR1.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in HDR; [| eapply client_range_block; [apply in_or_app; left; apply in_or_app; left; left; reflexivity | lia | cbn; lia]]. cbn [hl_segs hla_base A4L A4H] in HDR.
unstash SB1.
destruct (src_pres _ _ _ _ _ _ _ (((p, 48 + cap) :: DBS ++ PBS) ++ LB) (bv_unsigned sp + -80) m1 m2 Fs ks S sb HP1 HFS HS1 HS2 HPR2 (conj SB1 UN1)) as [SB2 UN2].
assert (AG2 : agree_on asegs ((p, 48 + cap) :: DBS ++ PBS) m1 m2).
{ eapply (agree_of_heap_pres asegs A4H); [exact HPR2 | reflexivity | intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb]. }
assert (HPR02 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m2).
{ eapply heap_pres_trans; [exact HPR1|]. eapply heap_pres_weaken; [exact HPR2 | lia |].
intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb]. }
pose proof (model_vm_only_trans _ _ _ VM1 VM2) as VM02.
assert (CH2 : jo_chargeA (ss_costB n) 2 B0 (charge B0 (16 * (n + 1) + 512) (uw_cost UWpaid))) by (unfold jo_chargeA, ss_costB, charge; cbn [bB bD uw_cost]; split; lia).
clear MU WM MI.
destruct OUT2 as [(-> & _ & HP2) | (Hq & [junk0 QB] & HP2)].
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
replace (ret_pc (wz 0xa056c)) with (wz 0xa056c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
reenterA asegs A4L HIx asegs_wx HP2.
bstep. if_lit. bstep. bstep.
evt_done5.
eapply (sc_exit m2 md2 A2 _ ((p, 48 + cap) :: DBS ++ PBS) fj 0 e2); [exact FR1 | exact ST2 | exact VM02 | exact HPR02 | exact ERR2 | exact HP2 | exact CH2 | | |].
+ rewrite SR. split; [lia|]. eapply (QrIB.Mq0.xstr_agree A4H A4F); [exact ROOT | exact AG2 | apply incl_refl].
+ intros _. apply rw_cells_app with (cs1 := [_;_;_;_;_;_]) in HDR as [_ LEN1]. cbn [cells_size csize Nat.add] in LEN1.
apply rw_cells_app with (cs1 := [_]) in LEN1 as [LEN1 _]. replace (p + Z.of_nat 40) with (p + 40) in LEN1 by lia.
refine (str_lenA_of_cell _ _ _ _ len0 LEN1 eq_refl _ LABS). clear - LABS LSB. subst n. lia.
+ intros Hf. exfalso. rewrite (string_root_true r SR) in Hf. discriminate.
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP2) as ND2.
assert (INp2 : In (p, 48 + cap) ((q, n + 1) :: ((p, 48 + cap) :: DBS ++ PBS) ++ LB)) by (right; left; reflexivity).
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p (48 + cap) 5 HP2 INp2 ltac:(lia) ltac:(lia)) as SH5.
replace (p / 8 + 2147450880 + 5) with (p / 8 + 2147450885) in SH5 by lia.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p (48 + cap) 6 HP2 INp2 ltac:(lia) ltac:(lia)) as SH6.
replace (p / 8 + 2147450880 + 6) with ((p + 48) / 8 + 2147450880) in SH6 by (rewrite (div8_add p 48) by lia; change (48 / 8) with 6; lia).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ q (n + 1) HP2 ltac:(apply in_or_app; left; left; reflexivity)) as (_ & _ & HqLO & HqHI & _).
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
replace (ret_pc (wz 0xa056c)) with (wz 0xa056c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
stash SB2.
reenterA asegs A4L HIx asegs_wx HP2.
bstep. if_falsex. bstep.
bstep. rewrite ?zxb_zero. bstep. if_false.
bstep. bstep. bstep.
rewrite (unsigned_lit (p + 48)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
bstep. bstep.
destruct FLAG as [(Hl0 & ->) | (Hl0 & pd & pdn & -> & ->)].
+
if_truex. cbn [app] in HP2, OPB, AG2.
unstash SB2.
evt_done5.
eapply (sc_grow2 m2 md2 A2 _ fj e2 PBS q cap pb junk0 junk (wz len0) x);
[ exact FR1 | exact ST2 | exact VM02 | exact HPR02 | exact ERR2 | exact HP2 | exact CH2 | exact SB2 | exact UN2 | exact QB
| unfold jhdr_cells; cbn [app]; exact HDR | | exact Hcap | exact Hn | exact SR ].
eapply opt_pbuf_agree; [exact OPB | exact AG2 | intros b Hb; right; exact Hb].
+
if_falsex. cbn [app] in HP2, AG2, ND2, INp2.
assert (Hqpd : q <> pd). { intros Eq. cbn in ND2. inversion ND2 as [|x_ l_ Hni Hnd]; subst x_ l_. apply Hni. cbn. right; left. symmetry; exact Eq. }
assert (Hppd : p <> pd). { intros Epd. cbn in ND2. inversion ND2 as [|x_ l_ Hni Hnd]; subst x_ l_. inversion Hnd as [|x2 l2 Hni2 Hnd2]; subst x2 l2. apply Hni2. cbn. left. symmetry; exact Epd. }
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ pd pdn HP2 ltac:(apply in_or_app; left; right; right; left; reflexivity)) as (_ & _ & Hpd0 & _).
bstep. bstep. rewrite ?zxb_zero. bstep. if_false.
bstep. bstep.
evt_done5.
eapply (hiA_free A4L HIx) with (p := pd) (u := UWpaid) (lo := lo) (errv := e2);
[ heap_nowA A4L HIx HP2 MU WM MI | right; exists pdn; right; right; left; reflexivity | .. ].
all: rewrite ?unsigned_lit by lia.
1: eassumption.
1: exact LO.
1: cbn [hl_stack_A A4L]; lia.
1: clear - SPA; Z.div_mod_to_equations; lia.
1: lia.
1: cbn [hl_segs hl_tp hla_base A4L A4H]; unfold A_TP; eassumption.
1: reflexivity.
1: reflexivity.
1: split; cbn; exact I.
1: cbn [charge bB uw_cost]; lia.
1: destruct (Z.eqb pd 0); cbn [charge bD uw_cost]; lia.
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3.
cbn [hl_segs hl_tp hla_base A4L A4H] in ST3, HPR3, ERR3, HP3. unfold A_TP in ERR3. change (6444320 - 164) with 6444156 in ERR3.
rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in ST3, HPR3 by lia.
rewrite (lb_remove_other pd) in HPR3, HP3 by (cbn; lia). rewrite (lb_remove_other pd) in HPR3, HP3 by (cbn; lia). rewrite lb_remove_head in HPR3, HP3.
replace (if pd =? 0 then 0 else uw_cost UWpaid) with 1 in HP3 by (destruct (Z.eqb_spec pd 0); [lia | reflexivity]).
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FR1; [| left; cbn; lia]. cbn [hl_segs hla_base A4L A4H] in FR1.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in HDR; [| eapply client_range_block; [right; left; reflexivity | lia | cbn; lia]]. cbn [hl_segs hla_base A4L A4H] in HDR.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in QB; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs hla_base A4L A4H] in QB.
unstash SB2.
lazymatch type of HPR3 with heap_pres _ (?LX ++ LM ++ _) _ ?ma _ =>
destruct (src_pres _ _ _ _ _ _ _ LX (bv_unsigned sp + -80) ma m3 Fs ks S sb HP2 HFS HS1 HS2 HPR3) as [SB3 UN3] end.
{ exact (conj SB2 UN2). }
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI3. cbn [hl_segs hla_base A4L A4H] in MI3.
clear MU WM. pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m3) as MU. pose proof (wmono_refl asegs m3) as WM.
replace (ret_pc (wz 656804)) with (wz 656804) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
stash SB3.
reenterA asegs A4L HIx asegs_wx HP3.
bstep. bstep.
unstash SB3.
evt_done5.
eapply (sc_grow2 m3 md3 A3 _ fj e2 PBS q cap pb junk0 junk (wz len0) (wz pd));
[ exact FR1 | exact ST3 | exact (model_vm_only_trans _ _ _ VM02 VM3) | | exact ERR3 | exact HP3 | | exact SB3 | exact UN3 | exact QB
| unfold jhdr_cells; cbn [app]; exact HDR | | exact Hcap | exact Hn | exact SR ].
* eapply heap_pres_trans; [exact HPR02|]. eapply heap_pres_weaken; [exact HPR3 | lia |].
intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; right; right; apply in_or_app; right; exact Hb | right; exact Hb].
* unfold jo_chargeA, ss_costB, charge; cbn [bB bD uw_cost]; split; lia.
* eapply opt_pbuf_agree; [exact OPB | | apply incl_refl]. eapply agree_on_trans.
-- eapply agree_on_incl; [exact AG2 | intros b Hb; right; right; exact Hb].
-- eapply (agree_of_heap_pres asegs A4H); [exact HPR3 | reflexivity | intros b Hb; apply in_or_app; left; right; right; apply in_or_app; left; exact Hb].
Qed.

Lemma sc_main : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (A : ASA A4L HIx),
HEAPAx A (BS ++ LB) LM FRS B0 m0 md0 -> stk asegs m0 lo (bv_unsigned sp) -> rw_cells asegs m0 6444156 [C4 errv] ->
jroot_repA r m0 BS p ->
bytes_at asegs m0 S sb -> (sb <> [] -> unpoisoned asegs m0 A_SB S n) ->
AJ5 A4L HIx A T md0
(MS (mkR ra sp gp (wz 6444320) t0 t1 t2 s0 s1 (wz p) (wz S) (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0xa04c4) fc None m0 (seg_rom asegs)).
Proof.
intros until A. intros HP ST ERR RR SB UN.
unfold SS_STK_A in LOS.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (wmono_refl asegs m0) as WM.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND0.
assert (ND : List.NoDup (map blk_addr BS)) by exact (nodup_app_l' _ _ (nodup_app_l' _ _ ND0)).
pose proof alloc_ceiling_range as ACR.
assert (Hn0 : 0 <= n) by (subst n; lia).
assert (CH0 : jo_chargeA (ss_costB n) 2 B0 B0) by (unfold jo_chargeA, ss_costB; split; lia).
carve_frame 80%nat ST.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m0) as MU.
stash SB.
a4l. reenterA asegs A4L HIx asegs_wx HP.
do 10 bstep. bstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => rename mX into m2 end.
unstash SB.

assert (XHP : HEAPAx A (BS ++ LB) LM FRS B0 m2 md0) by (heap_nowA A4L HIx HP MU WM MI).
assert (XHPR : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m2).
{ eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb] | clia | solve_clientWA A4L HIx HP]. }
assert (XAG : agree_on asegs BS m0 m2).
{ eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros bb kk Hb. cbn.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ bb kk HP ltac:(apply in_or_app; left; apply in_or_app; left; exact Hb)) as (_ & _ & _ & Hh & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hh. split; [lia | exact I]. }
destruct (src_pres _ _ _ _ _ _ _ LB (bv_unsigned sp) m0 m2 Fs ks S sb HP HFS HS1 HS2 XHPR (conj SB UN)) as [SB2 UN2].
destruct (jroot_null_decA r) as [Er | NN].
{
rewrite Er in RR. destruct RR as [Ep EB]. rewrite Ep. if_lit. bstep. bstep.
evt_done5.
eapply (sc_exit m2 md0 A B0 [] _ 0 errv); [eassumption | eassumption | apply model_vm_only_refl | exact XHPR | eassumption | rewrite EB in XHP; exact XHP | exact CH0 | | |].
- rewrite Er. split; [exact Ep | reflexivity].
- intros Hs. exfalso. rewrite Er in Hs. discriminate.
- intros _. symmetry. exact EB. }
destruct (jroot_str_casesA r m0 BS p RR NN ND) as (Hp & CASES).
assert (PB : exists pn, In (p, pn) BS).
{ destruct CASES as [((pb & PBS & DBS & cap & len0 & str & EBS & _) & _) | (_ & _ & n0 & ty & tojs & pb & udel & ud & rest & INp & _)];
[exists (48 + cap); rewrite EBS; left; reflexivity | exists n0; exact INp]. }
destruct PB as (pn & INp).
assert (INpA : In (p, pn) (BS ++ LB)) by (apply in_or_app; left; exact INp).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p pn XHP ltac:(apply in_or_app; left; exact INpA)) as (Hpn0 & Hpal & Hplo & Hphi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ p pn XHP ltac:(apply in_or_app; left; exact INpA)) as Hpimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hpimg.
assert (N48 : 48 <= pn).
{ destruct CASES as [((pb & PBS & DBS & cap & len0 & str & EBS & _ & Hc & _) & _) | (_ & _ & n0 & ty & tojs & pb & udel & ud & rest & INp' & _ & N48' & _)].
- rewrite (nodup_addr_size BS p pn (48 + cap) ND INp ltac:(rewrite EBS; left; reflexivity)). lia.
- rewrite (nodup_addr_size BS p pn n0 ND INp INp'). exact N48'. }
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p pn 0 XHP INpA ltac:(lia) ltac:(lia)) as SH0. rewrite Z.add_0_r in SH0.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p pn 5 XHP INpA ltac:(lia) ltac:(lia)) as SH5. replace (p / 8 + 2147450880 + 5) with (p / 8 + 2147450885) in SH5 by lia.
if_falsex.
do 3 bstep.
asan_chkA.
bstep. bstep. bstep. bstep. if_falsex.
destruct CASES as [(X & SR) | (SR & NSR & n0 & ty & tojs & pb & udel & ud & rest & INp' & SZ & N48' & TY & NS & HDR)].
2:{
rewrite (nodup_addr_size BS p pn n0 ND INp INp') in *.
unfold jhdr_cells in HDR, SZ. cbn [app hl_segs hla_base A4L A4H] in HDR, SZ.
apply (rw_cells_agree asegs BS m0 m2) in HDR; [| exact XAG | exists p, n0; split; [exact INp' | cbn [cells_size csize Nat.add app] in SZ |- *; rewrite <- SZ; lia]].
unfold JT_STRING in NS. bstep. rewrite sx32_small by lia. bstep. bstep. if_truex.
evt_done5.
eapply (sc_exit m2 md0 A B0 BS _ 0 errv); [eassumption | eassumption | apply model_vm_only_refl | exact XHPR | eassumption | exact XHP | exact CH0 | | |].
- rewrite SR. eapply (QrIB.Mq0.jroot_rep_agree A4H A4F); [exact RR | exact XAG | apply incl_refl].
- intros Hs. exfalso. rewrite NSR in Hs. discriminate.
- intros _. reflexivity. }

pose proof (QrIB.Mq0.xstr_agree A4H A4F _ _ _ _ _ _ X XAG (incl_refl _)) as X2.
destruct X as (pb & PBS & DBS & cap & len0 & str & EBS & OPB & Hcap & Hlen0 & Hstr & ALT).
rewrite (nodup_addr_size BS p pn (48 + cap) ND INp ltac:(rewrite EBS; left; reflexivity)) in *.
assert (OPB2 : opt_pbuf asegs m2 PBS pb).
{ eapply opt_pbuf_agree; [exact OPB | exact XAG | rewrite EBS; intros b Hb; right; apply in_or_app; right; exact Hb]. }
assert (HDRX : exists tl, rw_cells asegs m0 p (jhdr_cells JT_STRING 1 (fn_str_to_json_string A4F) pb 0 0 ++ C8 (wz len0) :: tl)
/\ Z.of_nat (cells_size (jhdr_cells JT_STRING 1 (fn_str_to_json_string A4F) pb 0 0 ++ C8 (wz len0) :: tl)) = 48 + cap).
{ destruct ALT as [(_ & _ & _ & jk & H) | (_ & pd & pdn & jk & jk2 & _ & _ & H & _)]; eexists; (split; [exact H|]);
unfold jhdr_cells; rewrite cells_size_app; cbn [cells_size csize Nat.add app]; lia. }
destruct HDRX as (tl & HDR & SZ). unfold jhdr_cells in HDR, SZ. cbn [app hl_segs hla_base A4L A4H] in HDR, SZ.
apply (rw_cells_agree asegs BS m0 m2) in HDR; [| exact XAG | exists p, (48 + cap); split; [rewrite EBS; left; reflexivity | rewrite SZ; lia]].
bstep. rewrite sx32_small by (unfold JT_STRING; lia). bstep. bstep. unfold JT_STRING. if_lit.
bstep. asan_chkA.
bstep. bstep.
clear HDR.
destruct ALT as [(Hl0 & EDBS & Hfit & jk & CELLS) | (Hl0 & pd & pdn & jk & jk2 & EDBS & Hpdn & CELLS & PD)].
-
subst DBS. cbn [app] in EBS.
if_falsex.
bstep. bstep. bstep. bstep.
unfold jhdr_cells in CELLS. cbn [app hl_segs hla_base A4L A4H] in CELLS.
apply (rw_cells_agree asegs BS m0 m2) in CELLS; [| exact XAG | exists p, (48 + cap); split; [rewrite EBS; left; reflexivity | cbn [cells_size csize Nat.add app]; lia]].
apply rw_cells_app with (cs1 := [_;_;_;_;_;_]) in CELLS as [HD LEN]. cbn [cells_size csize Nat.add] in LEN. change (p + Z.of_nat 40) with (p + 40) in LEN.
apply rw_cells_app with (cs1 := [_]) in LEN as [LEN DATA]. cbn [cells_size csize Nat.add] in DATA. change (p + 40 + Z.of_nat 8) with (p + 40 + 8) in DATA.
replace (p + 40 + 8) with (p + 48) in DATA by lia.
destruct (Z.lt_ge_cases len0 n) as [GROW | FIT].
+
if_falsex.
pose proof (Q6Vi.Mq1.rw_cells_CB_word asegs _ _ _ _ DATA ltac:(lia)) as DATA'.
assert (HDRG : rw_cells asegs m2 p (jhdr_cells JT_STRING 1 (fn_str_to_json_string A4F) pb 0 0 ++
[C8 (wz len0); C8 (le_bytes_to_word (firstn 8 (str ++ [Z_to_bv 8 0] ++ jk))); CB (Z.to_nat (cap - 8)) (skipn 8 (str ++ [Z_to_bv 8 0] ++ jk))])).
{ unfold jhdr_cells. cbn [app]. replace (Z.to_nat (cap - 8)) with (Z.to_nat cap - 8)%nat by lia. Q6Vi.Mq1.hdr_join HD LEN DATA'. }
evt_done5.
eapply sc_grow with (A1 := A) (PBS := PBS) (DBS := []) (cap := cap) (pb := pb);
[ eassumption | eassumption | apply model_vm_only_refl | exact XHPR | eassumption | rewrite EBS in XHP; exact XHP | exact SB2 | exact UN2 | exact HDRG
| exact OPB2 | exact Hcap | lia | rewrite EBS in X2; exact X2 | lia | lia | left; split; [lia | reflexivity] | exact SR ].
+
if_truex.
bstep. if_lit. bstep. bstep.
evt_done5.
eapply sc_tail with (A1 := A) (BS1 := BS) (D := p + 48) (k := Z.to_nat cap) (junk := str ++ [Z_to_bv 8 0] ++ jk) (lenw := wz len0) (bD := p) (szD := 48 + cap) (pn := 48 + cap);
[ eassumption | eassumption | apply model_vm_only_refl | exact XHPR | eassumption | exact XHP | exact CH0 | exact SB2 | exact UN2 | exact DATA | lia
| rewrite EBS; left; reflexivity | lia | lia | exact LEN | rewrite EBS; left; reflexivity | lia | left; lia | exact SR
| exists n; split; [reflexivity | lia] |].
intros m3 MU3 WM3 MI3 DST3 LEN3.
exists BS. split; [apply Permutation_refl|]. split; [exact Hp|].
exists pb, PBS, (@nil blk), cap, n, sb. split; [exact EBS|]. split.
{ eapply opt_pbuf_agree; [exact OPB2 | | apply incl_refl]. eapply (agree_of_munch asegs); [exact MU3 | exact WM3 |].
intros a k' Hin.
assert (INa : In (a, k') ((BS ++ LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; left; rewrite EBS; right; exact Hin).
assert (Hpa : p <> a).
{ intros <-. pose proof ND as NDB. rewrite EBS in NDB. cbn in NDB. inversion NDB as [|x_ l_ Hni Hnd]; subst x_ l_. apply Hni. exact (in_map blk_addr _ _ Hin). }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ p (48 + cap) a k' XHP ltac:(apply in_or_app; left; exact INpA) INa Hpa) as D1.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k' XHP INa) as (Hk' & _ & _ & Hh & _).
cbn. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
split; [lia|]. split; [lia|]. split; [subst n; lia|].
left. split; [lia|]. split; [reflexivity|]. split; [lia|]. exists (skipn (Z.to_nat (n + 1)) (str ++ [Z_to_bv 8 0] ++ jk)).
unfold jhdr_cells. cbn [app hl_segs hla_base A4L A4H].
lazymatch type of MU3 with munch ?W _ _ =>
apply (rw_cells_transport asegs W m2 m3) in HD; [| exact MU3 | exact WM3 | cbn [disjoint_from]; cbn; lia] end.
Q6Vi.Mq1.hdr_join HD LEN3 DST3.
-
subst DBS. cbn [app] in EBS.
if_truex.
unfold jhdr_cells in CELLS. cbn [app hl_segs hla_base A4L A4H] in CELLS.
apply (rw_cells_agree asegs BS m0 m2) in CELLS; [| exact XAG | exists p, (48 + cap); split; [rewrite EBS; left; reflexivity | cbn [cells_size csize Nat.add app]; lia]].
assert (INpdA : In (pd, pdn) ((BS ++ LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; left; rewrite EBS; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ pd pdn XHP INpdA) as (Hpdn0 & Hpdal & Hpdlo & Hpdhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ pd pdn XHP INpdA) as Hpdimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hpdimg.
assert (Hppd : p <> pd).
{ intros E. pose proof ND as NDB. rewrite EBS in NDB. cbn in NDB. inversion NDB as [|x_ l_ Hni Hnd]; subst x_ l_. apply Hni. left. symmetry. exact E. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ p (48 + cap) pd pdn XHP ltac:(apply in_or_app; left; exact INpA) INpdA Hppd) as DPD.
apply (rw_cells_agree asegs BS m0 m2) in PD; [| exact XAG | exists pd, pdn; split; [rewrite EBS; right; left; reflexivity | cbn; lia]].
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p (48 + cap) 6 XHP INpA ltac:(lia) ltac:(lia)) as SH6.
replace (p / 8 + 2147450880 + 6) with ((p + 48) / 8 + 2147450880) in SH6 by (rewrite (div8_add p 48) by lia; change (48 / 8) with 6; lia).
bstep.
destruct (Z.eq_dec n 0) as [N0 | N1].
2:{
if_falsex.

bstep. bstep. rewrite Q6Vi.Mq1.neg_word_negval by lia. bstep. bstep.
rewrite (v_slt_0 (Z_to_bv 64 0) (Z_to_bv 64 len0)) by (rewrite !signed_lit by lia; lia).
rewrite (v_slti_0 (Z_to_bv 64 (- len0)) 0) by (rewrite zsig_lit by lia; lia).
if_lit.
bstep. rewrite ?zxb_zero. bstep. if_false.
bstep. bstep. bstep. if_truex.
bstep. rewrite (unsigned_lit (p + 48)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
bstep. bstep. rewrite ?zxb_zero. bstep. if_false.
apply rw_cells_app with (cs1 := [_;_;_;_;_;_]) in CELLS as [HD LEN]. cbn [cells_size csize Nat.add] in LEN. change (p + Z.of_nat 40) with (p + 40) in LEN.
apply rw_cells_app with (cs1 := [_]) in LEN as [LEN PDC]. cbn [cells_size csize Nat.add] in PDC. change (p + 40 + Z.of_nat 8) with (p + 40 + 8) in PDC.
replace (p + 40 + 8) with (p + 48) in PDC by lia.
bstep. bstep. bstep.
destruct (Z.lt_ge_cases (- len0) n) as [GROW | FIT].
*
if_truex.
evt_done5.
eapply sc_grow with (A1 := A) (PBS := PBS) (DBS := [(pd, pdn)]) (cap := cap) (pb := pb);
[ eassumption | eassumption | apply model_vm_only_refl | exact XHPR | eassumption | rewrite EBS in XHP; exact XHP | exact SB2 | exact UN2
| unfold jhdr_cells; cbn [app]; Q6Vi.Mq1.hdr_join HD LEN PDC
| exact OPB2 | exact Hcap | lia | rewrite EBS in X2; exact X2 | lia | lia | right; split; [lia | exists pd, pdn; split; reflexivity] | exact SR ].
*
if_falsex.
bstep. if_lit. bstep.
evt_done5.
eapply sc_tail with (A1 := A) (BS1 := BS) (D := pd) (k := Z.to_nat pdn) (junk := str ++ [Z_to_bv 8 0] ++ jk2) (lenw := wz len0) (bD := pd) (szD := pdn) (pn := 48 + cap);
[ eassumption | eassumption | apply model_vm_only_refl | exact XHPR | eassumption | exact XHP | exact CH0 | exact SB2 | exact UN2 | exact PD | lia
| rewrite EBS; right; left; reflexivity | lia | lia | exact LEN | rewrite EBS; left; reflexivity | lia | lia | exact SR
| exists (- n); split; [apply neg_word_negvalA; lia | lia] |].
intros m3 MU3 WM3 MI3 DST3 LEN3.
exists BS. split; [apply Permutation_refl|]. split; [exact Hp|].
exists pb, PBS, [(pd, pdn)], cap, (- n), sb. split; [exact EBS|]. split.
{ eapply opt_pbuf_agree; [exact OPB2 | | apply incl_refl]. eapply (agree_of_munch asegs); [exact MU3 | exact WM3 |].
intros a k' Hin.
pose proof ND as NDB. rewrite EBS in NDB.
assert (INa : In (a, k') ((BS ++ LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; left; rewrite EBS; right; right; exact Hin).
assert (Hpa : p <> a).
{ intros <-. cbn in NDB. inversion NDB as [|x_ l_ Hni Hnd]; subst x_ l_. apply Hni. right. exact (in_map blk_addr _ _ Hin). }
assert (Hpda : pd <> a).
{ intros <-. cbn in NDB. inversion NDB as [|x_ l_ Hni Hnd]; subst x_ l_. inversion Hnd as [|x2_ l2_ Hni2 Hnd2]; subst x2_ l2_. apply Hni2. exact (in_map blk_addr _ _ Hin). }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ p (48 + cap) a k' XHP ltac:(apply in_or_app; left; exact INpA) INa Hpa) as D1.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ pd pdn a k' XHP INpdA INa Hpda) as D2.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k' XHP INa) as (Hk' & _ & _ & Hh & _).
cbn. split; [lia|]. split; [(clear - Hpdn FIT D2 Hpdn0; lia)|]. split; [(clear - Hcap D1; lia) | exact I]. }
split; [lia|]. split; [lia|]. split; [subst n; lia|].
right. split; [lia|]. exists pd, pdn, jk, (skipn (Z.to_nat (n + 1)) (str ++ [Z_to_bv 8 0] ++ jk2)). split; [reflexivity|]. split; [lia|]. split; [| exact DST3].
unfold jhdr_cells. cbn [app hl_segs hla_base A4L A4H].
lazymatch type of MU3 with munch ?W _ _ =>
apply (rw_cells_transport asegs W m2 m3) in HD; [| exact MU3 | exact WM3 | cbn [disjoint_from]; cbn; (clear - Hcap Hpdn0 DPD Hphi LO Hplo; lia)];
apply (rw_cells_transport asegs W m2 m3) in PDC; [| exact MU3 | exact WM3 | cbn [disjoint_from]; cbn [cells_size csize Nat.add]; (clear - Hcap Hl0 Hpdn DPD Hphi LO Hplo; lia)] end.
rewrite Q6Vi.Mq1.neg_word_negval in LEN3 by lia.
Q6Vi.Mq1.hdr_join HD LEN3 PDC. }

if_truex.
bstep. bstep. bstep. bstep. bstep.
rewrite (unsigned_lit (p + 48)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
bstep. rewrite ?zxb_zero. bstep. if_false.
bstep. bstep. bstep.
evt_done5.
eapply (hiA_free A4L HIx) with (p := pd) (u := UWpaid) (lo := lo) (errv := errv);
[ exact XHP | right; exists pdn; apply in_or_app; left; rewrite EBS; right; left; reflexivity | .. ].
all: rewrite ?unsigned_lit by lia.
1: eassumption.
1: exact LO.
1: cbn [hl_stack_A A4L]; lia.
1: clear - SPA; Z.div_mod_to_equations; lia.
1: lia.
1: cbn [hl_segs hl_tp hla_base A4L A4H]; unfold A_TP; eassumption.
1: reflexivity.
1: reflexivity.
1: split; cbn; exact I.
1: unfold ss_costB in BB0; lia.
1: destruct (Z.eqb pd 0); cbn [uw_cost]; lia.
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3.
cbn [hl_segs hl_tp hla_base A4L A4H] in ST3, HPR3, ERR3, HP3. unfold A_TP in ERR3. change (6444320 - 164) with 6444156 in ERR3.
rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in ST3, HPR3 by lia.
rewrite EBS in HPR3, HP3. cbn [app] in HPR3, HP3.
rewrite (lb_remove_other pd) in HPR3, HP3 by (cbn; lia). rewrite lb_remove_head in HPR3, HP3.
replace (if pd =? 0 then 0 else uw_cost UWpaid) with 1 in HP3 by (destruct (Z.eqb_spec pd 0); [lia | reflexivity]).
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. cbn [hl_segs hla_base A4L A4H] in FR.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in CELLS; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs hla_base A4L A4H] in CELLS.
lazymatch type of HPR3 with heap_pres _ (?LX ++ LM ++ _) _ ?ma _ =>
destruct (src_pres _ _ _ _ _ _ _ LX (bv_unsigned sp + -80) ma m3 Fs ks S sb XHP HFS HS1 HS2 HPR3 (conj SB2 UN2)) as [SB3 UN3] end.
assert (OPB3 : opt_pbuf asegs m3 PBS pb).
{ eapply opt_pbuf_agree; [exact OPB2 | | apply incl_refl].
eapply (agree_of_heap_pres asegs A4H); [exact HPR3 | reflexivity | intros b Hb; apply in_or_app; left; right; apply in_or_app; left; exact Hb]. }
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI3. cbn [hl_segs hla_base A4L A4H] in MI3.
assert (INp3 : In (p, 48 + cap) (((p, 48 + cap) :: PBS ++ LB))) by (left; reflexivity).
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p (48 + cap) 5 HP3 INp3 ltac:(lia) ltac:(lia)) as SH5c.
replace (p / 8 + 2147450880 + 5) with (p / 8 + 2147450885) in SH5c by lia.
clear MU WM. pose proof (munch_refl [(p + 40, p + 48)] m3) as MU. pose proof (wmono_refl asegs m3) as WM.
replace (ret_pc (wz 0xa0620)) with (wz 0xa0620) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
stash SB3.
reenterA asegs A4L HIx asegs_wx HP3.
bstep. rewrite ?zxb_zero. bstep. if_false.
bstep. bstepz. bstep. bstep. bstep. bstep.
bstep. bstep. bstep. bstep.
if_truex. bstep. if_lit. bstep. bstep.
unstash SB3.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => rename mX into m4 end.
lazymatch goal with H : rw_cells asegs m4 p ?cs |- _ => rename H into CELLS4 end.
assert (HP4 : HEAPAx A3 (((p, 48 + cap) :: PBS) ++ LB) LM FRS (charge B0 512 1) m4 md3).
{ eapply (heapA_client_frame A4L HIx); [exact HP3 | | exact WM | assumption].
eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP3 MU).
apply Forall_cons; [right; left; exists p, (48 + cap); cbn [fst snd]; split; [apply in_or_app; left; left; reflexivity | lia] | apply Forall_nil]. }
assert (HPR34 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m3 m4).
{ eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx);
[ exact HP3 | intros ? Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; right; apply in_or_app; right; exact Hb | right; exact Hb] | clia | ].
apply Forall_cons; [right; left; exists p, (48 + cap); cbn [fst snd]; split; [apply in_or_app; left; left; reflexivity | split; [| lia]] | apply Forall_nil].
exact (blk_not_pres A3 ((p, 48 + cap) :: PBS) _ _ _ _ _ HP3 ltac:(left; reflexivity)). }
assert (HPR04 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m4).
{ eapply heap_pres_trans; [exact XHPR|]. eapply heap_pres_trans; [| exact HPR34].
eapply heap_pres_weaken; [exact HPR3 | lia |].
intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; right; apply in_or_app; right; exact Hb | right; exact Hb]. }
destruct (src_pres _ _ _ _ _ _ _ LB (bv_unsigned sp) m3 m4 Fs ks S sb HP3 HFS HS1 HS2 HPR34 (conj SB3 UN3)) as [SB4 UN4].
apply rw_cells_app with (cs1 := [_;_;_;_;_;_]) in CELLS4 as [HD LEN]. cbn [cells_size csize Nat.add] in LEN. change (p + Z.of_nat 40) with (p + 40) in LEN.
apply rw_cells_app with (cs1 := [_]) in LEN as [LEN DATA]. cbn [cells_size csize Nat.add] in DATA. change (p + 40 + Z.of_nat 8) with (p + 40 + 8) in DATA.
replace (p + 40 + 8) with (p + 48) in DATA by lia.
apply (rw_cells_recast asegs _ _ _ [CB (Z.to_nat cap) (le8 (wz pd) ++ jk)]) in DATA;
[| split; [| exact I]; cbn [cell_wf]; rewrite length_app, length_le8; destruct DATA as [[[_ [Hw _]] _] _]; cbn [cell_wf] in Hw; lia
| cbn [cells_bytes cbytes app]; rewrite <- app_assoc; reflexivity | cbn; lia].
evt_done5.
eapply sc_tail with (A1 := A3) (BS1 := (p, 48 + cap) :: PBS) (D := p + 48) (k := Z.to_nat cap) (junk := le8 (wz pd) ++ jk) (bD := p) (szD := 48 + cap) (pn := 48 + cap);
[ eassumption | eassumption | exact VM3 | exact HPR04 | eassumption | exact HP4 | unfold jo_chargeA, ss_costB, charge; cbn [bB bD]; split; lia
| exact SB4 | exact UN4 | exact DATA | lia
| left; reflexivity | lia | lia | exact LEN | left; reflexivity | lia | left; lia | exact SR
| exists n; split; [reflexivity | lia] |].
intros m5 MU5 WM5 MI5 DST5 LEN5.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP3) as ND3.
exists ((p, 48 + cap) :: PBS). split; [apply Permutation_refl|]. split; [exact Hp|].
exists pb, PBS, (@nil blk), cap, 0, (@nil byte). split; [reflexivity|]. split.
{ eapply opt_pbuf_agree; [exact OPB3 | | apply incl_refl].
eapply agree_on_trans; (eapply (agree_of_munch asegs); [eassumption | eassumption |]); intros a k' Hin;
(assert (INa : In (a, k') (((p, 48 + cap) :: PBS ++ LB) ++ LM)) by (apply in_or_app; left; right; apply in_or_app; left; exact Hin));
(assert (Hpa : p <> a) by (intros <-; cbn in ND3; inversion ND3 as [|x_ l_ Hni Hnd]; subst x_ l_; apply Hni; rewrite !map_app; apply in_or_app; left; apply in_or_app; left; exact (in_map blk_addr _ _ Hin)));
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ p (48 + cap) a k' HP3 ltac:(apply in_or_app; left; left; reflexivity) INa Hpa) as D1;
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k' HP3 INa) as (Hk' & _ & _ & Hh & _); cbn; [split; [lia | exact I] | split; [lia|]; split; [lia|]; split; [lia | exact I]]. }
split; [lia|]. split; [lia|]. split; [cbn; lia|].
left. split; [lia|]. split; [reflexivity|]. split; [lia|]. exists (skipn (Z.to_nat (n + 1)) (le8 (wz pd) ++ jk)).
unfold jhdr_cells. cbn [app hl_segs hla_base A4L A4H].
lazymatch type of MU5 with munch ?W _ _ =>
apply (rw_cells_transport asegs W m4 m5) in HD; [| exact MU5 | exact WM5 | cbn [disjoint_from]; cbn; lia] end.
assert (Esb : sb = []) by (destruct sb; [reflexivity | exfalso; subst n; cbn [length] in N0; lia]).
rewrite Esb in DST5. cbn [app] in DST5 |- *. rewrite N0 in LEN5.
Q6Vi.Mq1.hdr_join HD LEN5 DST5.
Qed.
End BodyC.

Theorem set_string_len_A : jo_set_string_len_A_stmt HIx 0xa0748 SS_STK_A 2 ss_costB.
Proof.
unfold jo_set_string_len_A_stmt. intros until errv. intros (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA) RR (SB & (Fs & ks & HFS & HS1 & HS2) & UN) LSB BB BD A0 A1 A2 K.
subst a0 a1 a2 tp. word_range sp SPR. unfold A_ERRNO, A_TP in *. change (6444320 - 164) with 6444156 in ERR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU.
stash SB.
a4l. reenterA asegs A4L HIx asegs_wx HP.
bstep.
unstash SB.
evt_done5.
eapply (sc_main ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB BS LM FRS B lo p S sb r T errv Fs ks); try eassumption.
Qed.

Theorem set_string_A : jo_set_string_A_stmt HIx 0xa0484 SS_STK_A 2 ss_costB.
Proof.
unfold jo_set_string_A_stmt. intros until errv. intros (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA) RR (SB & NZ & PAD & (Fs & ks & HFS & HS1 & HS2) & UN) LSB BB BD A0 A1 K.
subst a0 a1 tp. word_range sp SPR. unfold A_ERRNO, A_TP in *. change (6444320 - 164) with 6444156 in ERR. unfold SS_STK_A in LOS.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof alloc_ceiling_range as ACR.
pose proof (hiA_top_le A4L HIx) as HT47.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP HFS) as (_ & _ & HF0 & HFc & _).
pose proof (asan_rt_ok_of_HEAPA HIx _ _ _ _ _ _ _ HP) as RT.
assert (NONUL : ~ In (Z_to_bv 8 0) sb) by (intros Hin; exact (proj1 (Forall_forall _ _) NZ _ Hin eq_refl)).
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
pose proof ST as ST0. carve_frame 32%nat ST.
stash SB.
a4l. reenterA asegs A4L HIx asegs_wx HP.
do 4 bstep. bstep. bstep. bstep. bstep.
unstash SB.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (SBc : bytes_at asegs mc S (sb ++ Z_to_bv 8 0 :: slack));
[ eapply (bytes_at_transport asegs); [exact SB | exact MU | cbn [disjoint_from]; rewrite length_app; cbn [length]; lia] |];
assert (UNc : unpoisoned asegs mc A_SB S (Z.of_nat (length sb) + 1));
[ eapply unpoisoned_transport; [exact UN | exact MU |]; intros a kk Ha Hkk; cbn [disjoint_from]; unfold shadow_span_lo, A_SB in Ha; unfold shadow_span_hi, A_SB in Hkk; repeat split; Z.div_mod_to_equations; lia |];
assert (RTc : asan_rt_ok mc)
end.
{ eapply (asan_rt_ok_of_HEAPA HIx). heap_nowA A4L HIx HP MU WM MI. }
eapply OBL_ASTRLEN_U with (s := S) (lo := lo) (str := sb) (slack := slack);
[ exact UNc | exact RTc | lia | lia | left; rewrite ?unsigned_lit by lia; lia | reflexivity | exact NONUL | lia | left; lia
| exact SBc | exact PAD | rewrite ?unsigned_lit by lia; eassumption | exact LO | rewrite ?unsigned_lit by lia; lia
| rewrite ?unsigned_lit by lia; clear - SPA; Z.div_mod_to_equations; lia | assumption | rewrite ?unsigned_lit by lia; reflexivity | ].
rewrite ?unsigned_lit by lia.
intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m3 MU3 WM3 MI3 SB3 ST3.
lazymatch type of MU3 with munch _ ?mq _ =>
transport_after_call asegs mq m3 MU3 WM3; try match goal with H : mem_inv asegs mq |- _ => clear H end; clear MU3 WM3 end.
replace (ret_pc (wz 0xa04a4)) with (wz 0xa04a4) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
do 6 bstep.
release_frame FR ST3 (bv_unsigned sp).
bstep. bstep.
assert (HP3 : HEAPAx A (BS ++ LB) LM FRS B m3 md) by (heap_nowA A4L HIx HP MU WM MI3).
assert (HPR3 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m3).
{ eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb] | clia | solve_clientWA A4L HIx HP]. }
assert (AG3 : agree_on asegs BS m m3).
{ eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros bb kk Hb. cbn.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ bb kk HP ltac:(apply in_or_app; left; apply in_or_app; left; exact Hb)) as (_ & _ & _ & Hh & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hh. split; [lia | exact I]. }
assert (BY0 : bytes_at asegs m S sb) by (apply bytes_at_app in SB as [BYa _]; exact BYa).
assert (UN0 : sb <> [] -> unpoisoned asegs m A_SB S (Z.of_nat (length sb))).
{ intros NE. eapply (QsKa.Mqa.unpoisoned_sub_any asegs _ A_SB S (Z.of_nat (length sb) + 1)); [exact UN | lia | lia |]. destruct sb; [exfalso; exact (NE eq_refl) | cbn [length]; lia]. }
destruct (src_pres _ _ _ _ _ _ _ LB (bv_unsigned sp) m m3 Fs ks S sb HP HFS HS1 ltac:(lia) HPR3 (conj BY0 UN0)) as [BY3 UN3].
evt_done5.
eapply (sc_main ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m3 md LB BS LM FRS B lo p S sb r T errv Fs ks);
[ exact SPR | exact LO | unfold SS_STK_A; exact LOS | exact SPA | exact HT | exact HFS | exact HS1 | lia | exact LSB | exact BB | exact BD
| | exact HP3 | eassumption | eassumption | eapply (QrIB.Mq0.jroot_rep_agree A4H A4F); [exact RR | exact AG3 | apply incl_refl] | exact BY3 | exact UN3 ].
intros ms' md' m' rv A' B' BS' PF CH ROOT HPf KSL KBS. eapply K; [| exact CH | exact ROOT | exact HPf | exact KSL | exact KBS].
destruct PF as (RS & VM & STf & HPRf & ERRf). split; [exact RS|]. split; [exact VM|]. split; [exact STf|]. split; [eapply heap_pres_trans; [exact HPR3 | exact HPRf] | exact ERRf].
Qed.
End MJoSetString.
End RC__1.
End Mqd.

Module Mqe.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ. Import QTEu. Import Qsw7 QJjn QRUw QKQo.
Import Q6WR Q6WR.Mq0 QrPc.
Import QYIF.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqh QlKV.Mqj QsKa.Mqg QJZd.Mqd QpNt.Mq8 QW22.Mq6 QI6Z.Mq4 QlKV.Mqf QJZd.Mq9.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section PutX.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud) (lo : Z) (errv : word)
(BS : list blk) (x : Z) (T : TSet).

Lemma mf_xstrA :
forall (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x20 x21 x22 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud),
HEAPAx A (BS ++ LB) LM FRS B m md ->
xstr A4H A4F m BS x 0 ->
mf_frameA ra sp s0 s1 s2 s3 s4 s5 s6 m ->
stk asegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -64 - 16 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> bv_unsigned ra mod 2 = 0 ->
model_vm_only (cfg_model md0) (cfg_model md) -> heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m -> fsaved F F1 -> (frm0 fc -> frm0 fc1) ->
bD B0 <= bD B -> bB B0 <= bB B -> 512 * Z.of_nat (length BS) <= bB B ->
KPOSTA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo errv Sbool BS x 1 T ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 x) x9 a0 a1 a2 a3 a4 a5 a6 a7
x18 (Z_to_bv 64 A_SB) x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x9c30c) fc1 None m (seg_rom asegs)).
Proof.
intros until B. intros HP J FR ST LO LOS SPA HT ERR RA VM0 HPR FS FRM BD BB0 BB K.
pose proof FR as FR0. unfold mf_frameA in FR. unfold_consts. unfold A_SB, A_TP, A_ERRNO in *. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP) as [HB00 HD00].
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [] m) as MU.
destruct J as (pb & PBS & DBS & cap & len & str & EBS & OPB & Hcap & Hlen & Hsl & CASES).
destruct CASES as [(Hl0 & EDBS & Hfit & junk & HDR) | (Hl0 & pd & pdn & junk & junk2 & EDBS & HPD & HDR & HD)]; subst DBS BS.
-
cbn [app] in HP.
blk_factsA A4L HIx HP x (48 + cap) Hxal Hxlo Hxhi Hximg.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ x (48 + cap) HP ltac:(left; reflexivity)) as SHx. unfold shad in SHx. a4l.
assert (SH : ro_cells asegs m (x / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
{ rewrite (shadow_bytes_split (48 + cap) 6) in SHx by lia.
apply bytes_at_app in SHx as [SH6 _]. split; [cbn; repeat split; exact I | cbn [cells_bytes cbytes app]; exact SH6]. }
clear SHx.
pose proof HDR as HDR0. unfold jhdr_cells in HDR. cbn [app] in HDR.
cbn [length app] in BB. rewrite ?Nat2Z.inj_succ in BB.
reenterA asegs A4L HIx asegs_wx HP.
asan_chk0.
bstep. norm_w32. bstep. bstep. if_truex.
bstep.
asan_chkA.
bstep.
bstep. if_truex.
evt_done5.
eapply (mf_genA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo errv Sbool ((x, 48 + cap) :: [] ++ PBS) x 1 T);
[ exact HP | lia | exact HDR0 | exact OPB | exact FR0 | exact ST | clia | clia | exact SPA | exact HT
| exact ERR | exact RA | exact VM0 | exact HPR | exact FS | exact FRM | reflexivity
| exact BD | cbn [length app] in *; rewrite ?Nat2Z.inj_succ in *; lia | cbn [length app] in *; rewrite ?Nat2Z.inj_succ in *; lia | exact K ].
-
cbn [app] in HP.
blk_factsA A4L HIx HP x (48 + cap) Hxal Hxlo Hxhi Hximg.
blk_factsA A4L HIx HP pd pdn Hpal Hplo Hphi Hpimg.
assert (Hxpd : x <> pd).
{ intros E. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. cbn in ND. inversion ND as [|y l Hni Hnd]. apply Hni. left. symmetry. exact E. }
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ x (48 + cap) HP ltac:(left; reflexivity)) as SHx. unfold shad in SHx. a4l.
assert (SH : ro_cells asegs m (x / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
{ rewrite (shadow_bytes_split (48 + cap) 7) in SHx by lia.
apply bytes_at_app in SHx as [SH7 _]. split; [cbn; repeat split; exact I | cbn [cells_bytes cbytes app]; exact SH7]. }
clear SHx HD.
unfold jhdr_cells in HDR. cbn [app] in HDR.
cbn [length app] in BB. rewrite ?Nat2Z.inj_succ in BB.
reenterA asegs A4L HIx asegs_wx HP.
asan_chk0.
bstep. norm_w32. bstep. bstep. if_truex.
bstep.
asan_chkA.
bstep.
bstep. if_falsex.
bstep.
asan_chkA.
bstep. bstep.

alloc_callA (hiA_free A4L HIx) blk pd uw UWptr A4L HIx HP MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists pdn. right; left. reflexivity. }
all: try (cbn [uw_pre uw_ok uw_key uw_cost]; intros _; split; [left; lia | unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (destruct (Z.eqb_spec pd 0); cbn [bB bD charge uw_cost] in *; lia).
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3. a4l.
rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in HPR3 by lia.
rewrite lb_remove_other in HPR3, HP3 by (cbn; lia). rewrite lb_remove_head in HPR3, HP3.
replace (if pd =? 0 then 0 else uw_cost UWptr) with 0 in HP3 by (destruct (Z.eqb_spec pd 0); reflexivity).
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in HDR; [| eapply client_range_block; [left; reflexivity | lia | cbn [cells_size csize Nat.add]; lia]].
assert (OPB3 : opt_pbuf asegs m3 PBS pb).
{ eapply opt_pbuf_agree; [exact OPB | | apply incl_refl].
eapply (agree_of_heap_pres asegs A4H); [exact HPR3 | reflexivity | intros b Hb; apply in_or_app; left; right; apply in_or_app; left; exact Hb]. }
assert (HPRb : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m3).
{ eapply heap_pres_trans; [exact HPR|].
eapply heap_pres_weaken; [exact HPR3 | lia | intros b Hb; cbn; right; apply in_or_app; apply in_app_or in Hb; destruct Hb; [left; apply in_or_app; right; assumption | right; assumption]]. }
replace (ret_pc (Z_to_bv 64 0x9c3b8)) with (Z_to_bv 64 0x9c3b8) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
a4l.
eapply (mf_genA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo errv Sbool ((x, 48 + cap) :: [(pd, pdn)] ++ PBS) x 1 T);
[ exact HP3 | lia | unfold jhdr_cells; cbn [app]; exact HDR | exact OPB3 | unfold mf_frameA; exact FR | exact ST3 | clia | clia | exact SPA | exact HT
| exact ERR3 | exact RA | eapply model_vm_only_trans; [exact VM0 | exact VM3] | exact HPRb | exact FS | exact FRM | reflexivity
| cbn [bD charge] in *; lia | cbn [bB charge length app] in *; rewrite ?Nat2Z.inj_succ in *; lia | cbn [bB charge length app] in *; rewrite ?Nat2Z.inj_succ in *; lia | exact K ].
Qed.

Lemma mfx_entryA :
forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (n ty tojs pb : Z) (rest : list cell),
HEAPAx A (BS ++ LB) LM FRS B m md ->
In (x, n) BS -> 48 <= n ->
rw_cells asegs m x (jhdr_cells ty 1 tojs pb 0 0 ++ rest) -> Z.of_nat (cells_size (jhdr_cells ty 1 tojs pb 0 0 ++ rest)) = n ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 - 96 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 x -> a1 = Z_to_bv 64 0 ->
(forall m3 (y1 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 yt5 yt6 y9 y18 y20 y21 y22 : word),
HEAPAx A (BS ++ LB) LM FRS B m3 md ->
rw_cells asegs m3 x (jhdr_cells ty 0 tojs pb 0 0 ++ rest) ->
mf_frameA ra sp s0 s1 s2 s3 s4 s5 s6 m3 ->
stk asegs m3 lo (bv_unsigned sp + -64) ->
rw_cells asegs m3 A_ERRNO [C4 errv] ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m3 ->
agree_on asegs (others x BS) m m3 ->
AJ5 A4L HIx A T md
(MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 A_TP) yt0 yt1 yt2 (Z_to_bv 64 x) y9 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7
y18 (Z_to_bv 64 A_SB) y20 y21 y22 s7 s8 s9 s10 s11 yt3 yt4 yt5 yt6)
F (Z_to_bv 64 0x9c30c) fc None m3 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9c240) fc None m (seg_rom asegs)).
Proof.
intros until rest. intros HP INx N48 HDR SZ ST LO LOS SPA HT ERR RA A0 A1 KZ.
unfold_consts. unfold A_SB, A_TP, A_ERRNO in *. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP) as [HB00 HD00].
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
assert (INx2 : In (x, n) ((BS ++ LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; left; exact INx).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ x n HP INx2) as (_ & Hxal & Hxlo & Hxhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ x n HP INx2) as Hximg.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ x n HP ltac:(apply in_or_app; left; exact INx)) as SHx. unfold shad in SHx.
a4l.
assert (SH : ro_cells asegs m (x / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
{ rewrite (shadow_bytes_split n 6) in SHx by lia.
apply bytes_at_app in SHx as [SH6 _]. split; [cbn; repeat split; exact I | cbn [cells_bytes cbytes app]; exact SH6]. }
clear SHx.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (x + 4, x + 8)] m) as MU.
pose proof SZ as RSZ. rewrite cells_size_app in RSZ. cbn [cells_size csize jhdr_cells Nat.add] in RSZ.
unfold jhdr_cells in HDR. cbn [app] in HDR.
reenterA asegs A4L HIx asegs_wx HP. subst a0 a1.
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
if_true.
replace (1 + -1) with 0 in HDR by lia.
bstep; asan_chkA; bstep; bstep.
bstep. if_true.

clear MU WM.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI2.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ x n 3 x n HP1 ltac:(apply in_or_app; left; exact INx) ltac:(clear - N48; Z.div_mod_to_equations; lia) INx2) as SEP3.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ x n 4 x n HP1 ltac:(apply in_or_app; left; exact INx) ltac:(clear - N48; Z.div_mod_to_equations; lia) INx2) as SEP4.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ x n HP1 ltac:(apply in_or_app; left; exact INx)) as SHx2. unfold shad in SHx2. a4l.
pose proof (shadow_granule0 asegs m1 (x / 8 + 2147450880) n 3 ltac:(lia) ltac:(lia) SHx2) as SH3.
pose proof (shadow_granule0 asegs m1 (x / 8 + 2147450880) n 4 ltac:(lia) ltac:(lia) SHx2) as SH4.
replace (x / 8 + 2147450880 + 3) with (x / 8 + 2147450883) in SH3 by lia.
replace (x / 8 + 2147450880 + 4) with (x / 8 + 2147450884) in SH4 by lia. clear SHx2.
pose proof (wmono_refl asegs m1) as WM. pose proof (munch_refl [(x + 24, x + 40)] m1) as MU.
bstep. rewrite ?zxb_zero. bstep. if_false.
bstepz.
bstep. bstep. sh_norm. rewrite (div8_add x 32) by lia. change (32 / 8) with 4.
bstep. rewrite ?zxb_zero. bstep. if_false.
bstepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (AG4 : agree_on asegs (others x BS) m1 mc);
[ eapply (agree_others_gen asegs); [exact MU | exact WM |]; intros a k Hin Hne;
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP1 ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin)) as (Hk & _ & _ & Hahi & _);
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ x n a k HP1 INx2 ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin) ltac:(congruence)) as D;
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hahi; cbn; lia |]
end.
evt_done5.
eapply KZ.
- lazymatch goal with Hmi : mem_inv asegs ?mc |- HEAPA _ _ _ _ _ _ _ ?mc _ => heap_nowA A4L HIx HP1 MU WM Hmi end.
- unfold jhdr_cells. cbn [app]. exact HDR.
- unfold mf_frameA. first [ eassumption | lazymatch goal with |- rw_cells _ ?mc _ _ => eapply (rw_cells_transport asegs _ m1 mc) in FR; [exact FR | exact MU | exact WM | cbn [disjoint_from]; lia] end ].
- assumption.
- first [ assumption | lazymatch goal with |- rw_cells _ ?mc _ _ => eapply (rw_cells_transport asegs _ m1 mc) in ERR; [exact ERR | exact MU | exact WM | cbn [disjoint_from]; lia] end ].
- eapply heap_pres_trans; [exact HPR1|].
eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP1 | intros b Hb; rewrite <- app_assoc; apply in_or_app; right; exact Hb | clia |].
apply Forall_cons; [cbn [fst snd] | apply Forall_nil]. right; left. exists x, n. split; [exact INx2|]. split; [| lia].
exact (not_in_app3 _ _ _ _ (nodup_prefix_suffix BS (LB ++ LM) x n n ltac:(pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP1) as NDx; rewrite <- app_assoc in NDx; exact NDx) INx) (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP1 INx2)).
- eapply agree_on_trans; [exact AG1 | exact AG4].
Qed.

Lemma maybe_free_x_A :
forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (A : ASA A4L HIx) (r : jroot),
HEAPAx A (BS ++ LB) LM FRS B0 m0 md0 ->
jroot_rep A4H A4F r m0 BS x -> match r with JRdblx _ | JRstrx => True | _ => False end ->
stk asegs m0 lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 - 96 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m0 A_ERRNO [C4 errv] -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 x -> a1 = Z_to_bv 64 0 ->
512 * Z.of_nat (length BS) <= bB B0 ->
KPOSTA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo errv Sbool BS x 1 T ->
AJ5 A4L HIx A T md0
(MS (mkR ra sp gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9c240) fc None m0 (seg_rom asegs)).
Proof.
intros until r. intros HP J XL ST LO LOS SPA HT ERR RA A0 A1 BB K.
pose proof (nodup_app_l' BS LB (nodup_app_l' (BS ++ LB) LM (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP))) as ND.
pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP) as [HB00 HD00].
destruct r as [|s|tojs|]; try contradiction.
-
destruct J as (Hx & Htojs & pb & PBS & bits & EBS & OPB & HDR).
assert (INx : In (x, 48) BS) by (rewrite EBS; left; reflexivity).
eapply (mfx_entryA t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m0 md0 A B0 48 JT_DOUBLE tojs pb [C8 bits]);
[ exact HP | exact INx | lia | exact HDR | reflexivity | exact ST | exact LO | exact LOS | exact SPA | exact HT | exact ERR | exact RA | exact A0 | exact A1 | ].
intros m3 y1 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 yt5 yt6 y9 y18 y20 y21 y22 HP3 HDR3 FR3 ST3 ERR3 HPR3 AG3.
assert (AGT : agree_on asegs PBS m0 m3).
{ eapply agree_on_incl; [exact AG3|]. rewrite EBS. apply (incl_others_tail x 48 [] PBS PBS); [rewrite EBS in ND; exact ND | intros b Hb; exact Hb]. }
rewrite EBS in HP3. cbn [app] in HP3.
eapply (mf_scalarA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo errv Sbool BS x 1 T
y1 yt0 yt1 yt2 y9 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y18 y20 y21 y22 yt3 yt4 yt5 yt6 F fc m3 md0 A B0 48 JT_DOUBLE tojs pb [C8 bits] PBS);
[ exact HP3 | lia | exact HDR3 | right; left; reflexivity | eapply opt_pbuf_agree; [exact OPB | exact AGT | apply incl_refl]
| exact FR3 | exact ST3 | exact LO | clear - LOS; lia | exact SPA | exact HT | exact ERR3 | exact RA | apply model_vm_only_refl | exact HPR3
| apply fsaved_refl | intros Hf; exact Hf | reflexivity | lia
| rewrite EBS; cbn [length app]; lia | rewrite EBS in BB; cbn [length app] in BB; lia | exact K ].
-
destruct J as (Hx & pb & PBS & DBS & cap & len & str & EBS & OPB & Hcap & Hlen & Hsl & CASES).
assert (INx : In (x, 48 + cap) BS) by (rewrite EBS; left; reflexivity).
destruct CASES as [(Hl0 & EDBS & Hfit & junk & HDR) | (Hl0 & pd & pdn & junk & junk2 & EDBS & HPD & HDR & HD)]; subst DBS.
+
eapply (mfx_entryA t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m0 md0 A B0 (48 + cap) JT_STRING (fn_str_to_json_string A4F) pb
[C8 (wz len); CB (Z.to_nat cap) (str ++ [Z_to_bv 8 0] ++ junk)]);
[ exact HP | exact INx | lia | exact HDR
| rewrite cells_size_app; cbn [cells_size csize jhdr_cells Nat.add]; lia
| exact ST | exact LO | exact LOS | exact SPA | exact HT | exact ERR | exact RA | exact A0 | exact A1 | ].
intros m3 y1 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 yt5 yt6 y9 y18 y20 y21 y22 HP3 HDR3 FR3 ST3 ERR3 HPR3 AG3.
assert (AGT : agree_on asegs PBS m0 m3).
{ eapply agree_on_incl; [exact AG3|]. rewrite EBS. apply (incl_others_tail x (48 + cap) [] PBS PBS); [rewrite EBS in ND; exact ND | intros b Hb; exact Hb]. }
eapply (mf_xstrA y1 yt0 yt1 yt2 y9 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y18 y20 y21 y22 yt3 yt4 yt5 yt6 F fc m3 md0 A B0);
[ exact HP3 | | exact FR3 | exact ST3 | exact LO | clear - LOS; lia | exact SPA | exact HT | exact ERR3 | exact RA
| apply model_vm_only_refl | exact HPR3 | apply fsaved_refl | intros Hf; exact Hf | lia | lia | exact BB | exact K ].
exists pb, PBS, [], cap, len, str. split; [exact EBS|].
split; [eapply opt_pbuf_agree; [exact OPB | exact AGT | apply incl_refl]|].
split; [exact Hcap|]. split; [exact Hlen|]. split; [exact Hsl|]. left.
split; [exact Hl0|]. split; [reflexivity|]. split; [exact Hfit|]. exists junk. exact HDR3.
+
eapply (mfx_entryA t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m0 md0 A B0 (48 + cap) JT_STRING (fn_str_to_json_string A4F) pb
[C8 (wz len); C8 (wz pd); CB (Z.to_nat (cap - 8)) junk]);
[ exact HP | exact INx | lia | exact HDR
| rewrite cells_size_app; cbn [cells_size csize jhdr_cells Nat.add]; lia
| exact ST | exact LO | exact LOS | exact SPA | exact HT | exact ERR | exact RA | exact A0 | exact A1 | ].
intros m3 y1 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 yt5 yt6 y9 y18 y20 y21 y22 HP3 HDR3 FR3 ST3 ERR3 HPR3 AG3.
assert (AGT : agree_on asegs ([(pd, pdn)] ++ PBS) m0 m3).
{ eapply agree_on_incl; [exact AG3|]. rewrite EBS.
apply (incl_others_tail x (48 + cap) [] ([(pd, pdn)] ++ PBS) ([(pd, pdn)] ++ PBS)); [rewrite EBS in ND; exact ND | intros b Hb; exact Hb]. }
eapply (mf_xstrA y1 yt0 yt1 yt2 y9 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y18 y20 y21 y22 yt3 yt4 yt5 yt6 F fc m3 md0 A B0);
[ exact HP3 | | exact FR3 | exact ST3 | exact LO | clear - LOS; lia | exact SPA | exact HT | exact ERR3 | exact RA
| apply model_vm_only_refl | exact HPR3 | apply fsaved_refl | intros Hf; exact Hf | lia | lia | exact BB | exact K ].
exists pb, PBS, [(pd, pdn)], cap, len, str. split; [exact EBS|].
split; [eapply opt_pbuf_agree; [exact OPB | eapply agree_on_incl; [exact AGT | intros b Hb; right; exact Hb] | apply incl_refl]|].
split; [exact Hcap|]. split; [exact Hlen|]. split; [exact Hsl|]. right.
split; [exact Hl0|]. exists pd, pdn, junk, junk2. split; [reflexivity|]. split; [exact HPD|].
split; [exact HDR3|].
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ pd pdn HP ltac:(apply in_or_app; left; apply in_or_app; left; rewrite EBS; right; left; reflexivity)) as (Hpdn & _).
eapply rw_cells_agree; [exact HD | exact AGT | exists pd, pdn; split; [left; reflexivity | cbn; lia]].
Qed.
End PutX.

Lemma xleaf_len : forall (m : word -> option byte) BS p r,
jroot_rep A4H A4F r m BS p -> match r with JRdblx _ | JRstrx => True | _ => False end -> Z.of_nat (length BS) <= 4.
Proof.
intros m BS p r J XL. destruct r as [|s|tojs|]; try contradiction.
- destruct J as (_ & _ & pb & PBS & bits & -> & OPB & _).
destruct OPB as [[_ ->]|[_ (buf & bpos & size & content & -> & _)]]; cbn; lia.
- destruct J as (_ & pb & PBS & DBS & cap & len & str & -> & OPB & _ & _ & _ & CASES).
assert (LD : (length DBS <= 1)%nat) by (destruct CASES as [(_ & -> & _)|(_ & pd & pdn & _ & _ & -> & _)]; cbn; lia).
destruct OPB as [[_ ->]|[_ (buf & bpos & size & content & -> & _)]]; cbn [length]; rewrite length_app; cbn [length]; lia.
Qed.

Ltac releaseB ST := lazymatch type of ST with stk _ ?mq _ _ =>
match goal with S : rw_cells _ mq (bv_unsigned ?spv + -112) [_], F : rw_cells _ mq (bv_unsigned ?spv + -104) _ |- _ =>
release_frame S ST (bv_unsigned spv + -104); release_frame F ST (bv_unsigned spv) end end.
Theorem put_xleaf_A : forall HIx : heap_iface_A A4L, jo_put_xleaf_A_stmt HIx put_entry_A put_stk_A 2048 2.
Proof.
intros HIx. unfold jo_put_xleaf_A_stmt. intros until errv. intros (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA) J XL CB CD A0 K.
unfold put_stk_A in LOS. unfold put_entry_A.
unfold_consts. unfold A_SB, A_TP, A_ERRNO in *. word_range sp SPW.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP) as [HB0 HD0].
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL]. a4l.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU.
pose proof (xleaf_len m BS p r J XL) as LEN.

assert (XB : p <> 0 /\ exists n, In (p, n) BS /\ 48 <= n).
{ destruct r as [|s|tojs|]; try contradiction.
- destruct J as (Hx & _ & pb & PBS & bits & EBS & _). split; [exact Hx|]. exists 48. split; [rewrite EBS; left; reflexivity | lia].
- destruct J as (Hx & pb & PBS & DBS & cap & len & str & EBS & _ & Hcap & _). split; [exact Hx|]. exists (48 + cap). split; [rewrite EBS; left; reflexivity | lia]. }
destruct XB as (Hp & n & INp & N48).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p n HP ltac:(apply in_or_app; left; apply in_or_app; left; exact INp)) as (_ & Hpal & Hplo & Hphi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
reenterA asegs A4L HIx asegs_wx HP. subst a0 tp.
carve_frame 104%nat ST. carve_frame 8%nat ST.
do 14 bstep.
bstep. if_falsex.
bstep. bstep. bstep. bstep. bstep. bstep. bstep.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
assert (AG : agree_on asegs BS m m1).
{ eapply (agree_of_munch asegs); [exact MU | exact WM |].
intros a k Hin. pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin)) as (Hk & _ & _ & Hahi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hahi. cbn. lia. }
assert (J1 : jroot_rep A4H A4F r m1 BS p).
{ destruct r as [|s|tojs|]; try contradiction.
- destruct J as (Hx & Htojs & pb & PBS & bits & EBS & OPB & HDR). split; [exact Hx|]. split; [exact Htojs|].
exists pb, PBS, bits. split; [exact EBS|]. split.
+ eapply opt_pbuf_agree; [exact OPB | eapply agree_on_incl; [exact AG | intros b Hb; rewrite EBS; right; exact Hb] | apply incl_refl].
+ eapply rw_cells_agree; [exact HDR | exact AG | exists p, 48; split; [rewrite EBS; left; reflexivity | cbn; lia]].
- destruct J as (Hx & pb & PBS & DBS & cap & len & str & EBS & OPB & Hcap & Hlen & Hsl & CASES). split; [exact Hx|].
exists pb, PBS, DBS, cap, len, str. split; [exact EBS|]. split.
{ eapply opt_pbuf_agree; [exact OPB | eapply agree_on_incl; [exact AG | intros b Hb; rewrite EBS; right; apply in_or_app; right; exact Hb] | apply incl_refl]. }
split; [exact Hcap|]. split; [exact Hlen|]. split; [exact Hsl|].
destruct CASES as [(Hl0 & EDBS & Hfit & junkx & HDR) | (Hl0 & pd & pdn & junkx & junkx2 & EDBS & HPD & HDR & HD)].
+ left. split; [exact Hl0|]. split; [exact EDBS|]. split; [exact Hfit|]. exists junkx.
eapply rw_cells_agree; [exact HDR | exact AG | exists p, (48 + cap); split; [rewrite EBS; left; reflexivity | rewrite cells_size_app; cbn [cells_size csize jhdr_cells Nat.add length app]; rewrite ?length_app; cbn [length]; lia]].
+ right. split; [exact Hl0|]. exists pd, pdn, junkx, junkx2. split; [exact EDBS|]. split; [exact HPD|].
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ pd pdn HP ltac:(apply in_or_app; left; apply in_or_app; left; rewrite EBS, EDBS; right; left; reflexivity)) as (Hpdn & _).
split.
* eapply rw_cells_agree; [exact HDR | exact AG | exists p, (48 + cap); split; [rewrite EBS; left; reflexivity | rewrite cells_size_app; cbn [cells_size csize jhdr_cells Nat.add]; lia]].
* eapply rw_cells_agree; [exact HD | exact AG | exists pd, pdn; split; [rewrite EBS, EDBS; right; left; reflexivity | cbn; lia]]. }
assert (HPR1 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m1).
{ eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; rewrite <- app_assoc; apply in_or_app; right; exact Hb | clia |].
apply Forall_cons; [cbn [fst snd]; left; clia | apply Forall_nil]. }
evt_done5.
eapply (maybe_free_x_A HIx) with (BS := BS) (LB := LB) (x := p) (lo := lo) (r := r);
[ heap_nowA A4L HIx HP MU WM MI | exact J1 | exact XL | .. ]; a4l_goal; rewrite ?unsigned_lit by lia; try first [reflexivity | lia].
all: try (replace (bv_unsigned sp + -112) with (bv_unsigned sp - 112) by lia; rewrite Zminus_mod, SPA; reflexivity).
all: try exact ERR. all: try assumption.
intros ms2 md2 A2 (m2 & rr & B2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & BD2 & OUT2).
destruct RS2 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F2 & fc2 & -> & FS2 & FRM2).
a4l. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in ST2 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in HPR2 by lia.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia].
match goal with S : rw_cells _ _ (bv_unsigned _ + -112) [_] |- _ => apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in S; [| left; cbn; lia] end. a4l.
assert (HPR12 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m2).
{ eapply heap_pres_trans; [exact HPR1 | eapply heap_pres_weaken; [exact HPR2 | lia | intros b Hb; exact Hb]]. }
clear MU WM MI J J1.
destruct OUT2 as [(Er & Hrc2 & _ & _ & _) | [(Er & _ & BB2 & HP2) | (Er & _ & ZM & _ & _)]]; [lia | subst rr | exfalso; cbn in ZM; exact ZM].
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
pose proof (wmono_refl asegs m2) as WM. pose proof (munch_refl [] m2) as MU.
reenterA asegs A4L HIx asegs_wx HP2. bstep. bstep. if_truex.
do 14 bstep. releaseB ST2. bstep.
evt_done5. eapply (K _ md2 m2 1 A2 B2).
- split; [apply ret_statew_intro; [exact FS2 | exact FRM2] |]. split; [exact VM2|]. split; [exact ST2|].
split; [exact HPR12|]. exists errv. exact ERR2.
- split; lia.
- reflexivity.
- exact ERR2.
- exact HP2.
Qed.
End RC__1.
End Mqe.

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qtgi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qtgi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkMG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkMG.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4v2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4v2.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Definition obj_capA (BS : list blk) : Z := snd (nth 2 BS (0, 0)) / 40.

Definition K_arr : Z := 1280.
Definition RA : Z := 1024.
Definition K_open_arr : Z := 8960.
Definition K_obj : Z := 3904.
Definition K_open_obj : Z := 15488.
Definition K_pb : Z := 48.
Definition K_free : Z := 512.
Definition K_tot : Z := 6656.
Definition K0 : Z := 333992.
Definition K_exit : Z := 20480.

Definition PhiA (cap len : Z) : Z := 768 * len - 256 * cap + 8192.
Definition PhiO (cap cnt : Z) : Z := 3904 * cnt - 1280 * cap + 20480.

Definition PhiPB (len cap : Z) : Z := 48 * (2 * len + 50) + 512 - 48 * cap.
Definition pb_inv (cap co : Z) : Prop := 32 <= cap /\ (cap = 32 \/ cap <= 2 * co + 18).

Definition phi_level (l : tlevel) : Z :=
match tl_cs l with
| Some (Sarr kids) => PhiA (arr_capA (tl_cbs l)) (Z.of_nat (length kids)) + RA
| Some (Sobj kids) => PhiO (obj_capA (tl_cbs l)) (Z.of_nat (length kids))
| _ => 0
end.

Fixpoint ledger_levels (levels : list tlevel) (n : nat) : Z :=
match n, levels with
| O, _ => 0
| S n', l :: rest => phi_level l + ledger_levels rest n'
| S _, [] => 0
end.

Definition pb_capA (pbs : list blk) : Z := snd (nth 1 pbs (0, 0)).

Definition pe_needB (len rem : Z) (levels : list tlevel) (depth : nat) (pbs : list blk) (nblk : Z) : Z :=
K_tot * rem + ledger_levels levels (S depth) + PhiPB len (pb_capA pbs) + K_free * nblk + K_exit.

Definition pe_needD (rem : Z) : Z := rem.

Definition arr_inv (cap len : Z) : Prop := 32 <= cap /\ 0 <= len <= cap /\ (cap = 32 \/ cap <= 2 * len).

Lemma potential_step_arr_add : forall cap len cap',
arr_inv cap len -> arr_grownA cap len cap' ->
PhiA cap len + RA + K_arr >= arr_add_costA cap len + (PhiA cap' (len + 1) + RA) /\ arr_inv cap' (len + 1).
Proof.
intros cap len cap' (H32 & Hl & Hi) G. unfold PhiA, RA, K_arr, arr_add_costA, arr_grownA, arr_inv in *.
destruct G as [[-> Hlt] | [-> Hge]].
- replace (len + 1 <? cap) with true by (symmetry; apply Z.ltb_lt; lia). lia.
- replace (len + 1 <? cap) with false by (symmetry; apply Z.ltb_ge; lia). lia.
Qed.

Lemma potential_step_arr_close : forall cap len,
arr_inv cap len -> PhiA cap len + RA >= arr_shrink_costA cap len.
Proof.
intros cap len (H32 & Hl & Hcap). unfold PhiA, RA, arr_shrink_costA.
destruct (len =? cap) eqn:E; [lia|]. apply Z.eqb_neq in E.
destruct (Z.max_spec len 1) as [[_ ->] | [_ ->]]; lia.
Qed.

Lemma arr_inv_new : arr_inv 32 0.
Proof. unfold arr_inv. lia. Qed.

Lemma pb_inv_mono : forall cap co co', pb_inv cap co -> co <= co' -> pb_inv cap co'.
Proof. intros cap co co' [A B] H. split; lia. Qed.

