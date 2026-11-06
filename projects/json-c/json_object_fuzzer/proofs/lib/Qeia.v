(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QRjH QHnV QCcH QfLs Q0Ek Qtgi QjDH QJjn QRUw QkMG QG8z QLbz Qdyh Q8tj Q7UD Qhd4 Qwm6 QsKa Qiiq Q1Y6 Qoif Q4v2 Q1Ey QrQv QEUF Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 QJjn QRUw.Mq0 QkMG. Import QG8z QLbz Qdyh.Mq0. Import Q8tj.
Import Q7UD Qhd4 Qwm6.Mq0 QsKa.Mq4 Qiiq.Mq0 Q1Y6.Mq0 Qoif.Mq0 Q4v2.Mq0 Q1Ey QrQv.Mq2 QEUF.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma lf_thr_lower : forall S, In S lf_sizes -> 2560 * S <= 3904 * lf_thr S + 3904.
Proof.
intros S H. assert (C : forallb (fun S => 2560 * S <=? 3904 * lf_thr S + 3904) lf_sizes = true) by (vm_compute; reflexivity).
rewrite forallb_forall in C. specialize (C S H). apply Z.leb_le in C. exact C.
Qed.
Lemma lf_thr_nonneg : forall S, In S lf_sizes -> 0 <= lf_thr S.
Proof.
intros S H. assert (C : forallb (fun S => 0 <=? lf_thr S) lf_sizes = true) by (vm_compute; reflexivity).
rewrite forallb_forall in C. specialize (C S H). apply Z.leb_le in C. exact C.
Qed.
Lemma lf_sizes_double : forall S, In S lf_sizes -> S <= 2^29 -> In (2 * S) lf_sizes.
Proof.
intros S H Hle. assert (C : forallb (fun S => if S <=? 2^29 then existsb (Z.eqb (2 * S)) lf_sizes else true) lf_sizes = true) by (vm_compute; reflexivity).
rewrite forallb_forall in C. specialize (C S H). rewrite (proj2 (Z.leb_le S (2^29)) Hle) in C.
apply existsb_exists in C as (x & Hx & E). apply Z.eqb_eq in E. rewrite E. exact Hx.
Qed.

Lemma lh_ns_small : forall S, S <= 2^29 -> lh_ns S = 2 * S.
Proof. intros S H. unfold lh_ns. rewrite (proj2 (Z.leb_le S (2^29)) H). reflexivity. Qed.

Lemma BOK_obj_add : forall pf pa ts B n l kids klen,
BOK pf pa ts B (S (Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192) + n)) -> 0 <= pa_bslack pa ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_cs l = Some (Sobj kids) -> lvl_closed l = false ->
0 <= klen <= Z.max 0 (pf_len pf) -> obj_capA (tl_cbs l) <= 2^29 ->
oadd_costB klen (obj_capA (tl_cbs l)) (Z.of_nat (length kids)) <= bB B /\ 512 * Z.of_nat (length (tl_cbs l)) <= bB B /\
(forall B', bB B - oadd_costB klen (obj_capA (tl_cbs l)) (Z.of_nat (length kids)) <= bB B' -> bD B <= bD B' ->
K_free * Z.of_nat (length (tstate_blocks ts)) + K_exit + pa_bslack pa <= bB B' /\ pa_dslack pa <= bD B') /\
(forall B' cbs2 kids2 st' ss' obj' objs', (ss' <> ST_finish \/ zin st' [ST_array_add; ST_ovadd] = true) ->
( (Z.of_nat (length kids2) = Z.of_nat (length kids) + 1
/\ bB B - oadd_costB klen (obj_capA (tl_cbs l)) (Z.of_nat (length kids)) <= bB B'
/\ Z.of_nat (length cbs2) = Z.of_nat (length (tl_cbs l)) + Z.of_nat (length (t_objbs ts)) + 1
/\ obj_grownA (obj_capA (tl_cbs l)) (Z.of_nat (length kids)) (obj_capA cbs2))
\/ (Z.of_nat (length kids2) = Z.of_nat (length kids)
/\ bB B - 512 * (Z.of_nat (length (tl_cbs l)) + Z.of_nat (length (t_objbs ts)) - Z.of_nat (length cbs2)) <= bB B'
/\ Z.of_nat (length cbs2) <= Z.of_nat (length (tl_cbs l)) + Z.of_nat (length (t_objbs ts))
/\ obj_capA cbs2 = obj_capA (tl_cbs l)) ) ->
bD B <= bD B' ->
BOK pf pa (ts_lvl_obj ts (TL st' ss' (tl_cur l) (Some (Sobj kids2)) cbs2 (tl_name l) (tl_nbs l)) obj' objs' []) B' n).
Proof.
intros pf pa ts B n l kids klen H BSL Hl Hcs Hop Hk Hcap.
pose proof H as (H1 & H2 & H3 & H4 & H5).
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
pose proof (H5 (t_depth ts) l (le_n _) Hl) as (P0 & _ & OI & NI). specialize (OI Hop kids Hcs).
set (cap := obj_capA (tl_cbs l)) in *. set (cnt := Z.of_nat (length kids)) in *.
assert (Ephi : phi_open l = PhiO cap cnt) by (unfold phi_open; rewrite Hop; unfold phi_level; rewrite Hcs; reflexivity).
pose proof (ledger_open_ge (t_levels ts) (S (t_depth ts)) (t_depth ts) l Hl (Nat.lt_succ_diag_r _)
ltac:(intros j lj Hj Hnj; exact (proj1 (H5 j lj ltac:(lia) Hnj)))) as GE.
pose proof (K_ev_pos pf) as KE. pose proof (Z.mul_nonneg_nonneg (K_ev pf) (Z.of_nat n) ltac:(lia) ltac:(lia)) as KN.
pose proof (Zle_0_nat (length (tstate_blocks ts))) as Hnb.
pose proof (lf_thr_lower cap OI) as LT. pose proof (lf_thr_nonneg cap OI) as LT0. pose proof (lf_size_range cap OI) as CR.
assert (Hcnt : 0 <= cnt) by (unfold cnt; lia).
unfold bneed in H1. set (U := 16 * Z.max 0 (pf_len pf) + 8192) in *.
assert (KU : K_ev pf * Z.of_nat (S (Z.to_nat U + n)) = K_ev pf * Z.of_nat n + (U + 1)) by (unfold K_ev, U; lia). rewrite KU in H1. clear KU.
assert (KEV : U = 16 * Z.max 0 (pf_len pf) + 8192) by reflexivity.

assert (COSTB : oadd_costB klen cap cnt <= U + PhiO cap cnt - 4944 /\ (lf_thr cap <= cnt -> oadd_costB klen cap cnt = 16 * (klen + 1) + 512 + (1280 * cap + 2944))
/\ (cnt < lf_thr cap -> oadd_costB klen cap cnt = 16 * (klen + 1) + 512)).
{ unfold oadd_costB, strdup_costB, ins_costB, resize_costB. rewrite (lh_ns_small cap Hcap). rewrite Ephi in P0. unfold PhiO in *.
destruct (lf_thr cap <=? cnt) eqn:E; [apply Z.leb_le in E | apply Z.leb_gt in E]; (split; [lia | split; intros; lia]). }
destruct COSTB as (COSTB & CRES & CNOR).
assert (Hcbs : Z.of_nat (length (tl_cbs l)) <= Z.of_nat (length (tstate_blocks ts))).
{ pose proof (tstate_blocks_lvl_length ts l (TL 0 0 0 None [] 0 []) Hl) as E. unfold lvl_blocks in E at 2. cbn [tl_cbs tl_nbs app length] in E.
pose proof (Zle_0_nat (length (tstate_blocks (ts_lvl ts (TL 0 0 0 None [] 0 []))))). unfold lvl_blocks in E. rewrite length_app in E. lia. }
unfold K_free, K_exit in *. rewrite Ephi in GE.
split; [lia|]. split; [lia|]. split.
{ intros B' HB HD. split; lia. }
intros B' cbs2 kids2 st' ss' obj' objs' Hss' CASES HD.
set (l' := TL st' ss' (tl_cur l) (Some (Sobj kids2)) cbs2 (tl_name l) (tl_nbs l)).
assert (Hphi' : phi_open l' = PhiO (obj_capA cbs2) (Z.of_nat (length kids2))).
{ unfold phi_open. replace (lvl_closed l') with false by (symmetry; destruct Hss' as [Hss' | Hss']; [apply lvl_closed_open_ss | apply lvl_closed_open_st]; exact Hss').
unfold phi_level, l'. cbn [tl_cs tl_cbs]. reflexivity. }
pose proof (tstate_blocks_lvl_obj_length ts l l' obj' objs' [] Hl) as Hblk. cbn [length] in Hblk.
assert (Hlb : Z.of_nat (length (lvl_blocks l')) = Z.of_nat (length cbs2) + Z.of_nat (length (tl_nbs l))) by (unfold lvl_blocks, l'; cbn [tl_cbs tl_nbs]; rewrite length_app; lia).
assert (Hlb0 : Z.of_nat (length (lvl_blocks l)) = Z.of_nat (length (tl_cbs l)) + Z.of_nat (length (tl_nbs l))) by (unfold lvl_blocks; rewrite length_app; lia).
assert (GOAL : (K_ev pf * Z.of_nat n + (ledger_open (t_levels ts) (S (t_depth ts)) - PhiO cap cnt + PhiO (obj_capA cbs2) (Z.of_nat (length kids2)))
+ PhiPB (pf_len pf) (pb_capA (t_pbs ts)) + 512 * (Z.of_nat (length (tstate_blocks ts)) - Z.of_nat (length (lvl_blocks l)) - Z.of_nat (length (t_objbs ts)) + Z.of_nat (length (lvl_blocks l')) + 0)
+ 20480 + pa_bslack pa <= bB B')
/\ 0 <= PhiO (obj_capA cbs2) (Z.of_nat (length kids2)) /\ In (obj_capA cbs2) lf_sizes).
{ destruct CASES as [(Ek & HB & Elen & GR) | (Ek & HB & Elen & Ecap)].
- rewrite Ek. destruct GR as [(-> & Hlt) | (-> & Hge)].
+ fold cap. rewrite (CNOR Hlt) in HB. rewrite Ephi in P0. unfold PhiO in *. split; [lia | split; [lia | exact OI]].
+ fold cap. rewrite (CRES Hge) in HB. rewrite (lh_ns_small cap Hcap). rewrite Ephi in P0. unfold PhiO in *. split; [lia | split; [lia | apply lf_sizes_double; [exact OI | exact Hcap]]].
- rewrite Ek, Ecap. fold cap. rewrite Ephi in P0. split; [lia | split; [exact P0 | exact OI]]. }
destruct GOAL as (G1 & G2 & G3).
unfold BOK, bneed. rewrite Hblk. unfold ts_lvl_obj; cbn [t_levels t_depth t_pbs t_co].
rewrite (ledger_open_lupd (t_levels ts) (S (t_depth ts)) (t_depth ts) l l' Hl (Nat.lt_succ_diag_r _)), Hphi', Ephi.
split; [unfold K_free, K_exit; lia|]. split; [lia|]. split; [exact H3|]. split; [exact H4|].
intros i li Hi Hn.
destruct (PeanoNat.Nat.eq_dec i (t_depth ts)) as [-> | NE].
- rewrite nth_error_lupd_eq in Hn by exact Hd. injection Hn as <-. split; [rewrite Hphi'; exact G2|].
split; [intros _ kids3 Hk3; unfold l' in Hk3; cbn [tl_cs] in Hk3; discriminate Hk3|].
split; [intros _ kids3 Hk3; unfold l'; cbn [tl_cbs]; exact G3 | exact NI].
- rewrite nth_error_lupd_neq in Hn by congruence. exact (H5 i li Hi Hn).
Qed.

Lemma BOK_name_free : forall pf pa ts B B' n l b st' ss' nm',
BOK pf pa ts B n -> nth_error (t_levels ts) (t_depth ts) = Some l -> tl_nbs l = [b] ->
(lvl_closed l = true -> lvl_closed (TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) nm' []) = true) ->
bB B - 512 <= bB B' -> bD B <= bD B' ->
BOK pf pa (ts_lvl ts (TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) nm' [])) B' n.
Proof.
intros pf pa ts B B' n l b st' ss' nm' (H1 & H2 & H3 & H4 & H5) Hl Hnbs Hcl HB HD.
set (l' := TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) nm' []) in *.
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
pose proof (H5 (t_depth ts) l (le_n _) Hl) as (P0 & AI & OI & NI).
assert (Hphi : 0 <= phi_open l' <= phi_open l).
{ unfold phi_open in *. change (phi_level l') with (phi_level l).
destruct (lvl_closed l') eqn:E1; destruct (lvl_closed l) eqn:E2; try lia; specialize (Hcl eq_refl); discriminate Hcl. }
pose proof (tstate_blocks_lvl_length ts l l' Hl) as Hblk.
assert (Hlb : Z.of_nat (length (lvl_blocks l')) = Z.of_nat (length (lvl_blocks l)) - 1) by (unfold lvl_blocks, l'; cbn [tl_cbs tl_nbs]; rewrite Hnbs, !length_app; cbn [length]; lia).
split.
{ unfold bneed in *. rewrite Hblk. unfold ts_lvl; cbn [t_levels t_depth t_pbs]. rewrite (ledger_open_lupd (t_levels ts) (S (t_depth ts)) (t_depth ts) l l' Hl (Nat.lt_succ_diag_r _)). unfold K_free in *. lia. }
split; [lia|]. split; [exact H3|]. split; [exact H4|].
unfold ts_lvl; cbn [t_levels t_depth]. intros i li Hi Hn.
destruct (PeanoNat.Nat.eq_dec i (t_depth ts)) as [-> | NE].
- rewrite nth_error_lupd_eq in Hn by exact Hd. injection Hn as <-. split; [lia|].
assert (Hopl : lvl_closed l' = false -> lvl_closed l = false) by (intros Hop; destruct (lvl_closed l) eqn:E; [| reflexivity]; rewrite (Hcl eq_refl) in Hop; discriminate Hop).
split; [intros Hop kids Hcs; apply AI; [exact (Hopl Hop) | exact Hcs]|]. split; [intros Hop kids Hcs; apply (OI (Hopl Hop) kids); exact Hcs | apply Forall_nil].
- rewrite nth_error_lupd_neq in Hn by congruence. exact (H5 i li Hi Hn).
Qed.

Lemma BOK_blk_512 : forall pf pa ts B n b, BOK pf pa ts B n -> 0 <= pa_bslack pa -> In b (tstate_blocks ts) -> 512 <= bB B.
Proof.
intros pf pa ts B n b H BSL Hin. pose proof (BOK_ledger_nonneg _ _ _ _ _ H) as L0. destruct H as (H1 & _ & H3 & _).
assert (Hlen : 1 <= Z.of_nat (length (tstate_blocks ts))) by (destruct (tstate_blocks ts); [destruct Hin | cbn [length]; lia]).
pose proof (K_ev_pos pf) as KE. pose proof (Z.mul_nonneg_nonneg (K_ev pf) (Z.of_nat n) ltac:(lia) ltac:(lia)) as KN.
unfold bneed, K_free, K_exit in H1. lia.
Qed.

Lemma BOK_obj_irrel : forall pf pa ts l o os o' os' B n, BOK pf pa (ts_lvl_obj ts l o os []) B n -> BOK pf pa (ts_lvl_obj ts l o' os' []) B n.
Proof. intros pf pa ts l o os o' os' B n H. exact H. Qed.

Lemma BOK_name_bound : forall pf pa ts B n l nm nn, BOK pf pa ts B n -> nth_error (t_levels ts) (t_depth ts) = Some l -> tl_nbs l = [(nm, nn)] -> nn <= Z.max 0 (pf_len pf) + 1.
Proof.
intros pf pa ts B n l nm nn (_ & _ & _ & _ & H5) Hl Hnbs. pose proof (H5 (t_depth ts) l (le_n _) Hl) as (_ & _ & _ & NI).
rewrite Hnbs in NI. apply Forall_cons_iff in NI as [NI _]. exact NI.
Qed.
End RC__1.
End Mq0.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1 Qsw7 QPZI QIsM QlKV QugP Ql4f QW22.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QRUw.Mq2. Import QPZI.Mq4. Import QkMG. Import QG8z QIsM.Mq2.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq4 Qiiq.Mq0 QsKa.Mq6 Q4v2.Mq0 QugP.Mq1 QlKV.Mq5 Q1Ey Ql4f.Mq1 QsKa.Mq8 QrQv.Mq2 QEUF QW22.Mq3.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition pe_frameAX (m : word -> option byte) (pf : pe_fix) (pa : pe_fixA) (nb : word) (pj : pe_junkA) (sv : pe_saved) (ffc shc : list cell) : Prop :=
rw_cells asegs m (pf_spf pf) (pe_slotsA pf pa nb pj) /\
rw_cells asegs m (pf_spf pf + 312) [CB (Z.to_nat (pa_sp0 pa - 104 - (pf_spf pf + 312))) (pj_gap pj)] /\
rw_cells asegs m (pa_sp0 pa - 104) (pe_savedA_cells sv) /\
rw_cells asegs m (pa_F pa) ffc /\
rw_cells asegs m (shA (pa_F pa)) shc.

Lemma pe_frameAX_of_A : forall m pf pa cb nb pj sv, pe_frameA asegs m pf pa cb nb pj sv -> pe_frameAX m pf pa nb pj sv (ff_cellsA cb pj) (ffsh_cells FSH0).
Proof. intros m pf pa cb nb pj sv H. exact H. Qed.
Lemma pe_frameA_of_X : forall m pf pa cb nb pj sv, pe_frameAX m pf pa nb pj sv (ff_cellsA cb pj) (ffsh_cells FSH0) -> pe_frameA asegs m pf pa cb nb pj sv.
Proof. intros m pf pa cb nb pj sv H. exact H. Qed.

Lemma scoped_unpoisoned_w : forall (m : word -> option byte) (F n : Z) (k : nat) (w : list byte),
F mod 256 = 0 -> 0 <= F ->
bytes_at asegs m (F / 8 + A_SB + 8 * (Z.of_nat k / 8)) w -> length w = 8%nat ->
nth_error w (Z.to_nat (Z.of_nat k mod 8)) = Some (Z_to_bv 8 n) -> 1 <= n <= 7 ->
unpoisoned asegs m A_SB (F + 8 * Z.of_nat k) n.
Proof.
intros m F n k w GF GF0 WB Lw Hn Rn.
assert (Es : (F + 8 * Z.of_nat k) / 8 = F / 8 + Z.of_nat k) by (clear - GF; Z.div_mod_to_equations; lia).
assert (Ee : (F + 8 * Z.of_nat k + n - 1) / 8 = F / 8 + Z.of_nat k) by (clear - GF Rn; Z.div_mod_to_equations; lia).
assert (Em : (F + 8 * Z.of_nat k + n - 1) mod 8 = n - 1) by (clear - GF Rn; Z.div_mod_to_equations; lia).
unfold unpoisoned. split; [lia|]. split; [intros g Hg; rewrite Es, Ee in Hg; lia|]. split.
- exists n. split; [| right; split; [lia | rewrite Em; lia]].
rewrite Ee. apply nth_error_split in Hn as (l1 & l2 & Ew & Ll1). rewrite Ew in WB.
apply (proj1 (bytes_at_app asegs _ _ _ _)) in WB as [_ WB]. change (Z_to_bv 8 n :: l2) with ([Z_to_bv 8 n] ++ l2) in WB.
apply (proj1 (bytes_at_app asegs _ _ _ _)) in WB as [WB _]. rewrite Ll1 in WB.
replace (F / 8 + Z.of_nat k + A_SB) with (F / 8 + A_SB + 8 * (Z.of_nat k / 8) + Z.of_nat (Z.to_nat (Z.of_nat k mod 8))); [exact WB|].
rewrite Z2Nat.id by (apply Z.mod_pos_bound; lia). pose proof (Z.div_mod (Z.of_nat k) 8 ltac:(lia)). lia.
- intros w' Hw'. rewrite Es, Ee in Hw'. exists w. split; [exact Lw|].
replace (w' * 8) with (F / 8 + A_SB + 8 * (Z.of_nat k / 8)); [exact WB|].
unfold A_SB in *. clear - GF Hw'. Z.div_mod_to_equations. lia.
Qed.

Section WithIface.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.

Lemma pe_frameAX_pres : forall pf pa (L : list blk) SP me m nb pj sv ffc shc,
heap_pres A4H L SP me m -> SP <= pf_spf pf -> pe_geomA pf pa ->
In (pa_F pa, 248) L -> In (shA (pa_F pa), 32) L ->
Z.of_nat (cells_size ffc) <= 248 -> Z.of_nat (cells_size shc) <= 32 ->
pe_frameAX me pf pa nb pj sv ffc shc -> pe_frameAX m pf pa nb pj sv ffc shc.
Proof.
intros pf pa L SP me m nb pj sv ffc shc HPR HSP GEO InF InS SZF SZS (SL & GP & SV & FF & FSH).
pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
split; [| split; [| split; [| split]]].
- eapply (heap_pres_rw_cells A4H); [exact HPR | exact SL | left; lia].
- eapply (heap_pres_rw_cells A4H); [exact HPR | exact GP | left; lia].
- eapply (heap_pres_rw_cells A4H); [exact HPR | exact SV | left; lia].
- eapply (heap_pres_rw_cells A4H); [exact HPR | exact FF | right; right]. exists (pa_F pa, 248). split; [exact InF | cbn; lia].
- eapply (heap_pres_rw_cells A4H); [exact HPR | exact FSH | right; right]. exists (shA (pa_F pa), 32). split; [exact InS | cbn; lia].
Qed.

Lemma pe_frameAX_write : forall pf pa q LB0 LM FRS B ts A m mc md lo nb pj sv ffc shc ffc' shc',
PE_STATIC_A HIx pf pa lo -> HEAPA A4L HIx A (pe_blocksA pf q LB0 ts) LM ((pa_F pa, 2) :: FRS) B m md ->
pe_frameAX m pf pa nb pj sv ffc shc ->
munch [(pf_tk pf, pf_tk pf + 72); (pa_F pa, pa_F pa + 248); (shA (pa_F pa), shA (pa_F pa) + 32)] m mc -> wmono asegs m mc ->
rw_cells asegs mc (pa_F pa) ffc' -> rw_cells asegs mc (shA (pa_F pa)) shc' ->
pe_frameAX mc pf pa nb pj sv ffc' shc'.
Proof.
intros pf pa q LB0 LM FRS B ts A m mc md lo nb pj sv ffc shc ffc' shc' STC HP (SLOTS & GAP & SAVED & _ & _) MU WM FFc FSHc.
pose proof STC as (LO & LOS & GEO & HT & SP0 & _). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof alloc_ceiling_range as ACR.
assert (INtk : In (pf_tk pf, 72) (pe_blocksA pf q LB0 ts ++ LM)) by (apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP INtk) as (_ & _ & Htlo & Hthi & _).
pose proof (pe_slotsA_size pf pa nb pj) as SZ.
assert (SHhi : shA (pa_F pa) + 32 <= alloc_ceiling) by (unfold shA, A_SB; clear - GFc ACR; Z.div_mod_to_equations; lia).
split; [| split; [| split; [| split; [exact FFc | exact FSHc]]]].
- eapply rw_cells_transport; [exact SLOTS | exact MU | exact WM |]. rewrite SZ. cbn [disjoint_from fst snd]. lia.
- eapply rw_cells_transport; [exact GAP | exact MU | exact WM |]. cbn [cells_size csize disjoint_from fst snd]. lia.
- eapply rw_cells_transport; [exact SAVED | exact MU | exact WM |]. cbn [pe_savedA_cells cells_size csize disjoint_from fst snd Nat.add]. lia.
Qed.

Definition PE_INV_AX (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (errv : word) (FRX : Prop) : Prop :=
(length (t_levels ts) = Z.to_nat (pf_mxd pf) /\ (t_depth ts < Z.to_nat (pf_mxd pf))%nat /\
0 <= t_co ts <= pf_len pf /\ ts_choff (t_x ts) = Z_to_bv 64 (t_co ts) /\
rw_cells asegs m (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) (t_pb ts) (Z.of_nat (t_depth ts)) q (t_x ts)) /\
pbuf asegs m (t_pbs ts) (t_pb ts) /\ t_pb ts <> 0 /\
tstack asegs m q (t_levels ts) /\
FRX) /\
PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts errv.

Lemma PE_INV_AX_of_A : forall pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv,
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PE_INV_AX pf pa q LB0 LM FRS payload me lo m md A B ts errv (pe_frameA asegs m pf pa cb nb pj sv).
Proof. intros until errv. intros H. exact H. Qed.

Lemma PE_INV_AX_tokw : forall pf pa q LB0 LM FRS payload me lo m mc md A B ts errv W co' x' (FRX FRX' : Prop),
PE_STATIC_A HIx pf pa lo ->
PE_INV_AX pf pa q LB0 LM FRS payload me lo m md A B ts errv FRX ->
munch W m mc -> wmono asegs m mc -> mem_inv asegs mc -> Forall (pe_wtfA pf pa) W ->
rw_cells asegs mc (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) (t_pb ts) (Z.of_nat (t_depth ts)) q x') ->
FRX' ->
0 <= co' <= pf_len pf -> ts_choff x' = Z_to_bv 64 co' ->
PE_INV_AX pf pa q LB0 LM FRS payload me lo mc md A B (ts_set_x ts co' x') errv FRX'
/\ (forall b, PBOKat m ts b -> PBOKat mc (ts_set_x ts co' x') b).
Proof.
intros pf pa q LB0 LM FRS payload me lo m mc md A B ts errv W co' x' FRX FRX' STC [CORE REST] MU WM MI HW TOKc FRc Hco Hch.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
split.
- split.
+ unfold ts_set_x; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [exact LEN32|]. split; [exact D32|]. split; [exact Hco|]. split; [exact Hch|].
split; [exact TOKc|]. split; [| split; [exact Hpb | split; [| exact FRc]]].
* eapply (pbuf_wtfA HIx) with (ts := ts); [exact STC | exact (proj1 REST) | exact PB | exact MU | exact WM | exact HW].
* eapply (tstack_wtfA HIx) with (ts := ts); [exact STC | exact (proj1 REST) | exact TSK | exact LEN32 | exact MU | exact WM | exact HW].
+ apply PE_REST_A_set_x.
eapply (PE_REST_A_private_write HIx GA GA_outside) with (ts := ts); [exact STC | exact REST | exact MU | exact WM | exact MI | apply pe_wtfA_private; exact HW].
- intros b PBK. eapply PBOKat_same with (ts := ts); [reflexivity | reflexivity |].
eapply PBOKat_agree; [exact PBK | | apply incl_refl].
eapply (agree_wtqA HIx); [exact STC | exact (proj1 REST) | exact MU | exact WM | apply pe_wtfA_wtqA; exact HW |].
intros a n Hin. assert (HinL : In (a, n) (pe_blocksA pf q LB0 ts ++ LM)) by (unfold pe_blocksA, tstate_blocks; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hin).
split; [exact HinL|].
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ (proj1 REST)) as ND. unfold pe_blocksA in ND. rewrite <- app_assoc in ND. split.
+ intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | left; reflexivity].
+ intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | right; left; reflexivity].
Qed.

Hypothesis MAPP : memappend_A_stmt2 HIx.

Lemma pe_memappend_gX :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (xb xn bnd : Z) (src : list byte) (ffc shc : list cell)
(ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_AX pf pa q LB0 LM FRS payload me lo m md A B ts errv (pe_frameAX m pf pa nb pj sv ffc shc) ->
Z.of_nat (cells_size ffc) <= 248 -> Z.of_nat (cells_size shc) <= 32 ->
PBOKat m ts bnd -> bnd + xn <= t_co ts + 1 -> 0 <= xn < 2^31 ->
forall kB : nat, BOK pf pa ts B kB -> bv_unsigned ra mod 2 = 0 ->
bytes_at asegs m xb src -> Z.of_nat (length src) = xn -> 0 <= xb ->
src_locA ((t_objbs ts ++ concat (map lvl_blocks (t_levels ts))) ++ (pf_tk pf, 72) :: (q, 32 * pf_mxd pf) :: LB0) ((pa_F pa, 2) :: FRS) xb xn ->
(0 < xn -> unpoisoned asegs m A_SB xb xn) ->
(forall m2 md2 A2 B2 pbs2 errv2 r (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word) F2 fc2,
PE_INV_AX pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 (ts_pbs ts pbs2) errv2 (pe_frameAX m2 pf pa nb pj sv ffc shc) ->
(r = xn /\ PBOKat m2 (ts_pbs ts pbs2) (bnd + xn) /\ BOK pf pa (ts_pbs ts pbs2) B2 kB) \/ (r = 2^64 - 1 /\ pbs2 = t_pbs ts) ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 s0 s1 (Z_to_bv 64 r) w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F2 (ret_pc ra) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 (t_pb ts)) (Z_to_bv 64 xb) (Z_to_bv 64 xn) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9a0ac) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC BSL INV SZF SZS PBK Hbn Hn kB BK RA SRC SRCL Hb0 SLOC UNP K.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof INV as [CORE REST1].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK1 & FR1).
destruct PBK as (buf & bpos & cap & pre & post & Epbs & Lpre & CORE1 & Hbp).
pose proof (proj1 REST1) as HP1. unfold pe_blocksA, tstate_blocks in HP1. rewrite Epbs in HP1. cbn [app] in HP1.
pose proof REST1 as (_ & _ & _ & ST1 & ERR1 & _ & _ & _ & _ & _ & _ & BUD1).
assert (Hbp0 : 0 <= bpos) by (destruct CORE1 as (C1 & _); lia).
pose proof (BOK_memappend pf pa ts B kB (t_pb ts) buf cap bpos xn BK Epbs BSL Hbp0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as BUDM.
assert (SPF1 : lo <= pf_spf pf - 112 - 4096 /\ pf_spf pf mod 16 = 0 /\ pf_spf pf <= hiA_top A4L HIx /\ 0 <= pf_spf pf < 2^62).
{ clear - LOS HT Gle Gspf SP0. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; lia. }
destruct SPF1 as (SPF1 & SPF2 & SPF3 & SPF4).
set (LBc := (t_objbs ts ++ concat (map lvl_blocks (t_levels ts))) ++ (pf_tk pf, 72) :: (q, 32 * pf_mxd pf) :: LB0) in *.
eapply MAPP with (lo := lo) (b := xb) (src := src) (n := xn) (pb := t_pb ts) (buf := buf) (bpos := bpos) (cap := cap);
[ exact HP1 | exact CORE1 | exact Hn | exact SRC | exact SRCL | exact Hb0 | exact SLOC | exact UNP
| rewrite unsigned_lit by lia; exact ST1 | exact LO | rewrite unsigned_lit by lia; exact SPF1
| rewrite unsigned_lit by lia; exact SPF2
| rewrite unsigned_lit by lia; exact SPF3
| exact ERR1 | reflexivity | exact RA | reflexivity | reflexivity | reflexivity
| exact (proj1 BUDM) | ].
intros ms2 md2 A2 (m2 & r & errv2 & buf' & cap' & B2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & HB2 & HD2 & HP2 & OUT2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp hla_base A4L A4H] in *. rewrite ?(unsigned_lit (pf_spf pf)) in ST2 by lia. rewrite ?(unsigned_lit (pf_spf pf)) in HPR2 by lia.
set (pbs2 := [(t_pb ts, 16); (buf', cap')]).
assert (INq2 : In (q, 32 * pf_mxd pf) LBc) by (apply in_or_app; right; right; left; reflexivity).
assert (INtk2 : In (pf_tk pf, 72) LBc) by (apply in_or_app; right; left; reflexivity).
assert (FR2 : pe_frameAX m2 pf pa nb pj sv ffc shc).
{ eapply pe_frameAX_pres; [exact HPR2 | lia | exact GEO | | | exact SZF | exact SZS | exact FR1].
- apply in_or_app; right. apply in_or_app; right. change 248 with (fr_size 2 - 8). apply fr_ivs_frame. left; reflexivity.
- apply in_or_app; right. apply in_or_app; right. rewrite <- fr_shadow_len_2. change (shA (pa_F pa)) with (shad A4L (pa_F pa)). apply fr_ivs_shadow. left; reflexivity. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in TOK; [| eapply client_range_block; [apply in_or_app; left; exact INtk2 | lia | unfold tok_cells_g; cbn; lia]]. cbn [hl_segs hla_base A4L A4H] in TOK.
apply (tstack_pres_g A4H _ _ _ _ _ _ HPR2 (in_or_app _ _ _ (or_introl INq2))) in TSK1; [| exact LEN32]. cbn [hl_segs hla_base A4L A4H] in TSK1.
assert (BUD2 : PE_BUD pf pa (ts_pbs ts pbs2) B2).
{ destruct OUT2 as [(_ & Ec & _) | (_ & Eb & Ec & _ & _)].
- subst cap'. exact (BOK_weak _ _ _ _ _ (proj2 BUDM buf' B2 HB2 HD2)).
- subst buf' cap'. unfold pbs2. change 16 with PB_SZ. rewrite <- Epbs. replace (ts_pbs ts (t_pbs ts)) with ts by (destruct ts; reflexivity).
exact (BOK_memappend_fail pf pa ts B B2 kB (t_pb ts) buf cap bpos xn BK Epbs Hbp0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HB2 HD2). }
assert (REST2 : PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 (ts_pbs ts pbs2) errv2).
{ eapply (PE_REST_A_call_pb HIx GA GA_pres) with (ts := ts) (LBc := LBc);
[exact STC | exact REST1 | exact VM2 | exact HPR2 | | | exact ST2 | exact ERR2 | exact BUD2].
- unfold LBc; intros b Hb; apply in_or_app;
apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; apply in_or_app; left; exact Hb | apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; right; right; exact Hb]].
- unfold pe_blocksA, tstate_blocks; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs]; exact HP2. }
assert (PBany : pbuf asegs m2 pbs2 (t_pb ts)).
{ destruct OUT2 as [(_ & _ & PBS) | (_ & -> & -> & _ & PC)]; [eapply pbufc_pbuf; exact PBS|].
exists buf, bpos, cap, pre, post. split; [reflexivity|]. split; [exact Lpre | exact PC]. }
assert (INV2 : PE_INV_AX pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 (ts_pbs ts pbs2) errv2 (pe_frameAX m2 pf pa nb pj sv ffc shc)).
{ split; [| exact REST2]. unfold ts_pbs; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOK|]. split; [exact PBany|]. split; [exact Hpb|]. split; [exact TSK1 | exact FR2]. }
assert (Hbl : 0 <= bpos <= Z.of_nat (length (pre ++ [Z_to_bv 8 0] ++ post))) by (destruct CORE1 as (C1 & _ & C3 & _); lia).
eapply (K m2 md2 A2 B2 pbs2 errv2 r); [exact INV2 | | exact FS2 | exact FRM2].
destruct OUT2 as [(-> & Ec & PBS) | (-> & -> & -> & _ & _)].
- left. split; [reflexivity|]. split.
+ eapply (PBOKat_appended m2 _ (bnd + xn) (t_pb ts) buf' cap' bpos (pre ++ [Z_to_bv 8 0] ++ post) src); [reflexivity | reflexivity | exact PBS | exact Hbl |]. lia.
+ unfold pbs2. rewrite Ec. exact (proj2 BUDM buf' B2 HB2 HD2).
- right. split; [reflexivity|]. unfold pbs2. change 16 with PB_SZ. symmetry. exact Epbs.
Qed.
End WithIface.
End RC__1.
End Mq1.
From Stdlib Require NArith.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg QmZZ QKQo Q6WR QrPc QeuE QI6Z QkXq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn QKQo Q8tj. Import QPZI.Mq4.
Import Q6WR Q6WR.Mq0 QrPc. Import QeuE.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mq3 QW22 QI6Z.Mq1 Qiiq.Mq2 QlKV.Mq5 QkXq.Mq3 Qiiq.Mq4 Qoif.Mq1.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PutA.
Variable HIx : heap_iface_A A4L.
Hypothesis DEL : lh_delete_tail_A_stmt HIx.

Theorem json_object_put_A_cps : put_stmt_A HIx.
Proof.
unfold put_stmt_A, put_stmtA. intros until rc. intros HP PRE A0 ST LO LOS SPA HT ERR TP RA BB K.
unfold put_stk_A in LOS. unfold put_entry_A.
unfold_consts. unfold A_SB, A_TP, A_ERRNO in *. word_range sp SPW.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP) as [HB0 HD0].
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL]. a4l.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU.
reenterA asegs A4L HIx asegs_wx HP. subst a0 tp.
carve_frame 112%nat ST.
do 14 step.
step.
destruct s as [c|].
- destruct PRE as (Hp & Hrc & J).
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND.
destruct (jval_hdr asegs A4F c m BS p rc J (nodup_app_l' _ _ (nodup_app_l' _ _ ND))) as (n & tojs_ & pb_ & udel_ & ud_ & rest_ & INp & _ & N48 & _ & _). clear tojs_ pb_ udel_ ud_ rest_.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p n HP ltac:(apply in_or_app; left; apply in_or_app; left; exact INp)) as (_ & Hpal & Hplo & Hphi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
if_falsex.
step. step. step. step. step. step. step.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
assert (J1 : jval asegs A4F c m1 BS p rc).
{ eapply jval_agree; [exact J | | apply incl_refl]. eapply (agree_of_munch asegs); [exact MU | exact WM |].
intros a k Hin. pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin)) as (Hk & _ & _ & Hahi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hahi. cbn. lia. }
assert (HPR1 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m1).
{ eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; rewrite <- app_assoc; apply in_or_app; right; exact Hb | clia |].
apply Forall_cons; [cbn [fst snd]; left; clia | apply Forall_nil]. }
evt_done5.
eapply (maybe_free_A_closed HIx) with (s := c) (BS := BS) (LB := LB) (x := p) (rc := rc) (lo := lo);
[ heap_nowA A4L HIx HP MU WM MI | exact Hp | exact Hrc | exact J1 | .. ]; a4l_goal; rewrite ?unsigned_lit by lia; try first [reflexivity | lia].
all: try (replace (bv_unsigned sp + -112) with (bv_unsigned sp - 112) by lia; rewrite Zminus_mod, SPA; reflexivity).
all: try exact ERR. all: try assumption.
all: try (intros ->; cbn [put_costA] in BB; rewrite Z.eqb_refl in BB; exact BB).
intros ms2 md2 A2 (m2 & r & B2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & BD2 & OUT2).
destruct RS2 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F2 & fc2 & -> & FS2 & FRM2).
a4l. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in ST2 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in HPR2 by lia.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
assert (HPR12 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m2).
{ eapply heap_pres_trans; [exact HPR1 | eapply heap_pres_weaken; [exact HPR2 | lia | intros b Hb; exact Hb]]. }
clear MU WM MI J J1.
destruct OUT2 as [(Er & Hrc2 & J2 & BB2 & HP2) | [(Er & -> & BB2 & HP2) | (Er & -> & ZM & BB2 & HP2)]]; subst r.
+
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
pose proof (wmono_refl asegs m2) as WM. pose proof (munch_refl [] m2) as MU.
reenterA asegs A4L HIx asegs_wx HP2. step. step. if_truex.
do 14 step. release_frame FR ST2 (bv_unsigned sp). step.
evt_done5. apply K. unfold put_postA. exists m2, (Z_to_bv 64 0), B2.
split; [apply ret_statew_intro; [exact FS2 | exact FRM2] |]. split; [exact VM2|]. split; [exact ST2|]. split; [exact HPR12|]. split; [exact ERR2|].
split; [cbn [put_costA]; replace (rc =? 1) with false by (symmetry; apply Z.eqb_neq; lia); lia|]. split; [exact BD2|].
right. exists c. split; [reflexivity|]. split; [lia|]. split; [exact J2 | exact HP2].
+
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
pose proof (wmono_refl asegs m2) as WM. pose proof (munch_refl [] m2) as MU.
reenterA asegs A4L HIx asegs_wx HP2. step. step. if_truex.
do 14 step. release_frame FR ST2 (bv_unsigned sp). step.
evt_done5. apply K. unfold put_postA. exists m2, (Z_to_bv 64 1), B2.
split; [apply ret_statew_intro; [exact FS2 | exact FRM2] |]. split; [exact VM2|]. split; [exact ST2|]. split; [exact HPR12|]. split; [exact ERR2|].
split; [cbn [put_costA]; rewrite Z.eqb_refl; lia|]. split; [exact BD2|].
left. split; [right; reflexivity | exact HP2].
+
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
pose proof (wmono_refl asegs m2) as WM. pose proof (munch_refl [] m2) as MU.
destruct (zomb_zhead HIx sp gp lo errv LM FRS c m2 p BS ZM (desc_allA HIx sp gp lo errv LM FRS LO ltac:(lia) SPA HT DEL c)) as (isobj & ck & ZH & HS).
reenterA asegs A4L HIx asegs_wx HP2. step. step. if_false.
step. step. step. step.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply bv_eq; vm_compute; reflexivity).
evt_done5.
stash FR.
eapply HS; [exact HP2 | exact ZH | exact ST2 | exact ERR2 | cbn [put_costA] in BB; rewrite Z.eqb_refl in BB; lia |].
intros ms3 md3 A3 (m3 & F3 & fc3 & B3 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w18 & w19 & w20 & w21 & w22 & w23 & -> & FS3 & FRM3 & VM3 & HP3 & ST3 & HPR3 & ERR3 & HB3 & HD3).
unstash FR.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. a4l.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI3.
clear WM MU. pose proof (wmono_refl asegs m3) as WM. pose proof (munch_refl [] m3) as MU.
reenterA asegs A4L HIx asegs_wx HP3.
step. step. if_true. step.
do 14 step. release_frame FR ST3 (bv_unsigned sp). step.
evt_done5. apply K. unfold put_postA. exists m3, (Z_to_bv 64 1), B3.
split; [apply ret_statew_intro; [eapply fsaved_trans; [exact FS2 | exact FS3] | intros Hf; exact (FRM3 (FRM2 Hf))] |].
split; [eapply model_vm_only_trans; [exact VM2 | exact VM3]|]. split; [exact ST3|].
split; [eapply heap_pres_trans; [exact HPR12 | eapply heap_pres_weaken; [exact HPR3 | lia | intros b Hb; exact Hb]]|].
split; [exact ERR3|]. split; [cbn [put_costA]; rewrite Z.eqb_refl; lia|]. split; [lia|].
left. split; [right; reflexivity | exact HP3].
-
destruct PRE as [-> ->]. cbn [app] in HP.
if_true.
do 14 step. release_frame FR ST (bv_unsigned sp). step.
evt_done5. apply K. unfold put_postA.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, (Z_to_bv 64 0), B end.
split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|]. split; [exact ST|].
split.
{ eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; exact Hb | clia |].
apply Forall_cons; [cbn [fst snd]; left; clia | apply Forall_nil]. }
split; [assumption|]. split; [cbn [put_costA]; lia|]. split; [lia|].
left. split; [left; reflexivity |].
eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); apply Forall_cons; [cbn [fst snd]; left; split; [clia | pose proof (hiA_top_hi A4L HIx); lia] | apply Forall_nil] | exact WM | assumption].
Qed.
End PutA.
End RC__1.
End Mq2.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache Qfw3_c1 Qc3B QSL3 Qvbw QYIF QnCn QR2u QrIB QXUB QJZd Qw5U Qvmy Qawr QB6X.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun QWxq_c1.Mq0 Qfw3_c1.Mq2 Qc3B Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn QKQo Q8tj QRUw.Mq2.
Import QSL3.
Import Qvbw QYIF.
Import QnCn.Mq0 QR2u.

Import Q7UD QXUB.Mq0 Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QsKa.Mq4 QlKV.Mqa QsKa.Mq7 QsKa.Mq0 QJZd.Mq0 QsKa.Mq8 Qw5U.Mq0 QsKa.Mq3 QsKa.Mq2 QlKV.Mq7 QsKa.Mq5 QlKV.Mq5 QlKV.Mq2 QsKa Qiiq.Mq0.

Import Qvmy.Mq0 Qawr.Mq0.
Import Qwm6.Mq2.
Import QB6X.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Import Qoif.Mq2.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section MDcTail.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Notation wz := (Z_to_bv 64).
Notation jroot_repA := (jroot_rep A4H A4F).
Hypothesis SHALLOW : shallow_A_stmt HIx.
Hypothesis PUT : put_stmt_A HIx.

Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB BS LM : list blk) (FRS : list frame) (B0 : bud) (lo p D w : Z) (r : jroot) (T : TSet).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp - dc_stkA (rdepth r).
Hypothesis SPA : bv_unsigned sp mod 32 = 0.
Hypothesis HT : bv_unsigned sp <= hiA_top A4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis FRM0 : frm0 fc.
Hypothesis DLOC : arg_locA FRS D 8.
Hypothesis DAL : D mod 8 = 0.
Hypothesis NN : r <> JRnull.
Hypothesis JR0 : jroot_repA r m0 BS p.
Hypothesis Kont : forall ms' md' m' rv (A' : ASA A4L HIx) (B' : bud),
jo_post_frameDA D ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 (BS ++ LB) (LM ++ fr_ivs A4L FRS) lo rv m' ms' md' ->
lh_globA m' -> jroot_repA r m' BS p -> dc_resA HIx r BS LB LM FRS D w B0 m' md' rv A' B' ->
AJ5 A4L HIx A' T md' ms'.
Local Notation fk1_HEAPA_W := (Qoif.Mq2.fk1_HEAPA_W HIx) (only parsing).
Local Notation fk1_pres_W := (Qoif.Mq2.fk1_pres_W HIx) (only parsing).
Local Notation dc_blk_notfr := (Qoif.Mq2.dc_blk_notfr HIx) (only parsing).
Local Notation ASP := (Qoif.Mq2.ASP sp) (only parsing).
Local Notation dc_save := (Qoif.Mq2.dc_save ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) (only parsing).
Local Notation dc_inv := (Qoif.Mq2.dc_inv ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB BS LM FRS lo D) (only parsing).
Local Notation dc_dst := (Qoif.Mq2.dc_dst D) (only parsing).
Local Notation dc_dfacts := (Qoif.Mq2.dc_dfacts HIx ra sp LM FRS D DLOC DAL) (only parsing).
Local Notation dc_dst_pres := (Qoif.Mq2.dc_dst_pres HIx ra sp LM FRS D DLOC) (only parsing).
Local Notation dc_blkW_disj := (Qoif.Mq2.dc_blkW_disj HIx ra sp LM FRS D DLOC DAL) (only parsing).
Local Notation dc_dst_blkW := (Qoif.Mq2.dc_dst_blkW HIx ra sp LM FRS D DLOC DAL) (only parsing).
Local Notation dc_epi := (Qoif.Mq2.dc_epi HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB BS LM FRS B0 lo p D w r T LO LOS HT DLOC NN JR0 Kont) (only parsing).
Local Notation dc_scr := (Qoif.Mq2.dc_scr p D) (only parsing).
Hypothesis OBL_STRDUP_NF : strdup_nf_stmt A4L HIx.

Lemma dc_tail_ud :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mc : word -> option byte) (mdc : config) (A : ASA A4L HIx) (Bc : bud) (Fr : Z) (v0 : word) (c24 : cell) (j16 : list byte)
(w0 : word) (frest : list cell) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : byte)
(q pb ud udn : Z) (uds : list byte) (bits bits' : word) (REM : list blk),
dc_inv mc mdc -> fsaved F F1 -> frm0 fc1 ->
HEAPAx A (BS ++ [(q, 48)] ++ REM ++ LB) LM ((Fr, 1) :: FRS) Bc mc mdc ->
rw_cells asegs mc ASP (dc_scr Fr v0 c24 j16) -> csize c24 = 8%nat ->
rw_cells asegs mc Fr (C8 w0 :: frest) -> Z.of_nat (cells_size frest) = 112 ->
rw_cells asegs mc (Fr / 8 + 2147450880) [C1 y0; C1 y1; C1 y2; C1 y3; C1 y4; C1 y5; C1 y6; C1 y7; C1 y8; C1 y9; C1 y10; C1 y11; C1 y12; C1 y13; C1 y14; C1 y15] ->
jroot_repA r mc BS p -> In (p, 48) BS -> In (ud, udn) BS -> udn <= 2^31 ->
rw_cells asegs mc p (jhdr_cells JT_DOUBLE 1 (fn_ud_to_json_string A4F) pb (fn_free_userdata A4F) ud ++ [C8 bits]) ->
cstr asegs mc ud udn uds ->
r = JRtree (Sdouble true) ->
q <> 0 -> dc_dst mc q ->
rw_cells asegs mc q (jhdr_cells JT_DOUBLE 1 (fn_ud_to_json_string A4F) 0 0 0 ++ [C8 bits']) ->
16 + Z.of_nat (length uds) <= w ->
16 * (Z.of_nat (length uds) + 1) + 512 <= bB Bc -> 1 <= bD Bc ->
bD B0 - w <= bD Bc - 1 -> bB B0 - DC_KB * w + 512 * 2 <= bB Bc - (16 * (Z.of_nat (length uds) + 1) + 512) ->
AJ5 A4L HIx A T mdc
(MS (mkR x1 (wz ASP) gp (wz A_TP) t0 t1 t2 sp (wz ASP) a0 a1 a2 a3 a4 a5 a6 a7
(wz (Fr / 8 + 2147450880)) x19 (wz 2147450880) x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
F1 (wz 0x9fba8) fc1 None mc (seg_rom asegs)).
Proof.
intros until REM. intros INV FS FRM1 HP SCR C24 FF FFsz FSH JRc INp INu UDN SRC CS Er Hq [DC DSH] QX WUD BBs BDs BDc BBc.
pose proof INV as (VMi & PRESi & STi & SAVEi & Gi). unfold dc_save in SAVEi.
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu. unfold ASP, dc_scr in *.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
destruct (dc_dfacts _ _ _ _ _ _ HP) as (D1 & D2 & D3 & D4 & DBLK & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13).
pose proof (rw_cells_bound asegs mc D _ DC) as DR. cbn [cells_size csize Nat.add] in DR.
assert (INp2 : In (p, 48) (BS ++ [(q, 48)] ++ REM ++ LB)) by (apply in_or_app; left; exact INp).
assert (INu2 : In (ud, udn) (BS ++ [(q, 48)] ++ REM ++ LB)) by (apply in_or_app; left; exact INu).
assert (INq2 : In (q, 48) (BS ++ [(q, 48)] ++ REM ++ LB)) by (apply in_or_app; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p 48 HP ltac:(apply in_or_app; left; exact INp2)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ q 48 HP ltac:(apply in_or_app; left; exact INq2)) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ q 48 HP ltac:(apply in_or_app; left; exact INq2)) as Hqimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hqimg.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ ud udn HP ltac:(apply in_or_app; left; exact INu2)) as (_ & Hual & Hulo & Huhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi, Hqhi, Huhi.
pose proof (DBLK p 48 ltac:(apply in_or_app; left; exact INp2)) as DBp. pose proof (DBLK q 48 ltac:(apply in_or_app; left; exact INq2)) as DBq.
assert (Hqp : q <> p).
{ intros ->. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. rewrite <- app_assoc in ND.
exact (nodup_mid_fresh BS [(p, 48)] ((REM ++ LB) ++ LM) p 48 48 ND ltac:(left; reflexivity) ltac:(apply in_or_app; left; exact INp)). }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ q 48 p 48 HP ltac:(apply in_or_app; left; exact INq2) ltac:(apply in_or_app; left; exact INp2) Hqp) as Hdqp.
destruct CS as (CL & CNZ & junk & CBk).
assert (NNu : ~ In (Z_to_bv 8 0) uds) by (intros X; rewrite Forall_forall in CNZ; apply (CNZ _ X); reflexivity).
assert (USTR : bytes_at asegs mc ud (uds ++ [Z_to_bv 8 0])).
{ assert (BBu : bytes_at asegs mc ud ((uds ++ [Z_to_bv 8 0]) ++ junk)) by (destruct CBk as [[[_ _] HB] _]; cbn in HB; rewrite app_nil_r in HB; rewrite <- app_assoc; exact HB).
apply bytes_at_app in BBu as [BBu _]. exact BBu. }
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p 48 3 HP INp2 ltac:(lia) ltac:(lia)) as SHp3.
replace (p / 8 + 2147450880 + 3) with (p / 8 + 2147450883) in SHp3 by lia.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p 48 4 HP INp2 ltac:(lia) ltac:(lia)) as SHp4.
replace (p / 8 + 2147450880 + 4) with (p / 8 + 2147450884) in SHp4 by lia.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ q 48 1 HP INq2 ltac:(lia) ltac:(lia)) as SHq1.
replace (q / 8 + 2147450880 + 1) with (q / 8 + 2147450881) in SHq1 by lia.
set (sh := Fr / 8 + 2147450880) in *.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. change (hl_segs A4L) with asegs in MI.
pose proof (Qw5U.Mq0.rtc_cell HIx _ _ _ _ _ _ _ 0xe6a58 (le8 (wz 0x9dd6c)) HP ltac:(unfold a4_rt_consts; repeat first [left; reflexivity | right])) as GOTU.
apply ro_C8_of_bytes_at in GOTU.
pose proof (wmono_refl asegs mc) as WM. pose proof (munch_refl [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6434236, 6434240)] mc) as MU.
unfold jhdr_cells in SRC, QX. cbn [app fn_ud_to_json_string fn_free_userdata A4F] in SRC, QX.
lazymatch type of SCR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?rest) => change (c0 :: c1 :: c2 :: c3 :: rest) with ([c0; c1; c2] ++ ([c3] ++ rest)) in SCR end.
destruct (proj1 (rw_cells_app asegs mc _ _ _) SCR) as [SCRa SCRx]. cbn [cells_size csize Nat.add] in SCRx.
destruct (proj1 (rw_cells_app asegs mc _ _ _) SCRx) as [SCR24 SCRb]. cbn [cells_size Nat.add] in SCRb. rewrite C24 in SCRb.
replace (bv_unsigned sp + -192 + Z.of_nat 24 + Z.of_nat (8 + 0)) with (bv_unsigned sp + -160) in SCRb by lia.
replace (bv_unsigned sp + -192 + Z.of_nat 24) with (bv_unsigned sp + -168) in SCR24 by lia.
stash SCR24. stash SCR. clear SCRx.
stash JRc. clear INV. stash PRESi. stash Gi. stash USTR. stash CBk.
unfold A_TP. a4l.
reenterA asegs A4L HIx asegs_wx HP.
step. step. step. step. if_lit.
step. asan_chkM 1.
step. step. asan_chkA.
step. step. step. step. if_truex.
step. asan_chkA.
step. step. step. step.
if_lit. step. step. step. if_lit.
step.

unstash USTR.
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP) as (errs & ERRs).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => constr_eq mx mc end.
evt_done5.
eapply OBL_STRDUP_NF with (u := UWpaid) (src := ud) (ab := ud) (nb := udn) (str := uds) (lo := lo) (errv := errs); [exact HP | .. ].
all: rewrite ?unsigned_lit by lia.
1: exact INu2. 1: lia. 1: lia. 1: exact USTR. 1: exact NNu. 1: lia.
1: exact STi.
1: exact LO. 1: cbn [hl_stack_A A4L]; lia. 1: clear - SPA; Z.div_mod_to_equations; lia. 1: lia.
1: exact ERRs. 1: reflexivity. 1: reflexivity. 1: exact I. 1: exact I. 1: exact BBs. 1: cbn [uw_cost]; lia.
intros ms2 m2 md2 A2 rd e2 RS2 VM2 ST2 HPR2 ERR2 Hrd SDUP HP2. open_ret RS2.
rewrite ?(unsigned_lit (bv_unsigned sp + -192)) in ST2 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -192)) in HPR2 by lia.
change (hl_segs A4L) with asegs in *. cbn [uw_cost] in HP2.

assert (HPRX : forall A0 cs0, rw_cells asegs mc A0 cs0 ->
client_range A4H ((BS ++ [(q, 48)] ++ REM ++ LB) ++ LM ++ fr_ivs A4L ((Fr, 1) :: FRS)) (bv_unsigned sp + -192) A0 (Z.of_nat (cells_size cs0)) -> rw_cells asegs m2 A0 cs0).
{ intros A0 cs0 H1 H2. exact (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2 H1 H2). }
unstash SCR. apply HPRX in SCR; [| left; lia]. stash SCR.
clear SCRa SCRb SCR24.
apply HPRX in SAVEi; [| left; lia].
apply HPRX in FF.
2: { eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; left; reflexivity | cbn [fr_base fst]; lia |].
cbn [fr_base fr_class fst snd]. rewrite fr_size_1. change (cells_size (C8 w0 :: frest)) with (8 + cells_size frest)%nat. rewrite Nat2Z.inj_add, FFsz. lia. }
apply HPRX in FSH; [| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; right; left; reflexivity | unfold shad; cbn [fr_base fst hl_sb A4L]; unfold A_SB; fold sh; lia
| unfold shad; cbn [cells_size csize Nat.add fr_base fr_class fst snd hl_sb A4L]; rewrite fr_shadow_len_1; unfold A_SB; fold sh; lia]].
apply HPRX in SRC; [| eapply client_range_block; [apply in_or_app; left; exact INp2 | lia | cbn [cells_size csize Nat.add]; lia]].
apply HPRX in QX; [| eapply client_range_block; [apply in_or_app; left; exact INq2 | lia | cbn [cells_size csize Nat.add]; lia]].
pose proof (dc_dst_pres _ _ _ _ _ _ _ _ _ _ _ HP (conj DC DSH) HPR2) as DD2.
clear HPRX DC DSH.

assert (INp3 : In (p, 48) ((rd, Z.of_nat (length uds) + 1) :: BS ++ [(q, 48)] ++ REM ++ LB)) by (right; exact INp2).
assert (INq3 : In (q, 48) ((rd, Z.of_nat (length uds) + 1) :: BS ++ [(q, 48)] ++ REM ++ LB)) by (right; exact INq2).
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p 48 3 HP2 INp3 ltac:(lia) ltac:(lia)) as SHp3'.
replace (p / 8 + 2147450880 + 3) with (p / 8 + 2147450883) in SHp3' by lia.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ q 48 3 HP2 INq3 ltac:(lia) ltac:(lia)) as SHq3.
replace (q / 8 + 2147450880 + 3) with (q / 8 + 2147450883) in SHq3 by lia.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ q 48 4 HP2 INq3 ltac:(lia) ltac:(lia)) as SHq4.
replace (q / 8 + 2147450880 + 4) with (q / 8 + 2147450884) in SHq4 by lia.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 48 3 q 48 HP2 INq3 ltac:(cbn; lia) ltac:(apply in_or_app; left; exact INq3)) as SEPq3.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 48 4 q 48 HP2 INq3 ltac:(cbn; lia) ltac:(apply in_or_app; left; exact INq3)) as SEPq4.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ p 48 3 q 48 HP2 INp3 ltac:(cbn; lia) ltac:(apply in_or_app; left; exact INq3)) as SEPp3.
cbn [hl_sb hl_img_lo hl_img_hi hla_base A4L A4H] in SEPq3, SEPq4, SEPp3. unfold A_SB in SEPq3, SEPq4, SEPp3.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ rd _ HP2 ltac:(apply in_or_app; left; left; reflexivity)) as (_ & Hrdal & Hrdlo & Hrdhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hrdhi.
clear SHp3 SHp4 SHq1 MU WM MI GOTU.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI2. change (hl_segs A4L) with asegs in MI2.
pose proof (wmono_refl asegs m2) as WM2.
pose proof (munch_refl [(q, q + 48)] m2) as MU2.
stash SAVEi. stash FF. stash FSH. stash DD2. stash ST2. stash SDUP. stash HPR2. clear ERR2 ERRs.
replace (ret_pc (wz 654436)) with (wz 654436) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
reenterA asegs A4L HIx asegs_wx HP2.
step. if_falsex.
step. asan_chkA. stepz.
step. asan_chkA.
step. asan_chkA.
step. stepz. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mX end.
assert (HW : Forall (fun iv : Z * Z => exists a n, In (a, n) (((rd, Z.of_nat (length uds) + 1) :: BS ++ [(q, 48)] ++ REM ++ LB) ++ LM) /\ a <= fst iv /\ snd iv <= a + n) [(q, q + 48)]).
{ apply Forall_cons; [| apply Forall_nil]. exists q, 48. split; [apply in_or_app; left; exact INq3 | cbn [fst snd]; lia]. }
assert (MUw : munch ([(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 16); (6434236, 6434240)] ++ [(q, q + 48)]) m2 mX).
{ eapply munch_weaken; [| exact MU2]. clear. intros x Hx. cbn [app outside] in *. tauto. }
pose proof (fk1_HEAPA_W _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -104) _ _ HP2 LO ltac:(lia) HW MUw WM2 MI2) as HPY.

assert (NIq : ~ In (q, 48) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS)).
{ pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. rewrite <- !app_assoc in ND.
pose proof (nodup_mid_fresh BS [(q, 48)] (REM ++ LB ++ LM) q 48 48 ND ltac:(left; reflexivity)) as NI.
intros Hin. apply in_app_or in Hin as [Hin | Hin]; [apply NI; apply in_app_or in Hin as [Hin | Hin]; [apply in_or_app; left; exact Hin | apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hin] |].
apply in_app_or in Hin as [Hin | Hin]; [apply NI; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hin |].
eapply (dc_blk_notfr _ _ _ _ _ _ _ q 48 HP); [apply in_or_app; left; exact INq2 | lia | cbn [fr_ivs flat_map app]; right; right; exact Hin]. }
assert (HPR2X : heap_pres A4H ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -104) m2 mX).
{ eapply (fk1_pres_W _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -104) [(q, q + 48)] _ _ HP2 LO ltac:(lia)); [| | exact MUw | exact WM2].
- intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [left; apply in_or_app; left; right; apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; right; cbn [app]; apply in_or_app; right; exact Hb] |].
apply in_app_or in Hb as [Hb | Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb].
- apply Forall_cons; [| apply Forall_nil]. exists q, 48. split; [apply in_or_app; left; exact INq3 |]. split; [exact NIq | cbn [fst snd]; lia]. }

assert (DJ : forall A0 n0, (alloc_ceiling <= A0 \/ (Fr <= A0 /\ A0 + n0 <= Fr + 128) \/ (2147450880 <= A0 /\ A0 + n0 <= 17594333495296) \/ (D <= A0 /\ A0 + n0 <= D + 8)) -> disjoint_from [(q, q + 48)] A0 n0).
{ intros A0 n0 K. exact (dc_blkW_disj _ _ _ _ _ _ _ A0 n0 HP2 HW K). }
unstash SCR. apply (rw_cells_transport asegs [(q, q + 48)] _ mX) in SCR; [| exact MU2 | exact WM2 | apply DJ; left; lia].
unstash SAVEi. apply (rw_cells_transport asegs [(q, q + 48)] _ mX) in SAVEi; [| exact MU2 | exact WM2 | apply DJ; left; lia].
unstash FF. apply (rw_cells_transport asegs [(q, q + 48)] _ mX) in FF; [| exact MU2 | exact WM2 |].
2: { apply DJ; right; left. change (cells_size (C8 w0 :: frest)) with (8 + cells_size frest)%nat. rewrite Nat2Z.inj_add, FFsz. lia. }
unstash FSH. apply (rw_cells_transport asegs [(q, q + 48)] _ mX) in FSH; [| exact MU2 | exact WM2 | apply DJ; right; right; left; cbn [cells_size csize Nat.add]; lia].
unstash ST2. apply (stk_transport_disjoint asegs [(q, q + 48)] _ mX) in ST2; [| exact MU2 | exact WM2 | apply DJ; left; lia].
unstash DD2. pose proof (dc_dst_blkW _ _ _ _ _ _ _ _ _ _ HP2 HW MU2 WM2 DD2) as [DCX DSHX].
assert (Hrq : rd + (Z.of_nat (length uds) + 1) <= q \/ q + 48 <= rd).
{ assert (NE : rd <> q).
{ intros ->. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP2) as ND. cbn [app map] in ND. apply List.NoDup_cons_iff in ND as [Hni _].
apply Hni. apply (in_map blk_addr _ (q, 48)). apply in_or_app; left. exact INq2. }
exact (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ rd _ q 48 HP2 ltac:(apply in_or_app; left; left; reflexivity) ltac:(apply in_or_app; left; exact INq3) NE). }
unstash SDUP. apply (bytes_at_transport asegs [(q, q + 48)] _ mX) in SDUP; [| exact MU2 | cbn [disjoint_from]; rewrite length_app; cbn [length]; clear - Hrq; lia].

assert (INCL2 : forall b, In b ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) -> In b ((BS ++ [(q, 48)] ++ REM ++ LB) ++ LM ++ fr_ivs A4L ((Fr, 1) :: FRS))).
{ intros b Hb. apply in_app_or in Hb as [Hb | Hb].
- apply in_or_app; left. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; right; cbn [app]; apply in_or_app; right; exact Hb].
- apply in_or_app; right. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; cbn [fr_ivs flat_map app]; right; right; exact Hb]. }
unstash HPR2.
assert (HPRcX : heap_pres A4H ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) mc mX).
{ eapply heap_pres_trans; [eapply heap_pres_weaken; [exact HPR2 | lia | exact INCL2] | eapply heap_pres_weaken; [exact HPR2X | lia | intros b Hb; exact Hb]]. }
unstash JRc. unstash PRESi. unstash Gi.
pose proof (agree_of_heap_pres asegs A4H _ _ (BS ++ LB) _ _ HPRcX eq_refl ltac:(intros b Hb; apply in_or_app; left; exact Hb)) as AGcX.
pose proof (QrIB.Mq0.jroot_rep_agree A4H A4F _ _ _ _ _ _ JRc AGcX ltac:(apply incl_appl; apply incl_refl)) as JRX.
assert (INVX : dc_inv mX md2).
{ split; [eapply model_vm_only_trans; [exact VMi | exact VM2] |].
split; [eapply (QrIB.Mq0.presxD_trans A4H); [exact PRESi | apply (QrIB.Mq0.pres_presxD A4H); exact HPRcX] |].
split; [exact ST2 |]. split; [unfold dc_save; exact SAVEi |]. eapply lh_globA_client; [exact HPRcX | exact Gi]. }
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ rd _ HPY ltac:(apply in_or_app; left; left; reflexivity)) as (_ & _ & _ & _ & Hrdwr).
evt_done5.
eapply (dc_epi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 mX md2 A2 _ (BS ++ [(q, 48); (rd, Z.of_nat (length uds) + 1)] ++ REM ++ LB) Fr 0);
[ exact INVX | exact FS | exact FRM1 | eapply (heapA_perm A4L HIx); [exact HPY | perm | apply Permutation_refl | apply Permutation_refl]
| exact SCR | rewrite !cells_size_app; cbn [cells_size]; rewrite C24; reflexivity | exact FF | exact FFsz | exact FSH | exact JRX | ].
split; [cbn [charge bD]; lia |]. left. split; [reflexivity|]. exists (JRtree (Sdouble true)), q, [(q, 48); (rd, Z.of_nat (length uds) + 1)], REM.
split; [reflexivity|]. split; [rewrite Er; exists (Sdouble true); split; [reflexivity | lia] |].
split; [cbn [dc_cwA jtx]; rewrite Z.eqb_refl; eexists; split; [reflexivity | lia] |].
split; [exact Hq|]. split; [exact DCX|].
split; [| cbn [charge bB length Z.of_nat]; lia].
split; [exact Hq|]. cbn [jval]. exists 0, [], [(q, 48); (rd, Z.of_nat (length uds) + 1)]. split; [reflexivity|]. split; [left; split; reflexivity|].
exists bits', rd, (Z.of_nat (length uds) + 1), uds. split; [reflexivity|]. split; [lia|].
split; [unfold jhdr_cells; cbn [fn_ud_to_json_string fn_free_userdata A4F app]; exact QX |].
unfold cstr. split; [lia|]. split; [exact CNZ|]. exists []. rewrite app_nil_r.
pose proof (bytes_at_bound _ _ _ _ SDUP) as NB. rewrite length_app in NB. cbn [length] in NB.
split; [split; [cbn; split; [rewrite length_app; cbn [length]; lia | exact I] | cbn; rewrite app_nil_r; exact SDUP] |].
cbn [cells_size csize Nat.add]. replace (Z.of_nat (Z.to_nat (Z.of_nat (length uds) + 1) + 0)) with (Z.of_nat (length uds) + 1) by lia. exact Hrdwr.
Qed.
End MDcTail.
End RC__1.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Q8tj.
Import QlKV.Mq2 Qiiq.Mq0 Q1Y6.Mq0 Qoif.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Definition DC_KOBJ : Z := 6848.

Definition obj_inv (cap cnt : Z) : Prop := In cap lf_sizes /\ 0 <= cnt /\ (cap = 16 \/ 1280 * cap <= 3904 * cnt).

Lemma lf_thr_lowerW : forall S, In S lf_sizes -> 2560 * S <= 3904 * lf_thr S + 3904.
Proof.
intros S H. assert (C : forallb (fun S => 2560 * S <=? 3904 * lf_thr S + 3904) lf_sizes = true) by (vm_compute; reflexivity).
rewrite forallb_forall in C. specialize (C S H). apply Z.leb_le in C. exact C.
Qed.
Lemma lf_sizes_doubleW : forall S, In S lf_sizes -> S <= 2^29 -> In (2 * S) lf_sizes.
Proof.
intros S H Hle. assert (C : forallb (fun S => if S <=? 2^29 then existsb (Z.eqb (2 * S)) lf_sizes else true) lf_sizes = true) by (vm_compute; reflexivity).
rewrite forallb_forall in C. specialize (C S H). rewrite (proj2 (Z.leb_le S (2^29)) Hle) in C.
apply existsb_exists in C as (x & Hx & E). apply Z.eqb_eq in E. rewrite E. exact Hx.
Qed.
Lemma lf_sizes_pos : forall S, In S lf_sizes -> 16 <= S.
Proof.
intros S H. assert (C : forallb (fun S => 16 <=? S) lf_sizes = true) by (vm_compute; reflexivity).
rewrite forallb_forall in C. specialize (C S H). apply Z.leb_le in C. exact C.
Qed.

Lemma obj_inv_new : obj_inv 16 0.
Proof. split; [left; reflexivity | split; [lia | left; reflexivity]]. Qed.
Lemma obj_inv_cap : forall cap cnt, obj_inv cap cnt -> cnt < 2^24 -> cap <= 2^29.
Proof. intros cap cnt (_ & _ & [-> | H]) Hc; lia. Qed.
Lemma PhiO_nonnegW : forall cap cnt, obj_inv cap cnt -> 0 <= PhiO cap cnt.
Proof. intros cap cnt (_ & H0 & [-> | H]); unfold PhiO; lia. Qed.

Lemma potential_step_obj_add : forall cap cnt cap',
obj_inv cap cnt -> cap <= 2^29 -> obj_grownA cap cnt cap' ->
PhiO cap cnt + DC_KOBJ >= ins_costB cap cnt + PhiO cap' (cnt + 1) /\ obj_inv cap' (cnt + 1).
Proof.
intros cap cnt cap' (HS & H0 & HI) Hcap G. pose proof (lf_thr_lowerW cap HS) as LT. pose proof (lf_sizes_pos cap HS) as SP.
unfold PhiO, DC_KOBJ, ins_costB, resize_costB, obj_grownA, obj_inv in *.
destruct G as [[-> Hlt] | [-> Hge]].
- replace (lf_thr cap <=? cnt) with false by (symmetry; apply Z.leb_gt; lia).
split; [lia|]. split; [exact HS|]. split; [lia|]. destruct HI as [-> | HI]; [left; reflexivity | right; lia].
- replace (lf_thr cap <=? cnt) with true by (symmetry; apply Z.leb_le; lia).
unfold lh_ns. rewrite (proj2 (Z.leb_le cap (2^29)) Hcap).
split; [lia|]. split; [apply lf_sizes_doubleW; assumption|]. split; [lia|]. right. lia.
Qed.

Lemma pair_budget : forall klen, 0 <= klen -> strdup_costB klen + 512 + DC_KOBJ <= 646 * key_w (klen + 1).
Proof. intros klen H. unfold strdup_costB, DC_KOBJ, key_w. replace (klen + 1 - 1) with klen by lia. rewrite Z.max_r by lia. lia. Qed.

End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Quoa QUr4 Qdgq_c1 Q2Do Q30W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun QWxq_c1.Mq0 Qfw3_c1.Mq2 Qc3B.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn.
Import Q6WR Q6WR.Mq0 QrPc.
Import Qvbw QYIF.
Import QnCn.Mq0 QR2u.
Import Quoa.Mq0 QUr4.

Import Q7UD QXUB.Mq0 Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QsKa.Mq4 QlKV.Mqa QsKa.Mq0 QJZd.Mq0 QsKa.Mq8 Qw5U.Mq0 QsKa.Mq3 Q2Do.Mq3 Q30W.Mq0.

Import Qvmy.Mq0 Qawr.Mq0.
Import Qoif.Mq3.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section MJoVisit2.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Notation joptA := (jopt asegs A4F).
Notation wz := (Z_to_bv 64).
Notation VISx := (VIS HIx).

Lemma arr_now : forall A LBa LM FRS' B mc mdc R SP0 m BS p tojs pb a AL ps,
HEAPAx A LBa LM FRS' B mc mdc -> heap_pres A4H (LBa ++ R) SP0 m mc -> incl BS LBa -> In (p, 48) BS -> incl AL BS ->
rw_cells asegs m p (jhdr_cells JT_ARRAY 1 tojs pb 0 0 ++ [C8 (wz a)]) -> alist asegs A4F m AL a ps ->
exists arr size,
rw_cells asegs mc p (jhdr_cells JT_ARRAY 1 tojs pb 0 0 ++ [C8 (wz a)]) /\ 0 < p /\ p + 48 <= alloc_ceiling /\ p mod 8 = 0 /\
ro_cells asegs mc (p / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] /\
p / 8 + A_SB + 6 <= alloc_ceiling /\
alist asegs A4F mc [(a, AL_SZ); (arr, 8 * size)] a ps /\ al_blkA a arr size /\
ro_cells asegs mc (a / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] /\
bytes_at asegs mc (arr / 8 + A_SB) (shadow_bytes (8 * size)) /\ 0 <= size /\ arr / 8 + A_SB + size <= alloc_ceiling /\
Z.of_nat (length ps) <= size.
Proof.
intros A LBa LM FRS' B mc mdc R SP0 m BS p tojs pb a AL ps HP HPR INC INp INAL HDR HAL.
pose proof alloc_ceiling_range as ACR.
destruct (alist_open asegs A4F m AL a ps HAL) as (arr & size & junk & EAL & OP).
exists arr, size.
assert (INpA : In (p, 48) LBa) by (apply INC; exact INp).
assert (INaA : In (a, 32) LBa) by (apply INC, INAL; rewrite EAL; left; reflexivity).
assert (INrA : In (arr, 8 * size) LBa) by (apply INC, INAL; rewrite EAL; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p 48 HP ltac:(apply in_or_app; left; exact INpA)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a 32 HP ltac:(apply in_or_app; left; exact INaA)) as (_ & Haal & Halo & Hahi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ arr (8 * size) HP ltac:(apply in_or_app; left; exact INrA)) as (Hrn & Hral & Hrlo & Hrhi & _).
assert (AG : agree_on asegs BS m mc).
{ eapply (agree_of_heap_pres asegs A4H); [exact HPR | reflexivity |]. intros b Hb. apply in_or_app; left. apply INC; exact Hb. }
split.
{ eapply rw_cells_agree; [exact HDR | exact AG |]. exists p, 48. split; [exact INp|]. unfold jhdr_cells. cbn. lia. }
split; [exact Hplo|]. split; [exact Hphi|]. split; [clear - Hpal; Z.div_mod_to_equations; lia|].
split.
{ pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ p 48 HP INpA) as SH. unfold shad in SH. apply shadow_ro_cells in SH.
cbn [hl_sb hl_segs hla_base A4L A4H] in SH. exact SH. }
split; [unfold A_SB; clear - Hphi ACR Hplo; Z.div_mod_to_equations; lia|].
split.
{ rewrite EAL in HAL. eapply (alist_agree asegs A4F); [exact HAL | exact AG |]. intros b Hb. apply INAL. rewrite EAL. exact Hb. }
split.
{ unfold al_blkA. split; [exact Halo|]. split; [clear - Haal; Z.div_mod_to_equations; lia|]. split; [exact Hahi|]. split; [exact Hrlo|]. split; [clear - Hral; Z.div_mod_to_equations; lia | exact Hrhi]. }
split.
{ pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ a 32 HP INaA) as SH. unfold shad in SH. apply shadow_ro_cells in SH.
cbn [hl_sb hl_segs hla_base A4L A4H] in SH. exact SH. }
split.
{ pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ arr (8 * size) HP INrA) as SH. unfold shad in SH.
cbn [hl_sb hl_segs hla_base A4L A4H] in SH. exact SH. }
split; [lia|].
split; [unfold A_SB; clear - Hrhi ACR Hrlo Hrn; Z.div_mod_to_equations; lia|].
destruct OP as (_ & _ & _ & Hlen & Hsz). lia.
Qed.

Lemma jopt_now : forall R SP0 m mc LBa k bs v,
heap_pres A4H (LBa ++ R) SP0 m mc -> incl bs LBa -> joptA k m bs v -> joptA k mc bs v.
Proof.
intros R SP0 m mc LBa k bs v HPR INC JO.
eapply (jopt_agree asegs A4F bs m mc k bs v); [exact JO | | apply incl_refl].
eapply (agree_of_heap_pres asegs A4H); [exact HPR | reflexivity |]. intros b Hb. apply in_or_app; left. apply INC; exact Hb.
Qed.

Lemma own_chunks_pres : forall LBa LM FRS Fr SPc mc m' A cs,
heap_pres A4H (LBa ++ LM ++ fr_ivs A4L ((Fr, 0) :: FRS)) SPc mc m' -> rw_cells asegs mc A cs ->
(SPc <= A \/ (Fr <= A /\ A + Z.of_nat (cells_size cs) <= Fr + 56) \/ (Fr / 8 + 2147450880 <= A /\ A + Z.of_nat (cells_size cs) <= Fr / 8 + 2147450880 + 8)) ->
rw_cells asegs m' A cs.
Proof.
intros LBa LM FRS Fr SPc mc m' A cs HPR H D.
change asegs with (hl_segs A4H). eapply (heap_pres_rw_cells A4H); [exact HPR | exact H |].
destruct D as [D | [D | D]].
- left. exact D.
- eapply client_range_block with (a := Fr) (k := 56); [| lia | lia].
apply in_or_app; right. apply in_or_app; right. cbn [fr_ivs flat_map app]. left. reflexivity.
- eapply client_range_block with (a := Fr / 8 + 2147450880) (k := 8); [| lia | lia].
apply in_or_app; right. apply in_or_app; right. cbn [fr_ivs flat_map app]. right. left. reflexivity.
Qed.

Lemma arr_loop : forall (fuel : nat) (kids : list (option jshape)),
(forall k, In k kids -> VISx k) ->
forall (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(LBa BS LM : list blk) (FRS : list frame) (B : bud) (lo p pb a : Z) (AL : list blk) (ps : list Z) (KBS : list (list blk)),
alloc_ceiling <= lo -> lo <= bv_unsigned sp - (VIS_STK0 + VIS_STK1 * odepth (Some (Sarr kids))) -> bv_unsigned sp <= hiA_top A4L HIx ->
0 <= bv_unsigned sp < 2^64 -> bv_unsigned sp mod 16 = 0 ->
Z.of_nat (length FRS) + (1 + odepth (Some (Sarr kids))) < 4096 ->
(forall ms' md' m' (A' : ASA A4L HIx),
ret_state A4H ra sp gp (wz 6434400) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (wz 0) m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (LBa ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' ->
HEAPAx A' LBa LM FRS B m' md' ->
AJ5 A4L HIx A' T md' ms') ->
incl BS LBa -> In (p, 48) BS -> incl AL BS -> (forall bs, In bs KBS -> incl bs BS) ->
rw_cells asegs m p (jhdr_cells JT_ARRAY 1 (fn_arr_to_json_string A4F) pb 0 0 ++ [C8 (wz a)]) ->
alist asegs A4F m AL a ps -> length ps = length kids -> length KBS = length kids -> akids asegs A4F m kids ps KBS ->
Z.of_nat (length ps) < 2^44 ->
forall (ASP d Fr : Z) (mX : word -> option byte) (mdX : config) (AX : ASA A4L HIx) (j0 j32 jG jf1 jf2 : list byte) (w8 fw0 fw1 fw2 : word) (ii : Z)
(x0 x1 x2 x3 x4 x5 x6 x7 : byte) (uaw keyw parw : word) (xra xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
Z.of_nat (length ps) - ii <= Z.of_nat fuel -> 0 <= ii < Z.of_nat (length ps) ->
(d = 0 \/ d = 16) -> ASP = bv_unsigned sp + -160 - d ->
HEAPAx AX LBa LM ((Fr, 0) :: FRS) B mX mdX ->
model_vm_only (cfg_model md) (cfg_model mdX) ->
heap_pres A4H (LBa ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mX ->
stk asegs mX lo ASP ->
rw_cells asegs mX (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mX ASP [CB 8 j0; C8 w8; C8 (wz 7547); C8 (wz (Z.of_nat (length ps))); CB 16 j32; C8 (wz Fr)] ->
rw_cells asegs mX (ASP + 56) [CB (Z.to_nat d) jG] ->
rw_cells asegs mX Fr [C8 fw0; C8 fw1; C8 fw2; CB 8 jf1; C8 (wz ii); CB 16 jf2] ->
rw_cells asegs mX (Fr / 8 + 2147450880) [C1 x0; C1 x1; C1 x2; C1 x3; C1 x4; C1 x5; C1 x6; C1 x7] ->
AJ5 A4L HIx AX T mdX
(MS (mkR xra (wz ASP) gp (wz 6434400) xt0 xt1 xt2 sp (wz ASP) xa0 (wz ii) xa2 xa3 xa4 xa5 xa6 xa7
(wz Fr) (wz EMIT_A) uaw (wz p) (wz 2147450880) keyw parw (wz (Fr + 32)) (wz (Fr / 8 + 2147450880)) (wz Fr) xt3 xt4 xt5 xt6)
F (wz 0xa42e4) fc None mX (seg_rom asegs)).
Proof.
induction fuel as [|fuel IHf]; intros kids IH; intros until KBS; intros LO LOS HT SPR SPA FRN K INC INp INAL INK HDR HAL L1 L2 KIDS LEN44;
intros until xt6; intros Hfuel Hii Hd0 HASP HPX VMX HPRX STX SAVE SCR GAP FFX FSHX.
{ exfalso. lia. }
unfold VIS_STK0, VIS_STK1 in LOS.
pose proof alloc_ceiling_range as ACR.
assert (DN : 0 <= odepth (Some (Sarr kids))) by (cbn [odepth]; apply sdepth_nonneg).
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HPX INF) as (_ & HFal & HF0 & HFc & HFimg & _ & _ & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HPX INF) as HFapp.
rewrite fr_size_0 in HFal, HFc, HFimg, HFapp. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp. unfold A_SB in HFapp.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 8 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HPX) as MI. change (hl_segs A4L) with asegs in MI.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HPX) as (SB1 & SB2 & _ & _).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2.

destruct (arr_now _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPX HPRX INC INp INAL HDR HAL) as (arr & size & HDR1 & Hp0 & Hp48 & Hp8 & SHp1 & SHpb & AL1 & ALB & SHa1 & SHr1 & Hsz0 & SHrb & Hlen).
destruct (akids_nth asegs A4F m kids ps KBS (Z.to_nat ii) (al_nth ps ii) KIDS (al_nth_in ps ii ltac:(lia))) as (k & bs & Hk & Hbs & JO).
pose proof (nth_error_In kids (Z.to_nat ii) Hk) as KIN.
pose proof (Qdgq_c1.odepth_kid_arr kids k KIN) as DK.
pose proof (Qdgq_c1.odepth_nonneg k) as DNk.
assert (BSI : incl bs LBa) by (intros b Hb; apply INC; eapply INK; [eapply nth_error_In; exact Hbs | exact Hb]).
stash SAVE. stash GAP.
a4l.
pose proof (wmono_refl asegs mX) as WM. pose proof (munch_refl [(lo, ASP + 56); (Fr, Fr + 56); (sh, sh + 8)] mX) as MU.
reenterA asegs A4L HIx asegs_wx HPX.
step. step.

eapply evt_cut.
{ eapply jo_array_get_idx_A with (lo := lo) (sbcell := 981752) (p := p) (rc := 1) (a := a) (arr := arr) (size := size) (ps := ps) (i := ii).
- unfold small_pre, A_GOT_SB, A_SB. rewrite ?unsigned_lit by lia.
split; [assumption|]. split; [eassumption|]. split; [lia|]. split; [exact LO|]. split; [eassumption|]. split; [eassumption|]. lia.
- exact HDR1.
- lia.
- lia.
- exact Hp8.
- exact SHp1.
- exact SHpb.
- exact AL1.
- lia.
- exact ALB.
- exact SHa1.
- exact SHr1.
- exact Hsz0.
- exact SHrb. }
intros ms' (w1 & w2 & w3 & w4 & m' & -> & MUg & WMg & MIg & STg).
rewrite ?unsigned_lit in MUg, STg by lia.
rewrite (proj2 (Z.ltb_lt ii (Z.of_nat (length ps)))) by lia.
lazymatch type of MUg with munch _ ?mq _ =>
transport_after_call asegs mq m' MUg WMg; try match goal with H : mem_inv asegs mq |- _ => clear H end; clear MUg WMg end.
replace (ret_pc (wz 0xa42ec)) with (wz 0xa42ec) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
clear AL1 SHp1 ALB Hsz0 SHrb SHpb Hlen.

do 6 step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ mX mc, WMc : wmono asegs mX mc, MIc : mem_inv asegs mc |- _ =>
pose proof (vk_HEAPA HIx _ _ _ _ _ _ _ _ lo (ASP + 56) _ HPX LO ltac:(lia) MUc WMc MIc) as HPc;
pose proof (vk_pres HIx _ _ _ _ _ _ _ _ lo (ASP + 56) _ HPX LO ltac:(lia) MUc WMc) as HPRc;
unstash SAVE; unstash GAP;
apply (rw_cells_transport asegs [(lo, ASP + 56); (Fr, Fr + 56); (sh, sh + 8)] _ mc) in SAVE; [| exact MUc | exact WMc | cbn [disjoint_from]; simpl_sizes; lia];
apply (rw_cells_transport asegs [(lo, ASP + 56); (Fr, Fr + 56); (sh, sh + 8)] _ mc) in GAP; [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; lia]
end end.
assert (HPR0c : heap_pres A4H (LBa ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m').
{ eapply heap_pres_trans; [exact HPRX |]. eapply heap_pres_weaken; [exact HPRc | lia | intros b Hb; exact Hb]. }
pose proof (jopt_now _ _ _ _ _ _ _ _ HPR0c BSI JO) as JOc.
evt_done5.
eapply (IH k KIN) with (LBa := LBa) (BS := bs) (LM := LM) (FRS := (Fr, 0) :: FRS) (B := B) (lo := lo) (p := al_nth ps ii);
[ exact HPc | exact BSI | rewrite unsigned_lit by lia; exact STg | exact LO
| rewrite unsigned_lit by lia; unfold VIS_STK0, VIS_STK1; lia
| rewrite unsigned_lit by lia; clear - SPA HASP Hd0; Z.div_mod_to_equations; lia
| rewrite unsigned_lit by lia; lia
| reflexivity | rewrite unsigned_lit by lia; reflexivity
| exact JOc | cbn [length]; lia | reflexivity | reflexivity | ].
intros msr mdr mr Ar RSr VMr STr HPRr HPr.
rewrite unsigned_lit in STr, HPRr by lia.
open_ret RSr.
apply (own_chunks_pres _ _ _ _ _ _ _ _ _ HPRr) in SAVE; [| left; lia].
apply (own_chunks_pres _ _ _ _ _ _ _ _ _ HPRr) in SCR; [| left; lia].
apply (own_chunks_pres _ _ _ _ _ _ _ _ _ HPRr) in GAP; [| left; cbn [cells_size csize Nat.add]; lia].
apply (own_chunks_pres _ _ _ _ _ _ _ _ _ HPRr) in FFX; [| right; left; cbn [cells_size csize Nat.add]; lia].
apply (own_chunks_pres _ _ _ _ _ _ _ _ _ HPRr) in FSHX; [| right; right; fold sh; cbn [cells_size csize Nat.add]; lia].
assert (HPR0r : heap_pres A4H (LBa ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mr).
{ eapply heap_pres_trans; [exact HPR0c |]. eapply heap_pres_weaken; [exact HPRr | lia |].
intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. rewrite app_assoc. apply in_or_app. destruct Hb as [H|H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H]. }
assert (VM0r : model_vm_only (cfg_model md) (cfg_model mdr)) by (eapply model_vm_only_trans; [exact VMX | exact VMr]).
clear HPc HPRc HPR0c JOc MIg STg MU WM SB1 SB2 VMr HPRr.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HPr) as MIr. change (hl_segs A4L) with asegs in MIr.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HPr) as (SB1 & SB2 & _ & _).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2.
stash SAVE. stash GAP.
a4l.
pose proof (wmono_refl asegs mr) as WM. pose proof (munch_refl [(lo, ASP + 56); (Fr, Fr + 56); (sh, sh + 8)] mr) as MU.
reenterA asegs A4L HIx asegs_wx HPr.
step. step. step. if_lit.
step. if_lit.

step. step. step. step. step.
destruct (Z_lt_dec (ii + 1) (Z.of_nat (length ps))) as [LT | GE].
- if_falsex.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ mr mc, WMc : wmono asegs mr mc, MIc : mem_inv asegs mc |- _ =>
pose proof (vk_HEAPA HIx _ _ _ _ _ _ _ _ lo (ASP + 56) _ HPr LO ltac:(lia) MUc WMc MIc) as HPc;
pose proof (vk_pres HIx _ _ _ _ _ _ _ _ lo (ASP + 56) _ HPr LO ltac:(lia) MUc WMc) as HPRc;
unstash SAVE; unstash GAP;
apply (rw_cells_transport asegs [(lo, ASP + 56); (Fr, Fr + 56); (sh, sh + 8)] _ mc) in SAVE; [| exact MUc | exact WMc | cbn [disjoint_from]; simpl_sizes; lia];
apply (rw_cells_transport asegs [(lo, ASP + 56); (Fr, Fr + 56); (sh, sh + 8)] _ mc) in GAP; [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; lia]
end end.
evt_done5.
eapply (IHf kids IH ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md T LBa BS LM FRS B lo p pb a AL ps KBS LO ltac:(unfold VIS_STK0, VIS_STK1; lia) HT SPR SPA FRN K INC INp INAL INK HDR HAL L1 L2 KIDS LEN44
ASP d Fr _ mdr Ar _ _ jG _ _ _ _ _ _ (ii + 1));
[ lia | lia | exact Hd0 | exact HASP | exact HPc | exact VM0r
| eapply heap_pres_trans; [exact HPR0r | eapply heap_pres_weaken; [exact HPRc | lia | intros b Hb; exact Hb]]
| eassumption | exact SAVE | eassumption | exact GAP | eassumption | eassumption ].
- if_truex. step. stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ mr mc, WMc : wmono asegs mr mc, MIc : mem_inv asegs mc |- _ =>
pose proof (vk_HEAPA HIx _ _ _ _ _ _ _ _ lo (ASP + 56) _ HPr LO ltac:(lia) MUc WMc MIc) as HPc;
pose proof (vk_pres HIx _ _ _ _ _ _ _ _ lo (ASP + 56) _ HPr LO ltac:(lia) MUc WMc) as HPRc;
unstash SAVE; unstash GAP;
apply (rw_cells_transport asegs [(lo, ASP + 56); (Fr, Fr + 56); (sh, sh + 8)] _ mc) in SAVE; [| exact MUc | exact WMc | cbn [disjoint_from]; simpl_sizes; lia];
apply (rw_cells_transport asegs [(lo, ASP + 56); (Fr, Fr + 56); (sh, sh + 8)] _ mc) in GAP; [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; lia]
end end.
evt_done5.
eapply (vis_tail HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md T LBa LM FRS B lo LO ltac:(unfold VIS_STK0; lia) HT SPR K ASP d Fr _ mdr Ar);
[ exact Hd0 | exact HASP | exact HPc | exact VM0r
| eapply heap_pres_trans; [exact HPR0r | eapply heap_pres_weaken; [exact HPRc | lia | intros b Hb; exact Hb]]
| eassumption | exact SAVE | eassumption | reflexivity | exact GAP | eassumption | eassumption ].
Qed.

Lemma vis_arr : forall kids, (forall k, In k kids -> VISx k) -> VISx (Some (Sarr kids)).
Proof.
intros kids IH. unfold VIS. intros until p. intros HP INC ST LO LOS SPA HT TP RA JO FRN A0 A4 K.
destruct JO as [Hp J]. subst a0 a4 tp.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (DN : 0 <= odepth (Some (Sarr kids))) by (cbn [odepth]; apply sdepth_nonneg).
destruct (sarr_open asegs A4F kids m BS p 1 J) as (pb & PBS & a & AL & ps & KBS & EBS & OPB & HDR & HAL & L1 & L2 & KIDS).
assert (INp : In (p, 48) BS) by (rewrite EBS; apply in_or_app; left; left; reflexivity).
assert (INAL : incl AL BS) by (intros b Hb; rewrite EBS; apply in_or_app; left; right; apply in_or_app; left; exact Hb).
assert (INK : forall bs, In bs KBS -> incl bs BS).
{ intros bs Hbs b Hb. rewrite EBS. apply in_or_app; left; right. apply in_or_app; right. apply in_concat. exists bs. split; assumption. }
eapply vis_pro; [exact HP | exact ST | exact LO | unfold VIS_STK0, VIS_STK1 in *; lia | exact SPA | exact HT | reflexivity | lia |].
intros ASP d Fr m1 md1 A1 jA jG jf xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 Hd0 HASP HP1 VM1 HPR1 ST1 SAVE SCRA GAP FF FSH.
pose proof LOS as LOS'. unfold VIS_STK0, VIS_STK1 in LOS.
pose proof alloc_ceiling_range as ACR.
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as (_ & HFal & HF0 & HFc & HFimg & _ & _ & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFapp.
rewrite fr_size_0 in HFal, HFc, HFimg, HFapp. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp. unfold A_SB in HFapp.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 8 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI. change (hl_segs A4L) with asegs in MI.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP1) as (SB1 & SB2 & _ & _).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2.
destruct (arr_now _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP1 HPR1 INC INp INAL HDR HAL) as (arr & size & HDR1 & Hp0 & Hp48 & Hp8 & SHp1 & SHpb & AL1 & ALB & SHa1 & SHr1 & Hsz0 & SHrb & Hlen).
assert (LEN44 : Z.of_nat (length ps) < 2^44) by (destruct ALB as (_ & _ & _ & Hr0 & _ & Hrh); clear - Hlen Hr0 Hrh ACR; lia).
pose proof (proj1 (rw_cells_app asegs m1 p _ _) HDR1) as [HDRh _].
stash SAVE. stash GAP.
a4l.
pose proof (wmono_refl asegs m1) as WM. pose proof (munch_refl [(lo, ASP + 56); (Fr, Fr + 56); (sh, sh + 8)] m1) as MU.
reenterA asegs A4L HIx asegs_wx HP1.
do 6 step. step.
unfold EMIT_A. replace (ret_pc (wz 0x925a4)) with (wz 0x925a4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
step. step.
replace (ret_pc (wz 0xa40c4)) with (wz 0xa40c4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
step. step. step. if_lit. step. step. if_lit. step. if_lit. step. step.

eapply evt_cut.
{ eapply jo_get_type_A with (lo := lo) (sbcell := 981752) (p := p) (ty := JT_ARRAY) (rc := 1).
- unfold small_pre, A_GOT_SB, A_SB. rewrite ?unsigned_lit by lia.
split; [assumption|]. split; [eassumption|]. split; [lia|]. split; [exact LO|]. split; [eassumption|]. split; [eassumption|]. lia.
- exact HDRh.
- lia.
- lia.
- exact Hp8.
- unfold JT_ARRAY; lia.
- apply (proj1 (ro_cells_app asegs m1 _ [C1 (Z_to_bv 8 0)] _) SHp1).
- unfold A_SB in *. lia. }
intros ms' (m' & (w & x & y & ->) & MUg & WMg & MIg & STg).
rewrite ?unsigned_lit in MUg, STg by lia.
lazymatch type of MUg with munch _ ?mq _ =>
transport_after_call asegs mq m' MUg WMg; try match goal with H : mem_inv asegs mq |- _ => clear H end; clear MUg WMg end.
replace (ret_pc (wz 0xa4104)) with (wz 0xa4104) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
clear AL1 SHp1 ALB Hsz0 SHrb Hlen SHpb arr size.
unfold JT_ARRAY.
step. step. step. if_lit. step. step. if_lit. step.
step. step. if_lit. step. step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m1 mc, WMc : wmono asegs m1 mc, MIc : mem_inv asegs mc |- _ =>
pose proof (vk_HEAPA HIx _ _ _ _ _ _ _ _ lo (ASP + 56) _ HP1 LO ltac:(lia) MUc WMc MIc) as HPc;
pose proof (vk_pres HIx _ _ _ _ _ _ _ _ lo (ASP + 56) _ HP1 LO ltac:(lia) MUc WMc) as HPRc end end.
assert (HPR0c : heap_pres A4H (LBa ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m0).
{ eapply heap_pres_trans; [exact HPR1 |]. eapply heap_pres_weaken; [exact HPRc | lia | intros b Hb; exact Hb]. }
destruct (arr_now _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPc HPR0c INC INp INAL HDR HAL) as (arr & size & HDR1 & _ & _ & _ & SHp1 & SHpb & AL1 & ALB & SHa1 & SHr1 & Hsz0 & SHrb & Hlen).
clear HPc HPRc HPR0c.
eapply evt_cut.
{ eapply jo_array_length_A with (lo := lo) (sbcell := 981752) (p := p) (rc := 1) (a := a) (arr := arr) (size := size) (ps := ps).
- unfold small_pre, A_GOT_SB, A_SB. rewrite ?unsigned_lit by lia.
split; [assumption|]. split; [eassumption|]. split; [lia|]. split; [exact LO|]. split; [eassumption|]. split; [eassumption|]. lia.
- exact HDR1.
- lia.
- lia.
- exact Hp8.
- exact SHp1.
- exact SHpb.
- exact AL1.
- exact ALB.
- exact SHa1. }
clear MIg STg. intros ms' (w1 & w2 & m'' & -> & MUg & WMg & MIg & STg).
rewrite ?unsigned_lit in MUg, STg by lia.
lazymatch type of MUg with munch _ ?mq _ =>
transport_after_call asegs mq m'' MUg WMg; try match goal with H : mem_inv asegs mq |- _ => clear H end; clear MUg WMg end.
replace (ret_pc (wz 0xa42a8)) with (wz 0xa42a8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
clear AL1 SHp1 ALB Hsz0 SHrb SHpb Hlen.

stepz. stepz. step. step.
destruct (Z.eq_dec (Z.of_nat (length ps)) 0) as [LZ | LNZ].
-
rewrite LZ in *. if_lit. step. stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m1 mc, WMc : wmono asegs m1 mc, MIc : mem_inv asegs mc |- _ =>
pose proof (vk_HEAPA HIx _ _ _ _ _ _ _ _ lo (ASP + 56) _ HP1 LO ltac:(lia) MUc WMc MIc) as HPc;
pose proof (vk_pres HIx _ _ _ _ _ _ _ _ lo (ASP + 56) _ HP1 LO ltac:(lia) MUc WMc) as HPRc;
unstash SAVE; unstash GAP;
apply (rw_cells_transport asegs [(lo, ASP + 56); (Fr, Fr + 56); (sh, sh + 8)] _ mc) in SAVE; [| exact MUc | exact WMc | cbn [disjoint_from]; simpl_sizes; lia];
apply (rw_cells_transport asegs [(lo, ASP + 56); (Fr, Fr + 56); (sh, sh + 8)] _ mc) in GAP; [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; lia]
end end.
evt_done5.
eapply (vis_tail HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md T LBa LM FRS B lo LO ltac:(unfold VIS_STK0; lia) HT SPR K ASP d Fr _ md1 A1);
[ exact Hd0 | exact HASP | exact HPc | exact VM1
| eapply heap_pres_trans; [exact HPR1 | eapply heap_pres_weaken; [exact HPRc | lia | intros b Hb; exact Hb]]
| eassumption | exact SAVE | eassumption | reflexivity | exact GAP | eassumption | eassumption ].
- if_falsex. step. step. step. stepz. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m1 mc, WMc : wmono asegs m1 mc, MIc : mem_inv asegs mc |- _ =>
pose proof (vk_HEAPA HIx _ _ _ _ _ _ _ _ lo (ASP + 56) _ HP1 LO ltac:(lia) MUc WMc MIc) as HPc;
pose proof (vk_pres HIx _ _ _ _ _ _ _ _ lo (ASP + 56) _ HP1 LO ltac:(lia) MUc WMc) as HPRc;
unstash SAVE; unstash GAP;
apply (rw_cells_transport asegs [(lo, ASP + 56); (Fr, Fr + 56); (sh, sh + 8)] _ mc) in SAVE; [| exact MUc | exact WMc | cbn [disjoint_from]; simpl_sizes; lia];
apply (rw_cells_transport asegs [(lo, ASP + 56); (Fr, Fr + 56); (sh, sh + 8)] _ mc) in GAP; [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; lia]
end end.
evt_done5.
eapply (arr_loop (S (length ps)) kids IH ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md T LBa BS LM FRS B lo p pb a AL ps KBS LO LOS' HT SPR SPA FRN K INC INp INAL INK HDR HAL L1 L2 KIDS LEN44
ASP d Fr _ md1 A1 _ _ jG _ _ _ _ _ _ 0);
[ lia | lia | exact Hd0 | exact HASP | exact HPc | exact VM1
| eapply heap_pres_trans; [exact HPR1 | eapply heap_pres_weaken; [exact HPRc | lia | intros b Hb; exact Hb]]
| eassumption | exact SAVE | eassumption | exact GAP | eassumption | eassumption ].
Qed.

Lemma gran4_now : forall A LBa LM FRS' B mc mdc a k e,
HEAPAx A LBa LM FRS' B mc mdc -> In (a, k) LBa -> a <= e -> e + 32 <= a + k -> e mod 8 = 0 ->
ro_cells asegs mc (e / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof.
intros A LBa LM FRS' B mc mdc a k e HP Hin Hlo Hhi He8.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP ltac:(apply in_or_app; left; exact Hin)) as (_ & Hal & _).
assert (E : forall i, 0 <= i -> e / 8 + 2147450880 + i = a / 8 + 2147450880 + ((e - a) / 8 + i)) by (intros i Hi; clear - Hal He8 Hlo; Z.div_mod_to_equations; lia).
assert (G : forall i, 0 <= i <= 3 -> ro_cells asegs mc (e / 8 + 2147450880 + i) [C1 (Z_to_bv 8 0)]).
{ intros i Hi. rewrite (E i) by lia. eapply (blk_gran0A HIx _ _ _ _ _ _ _ a k _ HP Hin); [clear - Hlo Hi; Z.div_mod_to_equations; lia | clear - Hal He8 Hlo Hhi Hi; Z.div_mod_to_equations; lia]. }
pose proof (G 0 ltac:(lia)) as G0. pose proof (G 1 ltac:(lia)) as G1. pose proof (G 2 ltac:(lia)) as G2. pose proof (G 3 ltac:(lia)) as G3.
rewrite Z.add_0_r in G0.
change [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] with ([C1 (Z_to_bv 8 0)] ++ [C1 (Z_to_bv 8 0)] ++ [C1 (Z_to_bv 8 0)] ++ [C1 (Z_to_bv 8 0)]).
apply ro_cells_app. split; [exact G0|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 1) with 1.
apply ro_cells_app. split; [exact G1|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 1) with 1.
apply ro_cells_app. split; [replace (e / 8 + 2147450880 + 1 + 1) with (e / 8 + 2147450880 + 2) by lia; exact G2|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 1) with 1.
replace (e / 8 + 2147450880 + 1 + 1 + 1) with (e / 8 + 2147450880 + 3) by lia. exact G3.
Qed.

Lemma obj_now : forall A LBa LM FRS' B mc mdc R SP0 m kids BS p pb0 PBS t TBS es KBS,
HEAPAx A LBa LM FRS' B mc mdc -> heap_pres A4H (LBa ++ R) SP0 m mc -> incl BS LBa ->
obj_view asegs A4F kids m BS p 1 pb0 PBS t TBS es KBS ->
obj_view asegs A4F kids mc BS p 1 pb0 PBS t TBS es KBS /\
0 < p /\ p + 48 <= alloc_ceiling /\ p mod 8 = 0 /\
ro_cells asegs mc (p / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] /\
p / 8 + A_SB + 6 <= alloc_ceiling /\
0 < t /\ t mod 8 = 0 /\ t + 56 <= alloc_ceiling /\
ro_cells asegs mc (t / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof.
intros A LBa LM FRS' B mc mdc R SP0 m kids BS p pb0 PBS t TBS es KBS HP HPR INC OV.
pose proof alloc_ceiling_range as ACR.
assert (AG : agree_on asegs BS m mc).
{ eapply (agree_of_heap_pres asegs A4H); [exact HPR | reflexivity |]. intros b Hb. apply in_or_app; left. apply INC; exact Hb. }
pose proof (obj_view_agree asegs A4F kids m mc BS p 1 pb0 PBS t TBS es KBS OV AG) as OVc.
destruct (obj_view_tbl asegs A4F kids m BS p 1 pb0 PBS t TBS es KBS OV) as [_ TINB].
assert (INp : In (p, 48) BS) by (destruct OV as (EBS & _); rewrite EBS; apply in_or_app; left; left; reflexivity).
assert (INpA : In (p, 48) LBa) by (apply INC; exact INp).
assert (INtA : In (t, 56) LBa) by (apply INC; exact TINB).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p 48 HP ltac:(apply in_or_app; left; exact INpA)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ t 56 HP ltac:(apply in_or_app; left; exact INtA)) as (_ & Htal & Htlo & Hthi & _).
split; [exact OVc|]. split; [exact Hplo|]. split; [exact Hphi|]. split; [clear - Hpal; Z.div_mod_to_equations; lia|].
split.
{ pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ p 48 HP INpA) as SH. unfold shad in SH. apply shadow_ro_cells in SH.
cbn [hl_sb hl_segs hla_base A4L A4H] in SH. exact SH. }
split; [unfold A_SB; clear - Hphi ACR Hplo; Z.div_mod_to_equations; lia|].
split; [exact Htlo|]. split; [clear - Htal; Z.div_mod_to_equations; lia|]. split; [exact Hthi|].
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ t 56 HP INtA) as SH. unfold shad in SH. apply shadow_ro_cells in SH.
cbn [hl_sb hl_segs hla_base A4L A4H] in SH. exact SH.
Qed.

Lemma ent_now : forall A LBa LM FRS' B mc mdc kids BS p pb0 PBS t TBS es KBS j e,
HEAPAx A LBa LM FRS' B mc mdc -> incl BS LBa ->
obj_view asegs A4F kids mc BS p 1 pb0 PBS t TBS es KBS -> nth_error es j = Some e ->
0 < oe_a e /\ oe_a e mod 8 = 0 /\ oe_a e + 32 <= alloc_ceiling /\
ro_cells asegs mc (oe_a e / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] /\
(exists pad : word, rw_cells asegs mc (oe_a e) [C8 (wz (oe_k e)); C4 (wz 0); C4 pad; C8 (wz (oe_v e)); C8 (wz (ohd (skipn (S j) es)))]) /\
exists k bs, nth_error kids j = Some k /\ nth_error KBS j = Some bs /\ incl bs BS /\ joptA k mc bs (oe_v e).
Proof.
intros A LBa LM FRS' B mc mdc kids BS p pb0 PBS t TBS es KBS j e HP INC OV He.
destruct (obj_view_entry asegs A4F kids mc BS p 1 pb0 PBS t TBS es KBS j e OV He) as (EA0 & EA8 & (ba & bk & Hin & Hlo & Hhi) & ENT & k & bs & Hk & Hbs & KOK).
assert (EBS : BS = ((p, 48) :: TBS ++ concat KBS) ++ PBS) by (destruct OV as (E & _); exact E).
assert (INbA : In (ba, bk) LBa) by (apply INC; rewrite EBS; apply in_or_app; left; right; apply in_or_app; left; exact Hin).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ ba bk HP ltac:(apply in_or_app; left; exact INbA)) as (_ & _ & _ & Hbhi & _).
split; [exact EA0|]. split; [exact EA8|]. split; [lia|].
split; [eapply (gran4_now _ _ _ _ _ _ _ ba bk (oe_a e) HP INbA); [exact Hlo | exact Hhi | exact EA8] |].
split; [exact ENT|].
exists k, bs. split; [exact Hk|]. split; [exact Hbs|]. split.
- intros b Hb. rewrite EBS. apply in_or_app; left; right. apply in_or_app; right. apply in_concat. exists bs. split; [eapply nth_error_In; exact Hbs | exact Hb].
- destruct k; exact KOK.
Qed.

Lemma obj_loop : forall (fuel : nat) (kids : list (option jshape)),
(forall k, In k kids -> VISx k) ->
forall (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(LBa BS LM : list blk) (FRS : list frame) (B : bud) (lo p pb0 t : Z) (PBS TBS : list blk) (es : list oent) (KBS : list (list blk)),
alloc_ceiling <= lo -> lo <= bv_unsigned sp - (VIS_STK0 + VIS_STK1 * odepth (Some (Sobj kids))) -> bv_unsigned sp <= hiA_top A4L HIx ->
0 <= bv_unsigned sp < 2^64 -> bv_unsigned sp mod 16 = 0 ->
Z.of_nat (length FRS) + (1 + odepth (Some (Sobj kids))) < 4096 ->
(forall ms' md' m' (A' : ASA A4L HIx),
ret_state A4H ra sp gp (wz 6434400) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (wz 0) m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (LBa ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' ->
HEAPAx A' LBa LM FRS B m' md' ->
AJ5 A4L HIx A' T md' ms') ->
incl BS LBa -> obj_view asegs A4F kids m BS p 1 pb0 PBS t TBS es KBS ->
forall (ASP d Fr : Z) (mX : word -> option byte) (mdX : config) (AX : ASA A4L HIx) (j0 j16 j32 jG jf : list byte) (w8 w24 fw0 fw1 fw2 : word)
(x0 x1 x2 x3 x4 x5 x6 x7 : byte) (j : nat) (e : oent) (uaw keyw parw : word) (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
Z.of_nat (length es) - Z.of_nat j <= Z.of_nat fuel -> nth_error es j = Some e ->
(d = 0 \/ d = 16) -> ASP = bv_unsigned sp + -160 - d ->
HEAPAx AX LBa LM ((Fr, 0) :: FRS) B mX mdX ->
model_vm_only (cfg_model md) (cfg_model mdX) ->
heap_pres A4H (LBa ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mX ->
stk asegs mX lo ASP ->
rw_cells asegs mX (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mX ASP [CB 8 j0; C8 w8; CB 8 j16; C8 w24; CB 16 j32; C8 (wz Fr)] ->
rw_cells asegs mX (ASP + 56) [CB (Z.to_nat d) jG] ->
rw_cells asegs mX Fr [C8 fw0; C8 fw1; C8 fw2; CB 32 jf] ->
rw_cells asegs mX (Fr / 8 + 2147450880) [C1 x0; C1 x1; C1 x2; C1 x3; C1 x4; C1 x5; C1 x6; C1 x7] ->
AJ5 A4L HIx AX T mdX
(MS (mkR xra (wz ASP) gp (wz 6434400) xt0 xt1 xt2 sp (wz ASP) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
(wz Fr) (wz EMIT_A) uaw (wz p) (wz 2147450880) keyw parw (wz (oe_a e)) (wz (Fr / 8 + 2147450880)) (wz Fr) xt3 xt4 xt5 xt6)
F (wz 0xa4214) fc None mX (seg_rom asegs)).
Proof.
induction fuel as [|fuel IHf]; intros kids IH; intros until KBS; intros LO LOS HT SPR SPA FRN K INC OV;
intros until xt6; intros Hfuel He Hd0 HASP HPX VMX HPRX STX SAVE SCR GAP FFX FSHX.
{ exfalso. assert (L : (j < length es)%nat) by (apply nth_error_Some; congruence). lia. }
unfold VIS_STK0, VIS_STK1 in LOS.
pose proof alloc_ceiling_range as ACR.
assert (DN : 0 <= odepth (Some (Sobj kids))) by (cbn [odepth]; apply sdepth_nonneg).
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HPX INF) as (_ & HFal & HF0 & HFc & HFimg & _ & _ & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HPX INF) as HFapp.
rewrite fr_size_0 in HFal, HFc, HFimg, HFapp. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp. unfold A_SB in HFapp.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 8 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HPX) as MI. change (hl_segs A4L) with asegs in MI.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HPX) as (SB1 & SB2 & _ & _).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2.

destruct (obj_now _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPX HPRX INC OV) as (OVX & _).
destruct (ent_now _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPX INC OVX He) as (E0 & E8 & E32 & SHe & (pad & ENT) & k & bs & Hk & Hbs & BSI0 & JOX).
pose proof (nth_error_In kids j Hk) as KIN.
pose proof (Qdgq_c1.odepth_kid_obj kids k KIN) as DK.
pose proof (Qdgq_c1.odepth_nonneg k) as DNk.
assert (BSI : incl bs LBa) by (intros b Hb; apply INC, BSI0; exact Hb).
stash SAVE. stash GAP.
a4l.
pose proof (wmono_refl asegs mX) as WM. pose proof (munch_refl [(lo, ASP + 56); (Fr, Fr + 56); (sh, sh + 8)] mX) as MU.
reenterA asegs A4L HIx asegs_wx HPX.
asan_chk0.
step. asan_chkA.
step. asan_chkA.
step. step. step.
do 5 step. step.
unstash SAVE. unstash GAP.
evt_done5.
eapply (IH k KIN) with (LBa := LBa) (BS := bs) (LM := LM) (FRS := (Fr, 0) :: FRS) (B := B) (lo := lo) (p := oe_v e);
[ exact HPX | exact BSI | rewrite unsigned_lit by lia; exact STX | exact LO
| rewrite unsigned_lit by lia; unfold VIS_STK0, VIS_STK1; lia
| rewrite unsigned_lit by lia; clear - SPA HASP Hd0; Z.div_mod_to_equations; lia
| rewrite unsigned_lit by lia; lia
| reflexivity | rewrite unsigned_lit by lia; reflexivity
| exact JOX | cbn [length]; lia | reflexivity | reflexivity | ].
intros msr mdr mr Ar RSr VMr STr HPRr HPr.
rewrite unsigned_lit in STr, HPRr by lia.
open_ret RSr.
apply (own_chunks_pres _ _ _ _ _ _ _ _ _ HPRr) in SAVE; [| left; lia].
apply (own_chunks_pres _ _ _ _ _ _ _ _ _ HPRr) in SCR; [| left; lia].
apply (own_chunks_pres _ _ _ _ _ _ _ _ _ HPRr) in GAP; [| left; cbn [cells_size csize Nat.add]; lia].
apply (own_chunks_pres _ _ _ _ _ _ _ _ _ HPRr) in FFX; [| right; left; cbn [cells_size csize Nat.add]; lia].
apply (own_chunks_pres _ _ _ _ _ _ _ _ _ HPRr) in FSHX; [| right; right; fold sh; cbn [cells_size csize Nat.add]; lia].
assert (HPR0r : heap_pres A4H (LBa ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mr).
{ eapply heap_pres_trans; [exact HPRX |]. eapply heap_pres_weaken; [exact HPRr | lia |].
intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. rewrite app_assoc. apply in_or_app. destruct Hb as [H|H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H]. }
assert (VM0r : model_vm_only (cfg_model md) (cfg_model mdr)) by (eapply model_vm_only_trans; [exact VMX | exact VMr]).
clear MI SB1 SB2 OVX SHe ENT JOX WM MU VMr HPRr.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HPr) as MIr. change (hl_segs A4L) with asegs in MIr.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HPr) as (SB1 & SB2 & _ & _).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2.
destruct (obj_now _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPr HPR0r INC OV) as (OVr & _).
rewrite (ohd_skipn es (S j)).
a4l.
pose proof (wmono_refl asegs mr) as WM. pose proof (munch_refl [(lo, ASP + 56); (Fr, Fr + 56); (sh, sh + 8)] mr) as MU.
destruct (nth_error es (S j)) as [e'|] eqn:He'.
- destruct (ent_now _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPr INC OVr He') as (E0' & E8' & E32' & _).
clear OVr.
reenterA asegs A4L HIx asegs_wx HPr.
step. step. step. if_lit. step. if_lit. step. if_falsex.
evt_done5.
eapply (IHf kids IH ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md T LBa BS LM FRS B lo p pb0 t PBS TBS es KBS LO ltac:(unfold VIS_STK0, VIS_STK1; lia) HT SPR SPA FRN K INC OV
ASP d Fr _ mdr Ar _ _ _ jG _ _ _ _ _ _ _ _ _ _ _ _ _ _ (S j) e');
[ lia | exact He' | exact Hd0 | exact HASP | exact HPr | exact VM0r | exact HPR0r
| eassumption | exact SAVE | eassumption | exact GAP | eassumption | eassumption ].
- clear OVr.
reenterA asegs A4L HIx asegs_wx HPr.
step. step. step. if_lit. step. if_lit. step. if_lit.
evt_done5.
eapply (vis_tail HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md T LBa LM FRS B lo LO ltac:(unfold VIS_STK0; lia) HT SPR K ASP d Fr _ mdr Ar);
[ exact Hd0 | exact HASP | exact HPr | exact VM0r | exact HPR0r
| eassumption | exact SAVE | eassumption | reflexivity | exact GAP | eassumption | eassumption ].
Qed.

Lemma vis_obj : forall kids, (forall k, In k kids -> VISx k) -> VISx (Some (Sobj kids)).
Proof.
intros kids IH. unfold VIS. intros until p. intros HP INC ST LO LOS SPA HT TP RA JO FRN A0 A4 K.
destruct JO as [Hp J]. subst a0 a4 tp.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (DN : 0 <= odepth (Some (Sobj kids))) by (cbn [odepth]; apply sdepth_nonneg).
assert (POS : forall a n, In (a, n) BS -> 0 < a /\ a mod 16 = 0).
{ intros b n Hb. pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ b n HP ltac:(apply in_or_app; left; apply INC; exact Hb)) as (_ & Hal & Hlo & _). split; assumption. }
destruct (jval_obj_view asegs A4F kids m BS p 1 J POS) as (pb0 & PBS & t & TBS & es & KBS & OV).
eapply vis_pro; [exact HP | exact ST | exact LO | unfold VIS_STK0, VIS_STK1 in *; lia | exact SPA | exact HT | reflexivity | lia |].
intros ASP d Fr m1 md1 A1 jA jG jf xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 Hd0 HASP HP1 VM1 HPR1 ST1 SAVE SCRA GAP FF FSH.
pose proof LOS as LOS'. unfold VIS_STK0, VIS_STK1 in LOS.
pose proof alloc_ceiling_range as ACR.
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as (_ & HFal & HF0 & HFc & HFimg & _ & _ & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFapp.
rewrite fr_size_0 in HFal, HFc, HFimg, HFapp. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp. unfold A_SB in HFapp.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 8 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI. change (hl_segs A4L) with asegs in MI.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP1) as (SB1 & SB2 & _ & _).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2.
destruct (obj_now _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP1 HPR1 INC OV) as (OV1 & Hp0 & Hp48 & Hp8 & SHp1 & SHpb & Ht0 & Ht8 & Ht56 & SHt1).
pose proof OV1 as (_ & _ & HDR1 & _).
pose proof (proj1 (rw_cells_app asegs m1 p _ _) HDR1) as [HDRh _].
stash SAVE. stash GAP.
a4l.
pose proof (wmono_refl asegs m1) as WM. pose proof (munch_refl [(lo, ASP + 56); (Fr, Fr + 56); (sh, sh + 8)] m1) as MU.
reenterA asegs A4L HIx asegs_wx HP1.
do 6 step. step.
unfold EMIT_A. replace (ret_pc (wz 0x925a4)) with (wz 0x925a4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
step. step.
replace (ret_pc (wz 0xa40c4)) with (wz 0xa40c4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
step. step. step. if_lit. step. step. if_lit. step. if_lit. step. step.

eapply evt_cut.
{ eapply jo_get_type_A with (lo := lo) (sbcell := 981752) (p := p) (ty := JT_OBJECT) (rc := 1).
- unfold small_pre, A_GOT_SB, A_SB. rewrite ?unsigned_lit by lia.
split; [assumption|]. split; [eassumption|]. split; [lia|]. split; [exact LO|]. split; [eassumption|]. split; [eassumption|]. lia.
- exact HDRh.
- lia.
- lia.
- exact Hp8.
- unfold JT_OBJECT; lia.
- apply (proj1 (ro_cells_app asegs m1 _ [C1 (Z_to_bv 8 0)] _) SHp1).
- unfold A_SB in *. lia. }
intros ms' (m' & (w & x & y & ->) & MUg & WMg & MIg & STg).
rewrite ?unsigned_lit in MUg, STg by lia.
lazymatch type of MUg with munch _ ?mq _ =>
transport_after_call asegs mq m' MUg WMg; try match goal with H : mem_inv asegs mq |- _ => clear H end; clear MUg WMg end.
replace (ret_pc (wz 0xa4104)) with (wz 0xa4104) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
clear OV1 SHp1 SHt1.
unfold JT_OBJECT.
step. step. step. if_lit. step. step. if_lit. step.
step. step. if_lit. step. step. if_lit. step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m1 mc, WMc : wmono asegs m1 mc, MIc : mem_inv asegs mc |- _ =>
pose proof (vk_HEAPA HIx _ _ _ _ _ _ _ _ lo (ASP + 56) _ HP1 LO ltac:(lia) MUc WMc MIc) as HPc;
pose proof (vk_pres HIx _ _ _ _ _ _ _ _ lo (ASP + 56) _ HP1 LO ltac:(lia) MUc WMc) as HPRc end end.
assert (HPR0c : heap_pres A4H (LBa ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m0).
{ eapply heap_pres_trans; [exact HPR1 |]. eapply heap_pres_weaken; [exact HPRc | lia | intros b Hb; exact Hb]. }
destruct (obj_now _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPc HPR0c INC OV) as (OVc & _ & _ & _ & SHpc & _ & _ & _ & _ & SHtc).
pose proof OVc as (_ & _ & HDRc & _).
clear HPc HPRc HPR0c.
eapply evt_cut.
{ eapply jo_get_object_A with (lo := lo) (sbcell := 981752) (p := p) (rc := 1) (t := t).
- unfold small_pre, A_GOT_SB, A_SB. rewrite ?unsigned_lit by lia.
split; [assumption|]. split; [eassumption|]. split; [lia|]. split; [exact LO|]. split; [eassumption|]. split; [eassumption|]. lia.
- exact HDRc.
- lia.
- lia.
- exact Hp8.
- exact SHpc.
- exact SHpb. }
clear MIg STg. intros ms' (m'' & (w1 & x1 & y1 & ->) & MUg & WMg & MIg & STg).
rewrite ?unsigned_lit in MUg, STg by lia.
lazymatch type of MUg with munch _ ?mq _ =>
transport_after_call asegs mq m'' MUg WMg; try match goal with H : mem_inv asegs mq |- _ => clear H end; clear MUg WMg end.
replace (ret_pc (wz 0xa41e0)) with (wz 0xa41e0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
clear OVc.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m1 mc, WMc : wmono asegs m1 mc, MIc : mem_inv asegs mc |- _ =>
pose proof (vk_HEAPA HIx _ _ _ _ _ _ _ _ lo (ASP + 56) _ HP1 LO ltac:(lia) MUc WMc MIc) as HPc;
pose proof (vk_pres HIx _ _ _ _ _ _ _ _ lo (ASP + 56) _ HP1 LO ltac:(lia) MUc WMc) as HPRc end end.
assert (HPR0c : heap_pres A4H (LBa ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m'').
{ eapply heap_pres_trans; [exact HPR1 |]. eapply heap_pres_weaken; [exact HPRc | lia | intros b Hb; exact Hb]. }
destruct (obj_now _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPc HPR0c INC OV) as (OVc & _ & _ & _ & _ & _ & _ & _ & _ & SHtc).
pose proof (obj_view_head asegs A4F kids m'' BS p 1 pb0 PBS t TBS es KBS OVc) as HEAD.
unfold A_SB in SHtc.
step.
asan_chkA.
step.
assert (OHD : ohd es = match nth_error es 0%nat with Some x => oe_a x | None => 0 end) by (destruct es; reflexivity).
rewrite OHD in *. clear OHD.
step.
destruct (nth_error es 0%nat) as [e0|] eqn:He0.
- destruct (ent_now _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPc INC OVc He0) as (E0 & E8 & E32 & _).
clear HPc HPRc HPR0c OVc.
if_falsex. step. step. stepz. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m1 mc, WMc : wmono asegs m1 mc, MIc : mem_inv asegs mc |- _ =>
pose proof (vk_HEAPA HIx _ _ _ _ _ _ _ _ lo (ASP + 56) _ HP1 LO ltac:(lia) MUc WMc MIc) as HPd;
pose proof (vk_pres HIx _ _ _ _ _ _ _ _ lo (ASP + 56) _ HP1 LO ltac:(lia) MUc WMc) as HPRd;
unstash SAVE; unstash GAP;
apply (rw_cells_transport asegs [(lo, ASP + 56); (Fr, Fr + 56); (sh, sh + 8)] _ mc) in SAVE; [| exact MUc | exact WMc | cbn [disjoint_from]; simpl_sizes; lia];
apply (rw_cells_transport asegs [(lo, ASP + 56); (Fr, Fr + 56); (sh, sh + 8)] _ mc) in GAP; [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; lia]
end end.
evt_done5.
eapply (obj_loop (S (length es)) kids IH ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md T LBa BS LM FRS B lo p pb0 t PBS TBS es KBS LO LOS' HT SPR SPA FRN K INC OV
ASP d Fr _ md1 A1 _ _ _ jG _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0%nat e0);
[ lia | exact He0 | exact Hd0 | exact HASP | exact HPd | exact VM1
| eapply heap_pres_trans; [exact HPR1 | eapply heap_pres_weaken; [exact HPRd | lia | intros b Hb; exact Hb]]
| eassumption | exact SAVE | eassumption | exact GAP | eassumption | eassumption ].
- clear HPc HPRc HPR0c OVc.
if_lit.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m1 mc, WMc : wmono asegs m1 mc, MIc : mem_inv asegs mc |- _ =>
pose proof (vk_HEAPA HIx _ _ _ _ _ _ _ _ lo (ASP + 56) _ HP1 LO ltac:(lia) MUc WMc MIc) as HPd;
pose proof (vk_pres HIx _ _ _ _ _ _ _ _ lo (ASP + 56) _ HP1 LO ltac:(lia) MUc WMc) as HPRd;
unstash SAVE; unstash GAP;
apply (rw_cells_transport asegs [(lo, ASP + 56); (Fr, Fr + 56); (sh, sh + 8)] _ mc) in SAVE; [| exact MUc | exact WMc | cbn [disjoint_from]; simpl_sizes; lia];
apply (rw_cells_transport asegs [(lo, ASP + 56); (Fr, Fr + 56); (sh, sh + 8)] _ mc) in GAP; [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; lia]
end end.
evt_done5.
eapply (vis_tail HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md T LBa LM FRS B lo LO ltac:(unfold VIS_STK0; lia) HT SPR K ASP d Fr _ md1 A1);
[ exact Hd0 | exact HASP | exact HPd | exact VM1
| eapply heap_pres_trans; [exact HPR1 | eapply heap_pres_weaken; [exact HPRd | lia | intros b Hb; exact Hb]]
| eassumption | exact SAVE | eassumption | reflexivity | exact GAP | eassumption | eassumption ].
Qed.

Theorem vis_all : forall s, VISx s.
Proof.
intros [s|]; [| apply vis_null].
induction s as [|u| |h|kids IHk|kids IHk] using jshape_ind2.
- apply vis_scalar; cbn; unfold JT_BOOLEAN, JT_OBJECT, JT_ARRAY; lia.
- apply vis_scalar; cbn; unfold JT_DOUBLE, JT_OBJECT, JT_ARRAY; lia.
- apply vis_scalar; cbn; unfold JT_INT, JT_OBJECT, JT_ARRAY; lia.
- apply vis_scalar; cbn; unfold JT_STRING, JT_OBJECT, JT_ARRAY; lia.
- apply vis_obj. intros [s'|] Hin; [apply IHk; exact Hin | apply vis_null].
- apply vis_arr. intros [s'|] Hin; [apply IHk; exact Hin | apply vis_null].
Qed.

Theorem json_c_visit_A : jo_visit_A_stmt HIx JCVISIT_A EMIT_A (16 + 176 + 4096) 176.
Proof.
unfold jo_visit_A_stmt. intros until errv. intros (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA) JO FRN A0 A1 A2 A3 K.
subst a0 a1 a2 a3 tp. word_range sp SPR. unfold JCVISIT_A, A_TP in *.
pose proof (Qdgq_c1.odepth_nonneg s) as DN.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof alloc_ceiling_range as ACR.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp + -16, bv_unsigned sp)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 16%nat ST.
do 7 step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
assert (HP1 : HEAPAx A (BS ++ LB) LM FRS B m1 md) by (match goal with MIc : mem_inv asegs m1 |- _ => heap_nowA A4L HIx HP MU WM MIc end).
assert (HPR1 : heap_pres A4H ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m1).
{ eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; exact Hb | clia | solve_clientWA A4L HIx HP]. }
assert (JO1 : joptA s m1 BS p) by (eapply (jopt_now _ _ _ _ _ _ _ _ HPR1); [apply incl_appl, incl_refl | exact JO]).
evt_done5.
eapply (vis_all s) with (LBa := BS ++ LB) (BS := BS) (LM := LM) (FRS := FRS) (B := B) (lo := lo) (p := p);
[ exact HP1 | apply incl_appl, incl_refl | rewrite unsigned_lit by lia; eassumption | exact LO
| rewrite unsigned_lit by lia; unfold VIS_STK0, VIS_STK1; lia
| rewrite unsigned_lit by lia; clear - SPA; Z.div_mod_to_equations; lia
| rewrite unsigned_lit by lia; lia
| reflexivity | rewrite unsigned_lit by lia; reflexivity
| exact JO1 | exact FRN | reflexivity | reflexivity | ].
intros msr mdr mr Ar RSr VMr STr HPRr HPr.
rewrite unsigned_lit in STr, HPRr by lia.
open_ret RSr.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPRr) in FR; [| left; lia]. change (hl_segs A4H) with asegs in FR.
assert (HPR0r : heap_pres A4H ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mr).
{ eapply heap_pres_trans; [exact HPR1 |]. eapply heap_pres_weaken; [exact HPRr | lia | intros b Hb; exact Hb]. }
pose proof (jopt_now _ _ _ _ _ _ _ _ HPR0r ltac:(apply incl_appl, incl_refl) JO) as JOr.
clear HP1 HPR1 JO1 MU WM HPRr.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HPr) as MIr. cbn [hl_segs hla_base A4L A4H] in MIr.
pose proof (wmono_refl asegs mr) as WM. pose proof (munch_refl [(bv_unsigned sp + -16, bv_unsigned sp)] mr) as MU.
reenterA asegs A4L HIx asegs_wx HPr.
step. step. step. step. step. if_lit. step. if_lit.
step. step. step.
clear ST. release_frame FR STr (bv_unsigned sp).
evt_done5.
eapply (K _ mdr mr 0 Ar); [| reflexivity | exact JOr | exact HPr].
split; [tw_ret|]. split; [exact VMr|]. split; [exact STr|]. split.
- eapply heap_pres_weaken; [exact HPR0r | lia |]. intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; apply in_or_app; right; exact Hb | apply in_or_app; right; exact Hb].
- unfold A_ERRNO, A_TP. exact (heapA_errno A4L HIx _ _ _ _ _ _ _ HPr).
Qed.
End MJoVisit2.
End RC__1.
End Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI QDwa QSHS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 QJjn QRUw.Mq0 QkMG. Import QG8z QLbz Qdyh.Mq0. Import Q8tj.
Import QbFI. Import Qhd4. Import Qwm6.Mq4 QsKa.Mqd Qiiq QDwa Qoif.Mq4 Q4v2 QSHS QrQv.Mq4 QEUF.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma lf_thr_lower : forall S, In S lf_sizes -> 2560 * S <= 3904 * lf_thr S + 3904.
Proof.
intros S H. assert (C : forallb (fun S => 2560 * S <=? 3904 * lf_thr S + 3904) lf_sizes = true) by (vm_compute; reflexivity).
rewrite forallb_forall in C. specialize (C S H). apply Z.leb_le in C. exact C.
Qed.
Lemma lf_thr_nonneg : forall S, In S lf_sizes -> 0 <= lf_thr S.
Proof.
intros S H. assert (C : forallb (fun S => 0 <=? lf_thr S) lf_sizes = true) by (vm_compute; reflexivity).
rewrite forallb_forall in C. specialize (C S H). apply Z.leb_le in C. exact C.
Qed.
Lemma lf_sizes_double : forall S, In S lf_sizes -> S <= 2^29 -> In (2 * S) lf_sizes.
Proof.
intros S H Hle. assert (C : forallb (fun S => if S <=? 2^29 then existsb (Z.eqb (2 * S)) lf_sizes else true) lf_sizes = true) by (vm_compute; reflexivity).
rewrite forallb_forall in C. specialize (C S H). rewrite (proj2 (Z.leb_le S (2^29)) Hle) in C.
apply existsb_exists in C as (x & Hx & E). apply Z.eqb_eq in E. rewrite E. exact Hx.
Qed.

Lemma lh_ns_small : forall S, S <= 2^29 -> lh_ns S = 2 * S.
Proof. intros S H. unfold lh_ns. rewrite (proj2 (Z.leb_le S (2^29)) H). reflexivity. Qed.

Lemma BOK_obj_add : forall pf pa ts B n l kids klen,
BOK pf pa ts B (S (Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192) + n)) -> 0 <= pa_bslack pa ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_cs l = Some (Sobj kids) -> lvl_closed l = false ->
0 <= klen <= Z.max 0 (pf_len pf) -> obj_capA (tl_cbs l) <= 2^29 ->
oadd_costB klen (obj_capA (tl_cbs l)) (Z.of_nat (length kids)) <= bB B /\ 512 * Z.of_nat (length (tl_cbs l)) <= bB B /\
(forall B', bB B - oadd_costB klen (obj_capA (tl_cbs l)) (Z.of_nat (length kids)) <= bB B' -> bD B <= bD B' ->
K_free * Z.of_nat (length (tstate_blocks ts)) + K_exit + pa_bslack pa <= bB B' /\ pa_dslack pa <= bD B') /\
(forall B' cbs2 kids2 st' ss' obj' objs', (ss' <> ST_finish \/ zin st' [ST_array_add; ST_ovadd] = true) ->
( (Z.of_nat (length kids2) = Z.of_nat (length kids) + 1
/\ bB B - oadd_costB klen (obj_capA (tl_cbs l)) (Z.of_nat (length kids)) <= bB B'
/\ Z.of_nat (length cbs2) = Z.of_nat (length (tl_cbs l)) + Z.of_nat (length (t_objbs ts)) + 1
/\ obj_grownA (obj_capA (tl_cbs l)) (Z.of_nat (length kids)) (obj_capA cbs2))
\/ (Z.of_nat (length kids2) = Z.of_nat (length kids)
/\ bB B - 512 * (Z.of_nat (length (tl_cbs l)) + Z.of_nat (length (t_objbs ts)) - Z.of_nat (length cbs2)) <= bB B'
/\ Z.of_nat (length cbs2) <= Z.of_nat (length (tl_cbs l)) + Z.of_nat (length (t_objbs ts))
/\ obj_capA cbs2 = obj_capA (tl_cbs l)) ) ->
bD B <= bD B' ->
BOK pf pa (ts_lvl_obj ts (TL st' ss' (tl_cur l) (Some (Sobj kids2)) cbs2 (tl_name l) (tl_nbs l)) obj' objs' []) B' n).
Proof.
intros pf pa ts B n l kids klen H BSL Hl Hcs Hop Hk Hcap.
pose proof H as (H1 & H2 & H3 & H4 & H5).
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
pose proof (H5 (t_depth ts) l (le_n _) Hl) as (P0 & _ & OI & NI). specialize (OI Hop kids Hcs).
set (cap := obj_capA (tl_cbs l)) in *. set (cnt := Z.of_nat (length kids)) in *.
assert (Ephi : phi_open l = PhiO cap cnt) by (unfold phi_open; rewrite Hop; unfold phi_level; rewrite Hcs; reflexivity).
pose proof (ledger_open_ge (t_levels ts) (S (t_depth ts)) (t_depth ts) l Hl (Nat.lt_succ_diag_r _)
ltac:(intros j lj Hj Hnj; exact (proj1 (H5 j lj ltac:(lia) Hnj)))) as GE.
pose proof (K_ev_pos pf) as KE. pose proof (Z.mul_nonneg_nonneg (K_ev pf) (Z.of_nat n) ltac:(lia) ltac:(lia)) as KN.
pose proof (Zle_0_nat (length (tstate_blocks ts))) as Hnb.
pose proof (lf_thr_lower cap OI) as LT. pose proof (lf_thr_nonneg cap OI) as LT0. pose proof (lf_size_range cap OI) as CR.
assert (Hcnt : 0 <= cnt) by (unfold cnt; lia).
unfold bneed in H1. set (U := 16 * Z.max 0 (pf_len pf) + 8192) in *.
assert (KU : K_ev pf * Z.of_nat (S (Z.to_nat U + n)) = K_ev pf * Z.of_nat n + (U + 1)) by (unfold K_ev, U; lia). rewrite KU in H1. clear KU.
assert (KEV : U = 16 * Z.max 0 (pf_len pf) + 8192) by reflexivity.

assert (COSTB : oadd_costB klen cap cnt <= U + PhiO cap cnt - 4944 /\ (lf_thr cap <= cnt -> oadd_costB klen cap cnt = 16 * (klen + 1) + 512 + (1280 * cap + 2944))
/\ (cnt < lf_thr cap -> oadd_costB klen cap cnt = 16 * (klen + 1) + 512)).
{ unfold oadd_costB, strdup_costB, ins_costB, resize_costB. rewrite (lh_ns_small cap Hcap). rewrite Ephi in P0. unfold PhiO in *.
destruct (lf_thr cap <=? cnt) eqn:E; [apply Z.leb_le in E | apply Z.leb_gt in E]; (split; [lia | split; intros; lia]). }
destruct COSTB as (COSTB & CRES & CNOR).
assert (Hcbs : Z.of_nat (length (tl_cbs l)) <= Z.of_nat (length (tstate_blocks ts))).
{ pose proof (tstate_blocks_lvl_length ts l (TL 0 0 0 None [] 0 []) Hl) as E. unfold lvl_blocks in E at 2. cbn [tl_cbs tl_nbs app length] in E.
pose proof (Zle_0_nat (length (tstate_blocks (ts_lvl ts (TL 0 0 0 None [] 0 []))))). unfold lvl_blocks in E. rewrite length_app in E. lia. }
unfold K_free, K_exit in *. rewrite Ephi in GE.
split; [lia|]. split; [lia|]. split.
{ intros B' HB HD. split; lia. }
intros B' cbs2 kids2 st' ss' obj' objs' Hss' CASES HD.
set (l' := TL st' ss' (tl_cur l) (Some (Sobj kids2)) cbs2 (tl_name l) (tl_nbs l)).
assert (Hphi' : phi_open l' = PhiO (obj_capA cbs2) (Z.of_nat (length kids2))).
{ unfold phi_open. replace (lvl_closed l') with false by (symmetry; destruct Hss' as [Hss' | Hss']; [apply lvl_closed_open_ss | apply lvl_closed_open_st]; exact Hss').
unfold phi_level, l'. cbn [tl_cs tl_cbs]. reflexivity. }
pose proof (tstate_blocks_lvl_obj_length ts l l' obj' objs' [] Hl) as Hblk. cbn [length] in Hblk.
assert (Hlb : Z.of_nat (length (lvl_blocks l')) = Z.of_nat (length cbs2) + Z.of_nat (length (tl_nbs l))) by (unfold lvl_blocks, l'; cbn [tl_cbs tl_nbs]; rewrite length_app; lia).
assert (Hlb0 : Z.of_nat (length (lvl_blocks l)) = Z.of_nat (length (tl_cbs l)) + Z.of_nat (length (tl_nbs l))) by (unfold lvl_blocks; rewrite length_app; lia).
assert (GOAL : (K_ev pf * Z.of_nat n + (ledger_open (t_levels ts) (S (t_depth ts)) - PhiO cap cnt + PhiO (obj_capA cbs2) (Z.of_nat (length kids2)))
+ PhiPB (pf_len pf) (pb_capA (t_pbs ts)) + 512 * (Z.of_nat (length (tstate_blocks ts)) - Z.of_nat (length (lvl_blocks l)) - Z.of_nat (length (t_objbs ts)) + Z.of_nat (length (lvl_blocks l')) + 0)
+ 20480 + pa_bslack pa <= bB B')
/\ 0 <= PhiO (obj_capA cbs2) (Z.of_nat (length kids2)) /\ In (obj_capA cbs2) lf_sizes).
{ destruct CASES as [(Ek & HB & Elen & GR) | (Ek & HB & Elen & Ecap)].
- rewrite Ek. destruct GR as [(-> & Hlt) | (-> & Hge)].
+ fold cap. rewrite (CNOR Hlt) in HB. rewrite Ephi in P0. unfold PhiO in *. split; [lia | split; [lia | exact OI]].
+ fold cap. rewrite (CRES Hge) in HB. rewrite (lh_ns_small cap Hcap). rewrite Ephi in P0. unfold PhiO in *. split; [lia | split; [lia | apply lf_sizes_double; [exact OI | exact Hcap]]].
- rewrite Ek, Ecap. fold cap. rewrite Ephi in P0. split; [lia | split; [exact P0 | exact OI]]. }
destruct GOAL as (G1 & G2 & G3).
unfold BOK, bneed. rewrite Hblk. unfold ts_lvl_obj; cbn [t_levels t_depth t_pbs t_co].
rewrite (ledger_open_lupd (t_levels ts) (S (t_depth ts)) (t_depth ts) l l' Hl (Nat.lt_succ_diag_r _)), Hphi', Ephi.
split; [unfold K_free, K_exit; lia|]. split; [lia|]. split; [exact H3|]. split; [exact H4|].
intros i li Hi Hn.
destruct (PeanoNat.Nat.eq_dec i (t_depth ts)) as [-> | NE].
- rewrite nth_error_lupd_eq in Hn by exact Hd. injection Hn as <-. split; [rewrite Hphi'; exact G2|].
split; [intros _ kids3 Hk3; unfold l' in Hk3; cbn [tl_cs] in Hk3; discriminate Hk3|].
split; [intros _ kids3 Hk3; unfold l'; cbn [tl_cbs]; exact G3 | exact NI].
- rewrite nth_error_lupd_neq in Hn by congruence. exact (H5 i li Hi Hn).
Qed.

Lemma BOK_name_free : forall pf pa ts B B' n l b st' ss' nm',
BOK pf pa ts B n -> nth_error (t_levels ts) (t_depth ts) = Some l -> tl_nbs l = [b] ->
(lvl_closed l = true -> lvl_closed (TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) nm' []) = true) ->
bB B - 512 <= bB B' -> bD B <= bD B' ->
BOK pf pa (ts_lvl ts (TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) nm' [])) B' n.
Proof.
intros pf pa ts B B' n l b st' ss' nm' (H1 & H2 & H3 & H4 & H5) Hl Hnbs Hcl HB HD.
set (l' := TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) nm' []) in *.
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
pose proof (H5 (t_depth ts) l (le_n _) Hl) as (P0 & AI & OI & NI).
assert (Hphi : 0 <= phi_open l' <= phi_open l).
{ unfold phi_open in *. change (phi_level l') with (phi_level l).
destruct (lvl_closed l') eqn:E1; destruct (lvl_closed l) eqn:E2; try lia; specialize (Hcl eq_refl); discriminate Hcl. }
pose proof (tstate_blocks_lvl_length ts l l' Hl) as Hblk.
assert (Hlb : Z.of_nat (length (lvl_blocks l')) = Z.of_nat (length (lvl_blocks l)) - 1) by (unfold lvl_blocks, l'; cbn [tl_cbs tl_nbs]; rewrite Hnbs, !length_app; cbn [length]; lia).
split.
{ unfold bneed in *. rewrite Hblk. unfold ts_lvl; cbn [t_levels t_depth t_pbs]. rewrite (ledger_open_lupd (t_levels ts) (S (t_depth ts)) (t_depth ts) l l' Hl (Nat.lt_succ_diag_r _)). unfold K_free in *. lia. }
split; [lia|]. split; [exact H3|]. split; [exact H4|].
unfold ts_lvl; cbn [t_levels t_depth]. intros i li Hi Hn.
destruct (PeanoNat.Nat.eq_dec i (t_depth ts)) as [-> | NE].
- rewrite nth_error_lupd_eq in Hn by exact Hd. injection Hn as <-. split; [lia|].
assert (Hopl : lvl_closed l' = false -> lvl_closed l = false) by (intros Hop; destruct (lvl_closed l) eqn:E; [| reflexivity]; rewrite (Hcl eq_refl) in Hop; discriminate Hop).
split; [intros Hop kids Hcs; apply AI; [exact (Hopl Hop) | exact Hcs]|]. split; [intros Hop kids Hcs; apply (OI (Hopl Hop) kids); exact Hcs | apply Forall_nil].
- rewrite nth_error_lupd_neq in Hn by congruence. exact (H5 i li Hi Hn).
Qed.

Lemma BOK_blk_512 : forall pf pa ts B n b, BOK pf pa ts B n -> 0 <= pa_bslack pa -> In b (tstate_blocks ts) -> 512 <= bB B.
Proof.
intros pf pa ts B n b H BSL Hin. pose proof (BOK_ledger_nonneg _ _ _ _ _ H) as L0. destruct H as (H1 & _ & H3 & _).
assert (Hlen : 1 <= Z.of_nat (length (tstate_blocks ts))) by (destruct (tstate_blocks ts); [destruct Hin | cbn [length]; lia]).
pose proof (K_ev_pos pf) as KE. pose proof (Z.mul_nonneg_nonneg (K_ev pf) (Z.of_nat n) ltac:(lia) ltac:(lia)) as KN.
unfold bneed, K_free, K_exit in H1. lia.
Qed.

Lemma BOK_obj_irrel : forall pf pa ts l o os o' os' B n, BOK pf pa (ts_lvl_obj ts l o os []) B n -> BOK pf pa (ts_lvl_obj ts l o' os' []) B n.
Proof. intros pf pa ts l o os o' os' B n H. exact H. Qed.

Lemma BOK_name_bound : forall pf pa ts B n l nm nn, BOK pf pa ts B n -> nth_error (t_levels ts) (t_depth ts) = Some l -> tl_nbs l = [(nm, nn)] -> nn <= Z.max 0 (pf_len pf) + 1.
Proof.
intros pf pa ts B n l nm nn (_ & _ & _ & _ & H5) Hl Hnbs. pose proof (H5 (t_depth ts) l (le_n _) Hl) as (_ & _ & _ & NI).
rewrite Hnbs in NI. apply Forall_cons_iff in NI as [NI _]. exact NI.
Qed.
End RC__1.
End Mq6.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QRUw.Mq2. Import QPZI.Mq4. Import QkMG. Import QG8z QIsM.Mq2.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QugP QlKV.Mqf QSHS Ql4f.Mq4 QsKa.Mqh QrQv.Mq4 QEUF.Mq2 QW22.Mq8.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition pe_frameAX (m : word -> option byte) (pf : pe_fix) (pa : pe_fixA) (nb : word) (pj : pe_junkA) (sv : pe_saved) (ffc shc : list cell) : Prop :=
rw_cells asegs m (pf_spf pf) (pe_slotsA pf pa nb pj) /\
rw_cells asegs m (pf_spf pf + 312) [CB (Z.to_nat (pa_sp0 pa - 104 - (pf_spf pf + 312))) (pj_gap pj)] /\
rw_cells asegs m (pa_sp0 pa - 104) (pe_savedA_cells sv) /\
rw_cells asegs m (pa_F pa) ffc /\
rw_cells asegs m (shA (pa_F pa)) shc.

Lemma pe_frameAX_of_A : forall m pf pa cb nb pj sv, pe_frameA asegs m pf pa cb nb pj sv -> pe_frameAX m pf pa nb pj sv (ff_cellsA cb pj) (ffsh_cells FSH0).
Proof. intros m pf pa cb nb pj sv H. exact H. Qed.
Lemma pe_frameA_of_X : forall m pf pa cb nb pj sv, pe_frameAX m pf pa nb pj sv (ff_cellsA cb pj) (ffsh_cells FSH0) -> pe_frameA asegs m pf pa cb nb pj sv.
Proof. intros m pf pa cb nb pj sv H. exact H. Qed.

Lemma scoped_unpoisoned_w : forall (m : word -> option byte) (F n : Z) (k : nat) (w : list byte),
F mod 256 = 0 -> 0 <= F ->
bytes_at asegs m (F / 8 + A_SB + 8 * (Z.of_nat k / 8)) w -> length w = 8%nat ->
nth_error w (Z.to_nat (Z.of_nat k mod 8)) = Some (Z_to_bv 8 n) -> 1 <= n <= 7 ->
unpoisoned asegs m A_SB (F + 8 * Z.of_nat k) n.
Proof.
intros m F n k w GF GF0 WB Lw Hn Rn.
assert (Es : (F + 8 * Z.of_nat k) / 8 = F / 8 + Z.of_nat k) by (clear - GF; Z.div_mod_to_equations; lia).
assert (Ee : (F + 8 * Z.of_nat k + n - 1) / 8 = F / 8 + Z.of_nat k) by (clear - GF Rn; Z.div_mod_to_equations; lia).
assert (Em : (F + 8 * Z.of_nat k + n - 1) mod 8 = n - 1) by (clear - GF Rn; Z.div_mod_to_equations; lia).
unfold unpoisoned. split; [lia|]. split; [intros g Hg; rewrite Es, Ee in Hg; lia|]. split.
- exists n. split; [| right; split; [lia | rewrite Em; lia]].
rewrite Ee. apply nth_error_split in Hn as (l1 & l2 & Ew & Ll1). rewrite Ew in WB.
apply (proj1 (bytes_at_app asegs _ _ _ _)) in WB as [_ WB]. change (Z_to_bv 8 n :: l2) with ([Z_to_bv 8 n] ++ l2) in WB.
apply (proj1 (bytes_at_app asegs _ _ _ _)) in WB as [WB _]. rewrite Ll1 in WB.
replace (F / 8 + Z.of_nat k + A_SB) with (F / 8 + A_SB + 8 * (Z.of_nat k / 8) + Z.of_nat (Z.to_nat (Z.of_nat k mod 8))); [exact WB|].
rewrite Z2Nat.id by (apply Z.mod_pos_bound; lia). pose proof (Z.div_mod (Z.of_nat k) 8 ltac:(lia)). lia.
- intros w' Hw'. rewrite Es, Ee in Hw'. exists w. split; [exact Lw|].
replace (w' * 8) with (F / 8 + A_SB + 8 * (Z.of_nat k / 8)); [exact WB|].
unfold A_SB in *. clear - GF Hw'. Z.div_mod_to_equations. lia.
Qed.

Section WithIface.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.

Lemma pe_frameAX_pres : forall pf pa (L : list blk) SP me m nb pj sv ffc shc,
heap_pres A4H L SP me m -> SP <= pf_spf pf -> pe_geomA pf pa ->
In (pa_F pa, 248) L -> In (shA (pa_F pa), 32) L ->
Z.of_nat (cells_size ffc) <= 248 -> Z.of_nat (cells_size shc) <= 32 ->
pe_frameAX me pf pa nb pj sv ffc shc -> pe_frameAX m pf pa nb pj sv ffc shc.
Proof.
intros pf pa L SP me m nb pj sv ffc shc HPR HSP GEO InF InS SZF SZS (SL & GP & SV & FF & FSH).
pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
split; [| split; [| split; [| split]]].
- eapply (heap_pres_rw_cells A4H); [exact HPR | exact SL | left; lia].
- eapply (heap_pres_rw_cells A4H); [exact HPR | exact GP | left; lia].
- eapply (heap_pres_rw_cells A4H); [exact HPR | exact SV | left; lia].
- eapply (heap_pres_rw_cells A4H); [exact HPR | exact FF | right; right]. exists (pa_F pa, 248). split; [exact InF | cbn; lia].
- eapply (heap_pres_rw_cells A4H); [exact HPR | exact FSH | right; right]. exists (shA (pa_F pa), 32). split; [exact InS | cbn; lia].
Qed.

Lemma pe_frameAX_write : forall pf pa q LB0 LM FRS B ts A m mc md lo nb pj sv ffc shc ffc' shc',
PE_STATIC_A HIx pf pa lo -> HEAPA A4L HIx A (pe_blocksA pf q LB0 ts) LM ((pa_F pa, 2) :: FRS) B m md ->
pe_frameAX m pf pa nb pj sv ffc shc ->
munch [(pf_tk pf, pf_tk pf + 72); (pa_F pa, pa_F pa + 248); (shA (pa_F pa), shA (pa_F pa) + 32)] m mc -> wmono asegs m mc ->
rw_cells asegs mc (pa_F pa) ffc' -> rw_cells asegs mc (shA (pa_F pa)) shc' ->
pe_frameAX mc pf pa nb pj sv ffc' shc'.
Proof.
intros pf pa q LB0 LM FRS B ts A m mc md lo nb pj sv ffc shc ffc' shc' STC HP (SLOTS & GAP & SAVED & _ & _) MU WM FFc FSHc.
pose proof STC as (LO & LOS & GEO & HT & SP0 & _). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof alloc_ceiling_range as ACR.
assert (INtk : In (pf_tk pf, 72) (pe_blocksA pf q LB0 ts ++ LM)) by (apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP INtk) as (_ & _ & Htlo & Hthi & _).
pose proof (pe_slotsA_size pf pa nb pj) as SZ.
assert (SHhi : shA (pa_F pa) + 32 <= alloc_ceiling) by (unfold shA, A_SB; clear - GFc ACR; Z.div_mod_to_equations; lia).
split; [| split; [| split; [| split; [exact FFc | exact FSHc]]]].
- eapply rw_cells_transport; [exact SLOTS | exact MU | exact WM |]. rewrite SZ. cbn [disjoint_from fst snd]. lia.
- eapply rw_cells_transport; [exact GAP | exact MU | exact WM |]. cbn [cells_size csize disjoint_from fst snd]. lia.
- eapply rw_cells_transport; [exact SAVED | exact MU | exact WM |]. cbn [pe_savedA_cells cells_size csize disjoint_from fst snd Nat.add]. lia.
Qed.

Definition PE_INV_AX (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (errv : word) (FRX : Prop) : Prop :=
(length (t_levels ts) = Z.to_nat (pf_mxd pf) /\ (t_depth ts < Z.to_nat (pf_mxd pf))%nat /\
0 <= t_co ts <= pf_len pf /\ ts_choff (t_x ts) = Z_to_bv 64 (t_co ts) /\
rw_cells asegs m (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) (t_pb ts) (Z.of_nat (t_depth ts)) q (t_x ts)) /\
pbuf asegs m (t_pbs ts) (t_pb ts) /\ t_pb ts <> 0 /\
tstack asegs m q (t_levels ts) /\
FRX) /\
PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts errv.

Lemma PE_INV_AX_of_A : forall pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv,
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PE_INV_AX pf pa q LB0 LM FRS payload me lo m md A B ts errv (pe_frameA asegs m pf pa cb nb pj sv).
Proof. intros until errv. intros H. exact H. Qed.

Lemma PE_INV_AX_tokw : forall pf pa q LB0 LM FRS payload me lo m mc md A B ts errv W co' x' (FRX FRX' : Prop),
PE_STATIC_A HIx pf pa lo ->
PE_INV_AX pf pa q LB0 LM FRS payload me lo m md A B ts errv FRX ->
munch W m mc -> wmono asegs m mc -> mem_inv asegs mc -> Forall (pe_wtfA pf pa) W ->
rw_cells asegs mc (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) (t_pb ts) (Z.of_nat (t_depth ts)) q x') ->
FRX' ->
0 <= co' <= pf_len pf -> ts_choff x' = Z_to_bv 64 co' ->
PE_INV_AX pf pa q LB0 LM FRS payload me lo mc md A B (ts_set_x ts co' x') errv FRX'
/\ (forall b, PBOKat m ts b -> PBOKat mc (ts_set_x ts co' x') b).
Proof.
intros pf pa q LB0 LM FRS payload me lo m mc md A B ts errv W co' x' FRX FRX' STC [CORE REST] MU WM MI HW TOKc FRc Hco Hch.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
split.
- split.
+ unfold ts_set_x; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [exact LEN32|]. split; [exact D32|]. split; [exact Hco|]. split; [exact Hch|].
split; [exact TOKc|]. split; [| split; [exact Hpb | split; [| exact FRc]]].
* eapply (pbuf_wtfA HIx) with (ts := ts); [exact STC | exact (proj1 REST) | exact PB | exact MU | exact WM | exact HW].
* eapply (tstack_wtfA HIx) with (ts := ts); [exact STC | exact (proj1 REST) | exact TSK | exact LEN32 | exact MU | exact WM | exact HW].
+ apply PE_REST_A_set_x.
eapply (PE_REST_A_private_write HIx GA GA_outside) with (ts := ts); [exact STC | exact REST | exact MU | exact WM | exact MI | apply pe_wtfA_private; exact HW].
- intros b PBK. eapply PBOKat_same with (ts := ts); [reflexivity | reflexivity |].
eapply PBOKat_agree; [exact PBK | | apply incl_refl].
eapply (agree_wtqA HIx); [exact STC | exact (proj1 REST) | exact MU | exact WM | apply pe_wtfA_wtqA; exact HW |].
intros a n Hin. assert (HinL : In (a, n) (pe_blocksA pf q LB0 ts ++ LM)) by (unfold pe_blocksA, tstate_blocks; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hin).
split; [exact HinL|].
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ (proj1 REST)) as ND. unfold pe_blocksA in ND. rewrite <- app_assoc in ND. split.
+ intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | left; reflexivity].
+ intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | right; left; reflexivity].
Qed.

Hypothesis MAPP : memappend_A_stmt2 HIx.

Lemma pe_memappend_gX :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (xb xn bnd : Z) (src : list byte) (ffc shc : list cell)
(ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_AX pf pa q LB0 LM FRS payload me lo m md A B ts errv (pe_frameAX m pf pa nb pj sv ffc shc) ->
Z.of_nat (cells_size ffc) <= 248 -> Z.of_nat (cells_size shc) <= 32 ->
PBOKat m ts bnd -> bnd + xn <= t_co ts + 1 -> 0 <= xn < 2^31 ->
forall kB : nat, BOK pf pa ts B kB -> bv_unsigned ra mod 2 = 0 ->
bytes_at asegs m xb src -> Z.of_nat (length src) = xn -> 0 <= xb ->
src_locA ((t_objbs ts ++ concat (map lvl_blocks (t_levels ts))) ++ (pf_tk pf, 72) :: (q, 32 * pf_mxd pf) :: LB0) ((pa_F pa, 2) :: FRS) xb xn ->
(0 < xn -> unpoisoned asegs m A_SB xb xn) ->
(forall m2 md2 A2 B2 pbs2 errv2 r (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word) F2 fc2,
PE_INV_AX pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 (ts_pbs ts pbs2) errv2 (pe_frameAX m2 pf pa nb pj sv ffc shc) ->
(r = xn /\ PBOKat m2 (ts_pbs ts pbs2) (bnd + xn) /\ BOK pf pa (ts_pbs ts pbs2) B2 kB) \/ (r = 2^64 - 1 /\ pbs2 = t_pbs ts) ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 s0 s1 (Z_to_bv 64 r) w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F2 (ret_pc ra) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 (t_pb ts)) (Z_to_bv 64 xb) (Z_to_bv 64 xn) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9b4fc) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC BSL INV SZF SZS PBK Hbn Hn kB BK RA SRC SRCL Hb0 SLOC UNP K.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof INV as [CORE REST1].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK1 & FR1).
destruct PBK as (buf & bpos & cap & pre & post & Epbs & Lpre & CORE1 & Hbp).
pose proof (proj1 REST1) as HP1. unfold pe_blocksA, tstate_blocks in HP1. rewrite Epbs in HP1. cbn [app] in HP1.
pose proof REST1 as (_ & _ & _ & ST1 & ERR1 & _ & _ & _ & _ & _ & _ & BUD1).
assert (Hbp0 : 0 <= bpos) by (destruct CORE1 as (C1 & _); lia).
pose proof (BOK_memappend pf pa ts B kB (t_pb ts) buf cap bpos xn BK Epbs BSL Hbp0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as BUDM.
assert (SPF1 : lo <= pf_spf pf - 112 - 4096 /\ pf_spf pf mod 16 = 0 /\ pf_spf pf <= hiA_top A4L HIx /\ 0 <= pf_spf pf < 2^62).
{ clear - LOS HT Gle Gspf SP0. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; lia. }
destruct SPF1 as (SPF1 & SPF2 & SPF3 & SPF4).
set (LBc := (t_objbs ts ++ concat (map lvl_blocks (t_levels ts))) ++ (pf_tk pf, 72) :: (q, 32 * pf_mxd pf) :: LB0) in *.
eapply MAPP with (lo := lo) (b := xb) (src := src) (n := xn) (pb := t_pb ts) (buf := buf) (bpos := bpos) (cap := cap);
[ exact HP1 | exact CORE1 | exact Hn | exact SRC | exact SRCL | exact Hb0 | exact SLOC | exact UNP
| rewrite unsigned_lit by lia; exact ST1 | exact LO | rewrite unsigned_lit by lia; exact SPF1
| rewrite unsigned_lit by lia; exact SPF2
| rewrite unsigned_lit by lia; exact SPF3
| exact ERR1 | reflexivity | exact RA | reflexivity | reflexivity | reflexivity
| exact (proj1 BUDM) | ].
intros ms2 md2 A2 (m2 & r & errv2 & buf' & cap' & B2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & HB2 & HD2 & HP2 & OUT2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp hla_base A4L A4H] in *. rewrite ?(unsigned_lit (pf_spf pf)) in ST2 by lia. rewrite ?(unsigned_lit (pf_spf pf)) in HPR2 by lia.
set (pbs2 := [(t_pb ts, 16); (buf', cap')]).
assert (INq2 : In (q, 32 * pf_mxd pf) LBc) by (apply in_or_app; right; right; left; reflexivity).
assert (INtk2 : In (pf_tk pf, 72) LBc) by (apply in_or_app; right; left; reflexivity).
assert (FR2 : pe_frameAX m2 pf pa nb pj sv ffc shc).
{ eapply pe_frameAX_pres; [exact HPR2 | lia | exact GEO | | | exact SZF | exact SZS | exact FR1].
- apply in_or_app; right. apply in_or_app; right. change 248 with (fr_size 2 - 8). apply fr_ivs_frame. left; reflexivity.
- apply in_or_app; right. apply in_or_app; right. rewrite <- fr_shadow_len_2. change (shA (pa_F pa)) with (shad A4L (pa_F pa)). apply fr_ivs_shadow. left; reflexivity. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in TOK; [| eapply client_range_block; [apply in_or_app; left; exact INtk2 | lia | unfold tok_cells_g; cbn; lia]]. cbn [hl_segs hla_base A4L A4H] in TOK.
apply (tstack_pres_g A4H _ _ _ _ _ _ HPR2 (in_or_app _ _ _ (or_introl INq2))) in TSK1; [| exact LEN32]. cbn [hl_segs hla_base A4L A4H] in TSK1.
assert (BUD2 : PE_BUD pf pa (ts_pbs ts pbs2) B2).
{ destruct OUT2 as [(_ & Ec & _) | (_ & Eb & Ec & _ & _)].
- subst cap'. exact (BOK_weak _ _ _ _ _ (proj2 BUDM buf' B2 HB2 HD2)).
- subst buf' cap'. unfold pbs2. change 16 with PB_SZ. rewrite <- Epbs. replace (ts_pbs ts (t_pbs ts)) with ts by (destruct ts; reflexivity).
exact (BOK_memappend_fail pf pa ts B B2 kB (t_pb ts) buf cap bpos xn BK Epbs Hbp0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HB2 HD2). }
assert (REST2 : PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 (ts_pbs ts pbs2) errv2).
{ eapply (PE_REST_A_call_pb HIx GA GA_pres) with (ts := ts) (LBc := LBc);
[exact STC | exact REST1 | exact VM2 | exact HPR2 | | | exact ST2 | exact ERR2 | exact BUD2].
- unfold LBc; intros b Hb; apply in_or_app;
apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; apply in_or_app; left; exact Hb | apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; right; right; exact Hb]].
- unfold pe_blocksA, tstate_blocks; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs]; exact HP2. }
assert (PBany : pbuf asegs m2 pbs2 (t_pb ts)).
{ destruct OUT2 as [(_ & _ & PBS) | (_ & -> & -> & _ & PC)]; [eapply pbufc_pbuf; exact PBS|].
exists buf, bpos, cap, pre, post. split; [reflexivity|]. split; [exact Lpre | exact PC]. }
assert (INV2 : PE_INV_AX pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 (ts_pbs ts pbs2) errv2 (pe_frameAX m2 pf pa nb pj sv ffc shc)).
{ split; [| exact REST2]. unfold ts_pbs; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOK|]. split; [exact PBany|]. split; [exact Hpb|]. split; [exact TSK1 | exact FR2]. }
assert (Hbl : 0 <= bpos <= Z.of_nat (length (pre ++ [Z_to_bv 8 0] ++ post))) by (destruct CORE1 as (C1 & _ & C3 & _); lia).
eapply (K m2 md2 A2 B2 pbs2 errv2 r); [exact INV2 | | exact FS2 | exact FRM2].
destruct OUT2 as [(-> & Ec & PBS) | (-> & -> & -> & _ & _)].
- left. split; [reflexivity|]. split.
+ eapply (PBOKat_appended m2 _ (bnd + xn) (t_pb ts) buf' cap' bpos (pre ++ [Z_to_bv 8 0] ++ post) src); [reflexivity | reflexivity | exact PBS | exact Hbl |]. lia.
+ unfold pbs2. rewrite Ec. exact (proj2 BUDM buf' B2 HB2 HD2).
- right. split; [reflexivity|]. unfold pbs2. change 16 with PB_SZ. symmetry. exact Epbs.
Qed.
End WithIface.
End RC__1.
End Mq7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn QKQo Q8tj. Import QPZI.Mq4.
Import Q6WR Q6WR.Mq0 QrPc. Import QeuE.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqd QW22.Mq6 QI6Z.Mq4 Qiiq.Mq9 QlKV.Mqf QkXq.Mq7 Qiiq.Mqb Qoif.Mq5.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PutA.
Variable HIx : heap_iface_A A4L.

Ltac releaseB ST := lazymatch type of ST with stk _ ?mq _ _ =>
match goal with S : rw_cells _ mq (bv_unsigned ?spv + -112) [_], F : rw_cells _ mq (bv_unsigned ?spv + -104) _ |- _ =>
release_frame S ST (bv_unsigned spv + -104); release_frame F ST (bv_unsigned spv) end end.

Ltac spl1 mq :=
match goal with
| S : rw_cells _ mq (bv_unsigned _ + -112) [_] |- _ =>
let bs := fresh "sbs" in let S2 := fresh "SPL" in
destruct (rw_cells_forget asegs _ _ _ S) as [bs S2]; cbn [cells_size csize Nat.add] in S2; eexists; exact S2
| S : rw_cells _ ?ma (bv_unsigned _ + -112) [_], H : heap_pres A4H _ _ ?ma ?mb |- _ =>
lazymatch mb with ma => fail | _ => idtac end;
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ H) in S; [ spl1 mq | left; cbn; lia ]
| |- _ => fail 1 "spill slot: no slot hypothesis / heap_pres chain to the current memory"
end.
Ltac spl := lazymatch goal with
| |- spillA _ ?mq /\ _ => split; [spl1 mq|] | |- spillA ?mq /\ _ => split; [spl1 mq|]
| |- spillA _ ?mq => spl1 mq | |- spillA ?mq => spl1 mq | |- _ => idtac end.
Ltac hpw H := eapply heap_pres_weaken; [exact H | lia | intros b' Hb'; exact Hb'].
Hypothesis DEL : lh_delete_tail_A_stmt HIx.

Theorem json_object_put_A_cps : put_stmt_A HIx.
Proof.
unfold put_stmt_A, put_stmtA. intros until rc. intros HP PRE A0 ST LO LOS SPA HT ERR TP RA BB K.
unfold put_stk_A in LOS. unfold put_entry_A.
unfold_consts. unfold A_SB, A_TP, A_ERRNO in *. word_range sp SPW.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP) as [HB0 HD0].
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL]. a4l.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU.
reenterA asegs A4L HIx asegs_wx HP. subst a0 tp.
carve_frame 104%nat ST. carve_frame 8%nat ST.
do 14 bstep.
bstep.
destruct s as [c|].
- destruct PRE as (Hp & Hrc & J).
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND.
destruct (jval_hdr asegs A4F c m BS p rc J (nodup_app_l' _ _ (nodup_app_l' _ _ ND))) as (n & tojs_ & pb_ & udel_ & ud_ & rest_ & INp & _ & N48 & _ & _). clear tojs_ pb_ udel_ ud_ rest_.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p n HP ltac:(apply in_or_app; left; apply in_or_app; left; exact INp)) as (_ & Hpal & Hplo & Hphi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
if_falsex.
bstep. bstep. bstep. bstep. bstep. bstep. bstep.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
assert (J1 : jval asegs A4F c m1 BS p rc).
{ eapply jval_agree; [exact J | | apply incl_refl]. eapply (agree_of_munch asegs); [exact MU | exact WM |].
intros a k Hin. pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin)) as (Hk & _ & _ & Hahi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hahi. cbn. lia. }
assert (HPR1 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m1).
{ eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; rewrite <- app_assoc; apply in_or_app; right; exact Hb | clia |].
apply Forall_cons; [cbn [fst snd]; left; clia | apply Forall_nil]. }
evt_done5.
eapply (maybe_free_A_closed HIx) with (s := c) (BS := BS) (LB := LB) (x := p) (rc := rc) (lo := lo);
[ heap_nowA A4L HIx HP MU WM MI | exact Hp | exact Hrc | exact J1 | .. ]; a4l_goal; rewrite ?unsigned_lit by lia; try first [reflexivity | lia].
all: try (replace (bv_unsigned sp + -112) with (bv_unsigned sp - 112) by lia; rewrite Zminus_mod, SPA; reflexivity).
all: try exact ERR. all: try assumption.
all: try (intros ->; cbn [put_costA] in BB; rewrite Z.eqb_refl in BB; exact BB).
intros ms2 md2 A2 (m2 & r & B2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & BD2 & OUT2).
destruct RS2 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F2 & fc2 & -> & FS2 & FRM2).
a4l. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in ST2 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in HPR2 by lia.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia].
match goal with S : rw_cells _ _ (bv_unsigned _ + -112) [_] |- _ => apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in S; [| left; cbn; lia] end. a4l.
assert (HPR12 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m2).
{ eapply heap_pres_trans; [hpw HPR1 | eapply heap_pres_weaken; [exact HPR2 | lia | intros b Hb; exact Hb]]. }
clear MU WM MI J J1.
destruct OUT2 as [(Er & Hrc2 & J2 & BB2 & HP2) | [(Er & -> & BB2 & HP2) | (Er & -> & ZM & BB2 & HP2)]]; subst r.
+
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
pose proof (wmono_refl asegs m2) as WM. pose proof (munch_refl [] m2) as MU.
reenterA asegs A4L HIx asegs_wx HP2. bstep. bstep. if_truex.
do 14 bstep. releaseB ST2. bstep.
evt_done5. apply K. unfold put_postA. exists m2, (Z_to_bv 64 0), B2.
split; [apply ret_statew_intro; [exact FS2 | exact FRM2] |]. split; [exact VM2|]. spl; split; [exact ST2|]. split; [hpw HPR12|]. split; [exact ERR2|].
split; [cbn [put_costA]; replace (rc =? 1) with false by (symmetry; apply Z.eqb_neq; lia); lia|]. split; [exact BD2|].
right. exists c. split; [reflexivity|]. split; [lia|]. split; [exact J2 | exact HP2].
+
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
pose proof (wmono_refl asegs m2) as WM. pose proof (munch_refl [] m2) as MU.
reenterA asegs A4L HIx asegs_wx HP2. bstep. bstep. if_truex.
do 14 bstep. releaseB ST2. bstep.
evt_done5. apply K. unfold put_postA. exists m2, (Z_to_bv 64 1), B2.
split; [apply ret_statew_intro; [exact FS2 | exact FRM2] |]. split; [exact VM2|]. spl; split; [exact ST2|]. split; [hpw HPR12|]. split; [exact ERR2|].
split; [cbn [put_costA]; rewrite Z.eqb_refl; lia|]. split; [exact BD2|].
left. split; [right; reflexivity | exact HP2].
+
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
pose proof (wmono_refl asegs m2) as WM. pose proof (munch_refl [] m2) as MU.
destruct (zomb_zhead HIx sp gp lo errv LM FRS c m2 p BS ZM (desc_allA HIx sp gp lo errv LM FRS LO ltac:(lia) SPA HT DEL c)) as (isobj & ck & ZH & HS).
reenterA asegs A4L HIx asegs_wx HP2. bstep. bstep. if_false.
bstep. bstep. bstep. bstep.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply bv_eq; vm_compute; reflexivity).
evt_done5.
stash FR.
eapply HS; [exact HP2 | exact ZH | exact ST2 | exact ERR2 | cbn [put_costA] in BB; rewrite Z.eqb_refl in BB; lia | spl |].
intros ms3 md3 A3 (m3 & F3 & fc3 & B3 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w18 & w19 & w20 & w21 & w22 & w23 & -> & FS3 & FRM3 & VM3 & HP3 & [sbsHP3x SPLHP3x] & ST3 & HPR3 & ERR3 & HB3 & HD3).
unstash FR.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. a4l.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI3.
clear WM MU. pose proof (wmono_refl asegs m3) as WM. pose proof (munch_refl [] m3) as MU.
reenterA asegs A4L HIx asegs_wx HP3.
bstep. bstep. if_true. bstep.
do 14 bstep. releaseB ST3. bstep.
evt_done5. apply K. unfold put_postA. exists m3, (Z_to_bv 64 1), B3.
split; [apply ret_statew_intro; [eapply fsaved_trans; [exact FS2 | exact FS3] | intros Hf; exact (FRM3 (FRM2 Hf))] |].
split; [eapply model_vm_only_trans; [exact VM2 | exact VM3]|]. spl; split; [exact ST3|].
split; [eapply heap_pres_trans; [hpw HPR12 | eapply heap_pres_weaken; [exact HPR3 | lia | intros b Hb; exact Hb]]|].
split; [exact ERR3|]. split; [cbn [put_costA]; rewrite Z.eqb_refl; lia|]. split; [lia|].
left. split; [right; reflexivity | exact HP3].
-
destruct PRE as [-> ->]. cbn [app] in HP.
if_true.
do 14 bstep. releaseB ST. bstep.
evt_done5. apply K. unfold put_postA.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, (Z_to_bv 64 0), B end.
split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|]. spl; split; [exact ST|].
split.
{ eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; exact Hb | clia |].
apply Forall_cons; [cbn [fst snd]; left; clia | apply Forall_nil]. }
split; [assumption|]. split; [cbn [put_costA]; lia|]. split; [lia|].
left. split; [left; reflexivity |].
eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); apply Forall_cons; [cbn [fst snd]; left; split; [clia | pose proof (hiA_top_hi A4L HIx); lia] | apply Forall_nil] | exact WM | assumption].
Qed.
End PutA.
End RC__1.
End Mq8.

Module Mq9.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun QWxq_c1.Mq0 Qfw3_c1.Mq2 Qc3B Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn QKQo Q8tj QRUw.Mq2.
Import QSL3.
Import Qvbw QYIF.
Import QnCn.Mq0 QR2u.

Import QbFI QXUB. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QsKa.Mqd QlKV.Mqj QsKa.Mqg QsKa.Mq9 QJZd.Mq9 QsKa.Mqh Qw5U.Mq5 QsKa.Mqc QsKa.Mqb QlKV.Mqh QsKa.Mqe QlKV.Mqf. Import QlKV.Mq2 QsKa. Import Qiiq.

Import Qvmy Qawr.
Import Qwm6.Mq2.
Import QB6X.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Import Qoif.Mq6.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section MDcTail.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Notation wz := (Z_to_bv 64).
Notation jroot_repA := (jroot_rep A4H A4F).
Hypothesis SHALLOW : shallow_A_stmt HIx.
Hypothesis PUT : put_stmt_A HIx.

Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB BS LM : list blk) (FRS : list frame) (B0 : bud) (lo p D w : Z) (r : jroot) (T : TSet).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp - dc_stkA (rdepth r).
Hypothesis SPA : bv_unsigned sp mod 32 = 0.
Hypothesis HT : bv_unsigned sp <= hiA_top A4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis FRM0 : frm0 fc.
Hypothesis DLOC : arg_locA FRS D 8.
Hypothesis DAL : D mod 8 = 0.
Hypothesis NN : r <> JRnull.
Hypothesis JR0 : jroot_repA r m0 BS p.
Hypothesis Kont : forall ms' md' m' rv (A' : ASA A4L HIx) (B' : bud),
jo_post_frameDA D ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 (BS ++ LB) (LM ++ fr_ivs A4L FRS) lo rv m' ms' md' ->
lh_globA m' -> jroot_repA r m' BS p -> dc_resA HIx r BS LB LM FRS D w B0 m' md' rv A' B' ->
AJ5 A4L HIx A' T md' ms'.
Local Notation fk1_HEAPA_W := (Qoif.Mq6.fk1_HEAPA_W HIx) (only parsing).
Local Notation fk1_pres_W := (Qoif.Mq6.fk1_pres_W HIx) (only parsing).
Local Notation dc_blk_notfr := (Qoif.Mq6.dc_blk_notfr HIx) (only parsing).
Local Notation ASP := (Qoif.Mq6.ASP sp) (only parsing).
Local Notation dc_save := (Qoif.Mq6.dc_save ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) (only parsing).
Local Notation dc_inv := (Qoif.Mq6.dc_inv ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB BS LM FRS lo D) (only parsing).
Local Notation dc_dst := (Qoif.Mq6.dc_dst D) (only parsing).
Local Notation dc_dfacts := (Qoif.Mq6.dc_dfacts HIx ra sp LM FRS D DLOC DAL) (only parsing).
Local Notation dc_dst_pres := (Qoif.Mq6.dc_dst_pres HIx ra sp LM FRS D DLOC) (only parsing).
Local Notation dc_blkW_disj := (Qoif.Mq6.dc_blkW_disj HIx ra sp LM FRS D DLOC DAL) (only parsing).
Local Notation dc_dst_blkW := (Qoif.Mq6.dc_dst_blkW HIx ra sp LM FRS D DLOC DAL) (only parsing).
Local Notation dc_epi := (Qoif.Mq6.dc_epi HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB BS LM FRS B0 lo p D w r T LO LOS HT DLOC NN JR0 Kont) (only parsing).
Local Notation dc_scr := (Qoif.Mq6.dc_scr p) (only parsing).
Hypothesis OBL_STRDUP_NF : strdup_nf_stmt A4L HIx.

Lemma dc_tail_ud :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x21 x23 x24 x25 x26 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mc : word -> option byte) (mdc : config) (A : ASA A4L HIx) (Bc : bud) (Fr : Z) (v0 : word) (j16a : list byte) (c40 : cell) (j16 : list byte)
(w0 : word) (frest : list cell) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : byte)
(q pb ud udn : Z) (uds : list byte) (bits bits' : word) (REM : list blk),
dc_inv mc mdc -> fsaved F F1 -> frm0 fc1 ->
HEAPAx A (BS ++ [(q, 48)] ++ REM ++ LB) LM ((Fr, 1) :: FRS) Bc mc mdc ->
rw_cells asegs mc ASP (dc_scr Fr v0 j16a c40 j16) -> csize c40 = 8%nat ->
rw_cells asegs mc Fr (C8 w0 :: frest) -> Z.of_nat (cells_size frest) = 112 ->
rw_cells asegs mc (Fr / 8 + 2147450880) [C1 y0; C1 y1; C1 y2; C1 y3; C1 y4; C1 y5; C1 y6; C1 y7; C1 y8; C1 y9; C1 y10; C1 y11; C1 y12; C1 y13; C1 y14; C1 y15] ->
jroot_repA r mc BS p -> In (p, 48) BS -> In (ud, udn) BS -> udn <= 2^31 ->
rw_cells asegs mc p (jhdr_cells JT_DOUBLE 1 (fn_ud_to_json_string A4F) pb (fn_free_userdata A4F) ud ++ [C8 bits]) ->
cstr asegs mc ud udn uds ->
r = JRtree (Sdouble true) ->
q <> 0 -> dc_dst mc q ->
rw_cells asegs mc q (jhdr_cells JT_DOUBLE 1 (fn_ud_to_json_string A4F) 0 0 0 ++ [C8 bits']) ->
16 + Z.of_nat (length uds) <= w ->
16 * (Z.of_nat (length uds) + 1) + 512 <= bB Bc -> 1 <= bD Bc ->
bD B0 - w <= bD Bc - 1 -> bB B0 - DC_KB * w + 512 * 2 <= bB Bc - (16 * (Z.of_nat (length uds) + 1) + 512) ->
AJ5 A4L HIx A T mdc
(MS (mkR x1 (wz ASP) gp (wz A_TP) t0 t1 t2 sp (wz ASP) a0 a1 a2 a3 a4 a5 a6 a7
(wz Fr) x19 (wz D) x21 (wz 2147450880) x23 x24 x25 x26 (wz (Fr / 8 + 2147450880)) t3 t4 t5 t6)
F1 (wz 0xa1984) fc1 None mc (seg_rom asegs)).
Proof.
intros until REM. intros INV FS FRM1 HP SCR C40 FF FFsz FSH JRc INp INu UDN SRC CS Er Hq [DC DSH] QX WUD BBs BDs BDc BBc.
pose proof INV as (VMi & PRESi & STi & SAVEi & Gi). unfold dc_save in SAVEi.
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu. unfold ASP, dc_scr in *.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
destruct (dc_dfacts _ _ _ _ _ _ HP) as (D1 & D2 & D3 & D4 & DBLK & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13).
pose proof (rw_cells_bound asegs mc D _ DC) as DR. cbn [cells_size csize Nat.add] in DR.
assert (INp2 : In (p, 48) (BS ++ [(q, 48)] ++ REM ++ LB)) by (apply in_or_app; left; exact INp).
assert (INu2 : In (ud, udn) (BS ++ [(q, 48)] ++ REM ++ LB)) by (apply in_or_app; left; exact INu).
assert (INq2 : In (q, 48) (BS ++ [(q, 48)] ++ REM ++ LB)) by (apply in_or_app; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p 48 HP ltac:(apply in_or_app; left; exact INp2)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ q 48 HP ltac:(apply in_or_app; left; exact INq2)) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ q 48 HP ltac:(apply in_or_app; left; exact INq2)) as Hqimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hqimg.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ ud udn HP ltac:(apply in_or_app; left; exact INu2)) as (_ & Hual & Hulo & Huhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi, Hqhi, Huhi.
pose proof (DBLK p 48 ltac:(apply in_or_app; left; exact INp2)) as DBp. pose proof (DBLK q 48 ltac:(apply in_or_app; left; exact INq2)) as DBq.
assert (Hqp : q <> p).
{ intros ->. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. rewrite <- app_assoc in ND.
exact (nodup_mid_fresh BS [(p, 48)] ((REM ++ LB) ++ LM) p 48 48 ND ltac:(left; reflexivity) ltac:(apply in_or_app; left; exact INp)). }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ q 48 p 48 HP ltac:(apply in_or_app; left; exact INq2) ltac:(apply in_or_app; left; exact INp2) Hqp) as Hdqp.
destruct CS as (CL & CNZ & junk & CBk).
assert (NNu : ~ In (Z_to_bv 8 0) uds) by (intros X; rewrite Forall_forall in CNZ; apply (CNZ _ X); reflexivity).
assert (USTR : bytes_at asegs mc ud (uds ++ [Z_to_bv 8 0])).
{ assert (BBu : bytes_at asegs mc ud ((uds ++ [Z_to_bv 8 0]) ++ junk)) by (destruct CBk as [[[_ _] HB] _]; cbn in HB; rewrite app_nil_r in HB; rewrite <- app_assoc; exact HB).
apply bytes_at_app in BBu as [BBu _]. exact BBu. }
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p 48 3 HP INp2 ltac:(lia) ltac:(lia)) as SHp3.
replace (p / 8 + 2147450880 + 3) with (p / 8 + 2147450883) in SHp3 by lia.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p 48 4 HP INp2 ltac:(lia) ltac:(lia)) as SHp4.
replace (p / 8 + 2147450880 + 4) with (p / 8 + 2147450884) in SHp4 by lia.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ q 48 1 HP INq2 ltac:(lia) ltac:(lia)) as SHq1.
replace (q / 8 + 2147450880 + 1) with (q / 8 + 2147450881) in SHq1 by lia.
set (sh := Fr / 8 + 2147450880) in *.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. change (hl_segs A4L) with asegs in MI.
pose proof (Qw5U.Mq5.rtc_cell HIx _ _ _ _ _ _ _ 0xe8e60 (le8 (wz 0x9f85c)) HP ltac:(unfold a4_rt_consts; repeat first [left; reflexivity | right])) as GOTU.
apply ro_C8_of_bytes_at in GOTU.
pose proof (wmono_refl asegs mc) as WM. pose proof (munch_refl [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6444156, 6444160)] mc) as MU.
unfold jhdr_cells in SRC, QX. cbn [app fn_ud_to_json_string fn_free_userdata A4F] in SRC, QX.
lazymatch type of SCR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) => change (c0 :: c1 :: c2 :: c3 :: c4 :: rest) with ([c0; c1; c2; c3] ++ ([c4] ++ rest)) in SCR end.
destruct (proj1 (rw_cells_app asegs mc _ _ _) SCR) as [SCRa SCRx]. cbn [cells_size csize Nat.add] in SCRx.
destruct (proj1 (rw_cells_app asegs mc _ _ _) SCRx) as [SCR40 SCRb]. cbn [cells_size Nat.add] in SCRb. rewrite C40 in SCRb.
replace (bv_unsigned sp + -192 + Z.of_nat 40 + Z.of_nat (8 + 0)) with (bv_unsigned sp + -144) in SCRb by lia.
replace (bv_unsigned sp + -192 + Z.of_nat 40) with (bv_unsigned sp + -152) in SCR40 by lia.
stash SCR40. stash SCR. clear SCRx.
stash JRc. clear INV. stash PRESi. stash Gi. stash USTR. stash CBk.
unfold A_TP. a4l.
reenterA asegs A4L HIx asegs_wx HP.
step. step. step. if_lit.
step. step. ub_resolve.
asan_chkA.
step. step. asan_chkM 1.
step. step. step. if_truex.
step. if_falsex.
step. step. ub_resolve.
step. asan_chkA.
step. step. step. step.
if_lit. step. step. step. if_lit.
step.

unstash USTR.
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP) as (errs & ERRs).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => constr_eq mx mc end.
evt_done5.
eapply OBL_STRDUP_NF with (u := UWpaid) (src := ud) (ab := ud) (nb := udn) (str := uds) (lo := lo) (errv := errs); [exact HP | .. ].
all: rewrite ?unsigned_lit by lia.
1: exact INu2. 1: lia. 1: lia. 1: exact USTR. 1: exact NNu. 1: lia.
1: exact STi.
1: exact LO. 1: cbn [hl_stack_A A4L]; lia. 1: clear - SPA; Z.div_mod_to_equations; lia. 1: lia.
1: exact ERRs. 1: reflexivity. 1: reflexivity. 1: exact I. 1: exact I. 1: exact BBs. 1: cbn [uw_cost]; lia.
intros ms2 m2 md2 A2 rd e2 RS2 VM2 ST2 HPR2 ERR2 Hrd SDUP HP2. open_ret RS2.
rewrite ?(unsigned_lit (bv_unsigned sp + -192)) in ST2 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -192)) in HPR2 by lia.
change (hl_segs A4L) with asegs in *. cbn [uw_cost] in HP2.

assert (HPRX : forall A0 cs0, rw_cells asegs mc A0 cs0 ->
client_range A4H ((BS ++ [(q, 48)] ++ REM ++ LB) ++ LM ++ fr_ivs A4L ((Fr, 1) :: FRS)) (bv_unsigned sp + -192) A0 (Z.of_nat (cells_size cs0)) -> rw_cells asegs m2 A0 cs0).
{ intros A0 cs0 H1 H2. exact (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2 H1 H2). }
unstash SCR. apply HPRX in SCR; [| left; lia]. stash SCR.
clear SCRa SCRb SCR40.
apply HPRX in SAVEi; [| left; lia].
apply HPRX in FF.
2: { eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; left; reflexivity | cbn [fr_base fst]; lia |].
cbn [fr_base fr_class fst snd]. rewrite fr_size_1. change (cells_size (C8 w0 :: frest)) with (8 + cells_size frest)%nat. rewrite Nat2Z.inj_add, FFsz. lia. }
apply HPRX in FSH; [| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; right; left; reflexivity | unfold shad; cbn [fr_base fst hl_sb A4L]; unfold A_SB; fold sh; lia
| unfold shad; cbn [cells_size csize Nat.add fr_base fr_class fst snd hl_sb A4L]; rewrite fr_shadow_len_1; unfold A_SB; fold sh; lia]].
apply HPRX in SRC; [| eapply client_range_block; [apply in_or_app; left; exact INp2 | lia | cbn [cells_size csize Nat.add]; lia]].
apply HPRX in QX; [| eapply client_range_block; [apply in_or_app; left; exact INq2 | lia | cbn [cells_size csize Nat.add]; lia]].
pose proof (dc_dst_pres _ _ _ _ _ _ _ _ _ _ _ HP (conj DC DSH) HPR2) as DD2.
clear HPRX DC DSH.

assert (INp3 : In (p, 48) ((rd, Z.of_nat (length uds) + 1) :: BS ++ [(q, 48)] ++ REM ++ LB)) by (right; exact INp2).
assert (INq3 : In (q, 48) ((rd, Z.of_nat (length uds) + 1) :: BS ++ [(q, 48)] ++ REM ++ LB)) by (right; exact INq2).
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p 48 3 HP2 INp3 ltac:(lia) ltac:(lia)) as SHp3'.
replace (p / 8 + 2147450880 + 3) with (p / 8 + 2147450883) in SHp3' by lia.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ q 48 3 HP2 INq3 ltac:(lia) ltac:(lia)) as SHq3.
replace (q / 8 + 2147450880 + 3) with (q / 8 + 2147450883) in SHq3 by lia.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ q 48 4 HP2 INq3 ltac:(lia) ltac:(lia)) as SHq4.
replace (q / 8 + 2147450880 + 4) with (q / 8 + 2147450884) in SHq4 by lia.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 48 3 q 48 HP2 INq3 ltac:(cbn; lia) ltac:(apply in_or_app; left; exact INq3)) as SEPq3.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 48 4 q 48 HP2 INq3 ltac:(cbn; lia) ltac:(apply in_or_app; left; exact INq3)) as SEPq4.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ p 48 3 q 48 HP2 INp3 ltac:(cbn; lia) ltac:(apply in_or_app; left; exact INq3)) as SEPp3.
cbn [hl_sb hl_img_lo hl_img_hi hla_base A4L A4H] in SEPq3, SEPq4, SEPp3. unfold A_SB in SEPq3, SEPq4, SEPp3.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ rd _ HP2 ltac:(apply in_or_app; left; left; reflexivity)) as (_ & Hrdal & Hrdlo & Hrdhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hrdhi.
clear SHp3 SHp4 SHq1 MU WM MI GOTU.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI2. change (hl_segs A4L) with asegs in MI2.
pose proof (wmono_refl asegs m2) as WM2.
pose proof (munch_refl [(q, q + 48)] m2) as MU2.
stash SAVEi. stash FF. stash FSH. stash DD2. stash ST2. stash SDUP. stash HPR2. clear ERR2 ERRs.
replace (ret_pc (wz 662088)) with (wz 662088) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
reenterA asegs A4L HIx asegs_wx HP2.
step. if_falsex.
step. asan_chkA. stepz.
step. asan_chkA.
step. asan_chkA.
step. stepz. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mX end.
assert (HW : Forall (fun iv : Z * Z => exists a n, In (a, n) (((rd, Z.of_nat (length uds) + 1) :: BS ++ [(q, 48)] ++ REM ++ LB) ++ LM) /\ a <= fst iv /\ snd iv <= a + n) [(q, q + 48)]).
{ apply Forall_cons; [| apply Forall_nil]. exists q, 48. split; [apply in_or_app; left; exact INq3 | cbn [fst snd]; lia]. }
assert (MUw : munch ([(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 16); (6444156, 6444160)] ++ [(q, q + 48)]) m2 mX).
{ eapply munch_weaken; [| exact MU2]. clear. intros x Hx. cbn [app outside] in *. tauto. }
pose proof (fk1_HEAPA_W _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -104) _ _ HP2 LO ltac:(lia) HW MUw WM2 MI2) as HPY.

assert (NIq : ~ In (q, 48) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS)).
{ pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. rewrite <- !app_assoc in ND.
pose proof (nodup_mid_fresh BS [(q, 48)] (REM ++ LB ++ LM) q 48 48 ND ltac:(left; reflexivity)) as NI.
intros Hin. apply in_app_or in Hin as [Hin | Hin]; [apply NI; apply in_app_or in Hin as [Hin | Hin]; [apply in_or_app; left; exact Hin | apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hin] |].
apply in_app_or in Hin as [Hin | Hin]; [apply NI; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hin |].
eapply (dc_blk_notfr _ _ _ _ _ _ _ q 48 HP); [apply in_or_app; left; exact INq2 | lia | cbn [fr_ivs flat_map app]; right; right; exact Hin]. }
assert (HPR2X : heap_pres A4H ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -104) m2 mX).
{ eapply (fk1_pres_W _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -104) [(q, q + 48)] _ _ HP2 LO ltac:(lia)); [| | exact MUw | exact WM2].
- intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [left; apply in_or_app; left; right; apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; right; cbn [app]; apply in_or_app; right; exact Hb] |].
apply in_app_or in Hb as [Hb | Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb].
- apply Forall_cons; [| apply Forall_nil]. exists q, 48. split; [apply in_or_app; left; exact INq3 |]. split; [exact NIq | cbn [fst snd]; lia]. }

assert (DJ : forall A0 n0, (alloc_ceiling <= A0 \/ (Fr <= A0 /\ A0 + n0 <= Fr + 128) \/ (2147450880 <= A0 /\ A0 + n0 <= 17594333495296) \/ (D <= A0 /\ A0 + n0 <= D + 8)) -> disjoint_from [(q, q + 48)] A0 n0).
{ intros A0 n0 K. exact (dc_blkW_disj _ _ _ _ _ _ _ A0 n0 HP2 HW K). }
unstash SCR. apply (rw_cells_transport asegs [(q, q + 48)] _ mX) in SCR; [| exact MU2 | exact WM2 | apply DJ; left; lia].
unstash SAVEi. apply (rw_cells_transport asegs [(q, q + 48)] _ mX) in SAVEi; [| exact MU2 | exact WM2 | apply DJ; left; lia].
unstash FF. apply (rw_cells_transport asegs [(q, q + 48)] _ mX) in FF; [| exact MU2 | exact WM2 |].
2: { apply DJ; right; left. change (cells_size (C8 w0 :: frest)) with (8 + cells_size frest)%nat. rewrite Nat2Z.inj_add, FFsz. lia. }
unstash FSH. apply (rw_cells_transport asegs [(q, q + 48)] _ mX) in FSH; [| exact MU2 | exact WM2 | apply DJ; right; right; left; cbn [cells_size csize Nat.add]; lia].
unstash ST2. apply (stk_transport_disjoint asegs [(q, q + 48)] _ mX) in ST2; [| exact MU2 | exact WM2 | apply DJ; left; lia].
unstash DD2. pose proof (dc_dst_blkW _ _ _ _ _ _ _ _ _ _ HP2 HW MU2 WM2 DD2) as [DCX DSHX].
assert (Hrq : rd + (Z.of_nat (length uds) + 1) <= q \/ q + 48 <= rd).
{ assert (NE : rd <> q).
{ intros ->. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP2) as ND. cbn [app map] in ND. apply List.NoDup_cons_iff in ND as [Hni _].
apply Hni. apply (in_map blk_addr _ (q, 48)). apply in_or_app; left. exact INq2. }
exact (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ rd _ q 48 HP2 ltac:(apply in_or_app; left; left; reflexivity) ltac:(apply in_or_app; left; exact INq3) NE). }
unstash SDUP. apply (bytes_at_transport asegs [(q, q + 48)] _ mX) in SDUP; [| exact MU2 | cbn [disjoint_from]; rewrite length_app; cbn [length]; clear - Hrq; lia].

assert (INCL2 : forall b, In b ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) -> In b ((BS ++ [(q, 48)] ++ REM ++ LB) ++ LM ++ fr_ivs A4L ((Fr, 1) :: FRS))).
{ intros b Hb. apply in_app_or in Hb as [Hb | Hb].
- apply in_or_app; left. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; right; cbn [app]; apply in_or_app; right; exact Hb].
- apply in_or_app; right. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; cbn [fr_ivs flat_map app]; right; right; exact Hb]. }
unstash HPR2.
assert (HPRcX : heap_pres A4H ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) mc mX).
{ eapply heap_pres_trans; [eapply heap_pres_weaken; [exact HPR2 | lia | exact INCL2] | eapply heap_pres_weaken; [exact HPR2X | lia | intros b Hb; exact Hb]]. }
unstash JRc. unstash PRESi. unstash Gi.
pose proof (agree_of_heap_pres asegs A4H _ _ (BS ++ LB) _ _ HPRcX eq_refl ltac:(intros b Hb; apply in_or_app; left; exact Hb)) as AGcX.
pose proof (QrIB.Mq0.jroot_rep_agree A4H A4F _ _ _ _ _ _ JRc AGcX ltac:(apply incl_appl; apply incl_refl)) as JRX.
assert (INVX : dc_inv mX md2).
{ split; [eapply model_vm_only_trans; [exact VMi | exact VM2] |].
split; [eapply (QrIB.Mq0.presxD_trans A4H); [exact PRESi | apply (QrIB.Mq0.pres_presxD A4H); exact HPRcX] |].
split; [exact ST2 |]. split; [unfold dc_save; exact SAVEi |]. eapply lh_globA_client; [exact HPRcX | exact Gi]. }
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ rd _ HPY ltac:(apply in_or_app; left; left; reflexivity)) as (_ & _ & _ & _ & Hrdwr).
evt_done5.
eapply (dc_epi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 mX md2 A2 _ (BS ++ [(q, 48); (rd, Z.of_nat (length uds) + 1)] ++ REM ++ LB) Fr 0);
[ exact INVX | exact FS | exact FRM1 | eapply (heapA_perm A4L HIx); [exact HPY | perm | apply Permutation_refl | apply Permutation_refl]
| exact SCR | rewrite !cells_size_app; cbn [cells_size]; rewrite C40; reflexivity | exact FF | exact FFsz | exact FSH | exact JRX | ].
split; [cbn [charge bD]; lia |]. left. split; [reflexivity|]. exists (JRtree (Sdouble true)), q, [(q, 48); (rd, Z.of_nat (length uds) + 1)], REM.
split; [reflexivity|]. split; [rewrite Er; exists (Sdouble true); split; [reflexivity | lia] |].
split; [cbn [dc_cwA jtx]; rewrite Z.eqb_refl; eexists; split; [reflexivity | lia] |].
split; [exact Hq|]. split; [exact DCX|].
split; [| cbn [charge bB length Z.of_nat]; lia].
split; [exact Hq|]. cbn [jval]. exists 0, [], [(q, 48); (rd, Z.of_nat (length uds) + 1)]. split; [reflexivity|]. split; [left; split; reflexivity|].
exists bits', rd, (Z.of_nat (length uds) + 1), uds. split; [reflexivity|]. split; [lia|].
split; [unfold jhdr_cells; cbn [fn_ud_to_json_string fn_free_userdata A4F app]; exact QX |].
unfold cstr. split; [lia|]. split; [exact CNZ|]. exists []. rewrite app_nil_r.
pose proof (bytes_at_bound _ _ _ _ SDUP) as NB. rewrite length_app in NB. cbn [length] in NB.
split; [split; [cbn; split; [rewrite length_app; cbn [length]; lia | exact I] | cbn; rewrite app_nil_r; exact SDUP] |].
cbn [cells_size csize Nat.add]. replace (Z.of_nat (Z.to_nat (Z.of_nat (length uds) + 1) + 0)) with (Z.of_nat (length uds) + 1) by lia. exact Hrdwr.
Qed.
End MDcTail.
End RC__1.
End Mq9.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmZZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmZZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6WR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6WR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6WR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6WR.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrPc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrPc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvbw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvbw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYIF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYIF.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnCn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnCn.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QR2u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QR2u.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Quoa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Quoa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUr4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUr4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdgq_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXUB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXUB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRBl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJZd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJZd.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qw5U.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2Do.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2Do.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q30W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q30W.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSHS.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvmy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvmy. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qawr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qawr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qoif.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qoif.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section MJoVisit2.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Notation joptA := (jopt asegs A4F).
Notation wz := (Z_to_bv 64).
Notation VISx := (VIS HIx).

Lemma arr_now : forall A LBa LM FRS' B mc mdc R SP0 m BS p tojs pb a AL ps,
HEAPAx A LBa LM FRS' B mc mdc -> heap_pres A4H (LBa ++ R) SP0 m mc -> incl BS LBa -> In (p, 48) BS -> incl AL BS ->
rw_cells asegs m p (jhdr_cells JT_ARRAY 1 tojs pb 0 0 ++ [C8 (wz a)]) -> alist asegs A4F m AL a ps ->
exists arr size,
rw_cells asegs mc p (jhdr_cells JT_ARRAY 1 tojs pb 0 0 ++ [C8 (wz a)]) /\ 0 < p /\ p + 48 <= alloc_ceiling /\ p mod 8 = 0 /\
ro_cells asegs mc (p / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] /\
p / 8 + A_SB + 6 <= alloc_ceiling /\
alist asegs A4F mc [(a, AL_SZ); (arr, 8 * size)] a ps /\ al_blkA a arr size /\
ro_cells asegs mc (a / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] /\
bytes_at asegs mc (arr / 8 + A_SB) (shadow_bytes (8 * size)) /\ 0 <= size /\ arr / 8 + A_SB + size <= alloc_ceiling /\
Z.of_nat (length ps) <= size.
Proof.
intros A LBa LM FRS' B mc mdc R SP0 m BS p tojs pb a AL ps HP HPR INC INp INAL HDR HAL.
pose proof alloc_ceiling_range as ACR.
destruct (alist_open asegs A4F m AL a ps HAL) as (arr & size & junk & EAL & OP).
exists arr, size.
assert (INpA : In (p, 48) LBa) by (apply INC; exact INp).
assert (INaA : In (a, 32) LBa) by (apply INC, INAL; rewrite EAL; left; reflexivity).
assert (INrA : In (arr, 8 * size) LBa) by (apply INC, INAL; rewrite EAL; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p 48 HP ltac:(apply in_or_app; left; exact INpA)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a 32 HP ltac:(apply in_or_app; left; exact INaA)) as (_ & Haal & Halo & Hahi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ arr (8 * size) HP ltac:(apply in_or_app; left; exact INrA)) as (Hrn & Hral & Hrlo & Hrhi & _).
assert (AG : agree_on asegs BS m mc).
{ eapply (agree_of_heap_pres asegs A4H); [exact HPR | reflexivity |]. intros b Hb. apply in_or_app; left. apply INC; exact Hb. }
split.
{ eapply rw_cells_agree; [exact HDR | exact AG |]. exists p, 48. split; [exact INp|]. unfold jhdr_cells. cbn. lia. }
split; [exact Hplo|]. split; [exact Hphi|]. split; [clear - Hpal; Z.div_mod_to_equations; lia|].
split.
{ pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ p 48 HP INpA) as SH. unfold shad in SH. apply shadow_ro_cells in SH.
cbn [hl_sb hl_segs hla_base A4L A4H] in SH. exact SH. }
split; [unfold A_SB; clear - Hphi ACR Hplo; Z.div_mod_to_equations; lia|].
split.
{ rewrite EAL in HAL. eapply (alist_agree asegs A4F); [exact HAL | exact AG |]. intros b Hb. apply INAL. rewrite EAL. exact Hb. }
split.
{ unfold al_blkA. split; [exact Halo|]. split; [clear - Haal; Z.div_mod_to_equations; lia|]. split; [exact Hahi|]. split; [exact Hrlo|]. split; [clear - Hral; Z.div_mod_to_equations; lia | exact Hrhi]. }
split.
{ pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ a 32 HP INaA) as SH. unfold shad in SH. apply shadow_ro_cells in SH.
cbn [hl_sb hl_segs hla_base A4L A4H] in SH. exact SH. }
split.
{ pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ arr (8 * size) HP INrA) as SH. unfold shad in SH.
cbn [hl_sb hl_segs hla_base A4L A4H] in SH. exact SH. }
split; [lia|].
split; [unfold A_SB; clear - Hrhi ACR Hrlo Hrn; Z.div_mod_to_equations; lia|].
destruct OP as (_ & _ & _ & Hlen & Hsz). lia.
Qed.

Lemma jopt_now : forall R SP0 m mc LBa k bs v,
heap_pres A4H (LBa ++ R) SP0 m mc -> incl bs LBa -> joptA k m bs v -> joptA k mc bs v.
Proof.
intros R SP0 m mc LBa k bs v HPR INC JO.
eapply (jopt_agree asegs A4F bs m mc k bs v); [exact JO | | apply incl_refl].
eapply (agree_of_heap_pres asegs A4H); [exact HPR | reflexivity |]. intros b Hb. apply in_or_app; left. apply INC; exact Hb.
Qed.

Lemma own_chunks_pres : forall LBa LM FRS Fr SPc mc m' A cs,
heap_pres A4H (LBa ++ LM ++ fr_ivs A4L ((Fr, 0) :: FRS)) SPc mc m' -> rw_cells asegs mc A cs ->
(SPc <= A \/ (Fr <= A /\ A + Z.of_nat (cells_size cs) <= Fr + 56) \/ (Fr / 8 + 2147450880 <= A /\ A + Z.of_nat (cells_size cs) <= Fr / 8 + 2147450880 + 8)) ->
rw_cells asegs m' A cs.
Proof.
intros LBa LM FRS Fr SPc mc m' A cs HPR H D.
change asegs with (hl_segs A4H). eapply (heap_pres_rw_cells A4H); [exact HPR | exact H |].
destruct D as [D | [D | D]].
- left. exact D.
- eapply client_range_block with (a := Fr) (k := 56); [| lia | lia].
apply in_or_app; right. apply in_or_app; right. cbn [fr_ivs flat_map app]. left. reflexivity.
- eapply client_range_block with (a := Fr / 8 + 2147450880) (k := 8); [| lia | lia].
apply in_or_app; right. apply in_or_app; right. cbn [fr_ivs flat_map app]. right. left. reflexivity.
Qed.

Lemma arr_loop : forall (fuel : nat) (kids : list (option jshape)),
(forall k, In k kids -> VISx k) ->
forall (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(LBa BS LM : list blk) (FRS : list frame) (B : bud) (lo p pb a : Z) (AL : list blk) (ps : list Z) (KBS : list (list blk)),
alloc_ceiling <= lo -> lo <= bv_unsigned sp - (VIS_STK0 + VIS_STK1 * odepth (Some (Sarr kids))) -> bv_unsigned sp <= hiA_top A4L HIx ->
0 <= bv_unsigned sp < 2^64 -> bv_unsigned sp mod 16 = 0 ->
Z.of_nat (length FRS) + (1 + odepth (Some (Sarr kids))) < 4096 ->
(forall ms' md' m' (A' : ASA A4L HIx),
ret_state A4H ra sp gp (wz 6444320) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (wz 0) m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (LBa ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' ->
HEAPAx A' LBa LM FRS B m' md' ->
AJ5 A4L HIx A' T md' ms') ->
incl BS LBa -> In (p, 48) BS -> incl AL BS -> (forall bs, In bs KBS -> incl bs BS) ->
rw_cells asegs m p (jhdr_cells JT_ARRAY 1 (fn_arr_to_json_string A4F) pb 0 0 ++ [C8 (wz a)]) ->
alist asegs A4F m AL a ps -> length ps = length kids -> length KBS = length kids -> akids asegs A4F m kids ps KBS ->
Z.of_nat (length ps) < 2^44 ->
forall (ASP d Fr : Z) (mX : word -> option byte) (mdX : config) (AX : ASA A4L HIx) (j0 j32 jG jf1 jf2 : list byte) (w8 fw0 fw1 fw2 : word) (ii : Z)
(x0 x1 x2 x3 x4 x5 x6 x7 : byte) (uaw keyw parw : word) (xra xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
Z.of_nat (length ps) - ii <= Z.of_nat fuel -> 0 <= ii < Z.of_nat (length ps) ->
(d = 0 \/ d = 16) -> ASP = bv_unsigned sp + -160 - d ->
HEAPAx AX LBa LM ((Fr, 0) :: FRS) B mX mdX ->
model_vm_only (cfg_model md) (cfg_model mdX) ->
heap_pres A4H (LBa ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mX ->
stk asegs mX lo ASP ->
rw_cells asegs mX (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mX ASP [CB 8 j0; C8 w8; C8 (wz 7547); C8 (wz (Z.of_nat (length ps))); CB 16 j32; C8 (wz Fr)] ->
rw_cells asegs mX (ASP + 56) [CB (Z.to_nat d) jG] ->
rw_cells asegs mX Fr [C8 fw0; C8 fw1; C8 fw2; CB 8 jf1; C8 (wz ii); CB 16 jf2] ->
rw_cells asegs mX (Fr / 8 + 2147450880) [C1 x0; C1 x1; C1 x2; C1 x3; C1 x4; C1 x5; C1 x6; C1 x7] ->
AJ5 A4L HIx AX T mdX
(MS (mkR xra (wz ASP) gp (wz 6444320) xt0 xt1 xt2 sp (wz ASP) xa0 (wz ii) xa2 xa3 xa4 xa5 xa6 xa7
(wz Fr) (wz EMIT_A) uaw (wz p) (wz 2147450880) keyw parw (wz (Fr + 32)) (wz (Fr / 8 + 2147450880)) (wz Fr) xt3 xt4 xt5 xt6)
F (wz 0xa69a0) fc None mX (seg_rom asegs)).
Proof.
induction fuel as [|fuel IHf]; intros kids IH; intros until KBS; intros LO LOS HT SPR SPA FRN K INC INp INAL INK HDR HAL L1 L2 KIDS LEN44;
intros until xt6; intros Hfuel Hii Hd0 HASP HPX VMX HPRX STX SAVE SCR GAP FFX FSHX.
{ exfalso. lia. }
unfold VIS_STK0, VIS_STK1 in LOS.
pose proof alloc_ceiling_range as ACR.
assert (DN : 0 <= odepth (Some (Sarr kids))) by (cbn [odepth]; apply sdepth_nonneg).
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HPX INF) as (_ & HFal & HF0 & HFc & HFimg & _ & _ & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HPX INF) as HFapp.
rewrite fr_size_0 in HFal, HFc, HFimg, HFapp. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp. unfold A_SB in HFapp.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 8 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HPX) as MI. change (hl_segs A4L) with asegs in MI.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HPX) as (SB1 & SB2 & _ & _).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2.

destruct (arr_now _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPX HPRX INC INp INAL HDR HAL) as (arr & size & HDR1 & Hp0 & Hp48 & Hp8 & SHp1 & SHpb & AL1 & ALB & SHa1 & SHr1 & Hsz0 & SHrb & Hlen).
destruct (akids_nth asegs A4F m kids ps KBS (Z.to_nat ii) (al_nth ps ii) KIDS (al_nth_in ps ii ltac:(lia))) as (k & bs & Hk & Hbs & JO).
pose proof (nth_error_In kids (Z.to_nat ii) Hk) as KIN.
pose proof (Qdgq_c1.odepth_kid_arr kids k KIN) as DK.
pose proof (Qdgq_c1.odepth_nonneg k) as DNk.
assert (BSI : incl bs LBa) by (intros b Hb; apply INC; eapply INK; [eapply nth_error_In; exact Hbs | exact Hb]).
stash SAVE. stash GAP.
a4l.
pose proof (wmono_refl asegs mX) as WM. pose proof (munch_refl [(lo, ASP + 56); (Fr, Fr + 56); (sh, sh + 8)] mX) as MU.
reenterA asegs A4L HIx asegs_wx HPX.
bstep. bstep.

eapply evt_cut.
{ eapply jo_array_get_idx_A with (lo := lo) (sbcell := 991672) (p := p) (rc := 1) (a := a) (arr := arr) (size := size) (ps := ps) (i := ii).
- unfold small_pre, A_GOT_SB, A_SB. rewrite ?unsigned_lit by lia.
split; [assumption|]. split; [eassumption|]. split; [lia|]. split; [exact LO|]. split; [eassumption|]. split; [eassumption|]. lia.
- exact HDR1.
- lia.
- lia.
- exact Hp8.
- exact SHp1.
- exact SHpb.
- exact AL1.
- lia.
- exact ALB.
- exact SHa1.
- exact SHr1.
- exact Hsz0.
- exact SHrb. }
intros ms' (w1 & w2 & w3 & w4 & w5 & m' & -> & MUg & WMg & MIg & STg).
rewrite ?unsigned_lit in MUg, STg by lia.
rewrite (proj2 (Z.ltb_lt ii (Z.of_nat (length ps)))) by lia.
lazymatch type of MUg with munch _ ?mq _ =>
transport_after_call asegs mq m' MUg WMg; try match goal with H : mem_inv asegs mq |- _ => clear H end; clear MUg WMg end.
replace (ret_pc (wz 0xa69a8)) with (wz 0xa69a8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
clear AL1 SHp1 ALB Hsz0 SHrb SHpb Hlen.

do 6 bstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ mX mc, WMc : wmono asegs mX mc, MIc : mem_inv asegs mc |- _ =>
pose proof (vk_HEAPA HIx _ _ _ _ _ _ _ _ lo (ASP + 56) _ HPX LO ltac:(lia) MUc WMc MIc) as HPc;
pose proof (vk_pres HIx _ _ _ _ _ _ _ _ lo (ASP + 56) _ HPX LO ltac:(lia) MUc WMc) as HPRc;
unstash SAVE; unstash GAP;
apply (rw_cells_transport asegs [(lo, ASP + 56); (Fr, Fr + 56); (sh, sh + 8)] _ mc) in SAVE; [| exact MUc | exact WMc | cbn [disjoint_from]; simpl_sizes; lia];
apply (rw_cells_transport asegs [(lo, ASP + 56); (Fr, Fr + 56); (sh, sh + 8)] _ mc) in GAP; [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; lia]
end end.
assert (HPR0c : heap_pres A4H (LBa ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m').
{ eapply heap_pres_trans; [exact HPRX |]. eapply heap_pres_weaken; [exact HPRc | lia | intros b Hb; exact Hb]. }
pose proof (jopt_now _ _ _ _ _ _ _ _ HPR0c BSI JO) as JOc.
evt_done5.
eapply (IH k KIN) with (LBa := LBa) (BS := bs) (LM := LM) (FRS := (Fr, 0) :: FRS) (B := B) (lo := lo) (p := al_nth ps ii);
[ exact HPc | exact BSI | rewrite unsigned_lit by lia; exact STg | exact LO
| rewrite unsigned_lit by lia; unfold VIS_STK0, VIS_STK1; lia
| rewrite unsigned_lit by lia; clear - SPA HASP Hd0; Z.div_mod_to_equations; lia
| rewrite unsigned_lit by lia; lia
| reflexivity | rewrite unsigned_lit by lia; reflexivity
| exact JOc | cbn [length]; lia | reflexivity | reflexivity | ].
intros msr mdr mr Ar RSr VMr STr HPRr HPr.
rewrite unsigned_lit in STr, HPRr by lia.
open_ret RSr.
apply (own_chunks_pres _ _ _ _ _ _ _ _ _ HPRr) in SAVE; [| left; lia].
apply (own_chunks_pres _ _ _ _ _ _ _ _ _ HPRr) in SCR; [| left; lia].
apply (own_chunks_pres _ _ _ _ _ _ _ _ _ HPRr) in GAP; [| left; cbn [cells_size csize Nat.add]; lia].
apply (own_chunks_pres _ _ _ _ _ _ _ _ _ HPRr) in FFX; [| right; left; cbn [cells_size csize Nat.add]; lia].
apply (own_chunks_pres _ _ _ _ _ _ _ _ _ HPRr) in FSHX; [| right; right; fold sh; cbn [cells_size csize Nat.add]; lia].
assert (HPR0r : heap_pres A4H (LBa ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mr).
{ eapply heap_pres_trans; [exact HPR0c |]. eapply heap_pres_weaken; [exact HPRr | lia |].
intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. rewrite app_assoc. apply in_or_app. destruct Hb as [H|H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H]. }
assert (VM0r : model_vm_only (cfg_model md) (cfg_model mdr)) by (eapply model_vm_only_trans; [exact VMX | exact VMr]).
clear HPc HPRc HPR0c JOc MIg STg MU WM SB1 SB2 VMr HPRr.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HPr) as MIr. change (hl_segs A4L) with asegs in MIr.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HPr) as (SB1 & SB2 & _ & _).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2.
stash SAVE. stash GAP.
a4l.
pose proof (wmono_refl asegs mr) as WM. pose proof (munch_refl [(lo, ASP + 56); (Fr, Fr + 56); (sh, sh + 8)] mr) as MU.
reenterA asegs A4L HIx asegs_wx HPr.
bstep. bstep. bstep. if_lit.
bstep. if_lit.

bstep. bstep. bstep. bstep. bstep.
destruct (Z_lt_dec (ii + 1) (Z.of_nat (length ps))) as [LT | GE].
- if_falsex.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ mr mc, WMc : wmono asegs mr mc, MIc : mem_inv asegs mc |- _ =>
pose proof (vk_HEAPA HIx _ _ _ _ _ _ _ _ lo (ASP + 56) _ HPr LO ltac:(lia) MUc WMc MIc) as HPc;
pose proof (vk_pres HIx _ _ _ _ _ _ _ _ lo (ASP + 56) _ HPr LO ltac:(lia) MUc WMc) as HPRc;
unstash SAVE; unstash GAP;
apply (rw_cells_transport asegs [(lo, ASP + 56); (Fr, Fr + 56); (sh, sh + 8)] _ mc) in SAVE; [| exact MUc | exact WMc | cbn [disjoint_from]; simpl_sizes; lia];
apply (rw_cells_transport asegs [(lo, ASP + 56); (Fr, Fr + 56); (sh, sh + 8)] _ mc) in GAP; [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; lia]
end end.
evt_done5.
eapply (IHf kids IH ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md T LBa BS LM FRS B lo p pb a AL ps KBS LO ltac:(unfold VIS_STK0, VIS_STK1; lia) HT SPR SPA FRN K INC INp INAL INK HDR HAL L1 L2 KIDS LEN44
ASP d Fr _ mdr Ar _ _ jG _ _ _ _ _ _ (ii + 1));
[ lia | lia | exact Hd0 | exact HASP | exact HPc | exact VM0r
| eapply heap_pres_trans; [exact HPR0r | eapply heap_pres_weaken; [exact HPRc | lia | intros b Hb; exact Hb]]
| eassumption | exact SAVE | eassumption | exact GAP | eassumption | eassumption ].
- if_truex. bstep. bstepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ mr mc, WMc : wmono asegs mr mc, MIc : mem_inv asegs mc |- _ =>
pose proof (vk_HEAPA HIx _ _ _ _ _ _ _ _ lo (ASP + 56) _ HPr LO ltac:(lia) MUc WMc MIc) as HPc;
pose proof (vk_pres HIx _ _ _ _ _ _ _ _ lo (ASP + 56) _ HPr LO ltac:(lia) MUc WMc) as HPRc;
unstash SAVE; unstash GAP;
apply (rw_cells_transport asegs [(lo, ASP + 56); (Fr, Fr + 56); (sh, sh + 8)] _ mc) in SAVE; [| exact MUc | exact WMc | cbn [disjoint_from]; simpl_sizes; lia];
apply (rw_cells_transport asegs [(lo, ASP + 56); (Fr, Fr + 56); (sh, sh + 8)] _ mc) in GAP; [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; lia]
end end.
evt_done5.
eapply (vis_tail HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md T LBa LM FRS B lo LO ltac:(unfold VIS_STK0; lia) HT SPR K ASP d Fr _ mdr Ar);
[ exact Hd0 | exact HASP | exact HPc | exact VM0r
| eapply heap_pres_trans; [exact HPR0r | eapply heap_pres_weaken; [exact HPRc | lia | intros b Hb; exact Hb]]
| eassumption | exact SAVE | eassumption | reflexivity | exact GAP | eassumption | eassumption ].
Qed.

Lemma vis_arr : forall kids, (forall k, In k kids -> VISx k) -> VISx (Some (Sarr kids)).
Proof.
intros kids IH. unfold VIS. intros until p. intros HP INC ST LO LOS SPA HT TP RA JO FRN A0 A4 K.
destruct JO as [Hp J]. subst a0 a4 tp.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (DN : 0 <= odepth (Some (Sarr kids))) by (cbn [odepth]; apply sdepth_nonneg).
destruct (sarr_open asegs A4F kids m BS p 1 J) as (pb & PBS & a & AL & ps & KBS & EBS & OPB & HDR & HAL & L1 & L2 & KIDS).
assert (INp : In (p, 48) BS) by (rewrite EBS; apply in_or_app; left; left; reflexivity).
assert (INAL : incl AL BS) by (intros b Hb; rewrite EBS; apply in_or_app; left; right; apply in_or_app; left; exact Hb).
assert (INK : forall bs, In bs KBS -> incl bs BS).
{ intros bs Hbs b Hb. rewrite EBS. apply in_or_app; left; right. apply in_or_app; right. apply in_concat. exists bs. split; assumption. }
eapply vis_pro; [exact HP | exact ST | exact LO | unfold VIS_STK0, VIS_STK1 in *; lia | exact SPA | exact HT | reflexivity | lia |].
intros ASP d Fr m1 md1 A1 jA jG jf xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 Hd0 HASP HP1 VM1 HPR1 ST1 SAVE SCRA GAP FF FSH.
pose proof LOS as LOS'. unfold VIS_STK0, VIS_STK1 in LOS.
pose proof alloc_ceiling_range as ACR.
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as (_ & HFal & HF0 & HFc & HFimg & _ & _ & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFapp.
rewrite fr_size_0 in HFal, HFc, HFimg, HFapp. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp. unfold A_SB in HFapp.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 8 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI. change (hl_segs A4L) with asegs in MI.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP1) as (SB1 & SB2 & _ & _).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2.
destruct (arr_now _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP1 HPR1 INC INp INAL HDR HAL) as (arr & size & HDR1 & Hp0 & Hp48 & Hp8 & SHp1 & SHpb & AL1 & ALB & SHa1 & SHr1 & Hsz0 & SHrb & Hlen).
assert (LEN44 : Z.of_nat (length ps) < 2^44) by (destruct ALB as (_ & _ & _ & Hr0 & _ & Hrh); clear - Hlen Hr0 Hrh ACR; lia).
pose proof (proj1 (rw_cells_app asegs m1 p _ _) HDR1) as [HDRh _].
stash SAVE. stash GAP.
a4l.
pose proof (wmono_refl asegs m1) as WM. pose proof (munch_refl [(lo, ASP + 56); (Fr, Fr + 56); (sh, sh + 8)] m1) as MU.
reenterA asegs A4L HIx asegs_wx HP1.
do 6 bstep. bstep.
unfold EMIT_A. replace (ret_pc (wz 0x92a2c)) with (wz 0x92a2c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
bstep. bstep.
replace (ret_pc (wz 0xa6770)) with (wz 0xa6770) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
bstep. bstep. bstep. if_lit. bstep. bstep. if_lit. bstep. if_lit. bstep. bstep.

eapply evt_cut.
{ eapply jo_get_type_A with (lo := lo) (sbcell := 991672) (p := p) (ty := JT_ARRAY) (rc := 1).
- unfold small_pre, A_GOT_SB, A_SB. rewrite ?unsigned_lit by lia.
split; [assumption|]. split; [eassumption|]. split; [lia|]. split; [exact LO|]. split; [eassumption|]. split; [eassumption|]. lia.
- exact HDRh.
- lia.
- lia.
- exact Hp8.
- unfold JT_ARRAY; lia.
- apply (proj1 (ro_cells_app asegs m1 _ [C1 (Z_to_bv 8 0)] _) SHp1).
- unfold A_SB in *. lia. }
intros ms' (m' & (w & x & y & ->) & MUg & WMg & MIg & STg).
rewrite ?unsigned_lit in MUg, STg by lia.
lazymatch type of MUg with munch _ ?mq _ =>
transport_after_call asegs mq m' MUg WMg; try match goal with H : mem_inv asegs mq |- _ => clear H end; clear MUg WMg end.
replace (ret_pc (wz 0xa67b0)) with (wz 0xa67b0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
clear AL1 SHp1 ALB Hsz0 SHrb Hlen SHpb arr size.
unfold JT_ARRAY.
bstep. bstep. bstep. if_lit. bstep. bstep. if_lit. bstep.
bstep. bstep. if_lit. bstep. bstep. bstep.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m1 mc, WMc : wmono asegs m1 mc, MIc : mem_inv asegs mc |- _ =>
pose proof (vk_HEAPA HIx _ _ _ _ _ _ _ _ lo (ASP + 56) _ HP1 LO ltac:(lia) MUc WMc MIc) as HPc;
pose proof (vk_pres HIx _ _ _ _ _ _ _ _ lo (ASP + 56) _ HP1 LO ltac:(lia) MUc WMc) as HPRc end end.
assert (HPR0c : heap_pres A4H (LBa ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m0).
{ eapply heap_pres_trans; [exact HPR1 |]. eapply heap_pres_weaken; [exact HPRc | lia | intros b Hb; exact Hb]. }
destruct (arr_now _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPc HPR0c INC INp INAL HDR HAL) as (arr & size & HDR1 & _ & _ & _ & SHp1 & SHpb & AL1 & ALB & SHa1 & SHr1 & Hsz0 & SHrb & Hlen).
clear HPc HPRc HPR0c.
eapply evt_cut.
{ eapply jo_array_length_A with (lo := lo) (sbcell := 991672) (p := p) (rc := 1) (a := a) (arr := arr) (size := size) (ps := ps).
- unfold small_pre, A_GOT_SB, A_SB. rewrite ?unsigned_lit by lia.
split; [assumption|]. split; [eassumption|]. split; [lia|]. split; [exact LO|]. split; [eassumption|]. split; [eassumption|]. lia.
- exact HDR1.
- lia.
- lia.
- exact Hp8.
- exact SHp1.
- exact SHpb.
- exact AL1.
- exact ALB.
- exact SHa1. }
clear MIg STg. intros ms' (w1 & w2 & m'' & -> & MUg & WMg & MIg & STg).
rewrite ?unsigned_lit in MUg, STg by lia.
lazymatch type of MUg with munch _ ?mq _ =>
transport_after_call asegs mq m'' MUg WMg; try match goal with H : mem_inv asegs mq |- _ => clear H end; clear MUg WMg end.
replace (ret_pc (wz 0xa6964)) with (wz 0xa6964) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
clear AL1 SHp1 ALB Hsz0 SHrb SHpb Hlen.

bstepz. bstepz. bstep. bstep.
destruct (Z.eq_dec (Z.of_nat (length ps)) 0) as [LZ | LNZ].
-
rewrite LZ in *. if_lit. bstep. bstepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m1 mc, WMc : wmono asegs m1 mc, MIc : mem_inv asegs mc |- _ =>
pose proof (vk_HEAPA HIx _ _ _ _ _ _ _ _ lo (ASP + 56) _ HP1 LO ltac:(lia) MUc WMc MIc) as HPc;
pose proof (vk_pres HIx _ _ _ _ _ _ _ _ lo (ASP + 56) _ HP1 LO ltac:(lia) MUc WMc) as HPRc;
unstash SAVE; unstash GAP;
apply (rw_cells_transport asegs [(lo, ASP + 56); (Fr, Fr + 56); (sh, sh + 8)] _ mc) in SAVE; [| exact MUc | exact WMc | cbn [disjoint_from]; simpl_sizes; lia];
apply (rw_cells_transport asegs [(lo, ASP + 56); (Fr, Fr + 56); (sh, sh + 8)] _ mc) in GAP; [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; lia]
end end.
evt_done5.
eapply (vis_tail HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md T LBa LM FRS B lo LO ltac:(unfold VIS_STK0; lia) HT SPR K ASP d Fr _ md1 A1);
[ exact Hd0 | exact HASP | exact HPc | exact VM1
| eapply heap_pres_trans; [exact HPR1 | eapply heap_pres_weaken; [exact HPRc | lia | intros b Hb; exact Hb]]
| eassumption | exact SAVE | eassumption | reflexivity | exact GAP | eassumption | eassumption ].
- if_falsex. bstep. bstep. bstep. bstepz. bstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m1 mc, WMc : wmono asegs m1 mc, MIc : mem_inv asegs mc |- _ =>
pose proof (vk_HEAPA HIx _ _ _ _ _ _ _ _ lo (ASP + 56) _ HP1 LO ltac:(lia) MUc WMc MIc) as HPc;
pose proof (vk_pres HIx _ _ _ _ _ _ _ _ lo (ASP + 56) _ HP1 LO ltac:(lia) MUc WMc) as HPRc;
unstash SAVE; unstash GAP;
apply (rw_cells_transport asegs [(lo, ASP + 56); (Fr, Fr + 56); (sh, sh + 8)] _ mc) in SAVE; [| exact MUc | exact WMc | cbn [disjoint_from]; simpl_sizes; lia];
apply (rw_cells_transport asegs [(lo, ASP + 56); (Fr, Fr + 56); (sh, sh + 8)] _ mc) in GAP; [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; lia]
end end.
evt_done5.
eapply (arr_loop (S (length ps)) kids IH ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md T LBa BS LM FRS B lo p pb a AL ps KBS LO LOS' HT SPR SPA FRN K INC INp INAL INK HDR HAL L1 L2 KIDS LEN44
ASP d Fr _ md1 A1 _ _ jG _ _ _ _ _ _ 0);
[ lia | lia | exact Hd0 | exact HASP | exact HPc | exact VM1
| eapply heap_pres_trans; [exact HPR1 | eapply heap_pres_weaken; [exact HPRc | lia | intros b Hb; exact Hb]]
| eassumption | exact SAVE | eassumption | exact GAP | eassumption | eassumption ].
Qed.

Lemma gran4_now : forall A LBa LM FRS' B mc mdc a k e,
HEAPAx A LBa LM FRS' B mc mdc -> In (a, k) LBa -> a <= e -> e + 32 <= a + k -> e mod 8 = 0 ->
ro_cells asegs mc (e / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof.
intros A LBa LM FRS' B mc mdc a k e HP Hin Hlo Hhi He8.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP ltac:(apply in_or_app; left; exact Hin)) as (_ & Hal & _).
assert (E : forall i, 0 <= i -> e / 8 + 2147450880 + i = a / 8 + 2147450880 + ((e - a) / 8 + i)) by (intros i Hi; clear - Hal He8 Hlo; Z.div_mod_to_equations; lia).
assert (G : forall i, 0 <= i <= 3 -> ro_cells asegs mc (e / 8 + 2147450880 + i) [C1 (Z_to_bv 8 0)]).
{ intros i Hi. rewrite (E i) by lia. eapply (blk_gran0A HIx _ _ _ _ _ _ _ a k _ HP Hin); [clear - Hlo Hi; Z.div_mod_to_equations; lia | clear - Hal He8 Hlo Hhi Hi; Z.div_mod_to_equations; lia]. }
pose proof (G 0 ltac:(lia)) as G0. pose proof (G 1 ltac:(lia)) as G1. pose proof (G 2 ltac:(lia)) as G2. pose proof (G 3 ltac:(lia)) as G3.
rewrite Z.add_0_r in G0.
change [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] with ([C1 (Z_to_bv 8 0)] ++ [C1 (Z_to_bv 8 0)] ++ [C1 (Z_to_bv 8 0)] ++ [C1 (Z_to_bv 8 0)]).
apply ro_cells_app. split; [exact G0|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 1) with 1.
apply ro_cells_app. split; [exact G1|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 1) with 1.
apply ro_cells_app. split; [replace (e / 8 + 2147450880 + 1 + 1) with (e / 8 + 2147450880 + 2) by lia; exact G2|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 1) with 1.
replace (e / 8 + 2147450880 + 1 + 1 + 1) with (e / 8 + 2147450880 + 3) by lia. exact G3.
Qed.

Lemma obj_now : forall A LBa LM FRS' B mc mdc R SP0 m kids BS p pb0 PBS t TBS es KBS,
HEAPAx A LBa LM FRS' B mc mdc -> heap_pres A4H (LBa ++ R) SP0 m mc -> incl BS LBa ->
obj_view asegs A4F kids m BS p 1 pb0 PBS t TBS es KBS ->
obj_view asegs A4F kids mc BS p 1 pb0 PBS t TBS es KBS /\
0 < p /\ p + 48 <= alloc_ceiling /\ p mod 8 = 0 /\
ro_cells asegs mc (p / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] /\
p / 8 + A_SB + 6 <= alloc_ceiling /\
0 < t /\ t mod 8 = 0 /\ t + 56 <= alloc_ceiling /\
ro_cells asegs mc (t / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof.
intros A LBa LM FRS' B mc mdc R SP0 m kids BS p pb0 PBS t TBS es KBS HP HPR INC OV.
pose proof alloc_ceiling_range as ACR.
assert (AG : agree_on asegs BS m mc).
{ eapply (agree_of_heap_pres asegs A4H); [exact HPR | reflexivity |]. intros b Hb. apply in_or_app; left. apply INC; exact Hb. }
pose proof (obj_view_agree asegs A4F kids m mc BS p 1 pb0 PBS t TBS es KBS OV AG) as OVc.
destruct (obj_view_tbl asegs A4F kids m BS p 1 pb0 PBS t TBS es KBS OV) as [_ TINB].
assert (INp : In (p, 48) BS) by (destruct OV as (EBS & _); rewrite EBS; apply in_or_app; left; left; reflexivity).
assert (INpA : In (p, 48) LBa) by (apply INC; exact INp).
assert (INtA : In (t, 56) LBa) by (apply INC; exact TINB).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p 48 HP ltac:(apply in_or_app; left; exact INpA)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ t 56 HP ltac:(apply in_or_app; left; exact INtA)) as (_ & Htal & Htlo & Hthi & _).
split; [exact OVc|]. split; [exact Hplo|]. split; [exact Hphi|]. split; [clear - Hpal; Z.div_mod_to_equations; lia|].
split.
{ pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ p 48 HP INpA) as SH. unfold shad in SH. apply shadow_ro_cells in SH.
cbn [hl_sb hl_segs hla_base A4L A4H] in SH. exact SH. }
split; [unfold A_SB; clear - Hphi ACR Hplo; Z.div_mod_to_equations; lia|].
split; [exact Htlo|]. split; [clear - Htal; Z.div_mod_to_equations; lia|]. split; [exact Hthi|].
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ t 56 HP INtA) as SH. unfold shad in SH. apply shadow_ro_cells in SH.
cbn [hl_sb hl_segs hla_base A4L A4H] in SH. exact SH.
Qed.

Lemma ent_now : forall A LBa LM FRS' B mc mdc kids BS p pb0 PBS t TBS es KBS j e,
HEAPAx A LBa LM FRS' B mc mdc -> incl BS LBa ->
obj_view asegs A4F kids mc BS p 1 pb0 PBS t TBS es KBS -> nth_error es j = Some e ->
0 < oe_a e /\ oe_a e mod 8 = 0 /\ oe_a e + 32 <= alloc_ceiling /\
ro_cells asegs mc (oe_a e / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] /\
(exists pad : word, rw_cells asegs mc (oe_a e) [C8 (wz (oe_k e)); C4 (wz 0); C4 pad; C8 (wz (oe_v e)); C8 (wz (ohd (skipn (S j) es)))]) /\
exists k bs, nth_error kids j = Some k /\ nth_error KBS j = Some bs /\ incl bs BS /\ joptA k mc bs (oe_v e).
Proof.
intros A LBa LM FRS' B mc mdc kids BS p pb0 PBS t TBS es KBS j e HP INC OV He.
destruct (obj_view_entry asegs A4F kids mc BS p 1 pb0 PBS t TBS es KBS j e OV He) as (EA0 & EA8 & (ba & bk & Hin & Hlo & Hhi) & ENT & k & bs & Hk & Hbs & KOK).
assert (EBS : BS = ((p, 48) :: TBS ++ concat KBS) ++ PBS) by (destruct OV as (E & _); exact E).
assert (INbA : In (ba, bk) LBa) by (apply INC; rewrite EBS; apply in_or_app; left; right; apply in_or_app; left; exact Hin).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ ba bk HP ltac:(apply in_or_app; left; exact INbA)) as (_ & _ & _ & Hbhi & _).
split; [exact EA0|]. split; [exact EA8|]. split; [lia|].
split; [eapply (gran4_now _ _ _ _ _ _ _ ba bk (oe_a e) HP INbA); [exact Hlo | exact Hhi | exact EA8] |].
split; [exact ENT|].
exists k, bs. split; [exact Hk|]. split; [exact Hbs|]. split.
- intros b Hb. rewrite EBS. apply in_or_app; left; right. apply in_or_app; right. apply in_concat. exists bs. split; [eapply nth_error_In; exact Hbs | exact Hb].
- destruct k; exact KOK.
Qed.

Lemma obj_loop : forall (fuel : nat) (kids : list (option jshape)),
(forall k, In k kids -> VISx k) ->
forall (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(LBa BS LM : list blk) (FRS : list frame) (B : bud) (lo p pb0 t : Z) (PBS TBS : list blk) (es : list oent) (KBS : list (list blk)),
alloc_ceiling <= lo -> lo <= bv_unsigned sp - (VIS_STK0 + VIS_STK1 * odepth (Some (Sobj kids))) -> bv_unsigned sp <= hiA_top A4L HIx ->
0 <= bv_unsigned sp < 2^64 -> bv_unsigned sp mod 16 = 0 ->
Z.of_nat (length FRS) + (1 + odepth (Some (Sobj kids))) < 4096 ->
(forall ms' md' m' (A' : ASA A4L HIx),
ret_state A4H ra sp gp (wz 6444320) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (wz 0) m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (LBa ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' ->
HEAPAx A' LBa LM FRS B m' md' ->
AJ5 A4L HIx A' T md' ms') ->
incl BS LBa -> obj_view asegs A4F kids m BS p 1 pb0 PBS t TBS es KBS ->
forall (ASP d Fr : Z) (mX : word -> option byte) (mdX : config) (AX : ASA A4L HIx) (j0 j16 j32 jG jf : list byte) (w8 w24 fw0 fw1 fw2 : word)
(x0 x1 x2 x3 x4 x5 x6 x7 : byte) (j : nat) (e : oent) (uaw keyw parw : word) (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
Z.of_nat (length es) - Z.of_nat j <= Z.of_nat fuel -> nth_error es j = Some e ->
(d = 0 \/ d = 16) -> ASP = bv_unsigned sp + -160 - d ->
HEAPAx AX LBa LM ((Fr, 0) :: FRS) B mX mdX ->
model_vm_only (cfg_model md) (cfg_model mdX) ->
heap_pres A4H (LBa ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mX ->
stk asegs mX lo ASP ->
rw_cells asegs mX (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mX ASP [CB 8 j0; C8 w8; CB 8 j16; C8 w24; CB 16 j32; C8 (wz Fr)] ->
rw_cells asegs mX (ASP + 56) [CB (Z.to_nat d) jG] ->
rw_cells asegs mX Fr [C8 fw0; C8 fw1; C8 fw2; CB 32 jf] ->
rw_cells asegs mX (Fr / 8 + 2147450880) [C1 x0; C1 x1; C1 x2; C1 x3; C1 x4; C1 x5; C1 x6; C1 x7] ->
AJ5 A4L HIx AX T mdX
(MS (mkR xra (wz ASP) gp (wz 6444320) xt0 xt1 xt2 sp (wz ASP) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
(wz Fr) (wz EMIT_A) uaw (wz p) (wz 2147450880) keyw parw (wz (oe_a e)) (wz (Fr / 8 + 2147450880)) (wz Fr) xt3 xt4 xt5 xt6)
F (wz 0xa68cc) fc None mX (seg_rom asegs)).
Proof.
induction fuel as [|fuel IHf]; intros kids IH; intros until KBS; intros LO LOS HT SPR SPA FRN K INC OV;
intros until xt6; intros Hfuel He Hd0 HASP HPX VMX HPRX STX SAVE SCR GAP FFX FSHX.
{ exfalso. assert (L : (j < length es)%nat) by (apply nth_error_Some; congruence). lia. }
unfold VIS_STK0, VIS_STK1 in LOS.
pose proof alloc_ceiling_range as ACR.
assert (DN : 0 <= odepth (Some (Sobj kids))) by (cbn [odepth]; apply sdepth_nonneg).
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HPX INF) as (_ & HFal & HF0 & HFc & HFimg & _ & _ & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HPX INF) as HFapp.
rewrite fr_size_0 in HFal, HFc, HFimg, HFapp. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp. unfold A_SB in HFapp.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 8 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HPX) as MI. change (hl_segs A4L) with asegs in MI.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HPX) as (SB1 & SB2 & _ & _).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2.

destruct (obj_now _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPX HPRX INC OV) as (OVX & _).
destruct (ent_now _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPX INC OVX He) as (E0 & E8 & E32 & SHe & (pad & ENT) & k & bs & Hk & Hbs & BSI0 & JOX).
pose proof (nth_error_In kids j Hk) as KIN.
pose proof (Qdgq_c1.odepth_kid_obj kids k KIN) as DK.
pose proof (Qdgq_c1.odepth_nonneg k) as DNk.
assert (BSI : incl bs LBa) by (intros b Hb; apply INC, BSI0; exact Hb).
stash SAVE. stash GAP.
a4l.
pose proof (wmono_refl asegs mX) as WM. pose proof (munch_refl [(lo, ASP + 56); (Fr, Fr + 56); (sh, sh + 8)] mX) as MU.
reenterA asegs A4L HIx asegs_wx HPX.
ub_skip. asan_chk0.
bstep. asan_chkA.
bstep. asan_chkA.
bstep. bstep. bstep.
do 4 bstep. bstep.
unstash SAVE. unstash GAP.
evt_done5.
eapply (IH k KIN) with (LBa := LBa) (BS := bs) (LM := LM) (FRS := (Fr, 0) :: FRS) (B := B) (lo := lo) (p := oe_v e);
[ exact HPX | exact BSI | rewrite unsigned_lit by lia; exact STX | exact LO
| rewrite unsigned_lit by lia; unfold VIS_STK0, VIS_STK1; lia
| rewrite unsigned_lit by lia; clear - SPA HASP Hd0; Z.div_mod_to_equations; lia
| rewrite unsigned_lit by lia; lia
| reflexivity | rewrite unsigned_lit by lia; reflexivity
| exact JOX | cbn [length]; lia | reflexivity | reflexivity | ].
intros msr mdr mr Ar RSr VMr STr HPRr HPr.
rewrite unsigned_lit in STr, HPRr by lia.
open_ret RSr.
apply (own_chunks_pres _ _ _ _ _ _ _ _ _ HPRr) in SAVE; [| left; lia].
apply (own_chunks_pres _ _ _ _ _ _ _ _ _ HPRr) in SCR; [| left; lia].
apply (own_chunks_pres _ _ _ _ _ _ _ _ _ HPRr) in GAP; [| left; cbn [cells_size csize Nat.add]; lia].
apply (own_chunks_pres _ _ _ _ _ _ _ _ _ HPRr) in FFX; [| right; left; cbn [cells_size csize Nat.add]; lia].
apply (own_chunks_pres _ _ _ _ _ _ _ _ _ HPRr) in FSHX; [| right; right; fold sh; cbn [cells_size csize Nat.add]; lia].
assert (HPR0r : heap_pres A4H (LBa ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mr).
{ eapply heap_pres_trans; [exact HPRX |]. eapply heap_pres_weaken; [exact HPRr | lia |].
intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. rewrite app_assoc. apply in_or_app. destruct Hb as [H|H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H]. }
assert (VM0r : model_vm_only (cfg_model md) (cfg_model mdr)) by (eapply model_vm_only_trans; [exact VMX | exact VMr]).
clear MI SB1 SB2 OVX SHe ENT JOX WM MU VMr HPRr.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HPr) as MIr. change (hl_segs A4L) with asegs in MIr.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HPr) as (SB1 & SB2 & _ & _).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2.
destruct (obj_now _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPr HPR0r INC OV) as (OVr & _).
rewrite (ohd_skipn es (S j)).
a4l.
pose proof (wmono_refl asegs mr) as WM. pose proof (munch_refl [(lo, ASP + 56); (Fr, Fr + 56); (sh, sh + 8)] mr) as MU.
destruct (nth_error es (S j)) as [e'|] eqn:He'.
- destruct (ent_now _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPr INC OVr He') as (E0' & E8' & E32' & _).
clear OVr.
reenterA asegs A4L HIx asegs_wx HPr.
bstep. bstep. bstep. if_lit. bstep. if_lit. bstep. if_falsex.
evt_done5.
eapply (IHf kids IH ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md T LBa BS LM FRS B lo p pb0 t PBS TBS es KBS LO ltac:(unfold VIS_STK0, VIS_STK1; lia) HT SPR SPA FRN K INC OV
ASP d Fr _ mdr Ar _ _ _ jG _ _ _ _ _ _ _ _ _ _ _ _ _ _ (S j) e');
[ lia | exact He' | exact Hd0 | exact HASP | exact HPr | exact VM0r | exact HPR0r
| eassumption | exact SAVE | eassumption | exact GAP | eassumption | eassumption ].
- clear OVr.
reenterA asegs A4L HIx asegs_wx HPr.
bstep. bstep. bstep. if_lit. bstep. if_lit. bstep. if_lit.
evt_done5.
eapply (vis_tail HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md T LBa LM FRS B lo LO ltac:(unfold VIS_STK0; lia) HT SPR K ASP d Fr _ mdr Ar);
[ exact Hd0 | exact HASP | exact HPr | exact VM0r | exact HPR0r
| eassumption | exact SAVE | eassumption | reflexivity | exact GAP | eassumption | eassumption ].
Qed.

Lemma vis_obj : forall kids, (forall k, In k kids -> VISx k) -> VISx (Some (Sobj kids)).
Proof.
intros kids IH. unfold VIS. intros until p. intros HP INC ST LO LOS SPA HT TP RA JO FRN A0 A4 K.
destruct JO as [Hp J]. subst a0 a4 tp.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (DN : 0 <= odepth (Some (Sobj kids))) by (cbn [odepth]; apply sdepth_nonneg).
assert (POS : forall a n, In (a, n) BS -> 0 < a /\ a mod 16 = 0).
{ intros b n Hb. pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ b n HP ltac:(apply in_or_app; left; apply INC; exact Hb)) as (_ & Hal & Hlo & _). split; assumption. }
destruct (jval_obj_view asegs A4F kids m BS p 1 J POS) as (pb0 & PBS & t & TBS & es & KBS & OV).
eapply vis_pro; [exact HP | exact ST | exact LO | unfold VIS_STK0, VIS_STK1 in *; lia | exact SPA | exact HT | reflexivity | lia |].
intros ASP d Fr m1 md1 A1 jA jG jf xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 Hd0 HASP HP1 VM1 HPR1 ST1 SAVE SCRA GAP FF FSH.
pose proof LOS as LOS'. unfold VIS_STK0, VIS_STK1 in LOS.
pose proof alloc_ceiling_range as ACR.
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as (_ & HFal & HF0 & HFc & HFimg & _ & _ & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFapp.
rewrite fr_size_0 in HFal, HFc, HFimg, HFapp. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp. unfold A_SB in HFapp.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 8 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI. change (hl_segs A4L) with asegs in MI.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP1) as (SB1 & SB2 & _ & _).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2.
destruct (obj_now _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP1 HPR1 INC OV) as (OV1 & Hp0 & Hp48 & Hp8 & SHp1 & SHpb & Ht0 & Ht8 & Ht56 & SHt1).
pose proof OV1 as (_ & _ & HDR1 & _).
pose proof (proj1 (rw_cells_app asegs m1 p _ _) HDR1) as [HDRh _].
stash SAVE. stash GAP.
a4l.
pose proof (wmono_refl asegs m1) as WM. pose proof (munch_refl [(lo, ASP + 56); (Fr, Fr + 56); (sh, sh + 8)] m1) as MU.
reenterA asegs A4L HIx asegs_wx HP1.
do 6 bstep. bstep.
unfold EMIT_A. replace (ret_pc (wz 0x92a2c)) with (wz 0x92a2c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
bstep. bstep.
replace (ret_pc (wz 0xa6770)) with (wz 0xa6770) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
bstep. bstep. bstep. if_lit. bstep. bstep. if_lit. bstep. if_lit. bstep. bstep.

eapply evt_cut.
{ eapply jo_get_type_A with (lo := lo) (sbcell := 991672) (p := p) (ty := JT_OBJECT) (rc := 1).
- unfold small_pre, A_GOT_SB, A_SB. rewrite ?unsigned_lit by lia.
split; [assumption|]. split; [eassumption|]. split; [lia|]. split; [exact LO|]. split; [eassumption|]. split; [eassumption|]. lia.
- exact HDRh.
- lia.
- lia.
- exact Hp8.
- unfold JT_OBJECT; lia.
- apply (proj1 (ro_cells_app asegs m1 _ [C1 (Z_to_bv 8 0)] _) SHp1).
- unfold A_SB in *. lia. }
intros ms' (m' & (w & x & y & ->) & MUg & WMg & MIg & STg).
rewrite ?unsigned_lit in MUg, STg by lia.
lazymatch type of MUg with munch _ ?mq _ =>
transport_after_call asegs mq m' MUg WMg; try match goal with H : mem_inv asegs mq |- _ => clear H end; clear MUg WMg end.
replace (ret_pc (wz 0xa67b0)) with (wz 0xa67b0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
clear OV1 SHp1 SHt1.
unfold JT_OBJECT.
bstep. bstep. bstep. if_lit. bstep. bstep. if_lit. bstep.
bstep. bstep. if_lit. bstep. bstep. if_lit. bstep. bstep.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m1 mc, WMc : wmono asegs m1 mc, MIc : mem_inv asegs mc |- _ =>
pose proof (vk_HEAPA HIx _ _ _ _ _ _ _ _ lo (ASP + 56) _ HP1 LO ltac:(lia) MUc WMc MIc) as HPc;
pose proof (vk_pres HIx _ _ _ _ _ _ _ _ lo (ASP + 56) _ HP1 LO ltac:(lia) MUc WMc) as HPRc end end.
assert (HPR0c : heap_pres A4H (LBa ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m0).
{ eapply heap_pres_trans; [exact HPR1 |]. eapply heap_pres_weaken; [exact HPRc | lia | intros b Hb; exact Hb]. }
destruct (obj_now _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPc HPR0c INC OV) as (OVc & _ & _ & _ & SHpc & _ & _ & _ & _ & SHtc).
pose proof OVc as (_ & _ & HDRc & _).
clear HPc HPRc HPR0c.
eapply evt_cut.
{ eapply jo_get_object_A with (lo := lo) (sbcell := 991672) (p := p) (rc := 1) (t := t).
- unfold small_pre, A_GOT_SB, A_SB. rewrite ?unsigned_lit by lia.
split; [assumption|]. split; [eassumption|]. split; [lia|]. split; [exact LO|]. split; [eassumption|]. split; [eassumption|]. lia.
- exact HDRc.
- lia.
- lia.
- exact Hp8.
- exact SHpc.
- exact SHpb. }
clear MIg STg. intros ms' (m'' & (w1 & x1 & y1 & ->) & MUg & WMg & MIg & STg).
rewrite ?unsigned_lit in MUg, STg by lia.
lazymatch type of MUg with munch _ ?mq _ =>
transport_after_call asegs mq m'' MUg WMg; try match goal with H : mem_inv asegs mq |- _ => clear H end; clear MUg WMg end.
replace (ret_pc (wz 0xa688c)) with (wz 0xa688c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
clear OVc.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m1 mc, WMc : wmono asegs m1 mc, MIc : mem_inv asegs mc |- _ =>
pose proof (vk_HEAPA HIx _ _ _ _ _ _ _ _ lo (ASP + 56) _ HP1 LO ltac:(lia) MUc WMc MIc) as HPc;
pose proof (vk_pres HIx _ _ _ _ _ _ _ _ lo (ASP + 56) _ HP1 LO ltac:(lia) MUc WMc) as HPRc end end.
assert (HPR0c : heap_pres A4H (LBa ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m'').
{ eapply heap_pres_trans; [exact HPR1 |]. eapply heap_pres_weaken; [exact HPRc | lia | intros b Hb; exact Hb]. }
destruct (obj_now _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPc HPR0c INC OV) as (OVc & _ & _ & _ & _ & _ & _ & _ & _ & SHtc).
pose proof (obj_view_head asegs A4F kids m'' BS p 1 pb0 PBS t TBS es KBS OVc) as HEAD.
unfold A_SB in SHtc.
bstep.
asan_chkA.
bstep.
assert (OHD : ohd es = match nth_error es 0%nat with Some x => oe_a x | None => 0 end) by (destruct es; reflexivity).
rewrite OHD in *. clear OHD.
bstep.
destruct (nth_error es 0%nat) as [e0|] eqn:He0.
- destruct (ent_now _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPc INC OVc He0) as (E0 & E8 & E32 & _).
clear HPc HPRc HPR0c OVc.
if_falsex. bstep. bstep. bstepz. bstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m1 mc, WMc : wmono asegs m1 mc, MIc : mem_inv asegs mc |- _ =>
pose proof (vk_HEAPA HIx _ _ _ _ _ _ _ _ lo (ASP + 56) _ HP1 LO ltac:(lia) MUc WMc MIc) as HPd;
pose proof (vk_pres HIx _ _ _ _ _ _ _ _ lo (ASP + 56) _ HP1 LO ltac:(lia) MUc WMc) as HPRd;
unstash SAVE; unstash GAP;
apply (rw_cells_transport asegs [(lo, ASP + 56); (Fr, Fr + 56); (sh, sh + 8)] _ mc) in SAVE; [| exact MUc | exact WMc | cbn [disjoint_from]; simpl_sizes; lia];
apply (rw_cells_transport asegs [(lo, ASP + 56); (Fr, Fr + 56); (sh, sh + 8)] _ mc) in GAP; [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; lia]
end end.
evt_done5.
eapply (obj_loop (S (length es)) kids IH ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md T LBa BS LM FRS B lo p pb0 t PBS TBS es KBS LO LOS' HT SPR SPA FRN K INC OV
ASP d Fr _ md1 A1 _ _ _ jG _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0%nat e0);
[ lia | exact He0 | exact Hd0 | exact HASP | exact HPd | exact VM1
| eapply heap_pres_trans; [exact HPR1 | eapply heap_pres_weaken; [exact HPRd | lia | intros b Hb; exact Hb]]
| eassumption | exact SAVE | eassumption | exact GAP | eassumption | eassumption ].
- clear HPc HPRc HPR0c OVc.
if_lit.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m1 mc, WMc : wmono asegs m1 mc, MIc : mem_inv asegs mc |- _ =>
pose proof (vk_HEAPA HIx _ _ _ _ _ _ _ _ lo (ASP + 56) _ HP1 LO ltac:(lia) MUc WMc MIc) as HPd;
pose proof (vk_pres HIx _ _ _ _ _ _ _ _ lo (ASP + 56) _ HP1 LO ltac:(lia) MUc WMc) as HPRd;
unstash SAVE; unstash GAP;
apply (rw_cells_transport asegs [(lo, ASP + 56); (Fr, Fr + 56); (sh, sh + 8)] _ mc) in SAVE; [| exact MUc | exact WMc | cbn [disjoint_from]; simpl_sizes; lia];
apply (rw_cells_transport asegs [(lo, ASP + 56); (Fr, Fr + 56); (sh, sh + 8)] _ mc) in GAP; [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; lia]
end end.
evt_done5.
eapply (vis_tail HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md T LBa LM FRS B lo LO ltac:(unfold VIS_STK0; lia) HT SPR K ASP d Fr _ md1 A1);
[ exact Hd0 | exact HASP | exact HPd | exact VM1
| eapply heap_pres_trans; [exact HPR1 | eapply heap_pres_weaken; [exact HPRd | lia | intros b Hb; exact Hb]]
| eassumption | exact SAVE | eassumption | reflexivity | exact GAP | eassumption | eassumption ].
Qed.

Theorem vis_all : forall s, VISx s.
Proof.
intros [s|]; [| apply vis_null].
induction s as [|u| |h|kids IHk|kids IHk] using jshape_ind2.
- apply vis_scalar; cbn; unfold JT_BOOLEAN, JT_OBJECT, JT_ARRAY; lia.
- apply vis_scalar; cbn; unfold JT_DOUBLE, JT_OBJECT, JT_ARRAY; lia.
- apply vis_scalar; cbn; unfold JT_INT, JT_OBJECT, JT_ARRAY; lia.
- apply vis_scalar; cbn; unfold JT_STRING, JT_OBJECT, JT_ARRAY; lia.
- apply vis_obj. intros [s'|] Hin; [apply IHk; exact Hin | apply vis_null].
- apply vis_arr. intros [s'|] Hin; [apply IHk; exact Hin | apply vis_null].
Qed.

Theorem json_c_visit_A : jo_visit_A_stmt HIx JCVISIT_A EMIT_A (16 + 176 + 4096) 176.
Proof.
unfold jo_visit_A_stmt. intros until errv. intros (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA) JO FRN A0 A1 A2 A3 K.
subst a0 a1 a2 a3 tp. word_range sp SPR. unfold JCVISIT_A, A_TP in *.
pose proof (Qdgq_c1.odepth_nonneg s) as DN.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof alloc_ceiling_range as ACR.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp + -16, bv_unsigned sp)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 16%nat ST.
do 7 bstep. bstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
assert (HP1 : HEAPAx A (BS ++ LB) LM FRS B m1 md) by (match goal with MIc : mem_inv asegs m1 |- _ => heap_nowA A4L HIx HP MU WM MIc end).
assert (HPR1 : heap_pres A4H ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m1).
{ eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; exact Hb | clia | solve_clientWA A4L HIx HP]. }
assert (JO1 : joptA s m1 BS p) by (eapply (jopt_now _ _ _ _ _ _ _ _ HPR1); [apply incl_appl, incl_refl | exact JO]).
evt_done5.
eapply (vis_all s) with (LBa := BS ++ LB) (BS := BS) (LM := LM) (FRS := FRS) (B := B) (lo := lo) (p := p);
[ exact HP1 | apply incl_appl, incl_refl | rewrite unsigned_lit by lia; eassumption | exact LO
| rewrite unsigned_lit by lia; unfold VIS_STK0, VIS_STK1; lia
| rewrite unsigned_lit by lia; clear - SPA; Z.div_mod_to_equations; lia
| rewrite unsigned_lit by lia; lia
| reflexivity | rewrite unsigned_lit by lia; reflexivity
| exact JO1 | exact FRN | reflexivity | reflexivity | ].
intros msr mdr mr Ar RSr VMr STr HPRr HPr.
rewrite unsigned_lit in STr, HPRr by lia.
open_ret RSr.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPRr) in FR; [| left; lia]. change (hl_segs A4H) with asegs in FR.
assert (HPR0r : heap_pres A4H ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mr).
{ eapply heap_pres_trans; [exact HPR1 |]. eapply heap_pres_weaken; [exact HPRr | lia | intros b Hb; exact Hb]. }
pose proof (jopt_now _ _ _ _ _ _ _ _ HPR0r ltac:(apply incl_appl, incl_refl) JO) as JOr.
clear HP1 HPR1 JO1 MU WM HPRr.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HPr) as MIr. cbn [hl_segs hla_base A4L A4H] in MIr.
pose proof (wmono_refl asegs mr) as WM. pose proof (munch_refl [(bv_unsigned sp + -16, bv_unsigned sp)] mr) as MU.
reenterA asegs A4L HIx asegs_wx HPr.
bstep. bstep. bstep. bstep. bstep. if_lit. bstep. if_lit.
bstep. bstep. bstep.
clear ST. release_frame FR STr (bv_unsigned sp).
evt_done5.
eapply (K _ mdr mr 0 Ar); [| reflexivity | exact JOr | exact HPr].
split; [tw_ret|]. split; [exact VMr|]. split; [exact STr|]. split.
- eapply heap_pres_weaken; [exact HPR0r | lia |]. intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; apply in_or_app; right; exact Hb | apply in_or_app; right; exact Hb].
- unfold A_ERRNO, A_TP. exact (heapA_errno A4L HIx _ _ _ _ _ _ _ HPr).
Qed.
End MJoVisit2.
End RC__1.
