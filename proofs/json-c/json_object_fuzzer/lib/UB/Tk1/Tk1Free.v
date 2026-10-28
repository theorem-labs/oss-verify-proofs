(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QRjH QHnV QCcH QfLs Q0Ek Qtgi QjDH Qsw7 QJjn QkMG QRUw QAyu QlCE Q6q3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM UC8c UPZI UG8z Uihm UhHQ U5Ki.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require TopUbTac.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Tk1 Require Tk1Tac Tk1Reset.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import QXup UEQM OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QRjH QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0.
Import UC8c.Mq0 Qsw7 QJjn QkMG QRUw UPZI.Mq4.
Import UhHQ U5Ki Tk1Reset.
Import TopUbTac Tk1Tac.
Import ListNotations. Unset Keyed Unification.
Open Scope Z_scope.
Import Q6q3.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section TokFreeTail.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Hypothesis PUT : put_stmt_P HIx.

Definition tkf_entry : Z := 138200.
Definition tkf_loop_pc : Z := 138204.

Definition tkf_frame (m : word -> option byte) (SP : Z) (junk : list byte) (s3v s2v s1v s0v rav : word) : Prop :=
rw_cells rsegs m SP [CB 8 junk; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].

Definition tkf_body_post (x2 gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(md : Model) (REST LB0 P : list blk) (SP : Z) (me mpre : word -> option byte) (lo : Z) (errv : word)
(q r pb depth : Z) (x : tscal) (levels : list tlevel) (i : nat) (junk : list byte) (s3v s2v s1v s0v rav : word)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) F' fc' x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
ms' = MS (mkR x1 x2 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F' (Z_to_bv 64 138216) fc' None m' (seg_rom rsegs) /\
fsaved F F' /\ (frm0 fc -> frm0 fc') /\
model_vm_only md md' /\
HEAPx A' REST m' md' /\
tstack rsegs m' q (lupd levels i lvl_reset) /\
rw_cells rsegs m' r (tok_cells pb depth q x) /\
tkf_frame m' SP junk s3v s2v s1v s0v rav /\
stk rsegs m' lo SP /\
heap_pres S4L LB0 (SP + 48) me m' /\
rw_cells rsegs m' (hl_tp S4L - 164) [C4 errv] /\
agree_on rsegs P mpre m'.

#[using="PUT"] Lemma tkf_body :
forall (i : nat) (x1 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m me : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (REST LB0 P : list blk) (SP lo : Z) (errv : word)
(q r pb depth : Z) (x : tscal) (levels : list tlevel) (l : tlevel) (junk : list byte) (s3v s2v s1v s0v rav : word),
nth_error levels i = Some l -> (i < 32)%nat -> length levels = 32%nat ->
HEAPx A (lvl_blocks l ++ REST) m md ->
REST = P ++ (r, 72) :: (q, 1024) :: LB0 ->
lvl_ok rsegs S4F m l ->
tstack rsegs m q levels ->
rw_cells rsegs m r (tok_cells pb depth q x) ->
tkf_frame m SP junk s3v s2v s1v s0v rav ->
stk rsegs m lo SP -> alloc_ceiling <= lo -> lo <= SP - RESET_STK ->
SP mod 16 = 0 -> SP + 48 <= hi_top S4L HIx -> 0 <= SP -> SP + 48 < 2^64 ->
heap_pres S4L LB0 (SP + 48) me m ->
rw_cells rsegs m (hl_tp S4L - 164) [C4 errv] ->
tp = Z_to_bv 64 (hl_tp S4L) ->
(forall ms' md', tkf_body_post (Z_to_bv 64 SP) gp tp (Z_to_bv 64 r) (Z_to_bv 64 (Z.of_nat i)) s2 (Z_to_bv 64 (-1)) s4 s5 s6 s7 s8 s9 s10 s11
F fc md REST LB0 P SP me m lo errv q r pb depth x levels i junk s3v s2v s1v s0v rav ms' md' ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR x1 (Z_to_bv 64 SP) gp tp t0 t1 t2 (Z_to_bv 64 r) (Z_to_bv 64 (Z.of_nat i))
a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (-1)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 tkf_loop_pc) fc None m (seg_rom rsegs)) md) T.
Proof.
intros until rav. intros Hl Hi LEN HP EREST LOK TS BLK FR ST LO LOS SPA HT SP0 SPR HPR ERR TP K.
subst tp.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
apply rz_evt; [exact MOK|]. unfold tkf_loop_pc.
bstep. bstep. bstep.
apply evt_RZ_done.
destruct LOK as [JO NM].
eapply (reset_level_cps HIx PUT i) with (l := l) (levels := levels) (P := P) (LB0 := LB0) (REST := REST) (lo := lo) (errv := errv)
(q := q) (r := r) (pb := pb) (depth := depth) (mxd := 32) (fl := 0) (x := x) (rc := 1) (me := m);
[ exact Hl | lia | lia | exact LEN | exact HP | exact EREST
| unfold put_pre; destruct (tl_cs l) as [s'|]; [destruct JO as [Hp J]; split; [exact Hp | split; [lia | exact J]] | exact JO]
| exact NM | exact TS | exact BLK
| rewrite unsigned_lit by lia; exact ST | exact LO | rewrite unsigned_lit by lia; exact LOS
| rewrite unsigned_lit by lia; exact SPA | rewrite unsigned_lit by lia; lia
| apply heap_pres_refl | exact ERR | rewrite unsigned_lit by lia; reflexivity | ].
intros ms2 md2 (m2 & A2 & rv & RS2 & VM2 & OUT2 & TS2 & TOK2 & ST2 & HPR2 & ERR2 & AG2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR2 by lia.
lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end.
apply K. unfold tkf_body_post.
exists m2, A2, F2, fc2. do 16 eexists.
split; [reflexivity|]. split; [exact FS2|]. split; [exact FRM2|]. split; [exact VM2|].
split; [destruct OUT2 as [(_ & H) | (s' & _ & Hrc & _)]; [exact H | exfalso; lia]|].
split; [exact TS2|]. split; [exact TOK2|].
split; [unfold tkf_frame in FR |- *; eapply (heap_pres_rw_cells S4L); [exact HPR2 | exact FR | left; cbn; lia]|].
split; [exact ST2|].
split; [eapply heap_pres_trans; [exact HPR | eapply heap_pres_weaken; [exact HPR2 | lia | intros b Hb; exact Hb]]|].
split; [exact ERR2 | exact AG2].
Qed.

Definition tkf_loop_post (x2 gp tp s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(md : Model) (BASE LB0 PBS : list blk) (SP : Z) (me mpre : word -> option byte) (lo : Z) (errv : word)
(q r pb depth : Z) (x : tscal) (levels : list tlevel) (i : nat) (junk : list byte) (s3v s2v s1v s0v rav : word)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) F' fc' levels' x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s1',
ms' = MS (mkR x1 x2 gp tp t0 t1 t2 s0 s1' a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F' (Z_to_bv 64 138224) fc' None m' (seg_rom rsegs) /\
fsaved F F' /\ (frm0 fc -> frm0 fc') /\
model_vm_only md md' /\
HEAPx A' BASE m' md' /\
length levels' = 32%nat /\
(forall j, (j <= i)%nat -> nth_error levels' j = Some lvl_reset) /\
(forall j, (i < j)%nat -> nth_error levels' j = nth_error levels j) /\
tstack rsegs m' q levels' /\
rw_cells rsegs m' r (tok_cells pb depth q x) /\
tkf_frame m' SP junk s3v s2v s1v s0v rav /\
stk rsegs m' lo SP /\
heap_pres S4L LB0 (SP + 48) me m' /\
rw_cells rsegs m' (hl_tp S4L - 164) [C4 errv] /\
agree_on rsegs PBS mpre m'.

#[using="PUT"] Lemma tkf_loop :
forall (i : nat) (x1 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m me : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (PBS LB0 : list blk) (SP lo : Z) (errv : word)
(q r pb depth : Z) (x : tscal) (levels : list tlevel) (junk : list byte) (s3v s2v s1v s0v rav : word),
(i < 32)%nat -> length levels = 32%nat ->
HEAPx A (lvblocks levels (S i) ++ PBS ++ (r, 72) :: (q, 1024) :: LB0) m md ->
(forall j l, nth_error levels j = Some l -> (j <= i)%nat -> lvl_ok rsegs S4F m l) ->
tstack rsegs m q levels ->
rw_cells rsegs m r (tok_cells pb depth q x) ->
tkf_frame m SP junk s3v s2v s1v s0v rav ->
stk rsegs m lo SP -> alloc_ceiling <= lo -> lo <= SP - RESET_STK ->
SP mod 16 = 0 -> SP + 48 <= hi_top S4L HIx -> 0 <= SP -> SP + 48 < 2^64 ->
heap_pres S4L LB0 (SP + 48) me m ->
rw_cells rsegs m (hl_tp S4L - 164) [C4 errv] ->
tp = Z_to_bv 64 (hl_tp S4L) ->
(forall ms' md', tkf_loop_post (Z_to_bv 64 SP) gp tp (Z_to_bv 64 r) s2 (Z_to_bv 64 (-1)) s4 s5 s6 s7 s8 s9 s10 s11
F fc md (PBS ++ (r, 72) :: (q, 1024) :: LB0) LB0 PBS SP me m lo errv q r pb depth x levels i junk s3v s2v s1v s0v rav ms' md' ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR x1 (Z_to_bv 64 SP) gp tp t0 t1 t2 (Z_to_bv 64 r) (Z_to_bv 64 (Z.of_nat i))
a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (-1)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 tkf_loop_pc) fc None m (seg_rom rsegs)) md) T.
Proof.
induction i as [|i IH]; intros until rav; intros Hi LEN HP LOK TS BLK FR ST LO LOS SPA HT SP0 SPR HPR ERR TP K.
-
destruct (nth_error levels 0) as [l|] eqn:Hl; [| apply nth_error_None in Hl; lia].
rewrite (lvblocks_S _ _ _ Hl) in HP. rewrite <- app_assoc in HP.
eapply (tkf_body 0) with (P := PBS); [exact Hl | lia | exact LEN | exact HP | rewrite lvblocks_0; reflexivity
| eapply LOK; [exact Hl | lia] | exact TS | exact BLK | exact FR | exact ST | exact LO | exact LOS | exact SPA | exact HT | exact SP0 | exact SPR | exact HPR | exact ERR | exact TP |].
intros ms1 md1 (m1 & A1 & F1 & fc1 & y1 & u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & -> & FS1 & FRM1 & VM1 & HP1 & TS1 & BLK1 & FR1 & ST1 & HPR1 & ERR1 & AG1).
pose proof (heap_model_ok _ _ _ _ _ _ HP1) as MOK1.
apply rz_evt; [exact MOK1|].
bstep. norm_w32. bstep. if_false.
apply evt_RZ_done. apply K. unfold tkf_loop_post.
exists m1, A1, F1, fc1, (lupd levels 0 lvl_reset). do 17 eexists.
split; [reflexivity|]. split; [exact FS1|]. split; [exact FRM1|]. split; [exact VM1|].
split; [rewrite lvblocks_0 in HP1; exact HP1|].
split; [rewrite lupd_length; exact LEN|].
split; [intros j Hj; replace j with 0%nat by lia; apply nth_error_lupd_eq; lia|].
split; [intros j Hj; apply nth_error_lupd_neq; lia|].
split; [exact TS1|]. split; [exact BLK1|]. split; [exact FR1|]. split; [exact ST1|]. split; [exact HPR1 |]. split; [exact ERR1|]. exact AG1.
-
destruct (nth_error levels (S i)) as [l|] eqn:Hl; [| apply nth_error_None in Hl; lia].
rewrite (lvblocks_S _ _ _ Hl) in HP. rewrite <- app_assoc in HP.
eapply (tkf_body (S i)) with (P := lvblocks levels (S i) ++ PBS); [exact Hl | lia | exact LEN | exact HP | rewrite <- app_assoc; reflexivity
| eapply LOK; [exact Hl | lia] | exact TS | exact BLK | exact FR | exact ST | exact LO | exact LOS | exact SPA | exact HT | exact SP0 | exact SPR | exact HPR | exact ERR | exact TP |].
intros ms1 md1 (m1 & A1 & F1 & fc1 & y1 & u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & -> & FS1 & FRM1 & VM1 & HP1 & TS1 & BLK1 & FR1 & ST1 & HPR1 & ERR1 & AG1).
pose proof (heap_model_ok _ _ _ _ _ _ HP1) as MOK1.
apply rz_evt; [exact MOK1|].
bstep. norm_w32. bstep. if_truex.
replace (Z.of_nat (S i) + -1) with (Z.of_nat i) by lia.
apply evt_RZ_done.
eapply (IH _ gp tp _ _ _ _ _ _ _ _ _ _ _ s2 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F1 fc1 m1 me md1 T A1 PBS LB0 SP lo errv q r pb depth x (lupd levels (S i) lvl_reset));
[lia | rewrite lupd_length; exact LEN | rewrite lvblocks_lupd_ge by lia; exact HP1 | | exact TS1 | exact BLK1 | exact FR1 | exact ST1 | exact LO | exact LOS | exact SPA | exact HT | exact SP0 | exact SPR | exact HPR1 | exact ERR1 | exact TP |].
+ intros j l' Hj Hji. rewrite nth_error_lupd_neq in Hj by lia.
eapply lvl_ok_agree; [eapply LOK; [exact Hj | lia] | exact AG1 | apply incl_appl; eapply incl_tran; [| eapply lvblocks_incl; [exact Hj | lia]]; unfold lvl_blocks; apply incl_appl; apply incl_refl].
+ intros ms2 md2 (m2 & A2 & F2 & fc2 & levels2 & y1' & u0' & u1' & u2' & w0 & v1' & v2' & v3' & v4' & v5' & v6' & v7' & u3' & u4' & u5' & u6' & s1' & -> & FS2 & FRM2 & VM2 & HP2 & LEN2 & RES2 & SAME2 & TS2 & BLK2 & FR2 & ST2 & HPR2 & ERR2 & AG2).
apply K. unfold tkf_loop_post.
exists m2, A2, F2, fc2, levels2. do 17 eexists.
split; [reflexivity|]. split; [eapply fsaved_trans; [exact FS1 | exact FS2]|]. split; [intros Hf; apply FRM2, FRM1, Hf|].
split; [eapply model_vm_only_trans; [exact VM1 | exact VM2]|].
split; [exact HP2|]. split; [exact LEN2|].
split. { intros j Hj. destruct (PeanoNat.Nat.eq_dec j (S i)) as [->|NE]; [| apply RES2; lia]. rewrite SAME2 by lia. apply nth_error_lupd_eq. lia. }
split. { intros j Hj. rewrite SAME2 by lia. apply nth_error_lupd_neq. lia. }
split; [exact TS2|]. split; [exact BLK2|]. split; [exact FR2|]. split; [exact ST2|]. split; [exact HPR2 |]. split; [exact ERR2|].
eapply agree_on_trans; [eapply agree_on_incl; [exact AG1 | apply incl_appr; apply incl_refl] | exact AG2].
Qed.

Definition tkf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (rv : word)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z) (errv : word)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx),
ret_statew S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc rv m' ms' /\
model_vm_only md md' /\
stk rsegs m' lo (bv_unsigned sp) /\
heap_pres S4L LB (bv_unsigned sp) m m' /\
rw_cells rsegs m' (hl_tp S4L - 164) [C4 errv] /\
HEAPx A' LB m' md'.

#[using="PUT"] Lemma tokfree_tail_cps :
forall (x1 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 rv s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB BS : list blk) (tk SP lo : Z) (errv : word)
(q pb depth : Z) (PBS : list blk) (levels : list tlevel) (x : tscal)
(junk : list byte) (s3v s2v s1v s0v rav : word),
HEAPx A (BS ++ LB) m md ->
tokrep_with rsegs S4F m BS tk q pb depth PBS levels x ->
tkf_frame m SP junk s3v s2v s1v s0v rav ->
stk rsegs m lo SP -> alloc_ceiling <= lo -> lo <= SP - RESET_STK ->
SP mod 16 = 0 -> SP + 48 <= hi_top S4L HIx -> 0 <= SP -> SP + 48 < 2^64 ->
rw_cells rsegs m (hl_tp S4L - 164) [C4 errv] ->
tp = Z_to_bv 64 (hl_tp S4L) ->
(forall ms' md', tkf_post rav (Z_to_bv 64 (SP + 48)) gp tp s0v s1v s2v s3v s4 s5 s6 s7 s8 s9 s10 s11 F fc rv m md LB lo errv ms' md' ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR x1 (Z_to_bv 64 SP) gp tp t0 t1 t2 (Z_to_bv 64 tk) (Z_to_bv 64 depth) a0 a1 a2 a3 a4 a5 a6 a7
rv s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 tkf_entry) fc None m (seg_rom rsegs)) md) T.
Proof.
intros until rav. intros HP TOKR FR ST LO LOS SPA HT SP0 SPR ERR TP K.
unfold RESET_STK, put_stk_P in LOS. unfold_consts.
destruct TOKR as (EBS & LEN & Hd & TOK & PB & Hpb & TS & LOK & CLEAN).
subst BS.
set (dn := Z.to_nat depth).
assert (PCV : Permutation (concat (map lvl_blocks levels)) (lvblocks levels (S dn))).
{ rewrite <- (lvblocks_trunc levels (S dn) ltac:(intros jj ll Hj Hkj; eapply CLEAN; [exact Hj | lia]) 32) by lia.
apply lvblocks_all. lia. }
assert (HP0 : HEAPx A (lvblocks levels (S dn) ++ PBS ++ (tk, 72) :: (q, 1024) :: LB) m md).
{ eapply heap_perm; [exact HP|].
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
pose proof (heap_model_ok _ _ _ _ _ _ HP0) as MOK.
apply rz_evt; [exact MOK|]. unfold tkf_entry.
bstep.
replace (Z_to_bv 64 depth) with (Z_to_bv 64 (Z.of_nat dn)) by (f_equal; unfold dn; lia).
apply evt_RZ_done.
eapply (tkf_loop dn _ gp _ _ _ _ _ _ _ _ _ _ _ _ rv s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m m md T A PBS LB SP lo errv q tk pb depth x levels junk s3v s2v s1v s0v rav);
[ lia | lia | exact HP0 | intros j l Hj Hji; eapply LOK; [exact Hj | lia] | exact TS | exact TOK | exact FR | exact ST | exact LO
| unfold RESET_STK, put_stk_P; lia
| exact SPA | exact HT | exact SP0 | exact SPR | apply heap_pres_refl | exact ERR | exact TP | ].
intros ms1 md1 (m1 & A1 & F1 & fc1 & levels1 & y1 & u0 & u1 & u2 & w0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & s1' & -> & FS1 & FRM1 & VM1 & HP1 & LEN1 & RES1 & SAME1 & TS1 & TOK1 & FR1 & ST1 & HPR1 & ERR1 & AG1).
clear TS TOK FR ST HP0 MOK.
unfold tok_cells in TOK1. unfold tkf_frame in FR1. cbn [hl_tp S4L] in ERR1, TP.
pose proof PB as PB'. destruct PB' as (buf & bpos & size & pre & post & EPBS & _). stash PB.
assert (INp : In (pb, 16) (PBS ++ (tk, 72) :: (q, 1024) :: LB)) by (rewrite EPBS; left; reflexivity).
assert (INtk1 : In (tk, 72) (PBS ++ (tk, 72) :: (q, 1024) :: LB)) by (apply in_or_app; right; left; reflexivity).
assert (INq1 : In (q, 1024) (PBS ++ (tk, 72) :: (q, 1024) :: LB)) by (apply in_or_app; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP1 INtk1) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ tk 72 HP1 INtk1) as Himg_t. cbn [hl_img_lo hl_img_hi S4L] in Himg_t.
pose proof (heap_blk S4L HIx _ _ _ _ q 1024 HP1 INq1) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heap_blk S4L HIx _ _ _ _ pb 16 HP1 INp) as (_ & Hpal & Hplo & Hphi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hqhi, Hphi.
assert (Htq : tk <> q).
{ intros ->. pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP1) as ND. rewrite map_app in ND. apply NoDup_app_remove_l in ND.
cbn [map blk_addr fst] in ND. apply List.NoDup_cons_iff in ND as [Hni _]. apply Hni. left. reflexivity. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 q 1024 HP1 INtk1 INq1 Htq) as Hdtq.
pose proof (heap_model_ok _ _ _ _ _ _ HP1) as MOK1.
pose proof (heap_mem_inv _ _ _ _ _ _ HP1) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m1) as WM.
pose proof (munch_refl [(SP, SP + 48); (tk, tk + 72)] m1) as MU.
reenter MOK1.
step. stepz. stepz. step. if_falsex. step.

unstash PB.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (PBc : pbuf rsegs mc PBS pb)
by (eapply pbuf_agree; [exact PB | | apply incl_refl];
eapply agree_on_trans; [exact AG1 |];
eapply agree_of_munch; [exact MU | exact WM | intros a n Hin; cbn; split; [| split; [| exact I]];
[ pose proof (heap_blk S4L HIx _ _ _ _ a n HP1 ltac:(apply in_or_app; left; exact Hin)) as (_ & _ & _ & Hhi' & _); unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi'; lia
| refine (heap_blk_disjoint S4L HIx _ _ _ _ a n tk 72 HP1 ltac:(apply in_or_app; left; exact Hin) INtk1 _);
intros ->; exact (nodup_prefix_suffix PBS ((tk, 72) :: (q, 1024) :: LB) tk n 72 (heap_blk_nodup S4L HIx _ _ _ _ HP1) Hin ltac:(left; reflexivity)) ]])
end.
apply evt_RZ_done.
eapply (Uihm.printbuf_free_cps HIx) with (LB := (tk, 72) :: (q, 1024) :: LB) (BS := PBS) (p := pb) (lo := lo);
[ eapply (heap_frame S4L HIx); [exact HP1 | | exact WM | exact MI];
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP1 MU);
apply Forall_cons; [left; cbn [fst snd]; clia | apply Forall_cons; [right; left; exists tk, 72; split; [exact INtk1 | cbn; lia] | apply Forall_nil]]
| right; split; [exact Hpb | apply pbuf_pbufw; exact PBc] | .. ]; try alloc_side.
all: try (unfold RESET_STK, put_stk_P in *; clia).
intros ms2 md2 (mb & A2 & r2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & HP2).
destruct RS2 as (w0' & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit SP) in ST2 by lia. rewrite ?(unsigned_lit SP) in HPR2 by lia.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR1; [| left; cbn; lia]. cbn [hl_segs S4L] in FR1.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in TOK1; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in TOK1.
assert (HPRb : heap_pres S4L LB (SP + 48) m mb).
{ eapply heap_pres_trans; [exact HPR1|]. eapply heap_pres_trans.
- eapply (heap_pres_of_munch S4L LB (SP + 48)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP1 | intros bb Hbb; apply in_or_app; right; right; right; exact Hbb | clia |].
apply Forall_cons; [left; cbn [fst snd]; clia | apply Forall_cons; [| apply Forall_nil]]. cbn [fst snd].
right; left. exists tk, 72. split; [exact INtk1|]. split; [| lia].
intros Hin0. pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP1) as ND. rewrite map_app in ND. apply NoDup_app_remove_l in ND.
cbn [map blk_addr fst] in ND. apply List.NoDup_cons_iff in ND as [Hni _]. apply Hni. right. exact (in_map blk_addr _ _ Hin0).
- eapply heap_pres_weaken; [exact HPR2 | lia | intros bb Hbb; right; right; exact Hbb]. }
clear MU WM MI HPR1.

pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs mb) as WM.
pose proof (munch_refl [(SP, SP + 48)] mb) as MU.
reenter MOK2.
step. step.
alloc_call (hi_free S4L HIx) S4L HIx HP2 MU WM MI.
{ right. exists 1024. right. left. reflexivity. }
all: try (unfold RESET_STK, put_stk_P in *; clia).
intros ms3 mx3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3. cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit SP) in ST3 by lia. rewrite ?(unsigned_lit SP) in HPR3 by lia.
rewrite (lb_remove_other q (tk, 72)) in HPR3, HP3 by (cbn; lia). rewrite lb_remove_head in HPR3, HP3.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in FR1; [| left; cbn; lia]. cbn [hl_segs S4L] in FR1.
assert (HPRd : heap_pres S4L LB (SP + 48) m mx3).
{ eapply heap_pres_trans; [exact HPRb|]. eapply heap_pres_trans.
- eapply (heap_pres_of_munch S4L LB (SP + 48)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP2 | intros bb Hbb; right; right; exact Hbb | clia |].
apply Forall_cons; [left; cbn [fst snd]; clia | apply Forall_nil].
- eapply heap_pres_weaken; [exact HPR3 | lia | intros bb Hbb; right; exact Hbb]. }
clear MU WM MI HPRb.

pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs mx3) as WM.
pose proof (munch_refl [(SP, SP + 48)] mx3) as MU.
reenter MOK3.
step. step.
alloc_call (hi_free S4L HIx) S4L HIx HP3 MU WM MI.
{ right. exists 72. left. reflexivity. }
all: try (unfold RESET_STK, put_stk_P in *; clia).
intros ms4 mx4 md4 A4 r4 RS4 VM4 ST4 HPR4 ERR4 HP4. open_ret RS4. cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit SP) in ST4 by lia. rewrite ?(unsigned_lit SP) in HPR4 by lia.
rewrite lb_remove_head in HPR4, HP4.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in FR1; [| left; cbn; lia]. cbn [hl_segs S4L] in FR1.
assert (HPRe : heap_pres S4L LB (SP + 48) m mx4).
{ eapply heap_pres_trans; [exact HPRd|]. eapply heap_pres_trans.
- eapply (heap_pres_of_munch S4L LB (SP + 48)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP3 | intros bb Hbb; right; exact Hbb | clia |].
apply Forall_cons; [left; cbn [fst snd]; clia | apply Forall_nil].
- eapply heap_pres_weaken; [exact HPR4 | lia | intros bb Hbb; exact Hbb]. }
clear MU WM MI HPRd.

pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4.
pose proof (wmono_refl rsegs mx4) as WM.
pose proof (munch_refl [(SP, SP + 48)] mx4) as MU.
reenter MOK4.
do 8 step.
apply evt_RZ_done. apply K. unfold tkf_post.
exists mx4, A4.
split; [| split; [| split; [| split; [| split]]]].
- eapply ret_statew_intro; [eapply fsaved_trans; [exact FS1 | exact FS2] | intros Hf; apply FRM2, FRM1, Hf].
- eapply model_vm_only_trans; [exact VM1|]. eapply model_vm_only_trans; [exact VM2|]. eapply model_vm_only_trans; [exact VM3| exact VM4].
- rewrite unsigned_lit by lia.
pose proof (stk_release rsegs mx4 lo SP _ ST4 FR1 ltac:(lia)) as STx. cbn [cells_size csize Nat.add] in STx.
replace (SP + _) with (SP + 48) in STx by lia. exact STx.
- rewrite unsigned_lit by lia. exact HPRe.
- exact ERR4.
- exact HP4.
Qed.

End TokFreeTail.
End RC__1.
