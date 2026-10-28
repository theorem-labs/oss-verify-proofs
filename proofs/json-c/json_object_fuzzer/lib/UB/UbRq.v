(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qtgi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qtgi. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UtMn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UtMn.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QkMG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkMG.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UG8z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UG8z. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Udyh.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U2Sr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U2Sr. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require ULbz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import ULbz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIsM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIsM.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UXfU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UXfU.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QgoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgoP.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U4Eu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U4Eu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uc8V.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uc8V.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UfOM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UfOM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uy2A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uy2A. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UdFq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UdFq. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UvXs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UvXs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UX85.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UX85. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UX85.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UX85.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UYrb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UYrb.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UubI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UubI. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UYrb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UYrb.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require TopUbTac.
Import TopUbTac.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition trimc (c : Z) : bool := (c =? 43) || (c =? 45) || (c =? 69) || (c =? 101).

#[using="Type"] Lemma trim_test : forall cl : byte, numb cl = true ->
Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr 288230376218820613 (bv_unsigned (Z_to_bv 64 (bv_unsigned cl + -43)) mod 64)))) 1
= (if trimc (bv_unsigned cl) then 1 else 0).
Proof.
intros cl H. unfold numb, numch in H. unfold trimc.
pose proof (bv_unsigned_in_range 8 cl) as R. unfold bv_modulus in R. cbn in R.
set (c := bv_unsigned cl) in *. clearbody c.
assert (CASES : exists k : nat, (k < 256)%nat /\ c = Z.of_nat k) by (exists (Z.to_nat c); split; lia).
destruct CASES as (k & Hk & ->).
do 102 (destruct k as [|k]; [first [discriminate H | vm_compute; reflexivity] |]).
exfalso. cbn in H. rewrite !Bool.orb_true_iff, !Bool.andb_true_iff, !Z.eqb_eq, !Z.leb_le in H. lia.
Qed.

#[using="Type"] Lemma numb_cases : forall b, numb b = true ->
let c := bv_unsigned b in c = 43 \/ c = 45 \/ c = 46 \/ (48 <= c <= 57) \/ c = 69 \/ c = 101.
Proof.
intros b H. unfold numb, numch in H. cbn zeta.
rewrite !Bool.orb_true_iff, !Bool.andb_true_iff, !Z.eqb_eq, !Z.leb_le in H. lia.
Qed.

#[using="Type"] Lemma last_skipn1 {A} (l : list A) c rest : nth_error l (length l - 1) = Some c ->
firstn 1 (skipn (length l - 1) (l ++ rest)) = [c].
Proof.
intros H. pose proof (@nth_error_split _ l (length l - 1) c H) as (l1 & l2 & E & L1).
rewrite E at 2. rewrite <- app_assoc, skipn_app, <- L1, skipn_all, Nat.sub_diag. cbn. reflexivity.
Qed.

#[using="Type"] Lemma after_last {A} (l : list A) rest : (1 <= length l)%nat ->
skipn 1 (skipn (length l - 1) (l ++ rest)) = rest.
Proof.
intros H. rewrite skipn_skipn. replace (1 + (length l - 1))%nat with (length l) by lia.
rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.

#[using="Type"] Lemma Forall_firstn {A} (P : A -> Prop) n (l : list A) : Forall P l -> Forall P (firstn n l).
Proof. intros H. rewrite <- (firstn_skipn n l) in H. apply Forall_app in H. exact (proj1 H). Qed.

Section PeNumTrim.
Variable HIx : heap_iface S4L.
Variables (pf : pe_fix) (q : Z) (LBc : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(sv : pe_saved) (T : TSet) (F0 : bvmap 5 word).
Hypothesis STRTOLL : strtox_stmt strtoll_entry.
Hypothesis STRTOULL : strtox_stmt strtoull_entry.
Hypothesis STRTOD : rstrtod_stmt.
Hypothesis STRDUP : strdup_stmt HIx.
Let LB0 : list blk := LB0 pf LBc.

#[using="Type"] Lemma trim_loop :
forall (k : nat) (ts : tstate) (l : tlevel) (txt : list byte)
(m : word -> option byte) (md : Model) (A : AS S4L HIx)
(cb : byte) (j1 j2 utf : list byte) (errv : word) (cop : Z)
(x1 gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s7 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
(length txt <= k)%nat ->
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
pbufc rsegs m (t_pbs ts) (t_pb ts) txt -> Forall (fun b => numb b = true) txt -> (2 <= length txt)%nat ->
(forall m' txt' a0' a1' a2' a3',
PE_INV HIx pf q LB0 payload me lo m' md A ts cb j1 j2 utf sv errv ->
pbufc rsegs m' (t_pbs ts) (t_pb ts) txt' -> Forall (fun b => numb b = true) txt' -> (1 <= length txt' <= length txt)%nat ->
realizes rsegs (mkCfg (pe_ms7 rsegs pf 0x22d28 cop x1 gp t0 t1 t2 a0' a1' a2' a3' a4 a5 a6 a7
s4 (Z_to_bv 64 (t_pb ts)) s7 (Z_to_bv 64 (pf_sb pf + t_co ts)) s9 s10 t3 t4 t5 t6 F fc m') md) T) ->
realizes rsegs (mkCfg (pe_ms7 rsegs pf 0x22c94 cop x1 gp t0 t1 t2 (Z_to_bv 64 (Z.of_nat (length txt))) a1 a2 a3 a4 a5 a6 a7
s4 (Z_to_bv 64 (t_pb ts)) s7 (Z_to_bv 64 (pf_sb pf + t_co ts)) s9 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
induction k as [|k IH]; intros until fc; intros Hk STC INV PBC NUM L2 KEXIT; [exfalso; lia|].
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
pose proof INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK.
unfold pe_ms7, pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
set (LBall := pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) in *.
assert (INtk : In (tk, 72) LBall) by (unfold LBall, pe_blocks; apply in_or_app; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi.

pose proof PBC as (buf & bpos & cap & post & Epbs & Ltxt & PCORE). pose proof PCORE as (Hbpos & Hcap & Hclen & PBS & PBUF). cbn [hl_segs S4L pf_mxd] in PBS, PBUF.
assert (INpb : In (pb, 16) LBall) by (unfold LBall, pe_blocks, tstate_blocks, ts0; cbn [t_pbs pf_mxd]; rewrite Epbs; apply in_or_app; left; apply in_or_app; left; left; reflexivity).
assert (INbuf : In (buf, cap) LBall) by (unfold LBall, pe_blocks, tstate_blocks, ts0; cbn [t_pbs pf_mxd]; rewrite Epbs; apply in_or_app; left; apply in_or_app; left; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ pb 16 HP INpb) as (_ & Hpbal & Hpblo & Hpbhi & _).
pose proof (heap_blk S4L HIx _ _ _ _ buf cap HP INbuf) as (_ & Hbufal & Hbuflo & Hbufhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hpbhi, Hbufhi.
pose proof (pe_pbs_sep HIx _ _ _ ts0 _ _ _ _ pb buf cap STC HP Epbs) as (Dpbbuf & Dtkpb & Dtkbuf & Dqpb & Dqbuf). cbn [pf_tk pf_mxd] in Dtkpb, Dtkbuf, Dqpb, Dqbuf.
rewrite !length_app in Hclen. cbn [length pf_mxd] in Hclen.

destruct (nth_error txt (length txt - 1)) as [cl|] eqn:Hcl; [| apply nth_error_None in Hcl; lia].
assert (TXT0 : bytes_at rsegs m buf (txt ++ [b0] ++ post)).
{ pose proof (rw_cells_bytes_at' _ _ _ _ PBUF) as X. cbn [cells_bytes cbytes pf_mxd] in X. rewrite app_nil_r in X. exact X. }
pose proof (string_byte m buf _ (Z.of_nat (length txt) - 1) cl TXT0 ltac:(rewrite nth_error_app1 by lia; replace (Z.to_nat (Z.of_nat (length txt) - 1)) with (length txt - 1)%nat by lia; exact Hcl) ltac:(lia)) as RDL.
pose proof (bv_unsigned_in_range 8 cl) as CLR. unfold bv_modulus in CLR. cbn in CLR.
assert (NUMcl : numb cl = true) by (eapply (Forall_forall (fun b => numb b = true) txt); [exact NUM | eapply nth_error_In; exact Hcl]).
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
stash PB. stash TSK. stash REST. stash FR. stash Dqpb. stash Dqbuf. clear PBC PCORE TXT0.
apply rz_evt; [exact MOK|].
step. step. step. step.
rewrite (unsigned_lit (Z.of_nat (length txt))) by lia. rewrite swrap32_id by lia.
if_truex. ub_skip. if_truex. step. step.
unfold zxb. rewrite (unsigned_lit (bv_unsigned cl)) by lia.
pose proof (numb_cases cl NUMcl) as CLC. cbn zeta in CLC.
step. step. if_falsex.
step. step. step. step. step.
step. step. rewrite (trim_test cl NUMcl).
destruct (trimc (bv_unsigned cl)) eqn:TC.
2:{
step. if_true. unstash PB. unstash TSK. unstash REST. unstash FR.
apply evt_RZ_done. eapply (KEXIT m txt); [exact INV | | exact NUM | lia].
exists buf, bpos, cap, post. split; [exact Epbs|]. split; [exact Ltxt|]. split; [lia|]. split; [lia|]. split; [rewrite !length_app; cbn [length pf_mxd]; lia|]. split; [exact PBS | exact PBUF]. }
step. if_false.

destruct (rw_cells_CB_cut rsegs _ _ _ _ (length txt - 1) PBUF ltac:(lia)) as [PB0 PB1].
destruct (rw_cells_CB_cut rsegs _ _ _ _ 1 PB1 ltac:(lia)) as [PBZ PB2]. clear PBUF PB1.
replace (buf + Z.of_nat (length txt - 1) + Z.of_nat 1) with (buf + Z.of_nat (length txt)) in PB2 by lia.
rewrite (last_skipn1 txt cl ([Z_to_bv 8 0] ++ post) Hcl) in PBZ.
rewrite (after_last txt ([Z_to_bv 8 0] ++ post)) in PB2 by lia.
replace (buf + Z.of_nat (length txt - 1)) with (buf + Z.of_nat (length txt) + -1) in PBZ by lia.
pose proof (wmono_refl rsegs m) as WM. pose proof (munch_refl [(buf, buf + cap); (pb, pb + 16)] m) as MU.
replace (buf + (Z.of_nat (length txt) + -1)) with (buf + Z.of_nat (length txt) + -1) by lia.
stepz.
step. ub_skip. if_truex. ub_skip. rewrite (unsigned_lit pb) by lia. rewrite (land7_of_mod16 pb Hpbal). ub_if_lit_c. ub_skip.
norm_sx32. rewrite (unsigned_lit bpos) by lia. rewrite swrap32_id by lia. rewrite <- Ltxt. if_truex.
step. step. step. norm_sx32. step.

unstash PB. unstash TSK. unstash REST. unstash FR. unstash Dqpb. unstash Dqbuf.
set (txt' := firstn (length txt - 1) txt).
assert (Ltxt' : length txt' = (length txt - 1)%nat) by (unfold txt'; rewrite length_firstn; lia).
assert (NUM' : Forall (fun b => numb b = true) txt') by (apply Forall_firstn; exact NUM).
assert (HW : Forall (pe_private (PEF tk oldl newl len lenr sb spf pmd mxd fl) q pbs) [(buf, buf + cap); (pb, pb + 16)]).
{ apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; right; right; left; cbn [fst snd pf_mxd]; rewrite Epbs.
- exists buf, cap. split; [right; left; reflexivity | lia].
- exists pb, 16. split; [left; reflexivity | lia]. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) => assert (PBC1 : pbufc rsegs m1 pbs pb txt') end.
{ exists buf, (Z.of_nat (length txt) - 1), cap, (Z_to_bv 8 0 :: post). split; [exact Epbs|]. split; [lia|].
split; [lia|]. split; [lia|]. split; [unfold txt'; rewrite !length_app, length_firstn; cbn [length pf_mxd]; lia|]. split.
- match goal with H : rw_cells rsegs _ pb _ |- _ => exact H end.
- match goal with Hz : rw_cells rsegs _ (buf + Z.of_nat (length txt) + -1) [C1 _] |- _ => rename Hz into PBZ1 end.
match goal with H0 : rw_cells rsegs _ buf [CB (length txt - 1) _] |- _ => rename H0 into PB01 end.
match goal with H2 : rw_cells rsegs _ (buf + Z.of_nat (length txt)) _ |- _ => rename H2 into PB21 end.
apply (rw_cells_recast rsegs _ _ _ [CB 1 [Z_to_bv 8 0]]) in PBZ1; [| cbn; auto | reflexivity | reflexivity].
replace (buf + Z.of_nat (length txt) + -1) with (buf + Z.of_nat (length txt - 1)) in PBZ1 by lia.
pose proof (rw_cells_CB_join rsegs _ _ _ _ _ _ PB01 PBZ1) as J1.
replace (buf + Z.of_nat (length txt)) with (buf + Z.of_nat (length txt - 1 + 1)) in PB21 by lia.
pose proof (rw_cells_CB_join rsegs _ _ _ _ _ _ J1 PB21) as J2.
replace (length txt - 1 + 1 + (Z.to_nat cap - (length txt - 1) - 1))%nat with (Z.to_nat cap) in J2 by lia.
rewrite firstn_app in J2. replace (length txt - 1 - length txt)%nat with 0%nat in J2 by lia. cbn [firstn pf_mxd] in J2.
rewrite app_nil_r in J2. unfold txt'. rewrite <- !app_assoc in J2. cbn [app pf_mxd] in J2 |- *. exact J2. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
assert (INV1 : PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m1 md A ts0 cb j1 j2 utf sv errv)
end.
{ split.
- unfold PE_CORE, ts0. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj ts_choff pf_len pf_tk pf_spf pf_mxd].
split; [exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [unfold tok_cells, tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd]; exact TOK|].
split; [eapply pbufc_pbuf; exact PBC1|]. split; [exact Hpb|]. split.
+ eapply (tstack_transport rsegs); [exact TSK | exact MU | exact WM |]. intros j Hj. rewrite LEN32 in Hj. cbn. lia.
+ unfold pe_frame. eapply (rw_cells_transport rsegs _ m); [exact FR | exact MU | exact WM | cbn; unfold PE_FRAME in *; lia].
- eapply (PE_REST_private_write HIx) with (ts := ts0) in REST; [exact REST | exact STC | exact MU | exact WM | assumption | exact HW]. }
step. destruct (Z.lt_ge_cases 2 (Z.of_nat (length txt))) as [MORE | DONE].
- if_falsex. apply evt_RZ_done.
replace (Z.of_nat (length txt) + -1) with (Z.of_nat (length txt')) by lia.
eapply (IH ts0 l txt'); [lia | exact STC | exact INV1 | exact PBC1 | exact NUM' | lia |].
intros m' txt'' a0' a1' a2' a3' INV' PBC' NUM'' L''. eapply KEXIT; [exact INV' | exact PBC' | exact NUM'' | lia].
- if_truex. apply evt_RZ_done. eapply (KEXIT _ txt'); [exact INV1 | exact PBC1 | exact NUM' | lia].
Qed.
End PeNumTrim.

Section PeNumTrim2.
Variable HIx : heap_iface S4L.
Variables (pf : pe_fix) (q : Z) (LBc : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(sv : pe_saved) (T : TSet) (F0 : bvmap 5 word).
Hypothesis STRTOLL : strtox_stmt strtoll_entry.
Hypothesis STRTOULL : strtox_stmt strtoull_entry.
Hypothesis STRTOD : rstrtod_stmt.
Hypothesis STRDUP : strdup_stmt HIx.
Let LB0 : list blk := LB0 pf LBc.

#[using="STRTOLL STRTOULL STRTOD STRDUP"] Lemma num_trim :
forall (n : nat) (ts : tstate) (l : tlevel) (txt : list byte)
(m : word -> option byte) (md : Model) (A : AS S4L HIx)
(cb : byte) (j1 j2 utf : list byte) (errv : word) (cop stv : Z)
(x1 gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s7 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
(stv = 0 \/ stv = 1) ->
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_number ->
pbufc rsegs m (t_pbs ts) (t_pb ts) txt -> Forall (fun b => numb b = true) txt -> Z.of_nat (length txt) <= pf_len pf ->
bytes_at rsegs me GOT_free_userdata (le8 (Z_to_bv 64 (fn_free_userdata S4F))) ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->
tdepth_ok ts ->
fsaved F0 F -> frm0 fc ->
(mbase pf ts + 8 <= n)%nat ->
KALL HIx pf q LBc payload me lo sv T F0 n -> KOUT7 HIx pf q LBc payload me lo sv T F0 ->
realizes rsegs (mkCfg (pe_ms7 rsegs pf 0x22c7c cop x1 gp t0 t1 t2 (Z_to_bv 64 stv) a1 a2 a3 a4 a5 a6 a7
s4 (Z_to_bv 64 (t_pb ts)) s7 (Z_to_bv 64 (pf_sb pf + t_co ts)) s9 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros Hstv STC INV Hl Hst PBC NUM LTXT GOTU Hco Hcb TDOK FS FRM Hn KALL KOUT.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
pose proof INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK.
unfold pe_ms7, pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
pose proof Hn as Hn0. unfold mbase in Hn. cbn [pf_len t_co pf_mxd] in Hn.
unfold_consts.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
set (LBall := pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) in *.
assert (INtk : In (tk, 72) LBall) by (unfold LBall, pe_blocks; apply in_or_app; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi.
pose proof PBC as (buf & bpos & cap & post & Epbs & Ltxt & PCORE). pose proof PCORE as (Hbpos & Hcap & Hclen & PBS & PBUF). cbn [hl_segs S4L pf_mxd] in PBS, PBUF.
assert (INpb : In (pb, 16) LBall) by (unfold LBall, pe_blocks, tstate_blocks, ts0; cbn [t_pbs pf_mxd]; rewrite Epbs; apply in_or_app; left; apply in_or_app; left; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ pb 16 HP INpb) as (_ & Hpbal & Hpblo & Hpbhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hpbhi.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
stash PB. stash TSK. stash REST. stash FR. clear PBUF.
apply rz_evt; [exact MOK|].
step. destruct Hstv as [-> | ->].
2:{
step. if_true. step. if_cases Kisd.
- zify_cond Kisd.
assert (SX0 : sx32 isd = Z_to_bv 64 0) by (apply bv_eq; change (bv_unsigned (Z_to_bv 64 0)) with 0; lia).
unstash PB. unstash TSK. unstash REST. unstash FR.
apply evt_RZ_done.
eapply (num_int HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LBc payload me lo sv T F0 STRTOLL STRTOULL n ts0 l txt);
[exact STC | exact INV | exact Hl | exact Hst | exact PBC | exact NUM | exact LTXT | exact SX0 | exact Hco | exact Hcb | tdok TDOK | exact FS | exact FRM | exact Hn0 | exact KALL | exact KOUT].
- unstash PB. unstash TSK. unstash REST. unstash FR.
apply evt_RZ_done.
eapply (num_double HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LBc payload me lo sv T F0 STRTOD STRDUP n ts0 l txt);
[exact STC | exact INV | exact Hl | exact Hst | exact PBC | exact NUM | exact LTXT | exact GOTU | exact Hco | exact Hcb | tdok TDOK | exact FS | exact FRM | exact Hn0 | exact KALL | exact KOUT]. }
step. if_false. step. if_cases Kisd.
-
zify_cond Kisd.
assert (SX0 : sx32 isd = Z_to_bv 64 0) by (apply bv_eq; change (bv_unsigned (Z_to_bv 64 0)) with 0; lia).
rewrite SX0. step. if_true.
unstash PB. unstash TSK. unstash REST. unstash FR.
apply evt_RZ_done.
eapply (num_int HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LBc payload me lo sv T F0 STRTOLL STRTOULL n ts0 l txt);
[exact STC | exact INV | exact Hl | exact Hst | exact PBC | exact NUM | exact LTXT | exact SX0 | exact Hco | exact Hcb | tdok TDOK | exact FS | exact FRM | exact Hn0 | exact KALL | exact KOUT].
- step. norm_sx32. rewrite <- Ltxt. step. step.
destruct (Z.lt_ge_cases (Z.of_nat (length txt)) 2) as [SHORT | LONG].
+
if_truex. step. step. rewrite Kisd. unstash PB. unstash TSK. unstash REST. unstash FR.
apply evt_RZ_done.
eapply (num_double HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LBc payload me lo sv T F0 STRTOD STRDUP n ts0 l txt);
[exact STC | exact INV | exact Hl | exact Hst | exact PBC | exact NUM | exact LTXT | exact GOTU | exact Hco | exact Hcb | tdok TDOK | exact FS | exact FRM | exact Hn0 | exact KALL | exact KOUT].
+ if_falsex. unstash PB. unstash TSK. unstash REST. unstash FR.
apply evt_RZ_done.
eapply (trim_loop HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LBc payload me lo sv T (length txt) ts0 l txt); [lia | exact STC | exact INV | exact PBC | exact NUM | lia |].
intros m' txt' a0' a1' a2' a3' INV' PBC' NUM' L'.
pose proof INV' as [CORE' REST']. destruct CORE' as (_ & _ & _ & _ & TOK' & _). pose proof REST' as (HP' & _).
unfold tok_cells, tok_cells_g in TOK'. cbn [t_pb t_depth t_x ts0 ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_tk pf_mxd] in TOK'.
pose proof (heap_model_ok _ _ _ _ _ _ HP') as MOK'.
apply rz_evt; [exact MOK'|]. unfold pe_ms7. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl].
step. step. rewrite Kisd.
apply evt_RZ_done.
eapply (num_double HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LBc payload me lo sv T F0 STRTOD STRDUP n ts0 l txt');
[exact STC | exact INV' | exact Hl | exact Hst | exact PBC' | exact NUM' | cbn [pf_len pf_mxd]; lia | exact GOTU | exact Hco | exact Hcb | tdok TDOK | exact FS | exact FRM | exact Hn0 | exact KALL | exact KOUT].
Qed.
End PeNumTrim2.

End RC__1.
