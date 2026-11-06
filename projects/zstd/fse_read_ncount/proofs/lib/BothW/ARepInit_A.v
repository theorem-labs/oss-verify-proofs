(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed AsanHandoffBoth.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import MainExport MainFactsBoth.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg ABase ALayout ARep AHeapP AQConst ARepQ ARepInit_kit.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Section CANSEC1. Context {rc : runConstT}.
Definition X0 : aconc := mkAConc (fun _ => mkXClass [] []) [].
Definition ST0 (V : nat -> Z) : astate := ainit (a_space_beg0 V) (a_ptr_array0 V).
#[using="Type"] Lemma get_cls_ST0 : forall V c, get_cls (ST0 V) c = aclass0.
Proof. intros. apply get_cls_ainit. Qed.
#[using="Type"] Lemma max_count_ST0 : forall V c, max_count (ST0 V) c = 0.
Proof. intros. reflexivity. Qed.
#[using="Type"] Lemma ndist_ST0 : forall V c, ndist (ST0 V) c = 0.
Proof. intros. unfold ndist. rewrite get_cls_ST0. cbn. apply Zdiv_0_l. Qed.
#[using="Type"] Lemma busy_slots_X0 : forall c, busy_slots X0 c = [].
Proof. intros. reflexivity. Qed.
#[using="Type"] Lemma page_round_up_Z_bounds : forall x, x <= page_round_up_Z x < x + 4096 /\ page_round_up_Z x mod 4096 = 0.
Proof.
intros x. unfold page_round_up_Z, page_size. split; [| apply Z_mod_mult]. Z.div_mod_to_equations. Local Ltac2 Set LiaHints.tbl := fun () => "0010=51504200131.9000006S1H2H0".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Local Ltac aobj_close :=
unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI;
split; [rewrite Z.mul_comm; apply Z_mod_mult|]; split; [lia|]; split; [lia|]; split; lia.
#[using="Type"] Theorem alayout_ok_init : forall (V : nat -> Z) (w : bool) (U : list (list Z)),
Forall (pfact_ok V) both_pure_facts -> (length U <= Z.to_nat AUMAX)%nat ->
32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP ->
alayout_ok (mkALayout (LV V) w U).
Proof.
intros V w U HP HU HAT.
pf V HP (PVar 0 4294901760 4294967295) Q0. pf V HP (PVar 6 0 255) Q6. pf V HP (PVar 10 0 7) Q10.
constructor; rewrite ?LV_t, ?LV_ctx, ?LV_nodes, ?LV_store, ?LV_fake, ?LV_ptr_array, ?LV_space_beg; unfold al_res, al_dtls; cbn [al_V LV Nat.eqb].
-
pf V HP (PVar 227 1 34359736319) P.
pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW.
pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZLit 2147446784) 17592186048512) DB.
pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZLit 65536) 6189056) DI.
Local Ltac2 Set LiaHints.tbl := fun () => "00E0>11601612111.1718274553776.1418274553776.1518926759668.1518930958230.1318933043916.172045788936.18 25041592359.1226304959527.1327572950718.1427572950718.1527681095499.1227681095499.1427681095499.1529181817650.1429181817650.1536871214227.1537610345433.1241702679174.1353649618577.1365504523926.1300000100:00A00B00C00D00Q00T00\00n01C01F01I01L01O01a01e01k01l026027SS2HU2DB1PS2HU2DBSSSS2HU1P1B2Hq1HS1PS3HAT2T1S2HU3HAT2Q61P2DW1HS2HU3HAT2Q61P2DW2DB1HS1PS1PS1PS1PS2HU3HAT2Q61P2DI1HS2H4S2HU1DSS3HAT2T11HS".
aobj_close.
-
pf V HP (PVar 228 1527 34359736304) P.
pf V HP (PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW.
pf V HP (PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZLit 2147446784) 17592186048512) DB.
aobj_close.
-
pf V HP (PVar 453 1527 34359736064) P.
pf V HP (PDisj (ZMul (ZLit 4096) (ZV 453)) 1048576 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW.
pf V HP (PDisj (ZMul (ZLit 4096) (ZV 453)) 1048576 (ZLit 2147446784) 17592186048512) DB.
aobj_close.
-
pf V HP (PVar 454 1527 34359734272) P.
pf V HP (PDisj (ZMul (ZLit 4096) (ZV 454)) 8388608 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW.
pf V HP (PDisj (ZMul (ZLit 4096) (ZV 454)) 8388608 (ZLit 2147446784) 17592186048512) DB.
aobj_close.
-
pf V HP (PVar 377 1527 34359733495) P.
pf V HP (PDisj (ZMul (ZLit 4096) (ZV 377)) 11571200 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW.
pf V HP (PDisj (ZMul (ZLit 4096) (ZV 377)) 11571200 (ZLit 2147446784) 17592186048512) DB.
aobj_close.
-
pf V HP (PVar 208 4295491576 34326181871) P.
pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW.
pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZLit 2147446784) 17592186048512) DB.
aobj_close.
-
pf V HP (PVar 226 1527 34359734272) P.
pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW.
pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZLit 2147446784) 17592186048512) DB.
aobj_close.
-
pf V HP (PVar 310 1 34359736319) P.
pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW.
pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZLit 2147446784) 17592186048512) DB.
pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZLit 65536) 6189056) DI.
aobj_close.
- pf V HP (PVar 208 4295491576 34326181871) P. lia.
- pf V HP (PVar 209 0 15) P. lia.
-
pf V HP (PRange (ZAdd (ZMul (ZLit (-4096)) (ZV 209)) (ZAnd (ZMul (ZLit 4096) (ZV 208)) (ZLit 65535))) 0 0) H4.
pf V HP (PVar 209 0 15) P.
change 65535 with (Z.ones 16) in H4. rewrite Z.land_ones in H4 by lia. change (2^16) with 65536 in H4.
pose proof (Z.mod_pos_bound (4096 * V 208%nat) 65536 ltac:(lia)) as B.
set (u := (4096 * V 208%nat) mod 65536) in *.
assert (Hv : (-4096 * V 209%nat + u) mod MainExport.two64 = 0) by lia.
apply Z.mod_divide in Hv; [| unfold MainExport.two64; lia]. destruct Hv as [q Hq]. unfold MainExport.two64 in Hq.
replace (4096 * (V 208%nat - V 209%nat) + 65536) with ((4096 * V 208%nat / 65536 + 1) * 65536); [apply Z_mod_mult|].
pose proof (Z.div_mod (4096 * V 208%nat) 65536 ltac:(lia)). lia.
- pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 227)) 4096) D. unfold adisj. lia.
- pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 228)) 65536) D. unfold adisj. lia.
- pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 453)) 1048576) D. unfold adisj. lia.
- pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 454)) 8388608) D. unfold adisj. lia.
- pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 377)) 11571200) D. unfold adisj. lia.
- pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 226)) 8388608) D. unfold adisj. lia.
- pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 228)) 65536) D. unfold adisj. lia.
- pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 453)) 1048576) D. unfold adisj. lia.
- pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 454)) 8388608) D. unfold adisj. lia.
- pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 377)) 11571200) D. unfold adisj. lia.
- pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 227)) 4096) D. unfold adisj. lia.
- pf V HP (PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZMul (ZLit 4096) (ZV 453)) 1048576) D. unfold adisj. lia.
- pf V HP (PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZMul (ZLit 4096) (ZV 454)) 8388608) D. unfold adisj. lia.
- pf V HP (PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZMul (ZLit 4096) (ZV 377)) 11571200) D. unfold adisj. lia.
- pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 228)) 65536) D. unfold adisj. lia.
- pf V HP (PDisj (ZMul (ZLit 4096) (ZV 453)) 1048576 (ZMul (ZLit 4096) (ZV 454)) 8388608) D. unfold adisj. lia.
- pf V HP (PDisj (ZMul (ZLit 4096) (ZV 377)) 11571200 (ZMul (ZLit 4096) (ZV 453)) 1048576) D. unfold adisj. lia.
- pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 453)) 1048576) D. unfold adisj. lia.
- pf V HP (PDisj (ZMul (ZLit 4096) (ZV 377)) 11571200 (ZMul (ZLit 4096) (ZV 454)) 8388608) D. unfold adisj. lia.
- pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 454)) 8388608) D. unfold adisj. lia.
- pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 377)) 11571200) D. unfold adisj. lia.
- pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 310)) 4096) D. unfold adisj. lia.
- pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 310)) 4096) D. unfold adisj. lia.
- pf V HP (PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZMul (ZLit 4096) (ZV 310)) 4096) D. unfold adisj. lia.
- pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 453)) 1048576) D. unfold adisj. lia.
- pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 454)) 8388608) D. unfold adisj. lia.
- pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 377)) 11571200) D. unfold adisj. lia.
- pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 310)) 4096) D. unfold adisj. lia.
-
clear Q0 Q6 Q10. pf V HP (PVar 0 4294901760 4294967295) P0. pf V HP (PVar 6 0 255) P6. pf V HP (PVar 10 0 7) P10.
unfold al_bot, al_top. rewrite LV_sp0.
pose proof (page_round_up_Z_bounds (32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 0xa0)) as [T1 T2].
set (T := page_round_up_Z _) in *. clearbody T.
apply Z.mod_divide in T2 as [q ->]; [| lia]. change (2^47) with (34359738368 * 4096).
split; [lia|]. split; [apply Z_mod_mult|]. split; lia.
- exact HU.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Theorem awf_init : forall (V : nat -> Z) (w : bool) (U : list (list Z)),
Forall (pfact_ok V) both_pure_facts -> (length U <= Z.to_nat AUMAX)%nat ->
32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP ->
awf (mkALayout (LV V) w U) (ST0 V) X0.
Proof.
intros V w U HP HU HAT. pose proof (alayout_space _ (alayout_ok_init V w U HP HU HAT)) as (S1 & S2 & S3 & S4).
unfold awf. repeat match goal with |- _ /\ _ => split end.
- unfold ST0, ainit, a_space_beg0, al_space_beg. cbn [a_space_beg al_V LV Nat.eqb]. Local Ltac2 Set LiaHints.tbl := fun () => "0090>15043033658.1416982081525.1418930958230.1427019518934.1428992528799.1446188560206.1448398490712.12633541053.14  64918363412.1400000400500900:00>00B00F00J00KS2HUFS2HUFS2HUS2HUS2HUS2HUF".
lia.
- reflexivity.
- exact S3. - exact S1. - exact S2.
- intros c Hc. rewrite get_cls_ST0, max_count_ST0, busy_slots_X0, ndist_ST0. cbn.
unfold K_FREEARR_OFF, K_FREEARR_MAX, K_USER_MAP, K_FREEARR_MAP.
repeat match goal with |- _ /\ _ => split end; try lia; try reflexivity;
first [ apply Zmod_0_l | constructor | intros k [] ].
- intros c _. apply get_cls_ST0.
- intros b [].
- intros p c n H. cbn in H. rewrite lookup_empty in H. discriminate.
- intros p ch H. cbn in H. rewrite lookup_empty in H. discriminate.
- intros b1 b2 [].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Theorem ablocks_init : forall L st, ablocks L st X0 [].
Proof.
intros L st. split; [intros p A n []|]. split; [intros cls A n []|]. split; constructor.
Qed.
#[using="Type"] Theorem qcoupled_init : forall L V, qcoupled L (ST0 V) X0 qconc0.
Proof.
intros L V. unfold qcoupled. cbn.
split; [reflexivity|]. split; [reflexivity|]. split; [constructor|]. split; [constructor|]. split; [constructor|].
split; [intros k; split; [intros []| intros (b & [] & _)]|].
split; [intros c k; split; [intros []| intros (b & [] & _)]|]. constructor.
Qed.
#[using="Type"] Theorem qnum_init : forall V, qnum (ST0 V).
Proof.
intros V. unfold qnum. cbn. unfold Q_CACHE, Q_MAX. repeat split; try lia. constructor.
Qed.
End CANSEC1.
