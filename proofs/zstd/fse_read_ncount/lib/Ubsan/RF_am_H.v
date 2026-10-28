(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import F_malloc_free MallocTree MallocModel_B F_ntf_B MallocKit_B MallocKit_B3 F_am_A F_am_K F_am_C F_am_F F_am_G F_am_H.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import ProgDeps.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require KStep.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_mm_syscalls RF_ntf_A RF_am_A RF_am_K RF_am_C RF_am_F RF_am_G.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma ram_disp_untried : forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
(m : word -> option byte) (st : mstate),
rmrep st m -> c_avail_meta_area_count (ctx st) = 0 -> c_brk (ctx st) = BrkUntried ->
evt usegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 4095) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15af0) fc None m (seg_rom usegs))
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15ab4) fc None m (seg_rom usegs)).
Proof.
intros until st. intros MR CNT BRK.
pose proof MR as (WF & (C1 & _ & _ & _ & _ & C6) & _). unfold rctx_head_cells, rsecw in C1. rewrite CNT in C1.
unfold ctx_tail_cells, brk_word in C6. rewrite BRK in C6.
unfold pw in C1. cbn [oconc] in C1. unfold wz in C1, C6.
unfold RCTX, RMLOCK, RSSP_GUARD in *. change (324152 + 912) with 325064 in C6.
st1. st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
st1. st1. st1.
change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 (-1))) with false. cbv iota.
st1. rewrite bv_eqb_refl. cbv iota.
st1. st1. st1.
apply evt_done. reflexivity.
Qed.
#[using="Type"] Lemma ram_disp_live : forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
(m : word -> option byte) (st : mstate) (rid : N) (off : Z),
rmrep st m -> c_avail_meta_area_count (ctx st) = 0 -> c_brk (ctx st) = BrkLive rid off ->
0 < conc st (rid, off) -> conc st (rid, off) + 4096 < 2^64 ->
evt usegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (conc st (rid, off) + 4096))
(Z_to_bv 64 (conc st (rid, off) + 4096)) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x15ad8) fc None m (seg_rom usegs))
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15ab4) fc None m (seg_rom usegs)).
Proof.
intros until off. intros MR CNT BRK C0 C1b.
pose proof MR as (WF & (C1 & _ & _ & _ & _ & C6) & _). unfold rctx_head_cells, rsecw in C1. rewrite CNT in C1.
unfold ctx_tail_cells, brk_word in C6. rewrite BRK in C6.
unfold pw in C1. cbn [oconc] in C1. unfold wz in C1, C6.
unfold RCTX, RMLOCK, RSSP_GUARD in *. change (324152 + 912) with 325064 in C6.
st1. st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
st1. st1. st1.
Local Ltac2 Set LiaHints.tbl := fun () => "0040>1687275099.43 3050237658.43 46590550738.4353519283860.4300000500=00A00BS3C1bS2C03C1bS2C0S".
assert (CF : bv_eqb (Z_to_bv 64 (conc st (rid, off))) (Z_to_bv 64 (-1)) = false)
by (unfold bv_eqb; rewrite (unsigned_lit (conc st (rid, off))) by lia; change (bv_unsigned (Z_to_bv 64 (-1))) with (2^64 - 1)%Z; apply Z.eqb_neq; lia).
rewrite CF; clear CF.
st1.
assert (CF : bv_eqb (Z_to_bv 64 (conc st (rid, off))) (Z_to_bv 64 0) = false)
by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
rewrite CF; clear CF.
st1. st1. st1.
apply evt_done. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma ram_bu_mid : forall (sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) (q0 : byte) (q1 : list byte) (q2 : word) F fc
(m : word -> option byte) (cur : Z),
0 < cur < 2^64 -> cur mod 4096 = 0 ->
rw_cells usegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 q2] -> mem_inv usegs m ->
evt usegs (fun ms' => exists a2' m',
ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 0) a2' a3 a4 a5 a6 (Z_to_bv 64 214)
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x15b14) fc None m' (seg_rom usegs)
/\ munch [(RCTX + 920, RCTX + 928)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ rw_cells usegs m' (RCTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 cur)])
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 0) (Z_to_bv 64 cur) (Z_to_bv 64 4095) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15af4) fc None m (seg_rom usegs)).
Proof.
intros until cur. intros CR CAL TC MI.
pose proof (munch_refl [(RCTX + 920, RCTX + 928)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
pose proof (land_neg_aligned cur CR CAL) as AL.
assert (AL' : Z.land 4095 (bv_unsigned (Z_to_bv 64 (0 + - cur))) = 0) by (rewrite Z.land_comm; exact AL).
change (cur mod 4096 = 0) with (pgal cur) in CAL.
unfold RCTX, RMLOCK, RSSP_GUARD in *. change (324152 + 912) with 325064 in TC. change (324152 + 920) with 325072 in MU. change (324152 + 928) with 325080 in MU.
Local Ltac2 Set LiaHints.tbl := fun () => "0070>16794307354.4022882320372.5022923951931.4024853101803.5031734794215.4154957376530.5067691039343.4000000100200600700800900:SSS2CRSSSF".
st1. st1. rewrite ?AL, ?AL'. st1. st1.
replace (0 + cur) with cur by lia.
st1. st1. st1. st1.
replace (8192 + cur) with (cur + 8192) by lia.
apply evt_done. do 2 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact TC.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma ram_bu_ok : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) (q0 : byte) (q1 : list byte) F fc
(m : word -> option byte) (cur : Z),
0 < cur -> cur + 8192 < 2^64 ->
rw_cells usegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 cur)] ->
evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x15b38) sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192))
(Z_to_bv 64 cur) (Z_to_bv 64 4096) (Z_to_bv 64 0) (Z_to_bv 64 50) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) a6 (Z_to_bv 64 214)
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom usegs))
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 (cur + 8192)) a1 a2 a3 a4 a5 a6 (Z_to_bv 64 214)
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15b18) fc None m (seg_rom usegs)).
Proof.
intros until cur. intros C0 C1b TC.
unfold RCTX, RMLOCK, RSSP_GUARD in *. change (324152 + 912) with 325064 in TC.
st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
st1. st1. st1. st1. st1. st1. st1.
apply evt_done. unfold rmmap_entry. reflexivity.
Qed.
#[using="Type"] Lemma ram_b_store : forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
(w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : word) (q0 : byte) (q1 : list byte) (q2 : word) F fc (m : word -> option byte) (nw : Z),
0 <= nw < 2^64 ->
rw_cells usegs m RCTX [C8 w0; C4 w1; C4 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10] ->
rw_cells usegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 q2] -> mem_inv usegs m ->
evt usegs (fun ms' => exists m',
ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 (nw - 4096)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x15bc4) fc None m' (seg_rom usegs)
/\ munch [(RCTX + 40, RCTX + 48); (RCTX + 920, RCTX + 928)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ rw_cells usegs m' RCTX [C8 w0; C4 w1; C4 w2; C8 w3; C8 w4; C8 w5; C8 (Z_to_bv 64 1); C8 w7; C8 w8; C8 w9; C8 w10]
/\ rw_cells usegs m' (RCTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 nw)])
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 nw) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15b38) fc None m (seg_rom usegs)).
Proof.
intros until nw. intros NW HC TC MI.
pose proof (munch_refl [(RCTX + 40, RCTX + 48); (RCTX + 920, RCTX + 928)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
unfold RCTX, RMLOCK, RSSP_GUARD in *. change (324152 + 912) with 325064 in TC.
change (324152 + 40) with 324192 in MU. change (324152 + 48) with 324200 in MU. change (324152 + 920) with 325072 in MU. change (324152 + 928) with 325080 in MU.
Local Ltac2 Set LiaHints.tbl := fun () => "0090>22882320372.5525675820201.5525675820201.6242212818192.5546723112739.5351163085556.6254957376530.5559715610898.626361280528.62 000001002003004005006007008009SSSSSSSSS".
st1. st1. rewrite ?(unsigned_lit nw) by lia. replace (nw + - (4096)) with (nw - 4096) by lia. st1. change (Z.shiftr 4096 12) with 1. st1. st1.
apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact HC| exact TC].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma ram_bl_ok : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
(w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : word) (q0 : byte) (q1 : list byte) (q2 : word) F fc (m : word -> option byte) (nw : Z),
0 <= nw < 2^64 ->
rw_cells usegs m RCTX [C8 w0; C4 w1; C4 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10] ->
rw_cells usegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 q2] -> mem_inv usegs m ->
evt usegs (fun ms' => exists m',
ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 (nw - 4096)) (Z_to_bv 64 nw) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x15bc4) fc None m' (seg_rom usegs)
/\ munch [(RCTX + 40, RCTX + 48); (RCTX + 920, RCTX + 928)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ rw_cells usegs m' RCTX [C8 w0; C4 w1; C4 w2; C8 w3; C8 w4; C8 w5; C8 (Z_to_bv 64 1); C8 w7; C8 w8; C8 w9; C8 w10]
/\ rw_cells usegs m' (RCTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 nw)])
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 nw) (Z_to_bv 64 nw) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15adc) fc None m (seg_rom usegs)).
Proof.
intros until nw. intros NW HC TC MI.
st1. rewrite bv_eqb_refl. cbv iota.
eapply (ram_b_store sp gp tp t0 t1 t2 _ a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 q0 q1 q2 F fc m nw NW HC TC MI).
Qed.
#[using="Type"] Lemma ram_brk_dead : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
(q0 : byte) (q1 : list byte) (q2 : word) F fc (m0 m : word -> option byte) (st : mstate),
rmrep st m0 -> munch [(RCTX + 920, RCTX + 928)]%Z m0 m -> wmono usegs m0 m ->
c_avail_meta_area_count (ctx st) = 0 ->
rw_cells usegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 q2] -> q0 = b8 (c_seq (ctx st)) -> q1 = zeros 7 -> mem_inv usegs m ->
evt usegs (fun ms' => exists m',
ms' = MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15b64) fc None m' (seg_rom usegs)
/\ munch [(RCTX + 920, RCTX + 928)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ rmrep (upd_ctx (set_brk BrkDead) st) m')
(MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15b4c) fc None m (seg_rom usegs)).
Proof.
intros until st. intros MR MU0 WM0 CNT TC -> -> MI.
pose proof MR as (WF & (C1 & _) & _). unfold rctx_head_cells, rsecw in C1. rewrite CNT in C1. unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
Local Ltac2 Set LiaHints.tbl := fun () => "00<0>1123187672.48 22178757405.4822706556426.4622882320372.5224853101803.5228341373945.4831332194325.4634752135640.4842212818192.5249253317592.4854957376530.5263578776024.4800000100200600700800900=00>00?00@00A00BSSS2HySSSS2HySSSSS".
lazymatch type of C1 with rw_cells _ _ _ ?cs =>
assert (C1' : rw_cells usegs m RCTX cs)
by (eapply RMallocKit_B.rrw_cells_agree; [exact C1| | exact WM0]; cbn [cells_size csize Nat.add]; intros y Hy; apply MU0;
rewrite wa_unsigned by (unfold RCTX in *; lia); unfold RCTX in *; cbn; lia) end.
clear C1.
pose proof (munch_refl [(RCTX + 920, RCTX + 928)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
unfold RCTX, RMLOCK, RSSP_GUARD in *. change (324152 + 912) with 325064 in TC.
change (324152 + 920) with 325072 in MU, MU0. change (324152 + 928) with 325080 in MU, MU0.
st1. st1. st1. st1. rewrite bv_eqb_refl. cbv iota.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR' : rmrep (upd_ctx (set_brk BrkDead) st) mX) end.
{ eapply (rmrep_ctx_frameW st _ m0 _ [(RCTX + 920, RCTX + 928)]%Z MR); try reflexivity.
- unfold RCTX. first [exact MU0 | eapply munch_trans; [exact MU0| exact MU]].
- first [exact WM0 | eapply wmono_trans; [exact WM0| exact WM]].
- intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- left. unfold ctx_tail_cells, brk_word, RCTX. cbn [ctx upd_ctx s_ctx set_brk c_brk c_seq]. change (324152 + 912) with 325064.
replace (wz (2 ^ 64 - 1)) with (Z_to_bv 64 (-1)) by (apply Z_to_bv_eqm; reflexivity).
lazymatch goal with H : rw_cells usegs ?mX 325064 _ |- _ => exact H end. }
apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact MR'.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma ram_bl_fail : forall (sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
F fc (m : word -> option byte) (st : mstate) (old : Z),
rmrep st m -> c_avail_meta_area_count (ctx st) = 0 -> 0 < old -> old + 4096 < 2^64 -> mem_inv usegs m ->
evt usegs (fun ms' => exists m',
ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (old + 4096)) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15b64) fc None m' (seg_rom usegs)
/\ munch [(RCTX + 920, RCTX + 928)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ rmrep (upd_ctx (set_brk BrkDead) st) m')
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (old + 4096)) (Z_to_bv 64 old) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15adc) fc None m (seg_rom usegs)).
Proof.
intros until old. intros MR CNT O0 O1 MI.
pose proof MR as (WF & (_ & _ & _ & _ & _ & C6) & _). unfold ctx_tail_cells in C6.
st1.
assert (CF : bv_eqb (Z_to_bv 64 old) (Z_to_bv 64 (old + 4096)) = false) by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
rewrite CF; clear CF.
st1.
eapply (ram_brk_dead sp gp tp t0 t1 t2 _ _ _ _ a2 a3 a4 a5 a6 _ s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ _ F fc m m st MR (munch_refl _ m) (wmono_refl usegs m) CNT C6 eq_refl eq_refl MI).
Qed.
#[using="Type"] Lemma ram_bu_fail : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
(q0 : byte) (q1 : list byte) F fc (m0 m : word -> option byte) (st : mstate) (cur : Z),
rmrep st m0 -> munch [(RCTX + 920, RCTX + 928)]%Z m0 m -> wmono usegs m0 m ->
c_avail_meta_area_count (ctx st) = 0 -> 0 < cur -> cur < 2^64 ->
rw_cells usegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 cur)] -> q0 = b8 (c_seq (ctx st)) -> q1 = zeros 7 -> mem_inv usegs m ->
evt usegs (fun ms' => exists m',
ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15b64) fc None m' (seg_rom usegs)
/\ munch [(RCTX + 920, RCTX + 928)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ rmrep (upd_ctx (set_brk BrkDead) st) m')
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 cur) a1 a2 a3 a4 a5 a6 (Z_to_bv 64 214)
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15b18) fc None m (seg_rom usegs)).
Proof.
intros until cur. intros MR MU0 WM0 CNT C0 C1b TC -> -> MI.
st1.
assert (CF : negb (bv_eqb (Z_to_bv 64 cur) (Z_to_bv 64 (cur + 8192))) = true).
{ apply Bool.negb_true_iff. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
apply Z.eqb_neq. Local Ltac2 Set LiaHints.tbl := fun () => "0020>22925851801.403023788465.47 00000800;S2C03C1bS1H".
rewrite (Z.mod_small cur) by lia. Z.div_mod_to_equations. lia. }
rewrite CF; clear CF.
eapply (ram_brk_dead sp gp tp t0 t1 t2 _ _ _ _ a2 a3 a4 a5 a6 _ s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ _ F fc m0 m st MR MU0 WM0 CNT TC eq_refl eq_refl MI).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
