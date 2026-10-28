(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UZ24.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UZ24.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UhI1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UhI1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require ULAQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import ULAQ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UXKA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UXKA.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition grs_entry : Z := 0x28b98.
Definition grs_head : Z := 0x28bb8.
Definition grs_link : Z := 0x28bc8.
Definition gr_ecall_pc : Z := 0x60868.
Definition grs_ret_pc : Z := 0x27890.

Section SeedGrs.
Variables (G : Z) (s0v : word).

Definition grs_frame (m : word -> option byte) (junk16 : list byte) (sbuf : list cell) : Prop :=
rw_cells rsegs m G ([CB 16 junk16] ++ sbuf ++ [C8 (Z_to_bv 64 (-1)); C8 (Z_to_bv 64 lh_seed_addr); C8 s0v; C8 (Z_to_bv 64 grs_ret_pc)]).

Definition grs_head_st (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 : word) (s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state :=
MS (mkR x1 (Z_to_bv 64 G) gp (Z_to_bv 64 0x77c00) t0 t1 t2 (Z_to_bv 64 4) (Z_to_bv 64 (-1)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 grs_head) fc None m (seg_rom rsegs).

Definition gr_pre_post (gp s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (junk16 : list byte) (sbuf : list cell) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 t3 t4 t5 t6 : word) junk8 m',
ms' = MS (mkR (Z_to_bv 64 0x51244) (Z_to_bv 64 (G + -16)) gp (Z_to_bv 64 0x77c00) t0 t1 t2 (Z_to_bv 64 4) (Z_to_bv 64 (-1))
(Z_to_bv 64 (G + 16)) (Z_to_bv 64 4) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 278)
(Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 gr_ecall_pc) fc None m' (seg_rom rsegs)
/\ munch [(G - 16, G)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (G + -16)
/\ rw_cells rsegs m' (G + -16) [CB 8 junk8; C8 (Z_to_bv 64 grs_link)]
/\ grs_frame m' junk16 sbuf.

#[using="Type"] Lemma gr_pre :
forall (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (junk16 : list byte) (sbuf : list cell),
mem_inv rsegs m -> stk rsegs m lo G -> lo <= G - 16 -> alloc_ceiling <= lo -> G + 176 <= 2^64 ->
grs_frame m junk16 sbuf ->
evt rsegs (gr_pre_post gp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo junk16 sbuf m)
(grs_head_st x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until sbuf. intros MI ST LOS LO SPH FR.
unfold grs_head_st, grs_head, grs_frame in *. unfold_consts.
pose proof (rw_cells_bound rsegs m _ _ FR) as FB.
pose proof (munch_refl [(G - 16, G)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
step. step. step. step.
carve_frame 16%nat ST.
step. stepz.
do 10 step.
do 8 step.
unfold gr_pre_post, gr_ecall_pc, grs_link. finish.
all: eassumption.
Qed.

Definition grseed_w (bs : list byte) : word := sext 64 (bv_extract 0 32 (le_bytes_to_word bs)).

Definition gr_full_post (gp s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (errv : word) (junk16 bs rest : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
ms' = MS (mkR (Z_to_bv 64 grs_ret_pc) (Z_to_bv 64 (G + 176)) gp (Z_to_bv 64 0x77c00) t0 t1 t2 s0v (Z_to_bv 64 lh_seed_addr)
(grseed_w bs) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 grs_ret_pc) fc None m' (seg_rom rsegs)
/\ munch [(G - 16, G); (0x77c00 - 164, 0x77c00 - 164 + 4)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (G + 176)
/\ rw_cells rsegs m' (0x77c00 - 164) [C4 errv].

#[using="Type"] Lemma gr_post_full :
forall (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (junk16 junk8 bs rest : list byte) (errv : word),
length bs = 4%nat ->
mem_inv rsegs m -> stk rsegs m lo (G + -16) -> lo <= G - 32 -> alloc_ceiling <= lo -> G + 176 <= 2^64 ->
grs_frame m junk16 [CB 4 bs; CB 124 rest] -> rw_cells rsegs m (G + -16) [CB 8 junk8; C8 (Z_to_bv 64 grs_link)] ->
rw_cells rsegs m (0x77c00 - 164) [C4 errv] ->
evt rsegs (gr_full_post gp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo errv junk16 bs rest m)
(MS (mkR (Z_to_bv 64 0x51244) (Z_to_bv 64 (G + -16)) gp (Z_to_bv 64 0x77c00) t0 t1 t2 (Z_to_bv 64 4) (Z_to_bv 64 (-1))
(len_word bs) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x6086c) fc None m (seg_rom rsegs)).
Proof.
intros until errv. intros LBS MI ST LOS LO GH FR FR16 ERR.
replace (len_word bs) with (Z_to_bv 64 4) by (unfold len_word; rewrite LBS; reflexivity).
unfold grs_frame, grs_link in *. unfold_consts.
pose proof (rw_cells_bound rsegs m _ _ FR) as FB.
pose proof (munch_refl [(G - 16, G); (0x77c00 - 164, 0x77c00 - 164 + 4)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
step. replace (ret_pc (Z_to_bv 64 0x51244)) with (Z_to_bv 64 0x51244) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
step. step. step.
release_frame FR16 ST G.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv rsegs m1 |- _ => rename H into MI1 end.

eapply evt_cut; [eapply (sysret_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 errv lo);
[rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; exact ERR | exact MI1 | rewrite unsigned_lit by lia; lia
| rewrite !unsigned_lit by lia; left; lia | rewrite unsigned_lit by lia; lia] |].
unfold sysret_post. cbv beta. rewrite (unsigned_lit G) by lia. rewrite (unsigned_lit 0x77c00) by lia.
unfold sysret_val, sysret_errno. rewrite (errno_of_small (Z_to_bv 64 4)) by (rewrite unsigned_lit by lia; lia).
post_call rsegs m1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
try clear ST. match goal with H : stk rsegs m2 lo _ |- _ => rename H into ST end.
match goal with H : rw_cells rsegs m2 (490496 + -164) _ |- _ => change (490496 + -164) with 490332 in H; rename H into ERR2 end.
match goal with H : rw_cells rsegs m2 G _ |- _ => rename H into FR2 end.
cbn [app] in FR2.
pose proof (rw_cells_bound rsegs m2 _ _ FR2) as FB2. cbn [cells_size csize Nat.add] in FB2.
step. if_true.
step.
step. if_false.
step.
change (sext 64 (bv_extract 0 32 (le_bytes_to_word bs))) with (grseed_w bs).
step. do 5 step.
release_frame FR2 ST (G + 176).
step. replace (ret_pc (Z_to_bv 64 grs_ret_pc)) with (Z_to_bv 64 grs_ret_pc) by (symmetry; apply ret_pc_even; [unfold grs_ret_pc; lia | reflexivity]).
unfold gr_full_post. finish.
Qed.

#[using="Type"] Lemma rw_cells_recast2 : forall m A (scr sbuf tl : list cell),
rw_cells rsegs m A (scr ++ sbuf ++ tl) -> cells_size scr = 16%nat -> cells_size sbuf = 128%nat ->
rw_cells rsegs m A ([CB 16 (cells_bytes scr)] ++ [CB 128 (cells_bytes sbuf)] ++ tl).
Proof.
intros m A scr sbuf tl H Hs Hb.
pose proof H as [[WF _] _]. apply cells_wf_app in WF as [W1 W23]. apply cells_wf_app in W23 as [W2 W3].
eapply rw_cells_recast; [exact H | | |].
- cbn. split; [rewrite cells_bytes_length by exact W1; exact Hs|]. split; [rewrite cells_bytes_length by exact W2; exact Hb|]. exact W3.
- rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite !app_nil_r. reflexivity.
- rewrite !cells_size_app. cbn [cells_size csize]. lia.
Qed.

Definition at_grs_ret (gp s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (w : word) (m : word -> option byte)
(t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) : machine_state :=
MS (mkR (Z_to_bv 64 grs_ret_pc) (Z_to_bv 64 (G + 176)) gp (Z_to_bv 64 0x77c00) t0 t1 t2 s0v (Z_to_bv 64 lh_seed_addr)
w a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 grs_ret_pc) fc None m (seg_rom rsegs).

Definition grs_reenter_post (gp s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) junk16 sbuf m',
ms' = grs_head_st x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m'
/\ munch [(G, G + 176)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo G
/\ grs_frame m' junk16 sbuf /\ cells_size sbuf = 128%nat.

#[using="Type"] Lemma grs_reenter :
forall (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (w : word),
bv_eqb w (Z_to_bv 64 (-1)) = true ->
mem_inv rsegs m -> stk rsegs m lo (G + 176) -> lo <= G -> alloc_ceiling <= lo -> G + 176 <= 2^64 ->
evt rsegs (grs_reenter_post gp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(at_grs_ret gp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc w m t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6).
Proof.
intros until w. intros EQ MI ST LOS LO GH.
unfold at_grs_ret, grs_ret_pc. unfold_consts.
pose proof (munch_refl [(G, G + 176)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
step. rewrite EQ. step.
carve_frame 176%nat ST.
step. stepz. step. stepz. stepz. stepz. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
match goal with H : rw_cells rsegs mx (G + 0) (?c16 :: ?c4 :: ?c124 :: ?tl) |- _ =>
change (rw_cells rsegs mx (G + 0) ([c16] ++ [c4; c124] ++ tl)) in H; rewrite (Z.add_0_r G) in H; rename H into FRN
end end.
replace (Z_to_bv 64 18446744073709551615) with (Z_to_bv 64 (-1)) in FRN by (apply bv_eq; reflexivity).
rewrite (Z.add_0_r G) in ST.
unfold grs_reenter_post, grs_head_st, grs_head, grs_frame, grs_ret_pc. finish.
all: try exact FRN. all: try reflexivity.
Qed.

Definition grs_exit_post (gp s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (hf : word)
(m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (seed' : word) m',
ms' = MS (mkR x1 (Z_to_bv 64 (G + 176)) gp (Z_to_bv 64 0x77c00) t0 t1 t2 s0v (Z_to_bv 64 lh_seed_addr) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x278a8) fc None m' (seg_rom rsegs)
/\ munch [(GHASH4 + 8, GHASH4 + 12)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' GHASH4 [C8 hf; C4 seed'].

#[using="Type"] Lemma grs_exit :
forall (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (w hf seedv : word),
bv_eqb w (Z_to_bv 64 (-1)) = false ->
mem_inv rsegs m -> rw_cells rsegs m GHASH4 [C8 hf; C4 seedv] -> sx32 seedv = Z_to_bv 64 (-1) ->
evt rsegs (grs_exit_post gp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc hf m)
(at_grs_ret gp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc w m t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6).
Proof.
intros until seedv. intros NEQ MI GC SEQ.
unfold at_grs_ret, grs_ret_pc, lh_seed_addr, GHASH4 in *.
pose proof (munch_refl [(0x66a38 + 8, 0x66a38 + 12)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
step. rewrite NEQ. step.
astep.
rewrite SEQ.
step. rewrite (bv_eqb_refl (Z_to_bv 64 (-1))). cbn [negb].
astep.
step. if_false.
unfold grs_exit_post, GHASH4. finish.
all: eassumption.
Qed.
End SeedGrs.

End RC__1.
