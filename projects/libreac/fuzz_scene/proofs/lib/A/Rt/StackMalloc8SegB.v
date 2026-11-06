(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: new file for libreac/fuzz_scene (asan). Seg B of the __asan_stack_malloc_8
   walk: `sm8_segB` of lib/A/Rt/StackMalloc8Cuts.v, the 64-frame flag-search loop from PC_SM8_LOOP to
   PC_SM8_FOUND. The loop lemma is cgif_rgb_fuzzer's class-7 `probe_loop` (lib/YF9a.v:251, used at
   lib/YF9c.v:214), ported to class 8: one generic induction over fs_probe's fuel, with the frame count
   `fs_frames CID8` in place of rgb's FS_N = 128. The seven loop words are the class-7 words (DELTA-7to8.md);
   the fetch lemmas below check each of them against the image at PC_SM8_LOOP + k.
   The all-busy exit (the fall-through after `bnez a0`) is not walked: the premise
   `apath (stack_malloc CID8 S) [] (PFake CID8 pos, S')` makes fs_probe return Some, and the loop lemma follows
   fs_probe to its free flag. No literal scene address in this file: every address is a name of
   lib/A/Rt/StackMalloc8Tbl.v. No Section hypothesis: the loop reads only the class-8 flags, which AR gives
   (am_flags), and the layout facts that put them outside the walk's stack window (am_layout). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import AB1v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Rt Require Import StackMalloc8Tbl StackMalloc8Cuts.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN32.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* The seven loop instructions, PC_SM8_LOOP + 0x0 .. + 0x18, read from the image. *)
Definition sm8b_tbl : ctable := Eval vm_compute in build_table tfibsegs PC_SM8_LOOP 7 TEmpty.
Lemma sm8b_tbl_eq : sm8b_tbl = build_table tfibsegs PC_SM8_LOOP 7 TEmpty.
Proof. vm_cast_no_check (eq_refl sm8b_tbl). Qed.
Lemma sm8b_tbl_ok : table_ok tfibsegs sm8b_tbl.
Proof. rewrite sm8b_tbl_eq. apply build_table_ok; [unfold PC_SM8_LOOP; lia | apply table_ok_empty]. Qed.
Lemma sm8b_fetch_lit : forall (p : word) (w : bv 32), clookup sm8b_tbl (bv_unsigned p) = Some (bv_unsigned w) -> fetch_word tfibsegs p = Some w.
Proof. intros p w H. rewrite <- (Z_to_bv_bv_unsigned 64 p), <- (Z_to_bv_bv_unsigned 32 w). apply sm8b_tbl_ok. exact H. Qed.
Lemma sm8b_wx : wx_segs_nowrap tfibsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma sm8b_frames : fs_frames CID8 = 64.
Proof. vm_compute. reflexivity. Qed.
Lemma sm8b_mod64 : forall h, (h mod 2 ^ 64) mod 64 = h mod 64.
Proof.
intros h. pose proof (Z.div_mod h (2 ^ 64) ltac:(lia)) as E.
rewrite E at 2. rewrite Z.add_comm.
replace (2 ^ 64 * (h / 2 ^ 64)) with ((h / 2 ^ 64 * 2 ^ 58) * 64) by (rewrite <- Z.mul_assoc; change (2 ^ 58 * 64) with (2 ^ 64); ring).
rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma sm8b_v_and_mask : forall h, v_and (Z_to_bv 64 h) (Z_to_bv 64 (fs_frames CID8 - 1)) = Z_to_bv 64 (h mod fs_frames CID8).
Proof.
intros h. rewrite sm8b_frames. unfold v_and. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small (64 - 1)) by lia. replace (64 - 1) with (Z.ones 6) by reflexivity. rewrite Z.land_ones by lia.
change (2 ^ 6) with 64. rewrite sm8b_mod64. reflexivity.
Qed.
Lemma sm8b_step_and_at : forall segs regs pc mem rom w rd rs1 rs2 v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op ALU_AND rd rs1 rs2, 4%Z) ->
bv_eqb rd 0 = false ->
v_and (getr regs rs1) (getr regs rs2) = v ->
RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv. rewrite (step_and segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity.
Qed.
Lemma sm8b_v_addiw_dec : forall c, 1 <= c < 2 ^ 31 -> v_addiw (Z_to_bv 64 c) (-1) = Z_to_bv 64 (c - 1).
Proof.
intros c Hc. unfold v_addiw. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296. f_equal.
change (2 ^ 31)%Z with 2147483648 in Hc. rewrite Z.mod_small by lia. lia.
Qed.
Lemma sm8b_stack_malloc_inv : forall cid S pos S',
apath (stack_malloc cid S) [] (PFake cid pos, S') ->
exists hint', fs_probe (Z.to_nat (fs_frames cid)) (fs_live (st_fs S)) cid (znth 0 cid (fs_hint (st_fs S))) = Some (pos, hint').
Proof.
intros cid S pos S' H. unfold stack_malloc, bind, get, put, ret in H. cbn [ibind] in H.
destruct (fs_probe (Z.to_nat (fs_frames cid)) (fs_live (st_fs S)) cid (znth 0 cid (fs_hint (st_fs S)))) as [[p h']|] eqn:Hp.
- cbn [ibind apath] in H. injection H as <- <-. exists h'. reflexivity.
- cbn [apath] in H. discriminate H.
Qed.
Lemma sm8b_aview_byte : forall H mem a v,
aview tfibsegs H mem a = Some v -> mbyte tfibsegs (mrestrict H mem) a = Some (Z_to_bv 8 v).
Proof.
intros H mem a v Hv. unfold aview in Hv. destruct (mbyte tfibsegs (mrestrict H mem) a) as [b|]; [|discriminate Hv].
cbn in Hv. injection Hv as <-. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma sm8b_aview_same : forall H (mem mem' : word -> option byte) a,
mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a) -> aview tfibsegs H mem' a = aview tfibsegs H mem a.
Proof. intros H mem mem' a E. unfold aview, mbyte, mrestrict. rewrite E. reflexivity. Qed.
Lemma sm8b_flag_addr : forall ly p, flag_addr ly CID8 p = flag_addr ly CID8 0 + p.
Proof. intros ly p. unfold flag_addr, fs_flag_off. lia. Qed.
End e.
Ltac sm8b_ftac := apply sm8b_fetch_lit; vm_compute; reflexivity.
Ltac sm8b_steplb1 F0 D RD := let F := litF F0 in
chain_step;
[ reflexivity
| eapply step_lbu; [ exact F | reflexivity | exact D | gr; imm_norm; rewrite v_addi_lit, Z.add_0_r; exact RD ]
| step_simpl ].
Ltac sm8b_svand F0 D vv := let F := litF F0 in
chain_step;
[ reflexivity
| eapply sm8b_step_and_at with (v := vv); [ exact F | reflexivity | exact D | reflexivity | val ]
| step_simpl ].
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma sm8b_F0 : fetch_word tfibsegs (Z_to_bv 64 (PC_SM8_LOOP + 0x0)) = Some (0x00f678b3%bv : bv 32). Proof. sm8b_ftac. Qed.
Lemma sm8b_D0 : decode_any (0x00f678b3%bv : bv 32) = Some (Op ALU_AND 17 12 15, 4%Z). Proof. vm_refl_bv. Qed.
Lemma sm8b_F4 : fetch_word tfibsegs (Z_to_bv 64 (PC_SM8_LOOP + 0x4)) = Some (0x011706b3%bv : bv 32). Proof. sm8b_ftac. Qed.
Lemma sm8b_D4 : decode_any (0x011706b3%bv : bv 32) = Some (Op ALU_ADD 13 14 17, 4%Z). Proof. vm_refl_bv. Qed.
Lemma sm8b_F8 : fetch_word tfibsegs (Z_to_bv 64 (PC_SM8_LOOP + 0x8)) = Some (0x0006c283%bv : bv 32). Proof. sm8b_ftac. Qed.
Lemma sm8b_D8 : decode_any (0x0006c283%bv : bv 32) = Some (Load SZ1 false 5 13 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma sm8b_Fc : fetch_word tfibsegs (Z_to_bv 64 (PC_SM8_LOOP + 0xc)) = Some (0x04028063%bv : bv 32). Proof. sm8b_ftac. Qed.
Lemma sm8b_Dc : decode_any (0x04028063%bv : bv 32) = Some (Branch BC_EQ 5 0 64, 4%Z). Proof. vm_refl_bv. Qed.
Lemma sm8b_F10 : fetch_word tfibsegs (Z_to_bv 64 (PC_SM8_LOOP + 0x10)) = Some (0xfff5051b%bv : bv 32). Proof. sm8b_ftac. Qed.
Lemma sm8b_D10 : decode_any (0xfff5051b%bv : bv 32) = Some (OpImm32 10 10 4095, 4%Z). Proof. vm_refl_bv. Qed.
Lemma sm8b_F14 : fetch_word tfibsegs (Z_to_bv 64 (PC_SM8_LOOP + 0x14)) = Some (0x00160613%bv : bv 32). Proof. sm8b_ftac. Qed.
Lemma sm8b_D14 : decode_any (0x00160613%bv : bv 32) = Some (OpImm ALU_ADD 12 12 1, 4%Z). Proof. vm_refl_bv. Qed.
Lemma sm8b_F18 : fetch_word tfibsegs (Z_to_bv 64 (PC_SM8_LOOP + 0x18)) = Some (0xfe0514e3%bv : bv 32). Proof. sm8b_ftac. Qed.
Lemma sm8b_D18 : decode_any (0xfe0514e3%bv : bv 32) = Some (Branch BC_NE 10 0 8168, 4%Z). Proof. vm_refl_bv. Qed.
Section o.
Variables (live : list (Z * Z)) (FL : Z) (mem rom : word -> option byte).
Hypothesis HFL : 0 <= FL /\ FL + fs_frames CID8 < 2 ^ 64.
Hypothesis Hflags : forall p, 0 <= p < fs_frames CID8 ->
rdn tfibsegs mem (Z_to_bv 64 (FL + p)) 1 = Some [Z_to_bv 8 (if mem_pos live CID8 p then 1 else 0)].
(* The registers the loop never writes: all but t0, a0, a2, a3 and a7. *)
Definition sm8b_lkeep (x : bv 5) : Prop := x <> 5%bv /\ x <> 10%bv /\ x <> 12%bv /\ x <> 13%bv /\ x <> 17%bv.
Definition sm8b_lfin (regs : bvmap 5 word) (pc : word) (pos hint' : Z) : Prop :=
exists regs' c', msteps tfibsegs (mkst regs pc mem rom) (mkst regs' (Z_to_bv 64 PC_SM8_FOUND) mem rom)
/\ getr regs' 12 = Z_to_bv 64 (hint' - 1) /\ getr regs' 17 = Z_to_bv 64 pos /\ getr regs' 13 = Z_to_bv 64 (FL + pos)
/\ getr regs' 5 = Z_to_bv 64 0 /\ getr regs' 10 = Z_to_bv 64 c' /\ 1 <= c' <= fs_frames CID8
/\ forall x, sm8b_lkeep x -> getr regs' x = getr regs x.
Lemma sm8b_lfin_steps : forall regs pc regs2 pc2 pos hint',
msteps tfibsegs (mkst regs pc mem rom) (mkst regs2 pc2 mem rom) -> (forall x, sm8b_lkeep x -> getr regs2 x = getr regs x) ->
sm8b_lfin regs2 pc2 pos hint' -> sm8b_lfin regs pc pos hint'.
Proof.
intros regs pc regs2 pc2 pos hint' Hms Hfr (regs' & c' & Hms' & A & Bq & C & D & E & G & K).
exists regs', c'. split; [eapply msteps_trans; [exact Hms | exact Hms']|]. split; [exact A|]. split; [exact Bq|]. split; [exact C|]. split; [exact D|]. split; [exact E|]. split; [exact G|].
intros x Hx. rewrite (K x Hx). apply Hfr. exact Hx.
Qed.
Lemma sm8b_lfin_pc : forall regs (pc pc' : word) pos hint', bv_unsigned pc = bv_unsigned pc' -> sm8b_lfin regs pc' pos hint' -> sm8b_lfin regs pc pos hint'.
Proof. intros regs pc pc' pos hint' H Hf. replace pc with pc' by (apply bv_eq; symmetry; exact H). exact Hf. Qed.
Ltac frame :=
let x := fresh "x" in let Hx := fresh "Hkeep" in
intros x Hx; unfold sm8b_lkeep in Hx; destruct Hx as (?&?&?&?&?); rewrite ?getr_other by assumption; reflexivity.
(* The loop lemma, generic in the fuel: from PC_SM8_LOOP with a2 = h, a5 = the index mask, a4 = the flag base and
   a0 = the fuel, the loop reaches PC_SM8_FOUND exactly where fs_probe finds its free flag. *)
Lemma sm8b_probe_loop : forall fuel h regs pos hint',
fs_probe fuel live CID8 h = Some (pos, hint') ->
getr regs 12 = Z_to_bv 64 h -> getr regs 15 = Z_to_bv 64 (fs_frames CID8 - 1) -> getr regs 14 = Z_to_bv 64 FL ->
getr regs 10 = Z_to_bv 64 (Z.of_nat fuel) -> Z.of_nat fuel <= fs_frames CID8 ->
sm8b_lfin regs (Z_to_bv 64 PC_SM8_LOOP) pos hint'.
Proof.
induction fuel as [|f IH]; intros h regs pos hint' Hp H12 H14 H13 H10 Hfuel; [discriminate Hp|].
destruct HFL as [HFL0 HFL1]. pose proof sm8b_frames as HN.
pose proof (Z.mod_pos_bound h (fs_frames CID8) ltac:(lia)) as Hm.
cbn [fs_probe] in Hp.
pose proof (Hflags (h mod fs_frames CID8) Hm) as RD.
destruct (mem_pos live CID8 (h mod fs_frames CID8)) eqn:Hmp.
-
assert (Hf1 : (1 <= f)%nat) by (destruct f; [cbn in Hp; discriminate Hp | lia]).
eapply sm8b_lfin_steps.
+ norm_pc.
sm8b_svand sm8b_F0 sm8b_D0 (Z_to_bv 64 (h mod fs_frames CID8)); [rewrite (sm8b_v_and_mask h); reflexivity|].
sv sm8b_F4 sm8b_D4 (Z_to_bv 64 (FL + h mod fs_frames CID8)).
sm8b_steplb1 sm8b_F8 sm8b_D8 RD.
stepbf sm8b_Fc sm8b_Dc.
stepiwv sm8b_F10 sm8b_D10 (Z_to_bv 64 (Z.of_nat f)) ltac:(gr; rwH; imm_norm; rewrite sm8b_v_addiw_dec by lia; f_equal; lia).
sv sm8b_F14 sm8b_D14 (Z_to_bv 64 (h + 1)).
stepbt sm8b_F18 sm8b_D18.
apply mst_refl.
+ frame.
+ eapply sm8b_lfin_pc; [| eapply (IH (h + 1))]; [vm_compute; reflexivity | exact Hp | gr; reflexivity | gr; exact H14 | gr; exact H13 | gr; reflexivity | lia].
-
injection Hp as <- <-.
eexists _, (Z.of_nat (S f)). split.
+ norm_pc.
sm8b_svand sm8b_F0 sm8b_D0 (Z_to_bv 64 (h mod fs_frames CID8)); [rewrite (sm8b_v_and_mask h); reflexivity|].
sv sm8b_F4 sm8b_D4 (Z_to_bv 64 (FL + h mod fs_frames CID8)).
sm8b_steplb1 sm8b_F8 sm8b_D8 RD.
stepbt sm8b_Fc sm8b_Dc.
lazymatch goal with |- msteps _ (mkst _ ?p _ _) (mkst _ ?q _ _) =>
replace q with p by (apply bv_eq; vm_compute; reflexivity) end.
apply mst_refl.
+ split; [gr; rewrite H12; f_equal; lia|]. split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; reflexivity|].
split; [gr; exact H10|]. split; [lia | frame].
Qed.
End o.
End g.

(* `x <> r` for two closed register names. *)
Ltac sm8b_lk := unfold sm8b_lkeep; repeat split;
let E := fresh "E" in intro E; apply (f_equal bv_unsigned) in E; vm_compute in E; discriminate E.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section f.
Variable B : asyms.
Theorem sm8_segB_holds : sm8_segB B.
Proof.
unfold sm8_segB. intros ly S W regs mem md pos S' n regs1 mem1 md1 HE HM.
destruct HE as (HPRE & _ & _ & _ & _ & Hpath).
destruct HPRE as (HAR & _ & _ & Hslo & _ & _).
destruct HM as (R2 & R8 & R9 & R18 & R19 & R10 & R11 & R12 & _ & R14 & R15 & _ & RK & SV & MK & SP & SBM).
destruct (sm8b_stack_malloc_inv CID8 S pos S' Hpath) as (hint' & Hprobe).
pose proof sm8b_frames as HN.
pose proof (proj1 HAR) as M.
pose proof (am_layout _ _ _ _ M) as LO.
pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) (ly_F ly, kFakeStackSize) ltac:(unfold owned_extents; cbn; tauto)) as HFapp.
cbn [fst snd] in HFapp. unfold in_app in HFapp.
pose proof (lo_stk_ceil _ LO) as SC.
pose proof ASAN_CEIL_range as [CR _].
assert (HFO : fs_flags_off CID8 = 32640) by (vm_compute; reflexivity).
assert (HFL0 : flag_addr ly CID8 0 = ly_F ly + (kFakeFlagsOff + 32640)) by (unfold flag_addr, fs_flag_off; rewrite HFO; lia).
(* The class-8 flags lie in the fake stack, below the stack, so far from the walk's window. *)
assert (FB : forall p, 0 <= p < fs_frames CID8 ->
0 <= flag_addr ly CID8 0 + p < 2 ^ 64 /\ flag_addr ly CID8 0 + p + SM8_WIN < spZ regs).
{ intros p Hp. rewrite HFL0. rewrite HN in Hp. unfold ESTACK in Hslo.
clear - Hp HFapp SC CR Hslo. unfold kFakeStackSize, kLowShadowBeg, kHighMemBeg, kFakeFlagsOff, SM8_WIN in *. lia. }
assert (HFLb : 0 <= flag_addr ly CID8 0 /\ flag_addr ly CID8 0 + fs_frames CID8 < 2 ^ 64).
{ rewrite HFL0, HN. clear - HFapp SC CR. unfold kFakeStackSize, kLowShadowBeg, kHighMemBeg, kFakeFlagsOff in *. lia. }
assert (FLAGS : forall p, 0 <= p < fs_frames CID8 ->
rdn tfibsegs (mrestrict (w_H W) mem1) (Z_to_bv 64 (flag_addr ly CID8 0 + p)) 1 =
Some [Z_to_bv 8 (if mem_pos (fs_live (st_fs S)) CID8 p then 1 else 0)]).
{ intros p Hp. pose proof (am_flags _ _ _ _ M CID8 p ltac:(unfold CID8; lia) Hp) as Hf.
destruct (FB p Hp) as [FB1 FB2].
rewrite sm8b_flag_addr in Hf.
rewrite <- (sm8b_aview_same (w_H W) mem mem1 _ (MK (Z_to_bv 64 (flag_addr ly CID8 0 + p))
ltac:(rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64); rewrite Z.mod_small by lia; lia))) in Hf.
apply (proj2 (rdn_mbytes tfibsegs _ 1 _ _)). split; [reflexivity|].
intros i Hi. replace i with 0%nat by lia. cbn [nth_error Z.of_nat]. rewrite Z.add_0_r.
exact (sm8b_aview_byte _ _ _ _ Hf). }
destruct (sm8b_probe_loop (fs_live (st_fs S)) (flag_addr ly CID8 0) (mrestrict (w_H W) mem1) (seg_rom tfibsegs)
HFLb FLAGS
(Z.to_nat (fs_frames CID8)) (znth 0 CID8 (fs_hint (st_fs S))) regs1 pos hint' Hprobe
R12 R15 R14 ltac:(rewrite Z2Nat.id by lia; exact R10) ltac:(rewrite Z2Nat.id by lia; lia))
as (regs' & c' & Hms & L12 & L17 & L13 & _ & _ & _ & LK).
unfold cfg_at. eapply (SRr_msteps tfibsegs sm8b_wx W); [rewrite restrict_mkst_fx; exact Hms|].
intros md' Hsbm _. cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
apply SRr_ret. split; [reflexivity|]. exists regs', mem1, md', hint'. split; [reflexivity|].
unfold sm8_midBC.
split; [exact Hprobe|]. split; [exact L12|]. split; [exact L17|].
split; [rewrite sm8b_flag_addr; exact L13|].
split; [etransitivity; [apply LK; sm8b_lk | exact R2]|].
split; [etransitivity; [apply LK; sm8b_lk | exact R8]|].
split; [etransitivity; [apply LK; sm8b_lk | exact R9]|].
split; [etransitivity; [apply LK; sm8b_lk | exact R18]|].
split; [etransitivity; [apply LK; sm8b_lk | exact R19]|].
split; [etransitivity; [apply LK; sm8b_lk | exact R11]|].
split.
{ intros r Hr. etransitivity; [apply LK | exact (RK r Hr)].
assert (Hr' : r = 3 \/ r = 4 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
repeat (destruct Hr' as [Hr' | Hr']; [subst r; sm8b_lk |]). subst r. sm8b_lk. }
split; [exact SV|]. split; [exact MK|]. split; [exact SP|].
exact (same_but_materialized_trans _ _ _ SBM Hsbm).
Qed.
End f.
End d.
