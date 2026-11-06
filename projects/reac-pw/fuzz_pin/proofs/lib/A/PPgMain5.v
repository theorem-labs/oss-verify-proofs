(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_knock/lib/A/APgMain7.v at 6ebe35ba632; made the exit segment
   S5 of reac-pw/fuzz_pin's ASan harness walk (LLVMFuzzerTestOneInput 0x806b4, fuzz_pin.asan sha256
   3e4859aed23f78a6eb028120d664abda29bcb8a3bfdea5d6ee5b32b646de9d16): the exit state is lib/A/PPgMainSt.v's ss_X with
   INV_X, the lemma is pm_S5 (rt_post's PX is True, so the PX step and the general rt_XP form are dropped), the module
   paths are pin's. rule 24 (reuse): no function is proved here; this is one segment of the harness walk.

   THE LEMMA
     pm_S5 : rt_from B MT FP (rt_post B MT FP) ss_X (INV_X B MT)
   in Section c with B, MT, FP and MTL TL LAWS ML ASF FFL MTF.

   THE CODE (the neutral disassembly of the function, 0x80934 .. 0x80a10)
     0x80934-0x8093c  addi a0,zero,-8; sb a0,4(s7); sb a0,8(s7)   the shadow bytes of F+32 and F+64 := 0xf8
     0x80940-0x80948  lui/addiw a0 = 0x45E0360E; sd a0,0(s8)      F[0] := 0x45E0360E (s8 = F)
     0x8094c          beqz s2,0x809a0                             the real-stack test; NOT taken (s2 = F)
     0x80950-0x80990  addi a0,zero,-11; 16 x sb a0,k(s7)          the frame's 16 shadow bytes := 0xf5
     0x80994-0x80998  ld a0,0x78(s2); sb zero,0(a0)               *(the flag address at F+120) := 0: frees the frame
     0x8099c          j 0x809d0
     0x809a0-0x809cc  12 x sb zero,k(s7)                          the real-stack path: never reached
     0x809d0-0x80a10  a0 := 0; addi sp,s0,-0x80; 13 restores (ra, s0-s11 from sp0-8 .. sp0-104); addi sp,sp,0x80; ret
   No call and no cut site in 0x80934-0x80a10.

   THE REAL-STACK PATH IS NOT REACHED. s2 is SOff 75 0 = F, and ss_X carries the atom (75, HPTR 5): F lies in the
   heap-pointer range, 32-aligned, so it is not 0 and the symbolic executor takes beqz s2 as not taken.

   WHERE PIN DIFFERS FROM THE DONOR
   - ss_X is PPgMainSt.v's: the frame region 75 is [0,128) writable with the flag chunk at 120 (knock: [0,32) and
     [112,128)); there is no spill region 70, as s2 and s8 hold F in registers (knock reloads it from 16(s1) / 24(s1)).
   - Two more shadow stores at the start (s7 + 4, s7 + 8 := 0xf8); fs_rwF makes the 16 shadow bytes writable first.
   - INV_X is k <= RT_EV /\ acc <= c_T cx /\ Permutation ..., with RT_EV = 2 (one malloc, one free).
   - rt_post's PX is True: its conjunct is closed by I. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import AWalkFw1 AWalkFw2 ACfm PPgMainRt PPgMainSt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : ACeh.ro_tfa_below_ofl}.
(* add the one-byte region of the flag (slot 87) to the state *)
Ltac add_flag_regionRT HS AG E87 Hp HFLrng HFLown HnoF :=
lazymatch type of HS with st_ok _ ?Ev _ _ =>
let HS3 := fresh "HS3" in
pose proof (ast_ok_add_region tfibsegs Ev _ _ (YP09.mkRegion (Some 87%nat) 0 1 0 1 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E87, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable tfibsegs); lazymatch goal with |- apresent _ _ (?fl + ?oo) => replace (fl + oo) with fl by lia end; exact Hp)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; evalE AG;
repeat split; first [zone_lia |
lazymatch goal with |- ?fl + 1 <= ?x + ?l \/ ?x + ?h <= ?fl + 0 =>
destruct (Z_lt_ge_dec fl (x + l)); [left; lia|]; destruct (Z_lt_ge_dec fl (x + h)); [exfalso | right; lia];
first [apply (HnoF fl); [lia | exact HFLown] | match goal with |- ?g => idtac "DISJFAIL" g end] end
| match goal with |- ?g => idtac "DISJ?" g end ])) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
(* every writable byte of the run's state is the frame's, its shadow's, the stack's or the flag (class 1: 128 bytes,
   16 shadow bytes) *)
Ltac wrangeRT AG fpos F EFA EFL :=
let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros a (r & Hin & Hr); rewrite ?EFA, ?EFL;
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalE AG; intros Hr;
first [ exfalso; clear - Hr; lia
| right; clear - Hr; lia
| left; left; lazymatch goal with FFS : LLVMF_STK = _ |- _ => clear - Hr FFS; lia end
| left; right; right; right; exists 1, fpos; split; [left; reflexivity|];
first [ left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 1) with 128; rewrite ?EFA; fold F; clear - Hr; lia
| right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16; rewrite ?EFA; fold F; unfold SB; clear - Hr; lia ]
| match goal with |- ?g => match type of Hr with ?t => idtac "WRFAIL" t g end end; fail 2 "wrangeRT" ]
| ]);
destruct Hin.
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Variable FP : list (Z * Z).
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Hypothesis MTF : ameter_fs_laws MT.
(* S5 EXIT: 0x80934 .. ret 0x80a10 *)
Lemma pm_S5 : rt_from B MT FP (rt_post B MT FP) ss_X (INV_X B MT).
Proof.
rt_prelude.
pose proof HINV as (Hk3 & Hacc & HPerm3). cbn [c_ly c_S] in HPerm3. cbn [c_T] in Hacc.
relowRT HS AG E10 E11 E32 E10n E11n E32n.
destruct (FFL _ _ _ _ _ 1 fpos (proj1 HJ3) Hfin3) as (HFLpres' & HFLown' & HFLrng'). rewrite ?EFL3 in HFLpres'. rewrite ?EFL3 in HFLown'. rewrite ?EFL3 in HFLrng'. fold FL in HFLpres', HFLown', HFLrng'.
assert (HnoF : forall a, F <= a < F + 128 -> ~ aowned B ly3 S3 a) by (intros a Ha; exact (proj2 (HFpres3 a Ha))).
fs_rwF HS E88 HFSpres3.
add_flag_regionRT HS AG E87 HFLpres' HFLrng' HFLown' HnoF.
aj_run_flag_sh tfibtbl_lib_ok HS HJ3; [clear; lia | wrangeRT AG fpos F EFA3 EFL3 | flag0 E87 EFL3 |].
rreg HS (1%bv : bv 5) Rra. rreg HS (10%bv : bv 5) Ra0.
lazymatch goal with |- SRr _ ?Wx _ _ =>
eapply (SRr_ret_at tfibsegs tfibtbl_lib tfibtbl_lib_ok Hwx_tfa Wx _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)) end.
intros mat'. unfold rt_post, rt_postP. cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_pl c_fpos c_sp1 c_E0 c_T].
lazymatch type of HJ3 with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx _ _ _ ?kx =>
lazymatch goal with |- exists ly' S' regs' mem' md' k', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists lyx, Sx, rg, mm, mdx, kx end end.
split.
{ unfold cfg_at. rewrite Rra. cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 1%nat) by lia.
rewrite (EE 1%nat 1%bv eq_refl). rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned.
rewrite Hra1. unfold raZ in Hra. unfold w64. rewrite <- Hra, Z_to_bv_bv_unsigned. reflexivity. }
split; [cbn [ms_mem]; apply (ajournal_materialize tfibsegs _ LAWS tfib_segs_low); exact HJ3|].
split; [exact Hk3|].
split; [apply aregs_preserved_eqs; creg HS AG EE|].
split; [rewrite Ra0; reflexivity|].
split; [unfold ablocks; rewrite blocks_stack_free_state; fold (ablocks B ly3 S3); exact HPerm3|].
split; [unfold stack_free_state; apply (mo_le_set_fs_r MT MTF); exact (mo_le_mono MT MTL _ _ _ _ HMLE Hacc)|].
exact I.
Qed.
End c.
End b.
