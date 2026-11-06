(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the tables of __asan_stack_free_8 for libreac/fuzz_scene's ASAN image, in the
   Tbl / walk split of a working branch's lib/A/Rt/StackMalloc4Tbl.v. This file holds every address and constant of that
   image; the walk over these names is lib/Reusable/StackFree8.v, which holds no address and is shared with the
   asan-ubsan image (its twin table is lib/AU/Rt/StackFree8Tbl.v). *)

(*   Every value below is MEASURED from the pinned image projects/libreac/bin/fuzz_scene/fuzz_scene.asan
   (sha256 43654a025fd02e1f248bcaf6b8ac44f9e5dbded7f2fc1d9a1e90f9d74feb3026, 579368 bytes, = harness.yaml's pin) with
   the symbols of its unstripped twin, pyelftools 0.33 + capstone 5.0.7
   (facts.py, rerun before this file was committed):
     __asan_stack_free_8                     = 0x3f588, 80 bytes, 20 four-byte words   (PC_STACK_FREE_8)
     the jal at 0x3f5b4 (word #11) targets    0x3f5d8 = __asan::MemToShadow (the static copy, 1 of 5)
       (= a Theorem Labs lane's PC_MEM_TO_SHADOW, lib/A/Rt/StackMalloc8Tbl.v:62; CID8 and PC_POISON_SHADOW come from there too)
       and its return pc is                   0x3f5b8                                   (MTS_RET)
     the tail j at 0x3f5d4 (word #19) targets 0x55bb8 = __asan::PoisonShadow(ul,ul,uc)   (PC_POISON_SHADOW)
     word #0  0xfe010113 addi sp,sp,-0x20  -> the walk's stack window SF_WIN 32
     word #6  0x00004537 lui a0,4          -> FS_B 16384 = fs_frame_bytes 8; the flag pointer at frame + 0x3ff8
     word #12 0x0f500613 addi a2,zero,0xf5 -> the poison value PoisonShadow is called with
     image top (last PT_LOAD end, page-rounded) = 0x5f9000                               (IMG_END)
   Read by the two summarised callees only, so used by no proof here (for the record, each MEASURED the same way):
     GOT 0x9b710 -> __asan_shadow_memory_dynamic_address 0xa37f8 (.bss); GOT 0x9b718 / 0x9b720 / 0x9b728 ->
     kMidMemBeg 0xa44e8 / kMidMemEnd 0xa44f0 / kHighMemEnd 0xa44e0; can_poison_memory 0xa305c;
     GOT 0x9b730 -> __interception::real_memset 0x9d580 (link-time value = musl memset 0x94e40);
     GOT 0x9b700 -> common_flags 0x135328 (+0x78 = clear_shadow_mmap_threshold 0x1353a0).
   A relocated file that disagrees with any of these values is a FINDING, not something to patch quietly. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0t YCe5.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import StackFreeDef AsStackLeaf.
From OSSVerify.libreac.fuzz_scene.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import AB1v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Rt Require Import StackMalloc8Tbl.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import StackFree8.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition PC_STACK_FREE_8 : Z := 0x3f588.
Definition MTS_RET : Z := 0x3f5b8.
Definition IMG_END : Z := 0x5f9000.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition tbl_sf : ctable := Eval vm_compute in build_table tfibsegs PC_STACK_FREE_8 20 TEmpty.
Lemma tbl_sf_eq : tbl_sf = build_table tfibsegs PC_STACK_FREE_8 20 TEmpty. Proof. vm_cast_no_check (eq_refl tbl_sf). Qed.
Lemma tbl_sf_ok : table_ok tfibsegs tbl_sf. Proof. rewrite tbl_sf_eq. apply build_table_ok0. unfold PC_STACK_FREE_8. lia. Qed.
(* The table holds exactly the 20 measured words of __asan_stack_free_8, and nothing at PC_MEM_TO_SHADOW or below PC_STACK_FREE_8. *)
Example tbl_sf_words :
map (clookup tbl_sf) [0x3f588; 0x3f58c; 0x3f590; 0x3f594; 0x3f598; 0x3f59c; 0x3f5a0; 0x3f5a4; 0x3f5a8; 0x3f5ac;
0x3f5b0; 0x3f5b4; 0x3f5b8; 0x3f5bc; 0x3f5c0; 0x3f5c4; 0x3f5c8; 0x3f5cc; 0x3f5d0; 0x3f5d4; 0x3f5d8; 0x3f584] =
map Some [0xfe010113; 0x00113c23; 0x00813823; 0x00913423; 0x00058413; 0x00050493; 0x00004537; 0x00a48533; 0xff853503;
0x00050023; 0x00048513; 0x024000ef; 0x0f500613; 0x00048513; 0x00040593; 0x01813083; 0x01013403; 0x00813483;
0x02010113; 0x5e41606f] ++ [None; None].
Proof. vm_compute. reflexivity. Qed.
Lemma Hwx_sfa : wx_segs_nowrap tfibsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma img_bound : forall a, YG0d.in_img tfibsegs a -> a < IMG_END.
Proof.
intros a (sg & Hin & Hr). unfold tfibsegs, Asan.M.loaded_segments in Hin. cbn in Hin.
unfold IMG_END. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hr; lia.
Qed.
Lemma fseg_none : forall a, ~ YG0d.in_img tfibsegs a -> find_segment tfibsegs a 1 = None.
Proof. exact (YCe5.find_segment_none tfibsegs). Qed.
Lemma rom_none : forall a, 0 <= a < 2 ^ 64 -> ~ YG0d.in_img tfibsegs a -> seg_rom tfibsegs (Z_to_bv 64 a) = None.
Proof. exact (YCe5.seg_rom_none tfibsegs). Qed.
Lemma mts_ret_ok : YK0s.ret_ok (Z_to_bv 64 MTS_RET). Proof. vm_compute. reflexivity. Qed.
Lemma mts_ret_small : 0 <= MTS_RET < 2 ^ 64. Proof. unfold MTS_RET. lia. Qed.
Definition RUN (s : sstate) := sym_runN tfibsegs tbl_sf FUEL s.
(* Phase 1: the entry to the jal into MemToShadow. *)
Definition e1 : sstate := Eval vm_compute in fst (RUN (ss0_of PC_STACK_FREE_8)).
Lemma r_sf1 : sym_runN tfibsegs tbl_sf FUEL (ss0_of PC_STACK_FREE_8) = (e1, RS_stopped SR_fetch).
Proof. vm_compute. reflexivity. Qed.
(* Phase 2: from MemToShadow's return to the tail jump into PoisonShadow. *)
Definition e2 : sstate := Eval vm_compute in fst (RUN (ss2_of MTS_RET e1)).
Lemma r_sf2 : sym_runN tfibsegs tbl_sf FUEL (ss2_of MTS_RET e1) = (e2, RS_stopped SR_fetch).
Proof. vm_compute. reflexivity. Qed.
Lemma e1_pc : ss_pc e1 = PC_MEM_TO_SHADOW. Proof. vm_compute. reflexivity. Qed.
Lemma e1_resv : ss_resv e1 = None. Proof. vm_compute. reflexivity. Qed.
Lemma e1_a0 : sr_get (ss_regs e1) 10%bv = SOff 10 0. Proof. vm_compute. reflexivity. Qed.
Lemma e1_ra : sr_get (ss_regs e1) 1%bv = SLit MTS_RET. Proof. vm_compute. reflexivity. Qed.
Lemma e1_atoms : ss_atoms_lt KA e1 = true /\ regions_wf (ss_mem e1) = true /\
no_cdata (ss_mem e1) = true /\ mem_atoms_lt KA (ss_mem e1) = true.
Proof. vm_compute. repeat split. Qed.
Lemma e1_mem : exists cs, ss_mem e1 = [stk_of cs; rFF; rFLG0].
Proof. eexists. vm_compute. reflexivity. Qed.
Lemma e2_pc : ss_pc e2 = PC_POISON_SHADOW. Proof. vm_compute. reflexivity. Qed.
Lemma e2_resv : ss_resv e2 = None. Proof. vm_compute. reflexivity. Qed.
Lemma e2_r10 : sr_get (ss_regs e2) 10%bv = SOff 10 0. Proof. vm_compute. reflexivity. Qed.
Lemma e2_r11 : sr_get (ss_regs e2) 11%bv = SOff 11 0. Proof. vm_compute. reflexivity. Qed.
Lemma e2_r12 : sr_get (ss_regs e2) 12%bv = SLit 0xf5. Proof. vm_compute. reflexivity. Qed.
Lemma e2_keepb : forallb (fun r => sv_eqb (sr_get (ss_regs e2) (Z_to_bv 5 r)) (SOff (Z.to_nat r) 0)) keep2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma e2_mem : exists cs, ss_mem e2 = [stk_of cs; rFF; rFLG0].
Proof. eexists. vm_compute. reflexivity. Qed.
Section inst.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis MTS_SUM : mem_to_shadow_realizes tfibsegs B PC_MEM_TO_SHADOW.
Hypothesis PS_SUM : poison_shadow_realizes tfibsegs B PC_POISON_SHADOW.
Theorem sce_stack_free_8 : astack_free_realizes tfibsegs B PC_STACK_FREE_8 CID8.
Proof.
exact (astack_free_8_at tfibsegs PC_STACK_FREE_8 PC_MEM_TO_SHADOW MTS_RET PC_POISON_SHADOW IMG_END tbl_sf e1 e2
Hwx_sfa tbl_sf_ok img_bound ltac:(unfold IMG_END; lia) fseg_none rom_none mts_ret_ok mts_ret_small
r_sf1 r_sf2 e1_pc e1_resv e1_a0 e1_ra e1_atoms e1_mem
e2_pc e2_resv e2_r10 e2_r11 e2_r12 e2_keepb e2_mem B LAWS MTS_SUM PS_SUM).
Qed.
End inst.
End e.
