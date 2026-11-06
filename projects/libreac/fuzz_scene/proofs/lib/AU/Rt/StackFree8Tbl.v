(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the tables of __asan_stack_free_8 for libreac/fuzz_scene's ASAN-UBSAN image, in the
   Tbl / walk split of a working branch's lib/A/Rt/StackMalloc4Tbl.v; the asan-ubsan twin of lib/A/Rt/StackFree8Tbl.v. This
   file holds every address and constant of that image; the walk over these names is lib/Reusable/StackFree8.v, which holds
   no address and is shared by both images. The segments are lib/AU/YB1v.v's tfibsegs (= AsanUbsan.M.loaded_segments). *)

(*   Every value below is MEASURED from the pinned image projects/libreac/bin/fuzz_scene/fuzz_scene.asan-ubsan
   (sha256 e98b1ed286c1aa5c3d558cb2069011d2413d58b2122f741531364382a528833f, 580184 bytes, = harness.yaml's pin) with
   the symbols of its unstripped twin (sha256 ef0b41158fe08b45b5a8a0e514f8ebc31f2960d2b90acc03576a682fae2baf33, whose
   PT_LOAD bytes equal the pinned image's at all three functions below), pyelftools 0.33 + capstone 5.0.7; e_flags = 4
   (no RVC). The 20 words are byte-identical to the asan image's (DELTA-7to8.md section 2); tbl_sf_words checks them
   against this image's segments:
     __asan_stack_free_8                     = 0x3f5b4, 80 bytes, 20 four-byte words   (PC_STACK_FREE_8)
     the jal at 0x3f5e0 (word #11) targets    0x3f604 = __asan::MemToShadow (the static copy, 2 of 5) (PC_MEM_TO_SHADOW)
       and its return pc is                   0x3f5e4                                   (MTS_RET)
     the tail j at 0x3f600 (word #19) targets 0x55be4 = __asan::PoisonShadow(ul,ul,uc), 1276 bytes (PC_POISON_SHADOW)
     word #0  0xfe010113 addi sp,sp,-0x20  -> the walk's stack window SF_WIN 32
     word #6  0x00004537 lui a0,4          -> FS_B 16384 = fs_frame_bytes 8; the flag pointer at frame + 0x3ff8
     word #12 0x0f500613 addi a2,zero,0xf5 -> the poison value PoisonShadow is called with
     image top (last PT_LOAD end 0x5f8378, page-rounded) = 0x5f9000                    (IMG_END)
   Read by the two summarised callees only, so used by no proof here (for the record, each MEASURED the same way):
     GOT 0x9ba40 -> __asan_shadow_memory_dynamic_address 0xa3af8 (.bss); GOT 0x9ba48 / 0x9ba50 / 0x9ba58 ->
     kMidMemBeg 0xa47e8 / kMidMemEnd 0xa47f0 / kHighMemEnd 0xa47e0 (.bss); GOT 0x9ba38 -> asan_flags_dont_use_directly
     0xa12f8; can_poison_memory 0xa335c (.bss); GOT 0x9ba60 -> __interception::real_memset 0x9d8b0 (link-time value =
     musl memset 0x95174); GOT 0x9ba30 -> common_flags_dont_use 0x135628; GOT 0x9ba20 -> PageSizeCached 0x1335a0.
   CID8, PC_MEM_TO_SHADOW and PC_POISON_SHADOW are a Theorem Labs lane's (lib/AU/Rt/StackMalloc8Tbl.v); this file defines
   no second numeral for them. The two callee summaries are a Theorem Labs lane's lib/Reusable/AsStackLeaf.v (re-exported there).
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
YG00 YG0a YG01 YG0f YG0n YG0d YG0t.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YCe5.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import StackFreeDef AsStackLeaf.
From OSSVerify.libreac.fuzz_scene.images Require Import AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YB1v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Rt Require Import StackMalloc8Tbl.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import StackFree8.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition PC_STACK_FREE_8 : Z := 0x3f5b4.
Definition MTS_RET : Z := 0x3f5e4.
Definition IMG_END : Z := 0x5f9000.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition tbl_sf : ctable := Eval vm_compute in build_table tfibsegs PC_STACK_FREE_8 20 TEmpty.
Lemma tbl_sf_eq : tbl_sf = build_table tfibsegs PC_STACK_FREE_8 20 TEmpty. Proof. vm_cast_no_check (eq_refl tbl_sf). Qed.
Lemma tbl_sf_ok : table_ok tfibsegs tbl_sf. Proof. rewrite tbl_sf_eq. apply build_table_ok0. unfold PC_STACK_FREE_8. lia. Qed.
(* The table holds exactly the 20 measured words of __asan_stack_free_8, and nothing at PC_MEM_TO_SHADOW or below PC_STACK_FREE_8. *)
Example tbl_sf_words :
map (clookup tbl_sf) [0x3f5b4; 0x3f5b8; 0x3f5bc; 0x3f5c0; 0x3f5c4; 0x3f5c8; 0x3f5cc; 0x3f5d0; 0x3f5d4; 0x3f5d8;
0x3f5dc; 0x3f5e0; 0x3f5e4; 0x3f5e8; 0x3f5ec; 0x3f5f0; 0x3f5f4; 0x3f5f8; 0x3f5fc; 0x3f600; PC_MEM_TO_SHADOW; 0x3f5b0] =
map Some [0xfe010113; 0x00113c23; 0x00813823; 0x00913423; 0x00058413; 0x00050493; 0x00004537; 0x00a48533; 0xff853503;
0x00050023; 0x00048513; 0x024000ef; 0x0f500613; 0x00048513; 0x00040593; 0x01813083; 0x01013403; 0x00813483;
0x02010113; 0x5e41606f] ++ [None; None].
Proof. vm_compute. reflexivity. Qed.
Lemma Hwx_sfb : wx_segs_nowrap tfibsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma img_bound : forall a, YG0d.in_img tfibsegs a -> a < IMG_END.
Proof.
intros a (sg & Hin & Hr). unfold tfibsegs, AsanUbsan.M.loaded_segments in Hin. cbn in Hin.
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
Theorem sce_stack_free_8_B : astack_free_realizes tfibsegs B PC_STACK_FREE_8 CID8.
Proof.
exact (astack_free_8_at tfibsegs PC_STACK_FREE_8 PC_MEM_TO_SHADOW MTS_RET PC_POISON_SHADOW IMG_END tbl_sf e1 e2
Hwx_sfb tbl_sf_ok img_bound ltac:(unfold IMG_END; lia) fseg_none rom_none mts_ret_ok mts_ret_small
r_sf1 r_sf2 e1_pc e1_resv e1_a0 e1_ra e1_atoms e1_mem
e2_pc e2_resv e2_r10 e2_r11 e2_r12 e2_keepb e2_mem B LAWS MTS_SUM PS_SUM).
Qed.
End inst.
End e.

Print Assumptions sce_stack_free_8_B.
