(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QTp6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Export QTp6.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Definition RIMG_LO : Z := 0x10000.
Definition RIMG_HI : Z := 0x645000.
Definition RDATA_LO : Z := 0xe2000.

Definition RCTX : Z := 0x6431e8.
Definition RMLOCK : Z := 0x6431e0.
Definition RLIBC : Z := 0x6430f0.
Definition RNEED_LOCKS : Z := 0x6430f3.
Definition RPAGE_SIZE : Z := 0x643120.
Definition RAUXV_CELL : Z := 0x6430f8.
Definition RSIZE_CLASSES : Z := 0x26f48.
Definition RDEBRUIJN : Z := 0x26f28.
Definition RSMALL_CNT : Z := 0x26fa8.
Definition RMED_CNT : Z := 0x26fc3.
Definition RGOT_SSP : Z := 0xe6b80.
Definition RSSP_GUARD : Z := 0x642ea0.
Definition RVMLOCK : Z := 0x6446f8.
Definition RATP : Z := 0x622e60.
Definition RERRNO : Z := 0x622dbc.

Definition rerrno_loc_entry : Z := 0xcc3a4.
Definition rsysret_entry : Z := 0xcca08.
Definition rcalloc_entry : Z := 0xcdb68.
Definition rfree_sym : Z := 0xcdca4.
Definition rmalloc_sym : Z := 0xcdca0.
Definition rfree_entry : Z := 0xcdca4.
Definition rget_meta_entry : Z := 0xcde70.
Definition rnontrivial_free_entry : Z := 0xcdf80.
Definition ralloc_meta_entry : Z := 0xce358.
Definition rmalloc_entry : Z := 0xce630.
Definition ralloc_slot_entry : Z := 0xce9a0.
Definition renframe_entry : Z := 0xcf244.
Definition ris_allzero_entry : Z := 0xcf394.
Definition rrealloc_entry : Z := 0x1bf08.
Definition rvm_wait_entry : Z := 0xde7d0.
Definition rmmap_entry : Z := 0xd1a70.
Definition rmprotect_entry : Z := 0xd1b5c.
Definition rmremap_entry : Z := 0xd1ba4.
Definition rmunmap_entry : Z := 0xd1c78.
Definition rlock_entry : Z := 0xdc43c.
Definition runlock_entry : Z := 0xdc6c4.

Definition ref_reserved : list (Z * Z) := [(0x10000, 0x2d000); (0x3d000, 0xa5000); (0xe2000, 0x5000); (0xe7000, 0x55e000)].

Lemma ref_find_segment_none : forall z n, 1 <= n -> (z + n <= 0x10000 \/ 0x645000 <= z) ->
find_segment rsegs z n = None.
Proof.
intros z n Hn Hz. unfold rsegs, Asan.M.loaded_segments, Asan.Asan_loaded_segments. cbn [find_segment].
replace (Z.of_N (seg_base Asan.Asan_segment_000)) with 0x10000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Asan.Asan_segment_000)) with 0x2d000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_base Asan.Asan_segment_001)) with 0x3d000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Asan.Asan_segment_001)) with 0xa5000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_base Asan.Asan_segment_002)) with 0xe2000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Asan.Asan_segment_002)) with 0x5000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_base Asan.Asan_segment_003)) with 0xe7000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Asan.Asan_segment_003)) with 0x55e000%Z by (vm_compute; reflexivity).
destruct (Z.leb_spec0 0x10000 z); destruct (Z.leb_spec0 (z + n) (0x10000 + 0x2d000)); cbn [andb]; try lia.
all: destruct (Z.leb_spec0 0x3d000 z); destruct (Z.leb_spec0 (z + n) (0x3d000 + 0xa5000)); cbn [andb]; try lia.
all: destruct (Z.leb_spec0 0xe2000 z); destruct (Z.leb_spec0 (z + n) (0xe2000 + 0x5000)); cbn [andb]; try lia.
all: destruct (Z.leb_spec0 0xe7000 z); destruct (Z.leb_spec0 (z + n) (0xe7000 + 0x55e000)); cbn [andb]; try lia.
all: reflexivity.
Qed.

Lemma ref_ro_addr_false : forall x : word,
(bv_unsigned x + 1 <= 0x10000 \/ 0x645000 <= bv_unsigned x)%Z -> ro_addr rsegs x = false.
Proof. intros x Hx. unfold ro_addr. rewrite ref_find_segment_none by lia. reflexivity. Qed.

Lemma ref_memory_read_none : forall (x : word) n,
(1 <= Z.of_N n)%Z -> (bv_unsigned x + Z.of_N n <= 0x10000 \/ 0x645000 <= bv_unsigned x)%Z -> memory_read rsegs x n = None.
Proof. intros x n Hn Hx. unfold memory_read. rewrite ref_find_segment_none by lia. reflexivity. Qed.

Lemma ref_wview_overlay : forall m (x : word),
(bv_unsigned x + 1 <= 0x10000 \/ 0x645000 <= bv_unsigned x)%Z -> wview rsegs m x = m x.
Proof.
intros m x Hx. unfold wview. destruct (m x); [reflexivity|]. rewrite ref_find_segment_none by lia. reflexivity.
Qed.

Lemma ref_seg_rom_none : forall (x : word),
(bv_unsigned x + 1 <= 0x10000 \/ 0x645000 <= bv_unsigned x)%Z -> seg_rom rsegs x = None.
Proof. intros x Hx. unfold seg_rom. rewrite ref_memory_read_none by (cbn; lia). reflexivity. Qed.

Lemma ref_mrd_overlay : forall m (x : word),
(bv_unsigned x + 1 <= 0x10000 \/ 0x645000 <= bv_unsigned x)%Z -> mrd rsegs m x = m x.
Proof. intros m x Hx. unfold mrd. destruct (m x); [reflexivity|]. apply ref_seg_rom_none. exact Hx. Qed.
End Mq0.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVbl.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBpX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBpX.
Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma gw_code : CodeAt.code_at usegs 0xd1d70 QVbl.Mq1.getf2_code.  Proof. StepGen.code_at_vm. Qed.
Lemma gw_base4 : (0xd1d70 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma gw_baser : (0 <= 0xd1d70 /\ 0xd1d70 + 188 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition getf2_entry := 0xd1d70%Z.
Lemma gw_eq_getf2_entry : @getf2_entry = ltac:(GwInst.gw_term (@QVbl.Mq1.getf2_entry 0xd1d70) (@getf2_entry)). Proof. unfold getf2_entry, QVbl.Mq1.getf2_entry; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_getf2_entry : gw_eqs.

Definition ge_isnan_w (lo hi : Z) : bool :=
(let absHi := Z.land hi ABS_HI in
if absHi =? INF_HI then negb (lo =? 0) else INF_HI <? absHi)%Z.
Lemma gw_eq_ge_isnan_w : @ge_isnan_w = ltac:(GwInst.gw_term (@QVbl.Mq1.ge_isnan_w) (@ge_isnan_w)). Proof. unfold ge_isnan_w, QVbl.Mq1.ge_isnan_w; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_ge_isnan_w : gw_eqs.

Definition ge_isless (a_lo a_hi b_lo b_hi : Z) : bool :=
(if negb (is_neg64 (Z.land b_hi a_hi)) then
(if a_hi =? b_hi then a_lo <? b_lo else lt_s64 a_hi b_hi)
else
(if a_hi =? b_hi then b_lo <? a_lo else lt_s64 b_hi a_hi))%Z.
Lemma gw_eq_ge_isless : @ge_isless = ltac:(GwInst.gw_term (@QVbl.Mq1.ge_isless) (@ge_isless)). Proof. unfold ge_isless, QVbl.Mq1.ge_isless; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_ge_isless : gw_eqs.

Definition ge_tail (il : bool) (a_lo a_hi b_lo b_hi : Z) : Z :=
if il then (-1)%Z else nez64 (Z.lor (Z.lxor a_lo b_lo) (Z.lxor a_hi b_hi)).
Lemma gw_eq_ge_tail : @ge_tail = ltac:(GwInst.gw_term (@QVbl.Mq1.ge_tail) (@ge_tail)). Proof. unfold ge_tail, QVbl.Mq1.ge_tail; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_ge_tail : gw_eqs.

Definition ge_core (a_lo a_hi b_lo b_hi : Z) : Z :=
(if Z.lor (Z.lor b_lo a_lo) (Z.lor (Z.land b_hi ABS_HI) (Z.land a_hi ABS_HI)) =? 0 then 0
else ge_tail (ge_isless a_lo a_hi b_lo b_hi) a_lo a_hi b_lo b_hi)%Z.
Lemma gw_eq_ge_core : @ge_core = ltac:(GwInst.gw_term (@QVbl.Mq1.ge_core) (@ge_core)). Proof. unfold ge_core, QVbl.Mq1.ge_core; rewrite ?gw_eq_ge_isless, ?gw_eq_ge_tail; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_ge_core : gw_eqs.

Lemma lo64_words : forall lo hi, (0 <= lo < 2^64)%Z -> lo64 (lo + 2^64 * hi) = lo.
Proof. first [GwInst.gw_exact (@QVbl.Mq1.lo64_words usegs 0xd1d70 gw_code gw_base4 gw_baser) | autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq1.lo64_words usegs 0xd1d70 gw_code gw_base4 gw_baser)]. Qed.

Lemma hi64_words : forall lo hi, (0 <= lo < 2^64)%Z -> (0 <= hi < 2^64)%Z -> hi64 (lo + 2^64 * hi) = hi.
Proof. first [GwInst.gw_exact (@QVbl.Mq1.hi64_words usegs 0xd1d70 gw_code gw_base4 gw_baser) | autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq1.hi64_words usegs 0xd1d70 gw_code gw_base4 gw_baser)]. Qed.

Lemma f128_ge_split : ltac2:(Q6nq.tyx '(@QVbl.Mq1.f128_ge_split usegs 0xd1d70 gw_code gw_base4 gw_baser) [[@gw_eq_ge_isnan_w]; [@gw_eq_ge_core]; [@gw_eq_getf2_entry__3; @gw_eq_getf2_entry__2; @gw_eq_getf2_entry]; [@gw_eq_ge_isless__3; @gw_eq_ge_isless__2; @gw_eq_ge_isless]; [@gw_eq_ge_tail__3; @gw_eq_ge_tail__2; @gw_eq_ge_tail]] '(@nil Z) 'Q6nq.gwt_nil).
Proof. rewrite ?gw_eq_ge_isnan_w, ?gw_eq_ge_core; first [GwInst.gw_exact (@QVbl.Mq1.f128_ge_split usegs 0xd1d70 gw_code gw_base4 gw_baser) | autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq1.f128_ge_split usegs 0xd1d70 gw_code gw_base4 gw_baser)]. Qed.

Lemma b2z_snez : forall x, (0 <= x)%Z -> Z.b2z (0 <? x)%Z = nez64 x.
Proof. first [GwInst.gw_exact (@QVbl.Mq1.b2z_snez usegs 0xd1d70 gw_code gw_base4 gw_baser) | autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq1.b2z_snez usegs 0xd1d70 gw_code gw_base4 gw_baser)]. Qed.

Definition getf2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(r : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [] m m' /\ wmono usegs m m' /\ mem_inv usegs m'.
Lemma gw_eq_getf2_post : @getf2_post = ltac:(GwInst.gw_term (@QVbl.Mq1.getf2_post usegs) (@getf2_post)). Proof. unfold getf2_post, QVbl.Mq1.getf2_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_getf2_post : gw_eqs.

Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Hypothesis MI : mem_inv usegs m.
Let MU : munch [] m m := munch_refl [] m.
Let WM : wmono usegs m m := wmono_refl usegs m.

Lemma getf2_L54 : ltac2:(Q6nq.tyx '(@QVbl.Mq1.getf2_L54 usegs 0xd1d70 gw_code gw_base4 gw_baser) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_getf2_entry__3; @gw_eq_getf2_entry__2; @gw_eq_getf2_entry]; [@gw_eq_ge_isnan_w__3; @gw_eq_ge_isnan_w__2; @gw_eq_ge_isnan_w]; [@gw_eq_ge_isless__3; @gw_eq_ge_isless__2; @gw_eq_ge_isless]; [@gw_eq_ge_tail__3; @gw_eq_ge_tail__2; @gw_eq_ge_tail]; [@gw_eq_ge_core__3; @gw_eq_ge_core__2; @gw_eq_ge_core]; [@gw_eq_getf2_post__3; @gw_eq_getf2_post__2; @gw_eq_getf2_post]] '([859672]%Z : list Z) 'Q6nq.gwt_nil).
Proof using MI. ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwInst.gw_exact (@QVbl.Mq1.getf2_L54 usegs 0xd1d70 gw_code gw_base4 gw_baser) | autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq1.getf2_L54 usegs 0xd1d70 gw_code gw_base4 gw_baser)]. Qed.

Lemma getf2_Lcc : ltac2:(Q6nq.tyx '(@QVbl.Mq1.getf2_Lcc usegs 0xd1d70 gw_code gw_base4 gw_baser) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_getf2_entry__3; @gw_eq_getf2_entry__2; @gw_eq_getf2_entry]; [@gw_eq_ge_isnan_w__3; @gw_eq_ge_isnan_w__2; @gw_eq_ge_isnan_w]; [@gw_eq_ge_isless__3; @gw_eq_ge_isless__2; @gw_eq_ge_isless]; [@gw_eq_ge_tail__3; @gw_eq_ge_tail__2; @gw_eq_ge_tail]; [@gw_eq_ge_core__3; @gw_eq_ge_core__2; @gw_eq_ge_core]; [@gw_eq_getf2_post__3; @gw_eq_getf2_post__2; @gw_eq_getf2_post]] '([859536]%Z : list Z) 'Q6nq.gwt_nil).
Proof using MI. ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwInst.gw_exact (@QVbl.Mq1.getf2_Lcc usegs 0xd1d70 gw_code gw_base4 gw_baser) | autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq1.getf2_Lcc usegs 0xd1d70 gw_code gw_base4 gw_baser)]. Qed.

Lemma getf2_L00 : ltac2:(Q6nq.tyx '(@QVbl.Mq1.getf2_L00 usegs 0xd1d70 gw_code gw_base4 gw_baser) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_ge_core]; [@gw_eq_getf2_entry__3; @gw_eq_getf2_entry__2; @gw_eq_getf2_entry]; [@gw_eq_ge_isnan_w__3; @gw_eq_ge_isnan_w__2; @gw_eq_ge_isnan_w]; [@gw_eq_ge_isless__3; @gw_eq_ge_isless__2; @gw_eq_ge_isless]; [@gw_eq_ge_tail__3; @gw_eq_ge_tail__2; @gw_eq_ge_tail]; [@gw_eq_getf2_post__3; @gw_eq_getf2_post__2; @gw_eq_getf2_post]] '([859588]%Z : list Z) 'Q6nq.gwt_nil).
Proof using MI. rewrite ?gw_eq_ge_core; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwInst.gw_exact (@QVbl.Mq1.getf2_L00 usegs 0xd1d70 gw_code gw_base4 gw_baser) | autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq1.getf2_L00 usegs 0xd1d70 gw_code gw_base4 gw_baser)]. Qed.

Lemma getf2_Ldc : ltac2:(Q6nq.tyx '(@QVbl.Mq1.getf2_Ldc usegs 0xd1d70 gw_code gw_base4 gw_baser) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_ge_isnan_w]; [@gw_eq_ge_core]; [@gw_eq_getf2_entry__3; @gw_eq_getf2_entry__2; @gw_eq_getf2_entry]; [@gw_eq_ge_isless__3; @gw_eq_ge_isless__2; @gw_eq_ge_isless]; [@gw_eq_ge_tail__3; @gw_eq_ge_tail__2; @gw_eq_ge_tail]; [@gw_eq_getf2_post__3; @gw_eq_getf2_post__2; @gw_eq_getf2_post]] '([859552]%Z : list Z) 'Q6nq.gwt_nil).
Proof using MI. rewrite ?gw_eq_ge_isnan_w, ?gw_eq_ge_core; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwInst.gw_exact (@QVbl.Mq1.getf2_Ldc usegs 0xd1d70 gw_code gw_base4 gw_baser) | autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq1.getf2_Ldc usegs 0xd1d70 gw_code gw_base4 gw_baser)]. Qed.
End Proofs.

Lemma getf2_spec : ltac2:(Q6nq.tyx '(@QVbl.Mq1.getf2_spec usegs 0xd1d70 gw_code gw_base4 gw_baser) [[@gw_eq_getf2_post]; [@gw_eq_getf2_entry__3; @gw_eq_getf2_entry__2; @gw_eq_getf2_entry]; [@gw_eq_ge_isnan_w__3; @gw_eq_ge_isnan_w__2; @gw_eq_ge_isnan_w]; [@gw_eq_ge_isless__3; @gw_eq_ge_isless__2; @gw_eq_ge_isless]; [@gw_eq_ge_tail__3; @gw_eq_ge_tail__2; @gw_eq_ge_tail]; [@gw_eq_ge_core__3; @gw_eq_ge_core__2; @gw_eq_ge_core]] '([859504]%Z : list Z) '(Q6nq.gwt_unf (@getf2_entry) Q6nq.gwt_nil)).
Proof. rewrite ?gw_eq_getf2_post; first [GwInst.gw_exact (@QVbl.Mq1.getf2_spec usegs 0xd1d70 gw_code gw_base4 gw_baser) | autorewrite with gw_eqs; GwInst.gw_exact (@QVbl.Mq1.getf2_spec usegs 0xd1d70 gw_code gw_base4 gw_baser)]. Qed.
