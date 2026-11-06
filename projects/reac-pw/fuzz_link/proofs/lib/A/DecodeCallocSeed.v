(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AFj0.v (SEED_ok: the entry state
   proved from the call precondition), A/AFis.v (E0, at_ST) and A/AFip.v (segA: the run of the seed to the wrapper's
   first call) to libreac/fuzz_decode's calloc wrapper chain in image A (fuzz_decode.asan); module paths changed. *)
(* The seed of the calloc walk of image A, and its run to the wrapper's first call.

   [SEED_ok] proves the entry state DecodeCallocSkel.SS0 at the trampoline 0x540d0 from the unit's call precondition
   alone (YG0d.v:226-234 acall_pre): the sp range and alignment and the stack window [sp - ASTACK, sp) present in
   memory are conjuncts of acall_pre, and the layout facts (kHighMemBeg <= ly_stk_lo, ly_stk_hi <= kHighMemEnd) are
   YG0f.v:322-324 lo_top of the layout_ok that the allocator relation carries (YG0n.v:490 AR, YG0n.v:209 am_layout).
   No image cell is read before the first call, so the seed takes no hypothesis about memory beyond acall_pre.

   [walk_C1] runs the seed over DecodeCallocTbl.tbl_calloc_A (words read out of the image, tbl_calloc_A_ok) from
   0x540d0 to 0x54504, the wrapper's call of TryAsanInitFromRtl (0x54504 `jal 0x5b214`), and lands in [at_C1]: the
   symbolic state DecodeCallocSkel.SS_C1 (sp = entry sp - 2144, s0 = entry sp, s1 = sz, s2 = nm, s3 = ra, the eight
   saved registers at entry sp - 64 .. entry sp - 8), memory outside the stack window equal to the entry memory, and
   the stack window still present.  The instructions run are listed in DecodeCallocSkel.v. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v DecodeCallocTbl DecodeCalloc DecodeCallocSkel.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YImgTop YImgTopSegs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* The image's writable-and-executable segments do not wrap (the run tactics' side condition). *)
Lemma decode_wx : wx_segs_nowrap tfibsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

(* No loaded segment of image A reaches IMG_TOP (YImgTop.v:44 segs_in_asan, decided against the image module). *)
Lemma find_segment_above : forall (l : list Segment) a,
segs_in l = true -> IMG_TOP <= a -> find_segment l a 1 = None.
Proof.
induction l as [|sg rest IH]; intros a Hin Ha; [reflexivity|].
unfold segs_in in Hin. cbn [forallb] in Hin. apply andb_prop in Hin as [Hs Hr].
apply andb_prop in Hs as [_ Hhi]. apply Z.leb_le in Hhi. unfold seg_hi in Hhi.
cbn. destruct (Z.leb (Z.of_N (seg_base sg)) a && Z.leb (a + 1) (Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))%bool eqn:E.
- apply andb_prop in E as [_ E2]. apply Z.leb_le in E2. lia.
- apply IH; [exact Hr | exact Ha].
Qed.

(* Above the image, a byte the restricted memory can write is a byte the memory holds and the world does not hide. *)
Lemma apresent_of_writable_high : forall (H : word -> bool) (m : word -> option byte) a,
IMG_TOP <= a < 2 ^ 64 -> writable_at tfibsegs (mrestrict H m) a -> apresent H m a.
Proof.
intros H m a Ha Hw. unfold writable_at, wview, mrestrict in Hw. unfold apresent.
assert (Ha0 : 0 <= a) by (pose proof IMG_TOP_val; lia).
rewrite unsigned_lit_small in Hw by lia.
rewrite (find_segment_above tfibsegs a segs_in_asan (proj1 Ha)) in Hw.
destruct (H (Z_to_bv 64 a)); [exfalso; apply Hw; reflexivity|].
split; [reflexivity|]. destruct (m (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | exfalso; apply Hw; reflexivity].
Qed.

Section e.
Variable B : asyms.
Variables (W : world tfibsegs) (ly : alayout) (S : astate).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (ch : list (Z * Z * Z)).
(* The unit's call precondition at the trampoline (YG0d.v:226-234). *)
Hypothesis PRE : acall_pre tfibsegs B ly S W regs0 mem0 md0 ch.
Let sp0 : Z := spZ regs0.

(* The environment: atom i < 32 is x_i at the trampoline (YI04.v:78 Ereg); no further atoms. *)
Definition E0 : env := Ereg regs0 [].
Lemma E0_reg (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E0 k = YK11.getr regs0 r.
Proof. intros Hk. exact (ew_Ereg_nat regs0 [] k r Hk). Qed.

(* The sp facts the seed needs, from acall_pre and the layout. *)
Lemma sp0_facts :
kHighMemBeg + ASTACK <= sp0 <= kHighMemEnd /\ sp0 mod 16 = 0 /\
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem0 a).
Proof.
pose proof PRE as (HAR & _ & _ & Hal & Hlo & _ & Hhi & Hpres & _).
destruct HAR as (HARm & _). pose proof (am_layout _ _ _ _ HARm) as LY.
pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7).
unfold sp0. unfold spZ in *. split; [lia|]. split; [exact Hal | exact Hpres].
Qed.

(* Item 2: the entry state at the trampoline. *)
Lemma SEED_ok : st_ok tfibsegs E0 SS0
(restrict (w_H W) (YK11.mkst regs0 (w64 0x540d0) mem0 (YK11.seg_rom tfibsegs))).
Proof.
pose proof sp0_facts as ((Slo & Shi) & Sal & Spres).
assert (E2 : bv_unsigned (ew E0 2) = sp0) by (rewrite (E0_reg 2 2%bv eq_refl); reflexivity).
rewrite restrict_mkst_fx. unfold SS0, w64, E0. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold REG0.
apply (region_ok_stack tfibsegs (Ereg regs0 []) _ 2 sp0 (- ASTACK) E2).
+ unfold ASTACK, kHighMemBeg in *. lia.
+ pose proof (u64_range (YK11.getr regs0 2)). unfold sp0, spZ in *. lia.
+ intros a Ha. destruct (Spres a ltac:(lia)) as [Hh [b Hb]].
unfold writable_at, wview, mrestrict. rewrite Hh, Hb. discriminate.
- cbn. split; exact I.
- split; [|split; exact I]. unfold FG0. cbn [f_atoms atoms_ok]. split; [|exact I].
unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E0. rewrite E2. split; [lia|]. split; [exact Sal | lia].
Qed.

(* Item 3: the run from the trampoline to the wrapper's first call.  The reached configuration: pc 0x54504, the
   symbolic state SS_C1 over the entry environment, memory outside the stack window [sp - ASTACK, sp) unchanged, and
   the stack window present, as cgif's at_ST (AFis.v:594-601) carries its frame and presence conjuncts. *)
Definition at_C1 (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists ms mat,
c' = mkCfg ms (with_vm_backing (m_vm_lazy md0) mat md0) /\
st_ok tfibsegs E0 SS_C1 (restrict (w_H W) ms) /\
(forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0) -> ms_mem ms x = mem0 x) /\
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a).

Lemma walk_C1 : SRr tfibsegs W (cfg_at tfibsegs 0x540d0 regs0 mem0 md0) at_C1.
Proof.
pose proof decode_wx as Hwx. pose proof SEED_ok as HS.
pose proof sp0_facts as ((Slo & Shi) & _ & _).
assert (E2 : bv_unsigned (ew E0 2) = sp0) by (rewrite (E0_reg 2 2%bv eq_refl); reflexivity).
unfold cfg_at.
srr_run_to_sh tbl_calloc_A_ok HS DEC_A_calloc_call1.
lazymatch type of HS with st_ok _ _ ?ss _ => replace ss with SS_C1 in HS by (vm_compute; reflexivity) end.
apply SRr_ret. split; [reflexivity|]. exists ms, mat. split; [reflexivity|]. split; [exact HS|]. split.
- intros x Hx. apply HF. intros (r & Hin & Hr). unfold SS0, REG0 in Hin. cbn [ss_mem In] in Hin.
destruct Hin as [<-|[]]. cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Hr. rewrite E2 in Hr. lia.
- intros a Ha. apply (st_ok_mem_ok tfibsegs) in HS. destruct HS as (_ & Hrs & _).
unfold SS_C1, REG_C1 in Hrs. cbn [ss_mem] in Hrs. apply Forall_inv in Hrs.
destruct Hrs as (_ & _ & Hw & _). cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Hw.
rewrite E2 in Hw. apply apresent_of_writable_high.
+ rewrite IMG_TOP_val. unfold ASTACK, kHighMemBeg, kHighMemEnd in *. lia.
+ replace a with (sp0 + (a - sp0)) by lia. apply Hw. lia.
Qed.

(* The registers of the reached state, read from SS_C1: the five the run wrote, and the argument, return-address,
   gp and tp registers it left as they were at the trampoline. *)
Lemma C1_regs : forall ms, st_ok tfibsegs E0 SS_C1 (restrict (w_H W) ms) ->
ms_pc_val ms = w64 DEC_A_calloc_call1 /\
YK11.getr (ms_regs ms) 2 = w64 (sp0 - ICPT_FRAME) /\ YK11.getr (ms_regs ms) 8 = YK11.getr regs0 2 /\
YK11.getr (ms_regs ms) 9 = YK11.getr regs0 11 /\ YK11.getr (ms_regs ms) 18 = YK11.getr regs0 10 /\
YK11.getr (ms_regs ms) 19 = YK11.getr regs0 1 /\
YK11.getr (ms_regs ms) 1 = YK11.getr regs0 1 /\ YK11.getr (ms_regs ms) 3 = YK11.getr regs0 3 /\
YK11.getr (ms_regs ms) 4 = YK11.getr regs0 4 /\
YK11.getr (ms_regs ms) 10 = YK11.getr regs0 10 /\ YK11.getr (ms_regs ms) 11 = YK11.getr regs0 11.
Proof.
intros ms HS.
assert (R : forall r : bv 5, YK11.getr (ms_regs ms) r = sv_denot E0 (sr_get (ss_regs SS_C1) r))
by (intros r; exact (st_ok_restrict_reg tfibsegs (w_H W) E0 SS_C1 ms r HS)).
assert (K : forall (k : nat) (r : bv 5), Z.of_nat k = bv_unsigned r ->
sv_denot E0 (SOff k 0) = YK11.getr regs0 r).
{ intros k r Hk. cbn [sv_denot]. rewrite (E0_reg k r Hk), Z.add_0_r. apply Z_to_bv_bv_unsigned. }
split; [exact (st_ok_restrict_pc tfibsegs (w_H W) E0 SS_C1 ms HS)|].
split.
{ rewrite R. change (sr_get (ss_regs SS_C1) 2%bv) with (SOff 2 (- ICPT_FRAME)). cbn [sv_denot].
rewrite (E0_reg 2 2%bv eq_refl). unfold w64, sp0, spZ, ICPT_FRAME. f_equal; lia. }
split; [rewrite R; change (sr_get (ss_regs SS_C1) 8%bv) with (SOff 2 0); exact (K 2%nat 2%bv eq_refl)|].
split; [rewrite R; change (sr_get (ss_regs SS_C1) 9%bv) with (SOff 11 0); exact (K 11%nat 11%bv eq_refl)|].
split; [rewrite R; change (sr_get (ss_regs SS_C1) 18%bv) with (SOff 10 0); exact (K 10%nat 10%bv eq_refl)|].
split; [rewrite R; change (sr_get (ss_regs SS_C1) 19%bv) with (SOff 1 0); exact (K 1%nat 1%bv eq_refl)|].
split; [rewrite R; change (sr_get (ss_regs SS_C1) 1%bv) with (SOff 1 0); exact (K 1%nat 1%bv eq_refl)|].
split; [rewrite R; change (sr_get (ss_regs SS_C1) 3%bv) with (SOff 3 0); exact (K 3%nat 3%bv eq_refl)|].
split; [rewrite R; change (sr_get (ss_regs SS_C1) 4%bv) with (SOff 4 0); exact (K 4%nat 4%bv eq_refl)|].
split; [rewrite R; change (sr_get (ss_regs SS_C1) 10%bv) with (SOff 10 0); exact (K 10%nat 10%bv eq_refl)|].
rewrite R; change (sr_get (ss_regs SS_C1) 11%bv) with (SOff 11 0); exact (K 11%nat 11%bv eq_refl).
Qed.

(* The word at the reached pc is the call: 0x54504 holds 0x511060ef = `jal ra, 0x5b214` in the image. *)
Lemma C1_call_word : clookup tbl_calloc_A DEC_A_calloc_call1 = Some 0x511060ef.
Proof. vm_compute. reflexivity. Qed.
(* The word at the trampoline: 0x540d0 holds 0x3fc0006f = `j 0x544cc` in the image. *)
Lemma tramp_word : clookup tbl_calloc_A DEC_A_wrap_calloc = Some 0x3fc0006f.
Proof. vm_compute. reflexivity. Qed.
End e.
End d.
