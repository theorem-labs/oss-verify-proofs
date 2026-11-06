(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBase.
From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Image ZBridge SysStep ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Malloc_fp.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocKit_A2__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocHINV.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec.
From Stdlib Require Permutation.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog HeapFull.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_enframe RMallocKit_A.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_Bpres__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_get_meta__S3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module RF_malloc_entry.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import TlsBase.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_enframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Malloc_fp. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocKit_A2__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.Malloc_fp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_entry.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Local Unset Keyed Unification.

(* [comment removed for export] *)
Definition rDB32 : Z := 125613361.   (* [comment removed for export] *)
Definition rdbi (k : Z) : Z := ((2 ^ k * rDB32) mod 2^32) / 2^27.

Lemma rdbi_range k : 0 <= rdbi k < 32.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts. unfold rdbi. pose proof (Z.mod_pos_bound (2^k * rDB32) (2^32) ltac:(lia)). Z.div_mod_to_equations. nia. Qed.

Definition rdebruijn_bytes : list byte :=
  Eval vm_compute in (match image_bytes ssegs RDEBRUIJN 32 with Some bs => bs | None => [] end).

Lemma rdebruijn_ro : forall m, mem_inv ssegs m -> ro_cells ssegs m RDEBRUIJN [CB 32 rdebruijn_bytes].
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts. intros m MI. apply (ro_cells_image ssegs m); [exact MI | vm_compute; reflexivity | unfold RDEBRUIJN; lia | unfold RDEBRUIJN; cbn; lia]. Qed.

Lemma rdebruijn_read : forall m k, mem_inv ssegs m -> 0 <= k < 32 ->
  ov_read_bytes ssegs m (wa (RDEBRUIJN + rdbi k)) 1 = Some [b8 k].
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros m k MI Hk.
  destruct (rdebruijn_ro m MI) as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  pose proof (rdbi_range k) as R.
  rewrite (bytes_at_read ssegs m RDEBRUIJN rdebruijn_bytes (rdbi k) 1 B) by (cbn; lia).
  assert (Hn : exists n, k = Z.of_nat n /\ (n < 32)%nat) by (exists (Z.to_nat k); split; [lia|lia]).
  destruct Hn as (n & -> & Hn).
  Ltac solve_db := vm_compute; reflexivity.
  do 32 (destruct n as [|n]; [solve_db |]). lia.
Qed.

(* [comment removed for export] *)
Lemma mul_srliw27 k : 0 <= k < 32 ->
  bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (Z_to_bv 64 (2 ^ k * rDB32)))) 27) = rdbi k.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros Hk. unfold rdbi.
  assert (P : 0 < 2 ^ k <= 2 ^ 31) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_le_mono_r; lia]).
  rewrite unsigned_lit by (unfold rDB32; nia).
  change (bv_wrap 32 (2 ^ k * rDB32)) with ((2 ^ k * rDB32) mod 2^32).
  rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.mod_pos_bound (2 ^ k * rDB32) (2^32) ltac:(lia)).
  apply swrap32_small. Z.div_mod_to_equations. nia.
Qed.

Definition rclz_v4 (x : Z) : Z :=
  let v1 := Z.lor (Z.shiftr x 2) x in
  let v2 := Z.lor v1 (Z.shiftr x 1) in
  let w2 := Z.lor (Z.shiftr v2 2) (Z.shiftr x 1) in
  let w3 := Z.lor (Z.shiftr w2 4) w2 in
  Z.lor (Z.shiftr w3 8) w3.
Definition rclz_pow (x : Z) : Z := Z.land (rclz_v4 x + 1) (Z.lxor (rclz_v4 x) 18446744073709551615).
Definition rclz_fn (x : Z) : bool := (rclz_pow x =? 2 ^ Z.log2 x) && (rclz_v4 x <? 2 ^ 13).
(* [comment removed for export] *)
Fixpoint rme_zgo (x : Z) (k : nat) : list Z := match k with O => [] | S k' => x :: rme_zgo (x + 1) k' end.
#[using="Type"] Lemma rme_zgo_seq k s : map Z.of_nat (seq s k) = rme_zgo (Z.of_nat s) k.
Proof. revert s. induction k as [|k IH]; intros s; [reflexivity|]. cbn [seq map rme_zgo]. f_equal. rewrite IH. f_equal. lia. Qed.
#[using="Type"] Lemma rme_zseq_go a n : 0 <= a -> zseq a n = rme_zgo a (Z.to_nat n).
Proof. intros Ha. unfold zseq. rewrite rme_zgo_seq. f_equal. lia. Qed.
Lemma rclz_check_true : forallb rclz_fn (zseq 11 8181) = true.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  rewrite (rme_zseq_go 11 8181) by lia. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Lemma rclz_pow_eq x : 11 <= x < 8192 -> rclz_pow x = 2 ^ Z.log2 x /\ 0 <= rclz_v4 x < 2 ^ 13.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros Hx. pose proof (forallb_zseq rclz_fn 11 8181 x rclz_check_true ltac:(lia) ltac:(lia)) as X. unfold rclz_fn in X.
  apply andb_prop in X. destruct X as [X1 X2].
  apply Z.eqb_eq in X1. apply Z.ltb_lt in X2. split; [exact X1| split; [|exact X2]].
  unfold rclz_v4. repeat first [apply Z.lor_nonneg; split | apply Z.shiftr_nonneg]; lia.
Qed.

Lemma lxor_4k_124 k : 3 <= k <= 12 -> Z.lxor (k * 4) 124 = 124 - 4 * k.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts. intros Hk. assert (H : k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12) by lia.
  destruct H as [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]]]; reflexivity. Qed.

Lemma lor_even_1 a : 0 <= a -> Z.even a = true -> Z.lor a 1 = a + 1.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts. intros Ha He.
  assert (D : Z.land a 1 = 0). { change 1 with (Z.ones 1). rewrite Z.land_ones by lia. change (2^1) with 2. rewrite Zeven_mod in He. apply Z.eqb_eq in He. exact He. }
  rewrite <- Z.lxor_lor by exact D. rewrite <- Z.add_nocarry_lxor by exact D. reflexivity. Qed.

Definition rentry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
   (lo : Z) (m : mem) (n : Z) : machine_state -> Prop :=
  fun ms' => exists a0 a1 a2 a3 m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) a0 a1 a2 a3 a4 a5 a6 a7
                  s2 (Z_to_bv 64 RDEBRUIJN) (Z_to_bv 64 (size_to_class n)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x19468) fc None m' (seg_rom ssegs)
    /\ rw_cells ssegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk ssegs m' lo (bv_unsigned sp + -48)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'.

Definition rmalloc_entry_walk__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (lo n : Z),
  a0 = Z_to_bv 64 n -> 0 <= n < MMAP_THRESHOLD ->
  stk ssegs m lo (bv_unsigned sp) -> 0x55000 <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv ssegs m ->
  rw_cells ssegs m RNEED_LOCKS [C1 (b8 0)] ->
  evt ssegs (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m n)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom ssegs)).
Section Sz3.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo n : ltac2:(SecDiet.SzSec.tyM 'rmalloc_entry_walk__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rmalloc_entry_walk__body : ltac2:(SecDiet.SzSec.bodyP 'rmalloc_entry_walk__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros HA N ST ILO LO MI NL.
 subst a0.
  pose proof (size_to_class_props n N) as (SCR & SFIT & LG). unfold MMAP_THRESHOLD in N.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold rmalloc_entry, RNEED_LOCKS in *.
  step. carve_frame 48%nat ST. step. step. step. step. step. step.
  (* [comment removed for export] *)
  step. step. step.
  step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  clear K0.
  (* [comment removed for export] *)
  step. step. step. step. step.
  step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  clear K1.
  (* [comment removed for export] *)
  step. step. step. step. step.
  rewrite (unsigned_lit (n + 3)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
  set (q := (n + 3) / 16) in *. assert (QR : 0 <= q < 8191) by (subst q; Z.div_mod_to_equations; lia).
  assert (STC : size_to_class n = stc_q q) by (apply size_to_class_q; lia).
  (* [comment removed for export] *)
  assert (LOCKJ : forall (a0' a1' a2' a3' : word) (sc : Z) (mj : mem),
    sc = size_to_class n ->
    mem_inv ssegs mj -> rw_cells ssegs mj (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> stk ssegs mj lo (bv_unsigned sp + -48) ->
    munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m mj -> wmono ssegs m mj -> rw_cells ssegs mj 343339 [C1 (b8 0)] ->
    evt ssegs (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m n)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 343448) a0' a1' a2' a3' a4 a5 a6 a7
               s2 (Z_to_bv 64 70156) (Z_to_bv 64 sc) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19450) fc None mj (seg_rom ssegs))).
  { intros a0' a1' a2' a3' sc mj -> MIj FRj STj MUj WMj NLj.
    step. step. rewrite ?zxb_b8 by lia. step. if_cases KL; zify_cond KL. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in KL by lia. lia. }
    apply evt_done. unfold rentry_post, RMLOCK, RDEBRUIJN. do 5 eexists. split; [reflexivity|].
    split; [exact FRj|]. split; [exact STj|]. split; [exact MUj|]. split; [exact WMj| exact MIj]. }
  step. if_cases K2; zify_cond K2; rewrite ?(unsigned_lit n) in K2 by lia.
  - (* [comment removed for export] *)
    apply LOCKJ; try assumption.
    rewrite STC. unfold stc_q. replace (q <? 10) with true by (symmetry; apply Z.ltb_lt; subst q; Z.div_mod_to_equations; lia). reflexivity.
  - (* [comment removed for export] *)
    assert (Q10 : 10 <= q) by (subst q; Z.div_mod_to_equations; lia).
    step. rewrite ?(unsigned_lit q) by lia. set (x := q + 1) in *. assert (XR : 11 <= x < 8192) by lia.
    destruct (rclz_pow_eq x XR) as [PW RV4].
    (* [comment removed for export] *)
    step.
    step. rewrite (unsigned_lit x), srliw_small by lia.
    pose proof (shiftr_small 13 x 1 ltac:(lia) ltac:(lia)) as R1. pose proof (shiftr_small 13 x 2 ltac:(lia) ltac:(lia)) as R2.
    step. rewrite (unsigned_lit (Z.shiftr x 2)), (unsigned_lit x) by lia.
    set (v1 := Z.lor (Z.shiftr x 2) x). assert (RX : 0 <= x < 2 ^ 13) by lia. pose proof (lor_small 13 _ _ ltac:(lia) R2 RX) as RV1. fold v1 in RV1.
    step. rewrite (unsigned_lit x), srliw_small by lia.
    step.
    step. rewrite (unsigned_lit v1), (unsigned_lit (Z.shiftr x 1)) by lia.
    set (v2 := Z.lor v1 (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) RV1 R1) as RV2. fold v2 in RV2.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit v2), srliw_small by lia. pose proof (shiftr_small 13 v2 2 RV2 ltac:(lia)) as R3.
    step. rewrite (unsigned_lit (Z.shiftr v2 2)), (unsigned_lit (Z.shiftr x 1)) by lia.
    set (w2 := Z.lor (Z.shiftr v2 2) (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) R3 R1) as RW2. fold w2 in RW2.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit w2) by lia. pose proof (shiftr_small 13 w2 4 RW2 ltac:(lia)) as R4.
    step. rewrite (unsigned_lit (Z.shiftr w2 4)), (unsigned_lit w2) by lia.
    set (w3 := Z.lor (Z.shiftr w2 4) w2). pose proof (lor_small 13 _ _ ltac:(lia) R4 RW2) as RW3. fold w3 in RW3.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit w3) by lia. pose proof (shiftr_small 13 w3 8 RW3 ltac:(lia)) as R5.
    step. rewrite (unsigned_lit (Z.shiftr w3 8)), (unsigned_lit w3) by lia.
    set (w4 := Z.lor (Z.shiftr w3 8) w3). pose proof (lor_small 13 _ _ ltac:(lia) R5 RW3) as RW4. fold w4 in RW4.
    assert (EW4 : w4 = rclz_v4 x) by reflexivity.
    (* [comment removed for export] *)
    step. step. step.
    rewrite (unsigned_lit w4), Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (w4 * 2 ^ 33)) by lia.
    replace ((w4 * 2 ^ 33) ≫ 49) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
    rewrite (unsigned_lit 0), Z.lor_0_l by lia.
    (* [comment removed for export] *)
    step. step. rewrite (unsigned_lit w4) by lia.
    step. rewrite (unsigned_lit (w4 + 1)) by lia. rewrite (unsigned_lit (Z.lxor w4 18446744073709551615)) by (rewrite zb_lxor_ones by lia; lia).
    change (Z.land (w4 + 1) (Z.lxor w4 18446744073709551615)) with (rclz_pow x). rewrite PW.
    set (k := Z.log2 x) in *.
    assert (P2 : 0 < 2 ^ k < 2 ^ 13) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
    assert (EK : k = Z.log2 x) by reflexivity. clearbody k. clear PW RV4 EW4 RW4 R5 RW3 R4 RW2 R3 RV2 RV1 R1 R2. subst w4 w3 w2 v2 v1.
    assert (EX : x = q + 1) by reflexivity. clearbody x.
    assert (K13 : 3 <= k <= 12) by (apply LG; lia).
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit (2 ^ k)) by lia. change 125613361 with rDB32.
    step. rewrite (mul_srliw27 k) by lia.
    pose proof (rdbi_range k) as DR.
    step. rewrite ?(unsigned_lit (rdbi k)) by lia.
    lazymatch goal with HI : mem_inv ssegs ?mc |- _ => pose proof (rdebruijn_read mc k HI ltac:(lia)) as DBR; unfold RDEBRUIJN in DBR end.
    step. rewrite ?zxb_b8 by lia. clear DBR.
    (* [comment removed for export] *)
    step. step. step. rewrite (wz_unsigned k), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
    step.
    rewrite (unsigned_lit (k * 4)), lxor_4k_124 by lia.
    set (i := 4 * k - 4). assert (IR : 8 <= i <= 44) by lia.
    replace (124 - 4 * k) with (120 - i) by lia.
    assert (STQ : stc_q q = (let i1 := if size_class (i + 1) <? x then i + 2 else i in if size_class i1 <? x then i1 + 1 else i1)).
    { unfold stc_q. replace (q <? 10) with false by (symmetry; apply Z.ltb_ge; lia). rewrite <- EX, <- EK. reflexivity. }
    assert (IEV : Z.even i = true) by (subst i; rewrite Z.even_sub, Z.even_mul; reflexivity).
    clearbody i. clear EK.
    pose proof (size_class_range (i + 1) ltac:(lia)) as SR1.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit (120 - i)) by lia. replace (121 - (120 - i)) with (i + 1) by lia.
    step. rewrite (unsigned_lit (i + 1)), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
    step. step. replace (70188 + (i + 1) * 2) with (70188 + 2 * (i + 1)) by lia.
    lazymatch goal with HI : mem_inv ssegs ?mc |- _ => pose proof (rsize_classes_read mc (i + 1) HI ltac:(lia)) as RS1; unfold RSIZE_CLASSES in RS1 end.
    (* [comment removed for export] *)
    step. rewrite ?zx16_wz by lia. clear RS1.
    (* [comment removed for export] *)
    assert (J1 : forall (i1 c : Z) (mj : mem),
      i1 = (if size_class (i + 1) <? x then i + 2 else i) -> c = i1 - i + 120 ->
      mem_inv ssegs mj -> rw_cells ssegs mj (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> stk ssegs mj lo (bv_unsigned sp + -48) ->
      munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m mj -> wmono ssegs m mj -> rw_cells ssegs mj 343339 [C1 (b8 0)] ->
      evt ssegs (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m n)
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 343448)
                 (Z_to_bv 64 (120 - i)) (Z_to_bv 64 70188) (Z_to_bv 64 c) (Z_to_bv 64 (70188 + 2 * (i + 1))) a4 a5 a6 a7
                 s2 (Z_to_bv 64 70156) (Z_to_bv 64 q) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x19434) fc None mj (seg_rom ssegs))).
    { intros i1 c mj Hi1 Hc MIj FRj STj MUj WMj NLj.
      assert (I1R : 8 <= i1 <= 46 /\ Z.even i1 = true).
      { subst i1. destruct (size_class (i + 1) <? x); (split; [lia|]); rewrite ?Z.even_add, ?IEV; reflexivity. }
      destruct I1R as [I1R I1E].
      pose proof (size_class_range i1 ltac:(lia)) as SR2.
      (* [comment removed for export] *)
      step. rewrite (unsigned_lit c), (unsigned_lit (120 - i)) by lia. replace (c - (120 - i)) with i1 by lia.
      step. rewrite (unsigned_lit i1), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
      step. replace (70188 + i1 * 2) with (70188 + 2 * i1) by lia.
      pose proof (rsize_classes_read mj i1 MIj ltac:(lia)) as RS2. unfold RSIZE_CLASSES in RS2.
      step. rewrite ?zx16_wz by lia. clear RS2.
      (* [comment removed for export] *)
      step. rewrite v_sltu_b2z, (unsigned_lit q), (wz_unsigned (size_class i1)) by lia.
      step. step.
      destruct (Z.ltb_spec q (size_class i1)) as [LT|GE]; cbn [Z.b2z].
      * rewrite (unsigned_lit 1), (unsigned_lit i1) by lia. change (Z.lxor 1 1) with 0. rewrite (unsigned_lit 0), Z.lor_0_r by lia.
        apply LOCKJ; try assumption. rewrite STC, STQ. cbv zeta. rewrite <- Hi1.
        replace (size_class i1 <? x) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
      * rewrite (unsigned_lit 0), (unsigned_lit i1) by lia. change (Z.lxor 0 1) with 1. rewrite (unsigned_lit 1), (lor_even_1 i1 ltac:(lia) I1E) by lia.
        apply LOCKJ; try assumption. rewrite STC, STQ. cbv zeta. rewrite <- Hi1.
        replace (size_class i1 <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
    step. if_cases K3; zify_cond K3; rewrite ?(unsigned_lit q), ?(wz_unsigned (size_class (i + 1))) in K3 by lia.
    + (* [comment removed for export] *)
      step. eapply J1; try eassumption; [reflexivity|]. replace (size_class (i + 1) <? x) with false by (symmetry; apply Z.ltb_ge; lia). lia.
    + (* [comment removed for export] *)
      step. step. eapply J1; try eassumption; [reflexivity|]. replace (size_class (i + 1) <? x) with true by (symmetry; apply Z.ltb_lt; lia). lia.
Qed.
End Sz3.
Lemma rmalloc_entry_walk : ltac:(let t := eval cbv delta [rmalloc_entry_walk__stmt] in rmalloc_entry_walk__stmt in exact t).
Proof using MSECV TLSFACTS. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo n. ltac2:(SecDiet.SzSec.closeP 'rmalloc_entry_walk__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
Definition rentry_big_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
   (lo : Z) (m : mem) (n : Z) : machine_state -> Prop :=
  fun ms' => exists a1 m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 131052) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x192d0) fc None m' (seg_rom ssegs)
    /\ rw_cells ssegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk ssegs m' lo (bv_unsigned sp + -48)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'.

Definition rentry_big_walk__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (lo n : Z),
  a0 = Z_to_bv 64 n -> MMAP_THRESHOLD <= n < 2^32 ->
  stk ssegs m lo (bv_unsigned sp) -> 0x55000 <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv ssegs m ->
  evt ssegs (rentry_big_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m n)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom ssegs)).
Section Sz4.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo n : ltac2:(SecDiet.SzSec.tyM 'rentry_big_walk__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rentry_big_walk__body : ltac2:(SecDiet.SzSec.bodyP 'rentry_big_walk__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros HA N ST ILO LO MI.
 subst a0. unfold MMAP_THRESHOLD in N.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold rmalloc_entry.
  step. carve_frame 48%nat ST. step. step. step. step. step. step.
  step. step. step.
  step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  clear K0.
  step. step. step. step. step.
  step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  clear K1.
  apply evt_done. unfold rentry_big_post, RMLOCK. do 2 eexists. split; [reflexivity|].
  lazymatch goal with H : rw_cells ssegs _ (bv_unsigned sp + -48) _ |- _ => split; [exact H|] end.
  repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed.
End Sz4.
Lemma rentry_big_walk : ltac:(let t := eval cbv delta [rentry_big_walk__stmt] in rentry_big_walk__stmt in exact t).
Proof using MSECV TB. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo n. ltac2:(SecDiet.SzSec.closeP 'rentry_big_walk__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End PORT.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.TlsBaseU.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.SFModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_enframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.Malloc_fp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_entry.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MSecret.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Local Unset Keyed Unification.

(* [comment removed for export] *)
Definition rDB32 : Z := 125613361.   (* [comment removed for export] *)
Definition rdbi (k : Z) : Z := ((2 ^ k * rDB32) mod 2^32) / 2^27.

Lemma rdbi_range k : 0 <= rdbi k < 32.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts. unfold rdbi. pose proof (Z.mod_pos_bound (2^k * rDB32) (2^32) ltac:(lia)). Z.div_mod_to_equations. nia. Qed.

Definition rdebruijn_bytes : list byte :=
  Eval vm_compute in (match image_bytes usegs RDEBRUIJN 32 with Some bs => bs | None => [] end).

Lemma rdebruijn_ro : forall m, mem_inv usegs m -> ro_cells usegs m RDEBRUIJN [CB 32 rdebruijn_bytes].
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts. intros m MI. apply (ro_cells_image usegs m); [exact MI | vm_compute; reflexivity | unfold RDEBRUIJN; lia | unfold RDEBRUIJN; cbn; lia]. Qed.

Lemma rdebruijn_read : forall m k, mem_inv usegs m -> 0 <= k < 32 ->
  ov_read_bytes usegs m (wa (RDEBRUIJN + rdbi k)) 1 = Some [b8 k].
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros m k MI Hk.
  destruct (rdebruijn_ro m MI) as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  pose proof (rdbi_range k) as R.
  rewrite (bytes_at_read usegs m RDEBRUIJN rdebruijn_bytes (rdbi k) 1 B) by (cbn; lia).
  assert (Hn : exists n, k = Z.of_nat n /\ (n < 32)%nat) by (exists (Z.to_nat k); split; [lia|lia]).
  destruct Hn as (n & -> & Hn).
  Ltac solve_db := vm_compute; reflexivity.
  do 32 (destruct n as [|n]; [solve_db |]). lia.
Qed.

(* [comment removed for export] *)
Lemma mul_srliw27 k : 0 <= k < 32 ->
  bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (Z_to_bv 64 (2 ^ k * rDB32)))) 27) = rdbi k.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros Hk. unfold rdbi.
  assert (P : 0 < 2 ^ k <= 2 ^ 31) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_le_mono_r; lia]).
  rewrite unsigned_lit by (unfold rDB32; nia).
  change (bv_wrap 32 (2 ^ k * rDB32)) with ((2 ^ k * rDB32) mod 2^32).
  rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.mod_pos_bound (2 ^ k * rDB32) (2^32) ltac:(lia)).
  apply swrap32_small. Z.div_mod_to_equations. nia.
Qed.

Definition rclz_v4 (x : Z) : Z :=
  let v1 := Z.lor (Z.shiftr x 2) x in
  let v2 := Z.lor v1 (Z.shiftr x 1) in
  let w2 := Z.lor (Z.shiftr v2 2) (Z.shiftr x 1) in
  let w3 := Z.lor (Z.shiftr w2 4) w2 in
  Z.lor (Z.shiftr w3 8) w3.
Definition rclz_pow (x : Z) : Z := Z.land (rclz_v4 x + 1) (Z.lxor (rclz_v4 x) 18446744073709551615).
Definition rclz_fn (x : Z) : bool := (rclz_pow x =? 2 ^ Z.log2 x) && (rclz_v4 x <? 2 ^ 13).
(* [comment removed for export] *)
Fixpoint rme_zgo (x : Z) (k : nat) : list Z := match k with O => [] | S k' => x :: rme_zgo (x + 1) k' end.
#[using="Type"] Lemma rme_zgo_seq k s : map Z.of_nat (seq s k) = rme_zgo (Z.of_nat s) k.
Proof. revert s. induction k as [|k IH]; intros s; [reflexivity|]. cbn [seq map rme_zgo]. f_equal. rewrite IH. f_equal. lia. Qed.
#[using="Type"] Lemma rme_zseq_go a n : 0 <= a -> zseq a n = rme_zgo a (Z.to_nat n).
Proof. intros Ha. unfold zseq. rewrite rme_zgo_seq. f_equal. lia. Qed.
Lemma rclz_check_true : forallb rclz_fn (zseq 11 8181) = true.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  rewrite (rme_zseq_go 11 8181) by lia. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
Lemma rclz_pow_eq x : 11 <= x < 8192 -> rclz_pow x = 2 ^ Z.log2 x /\ 0 <= rclz_v4 x < 2 ^ 13.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros Hx. pose proof (forallb_zseq rclz_fn 11 8181 x rclz_check_true ltac:(lia) ltac:(lia)) as X. unfold rclz_fn in X.
  apply andb_prop in X. destruct X as [X1 X2].
  apply Z.eqb_eq in X1. apply Z.ltb_lt in X2. split; [exact X1| split; [|exact X2]].
  unfold rclz_v4. repeat first [apply Z.lor_nonneg; split | apply Z.shiftr_nonneg]; lia.
Qed.

Lemma lxor_4k_124 k : 3 <= k <= 12 -> Z.lxor (k * 4) 124 = 124 - 4 * k.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts. intros Hk. assert (H : k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12) by lia.
  destruct H as [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]]]; reflexivity. Qed.

Lemma lor_even_1 a : 0 <= a -> Z.even a = true -> Z.lor a 1 = a + 1.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts. intros Ha He.
  assert (D : Z.land a 1 = 0). { change 1 with (Z.ones 1). rewrite Z.land_ones by lia. change (2^1) with 2. rewrite Zeven_mod in He. apply Z.eqb_eq in He. exact He. }
  rewrite <- Z.lxor_lor by exact D. rewrite <- Z.add_nocarry_lxor by exact D. reflexivity. Qed.

Definition rentry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
   (lo : Z) (m : mem) (n : Z) : machine_state -> Prop :=
  fun ms' => exists a0 a1 a2 a3 m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) a0 a1 a2 a3 a4 a5 a6 a7
                  s2 (Z_to_bv 64 RDEBRUIJN) (Z_to_bv 64 (size_to_class n)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x19c28) fc None m' (seg_rom usegs)
    /\ rw_cells usegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk usegs m' lo (bv_unsigned sp + -48)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'.

Definition rmalloc_entry_walk__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (lo n : Z),
  a0 = Z_to_bv 64 n -> 0 <= n < MMAP_THRESHOLD ->
  stk usegs m lo (bv_unsigned sp) -> 0x56000 <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv usegs m ->
  rw_cells usegs m RNEED_LOCKS [C1 (b8 0)] ->
  evt usegs (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m n)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom usegs)).
Section Sz3.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo n : ltac2:(SecDiet.SzSec.tyM 'rmalloc_entry_walk__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rmalloc_entry_walk__body : ltac2:(SecDiet.SzSec.bodyP 'rmalloc_entry_walk__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
 intros HA N ST ILO LO MI NL. subst a0.
  pose proof (size_to_class_props n N) as (SCR & SFIT & LG). unfold MMAP_THRESHOLD in N.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold rmalloc_entry, RNEED_LOCKS in *.
  step. carve_frame 48%nat ST. step. step. step. step. step. step.
  (* [comment removed for export] *)
  step. step. step.
  step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  clear K0.
  (* [comment removed for export] *)
  step. step. step. step. step.
  step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  clear K1.
  (* [comment removed for export] *)
  step. step. step. step. step.
  rewrite (unsigned_lit (n + 3)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
  set (q := (n + 3) / 16) in *. assert (QR : 0 <= q < 8191) by (subst q; Z.div_mod_to_equations; lia).
  assert (STC : size_to_class n = stc_q q) by (apply size_to_class_q; lia).
  (* [comment removed for export] *)
  assert (LOCKJ : forall (a0' a1' a2' a3' : word) (sc : Z) (mj : mem),
    sc = size_to_class n ->
    mem_inv usegs mj -> rw_cells usegs mj (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> stk usegs mj lo (bv_unsigned sp + -48) ->
    munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m mj -> wmono usegs m mj -> rw_cells usegs mj 345323 [C1 (b8 0)] ->
    evt usegs (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m n)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 345432) a0' a1' a2' a3' a4 a5 a6 a7
               s2 (Z_to_bv 64 70156) (Z_to_bv 64 sc) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19c10) fc None mj (seg_rom usegs))).
  { intros a0' a1' a2' a3' sc mj -> MIj FRj STj MUj WMj NLj.
    step. step. rewrite ?zxb_b8 by lia. step. if_cases KL; zify_cond KL. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in KL by lia. lia. }
    apply evt_done. unfold rentry_post, RMLOCK, RDEBRUIJN. do 5 eexists. split; [reflexivity|].
    split; [exact FRj|]. split; [exact STj|]. split; [exact MUj|]. split; [exact WMj| exact MIj]. }
  step. if_cases K2; zify_cond K2; rewrite ?(unsigned_lit n) in K2 by lia.
  - (* [comment removed for export] *)
    apply LOCKJ; try assumption.
    rewrite STC. unfold stc_q. replace (q <? 10) with true by (symmetry; apply Z.ltb_lt; subst q; Z.div_mod_to_equations; lia). reflexivity.
  - (* [comment removed for export] *)
    assert (Q10 : 10 <= q) by (subst q; Z.div_mod_to_equations; lia).
    step. rewrite ?(unsigned_lit q) by lia. set (x := q + 1) in *. assert (XR : 11 <= x < 8192) by lia.
    destruct (rclz_pow_eq x XR) as [PW RV4].
    (* [comment removed for export] *)
    step.
    step. rewrite (unsigned_lit x), srliw_small by lia.
    pose proof (shiftr_small 13 x 1 ltac:(lia) ltac:(lia)) as R1. pose proof (shiftr_small 13 x 2 ltac:(lia) ltac:(lia)) as R2.
    step. rewrite (unsigned_lit (Z.shiftr x 2)), (unsigned_lit x) by lia.
    set (v1 := Z.lor (Z.shiftr x 2) x). assert (RX : 0 <= x < 2 ^ 13) by lia. pose proof (lor_small 13 _ _ ltac:(lia) R2 RX) as RV1. fold v1 in RV1.
    step. rewrite (unsigned_lit x), srliw_small by lia.
    step.
    step. rewrite (unsigned_lit v1), (unsigned_lit (Z.shiftr x 1)) by lia.
    set (v2 := Z.lor v1 (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) RV1 R1) as RV2. fold v2 in RV2.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit v2), srliw_small by lia. pose proof (shiftr_small 13 v2 2 RV2 ltac:(lia)) as R3.
    step. rewrite (unsigned_lit (Z.shiftr v2 2)), (unsigned_lit (Z.shiftr x 1)) by lia.
    set (w2 := Z.lor (Z.shiftr v2 2) (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) R3 R1) as RW2. fold w2 in RW2.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit w2) by lia. pose proof (shiftr_small 13 w2 4 RW2 ltac:(lia)) as R4.
    step. rewrite (unsigned_lit (Z.shiftr w2 4)), (unsigned_lit w2) by lia.
    set (w3 := Z.lor (Z.shiftr w2 4) w2). pose proof (lor_small 13 _ _ ltac:(lia) R4 RW2) as RW3. fold w3 in RW3.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit w3) by lia. pose proof (shiftr_small 13 w3 8 RW3 ltac:(lia)) as R5.
    step. rewrite (unsigned_lit (Z.shiftr w3 8)), (unsigned_lit w3) by lia.
    set (w4 := Z.lor (Z.shiftr w3 8) w3). pose proof (lor_small 13 _ _ ltac:(lia) R5 RW3) as RW4. fold w4 in RW4.
    assert (EW4 : w4 = rclz_v4 x) by reflexivity.
    (* [comment removed for export] *)
    step. step. step.
    rewrite (unsigned_lit w4), Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (w4 * 2 ^ 33)) by lia.
    replace ((w4 * 2 ^ 33) ≫ 49) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
    rewrite (unsigned_lit 0), Z.lor_0_l by lia.
    (* [comment removed for export] *)
    step. step. rewrite (unsigned_lit w4) by lia.
    step. rewrite (unsigned_lit (w4 + 1)) by lia. rewrite (unsigned_lit (Z.lxor w4 18446744073709551615)) by (rewrite zb_lxor_ones by lia; lia).
    change (Z.land (w4 + 1) (Z.lxor w4 18446744073709551615)) with (rclz_pow x). rewrite PW.
    set (k := Z.log2 x) in *.
    assert (P2 : 0 < 2 ^ k < 2 ^ 13) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
    assert (EK : k = Z.log2 x) by reflexivity. clearbody k. clear PW RV4 EW4 RW4 R5 RW3 R4 RW2 R3 RV2 RV1 R1 R2. subst w4 w3 w2 v2 v1.
    assert (EX : x = q + 1) by reflexivity. clearbody x.
    assert (K13 : 3 <= k <= 12) by (apply LG; lia).
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit (2 ^ k)) by lia. change 125613361 with rDB32.
    step. rewrite (mul_srliw27 k) by lia.
    pose proof (rdbi_range k) as DR.
    step. rewrite ?(unsigned_lit (rdbi k)) by lia.
    lazymatch goal with HI : mem_inv usegs ?mc |- _ => pose proof (rdebruijn_read mc k HI ltac:(lia)) as DBR; unfold RDEBRUIJN in DBR end.
    step. rewrite ?zxb_b8 by lia. clear DBR.
    (* [comment removed for export] *)
    step. step. step. rewrite (wz_unsigned k), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
    step.
    rewrite (unsigned_lit (k * 4)), lxor_4k_124 by lia.
    set (i := 4 * k - 4). assert (IR : 8 <= i <= 44) by lia.
    replace (124 - 4 * k) with (120 - i) by lia.
    assert (STQ : stc_q q = (let i1 := if size_class (i + 1) <? x then i + 2 else i in if size_class i1 <? x then i1 + 1 else i1)).
    { unfold stc_q. replace (q <? 10) with false by (symmetry; apply Z.ltb_ge; lia). rewrite <- EX, <- EK. reflexivity. }
    assert (IEV : Z.even i = true) by (subst i; rewrite Z.even_sub, Z.even_mul; reflexivity).
    clearbody i. clear EK.
    pose proof (size_class_range (i + 1) ltac:(lia)) as SR1.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit (120 - i)) by lia. replace (121 - (120 - i)) with (i + 1) by lia.
    step. rewrite (unsigned_lit (i + 1)), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
    step. step. replace (70188 + (i + 1) * 2) with (70188 + 2 * (i + 1)) by lia.
    lazymatch goal with HI : mem_inv usegs ?mc |- _ => pose proof (rsize_classes_read mc (i + 1) HI ltac:(lia)) as RS1; unfold RSIZE_CLASSES in RS1 end.
    (* [comment removed for export] *)
    step. rewrite ?zx16_wz by lia. clear RS1.
    (* [comment removed for export] *)
    assert (J1 : forall (i1 c : Z) (mj : mem),
      i1 = (if size_class (i + 1) <? x then i + 2 else i) -> c = i1 - i + 120 ->
      mem_inv usegs mj -> rw_cells usegs mj (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> stk usegs mj lo (bv_unsigned sp + -48) ->
      munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m mj -> wmono usegs m mj -> rw_cells usegs mj 345323 [C1 (b8 0)] ->
      evt usegs (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m n)
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 345432)
                 (Z_to_bv 64 (120 - i)) (Z_to_bv 64 70188) (Z_to_bv 64 c) (Z_to_bv 64 (70188 + 2 * (i + 1))) a4 a5 a6 a7
                 s2 (Z_to_bv 64 70156) (Z_to_bv 64 q) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x19bf4) fc None mj (seg_rom usegs))).
    { intros i1 c mj Hi1 Hc MIj FRj STj MUj WMj NLj.
      assert (I1R : 8 <= i1 <= 46 /\ Z.even i1 = true).
      { subst i1. destruct (size_class (i + 1) <? x); (split; [lia|]); rewrite ?Z.even_add, ?IEV; reflexivity. }
      destruct I1R as [I1R I1E].
      pose proof (size_class_range i1 ltac:(lia)) as SR2.
      (* [comment removed for export] *)
      step. rewrite (unsigned_lit c), (unsigned_lit (120 - i)) by lia. replace (c - (120 - i)) with i1 by lia.
      step. rewrite (unsigned_lit i1), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
      step. replace (70188 + i1 * 2) with (70188 + 2 * i1) by lia.
      pose proof (rsize_classes_read mj i1 MIj ltac:(lia)) as RS2. unfold RSIZE_CLASSES in RS2.
      step. rewrite ?zx16_wz by lia. clear RS2.
      (* [comment removed for export] *)
      step. rewrite v_sltu_b2z, (unsigned_lit q), (wz_unsigned (size_class i1)) by lia.
      step. step.
      destruct (Z.ltb_spec q (size_class i1)) as [LT|GE]; cbn [Z.b2z].
      * rewrite (unsigned_lit 1), (unsigned_lit i1) by lia. change (Z.lxor 1 1) with 0. rewrite (unsigned_lit 0), Z.lor_0_r by lia.
        apply LOCKJ; try assumption. rewrite STC, STQ. cbv zeta. rewrite <- Hi1.
        replace (size_class i1 <? x) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
      * rewrite (unsigned_lit 0), (unsigned_lit i1) by lia. change (Z.lxor 0 1) with 1. rewrite (unsigned_lit 1), (lor_even_1 i1 ltac:(lia) I1E) by lia.
        apply LOCKJ; try assumption. rewrite STC, STQ. cbv zeta. rewrite <- Hi1.
        replace (size_class i1 <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
    step. if_cases K3; zify_cond K3; rewrite ?(unsigned_lit q), ?(wz_unsigned (size_class (i + 1))) in K3 by lia.
    + (* [comment removed for export] *)
      step. eapply J1; try eassumption; [reflexivity|]. replace (size_class (i + 1) <? x) with false by (symmetry; apply Z.ltb_ge; lia). lia.
    + (* [comment removed for export] *)
      step. step. eapply J1; try eassumption; [reflexivity|]. replace (size_class (i + 1) <? x) with true by (symmetry; apply Z.ltb_lt; lia). lia.
Qed.
End Sz3.
Lemma rmalloc_entry_walk : ltac:(let t := eval cbv delta [rmalloc_entry_walk__stmt] in rmalloc_entry_walk__stmt in exact t).
Proof using MSECV TLSFACTS. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo n. ltac2:(SecDiet.SzSec.closeP 'rmalloc_entry_walk__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
Definition rentry_big_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
   (lo : Z) (m : mem) (n : Z) : machine_state -> Prop :=
  fun ms' => exists a1 m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 131052) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x19a90) fc None m' (seg_rom usegs)
    /\ rw_cells usegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk usegs m' lo (bv_unsigned sp + -48)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'.

Definition rentry_big_walk__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (lo n : Z),
  a0 = Z_to_bv 64 n -> MMAP_THRESHOLD <= n < 2^32 ->
  stk usegs m lo (bv_unsigned sp) -> 0x56000 <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv usegs m ->
  evt usegs (rentry_big_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m n)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom usegs)).
Section Sz4.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo n : ltac2:(SecDiet.SzSec.tyM 'rentry_big_walk__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rentry_big_walk__body : ltac2:(SecDiet.SzSec.bodyP 'rentry_big_walk__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
 intros HA N ST ILO LO MI. subst a0. unfold MMAP_THRESHOLD in N.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold rmalloc_entry.
  step. carve_frame 48%nat ST. step. step. step. step. step. step.
  step. step. step.
  step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  clear K0.
  step. step. step. step. step.
  step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  clear K1.
  apply evt_done. unfold rentry_big_post, RMLOCK. do 2 eexists. split; [reflexivity|].
  lazymatch goal with H : rw_cells usegs _ (bv_unsigned sp + -48) _ |- _ => split; [exact H|] end.
  repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed.
End Sz4.
Lemma rentry_big_walk : ltac:(let t := eval cbv delta [rentry_big_walk__stmt] in rentry_big_walk__stmt in exact t).
Proof using MSECV TB. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo n. ltac2:(SecDiet.SzSec.closeP 'rentry_big_walk__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End PORT.

End WithCeil.
End TwB.
End RF_malloc_entry.

(* [comment removed for export] *)
Module RF_reallocB.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import TlsBase.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocKit_A2__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_entry.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RF_malloc_entry.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

(* [comment removed for export] *)
Definition rrdec_small_post (ra sp gp tp t0 s0 s1 a0 a1 a3 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (inplace : bool) : machine_state -> Prop :=
  fun ms' => exists t1 t2 a2 a4 a5 a7 t3 t4,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 (if inplace then 0x1a504 else 0x1a4c4)) fc None m (seg_rom ssegs).

(* [comment removed for export] *)
Lemma rrealloc_stc_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a4 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (n sc : Z),
  bv_unsigned a1 = n -> 0 <= n < MMAP_THRESHOLD -> 0 <= sc < 64 -> mem_inv ssegs m ->
  evt ssegs (rrdec_small_post ra sp gp tp t0 s0 s1 a0 a1 (Z_to_bv 64 sc) a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 F fc m (sc <=? size_to_class n + 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 sc) a4 (Z_to_bv 64 RSIZE_CLASSES) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1a330) fc None m (seg_rom ssegs)).
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros until sc. intros HN N SC MI.
  pose proof (size_to_class_props n N) as (SCR & SFIT & LG). unfold MMAP_THRESHOLD in N.
  unfold RSIZE_CLASSES.
  (* [comment removed for export] *)
  step. step. step.
  rewrite HN, ?(unsigned_lit (n + 3)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
  set (q := (n + 3) / 16) in *. assert (QR : 0 <= q < 8191) by (subst q; Z.div_mod_to_equations; lia).
  assert (STC : size_to_class n = stc_q q) by (apply size_to_class_q; lia).
  (* [comment removed for export] *)
  assert (JOIN : forall (a4' a5' a7' t1' : word) (c : Z), c = size_to_class n ->
    evt ssegs (rrdec_small_post ra sp gp tp t0 s0 s1 a0 a1 (Z_to_bv 64 sc) a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 F fc m (sc <=? size_to_class n + 1))
      (MS (mkR ra sp gp tp t0 t1' t2 s0 s1 a0 a1 (Z_to_bv 64 c) (Z_to_bv 64 sc) a4' a5' a6 a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1a4bc) fc None m (seg_rom ssegs))).
  { intros a4' a5' a7' t1' c ->.
    step. rewrite ?(unsigned_lit (size_to_class n)) by lia. rewrite swrap32_small by lia.
    step. if_cases K; zify_cond K; rewrite ?signed_of_Z in K by lia.
    - unfold rrdec_small_post. replace (sc <=? size_to_class n + 1) with true by (symmetry; apply Z.leb_le; lia).
      apply evt_done. do 8 eexists. reflexivity.
    - unfold rrdec_small_post. replace (sc <=? size_to_class n + 1) with false by (symmetry; apply Z.leb_gt; lia).
      apply evt_done. do 8 eexists. reflexivity. }
  step. if_cases K2; zify_cond K2; rewrite ?HN, ?(unsigned_lit n) in K2 by lia.
  - (* [comment removed for export] *)
    apply JOIN. rewrite STC. unfold stc_q. replace (q <? 10) with true by (symmetry; apply Z.ltb_lt; subst q; Z.div_mod_to_equations; lia). reflexivity.
  - (* [comment removed for export] *)
    assert (Q10 : 10 <= q) by (subst q; Z.div_mod_to_equations; lia).
    step. rewrite ?(unsigned_lit q) by lia. set (x := q + 1) in *. assert (XR : 11 <= x < 8192) by lia.
    destruct (rclz_pow_eq x XR) as [PW RV4].
    (* [comment removed for export] *)
    step.
    step. rewrite (unsigned_lit x), srliw_small by lia.
    pose proof (shiftr_small 13 x 1 ltac:(lia) ltac:(lia)) as R1. pose proof (shiftr_small 13 x 2 ltac:(lia) ltac:(lia)) as R2.
    step. rewrite (unsigned_lit (Z.shiftr x 2)), (unsigned_lit x) by lia.
    set (v1 := Z.lor (Z.shiftr x 2) x). assert (RX : 0 <= x < 2 ^ 13) by lia. pose proof (lor_small 13 _ _ ltac:(lia) R2 RX) as RV1. fold v1 in RV1.
    step. rewrite (unsigned_lit x), srliw_small by lia.
    step. rewrite (unsigned_lit v1), (unsigned_lit (Z.shiftr x 1)) by lia.
    set (v2 := Z.lor v1 (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) RV1 R1) as RV2. fold v2 in RV2.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit v2), srliw_small by lia. pose proof (shiftr_small 13 v2 2 RV2 ltac:(lia)) as R3.
    step. rewrite (unsigned_lit (Z.shiftr v2 2)), (unsigned_lit (Z.shiftr x 1)) by lia.
    set (w2 := Z.lor (Z.shiftr v2 2) (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) R3 R1) as RW2. fold w2 in RW2.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit w2) by lia. pose proof (shiftr_small 13 w2 4 RW2 ltac:(lia)) as R4.
    step. rewrite (unsigned_lit (Z.shiftr w2 4)), (unsigned_lit w2) by lia.
    set (w3 := Z.lor (Z.shiftr w2 4) w2). pose proof (lor_small 13 _ _ ltac:(lia) R4 RW2) as RW3. fold w3 in RW3.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit w3) by lia. pose proof (shiftr_small 13 w3 8 RW3 ltac:(lia)) as R5.
    step. rewrite (unsigned_lit (Z.shiftr w3 8)), (unsigned_lit w3) by lia.
    set (w4 := Z.lor (Z.shiftr w3 8) w3). pose proof (lor_small 13 _ _ ltac:(lia) R5 RW3) as RW4. fold w4 in RW4.
    assert (EW4 : w4 = rclz_v4 x) by reflexivity.
    (* [comment removed for export] *)
    step. rewrite ?(unsigned_lit w4) by lia.
    step. rewrite ?(unsigned_lit w4) by lia.
    step. rewrite (unsigned_lit (w4 + 1)) by lia. rewrite (unsigned_lit (Z.lxor w4 18446744073709551615)) by (rewrite zb_lxor_ones by lia; lia).
    change (Z.land (w4 + 1) (Z.lxor w4 18446744073709551615)) with (rclz_pow x). rewrite PW.
    set (k := Z.log2 x) in *.
    assert (P2 : 0 < 2 ^ k < 2 ^ 13) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
    assert (EK : k = Z.log2 x) by reflexivity. clearbody k. clear PW RV4 EW4 RW4 R5 RW3 R4 RW2 R3 RV2 RV1 R1 R2. subst w4 w3 w2 v2 v1.
    assert (EX : x = q + 1) by reflexivity. clearbody x.
    assert (K13 : 3 <= k <= 12) by (apply LG; lia).
    (* [comment removed for export] *)
    step. step. step.
    step. rewrite (unsigned_lit (2 ^ k)) by lia. change 125613361 with rDB32.
    step. rewrite (mul_srliw27 k) by lia.
    pose proof (rdbi_range k) as DR.
    step. rewrite ?(unsigned_lit (rdbi k)) by lia.
    pose proof (rdebruijn_read m k MI ltac:(lia)) as DBR. unfold RDEBRUIJN in DBR.
    step. rewrite ?zxb_b8 by lia. clear DBR.
    (* [comment removed for export] *)
    step. rewrite (wz_unsigned k), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
    step. rewrite (unsigned_lit (k * 4)), lxor_4k_124 by lia.
    set (i := 4 * k - 4). assert (IR : 8 <= i <= 44) by lia.
    replace (124 - 4 * k) with (120 - i) by lia.
    assert (STQ : stc_q q = (let i1 := if size_class (i + 1) <? x then i + 2 else i in if size_class i1 <? x then i1 + 1 else i1)).
    { unfold stc_q. replace (q <? 10) with false by (symmetry; apply Z.ltb_ge; lia). rewrite <- EX, <- EK. reflexivity. }
    assert (IEV : Z.even i = true) by (subst i; rewrite Z.even_sub, Z.even_mul; reflexivity).
    clearbody i. clear EK.
    pose proof (size_class_range (i + 1) ltac:(lia)) as SR1.
    step. step. rewrite ?(unsigned_lit (120 - i)) by lia. replace (121 + - (120 - i)) with (i + 1) by lia.
    step. rewrite ?(unsigned_lit (i + 1)), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
    step. replace (70188 + (i + 1) * 2) with (70188 + 2 * (i + 1)) by lia.
    pose proof (rsize_classes_read m (i + 1) MI ltac:(lia)) as RS1. unfold RSIZE_CLASSES in RS1.
    step. rewrite ?zx16_wz by lia. clear RS1.
    (* [comment removed for export] *)
    assert (J1 : forall (i1 c : Z),
      i1 = (if size_class (i + 1) <? x then i + 2 else i) -> c = i1 - i + 120 ->
      evt ssegs (rrdec_small_post ra sp gp tp t0 s0 s1 a0 a1 (Z_to_bv 64 sc) a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 F fc m (sc <=? size_to_class n + 1))
        (MS (mkR ra sp gp tp t0 (Z_to_bv 64 70156) t2 s0 s1 a0 a1 (Z_to_bv 64 q) (Z_to_bv 64 sc) (Z_to_bv 64 (120 - i)) (Z_to_bv 64 70188) a6 (Z_to_bv 64 c)
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1a4a0) fc None m (seg_rom ssegs))).
    { intros i1 c Hi1 Hc.
      assert (I1R : 8 <= i1 <= 46 /\ Z.even i1 = true).
      { subst i1. destruct (size_class (i + 1) <? x); (split; [lia|]); rewrite ?Z.even_add, ?IEV; reflexivity. }
      destruct I1R as [I1R I1E].
      pose proof (size_class_range i1 ltac:(lia)) as SR2.
      (* [comment removed for export] *)
      step. rewrite ?(unsigned_lit c), ?(unsigned_lit (120 - i)) by lia. replace (c + - (120 - i)) with i1 by lia.
      step. rewrite ?(unsigned_lit i1), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
      step. rewrite ?(unsigned_lit i1) by lia. replace (70188 + i1 * 2) with (70188 + 2 * i1) by lia.
      pose proof (rsize_classes_read m i1 MI ltac:(lia)) as RS2. unfold RSIZE_CLASSES in RS2.
      step. rewrite ?zx16_wz by lia. clear RS2.
      (* [comment removed for export] *)
      step. rewrite v_sltu_b2z, (unsigned_lit q), (wz_unsigned (size_class i1)) by lia.
      step. step.
      destruct (Z.ltb_spec q (size_class i1)) as [LT|GE]; cbn [Z.b2z].
      * rewrite (unsigned_lit 1), (unsigned_lit i1) by lia. change (Z.lxor 1 1) with 0. rewrite (unsigned_lit 0), Z.lor_0_r by lia.
        apply JOIN. rewrite STC, STQ. cbv zeta. rewrite <- Hi1.
        replace (size_class i1 <? x) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
      * rewrite (unsigned_lit 0), (unsigned_lit i1) by lia. change (Z.lxor 0 1) with 1. rewrite (unsigned_lit 1), (lor_even_1 i1 ltac:(lia) I1E) by lia.
        apply JOIN. rewrite STC, STQ. cbv zeta. rewrite <- Hi1.
        replace (size_class i1 <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
    step. if_cases K3; zify_cond K3; rewrite ?(unsigned_lit q), ?(wz_unsigned (size_class (i + 1))) in K3 by lia.
    + (* [comment removed for export] *)
      step. eapply J1; [reflexivity|]. replace (size_class (i + 1) <? x) with false by (symmetry; apply Z.ltb_ge; lia). lia.
    + (* [comment removed for export] *)
      step. step. eapply J1; [reflexivity|]. replace (size_class (i + 1) <? x) with true by (symmetry; apply Z.ltb_lt; lia). lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rrealloc_dec_small : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a4 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (n sc avail : Z),
  bv_unsigned a1 = n -> 0 <= n < MMAP_THRESHOLD -> n <= avail -> 0 <= avail < 2^64 -> 0 <= sc < 64 -> mem_inv ssegs m ->
  evt ssegs (rrdec_small_post ra sp gp tp t0 s0 s1 a0 a1 (Z_to_bv 64 sc) a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 F fc m (sc <=? size_to_class n + 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 sc) a4 (Z_to_bv 64 RSIZE_CLASSES) a6 (Z_to_bv 64 avail) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1a320) fc None m (seg_rom ssegs)).
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros until avail. intros HN N LE AV SC MI. unfold MMAP_THRESHOLD in N.
  (* [comment removed for export] *)
  step. step. step. if_cases K1; zify_cond K1. { exfalso. rewrite ?HN, ?unsigned_lit in K1 by lia. lia. }
  step. if_cases K2; zify_cond K2. { exfalso. rewrite ?HN, ?unsigned_lit in K2 by lia. lia. }
  eapply rrealloc_stc_walk; [exact HN| unfold MMAP_THRESHOLD; lia| exact SC| exact MI].
Qed.

(* [comment removed for export] *)
Definition rrdec_big_post (ra sp gp tp t0 t1 s0 s1 a0 a1 a2 a3 a4 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) : machine_state -> Prop :=
  fun ms' => exists t2 a5 t3,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x1a3dc) fc None m (seg_rom ssegs).

Lemma rrealloc_dec_big : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a4 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (n sc avail : Z),
  bv_unsigned a1 = n -> MMAP_THRESHOLD <= n < 2^64 -> 0 <= avail < 2^64 -> sc = 63 ->
  evt ssegs (rrdec_big_post ra sp gp tp t0 t1 s0 s1 a0 a1 a2 (Z_to_bv 64 sc) a4 a6 (Z_to_bv 64 avail) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 sc) a4 (Z_to_bv 64 RSIZE_CLASSES) a6 (Z_to_bv 64 avail) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1a320) fc None m (seg_rom ssegs)).
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros until avail. intros HN N AV SC. unfold MMAP_THRESHOLD in N.
  step. step. step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?HN, ?unsigned_lit in K1 by lia. lia. }
  (* [comment removed for export] *)
  step. step. if_cases K2; zify_cond K2. { exfalso. rewrite ?HN, ?unsigned_lit in K2 by lia. lia. }
  step. step. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by lia. lia. }
  step. step. if_cases K4; zify_cond K4. 2:{ exfalso. rewrite ?unsigned_lit in K4 by lia. lia. }
  unfold rrdec_big_post. apply evt_done. do 3 eexists. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rrealloc_dec_fb : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a4 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (n sc avail : Z),
  bv_unsigned a1 = n -> 0 <= n < 2^64 -> 0 <= avail < 2^64 -> 0 <= sc < 64 -> (48 <= sc -> sc = 63) -> mem_inv ssegs m ->
  (n <=? avail) && (n <? MMAP_THRESHOLD) && (sc <=? size_to_class n + 1) = false ->
  (48 <=? sc) && (MMAP_THRESHOLD <=? n) = false ->
  evt ssegs (rrdec_small_post ra sp gp tp t0 s0 s1 a0 a1 (Z_to_bv 64 sc) a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 F fc m false)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 sc) a4 (Z_to_bv 64 RSIZE_CLASSES) a6 (Z_to_bv 64 avail) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1a320) fc None m (seg_rom ssegs)).
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros until avail. intros HN N AV SC SC63 MI C1 C2. unfold MMAP_THRESHOLD in *.
  step. step. step. if_cases K1; zify_cond K1; rewrite ?HN, ?unsigned_lit in K1 by lia.
  - (* [comment removed for export] *)
    step. step. if_cases K2; zify_cond K2; rewrite ?HN, ?unsigned_lit in K2 by lia. { exfalso. lia. }
    step. step. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia.
    + unfold rrdec_small_post. apply evt_done. do 8 eexists. reflexivity.
    + exfalso. replace (48 <=? sc) with true in C2 by (symmetry; apply Z.leb_le; lia).
      replace (131052 <=? n) with true in C2 by (symmetry; apply Z.leb_le; lia). discriminate C2.
  - step. if_cases K2; zify_cond K2; rewrite ?HN, ?unsigned_lit in K2 by lia.
    + (* [comment removed for export] *)
      step. step. if_cases K3; zify_cond K3; rewrite ?HN, ?unsigned_lit in K3 by lia. 2:{ exfalso. lia. }
      unfold rrdec_small_post. apply evt_done. do 8 eexists. reflexivity.
    + (* [comment removed for export] *)
      replace (n <=? avail) with true in C1 by (symmetry; apply Z.leb_le; lia).
      replace (n <? 131052) with true in C1 by (symmetry; apply Z.ltb_lt; lia). cbn [andb] in C1.
      replace false with (sc <=? size_to_class n + 1) by exact C1.
      eapply rrealloc_stc_walk; [exact HN| unfold MMAP_THRESHOLD; lia| exact SC| exact MI].
Qed.
End PORT.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.TlsBaseU.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.SFModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_entry.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RF_malloc_entry.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MSecret.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

(* [comment removed for export] *)
Definition rrdec_small_post (ra sp gp tp t0 s0 s1 a0 a1 a3 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (inplace : bool) : machine_state -> Prop :=
  fun ms' => exists t1 t2 a2 a4 a5 a7 t3 t4,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 (if inplace then 0x1acc4 else 0x1ac84)) fc None m (seg_rom usegs).

(* [comment removed for export] *)
Definition rrealloc_stc_walk__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a4 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (n sc : Z),
  bv_unsigned a1 = n -> 0 <= n < MMAP_THRESHOLD -> 0 <= sc < 64 -> mem_inv usegs m ->
  evt usegs (rrdec_small_post ra sp gp tp t0 s0 s1 a0 a1 (Z_to_bv 64 sc) a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 F fc m (sc <=? size_to_class n + 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 sc) a4 (Z_to_bv 64 RSIZE_CLASSES) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1aaf0) fc None m (seg_rom usegs)).
Section Sz1.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a4 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n sc : ltac2:(SecDiet.SzSec.tyM 'rrealloc_stc_walk__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rrealloc_stc_walk__body : ltac2:(SecDiet.SzSec.bodyP 'rrealloc_stc_walk__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
 intros HN N SC MI.
  pose proof (size_to_class_props n N) as (SCR & SFIT & LG). unfold MMAP_THRESHOLD in N.
  unfold RSIZE_CLASSES.
  (* [comment removed for export] *)
  step. step. step.
  rewrite HN, ?(unsigned_lit (n + 3)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
  set (q := (n + 3) / 16) in *. assert (QR : 0 <= q < 8191) by (subst q; Z.div_mod_to_equations; lia).
  assert (STC : size_to_class n = stc_q q) by (apply size_to_class_q; lia).
  (* [comment removed for export] *)
  assert (JOIN : forall (a4' a5' a7' t1' : word) (c : Z), c = size_to_class n ->
    evt usegs (rrdec_small_post ra sp gp tp t0 s0 s1 a0 a1 (Z_to_bv 64 sc) a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 F fc m (sc <=? size_to_class n + 1))
      (MS (mkR ra sp gp tp t0 t1' t2 s0 s1 a0 a1 (Z_to_bv 64 c) (Z_to_bv 64 sc) a4' a5' a6 a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1ac7c) fc None m (seg_rom usegs))).
  { intros a4' a5' a7' t1' c ->.
    step. rewrite ?(unsigned_lit (size_to_class n)) by lia. rewrite swrap32_small by lia.
    step. if_cases K; zify_cond K; rewrite ?signed_of_Z in K by lia.
    - unfold rrdec_small_post. replace (sc <=? size_to_class n + 1) with true by (symmetry; apply Z.leb_le; lia).
      apply evt_done. do 8 eexists. reflexivity.
    - unfold rrdec_small_post. replace (sc <=? size_to_class n + 1) with false by (symmetry; apply Z.leb_gt; lia).
      apply evt_done. do 8 eexists. reflexivity. }
  step. if_cases K2; zify_cond K2; rewrite ?HN, ?(unsigned_lit n) in K2 by lia.
  - (* [comment removed for export] *)
    apply JOIN. rewrite STC. unfold stc_q. replace (q <? 10) with true by (symmetry; apply Z.ltb_lt; subst q; Z.div_mod_to_equations; lia). reflexivity.
  - (* [comment removed for export] *)
    assert (Q10 : 10 <= q) by (subst q; Z.div_mod_to_equations; lia).
    step. rewrite ?(unsigned_lit q) by lia. set (x := q + 1) in *. assert (XR : 11 <= x < 8192) by lia.
    destruct (rclz_pow_eq x XR) as [PW RV4].
    (* [comment removed for export] *)
    step.
    step. rewrite (unsigned_lit x), srliw_small by lia.
    pose proof (shiftr_small 13 x 1 ltac:(lia) ltac:(lia)) as R1. pose proof (shiftr_small 13 x 2 ltac:(lia) ltac:(lia)) as R2.
    step. rewrite (unsigned_lit (Z.shiftr x 2)), (unsigned_lit x) by lia.
    set (v1 := Z.lor (Z.shiftr x 2) x). assert (RX : 0 <= x < 2 ^ 13) by lia. pose proof (lor_small 13 _ _ ltac:(lia) R2 RX) as RV1. fold v1 in RV1.
    step. rewrite (unsigned_lit x), srliw_small by lia.
    step. rewrite (unsigned_lit v1), (unsigned_lit (Z.shiftr x 1)) by lia.
    set (v2 := Z.lor v1 (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) RV1 R1) as RV2. fold v2 in RV2.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit v2), srliw_small by lia. pose proof (shiftr_small 13 v2 2 RV2 ltac:(lia)) as R3.
    step. rewrite (unsigned_lit (Z.shiftr v2 2)), (unsigned_lit (Z.shiftr x 1)) by lia.
    set (w2 := Z.lor (Z.shiftr v2 2) (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) R3 R1) as RW2. fold w2 in RW2.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit w2) by lia. pose proof (shiftr_small 13 w2 4 RW2 ltac:(lia)) as R4.
    step. rewrite (unsigned_lit (Z.shiftr w2 4)), (unsigned_lit w2) by lia.
    set (w3 := Z.lor (Z.shiftr w2 4) w2). pose proof (lor_small 13 _ _ ltac:(lia) R4 RW2) as RW3. fold w3 in RW3.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit w3) by lia. pose proof (shiftr_small 13 w3 8 RW3 ltac:(lia)) as R5.
    step. rewrite (unsigned_lit (Z.shiftr w3 8)), (unsigned_lit w3) by lia.
    set (w4 := Z.lor (Z.shiftr w3 8) w3). pose proof (lor_small 13 _ _ ltac:(lia) R5 RW3) as RW4. fold w4 in RW4.
    assert (EW4 : w4 = rclz_v4 x) by reflexivity.
    (* [comment removed for export] *)
    step. rewrite ?(unsigned_lit w4) by lia.
    step. rewrite ?(unsigned_lit w4) by lia.
    step. rewrite (unsigned_lit (w4 + 1)) by lia. rewrite (unsigned_lit (Z.lxor w4 18446744073709551615)) by (rewrite zb_lxor_ones by lia; lia).
    change (Z.land (w4 + 1) (Z.lxor w4 18446744073709551615)) with (rclz_pow x). rewrite PW.
    set (k := Z.log2 x) in *.
    assert (P2 : 0 < 2 ^ k < 2 ^ 13) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
    assert (EK : k = Z.log2 x) by reflexivity. clearbody k. clear PW RV4 EW4 RW4 R5 RW3 R4 RW2 R3 RV2 RV1 R1 R2. subst w4 w3 w2 v2 v1.
    assert (EX : x = q + 1) by reflexivity. clearbody x.
    assert (K13 : 3 <= k <= 12) by (apply LG; lia).
    (* [comment removed for export] *)
    step. step. step.
    step. rewrite (unsigned_lit (2 ^ k)) by lia. change 125613361 with rDB32.
    step. rewrite (mul_srliw27 k) by lia.
    pose proof (rdbi_range k) as DR.
    step. rewrite ?(unsigned_lit (rdbi k)) by lia.
    pose proof (rdebruijn_read m k MI ltac:(lia)) as DBR. unfold RDEBRUIJN in DBR.
    step. rewrite ?zxb_b8 by lia. clear DBR.
    (* [comment removed for export] *)
    step. rewrite (wz_unsigned k), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
    step. rewrite (unsigned_lit (k * 4)), lxor_4k_124 by lia.
    set (i := 4 * k - 4). assert (IR : 8 <= i <= 44) by lia.
    replace (124 - 4 * k) with (120 - i) by lia.
    assert (STQ : stc_q q = (let i1 := if size_class (i + 1) <? x then i + 2 else i in if size_class i1 <? x then i1 + 1 else i1)).
    { unfold stc_q. replace (q <? 10) with false by (symmetry; apply Z.ltb_ge; lia). rewrite <- EX, <- EK. reflexivity. }
    assert (IEV : Z.even i = true) by (subst i; rewrite Z.even_sub, Z.even_mul; reflexivity).
    clearbody i. clear EK.
    pose proof (size_class_range (i + 1) ltac:(lia)) as SR1.
    step. step. rewrite ?(unsigned_lit (120 - i)) by lia. replace (121 + - (120 - i)) with (i + 1) by lia.
    step. rewrite ?(unsigned_lit (i + 1)), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
    step. replace (70188 + (i + 1) * 2) with (70188 + 2 * (i + 1)) by lia.
    pose proof (rsize_classes_read m (i + 1) MI ltac:(lia)) as RS1. unfold RSIZE_CLASSES in RS1.
    step. rewrite ?zx16_wz by lia. clear RS1.
    (* [comment removed for export] *)
    assert (J1 : forall (i1 c : Z),
      i1 = (if size_class (i + 1) <? x then i + 2 else i) -> c = i1 - i + 120 ->
      evt usegs (rrdec_small_post ra sp gp tp t0 s0 s1 a0 a1 (Z_to_bv 64 sc) a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 F fc m (sc <=? size_to_class n + 1))
        (MS (mkR ra sp gp tp t0 (Z_to_bv 64 70156) t2 s0 s1 a0 a1 (Z_to_bv 64 q) (Z_to_bv 64 sc) (Z_to_bv 64 (120 - i)) (Z_to_bv 64 70188) a6 (Z_to_bv 64 c)
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1ac60) fc None m (seg_rom usegs))).
    { intros i1 c Hi1 Hc.
      assert (I1R : 8 <= i1 <= 46 /\ Z.even i1 = true).
      { subst i1. destruct (size_class (i + 1) <? x); (split; [lia|]); rewrite ?Z.even_add, ?IEV; reflexivity. }
      destruct I1R as [I1R I1E].
      pose proof (size_class_range i1 ltac:(lia)) as SR2.
      (* [comment removed for export] *)
      step. rewrite ?(unsigned_lit c), ?(unsigned_lit (120 - i)) by lia. replace (c + - (120 - i)) with i1 by lia.
      step. rewrite ?(unsigned_lit i1), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
      step. rewrite ?(unsigned_lit i1) by lia. replace (70188 + i1 * 2) with (70188 + 2 * i1) by lia.
      pose proof (rsize_classes_read m i1 MI ltac:(lia)) as RS2. unfold RSIZE_CLASSES in RS2.
      step. rewrite ?zx16_wz by lia. clear RS2.
      (* [comment removed for export] *)
      step. rewrite v_sltu_b2z, (unsigned_lit q), (wz_unsigned (size_class i1)) by lia.
      step. step.
      destruct (Z.ltb_spec q (size_class i1)) as [LT|GE]; cbn [Z.b2z].
      * rewrite (unsigned_lit 1), (unsigned_lit i1) by lia. change (Z.lxor 1 1) with 0. rewrite (unsigned_lit 0), Z.lor_0_r by lia.
        apply JOIN. rewrite STC, STQ. cbv zeta. rewrite <- Hi1.
        replace (size_class i1 <? x) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
      * rewrite (unsigned_lit 0), (unsigned_lit i1) by lia. change (Z.lxor 0 1) with 1. rewrite (unsigned_lit 1), (lor_even_1 i1 ltac:(lia) I1E) by lia.
        apply JOIN. rewrite STC, STQ. cbv zeta. rewrite <- Hi1.
        replace (size_class i1 <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
    step. if_cases K3; zify_cond K3; rewrite ?(unsigned_lit q), ?(wz_unsigned (size_class (i + 1))) in K3 by lia.
    + (* [comment removed for export] *)
      step. eapply J1; [reflexivity|]. replace (size_class (i + 1) <? x) with false by (symmetry; apply Z.ltb_ge; lia). lia.
    + (* [comment removed for export] *)
      step. step. eapply J1; [reflexivity|]. replace (size_class (i + 1) <? x) with true by (symmetry; apply Z.ltb_lt; lia). lia.
Qed.
End Sz1.
Lemma rrealloc_stc_walk : ltac:(let t := eval cbv delta [rrealloc_stc_walk__stmt] in rrealloc_stc_walk__stmt in exact t).
Proof using MSECV TLSFACTS. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a4 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n sc. ltac2:(SecDiet.SzSec.closeP 'rrealloc_stc_walk__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rrealloc_dec_small : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a4 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (n sc avail : Z),
  bv_unsigned a1 = n -> 0 <= n < MMAP_THRESHOLD -> n <= avail -> 0 <= avail < 2^64 -> 0 <= sc < 64 -> mem_inv usegs m ->
  evt usegs (rrdec_small_post ra sp gp tp t0 s0 s1 a0 a1 (Z_to_bv 64 sc) a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 F fc m (sc <=? size_to_class n + 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 sc) a4 (Z_to_bv 64 RSIZE_CLASSES) a6 (Z_to_bv 64 avail) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1aae0) fc None m (seg_rom usegs)).
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros until avail. intros HN N LE AV SC MI. unfold MMAP_THRESHOLD in N.
  (* [comment removed for export] *)
  step. step. step. if_cases K1; zify_cond K1. { exfalso. rewrite ?HN, ?unsigned_lit in K1 by lia. lia. }
  step. if_cases K2; zify_cond K2. { exfalso. rewrite ?HN, ?unsigned_lit in K2 by lia. lia. }
  eapply rrealloc_stc_walk; [exact HN| unfold MMAP_THRESHOLD; lia| exact SC| exact MI].
Qed.

(* [comment removed for export] *)
Definition rrdec_big_post (ra sp gp tp t0 t1 s0 s1 a0 a1 a2 a3 a4 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) : machine_state -> Prop :=
  fun ms' => exists t2 a5 t3,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x1ab9c) fc None m (seg_rom usegs).

Definition rrealloc_dec_big__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a4 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (n sc avail : Z),
  bv_unsigned a1 = n -> MMAP_THRESHOLD <= n < 2^64 -> 0 <= avail < 2^64 -> sc = 63 ->
  evt usegs (rrdec_big_post ra sp gp tp t0 t1 s0 s1 a0 a1 a2 (Z_to_bv 64 sc) a4 a6 (Z_to_bv 64 avail) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 sc) a4 (Z_to_bv 64 RSIZE_CLASSES) a6 (Z_to_bv 64 avail) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1aae0) fc None m (seg_rom usegs)).
Section Sz3.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a4 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n sc avail : ltac2:(SecDiet.SzSec.tyM 'rrealloc_dec_big__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rrealloc_dec_big__body : ltac2:(SecDiet.SzSec.bodyP 'rrealloc_dec_big__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
 intros HN N AV SC. unfold MMAP_THRESHOLD in N.
  step. step. step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?HN, ?unsigned_lit in K1 by lia. lia. }
  (* [comment removed for export] *)
  step. step. if_cases K2; zify_cond K2. { exfalso. rewrite ?HN, ?unsigned_lit in K2 by lia. lia. }
  step. step. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by lia. lia. }
  step. step. if_cases K4; zify_cond K4. 2:{ exfalso. rewrite ?unsigned_lit in K4 by lia. lia. }
  unfold rrdec_big_post. apply evt_done. do 3 eexists. reflexivity.
Qed.
End Sz3.
Lemma rrealloc_dec_big : ltac:(let t := eval cbv delta [rrealloc_dec_big__stmt] in rrealloc_dec_big__stmt in exact t).
Proof using MSECV TLSFACTS. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a4 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n sc avail. ltac2:(SecDiet.SzSec.closeP 'rrealloc_dec_big__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
Definition rrealloc_dec_fb__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a4 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (n sc avail : Z),
  bv_unsigned a1 = n -> 0 <= n < 2^64 -> 0 <= avail < 2^64 -> 0 <= sc < 64 -> (48 <= sc -> sc = 63) -> mem_inv usegs m ->
  (n <=? avail) && (n <? MMAP_THRESHOLD) && (sc <=? size_to_class n + 1) = false ->
  (48 <=? sc) && (MMAP_THRESHOLD <=? n) = false ->
  evt usegs (rrdec_small_post ra sp gp tp t0 s0 s1 a0 a1 (Z_to_bv 64 sc) a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 F fc m false)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 sc) a4 (Z_to_bv 64 RSIZE_CLASSES) a6 (Z_to_bv 64 avail) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1aae0) fc None m (seg_rom usegs)).
Section Sz4.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a4 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n sc avail : ltac2:(SecDiet.SzSec.tyM 'rrealloc_dec_fb__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rrealloc_dec_fb__body : ltac2:(SecDiet.SzSec.bodyP 'rrealloc_dec_fb__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
 intros HN N AV SC SC63 MI C1 C2. unfold MMAP_THRESHOLD in *.
  step. step. step. if_cases K1; zify_cond K1; rewrite ?HN, ?unsigned_lit in K1 by lia.
  - (* [comment removed for export] *)
    step. step. if_cases K2; zify_cond K2; rewrite ?HN, ?unsigned_lit in K2 by lia. { exfalso. lia. }
    step. step. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia.
    + unfold rrdec_small_post. apply evt_done. do 8 eexists. reflexivity.
    + exfalso. replace (48 <=? sc) with true in C2 by (symmetry; apply Z.leb_le; lia).
      replace (131052 <=? n) with true in C2 by (symmetry; apply Z.leb_le; lia). discriminate C2.
  - step. if_cases K2; zify_cond K2; rewrite ?HN, ?unsigned_lit in K2 by lia.
    + (* [comment removed for export] *)
      step. step. if_cases K3; zify_cond K3; rewrite ?HN, ?unsigned_lit in K3 by lia. 2:{ exfalso. lia. }
      unfold rrdec_small_post. apply evt_done. do 8 eexists. reflexivity.
    + (* [comment removed for export] *)
      replace (n <=? avail) with true in C1 by (symmetry; apply Z.leb_le; lia).
      replace (n <? 131052) with true in C1 by (symmetry; apply Z.ltb_lt; lia). cbn [andb] in C1.
      replace false with (sc <=? size_to_class n + 1) by exact C1.
      eapply rrealloc_stc_walk; [exact HN| unfold MMAP_THRESHOLD; lia| exact SC| exact MI].
Qed.
End Sz4.
Lemma rrealloc_dec_fb : ltac:(let t := eval cbv delta [rrealloc_dec_fb__stmt] in rrealloc_dec_fb__stmt in exact t).
Proof using MSECV TLSFACTS. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a4 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n sc avail. ltac2:(SecDiet.SzSec.closeP 'rrealloc_dec_fb__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End PORT.

End WithCeil.
End TwB.
End RF_reallocB.

(* [comment removed for export] *)
Module RMallocKit_B2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import TlsBase.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep  Arr ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_enframe.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. Export OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import Malloc_fp.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.


(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Lemma rimplT_guard {R} o t (c : bool) (k bail : Malloc.M R) s Q ms :
  (c = true -> rimplT o k s Q ms) -> rimplT o (guard t c k bail) s Q ms.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts. intros H. unfold guard. destruct c; [apply H; reflexivity| apply rimplT_undef]. Qed.

(* [comment removed for export] *)
Definition peek_agrees (o : mem) (st : mstate) (ms : machine_state) (q : aptr) : Prop :=
  forall h, cell_read (get_shadow st (fst q)) (snd q) = Unknown h ->
    peek_byte ssegs ms (conc st q) = pans_mem o q (conc st q) h.

Lemma peek_agrees_known o st ms q v : cell_read (get_shadow st (fst q)) (snd q) = Known v -> peek_agrees o st ms q.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts. intros E h E'. rewrite E in E'. discriminate. Qed.

Lemma peek_agrees_of_unk o st m q r regs F pc fc rv :
  rmrep st m -> unk_agree st o m ->
  (s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
  ~ grp_hdr_cov st (fst q) (snd q) ->
  peek_agrees o st (MS regs F pc fc rv m (seg_rom ssegs)) q.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros MR UA Hr Hk Ho NC h E. unfold peek_byte, pans_mem. cbn [ms_mem].
  unfold conc, get_region. rewrite Hr.
  destruct MR as (WF & _). destruct WF as (_ & WR & _). destruct (WR _ _ Hr) as (B0 & _ & L0 & BC & RF).
  pose proof (rreserved_disjoint1 _ _ RF) as D. pose proof (round_up_pg_ge (r_len r)).
  assert (HA : 0 <= r_base r + snd q /\ r_base r + snd q + 1 <= 2^64) by (ceil_facts; lia).
  rewrite ref_mrd_overlay by (rewrite wa_unsigned by lia; lia).
  change (ms_mem (MS regs F pc fc rv m (seg_rom ssegs))) with m. rewrite (UA (fst q) r (snd q) h Hr Hk Ho E NC). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma peek_agrees_of_rdv o st m q (x : byte) regs F pc fc rv :
  mrd ssegs m (wa (conc st q)) = Some x -> rdv pans_mem o st q = bv_unsigned x ->
  peek_agrees o st (MS regs F pc fc rv m (seg_rom ssegs)) q.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  intros HM HR h E. unfold peek_byte. change (ms_mem (MS regs F pc fc rv m (seg_rom ssegs))) with m.
  rewrite HM. unfold rdv in HR. rewrite E in HR. symmetry. exact HR.
Qed.

Lemma peek_agrees_of_bytes_at o st m q A bs (i : nat) (x : byte) regs F pc fc rv :
  bytes_at ssegs m A bs -> nth_error bs i = Some x -> conc st q = A + Z.of_nat i ->
  rdv pans_mem o st q = bv_unsigned x ->
  peek_agrees o st (MS regs F pc fc rv m (seg_rom ssegs)) q.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  intros (B0 & B1 & BB) Hi Hc HR. eapply peek_agrees_of_rdv; [| exact HR].
  rewrite Hc. rewrite (BB i). { exact Hi. } apply (proj1 (nth_error_Some bs i)). rewrite Hi. discriminate.
Qed.

Lemma peek_agrees_of_bytes_at_b8 o st m q A bs (i : nat) (v : Z) regs F pc fc rv :
  bytes_at ssegs m A bs -> nth_error bs i = Some (b8 v) -> 0 <= v < 256 -> conc st q = A + Z.of_nat i ->
  rdv pans_mem o st q = v ->
  peek_agrees o st (MS regs F pc fc rv m (seg_rom ssegs)) q.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  intros HB Hi Hv Hc HR. eapply (peek_agrees_of_bytes_at o st m q A bs i (b8 v)); [exact HB| exact Hi| exact Hc|].
  rewrite b8_unsigned by exact Hv. exact HR.
Qed.

Lemma rimplT_rd8 {R} o st q (k : Z -> Malloc.M R) s Q ms :
  peek_agrees o st ms q ->
  rimplT o (k (rdv pans_mem o st q)) s Q ms -> rimplT o (rd8 st q k) s Q ms.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros HA H. unfold rd8. unfold rdv in H.
  destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h] eqn:E; [exact H|].
  apply rimplT_peek_now. rewrite (HA h E). rewrite peek_ok_pans. exact H.
Qed.

Lemma rimplT_rd16 {R} o st q (k : Z -> Malloc.M R) s Q ms :
  peek_agrees o st ms q -> peek_agrees o st ms (aadd q 1) ->
  rimplT o (k (rdv pans_mem o st q + 256 * rdv pans_mem o st (aadd q 1))) s Q ms -> rimplT o (rd16 st q k) s Q ms.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts. intros HA1 HA2 H. unfold rd16. apply rimplT_rd8; [exact HA1|]. apply rimplT_rd8; [exact HA2|]. exact H. Qed.

Lemma rimplT_rd32 {R} o st q (k : Z -> Malloc.M R) s Q ms :
  peek_agrees o st ms q -> peek_agrees o st ms (aadd q 1) -> peek_agrees o st ms (aadd q 2) -> peek_agrees o st ms (aadd q 3) ->
  rimplT o (k (rdv pans_mem o st q + 256 * rdv pans_mem o st (aadd q 1)
             + 65536 * rdv pans_mem o st (aadd q 2) + 16777216 * rdv pans_mem o st (aadd q 3))) s Q ms ->
  rimplT o (rd32 st q k) s Q ms.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros HA1 HA2 HA3 HA4 H. unfold rd32.
  apply rimplT_rd8; [exact HA1|]. apply rimplT_rd8; [exact HA2|]. apply rimplT_rd8; [exact HA3|]. apply rimplT_rd8; [exact HA4|]. exact H.
Qed.

(* [comment removed for export] *)
Lemma rimplT_if {R} o (c : bool) (t1 t2 : Malloc.M R) s Q ms :
  (c = true -> rimplT o t1 s Q ms) -> (c = false -> rimplT o t2 s Q ms) -> rimplT o (if c then t1 else t2) s Q ms.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts. intros H1 H2. destruct c; auto. Qed.

(* [comment removed for export] *)
Lemma rrdv_range : forall o st m q r,
  rmrep st m -> (s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
  0 <= rdv pans_mem o st q < 256.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros o st m q r MR Hr Hk Ho. unfold rdv.
  destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h] eqn:E.
  - exact (proj2 (rmrep_shadow_read st m (fst q) r (snd q) v MR Hr Hk Ho E)).
  - apply pans_mem_range.
Qed.

(* [comment removed for export] *)
Lemma rrdv_cur : forall o st mX q r (x : byte),
  rmrep st mX ->
  (s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
  (forall h, cell_read (get_shadow st (fst q)) (snd q) = Unknown h -> o (wa (r_base r + snd q)) = mX (wa (r_base r + snd q))) ->
  bytes_at ssegs mX (r_base r + snd q) [x] ->
  rdv pans_mem o st q = bv_unsigned x.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros o st mX q r x MR Hr Hk Ho AG Hb. unfold rdv.
  destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h] eqn:E.
  - destruct (rmrep_shadow_read st mX (fst q) r (snd q) v MR Hr Hk Ho E) as [RD Hv].
    pose proof (bytes_at_read ssegs mX _ [x] 0 1 Hb ltac:(lia) ltac:(cbn; lia)) as RD'. cbn [firstn skipn Z.to_nat] in RD'.
    rewrite Z.add_0_r in RD'. rewrite RD in RD'. inversion RD'. rewrite b8_unsigned by lia. reflexivity.
  - unfold pans_mem. rewrite (conc_region' st q r Hr).
    destruct Hb as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn in HB. rewrite Z.add_0_r in HB.
    unfold mrd in HB |- *. rewrite (AG h eq_refl).
    destruct (mX (wa (r_base r + snd q))) as [b|] eqn:EMX; [inversion HB; subst; reflexivity|].
    exfalso. pose proof MR as ((_ & WR & _) & _). destruct (WR _ _ Hr) as (RB0 & _ & _ & RBC & RF). ceil_facts.
    pose proof (rreserved_disjoint1 _ _ RF ltac:(lia)) as D.
    rewrite ref_seg_rom_none in HB; [discriminate|]. rewrite wa_unsigned by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rwview_ext : forall m m' a, m' a = m a -> wview ssegs m' a = wview ssegs m a.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts. intros m m' a E. unfold wview. rewrite E. reflexivity. Qed.

Lemma rwr_at_agree : forall m m' A n, wr_at ssegs m A n -> agree_on m m' A n -> wr_at ssegs m' A n.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros m m' A n (H0 & H1 & HW) AG. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite (rwview_ext m m') by (apply AG; lia). apply HW. exact Hi.
Qed.

Lemma rrw_cells_agree' : forall m m' A cs,
  rw_cells ssegs m A cs -> agree_on m m' A (Z.of_nat (cells_size cs)) -> rw_cells ssegs m' A cs.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros m m' A cs [[Hwf HB] HW] AG. split; [split; [exact Hwf|]|].
  - eapply rbytes_at_agree; [exact HB|]. rewrite cells_bytes_length by assumption. exact AG.
  - eapply rwr_at_agree; eauto.
Qed.

Lemma ru64arr_agree' : forall m m' A ws,
  u64arr ssegs m A ws -> agree_on m m' A (8 * Z.of_nat (length ws)) -> u64arr ssegs m' A ws.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros m m' A ws [HB HW] AG. split.
  - eapply rbytes_at_agree; [exact HB|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact AG.
  - eapply rwr_at_agree; [exact HW|]. exact AG.
Qed.

Lemma ru8arr_agree' : forall m m' A bs,
  u8arr ssegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> u8arr ssegs m' A bs.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts. intros m m' A bs [HB HW] AG. split; [eapply rbytes_at_agree; eauto| eapply rwr_at_agree; eauto]. Qed.

Lemma rstk_agree : forall m m' lo hi, stk ssegs m lo hi -> agree_on m m' lo (hi - lo) -> stk ssegs m' lo hi.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros m m' lo hi (H0 & H1 & HS) AG. split; [exact H0|]. split; [exact H1|].
  intros a Ha. rewrite (rwview_ext m m') by (apply AG; lia). unfold mrd. rewrite (AG a) by lia. apply HS. exact Ha.
Qed.



(* [comment removed for export] *)
Definition rgrp_region_addr (st : mstate) (a : Z) : Prop :=
  exists rid r, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup /\ r_base r <= a < r_base r + round_up_pg (r_len r).

Lemma rmrep_transport_agree : forall st m m',
  rmrep st m ->
  (forall a, 0 <= a < 2^64 -> rrepfoot st a -> m' (wa a) = m (wa a)) ->
  (forall a, 0 <= a < 2^64 -> rgrp_region_addr st a -> wview ssegs m (wa a) <> None -> wview ssegs m' (wa a) <> None) ->
  rmrep st m'.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros st m m' (WF & CX & GL & AR & GR & SH) AG WG.
  pose proof WF as (Hres & WR & DJ & WA & WGr).
  assert (TC : forall A cs, rw_cells ssegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> rrepfoot st a) -> rw_cells ssegs m' A cs).
  { intros A cs H HP. pose proof (rw_cells_bound ssegs m A cs H). eapply rrw_cells_agree'; eauto. intros a Ha. apply AG; [lia| apply HP; exact Ha]. }
  split; [exact WF|]. split; [|split; [|split; [|split]]].
  - destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
    pose proof (u64arr_bound ssegs m _ _ C2) as B2. pose proof (u64arr_bound ssegs m _ _ C3) as B3.
    pose proof (u8arr_bound ssegs m _ _ C4) as B4. pose proof (u8arr_bound ssegs m _ _ C5) as B5.
    rewrite actives_length in B2. rewrite usages_length in B3. rewrite unmap_seqs_length in B4. rewrite bouncess_length in B5.
    split; [|split; [|split; [|split; [|split]]]].
    + apply TC; [exact C1 |]. intros a Ha. apply rrepfoot_ctx. cbn in Ha. unfold RCTX in *. lia.
    + eapply ru64arr_agree'; eauto. rewrite actives_length. intros a Ha. apply AG; [unfold RCTX in *; lia|]. apply rrepfoot_ctx. unfold RCTX in *. lia.
    + eapply ru64arr_agree'; eauto. rewrite usages_length. intros a Ha. apply AG; [unfold RCTX in *; lia|]. apply rrepfoot_ctx. unfold RCTX in *. lia.
    + eapply ru8arr_agree'; eauto. rewrite unmap_seqs_length. intros a Ha. apply AG; [unfold RCTX in *; lia|]. apply rrepfoot_ctx. unfold RCTX in *. lia.
    + eapply ru8arr_agree'; eauto. rewrite bouncess_length. intros a Ha. apply AG; [unfold RCTX in *; lia|]. apply rrepfoot_ctx. unfold RCTX in *. lia.
    + apply TC; [exact C6 |]. intros a Ha. apply rrepfoot_ctx. cbn in Ha. unfold RCTX in *. lia.
  - destruct GL as (G1 & G2 & G3 & G4 & G5). split; [|split; [|split; [|split]]].
    + apply TC; [exact G1 |]. intros a Ha. apply rrepfoot_mlock. cbn in Ha. unfold RMLOCK in *. lia.
    + apply TC; [exact G2 |]. intros a Ha. apply rrepfoot_nl. cbn in Ha. unfold RNEED_LOCKS in *. lia.
    + apply TC; [exact G3 |]. intros a Ha. apply rrepfoot_pgsz. cbn in Ha. unfold RPAGE_SIZE in *. lia.
    + apply TC; [exact G4 |]. intros a Ha. apply rrepfoot_got. cbn in Ha. unfold RGOT_SSP in *. lia.
    + apply TC; [exact G5 |]. intros a Ha. apply rrepfoot_guard. cbn in Ha. unfold RSSP_GUARD in *. lia.
  - intros ak ar Ha. destruct (AR ak ar Ha) as (A1 & A2 & A3).
    split; [|split].
    + apply TC; [exact A1 |]. intros a H. cbn in H. eapply rrepfoot_area; [exact Ha|lia].
    + intros k Hk. apply TC; [apply A2; exact Hk |]. unfold meta_cells; cbn [cells_size csize Nat.add length].
      unfold AREA_HDR, META_SIZE, NSLOTS in *. intros a H. eapply rrepfoot_area; [exact Ha|lia].
    + apply TC; [exact A3 |]. intros a H. cbn in H. eapply rrepfoot_area; [exact Ha|lia].
  - intros b gh Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
    apply TC; [exact R |]. intros a H. cbn in H. eapply rrepfoot_group; [exact Hb|lia].
  - intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB].
    destruct (WR rid r Hr) as (RB0 & _ & _ & RBC & _). ceil_facts.
    split.
    + destruct HWr as (W0 & W1 & HW). split; [exact W0|]. split; [exact W1|].
      intros i Hi. apply WG; [lia| exists rid, r; repeat split; auto; lia| apply HW; exact Hi].
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
      eapply rbytes_at_agree; [exact Bt|]. cbn. intros a Ha. apply AG; [lia|].
      eapply (rrepfoot_known st a rid r v Hr Hk ltac:(lia)). replace (a - r_base r) with o by lia. exact Hc.
Qed.

(* [comment removed for export] *)
Lemma rmrep_transport_agree' : forall st m m',
  rmrep st m ->
  (forall a, 0 <= a < 2^64 -> rrepfoot st a \/ rgrp_region_addr st a -> m' (wa a) = m (wa a)) ->
  rmrep st m'.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros st m m' MR AG. eapply rmrep_transport_agree; [exact MR| |].
  - intros a Ha Hf. apply AG; auto.
  - intros a Ha Hg. rewrite (rwview_ext m m'); [tauto|]. apply AG; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rpres_except_of_munch_nw : forall C W m m',
  munch W m m' -> (forall a, 0 <= a < 2^64 -> ~ C a -> outside W a) -> rpres_except C m m'.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros C W m m' MU HW a Ha Hc.
  assert (E : m' (wa a) = m (wa a)) by (apply MU; rewrite wa_unsigned by lia; apply HW; assumption).
  split; [exact E|]. rewrite (rwview_ext m m' (wa a) E). tauto.
Qed.

Lemma rpres_except_agree : forall C m m' A n,
  rpres_except C m m' -> 0 <= A -> A + n <= 2^64 -> (forall a, A <= a < A + n -> ~ C a) -> agree_on m m' A n.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts. intros C m m' A n HP HA HB HC a Ha. apply (HP a); [lia| apply HC; exact Ha]. Qed.

Lemma ru64arr_pres : forall C m m' A ws,
  rpres_except C m m' -> u64arr ssegs m A ws -> (forall a, A <= a < A + 8 * Z.of_nat (length ws) -> ~ C a) -> u64arr ssegs m' A ws.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros C m m' A ws HP H HC. pose proof (u64arr_bound ssegs m A ws H).
  eapply ru64arr_agree'; [exact H|]. eapply rpres_except_agree; eauto; lia.
Qed.

Lemma ru8arr_pres : forall C m m' A bs,
  rpres_except C m m' -> u8arr ssegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> ~ C a) -> u8arr ssegs m' A bs.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros C m m' A bs HP H HC. pose proof (u8arr_bound ssegs m A bs H).
  eapply ru8arr_agree'; [exact H|]. eapply rpres_except_agree; eauto; lia.
Qed.

End PORT.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.TlsBaseU.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.SFModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_enframe.
Export OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B2.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.Malloc_fp.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MSecret.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.


(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Lemma rimplT_guard {R} o t (c : bool) (k bail : Malloc.M R) s Q ms :
  (c = true -> rimplT o k s Q ms) -> rimplT o (guard t c k bail) s Q ms.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts. intros H. unfold guard. destruct c; [apply H; reflexivity| apply rimplT_undef]. Qed.

(* [comment removed for export] *)
Definition peek_agrees (o : mem) (st : mstate) (ms : machine_state) (q : aptr) : Prop :=
  forall h, cell_read (get_shadow st (fst q)) (snd q) = Unknown h ->
    peek_byte usegs ms (conc st q) = pans_mem o q (conc st q) h.

Lemma peek_agrees_known o st ms q v : cell_read (get_shadow st (fst q)) (snd q) = Known v -> peek_agrees o st ms q.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts. intros E h E'. rewrite E in E'. discriminate. Qed.

Lemma peek_agrees_of_unk o st m q r regs F pc fc rv :
  rmrep st m -> unk_agree st o m ->
  (s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
  ~ grp_hdr_cov st (fst q) (snd q) ->
  peek_agrees o st (MS regs F pc fc rv m (seg_rom usegs)) q.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros MR UA Hr Hk Ho NC h E. unfold peek_byte, pans_mem. cbn [ms_mem].
  unfold conc, get_region. rewrite Hr.
  destruct MR as (WF & _). destruct WF as (_ & WR & _). destruct (WR _ _ Hr) as (B0 & _ & L0 & BC & RF).
  pose proof (rreserved_disjoint1 _ _ RF) as D. pose proof (round_up_pg_ge (r_len r)).
  assert (HA : 0 <= r_base r + snd q /\ r_base r + snd q + 1 <= 2^64) by (ceil_facts; lia).
  rewrite ref_mrd_overlay by (rewrite wa_unsigned by lia; lia).
  change (ms_mem (MS regs F pc fc rv m (seg_rom usegs))) with m. rewrite (UA (fst q) r (snd q) h Hr Hk Ho E NC). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma peek_agrees_of_rdv o st m q (x : byte) regs F pc fc rv :
  mrd usegs m (wa (conc st q)) = Some x -> rdv pans_mem o st q = bv_unsigned x ->
  peek_agrees o st (MS regs F pc fc rv m (seg_rom usegs)) q.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  intros HM HR h E. unfold peek_byte. change (ms_mem (MS regs F pc fc rv m (seg_rom usegs))) with m.
  rewrite HM. unfold rdv in HR. rewrite E in HR. symmetry. exact HR.
Qed.

Lemma peek_agrees_of_bytes_at o st m q A bs (i : nat) (x : byte) regs F pc fc rv :
  bytes_at usegs m A bs -> nth_error bs i = Some x -> conc st q = A + Z.of_nat i ->
  rdv pans_mem o st q = bv_unsigned x ->
  peek_agrees o st (MS regs F pc fc rv m (seg_rom usegs)) q.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  intros (B0 & B1 & BB) Hi Hc HR. eapply peek_agrees_of_rdv; [| exact HR].
  rewrite Hc. rewrite (BB i). { exact Hi. } apply (proj1 (nth_error_Some bs i)). rewrite Hi. discriminate.
Qed.

Lemma peek_agrees_of_bytes_at_b8 o st m q A bs (i : nat) (v : Z) regs F pc fc rv :
  bytes_at usegs m A bs -> nth_error bs i = Some (b8 v) -> 0 <= v < 256 -> conc st q = A + Z.of_nat i ->
  rdv pans_mem o st q = v ->
  peek_agrees o st (MS regs F pc fc rv m (seg_rom usegs)) q.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  intros HB Hi Hv Hc HR. eapply (peek_agrees_of_bytes_at o st m q A bs i (b8 v)); [exact HB| exact Hi| exact Hc|].
  rewrite b8_unsigned by exact Hv. exact HR.
Qed.

Lemma rimplT_rd8 {R} o st q (k : Z -> Malloc.M R) s Q ms :
  peek_agrees o st ms q ->
  rimplT o (k (rdv pans_mem o st q)) s Q ms -> rimplT o (rd8 st q k) s Q ms.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros HA H. unfold rd8. unfold rdv in H.
  destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h] eqn:E; [exact H|].
  apply rimplT_peek_now. rewrite (HA h E). rewrite peek_ok_pans. exact H.
Qed.

Lemma rimplT_rd16 {R} o st q (k : Z -> Malloc.M R) s Q ms :
  peek_agrees o st ms q -> peek_agrees o st ms (aadd q 1) ->
  rimplT o (k (rdv pans_mem o st q + 256 * rdv pans_mem o st (aadd q 1))) s Q ms -> rimplT o (rd16 st q k) s Q ms.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts. intros HA1 HA2 H. unfold rd16. apply rimplT_rd8; [exact HA1|]. apply rimplT_rd8; [exact HA2|]. exact H. Qed.

Lemma rimplT_rd32 {R} o st q (k : Z -> Malloc.M R) s Q ms :
  peek_agrees o st ms q -> peek_agrees o st ms (aadd q 1) -> peek_agrees o st ms (aadd q 2) -> peek_agrees o st ms (aadd q 3) ->
  rimplT o (k (rdv pans_mem o st q + 256 * rdv pans_mem o st (aadd q 1)
             + 65536 * rdv pans_mem o st (aadd q 2) + 16777216 * rdv pans_mem o st (aadd q 3))) s Q ms ->
  rimplT o (rd32 st q k) s Q ms.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros HA1 HA2 HA3 HA4 H. unfold rd32.
  apply rimplT_rd8; [exact HA1|]. apply rimplT_rd8; [exact HA2|]. apply rimplT_rd8; [exact HA3|]. apply rimplT_rd8; [exact HA4|]. exact H.
Qed.

(* [comment removed for export] *)
Lemma rimplT_if {R} o (c : bool) (t1 t2 : Malloc.M R) s Q ms :
  (c = true -> rimplT o t1 s Q ms) -> (c = false -> rimplT o t2 s Q ms) -> rimplT o (if c then t1 else t2) s Q ms.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts. intros H1 H2. destruct c; auto. Qed.

(* [comment removed for export] *)
Lemma rrdv_range : forall o st m q r,
  rmrep st m -> (s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
  0 <= rdv pans_mem o st q < 256.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros o st m q r MR Hr Hk Ho. unfold rdv.
  destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h] eqn:E.
  - exact (proj2 (rmrep_shadow_read st m (fst q) r (snd q) v MR Hr Hk Ho E)).
  - apply pans_mem_range.
Qed.

(* [comment removed for export] *)
Lemma rrdv_cur : forall o st mX q r (x : byte),
  rmrep st mX ->
  (s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
  (forall h, cell_read (get_shadow st (fst q)) (snd q) = Unknown h -> o (wa (r_base r + snd q)) = mX (wa (r_base r + snd q))) ->
  bytes_at usegs mX (r_base r + snd q) [x] ->
  rdv pans_mem o st q = bv_unsigned x.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros o st mX q r x MR Hr Hk Ho AG Hb. unfold rdv.
  destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h] eqn:E.
  - destruct (rmrep_shadow_read st mX (fst q) r (snd q) v MR Hr Hk Ho E) as [RD Hv].
    pose proof (bytes_at_read usegs mX _ [x] 0 1 Hb ltac:(lia) ltac:(cbn; lia)) as RD'. cbn [firstn skipn Z.to_nat] in RD'.
    rewrite Z.add_0_r in RD'. rewrite RD in RD'. inversion RD'. rewrite b8_unsigned by lia. reflexivity.
  - unfold pans_mem. rewrite (conc_region' st q r Hr).
    destruct Hb as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn in HB. rewrite Z.add_0_r in HB.
    unfold mrd in HB |- *. rewrite (AG h eq_refl).
    destruct (mX (wa (r_base r + snd q))) as [b|] eqn:EMX; [inversion HB; subst; reflexivity|].
    exfalso. pose proof MR as ((_ & WR & _) & _). destruct (WR _ _ Hr) as (RB0 & _ & _ & RBC & RF). ceil_facts.
    pose proof (rreserved_disjoint1 _ _ RF ltac:(lia)) as D.
    rewrite ref_seg_rom_none in HB; [discriminate|]. rewrite wa_unsigned by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rwview_ext : forall m m' a, m' a = m a -> wview usegs m' a = wview usegs m a.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts. intros m m' a E. unfold wview. rewrite E. reflexivity. Qed.

Lemma rwr_at_agree : forall m m' A n, wr_at usegs m A n -> agree_on m m' A n -> wr_at usegs m' A n.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros m m' A n (H0 & H1 & HW) AG. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite (rwview_ext m m') by (apply AG; lia). apply HW. exact Hi.
Qed.

Lemma rrw_cells_agree' : forall m m' A cs,
  rw_cells usegs m A cs -> agree_on m m' A (Z.of_nat (cells_size cs)) -> rw_cells usegs m' A cs.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros m m' A cs [[Hwf HB] HW] AG. split; [split; [exact Hwf|]|].
  - eapply rbytes_at_agree; [exact HB|]. rewrite cells_bytes_length by assumption. exact AG.
  - eapply rwr_at_agree; eauto.
Qed.

Lemma ru64arr_agree' : forall m m' A ws,
  u64arr usegs m A ws -> agree_on m m' A (8 * Z.of_nat (length ws)) -> u64arr usegs m' A ws.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros m m' A ws [HB HW] AG. split.
  - eapply rbytes_at_agree; [exact HB|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact AG.
  - eapply rwr_at_agree; [exact HW|]. exact AG.
Qed.

Lemma ru8arr_agree' : forall m m' A bs,
  u8arr usegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> u8arr usegs m' A bs.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts. intros m m' A bs [HB HW] AG. split; [eapply rbytes_at_agree; eauto| eapply rwr_at_agree; eauto]. Qed.

Lemma rstk_agree : forall m m' lo hi, stk usegs m lo hi -> agree_on m m' lo (hi - lo) -> stk usegs m' lo hi.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros m m' lo hi (H0 & H1 & HS) AG. split; [exact H0|]. split; [exact H1|].
  intros a Ha. rewrite (rwview_ext m m') by (apply AG; lia). unfold mrd. rewrite (AG a) by lia. apply HS. exact Ha.
Qed.



(* [comment removed for export] *)
Definition rgrp_region_addr (st : mstate) (a : Z) : Prop :=
  exists rid r, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup /\ r_base r <= a < r_base r + round_up_pg (r_len r).

Lemma rmrep_transport_agree : forall st m m',
  rmrep st m ->
  (forall a, 0 <= a < 2^64 -> rrepfoot st a -> m' (wa a) = m (wa a)) ->
  (forall a, 0 <= a < 2^64 -> rgrp_region_addr st a -> wview usegs m (wa a) <> None -> wview usegs m' (wa a) <> None) ->
  rmrep st m'.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros st m m' (WF & CX & GL & AR & GR & SH) AG WG.
  pose proof WF as (Hres & WR & DJ & WA & WGr).
  assert (TC : forall A cs, rw_cells usegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> rrepfoot st a) -> rw_cells usegs m' A cs).
  { intros A cs H HP. pose proof (rw_cells_bound usegs m A cs H). eapply rrw_cells_agree'; eauto. intros a Ha. apply AG; [lia| apply HP; exact Ha]. }
  split; [exact WF|]. split; [|split; [|split; [|split]]].
  - destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
    pose proof (u64arr_bound usegs m _ _ C2) as B2. pose proof (u64arr_bound usegs m _ _ C3) as B3.
    pose proof (u8arr_bound usegs m _ _ C4) as B4. pose proof (u8arr_bound usegs m _ _ C5) as B5.
    rewrite actives_length in B2. rewrite usages_length in B3. rewrite unmap_seqs_length in B4. rewrite bouncess_length in B5.
    split; [|split; [|split; [|split; [|split]]]].
    + apply TC; [exact C1 |]. intros a Ha. apply rrepfoot_ctx. cbn in Ha. unfold RCTX in *. lia.
    + eapply ru64arr_agree'; eauto. rewrite actives_length. intros a Ha. apply AG; [unfold RCTX in *; lia|]. apply rrepfoot_ctx. unfold RCTX in *. lia.
    + eapply ru64arr_agree'; eauto. rewrite usages_length. intros a Ha. apply AG; [unfold RCTX in *; lia|]. apply rrepfoot_ctx. unfold RCTX in *. lia.
    + eapply ru8arr_agree'; eauto. rewrite unmap_seqs_length. intros a Ha. apply AG; [unfold RCTX in *; lia|]. apply rrepfoot_ctx. unfold RCTX in *. lia.
    + eapply ru8arr_agree'; eauto. rewrite bouncess_length. intros a Ha. apply AG; [unfold RCTX in *; lia|]. apply rrepfoot_ctx. unfold RCTX in *. lia.
    + apply TC; [exact C6 |]. intros a Ha. apply rrepfoot_ctx. cbn in Ha. unfold RCTX in *. lia.
  - destruct GL as (G1 & G2 & G3 & G4 & G5). split; [|split; [|split; [|split]]].
    + apply TC; [exact G1 |]. intros a Ha. apply rrepfoot_mlock. cbn in Ha. unfold RMLOCK in *. lia.
    + apply TC; [exact G2 |]. intros a Ha. apply rrepfoot_nl. cbn in Ha. unfold RNEED_LOCKS in *. lia.
    + apply TC; [exact G3 |]. intros a Ha. apply rrepfoot_pgsz. cbn in Ha. unfold RPAGE_SIZE in *. lia.
    + apply TC; [exact G4 |]. intros a Ha. apply rrepfoot_got. cbn in Ha. unfold RGOT_SSP in *. lia.
    + apply TC; [exact G5 |]. intros a Ha. apply rrepfoot_guard. cbn in Ha. unfold RSSP_GUARD in *. lia.
  - intros ak ar Ha. destruct (AR ak ar Ha) as (A1 & A2 & A3).
    split; [|split].
    + apply TC; [exact A1 |]. intros a H. cbn in H. eapply rrepfoot_area; [exact Ha|lia].
    + intros k Hk. apply TC; [apply A2; exact Hk |]. unfold meta_cells; cbn [cells_size csize Nat.add length].
      unfold AREA_HDR, META_SIZE, NSLOTS in *. intros a H. eapply rrepfoot_area; [exact Ha|lia].
    + apply TC; [exact A3 |]. intros a H. cbn in H. eapply rrepfoot_area; [exact Ha|lia].
  - intros b gh Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
    apply TC; [exact R |]. intros a H. cbn in H. eapply rrepfoot_group; [exact Hb|lia].
  - intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB].
    destruct (WR rid r Hr) as (RB0 & _ & _ & RBC & _). ceil_facts.
    split.
    + destruct HWr as (W0 & W1 & HW). split; [exact W0|]. split; [exact W1|].
      intros i Hi. apply WG; [lia| exists rid, r; repeat split; auto; lia| apply HW; exact Hi].
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
      eapply rbytes_at_agree; [exact Bt|]. cbn. intros a Ha. apply AG; [lia|].
      eapply (rrepfoot_known st a rid r v Hr Hk ltac:(lia)). replace (a - r_base r) with o by lia. exact Hc.
Qed.

(* [comment removed for export] *)
Lemma rmrep_transport_agree' : forall st m m',
  rmrep st m ->
  (forall a, 0 <= a < 2^64 -> rrepfoot st a \/ rgrp_region_addr st a -> m' (wa a) = m (wa a)) ->
  rmrep st m'.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros st m m' MR AG. eapply rmrep_transport_agree; [exact MR| |].
  - intros a Ha Hf. apply AG; auto.
  - intros a Ha Hg. rewrite (rwview_ext m m'); [tauto|]. apply AG; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rpres_except_of_munch_nw : forall C W m m',
  munch W m m' -> (forall a, 0 <= a < 2^64 -> ~ C a -> outside W a) -> rpres_except C m m'.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros C W m m' MU HW a Ha Hc.
  assert (E : m' (wa a) = m (wa a)) by (apply MU; rewrite wa_unsigned by lia; apply HW; assumption).
  split; [exact E|]. rewrite (rwview_ext m m' (wa a) E). tauto.
Qed.

Lemma rpres_except_agree : forall C m m' A n,
  rpres_except C m m' -> 0 <= A -> A + n <= 2^64 -> (forall a, A <= a < A + n -> ~ C a) -> agree_on m m' A n.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts. intros C m m' A n HP HA HB HC a Ha. apply (HP a); [lia| apply HC; exact Ha]. Qed.

Lemma ru64arr_pres : forall C m m' A ws,
  rpres_except C m m' -> u64arr usegs m A ws -> (forall a, A <= a < A + 8 * Z.of_nat (length ws) -> ~ C a) -> u64arr usegs m' A ws.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros C m m' A ws HP H HC. pose proof (u64arr_bound usegs m A ws H).
  eapply ru64arr_agree'; [exact H|]. eapply rpres_except_agree; eauto; lia.
Qed.

Lemma ru8arr_pres : forall C m m' A bs,
  rpres_except C m m' -> u8arr usegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> ~ C a) -> u8arr usegs m' A bs.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros C m m' A bs HP H HC. pose proof (u8arr_bound usegs m A bs H).
  eapply ru8arr_agree'; [exact H|]. eapply rpres_except_agree; eauto; lia.
Qed.

End PORT.

End WithCeil.
End TwB.
End RMallocKit_B2.

(* [comment removed for export] *)
Module RMalloc_iface.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocHINV. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocHINV OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.Malloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.

Definition RMALLOC_SYM : Z := 0x188cc.   (* [comment removed for export] *)
Definition RFREE_SYM : Z := 0x1878c.     (* [comment removed for export] *)
Definition RMALLOC_STACK : Z := 8192.
Definition RFREE_STACK : Z := 8192.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ralloc_static (a : Z) : Prop := RMLOCK <= a < RCTX + 936.
(* [comment removed for export] *)
Definition RMREPLACED : Z := RCTX + 928.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition RHEAPm (st : mstate) (pbrk : Z) (LB : list block) (m : mem) : Prop :=
  exists LB0, Permutation.Permutation LB0 LB /\ rmrep st m
              /\ HINV_from ref_reserved st pbrk LB0
              /\ rw_cells ssegs m RMREPLACED [C4 (Z_to_bv 64 0)].

Definition RHEAP (s : PState) (LB : list block) (m : mem) : Prop := RHEAPm (ps_m s) (ps_brk s) LB m.

Lemma RHEAP_ext : forall s s' LB m, RHEAP s LB m -> ps_m s' = ps_m s -> ps_brk s' = ps_brk s -> RHEAP s' LB m.
Proof using Type. pin_using tt. ceil_facts. msec_facts. intros s s' LB m H E1 E2. unfold RHEAP. rewrite E1, E2. exact H. Qed.

Lemma RHEAP_perm : forall s LB LB' m, RHEAP s LB m -> Permutation.Permutation LB LB' -> RHEAP s LB' m.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros s LB LB' m (LB0 & HP & H2 & H3) P. exists LB0. split; [|auto].
  eapply Permutation.Permutation_trans; [exact HP| exact P].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rclient_addr (LB : list block) (SP : Z) (a : Z) : Prop :=
  SP <= a \/ (0x22000 <= a < 0x55000 /\ ~ ralloc_static a /\ ~ (RERRNO <= a < RERRNO + 4)) \/ in_block LB a
  \/ (the_tb <= a < the_tb + 4096 /\ ~ (RERRNO <= a < RERRNO + 4)).

Definition rheap_pres (LB : list block) (SP : Z) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> rclient_addr LB SP a ->
    m' (wa a) = m (wa a) /\ (wview ssegs m (wa a) <> None -> wview ssegs m' (wa a) <> None).

Lemma rheap_pres_refl : forall LB SP m, rheap_pres LB SP m m.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts. intros LB SP m a _ _. auto. Qed.

Lemma rheap_pres_trans : forall LB SP m1 m2 m3,
  rheap_pres LB SP m1 m2 -> rheap_pres LB SP m2 m3 -> rheap_pres LB SP m1 m3.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros LB SP m1 m2 m3 H1 H2 a Ha Hc. destruct (H1 a Ha Hc) as [E1 W1]. destruct (H2 a Ha Hc) as [E2 W2].
  split; [congruence| auto].
Qed.

Lemma rheap_pres_weaken : forall LB LB' SP SP' m m',
  rheap_pres LB SP m m' -> SP <= SP' -> (forall b, In b LB' -> In b LB) -> rheap_pres LB' SP' m m'.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros LB LB' SP SP' m m' H HS HL a Ha Hc. apply H; [exact Ha|].
  destruct Hc as [Hc|[Hc|[(b & Hb & Hr)|Hc]]]; [left; lia| right; left; exact Hc| right; right; left| right; right; right; exact Hc].
  exists b. split; [apply HL; exact Hb| exact Hr].
Qed.

(* [comment removed for export] *)
Definition rclient_range (LB : list block) (SP : Z) (A n : Z) : Prop :=
  SP <= A
  \/ (0x22000 <= A /\ A + n <= 0x55000 /\ (A + n <= RMLOCK \/ RCTX + 936 <= A) /\ (A + n <= RERRNO \/ RERRNO + 4 <= A))
  \/ (exists b, In b LB /\ blk_addr b <= A /\ A + n <= blk_addr b + blk_size b)
  \/ (the_tb <= A /\ A + n <= the_tb + 4096 /\ (A + n <= RERRNO \/ RERRNO + 4 <= A)).

Lemma rclient_range_addr : forall LB SP A n a,
  rclient_range LB SP A n -> A <= a < A + n -> rclient_addr LB SP a.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros LB SP A n a HR Ha. unfold rclient_range, rclient_addr, ralloc_static, RMLOCK, RCTX in *.
  destruct HR as [H|[H|[(b & Hb & H1 & H2)|H]]]; [left; lia| right; left; lia| right; right; left; exists b; split; [exact Hb|lia]| right; right; right; lia].
Qed.

Lemma rheap_pres_bytes_at : forall LB SP m m' A bs,
  rheap_pres LB SP m m' -> bytes_at ssegs m A bs -> rclient_range LB SP A (Z.of_nat (length bs)) ->
  bytes_at ssegs m' A bs.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros LB SP m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(eapply rclient_range_addr; [exact HR|lia])) as [E _].
  rewrite E. reflexivity.
Qed.

Lemma rheap_pres_wr_at : forall LB SP m m' A n,
  rheap_pres LB SP m m' -> wr_at ssegs m A n -> rclient_range LB SP A n -> wr_at ssegs m' A n.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros LB SP m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(eapply rclient_range_addr; [exact HR|lia])) as [_ W].
  apply W. apply HW. exact Hi.
Qed.

Lemma rheap_pres_rw_cells : forall LB SP m m' A cs,
  rheap_pres LB SP m m' -> rw_cells ssegs m A cs -> rclient_range LB SP A (Z.of_nat (cells_size cs)) ->
  rw_cells ssegs m' A cs.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros LB SP m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply rheap_pres_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply rheap_pres_wr_at; eauto.
Qed.

Lemma rheap_pres_u8arr : forall LB SP m m' A xs,
  rheap_pres LB SP m m' -> u8arr ssegs m A xs -> rclient_range LB SP A (Z.of_nat (length xs)) ->
  u8arr ssegs m' A xs.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros LB SP m m' A xs HP H HR. apply (u8arr_of_rw_cells ssegs m' A (length xs)).
  eapply rheap_pres_rw_cells; [exact HP| apply rw_cells_of_u8arr; exact H|].
  cbn [cells_size csize]. rewrite Nat.add_0_r. exact HR.
Qed.

Lemma rheap_pres_stk : forall LB SP m m' lo hi,
  rheap_pres LB SP m m' -> stk ssegs m lo hi -> SP <= lo -> stk ssegs m' lo hi.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros LB SP m m' lo hi HP ST HS. destruct ST as (H0 & H1 & HW). split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP i ltac:(lia) ltac:(left; lia)) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
  split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rblock_range (A n : Z) : Prop :=
  0 < A /\ A mod 16 = 0 /\ 0 <= n /\ A + n <= alloc_ceiling /\ (A + n <= 0x10000 \/ 0x55000 <= A)
  /\ (A + n <= the_tb \/ the_tb + 4096 <= A).

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition rclient_write_ok (LB : list block) (iv : Z * Z) : Prop :=
  alloc_ceiling <= fst iv
  \/ (0x22000 <= fst iv /\ snd iv <= 0x55000 /\ (snd iv <= RLIBC \/ RCTX + 936 <= fst iv)
      /\ (snd iv <= RSSP_GUARD \/ RSSP_GUARD + 8 <= fst iv) /\ (snd iv <= RGOT_SSP \/ RGOT_SSP + 8 <= fst iv))
  \/ (exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)
  \/ (the_tb <= fst iv /\ snd iv <= the_tb + 4096).
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rmalloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (n lo B : Z) (m : mem)
    (r : option aptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp)
    /\ rw_cells ssegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' B
    /\ rheap_pres LB (bv_unsigned sp) m m'
    /\ ps_rest s' = ps_rest s
    /\ match r with
       | None => a0 = Z_to_bv 64 0 /\ errv' = Z_to_bv 64 ENOMEM /\ RHEAP s' LB m'
       | Some pf => exists (c : cptr) (off : Z) A junk,
           pf = aadd c (UNIT * off)
           /\ a0 = Z_to_bv 64 A /\ A = conc (ps_m s') pf /\ rblock_range A n
           /\ RHEAP s' (((c, off), A, n) :: LB) m'
           /\ rw_cells ssegs m' A [CB (Z.to_nat n) junk]
       end.

Definition rmalloc_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (n lo B : Z) (errv : word),
  RHEAP s LB m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk ssegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RMALLOC_STACK ->
  rw_cells ssegs m (errno_addr tp) [C4 errv] ->
  mem_inv ssegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  implM ssegs (raw_mallocF peekG n) s
        (rmalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RMALLOC_SYM) fc None m (seg_rom ssegs)).

Definition rfree_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (p : bptr) (lo B : Z) (errv : word) (m : mem)
    (r : unit) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp)
    /\ rw_cells ssegs m' (errno_addr tp) [C4 errv]          (* [comment removed for export] *)
    /\ rauxv_ok m' B
    /\ rheap_pres (lb_remove p LB) (bv_unsigned sp) m m'
    /\ ps_rest s' = ps_rest s
    /\ RHEAP s' (lb_remove p LB) m'.

Definition rfree_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word),
  RHEAP s LB m -> In (p, A, n) LB ->     (* [comment removed for export] *)
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk ssegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RFREE_STACK ->
  rw_cells ssegs m (errno_addr tp) [C4 errv] ->
  mem_inv ssegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 A ->
  implM ssegs (raw_freeF peekG (aadd (fst p) (UNIT * snd p))) s
        (rfree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B errv m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RFREE_SYM) fc None m (seg_rom ssegs)).

(* [comment removed for export] *)
Definition rfree_null_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  a0 = Z_to_bv 64 0 ->
  evt ssegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m (seg_rom ssegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RFREE_SYM) fc None m (seg_rom ssegs)).

Lemma rfree_null_spec : rfree_null_stmt.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  intros until m. intros ->. unfold RFREE_SYM.
  step. step. if_true. step. apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rheap_init_mem (m : mem) : Prop :=   (* [comment removed for export] *)
  rw_cells ssegs m RMLOCK [C4 (Z_to_bv 64 0)]
  /\ bytes_at ssegs m RCTX (repeat (Z_to_bv 8 0) 928) /\ wr_at ssegs m RCTX 928
  /\ rw_cells ssegs m RNEED_LOCKS [C1 (Z_to_bv 8 0)]
  /\ rw_cells ssegs m RPAGE_SIZE [C8 (Z_to_bv 64 4096)]
  /\ rw_cells ssegs m RGOT_SSP [C8 (Z_to_bv 64 RSSP_GUARD)]
  /\ rw_cells ssegs m RSSP_GUARD [C8 mcanary]
  /\ rw_cells ssegs m RMREPLACED [C4 (Z_to_bv 64 0)].

Definition RHEAP_init_stmt : Prop :=
  forall (s : PState) (m : mem),
    ps_m s = minit msecret ref_reserved -> ps_brk s = 0 -> rheap_init_mem m -> RHEAP s [] m.

(* [comment removed for export] *)
Definition RHEAP_frame_stmt : Prop :=
  forall s LB m m' W,
    RHEAP s LB m -> munch W m m' -> wmono ssegs m m' -> Forall (rclient_write_ok LB) W -> RHEAP s LB m'.

(* [comment removed for export] *)
Definition RHEAP_block_range_stmt : Prop :=
  forall s LB m p A n, RHEAP s LB m -> In (p, A, n) LB -> rblock_range A n /\ A = conc (ps_m s) (aadd (fst p) (UNIT * snd p)).
Definition RHEAP_blocks_disjoint_stmt : Prop :=
  forall s LB m b1 b2, RHEAP s LB m -> In b1 LB -> In b2 LB -> blk_id b1 <> blk_id b2 ->
    blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1.
Definition RHEAP_blocks_nodup_stmt : Prop :=
  forall s LB m, RHEAP s LB m -> List.NoDup (map blk_id LB).

End PORT.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Consumer.
Context {PState : Type} {AS : AllocSt PState}.

(* [comment removed for export] *)
Definition TBu (utp : Z) (H : tls_ok (utp - 200)) : TlsBase := {| the_tb := utp - 200 ; the_tb_ok := H |}.

Definition RHEAPu (s : PState) (utp : Z) (LB : list block) (m : mem) : Prop :=
  exists H : tls_ok (utp - 200), RHEAP (PState:=PState) (AS:=AS) (TB:=TBu utp H) s LB m.

Definition rheap_presu (utp : Z) (LB : list block) (SP : Z) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 ->
    (SP <= a \/ (0x22000 <= a < 0x55000 /\ ~ (RMLOCK <= a < RCTX + 936) /\ ~ (utp - 164 <= a < utp - 160)) \/ in_block LB a
     \/ (utp - 200 <= a < utp - 200 + 4096 /\ ~ (utp - 164 <= a < utp - 160))) ->
    m' (wa a) = m (wa a) /\ (wview ssegs m (wa a) <> None -> wview ssegs m' (wa a) <> None).

Lemma rheap_pres_u : forall utp (H : tls_ok (utp - 200)) LB SP m m',
  @rheap_pres (TBu utp H) LB SP m m' <-> rheap_presu utp LB SP m m'.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros utp H LB SP m m'. unfold rheap_pres, rheap_presu, rclient_addr, ralloc_static. cbn [the_tb TBu].
  split; intros X a Ha Hc; apply X; [exact Ha| |exact Ha|]; (destruct Hc as [?|[?|[?|?]]]; [tauto|right; left; lia|tauto|right; right; right; lia]).
Qed.

Definition rblock_rangeu (utp A n : Z) : Prop :=
  0 < A /\ A mod 16 = 0 /\ 0 <= n /\ A + n <= alloc_ceiling /\ (A + n <= 0x10000 \/ 0x55000 <= A)
  /\ (A + n <= utp - 200 \/ utp - 200 + 4096 <= A).

Definition rmalloc_postu (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (n lo B : Z) (m : mem)
    (r : option aptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp)
    /\ rw_cells ssegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' B
    /\ rheap_presu (bv_unsigned tp) LB (bv_unsigned sp) m m'
    /\ ps_rest s' = ps_rest s
    /\ match r with
       | None => a0 = Z_to_bv 64 0 /\ errv' = Z_to_bv 64 ENOMEM /\ RHEAPu s' (bv_unsigned tp) LB m'
       | Some pf => exists (c : cptr) (off : Z) A junk,
           pf = aadd c (UNIT * off)
           /\ a0 = Z_to_bv 64 A /\ A = conc (ps_m s') pf /\ rblock_rangeu (bv_unsigned tp) A n
           /\ RHEAPu s' (bv_unsigned tp) (((c, off), A, n) :: LB) m'
           /\ rw_cells ssegs m' A [CB (Z.to_nat n) junk]
       end.

Definition rmalloc_stmt_u : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (n lo B : Z) (errv : word),
  RHEAPu s (bv_unsigned tp) LB m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk ssegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RMALLOC_STACK ->
  rw_cells ssegs m (errno_addr tp) [C4 errv] ->
  mem_inv ssegs m ->
  a0 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  implM ssegs (raw_mallocF peekG n) s
        (rmalloc_postu ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RMALLOC_SYM) fc None m (seg_rom ssegs)).

Definition rfree_postu (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (p : bptr) (lo B : Z) (errv : word) (m : mem)
    (r : unit) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp)
    /\ rw_cells ssegs m' (errno_addr tp) [C4 errv]
    /\ rauxv_ok m' B
    /\ rheap_presu (bv_unsigned tp) (lb_remove p LB) (bv_unsigned sp) m m'
    /\ ps_rest s' = ps_rest s
    /\ RHEAPu s' (bv_unsigned tp) (lb_remove p LB) m'.

Definition rfree_stmt_u : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word),
  RHEAPu s (bv_unsigned tp) LB m -> In (p, A, n) LB ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk ssegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RFREE_STACK ->
  rw_cells ssegs m (errno_addr tp) [C4 errv] ->
  mem_inv ssegs m ->
  a0 = Z_to_bv 64 A ->
  implM ssegs (raw_freeF peekG (aadd (fst p) (UNIT * snd p))) s
        (rfree_postu ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B errv m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RFREE_SYM) fc None m (seg_rom ssegs)).

Lemma rfree_stmt_of_class : (forall TB : TlsBase, rfree_stmt (PState:=PState) (AS:=AS) (TB:=TB)) -> rfree_stmt_u.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros HM. intros until errv. intros (H & HP) HIN AUX HB ST CLO LO ERR MI Ha0.
  assert (TP : tp = Z_to_bv 64 (@the_tb _ (TBu (bv_unsigned tp) H) + 200)).
  { cbn [the_tb TBu]. replace (bv_unsigned tp - 200 + 200) with (bv_unsigned tp) by lia. symmetry. apply Z_to_bv_bv_unsigned. }
  eapply implM_mono; [exact (HM (TBu (bv_unsigned tp) H) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                                F fc m s LB p A n lo B errv HP HIN AUX HB ST CLO LO ERR MI TP Ha0)|].
  intros r s' ms' PO. cbn beta in PO |- *. unfold rfree_post in PO. unfold rfree_postu.
  destruct PO as (u0&u1&u2&b0&b1&b2&b3&b4&b5&b6&b7&u3&u4&u5&u6&m'&E&MI'&ST'&ERR'&AUX'&PR&RST&HP').
  exists u0,u1,u2,b0,b1,b2,b3,b4,b5,b6,b7,u3,u4,u5,u6,m'.
  split; [exact E|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|].
  split; [apply (proj1 (rheap_pres_u _ H _ _ _ _)); exact PR|]. split; [exact RST|]. exists H; exact HP'.
Qed.

(* [comment removed for export] *)
Lemma rmalloc_stmt_of_class : (forall TB : TlsBase, rmalloc_stmt (PState:=PState) (AS:=AS) (TB:=TB)) -> rmalloc_stmt_u.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros HM. intros until errv. intros (H & HP) AUX HB ST CLO LO ERR MI Ha0 Hn.
  assert (TP : tp = Z_to_bv 64 (@the_tb _ (TBu (bv_unsigned tp) H) + 200)).
  { cbn [the_tb TBu]. replace (bv_unsigned tp - 200 + 200) with (bv_unsigned tp) by lia. symmetry. apply Z_to_bv_bv_unsigned. }
  eapply implM_mono; [exact (HM (TBu (bv_unsigned tp) H) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                                F fc m s LB n lo B errv HP AUX HB ST CLO LO ERR MI TP Ha0 Hn)|].
  intros r s' ms' PO. cbn beta in PO |- *. unfold rmalloc_post in PO. unfold rmalloc_postu.
  destruct PO as (u0&u1&u2&b0&b1&b2&b3&b4&b5&b6&b7&u3&u4&u5&u6&m'&errv'&E&MI'&ST'&ERR'&AUX'&PR&RST&RES).
  exists u0,u1,u2,b0,b1,b2,b3,b4,b5,b6,b7,u3,u4,u5,u6,m',errv'.
  split; [exact E|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|].
  split; [apply (proj1 (rheap_pres_u _ H _ _ _ _)); exact PR|]. split; [exact RST|].
  destruct r as [pf|].
  - destruct RES as (c & off & A & junk & Epf & EA & EC & BR & HP' & CH). exists c, off, A, junk.
    split; [exact Epf|]. split; [exact EA|]. split; [exact EC|]. split; [exact BR|]. split; [exists H; exact HP'| exact CH].
  - destruct RES as (EA & EEN & HP'). split; [exact EA|]. split; [exact EEN|]. exists H; exact HP'.
Qed.

End Consumer.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.SFModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocHINV OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.Malloc_iface.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MSecret.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.

Definition RMALLOC_SYM : Z := 0x1908c.   (* [comment removed for export] *)
Definition RFREE_SYM : Z := 0x18f4c.     (* [comment removed for export] *)
Definition RMALLOC_STACK : Z := 8192.
Definition RFREE_STACK : Z := 8192.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ralloc_static (a : Z) : Prop := RMLOCK <= a < RCTX + 936.
(* [comment removed for export] *)
Definition RMREPLACED : Z := RCTX + 928.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition RHEAPm (st : mstate) (pbrk : Z) (LB : list block) (m : mem) : Prop :=
  exists LB0, Permutation.Permutation LB0 LB /\ rmrep st m
              /\ HINV_from ref_reserved st pbrk LB0
              /\ rw_cells usegs m RMREPLACED [C4 (Z_to_bv 64 0)].

Definition RHEAP (s : PState) (LB : list block) (m : mem) : Prop := RHEAPm (ps_m s) (ps_brk s) LB m.

Lemma RHEAP_ext : forall s s' LB m, RHEAP s LB m -> ps_m s' = ps_m s -> ps_brk s' = ps_brk s -> RHEAP s' LB m.
Proof using Type. pin_using tt. ceil_facts. msec_facts. intros s s' LB m H E1 E2. unfold RHEAP. rewrite E1, E2. exact H. Qed.

Lemma RHEAP_perm : forall s LB LB' m, RHEAP s LB m -> Permutation.Permutation LB LB' -> RHEAP s LB' m.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros s LB LB' m (LB0 & HP & H2 & H3) P. exists LB0. split; [|auto].
  eapply Permutation.Permutation_trans; [exact HP| exact P].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rclient_addr (LB : list block) (SP : Z) (a : Z) : Prop :=
  SP <= a \/ (0x22000 <= a < 0x56000 /\ ~ ralloc_static a /\ ~ (RERRNO <= a < RERRNO + 4)) \/ in_block LB a
  \/ (the_tb <= a < the_tb + 4096 /\ ~ (RERRNO <= a < RERRNO + 4)).

Definition rheap_pres (LB : list block) (SP : Z) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> rclient_addr LB SP a ->
    m' (wa a) = m (wa a) /\ (wview usegs m (wa a) <> None -> wview usegs m' (wa a) <> None).

Lemma rheap_pres_refl : forall LB SP m, rheap_pres LB SP m m.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts. intros LB SP m a _ _. auto. Qed.

Lemma rheap_pres_trans : forall LB SP m1 m2 m3,
  rheap_pres LB SP m1 m2 -> rheap_pres LB SP m2 m3 -> rheap_pres LB SP m1 m3.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros LB SP m1 m2 m3 H1 H2 a Ha Hc. destruct (H1 a Ha Hc) as [E1 W1]. destruct (H2 a Ha Hc) as [E2 W2].
  split; [congruence| auto].
Qed.

Lemma rheap_pres_weaken : forall LB LB' SP SP' m m',
  rheap_pres LB SP m m' -> SP <= SP' -> (forall b, In b LB' -> In b LB) -> rheap_pres LB' SP' m m'.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros LB LB' SP SP' m m' H HS HL a Ha Hc. apply H; [exact Ha|].
  destruct Hc as [Hc|[Hc|[(b & Hb & Hr)|Hc]]]; [left; lia| right; left; exact Hc| right; right; left| right; right; right; exact Hc].
  exists b. split; [apply HL; exact Hb| exact Hr].
Qed.

(* [comment removed for export] *)
Definition rclient_range (LB : list block) (SP : Z) (A n : Z) : Prop :=
  SP <= A
  \/ (0x22000 <= A /\ A + n <= 0x56000 /\ (A + n <= RMLOCK \/ RCTX + 936 <= A) /\ (A + n <= RERRNO \/ RERRNO + 4 <= A))
  \/ (exists b, In b LB /\ blk_addr b <= A /\ A + n <= blk_addr b + blk_size b)
  \/ (the_tb <= A /\ A + n <= the_tb + 4096 /\ (A + n <= RERRNO \/ RERRNO + 4 <= A)).

Lemma rclient_range_addr : forall LB SP A n a,
  rclient_range LB SP A n -> A <= a < A + n -> rclient_addr LB SP a.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros LB SP A n a HR Ha. unfold rclient_range, rclient_addr, ralloc_static, RMLOCK, RCTX in *.
  destruct HR as [H|[H|[(b & Hb & H1 & H2)|H]]]; [left; lia| right; left; lia| right; right; left; exists b; split; [exact Hb|lia]| right; right; right; lia].
Qed.

Lemma rheap_pres_bytes_at : forall LB SP m m' A bs,
  rheap_pres LB SP m m' -> bytes_at usegs m A bs -> rclient_range LB SP A (Z.of_nat (length bs)) ->
  bytes_at usegs m' A bs.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros LB SP m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(eapply rclient_range_addr; [exact HR|lia])) as [E _].
  rewrite E. reflexivity.
Qed.

Lemma rheap_pres_wr_at : forall LB SP m m' A n,
  rheap_pres LB SP m m' -> wr_at usegs m A n -> rclient_range LB SP A n -> wr_at usegs m' A n.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros LB SP m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(eapply rclient_range_addr; [exact HR|lia])) as [_ W].
  apply W. apply HW. exact Hi.
Qed.

Lemma rheap_pres_rw_cells : forall LB SP m m' A cs,
  rheap_pres LB SP m m' -> rw_cells usegs m A cs -> rclient_range LB SP A (Z.of_nat (cells_size cs)) ->
  rw_cells usegs m' A cs.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros LB SP m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply rheap_pres_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply rheap_pres_wr_at; eauto.
Qed.

Lemma rheap_pres_u8arr : forall LB SP m m' A xs,
  rheap_pres LB SP m m' -> u8arr usegs m A xs -> rclient_range LB SP A (Z.of_nat (length xs)) ->
  u8arr usegs m' A xs.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros LB SP m m' A xs HP H HR. apply (u8arr_of_rw_cells usegs m' A (length xs)).
  eapply rheap_pres_rw_cells; [exact HP| apply rw_cells_of_u8arr; exact H|].
  cbn [cells_size csize]. rewrite Nat.add_0_r. exact HR.
Qed.

Lemma rheap_pres_stk : forall LB SP m m' lo hi,
  rheap_pres LB SP m m' -> stk usegs m lo hi -> SP <= lo -> stk usegs m' lo hi.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros LB SP m m' lo hi HP ST HS. destruct ST as (H0 & H1 & HW). split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP i ltac:(lia) ltac:(left; lia)) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
  split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rblock_range (A n : Z) : Prop :=
  0 < A /\ A mod 16 = 0 /\ 0 <= n /\ A + n <= alloc_ceiling /\ (A + n <= 0x10000 \/ 0x56000 <= A)
  /\ (A + n <= the_tb \/ the_tb + 4096 <= A).

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition rclient_write_ok (LB : list block) (iv : Z * Z) : Prop :=
  alloc_ceiling <= fst iv
  \/ (0x22000 <= fst iv /\ snd iv <= 0x56000 /\ (snd iv <= RLIBC \/ RCTX + 936 <= fst iv)
      /\ (snd iv <= RSSP_GUARD \/ RSSP_GUARD + 8 <= fst iv) /\ (snd iv <= RGOT_SSP \/ RGOT_SSP + 8 <= fst iv))
  \/ (exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)
  \/ (the_tb <= fst iv /\ snd iv <= the_tb + 4096).
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rmalloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (n lo B : Z) (m : mem)
    (r : option aptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' B
    /\ rheap_pres LB (bv_unsigned sp) m m'
    /\ ps_rest s' = ps_rest s
    /\ match r with
       | None => a0 = Z_to_bv 64 0 /\ errv' = Z_to_bv 64 ENOMEM /\ RHEAP s' LB m'
       | Some pf => exists (c : cptr) (off : Z) A junk,
           pf = aadd c (UNIT * off)
           /\ a0 = Z_to_bv 64 A /\ A = conc (ps_m s') pf /\ rblock_range A n
           /\ RHEAP s' (((c, off), A, n) :: LB) m'
           /\ rw_cells usegs m' A [CB (Z.to_nat n) junk]
       end.

Definition rmalloc_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (n lo B : Z) (errv : word),
  RHEAP s LB m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RMALLOC_STACK ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  implM usegs (raw_mallocF peekG n) s
        (rmalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RMALLOC_SYM) fc None m (seg_rom usegs)).

Definition rfree_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (p : bptr) (lo B : Z) (errv : word) (m : mem)
    (r : unit) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 errv]          (* [comment removed for export] *)
    /\ rauxv_ok m' B
    /\ rheap_pres (lb_remove p LB) (bv_unsigned sp) m m'
    /\ ps_rest s' = ps_rest s
    /\ RHEAP s' (lb_remove p LB) m'.

Definition rfree_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word),
  RHEAP s LB m -> In (p, A, n) LB ->     (* [comment removed for export] *)
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RFREE_STACK ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 A ->
  implM usegs (raw_freeF peekG (aadd (fst p) (UNIT * snd p))) s
        (rfree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B errv m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RFREE_SYM) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
Definition rfree_null_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  a0 = Z_to_bv 64 0 ->
  evt usegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m (seg_rom usegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RFREE_SYM) fc None m (seg_rom usegs)).

Lemma rfree_null_spec : rfree_null_stmt.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  intros until m. intros ->. unfold RFREE_SYM.
  step. step. if_true. step. apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rheap_init_mem (m : mem) : Prop :=   (* [comment removed for export] *)
  rw_cells usegs m RMLOCK [C4 (Z_to_bv 64 0)]
  /\ bytes_at usegs m RCTX (repeat (Z_to_bv 8 0) 928) /\ wr_at usegs m RCTX 928
  /\ rw_cells usegs m RNEED_LOCKS [C1 (Z_to_bv 8 0)]
  /\ rw_cells usegs m RPAGE_SIZE [C8 (Z_to_bv 64 4096)]
  /\ rw_cells usegs m RGOT_SSP [C8 (Z_to_bv 64 RSSP_GUARD)]
  /\ rw_cells usegs m RSSP_GUARD [C8 mcanary]
  /\ rw_cells usegs m RMREPLACED [C4 (Z_to_bv 64 0)].

Definition RHEAP_init_stmt : Prop :=
  forall (s : PState) (m : mem),
    ps_m s = minit msecret ref_reserved -> ps_brk s = 0 -> rheap_init_mem m -> RHEAP s [] m.

(* [comment removed for export] *)
Definition RHEAP_frame_stmt : Prop :=
  forall s LB m m' W,
    RHEAP s LB m -> munch W m m' -> wmono usegs m m' -> Forall (rclient_write_ok LB) W -> RHEAP s LB m'.

(* [comment removed for export] *)
Definition RHEAP_block_range_stmt : Prop :=
  forall s LB m p A n, RHEAP s LB m -> In (p, A, n) LB -> rblock_range A n /\ A = conc (ps_m s) (aadd (fst p) (UNIT * snd p)).
Definition RHEAP_blocks_disjoint_stmt : Prop :=
  forall s LB m b1 b2, RHEAP s LB m -> In b1 LB -> In b2 LB -> blk_id b1 <> blk_id b2 ->
    blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1.
Definition RHEAP_blocks_nodup_stmt : Prop :=
  forall s LB m, RHEAP s LB m -> List.NoDup (map blk_id LB).

End PORT.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Consumer.
Context {PState : Type} {AS : AllocSt PState}.

(* [comment removed for export] *)
Definition TBu (utp : Z) (H : tls_ok (utp - 200)) : TlsBase := {| the_tb := utp - 200 ; the_tb_ok := H |}.

Definition RHEAPu (s : PState) (utp : Z) (LB : list block) (m : mem) : Prop :=
  exists H : tls_ok (utp - 200), RHEAP (PState:=PState) (AS:=AS) (TB:=TBu utp H) s LB m.

Definition rheap_presu (utp : Z) (LB : list block) (SP : Z) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 ->
    (SP <= a \/ (0x22000 <= a < 0x56000 /\ ~ (RMLOCK <= a < RCTX + 936) /\ ~ (utp - 164 <= a < utp - 160)) \/ in_block LB a
     \/ (utp - 200 <= a < utp - 200 + 4096 /\ ~ (utp - 164 <= a < utp - 160))) ->
    m' (wa a) = m (wa a) /\ (wview usegs m (wa a) <> None -> wview usegs m' (wa a) <> None).

Lemma rheap_pres_u : forall utp (H : tls_ok (utp - 200)) LB SP m m',
  @rheap_pres (TBu utp H) LB SP m m' <-> rheap_presu utp LB SP m m'.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros utp H LB SP m m'. unfold rheap_pres, rheap_presu, rclient_addr, ralloc_static. cbn [the_tb TBu].
  split; intros X a Ha Hc; apply X; [exact Ha| |exact Ha|]; (destruct Hc as [?|[?|[?|?]]]; [tauto|right; left; lia|tauto|right; right; right; lia]).
Qed.

Definition rblock_rangeu (utp A n : Z) : Prop :=
  0 < A /\ A mod 16 = 0 /\ 0 <= n /\ A + n <= alloc_ceiling /\ (A + n <= 0x10000 \/ 0x56000 <= A)
  /\ (A + n <= utp - 200 \/ utp - 200 + 4096 <= A).

Definition rmalloc_postu (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (n lo B : Z) (m : mem)
    (r : option aptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' B
    /\ rheap_presu (bv_unsigned tp) LB (bv_unsigned sp) m m'
    /\ ps_rest s' = ps_rest s
    /\ match r with
       | None => a0 = Z_to_bv 64 0 /\ errv' = Z_to_bv 64 ENOMEM /\ RHEAPu s' (bv_unsigned tp) LB m'
       | Some pf => exists (c : cptr) (off : Z) A junk,
           pf = aadd c (UNIT * off)
           /\ a0 = Z_to_bv 64 A /\ A = conc (ps_m s') pf /\ rblock_rangeu (bv_unsigned tp) A n
           /\ RHEAPu s' (bv_unsigned tp) (((c, off), A, n) :: LB) m'
           /\ rw_cells usegs m' A [CB (Z.to_nat n) junk]
       end.

Definition rmalloc_stmt_u : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (n lo B : Z) (errv : word),
  RHEAPu s (bv_unsigned tp) LB m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RMALLOC_STACK ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  implM usegs (raw_mallocF peekG n) s
        (rmalloc_postu ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RMALLOC_SYM) fc None m (seg_rom usegs)).

Definition rfree_postu (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (p : bptr) (lo B : Z) (errv : word) (m : mem)
    (r : unit) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 errv]
    /\ rauxv_ok m' B
    /\ rheap_presu (bv_unsigned tp) (lb_remove p LB) (bv_unsigned sp) m m'
    /\ ps_rest s' = ps_rest s
    /\ RHEAPu s' (bv_unsigned tp) (lb_remove p LB) m'.

Definition rfree_stmt_u : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word),
  RHEAPu s (bv_unsigned tp) LB m -> In (p, A, n) LB ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RFREE_STACK ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 A ->
  implM usegs (raw_freeF peekG (aadd (fst p) (UNIT * snd p))) s
        (rfree_postu ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B errv m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RFREE_SYM) fc None m (seg_rom usegs)).

Lemma rfree_stmt_of_class : (forall TB : TlsBase, rfree_stmt (PState:=PState) (AS:=AS) (TB:=TB)) -> rfree_stmt_u.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros HM. intros until errv. intros (H & HP) HIN AUX HB ST CLO LO ERR MI Ha0.
  assert (TP : tp = Z_to_bv 64 (@the_tb _ (TBu (bv_unsigned tp) H) + 200)).
  { cbn [the_tb TBu]. replace (bv_unsigned tp - 200 + 200) with (bv_unsigned tp) by lia. symmetry. apply Z_to_bv_bv_unsigned. }
  eapply implM_mono; [exact (HM (TBu (bv_unsigned tp) H) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                                F fc m s LB p A n lo B errv HP HIN AUX HB ST CLO LO ERR MI TP Ha0)|].
  intros r s' ms' PO. cbn beta in PO |- *. unfold rfree_post in PO. unfold rfree_postu.
  destruct PO as (u0&u1&u2&b0&b1&b2&b3&b4&b5&b6&b7&u3&u4&u5&u6&m'&E&MI'&ST'&ERR'&AUX'&PR&RST&HP').
  exists u0,u1,u2,b0,b1,b2,b3,b4,b5,b6,b7,u3,u4,u5,u6,m'.
  split; [exact E|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|].
  split; [apply (proj1 (rheap_pres_u _ H _ _ _ _)); exact PR|]. split; [exact RST|]. exists H; exact HP'.
Qed.

(* [comment removed for export] *)
Lemma rmalloc_stmt_of_class : (forall TB : TlsBase, rmalloc_stmt (PState:=PState) (AS:=AS) (TB:=TB)) -> rmalloc_stmt_u.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros HM. intros until errv. intros (H & HP) AUX HB ST CLO LO ERR MI Ha0 Hn.
  assert (TP : tp = Z_to_bv 64 (@the_tb _ (TBu (bv_unsigned tp) H) + 200)).
  { cbn [the_tb TBu]. replace (bv_unsigned tp - 200 + 200) with (bv_unsigned tp) by lia. symmetry. apply Z_to_bv_bv_unsigned. }
  eapply implM_mono; [exact (HM (TBu (bv_unsigned tp) H) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                                F fc m s LB n lo B errv HP AUX HB ST CLO LO ERR MI TP Ha0 Hn)|].
  intros r s' ms' PO. cbn beta in PO |- *. unfold rmalloc_post in PO. unfold rmalloc_postu.
  destruct PO as (u0&u1&u2&b0&b1&b2&b3&b4&b5&b6&b7&u3&u4&u5&u6&m'&errv'&E&MI'&ST'&ERR'&AUX'&PR&RST&RES).
  exists u0,u1,u2,b0,b1,b2,b3,b4,b5,b6,b7,u3,u4,u5,u6,m',errv'.
  split; [exact E|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|].
  split; [apply (proj1 (rheap_pres_u _ H _ _ _ _)); exact PR|]. split; [exact RST|].
  destruct r as [pf|].
  - destruct RES as (c & off & A & junk & Epf & EA & EC & BR & HP' & CH). exists c, off, A, junk.
    split; [exact Epf|]. split; [exact EA|]. split; [exact EC|]. split; [exact BR|]. split; [exists H; exact HP'| exact CH].
  - destruct RES as (EA & EEN & HP'). split; [exact EA|]. split; [exact EEN|]. exists H; exact HP'.
Qed.

End Consumer.

End WithCeil.
End TwB.
End RMalloc_iface.

(* [comment removed for export] *)
Module RMalloc_ifaceB.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import TlsBase.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocHINV. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocBlocks OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocHINV OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.Malloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Definition RCALLOC_SYM : Z := 0x18654.      (* [comment removed for export] *)
Definition RREALLOC_SYM : Z := 0x1a138.     (* [comment removed for export] *)
Definition RCALLOC_STACK : Z := 8224.       (* [comment removed for export] *)
Definition RCALLOC_MAX : Z := 3260.         (* [comment removed for export] *)
Definition RREALLOC_STACK : Z := 8256.      (* [comment removed for export] *)

Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rcalloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (n lo B : Z) (m : mem)
    (r : option aptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp)
    /\ rw_cells ssegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' B
    /\ rheap_pres LB (bv_unsigned sp) m m'
    /\ ps_rest s' = ps_rest s
    /\ match r with
       | None => a0 = Z_to_bv 64 0 /\ errv' = Z_to_bv 64 ENOMEM /\ RHEAP s' LB m'
       | Some pf => exists (c : cptr) (off : Z) A,
           pf = aadd c (UNIT * off)
           /\ a0 = Z_to_bv 64 A /\ A = conc (ps_m s') pf /\ rblock_range A n
           /\ RHEAP s' (((c, off), A, n) :: LB) m'
           /\ rw_cells ssegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))]
       end.

Definition rcalloc_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (cnt sz lo B : Z) (errv : word),
  RHEAP s LB m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk ssegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RCALLOC_STACK ->
  rw_cells ssegs m (errno_addr tp) [C4 errv] ->
  mem_inv ssegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 sz -> 0 <= cnt < 2^64 -> 0 <= sz < 2^64 -> cnt * sz <= RCALLOC_MAX ->
  implM ssegs (raw_callocF peekG cnt sz) s
        (rcalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB (cnt * sz) lo B m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RCALLOC_SYM) fc None m (seg_rom ssegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rrealloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (p : bptr) (A sz n lo B : Z) (bs : list byte) (m : mem)
    (r : option aptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp)
    /\ rw_cells ssegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' B
    /\ rheap_pres (lb_remove p LB) (bv_unsigned sp) m m'
    /\ ps_rest s' = ps_rest s
    /\ match r with
       | None => a0 = Z_to_bv 64 0 /\ errv' = Z_to_bv 64 ENOMEM /\ RHEAP s' LB m'
                 /\ rw_cells ssegs m' A [CB (Z.to_nat sz) bs]
       | Some q => exists (c : cptr) (off : Z) A',
           q = aadd c (UNIT * off)
           /\ a0 = Z_to_bv 64 A' /\ A' = conc (ps_m s') q /\ rblock_range A' n
           /\ RHEAP s' (((c, off), A', n) :: lb_remove p LB) m'
           /\ exists junk, rw_cells ssegs m' A' [CB (Z.to_nat (Z.min sz n)) (firstn (Z.to_nat (Z.min sz n)) bs);
                                               CB (Z.to_nat (n - Z.min sz n)) junk]
       end.

Definition rrealloc_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (p : bptr) (A sz n lo B : Z) (bs : list byte) (errv : word),
  RHEAP s LB m -> In (p, A, sz) LB ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk ssegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RREALLOC_STACK ->
  rw_cells ssegs m (errno_addr tp) [C4 errv] ->
  mem_inv ssegs m ->
  tp = Z_to_bv 64 RATP ->
  rw_cells ssegs m A [CB (Z.to_nat sz) bs] ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  implM ssegs (raw_reallocF peekG (Some (aadd (fst p) (UNIT * snd p))) n) s
        (rrealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p A sz n lo B bs m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RREALLOC_SYM) fc None m (seg_rom ssegs)).

End PORT.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Consumer.
Context {PState : Type} {AS : AllocSt PState}.

Definition rcalloc_postu (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (n lo B : Z) (m : mem)
    (r : option aptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp)
    /\ rw_cells ssegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' B
    /\ rheap_presu (bv_unsigned tp) LB (bv_unsigned sp) m m'
    /\ ps_rest s' = ps_rest s
    /\ match r with
       | None => a0 = Z_to_bv 64 0 /\ errv' = Z_to_bv 64 ENOMEM /\ RHEAPu s' (bv_unsigned tp) LB m'
       | Some pf => exists (c : cptr) (off : Z) A,
           pf = aadd c (UNIT * off)
           /\ a0 = Z_to_bv 64 A /\ A = conc (ps_m s') pf /\ rblock_rangeu (bv_unsigned tp) A n
           /\ RHEAPu s' (bv_unsigned tp) (((c, off), A, n) :: LB) m'
           /\ rw_cells ssegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))]
       end.

Definition rcalloc_stmt_u : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (cnt sz lo B : Z) (errv : word),
  RHEAPu s (bv_unsigned tp) LB m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk ssegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RCALLOC_STACK ->
  rw_cells ssegs m (errno_addr tp) [C4 errv] ->
  mem_inv ssegs m ->
  a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 sz -> 0 <= cnt < 2^64 -> 0 <= sz < 2^64 -> cnt * sz <= RCALLOC_MAX ->
  implM ssegs (raw_callocF peekG cnt sz) s
        (rcalloc_postu ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB (cnt * sz) lo B m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RCALLOC_SYM) fc None m (seg_rom ssegs)).

Definition rrealloc_postu (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (p : bptr) (A sz n lo B : Z) (bs : list byte) (m : mem)
    (r : option aptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp)
    /\ rw_cells ssegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' B
    /\ rheap_presu (bv_unsigned tp) (lb_remove p LB) (bv_unsigned sp) m m'
    /\ ps_rest s' = ps_rest s
    /\ match r with
       | None => a0 = Z_to_bv 64 0 /\ errv' = Z_to_bv 64 ENOMEM /\ RHEAPu s' (bv_unsigned tp) LB m'
                 /\ rw_cells ssegs m' A [CB (Z.to_nat sz) bs]
       | Some q => exists (c : cptr) (off : Z) A',
           q = aadd c (UNIT * off)
           /\ a0 = Z_to_bv 64 A' /\ A' = conc (ps_m s') q /\ rblock_rangeu (bv_unsigned tp) A' n
           /\ RHEAPu s' (bv_unsigned tp) (((c, off), A', n) :: lb_remove p LB) m'
           /\ exists junk, rw_cells ssegs m' A' [CB (Z.to_nat (Z.min sz n)) (firstn (Z.to_nat (Z.min sz n)) bs);
                                               CB (Z.to_nat (n - Z.min sz n)) junk]
       end.

Definition rrealloc_stmt_u : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (p : bptr) (A sz n lo B : Z) (bs : list byte) (errv : word),
  RHEAPu s (bv_unsigned tp) LB m -> In (p, A, sz) LB ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk ssegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RREALLOC_STACK ->
  rw_cells ssegs m (errno_addr tp) [C4 errv] ->
  mem_inv ssegs m ->
  rw_cells ssegs m A [CB (Z.to_nat sz) bs] ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  implM ssegs (raw_reallocF peekG (Some (aadd (fst p) (UNIT * snd p))) n) s
        (rrealloc_postu ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p A sz n lo B bs m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RREALLOC_SYM) fc None m (seg_rom ssegs)).

Definition rrealloc_stmt_of_class__stmt : Prop := (forall TB : TlsBase, rrealloc_stmt (PState:=PState) (AS:=AS) (TB:=TB)) -> rrealloc_stmt_u.
Section Sz1.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A sz n lo B bs errv : ltac2:(SecDiet.SzSec.tyM 'rrealloc_stmt_of_class__stmt "hvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rrealloc_stmt_of_class__body : ltac2:(SecDiet.SzSec.bodyP 'rrealloc_stmt_of_class__stmt "hvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros HM.
 intros (H & HP) Hin AUX HB ST CLO LO ERR MI CH Ha0 Ha1 Hn.
  assert (TP : tp = Z_to_bv 64 (@the_tb _ (TBu (bv_unsigned tp) H) + 200)).
  { cbn [the_tb TBu]. replace (bv_unsigned tp - 200 + 200) with (bv_unsigned tp) by lia. symmetry. apply Z_to_bv_bv_unsigned. }
  eapply implM_mono; [exact (HM (TBu (bv_unsigned tp) H) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                                F fc m s LB p A sz n lo B bs errv HP Hin AUX HB ST CLO LO ERR MI TP CH Ha0 Ha1 Hn)|].
  intros r s' ms' PO. cbn beta in PO |- *. unfold rrealloc_post in PO. unfold rrealloc_postu.
  destruct PO as (u0&u1&u2&b0&b1&b2&b3&b4&b5&b6&b7&u3&u4&u5&u6&m'&errv'&E&MI'&ST'&ERR'&AUX'&PR&RST&RES).
  exists u0,u1,u2,b0,b1,b2,b3,b4,b5,b6,b7,u3,u4,u5,u6,m',errv'.
  split; [exact E|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|].
  split; [apply (proj1 (rheap_pres_u _ H _ _ _ _)); exact PR|]. split; [exact RST|].
  destruct r as [q|].
  - destruct RES as (c & off & A' & Eq & EA & EC & BR & HP' & CH'). exists c, off, A'.
    split; [exact Eq|]. split; [exact EA|]. split; [exact EC|]. split; [exact BR|]. split; [exists H; exact HP'| exact CH'].
  - destruct RES as (EA & EEN & HP' & CH'). split; [exact EA|]. split; [exact EEN|]. split; [exists H; exact HP'| exact CH'].
Qed.
End Sz1.
Lemma rrealloc_stmt_of_class : ltac:(let t := eval cbv delta [rrealloc_stmt_of_class__stmt] in rrealloc_stmt_of_class__stmt in exact t).
Proof using Type. intros HM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A sz n lo B bs errv. ltac2:(SecDiet.SzSec.closeP 'rrealloc_stmt_of_class__body "hvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

Definition rcalloc_stmt_of_class__stmt : Prop := (forall TB : TlsBase, rcalloc_stmt (PState:=PState) (AS:=AS) (TB:=TB)) -> rcalloc_stmt_u.
Section Sz2.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB cnt sz lo B errv : ltac2:(SecDiet.SzSec.tyM 'rcalloc_stmt_of_class__stmt "hvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rcalloc_stmt_of_class__body : ltac2:(SecDiet.SzSec.bodyP 'rcalloc_stmt_of_class__stmt "hvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros HM.
 intros (H & HP) AUX HB ST CLO LO ERR MI Ha0 Ha1 Hc Hs Hmax.
  assert (TP : tp = Z_to_bv 64 (@the_tb _ (TBu (bv_unsigned tp) H) + 200)).
  { cbn [the_tb TBu]. replace (bv_unsigned tp - 200 + 200) with (bv_unsigned tp) by lia. symmetry. apply Z_to_bv_bv_unsigned. }
  eapply implM_mono; [exact (HM (TBu (bv_unsigned tp) H) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                                F fc m s LB cnt sz lo B errv HP AUX HB ST CLO LO ERR MI TP Ha0 Ha1 Hc Hs Hmax)|].
  intros r s' ms' PO. cbn beta in PO |- *. unfold rcalloc_post in PO. unfold rcalloc_postu.
  destruct PO as (u0&u1&u2&b0&b1&b2&b3&b4&b5&b6&b7&u3&u4&u5&u6&m'&errv'&E&MI'&ST'&ERR'&AUX'&PR&RST&RES).
  exists u0,u1,u2,b0,b1,b2,b3,b4,b5,b6,b7,u3,u4,u5,u6,m',errv'.
  split; [exact E|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|].
  split; [apply (proj1 (rheap_pres_u _ H _ _ _ _)); exact PR|]. split; [exact RST|].
  destruct r as [pf|].
  - destruct RES as (c & off & A & Epf & EA & EC & BR & HP' & CH). exists c, off, A.
    split; [exact Epf|]. split; [exact EA|]. split; [exact EC|]. split; [exact BR|]. split; [exists H; exact HP'| exact CH].
  - destruct RES as (EA & EEN & HP'). split; [exact EA|]. split; [exact EEN|]. exists H; exact HP'.
Qed.
End Sz2.
Lemma rcalloc_stmt_of_class : ltac:(let t := eval cbv delta [rcalloc_stmt_of_class__stmt] in rcalloc_stmt_of_class__stmt in exact t).
Proof using Type. intros HM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB cnt sz lo B errv. ltac2:(SecDiet.SzSec.closeP 'rcalloc_stmt_of_class__body "hvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End Consumer.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.TlsBaseU.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.SFModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocBlocks OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocHINV OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.Malloc_iface.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MSecret.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Definition RCALLOC_SYM : Z := 0x18e14.      (* [comment removed for export] *)
Definition RREALLOC_SYM : Z := 0x1a8f8.     (* [comment removed for export] *)
Definition RCALLOC_STACK : Z := 8224.       (* [comment removed for export] *)
Definition RCALLOC_MAX : Z := 3260.         (* [comment removed for export] *)
Definition RREALLOC_STACK : Z := 8256.      (* [comment removed for export] *)

Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rcalloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (n lo B : Z) (m : mem)
    (r : option aptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' B
    /\ rheap_pres LB (bv_unsigned sp) m m'
    /\ ps_rest s' = ps_rest s
    /\ match r with
       | None => a0 = Z_to_bv 64 0 /\ errv' = Z_to_bv 64 ENOMEM /\ RHEAP s' LB m'
       | Some pf => exists (c : cptr) (off : Z) A,
           pf = aadd c (UNIT * off)
           /\ a0 = Z_to_bv 64 A /\ A = conc (ps_m s') pf /\ rblock_range A n
           /\ RHEAP s' (((c, off), A, n) :: LB) m'
           /\ rw_cells usegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))]
       end.

Definition rcalloc_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (cnt sz lo B : Z) (errv : word),
  RHEAP s LB m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RCALLOC_STACK ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 sz -> 0 <= cnt < 2^64 -> 0 <= sz < 2^64 -> cnt * sz <= RCALLOC_MAX ->
  implM usegs (raw_callocF peekG cnt sz) s
        (rcalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB (cnt * sz) lo B m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RCALLOC_SYM) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rrealloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (p : bptr) (A sz n lo B : Z) (bs : list byte) (m : mem)
    (r : option aptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' B
    /\ rheap_pres (lb_remove p LB) (bv_unsigned sp) m m'
    /\ ps_rest s' = ps_rest s
    /\ match r with
       | None => a0 = Z_to_bv 64 0 /\ errv' = Z_to_bv 64 ENOMEM /\ RHEAP s' LB m'
                 /\ rw_cells usegs m' A [CB (Z.to_nat sz) bs]
       | Some q => exists (c : cptr) (off : Z) A',
           q = aadd c (UNIT * off)
           /\ a0 = Z_to_bv 64 A' /\ A' = conc (ps_m s') q /\ rblock_range A' n
           /\ RHEAP s' (((c, off), A', n) :: lb_remove p LB) m'
           /\ exists junk, rw_cells usegs m' A' [CB (Z.to_nat (Z.min sz n)) (firstn (Z.to_nat (Z.min sz n)) bs);
                                               CB (Z.to_nat (n - Z.min sz n)) junk]
       end.

Definition rrealloc_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (p : bptr) (A sz n lo B : Z) (bs : list byte) (errv : word),
  RHEAP s LB m -> In (p, A, sz) LB ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RREALLOC_STACK ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  tp = Z_to_bv 64 RATP ->
  rw_cells usegs m A [CB (Z.to_nat sz) bs] ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  implM usegs (raw_reallocF peekG (Some (aadd (fst p) (UNIT * snd p))) n) s
        (rrealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p A sz n lo B bs m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RREALLOC_SYM) fc None m (seg_rom usegs)).

End PORT.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Consumer.
Context {PState : Type} {AS : AllocSt PState}.

Definition rcalloc_postu (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (n lo B : Z) (m : mem)
    (r : option aptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' B
    /\ rheap_presu (bv_unsigned tp) LB (bv_unsigned sp) m m'
    /\ ps_rest s' = ps_rest s
    /\ match r with
       | None => a0 = Z_to_bv 64 0 /\ errv' = Z_to_bv 64 ENOMEM /\ RHEAPu s' (bv_unsigned tp) LB m'
       | Some pf => exists (c : cptr) (off : Z) A,
           pf = aadd c (UNIT * off)
           /\ a0 = Z_to_bv 64 A /\ A = conc (ps_m s') pf /\ rblock_rangeu (bv_unsigned tp) A n
           /\ RHEAPu s' (bv_unsigned tp) (((c, off), A, n) :: LB) m'
           /\ rw_cells usegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))]
       end.

Definition rcalloc_stmt_u : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (cnt sz lo B : Z) (errv : word),
  RHEAPu s (bv_unsigned tp) LB m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RCALLOC_STACK ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 sz -> 0 <= cnt < 2^64 -> 0 <= sz < 2^64 -> cnt * sz <= RCALLOC_MAX ->
  implM usegs (raw_callocF peekG cnt sz) s
        (rcalloc_postu ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB (cnt * sz) lo B m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RCALLOC_SYM) fc None m (seg_rom usegs)).

Definition rrealloc_postu (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (p : bptr) (A sz n lo B : Z) (bs : list byte) (m : mem)
    (r : option aptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' B
    /\ rheap_presu (bv_unsigned tp) (lb_remove p LB) (bv_unsigned sp) m m'
    /\ ps_rest s' = ps_rest s
    /\ match r with
       | None => a0 = Z_to_bv 64 0 /\ errv' = Z_to_bv 64 ENOMEM /\ RHEAPu s' (bv_unsigned tp) LB m'
                 /\ rw_cells usegs m' A [CB (Z.to_nat sz) bs]
       | Some q => exists (c : cptr) (off : Z) A',
           q = aadd c (UNIT * off)
           /\ a0 = Z_to_bv 64 A' /\ A' = conc (ps_m s') q /\ rblock_rangeu (bv_unsigned tp) A' n
           /\ RHEAPu s' (bv_unsigned tp) (((c, off), A', n) :: lb_remove p LB) m'
           /\ exists junk, rw_cells usegs m' A' [CB (Z.to_nat (Z.min sz n)) (firstn (Z.to_nat (Z.min sz n)) bs);
                                               CB (Z.to_nat (n - Z.min sz n)) junk]
       end.

Definition rrealloc_stmt_u : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (p : bptr) (A sz n lo B : Z) (bs : list byte) (errv : word),
  RHEAPu s (bv_unsigned tp) LB m -> In (p, A, sz) LB ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RREALLOC_STACK ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  rw_cells usegs m A [CB (Z.to_nat sz) bs] ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  implM usegs (raw_reallocF peekG (Some (aadd (fst p) (UNIT * snd p))) n) s
        (rrealloc_postu ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p A sz n lo B bs m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RREALLOC_SYM) fc None m (seg_rom usegs)).

Definition rrealloc_stmt_of_class__stmt : Prop := (forall TB : TlsBase, rrealloc_stmt (PState:=PState) (AS:=AS) (TB:=TB)) -> rrealloc_stmt_u.
Section Sz1.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A sz n lo B bs errv : ltac2:(SecDiet.SzSec.tyM 'rrealloc_stmt_of_class__stmt "hvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rrealloc_stmt_of_class__body : ltac2:(SecDiet.SzSec.bodyP 'rrealloc_stmt_of_class__stmt "hvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros HM.
 intros (H & HP) Hin AUX HB ST CLO LO ERR MI CH Ha0 Ha1 Hn.
  assert (TP : tp = Z_to_bv 64 (@the_tb _ (TBu (bv_unsigned tp) H) + 200)).
  { cbn [the_tb TBu]. replace (bv_unsigned tp - 200 + 200) with (bv_unsigned tp) by lia. symmetry. apply Z_to_bv_bv_unsigned. }
  eapply implM_mono; [exact (HM (TBu (bv_unsigned tp) H) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                                F fc m s LB p A sz n lo B bs errv HP Hin AUX HB ST CLO LO ERR MI TP CH Ha0 Ha1 Hn)|].
  intros r s' ms' PO. cbn beta in PO |- *. unfold rrealloc_post in PO. unfold rrealloc_postu.
  destruct PO as (u0&u1&u2&b0&b1&b2&b3&b4&b5&b6&b7&u3&u4&u5&u6&m'&errv'&E&MI'&ST'&ERR'&AUX'&PR&RST&RES).
  exists u0,u1,u2,b0,b1,b2,b3,b4,b5,b6,b7,u3,u4,u5,u6,m',errv'.
  split; [exact E|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|].
  split; [apply (proj1 (rheap_pres_u _ H _ _ _ _)); exact PR|]. split; [exact RST|].
  destruct r as [q|].
  - destruct RES as (c & off & A' & Eq & EA & EC & BR & HP' & CH'). exists c, off, A'.
    split; [exact Eq|]. split; [exact EA|]. split; [exact EC|]. split; [exact BR|]. split; [exists H; exact HP'| exact CH'].
  - destruct RES as (EA & EEN & HP' & CH'). split; [exact EA|]. split; [exact EEN|]. split; [exists H; exact HP'| exact CH'].
Qed.
End Sz1.
Lemma rrealloc_stmt_of_class : ltac:(let t := eval cbv delta [rrealloc_stmt_of_class__stmt] in rrealloc_stmt_of_class__stmt in exact t).
Proof using Type. intros HM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A sz n lo B bs errv. ltac2:(SecDiet.SzSec.closeP 'rrealloc_stmt_of_class__body "hvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

Definition rcalloc_stmt_of_class__stmt : Prop := (forall TB : TlsBase, rcalloc_stmt (PState:=PState) (AS:=AS) (TB:=TB)) -> rcalloc_stmt_u.
Section Sz2.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB cnt sz lo B errv : ltac2:(SecDiet.SzSec.tyM 'rcalloc_stmt_of_class__stmt "hvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rcalloc_stmt_of_class__body : ltac2:(SecDiet.SzSec.bodyP 'rcalloc_stmt_of_class__stmt "hvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros HM.
 intros (H & HP) AUX HB ST CLO LO ERR MI Ha0 Ha1 Hc Hs Hmax.
  assert (TP : tp = Z_to_bv 64 (@the_tb _ (TBu (bv_unsigned tp) H) + 200)).
  { cbn [the_tb TBu]. replace (bv_unsigned tp - 200 + 200) with (bv_unsigned tp) by lia. symmetry. apply Z_to_bv_bv_unsigned. }
  eapply implM_mono; [exact (HM (TBu (bv_unsigned tp) H) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                                F fc m s LB cnt sz lo B errv HP AUX HB ST CLO LO ERR MI TP Ha0 Ha1 Hc Hs Hmax)|].
  intros r s' ms' PO. cbn beta in PO |- *. unfold rcalloc_post in PO. unfold rcalloc_postu.
  destruct PO as (u0&u1&u2&b0&b1&b2&b3&b4&b5&b6&b7&u3&u4&u5&u6&m'&errv'&E&MI'&ST'&ERR'&AUX'&PR&RST&RES).
  exists u0,u1,u2,b0,b1,b2,b3,b4,b5,b6,b7,u3,u4,u5,u6,m',errv'.
  split; [exact E|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|].
  split; [apply (proj1 (rheap_pres_u _ H _ _ _ _)); exact PR|]. split; [exact RST|].
  destruct r as [pf|].
  - destruct RES as (c & off & A & Epf & EA & EC & BR & HP' & CH). exists c, off, A.
    split; [exact Epf|]. split; [exact EA|]. split; [exact EC|]. split; [exact BR|]. split; [exists H; exact HP'| exact CH].
  - destruct RES as (EA & EEN & HP'). split; [exact EA|]. split; [exact EEN|]. exists H; exact HP'.
Qed.
End Sz2.
Lemma rcalloc_stmt_of_class : ltac:(let t := eval cbv delta [rcalloc_stmt_of_class__stmt] in rcalloc_stmt_of_class__stmt in exact t).
Proof using Type. intros HM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB cnt sz lo B errv. ltac2:(SecDiet.SzSec.closeP 'rcalloc_stmt_of_class__body "hvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End Consumer.

End WithCeil.
End TwB.
End RMalloc_ifaceB.

(* [comment removed for export] *)
Module RPeek.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import TlsBase.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep  Arr ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_enframe.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMallocKit_B2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Lemma peek_agrees_known_sh o st st' ms q v :
  get_shadow st' (fst q) = get_shadow st (fst q) ->
  cell_read (get_shadow st (fst q)) (snd q) = Known v -> peek_agrees o st' ms q.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts. intros E K h E'. rewrite E, K in E'. discriminate. Qed.

(* [comment removed for export] *)
Lemma peek_agrees_same o st q r regs F pc fc rv :
  rmrep st o -> (s_regions st) !! (fst q) = Some r -> 0 <= snd q < round_up_pg (r_len r) ->
  peek_agrees o st (MS regs F pc fc rv o (seg_rom ssegs)) q.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros MR Hr Hq h E. unfold peek_byte, pans_mem. cbn [ms_mem].
  unfold conc, get_region. rewrite Hr.
  destruct MR as (WF & _). destruct WF as (_ & WR & _). destruct (WR _ _ Hr) as (B0 & _ & L0 & BC & RF).
  pose proof (rreserved_disjoint1 _ _ RF) as D. pose proof (round_up_pg_ge (r_len r)).
  assert (HA : 0 <= r_base r + snd q /\ r_base r + snd q + 1 <= 2^64) by (ceil_facts; lia).
  rewrite ref_mrd_overlay by (rewrite wa_unsigned by lia; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma peek_agrees_of_byte o st m q (x : byte) regs F pc fc rv :
  bytes_at ssegs m (conc st q) [x] -> rdv pans_mem o st q = bv_unsigned x ->
  peek_agrees o st (MS regs F pc fc rv m (seg_rom ssegs)) q.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros HB HR. eapply (peek_agrees_of_bytes_at o st m q (conc st q) [x] 0 x); [exact HB| reflexivity| cbn; lia| exact HR].
Qed.

(* [comment removed for export] *)
Lemma rreserved_tlsF : forall b n, ranges_free ref_reserved b n = true -> b + n <= the_tb \/ the_tb + 4096 <= b.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros b n H. unfold ranges_free, ref_reserved in H. cbn [forallb fst snd] in H.
  unfold iv_disjoint in H. rewrite !Bool.andb_true_iff, !Bool.orb_true_iff, !Z.leb_le in H. lia.
Qed.

End PORT.

(* [comment removed for export] *)
End WithCeil.

Ltac find_known :=
  cbn [aadd fst snd];
  match goal with
  | K : cell_read ?sh ?i = Known ?v |- cell_read ?sh ?j = Known _ =>
      fastfirst (first [ noevar_assumption | exact K | replace j with i by (unfold IB, UNIT in *; lia); exact K ])
  | E : fst ?a = ?c, K : cell_read (get_shadow ?st ?c') ?i = Known ?v |- cell_read (get_shadow ?st (fst ?a)) ?j = Known _ =>
      rewrite E; fastfirst (first [ noevar_assumption | exact K | replace j with i by (unfold IB, UNIT in *; lia); exact K ])
  | E : ?c = fst ?a, K : cell_read (get_shadow ?st ?c') ?i = Known ?v |- cell_read (get_shadow ?st (fst ?a)) ?j = Known _ =>
      rewrite <- E; fastfirst (first [ noevar_assumption | exact K | replace j with i by (unfold IB, UNIT in *; lia); exact K ])
  end.

(* [comment removed for export] *)
Ltac peek_known := eapply peek_agrees_known; find_known.
(* [comment removed for export] *)
Ltac peek_known_sh SH := eapply peek_agrees_known_sh; [apply SH | find_known].
(* [comment removed for export] *)
Ltac peek_same MR :=
  eapply peek_agrees_same; [exact MR | cbn [aadd fst]; first [eassumption | match goal with E : fst _ = _ |- _ => rewrite E; eassumption end]
                          | cbn [aadd snd]; unfold UNIT, IB in *; lia].

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.TlsBaseU.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.SFModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_enframe.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMallocKit_B2.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MSecret.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Lemma peek_agrees_known_sh o st st' ms q v :
  get_shadow st' (fst q) = get_shadow st (fst q) ->
  cell_read (get_shadow st (fst q)) (snd q) = Known v -> peek_agrees o st' ms q.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts. intros E K h E'. rewrite E, K in E'. discriminate. Qed.

(* [comment removed for export] *)
Lemma peek_agrees_same o st q r regs F pc fc rv :
  rmrep st o -> (s_regions st) !! (fst q) = Some r -> 0 <= snd q < round_up_pg (r_len r) ->
  peek_agrees o st (MS regs F pc fc rv o (seg_rom usegs)) q.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros MR Hr Hq h E. unfold peek_byte, pans_mem. cbn [ms_mem].
  unfold conc, get_region. rewrite Hr.
  destruct MR as (WF & _). destruct WF as (_ & WR & _). destruct (WR _ _ Hr) as (B0 & _ & L0 & BC & RF).
  pose proof (rreserved_disjoint1 _ _ RF) as D. pose proof (round_up_pg_ge (r_len r)).
  assert (HA : 0 <= r_base r + snd q /\ r_base r + snd q + 1 <= 2^64) by (ceil_facts; lia).
  rewrite ref_mrd_overlay by (rewrite wa_unsigned by lia; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma peek_agrees_of_byte o st m q (x : byte) regs F pc fc rv :
  bytes_at usegs m (conc st q) [x] -> rdv pans_mem o st q = bv_unsigned x ->
  peek_agrees o st (MS regs F pc fc rv m (seg_rom usegs)) q.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros HB HR. eapply (peek_agrees_of_bytes_at o st m q (conc st q) [x] 0 x); [exact HB| reflexivity| cbn; lia| exact HR].
Qed.

(* [comment removed for export] *)
Lemma rreserved_tlsF : forall b n, ranges_free ref_reserved b n = true -> b + n <= the_tb \/ the_tb + 4096 <= b.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros b n H. unfold ranges_free, ref_reserved in H. cbn [forallb fst snd] in H.
  unfold iv_disjoint in H. rewrite !Bool.andb_true_iff, !Bool.orb_true_iff, !Z.leb_le in H. lia.
Qed.

End PORT.

(* [comment removed for export] *)
End WithCeil.

Ltac find_known :=
  cbn [aadd fst snd];
  match goal with
  | K : cell_read ?sh ?i = Known ?v |- cell_read ?sh ?j = Known _ =>
      fastfirst (first [ noevar_assumption | exact K | replace j with i by (unfold IB, UNIT in *; lia); exact K ])
  | E : fst ?a = ?c, K : cell_read (get_shadow ?st ?c') ?i = Known ?v |- cell_read (get_shadow ?st (fst ?a)) ?j = Known _ =>
      rewrite E; fastfirst (first [ noevar_assumption | exact K | replace j with i by (unfold IB, UNIT in *; lia); exact K ])
  | E : ?c = fst ?a, K : cell_read (get_shadow ?st ?c') ?i = Known ?v |- cell_read (get_shadow ?st (fst ?a)) ?j = Known _ =>
      rewrite <- E; fastfirst (first [ noevar_assumption | exact K | replace j with i by (unfold IB, UNIT in *; lia); exact K ])
  end.

(* [comment removed for export] *)
Ltac peek_known := eapply peek_agrees_known; find_known.
(* [comment removed for export] *)
Ltac peek_known_sh SH := eapply peek_agrees_known_sh; [apply SH | find_known].
(* [comment removed for export] *)
Ltac peek_same MR :=
  eapply peek_agrees_same; [exact MR | cbn [aadd fst]; first [eassumption | match goal with E : fst _ = _ |- _ => rewrite E; eassumption end]
                          | cbn [aadd snd]; unfold UNIT, IB in *; lia].
End TwB.
End RPeek.

(* [comment removed for export] *)
Module RMalloc_ifaceT.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog HeapFull. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.HeapFull.
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBase MallocHINV. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.TlsBase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocHINV OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.Malloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

#[local] Notation PS := (PState fheap hptr).
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Definition tblock : Type := (hptr * Z * Z)%type.     (* [comment removed for export] *)
Definition tb_tok (t : tblock) : hptr := fst (fst t).
Definition tb_addr (t : tblock) : Z := snd (fst t).
Definition tb_size (t : tblock) : Z := snd t.

(* [comment removed for export] *)
Definition tgen (ids : hptr -> bptr) (t : tblock) : block := (ids (tb_tok t), tb_addr t, tb_size t).

(* [comment removed for export] *)
Definition HEAPT (h : fheap) (utp : Z) (LB : list tblock) (m : mem) : Prop :=
  exists (H : tls_ok (utp - 200)) (ids : hptr -> bptr),
       RHEAPm (TB:=TBu utp H) (fh_m h) (fh_brk h) (map (tgen ids) LB) m
    /\ (forall t, In t LB -> fh_blk h !! (tb_tok t) = Some (blk_ptr (tgen ids t), tb_size t))
    /\ List.NoDup (map tb_tok LB)
    /\ (forall k, fh_blk h !! k <> None -> (k < fh_next h)%N).

Definition in_blockT (LB : list tblock) (a : Z) : Prop :=
  exists t, In t LB /\ tb_addr t <= a < tb_addr t + tb_size t.

Definition heap_presT (utp : Z) (LB : list tblock) (SP : Z) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 ->
    (SP <= a \/ (0x22000 <= a < 0x55000 /\ ~ (RMLOCK <= a < RCTX + 936) /\ ~ (utp - 164 <= a < utp - 160)) \/ in_blockT LB a
     \/ (utp - 200 <= a < utp - 200 + 4096 /\ ~ (utp - 164 <= a < utp - 160))) ->
    m' (wa a) = m (wa a) /\ (wview ssegs m (wa a) <> None -> wview ssegs m' (wa a) <> None).

Definition lbt_remove (q : hptr) (LB : list tblock) : list tblock :=
  List.filter (fun t => negb (N.eqb (tb_tok t) q)) LB.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_blockT_iff ids LB a : in_blockT LB a <-> in_block (map (tgen ids) LB) a.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  split.
  - intros (t & Ht & Hr). exists (tgen ids t). split; [apply in_map; exact Ht| exact Hr].
  - intros (b & Hb & Hr). apply in_map_iff in Hb. destruct Hb as (t & <- & Ht). exists t. split; [exact Ht| exact Hr].
Qed.

Lemma heap_presT_of ids utp LB SP m m' :
  rheap_presu utp (map (tgen ids) LB) SP m m' -> heap_presT utp LB SP m m'.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  intros HP a Ha Hc. apply HP; [exact Ha|].
  destruct Hc as [X|[X|[X|X]]]; [tauto|tauto| |tauto]. right; right; left. apply (proj1 (in_blockT_iff ids LB a)). exact X.
Qed.

Lemma NoDup_map_inj' {A B} (f : A -> B) l x y : List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  induction l as [|z l IH]; intros ND Hx Hy E; [destruct Hx|].
  cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND].
  destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity| | | exact (IH ND Hx Hy E)].
  - exfalso. apply NI. rewrite E. apply in_map. exact Hy.
  - exfalso. apply NI. rewrite <- E. apply in_map. exact Hx.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma HEAPT_perm : forall h utp LB LB' m, HEAPT h utp LB m -> Permutation LB LB' -> HEAPT h utp LB' m.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros h utp LB LB' m (H & ids & HR & CR & ND & FR) P.
  exists H, ids. split; [| split; [intros t Ht; apply CR; eapply Permutation_in; [apply Permutation_sym; exact P| exact Ht]| split; [| exact FR]]].
  - destruct HR as (LB0 & P0 & MR & HI). exists LB0. split; [| split; [exact MR| exact HI]].
    eapply Permutation_trans; [exact P0| apply Permutation_map; exact P].
  - eapply Permutation_NoDup; [apply Permutation_map; exact P| exact ND].
Qed.

Lemma HEAPT_nodup : forall h utp LB m, HEAPT h utp LB m -> List.NoDup (map tb_tok LB).
Proof using Type. pin_using tt. ceil_facts. msec_facts. intros h utp LB m (H & ids & HR & CR & ND & FR). exact ND. Qed.

Lemma HEAPT_addr_of : (forall TB : TlsBase, RHEAP_block_range_stmt (PState:=PS) (AS:=fheap_AllocSt) (TB:=TB)) ->
  forall h utp LB m q A n, HEAPT h utp LB m -> In (q, A, n) LB -> hf_addr h q = A.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros HBR h utp LB m q A n (H & ids & HR & CR & ND & FR) Hin.
  unfold hf_addr. rewrite (CR _ Hin). cbn [tb_tok tb_size tgen tb_addr fst snd].
  destruct (HBR (TBu utp H) (ps_init h : PS) (map (tgen ids) LB) m (ids q) A n) as [_ EA]; [exact HR| |].
  - apply in_map_iff. exists (q, A, n). split; [reflexivity| exact Hin].
  - cbn in EA. unfold blk_ptr, blk_slot, blk_id, tgen. cbn [fst snd tb_tok]. symmetry. exact EA.
Qed.

Lemma HEAPT_range_of : (forall TB : TlsBase, RHEAP_block_range_stmt (PState:=PS) (AS:=fheap_AllocSt) (TB:=TB)) ->
  forall h utp LB m q A n, HEAPT h utp LB m -> In (q, A, n) LB -> rblock_rangeu utp A n.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros HBR h utp LB m q A n (H & ids & HR & CR & ND & FR) Hin.
  destruct (HBR (TBu utp H) (ps_init h : PS) (map (tgen ids) LB) m (ids q) A n) as [BR _]; [exact HR| |].
  - apply in_map_iff. exists (q, A, n). split; [reflexivity| exact Hin].
  - exact BR.
Qed.

Lemma HEAPT_disjoint_of : (forall TB : TlsBase, RHEAP_blocks_disjoint_stmt (PState:=PS) (AS:=fheap_AllocSt) (TB:=TB)) ->
  (forall TB : TlsBase, RHEAP_blocks_nodup_stmt (PState:=PS) (AS:=fheap_AllocSt) (TB:=TB)) ->
  forall h utp LB m t1 t2, HEAPT h utp LB m -> In t1 LB -> In t2 LB -> tb_tok t1 <> tb_tok t2 ->
    tb_addr t1 + tb_size t1 <= tb_addr t2 \/ tb_addr t2 + tb_size t2 <= tb_addr t1.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros HBD HND h utp LB m t1 t2 (H & ids & HR & CR & ND & FR) H1 H2 NE.
  apply (HBD (TBu utp H) (ps_init h : PS) (map (tgen ids) LB) m (tgen ids t1) (tgen ids t2)); [exact HR| apply in_map; exact H1| apply in_map; exact H2|].
  intros E. apply NE. cbn [blk_id tgen fst] in E.
  pose proof (HND (TBu utp H) (ps_init h : PS) (map (tgen ids) LB) m HR) as NDg. rewrite map_map in NDg. cbn [blk_id tgen fst] in NDg.
  assert (t1 = t2) as ->; [| reflexivity].
  apply (NoDup_map_inj' (fun x => ids (tb_tok x)) LB t1 t2 NDg H1 H2 E).
Qed.

Definition client_write_okT (utp : Z) (LB : list tblock) (iv : Z * Z) : Prop :=
  alloc_ceiling <= fst iv
  \/ (0x22000 <= fst iv /\ snd iv <= 0x55000 /\ (snd iv <= RLIBC \/ RCTX + 936 <= fst iv)
      /\ (snd iv <= RSSP_GUARD \/ RSSP_GUARD + 8 <= fst iv) /\ (snd iv <= RGOT_SSP \/ RGOT_SSP + 8 <= fst iv))
  \/ (exists t, In t LB /\ tb_addr t <= fst iv /\ snd iv <= tb_addr t + tb_size t)
  \/ (utp - 200 <= fst iv /\ snd iv <= utp - 200 + 4096).

Lemma HEAPT_frame_of : (forall TB : TlsBase, RHEAP_frame_stmt (PState:=PS) (AS:=fheap_AllocSt) (TB:=TB)) ->
  forall h utp LB m m' W,
    HEAPT h utp LB m -> munch W m m' -> wmono ssegs m m' -> Forall (client_write_okT utp LB) W -> HEAPT h utp LB m'.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros HF h utp LB m m' W (H & ids & HR & CR & ND & FR) MU WM FW.
  exists H, ids. split; [| split; [exact CR| split; [exact ND| exact FR]]].
  apply (HF (TBu utp H) (ps_init h : PS) (map (tgen ids) LB) m m' W HR MU WM).
  eapply Forall_impl; [|exact FW]. intros iv Hiv. unfold rclient_write_ok. cbn [the_tb TBu].
  destruct Hiv as [X|[X|[(t & Ht & X1 & X2)|X]]]; [left; exact X| right; left; exact X| | right; right; right; exact X].
  right; right; left. exists (tgen ids t). split; [apply in_map; exact Ht|]. cbn. lia.
Qed.

Lemma HEAPT_init_of : (forall TB : TlsBase, RHEAP_init_stmt (PState:=PS) (AS:=fheap_AllocSt) (TB:=TB)) ->
  forall utp m (H : tls_ok (utp - 200)), rheap_init_mem m ->
    HEAPT (fheap_init msecret (reservedZ ssegs ++ [(utp - 200, 4096)])) utp [] m.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros HI utp m H IM. exists H, (fun _ => ((0%N, 0), 0)). split; [| split; [intros t []| split; [constructor|]]].
  - cbn [map fh_m fh_brk fheap_init].
    pose proof (HI (TBu utp H) (ps_init (fheap_init msecret (reservedZ ssegs ++ [(utp - 200, 4096)])) : PS) m) as X.
    apply X; [| reflexivity| exact IM]. cbn. rewrite <- (reservedZ_ref (TB:=TBu utp H)). reflexivity.
  - cbn [fh_blk fheap_init]. intros k Hk. rewrite lookup_empty in Hk. exfalso. apply Hk. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition hmalloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PS) (LB : list tblock) (n lo B : Z) (m : mem)
    (r : option hptr) (s' : PS) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp)
    /\ rw_cells ssegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' B
    /\ heap_presT (bv_unsigned tp) LB (bv_unsigned sp) m m'
    /\ s' = set_heap (ps_heap s') s
    /\ match r with
       | None => a0 = Z_to_bv 64 0 /\ errv' = Z_to_bv 64 ENOMEM /\ HEAPT (ps_heap s') (bv_unsigned tp) LB m'
       | Some q => exists A junk,
           a0 = Z_to_bv 64 A /\ hf_addr (ps_heap s') q = A /\ ~ In q (map tb_tok LB)
           /\ rblock_rangeu (bv_unsigned tp) A n
           /\ HEAPT (ps_heap s') (bv_unsigned tp) ((q, A, n) :: LB) m'
           /\ rw_cells ssegs m' A [CB (Z.to_nat n) junk]
       end.

Definition hmalloc_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PS) (LB : list tblock) (n lo B : Z) (errv : word),
  HEAPT (ps_heap s) (bv_unsigned tp) LB m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk ssegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RMALLOC_STACK ->
  rw_cells ssegs m (errno_addr tp) [C4 errv] ->
  mem_inv ssegs m ->
  a0 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  implM ssegs (hf_malloc n) s
        (hmalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RMALLOC_SYM) fc None m (seg_rom ssegs)).

Lemma ps_rest_eq_set_heap (s s' : PS) :
  @ps_rest PS fheap_AllocSt s' = @ps_rest PS fheap_AllocSt s ->
  fh_next (ps_heap s') = fh_next (ps_heap s) /\ fh_blk (ps_heap s') = fh_blk (ps_heap s) /\ s' = set_heap (ps_heap s') s.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  intros E. cbn in E.
  pose proof (f_equal (fun x => fst (fst x)) E) as E1. pose proof (f_equal (fun x => snd (fst x)) E) as E2. pose proof (f_equal snd E) as E3.
  cbn [fst snd] in E1, E2, E3. split; [exact E1|]. split; [exact E2|].
  destruct s as [h l o t], s' as [h' l' o' t']. unfold set_heap in E3 |- *. cbn in E3 |- *. inversion E3. subst. reflexivity.
Qed.

Lemma hmalloc_of_rmalloc : rmalloc_stmt_u (PState:=PS) (AS:=fheap_AllocSt) -> hmalloc_stmt.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros HM. intros until errv. intros (H & ids & HR & CR & ND & FR) AUX HB ST CLO LO ERR MI Ha0 Hn.
  unfold hf_malloc.
  eapply (implM_bind ssegs).
  { apply (HM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s (map (tgen ids) LB) n lo B errv);
      [exists H; exact HR| exact AUX| exact HB| exact ST| exact CLO| exact LO| exact ERR| exact MI| exact Ha0| exact Hn]. }
  intros r sA ms1 PO. cbn beta in PO. unfold rmalloc_postu in PO.
  destruct PO as (u0&u1&u2&b0&b1&b2&b3&b4&b5&b6&b7&u3&u4&u5&u6&m'&errv'&E&MI'&ST'&ERR'&AUX'&PR&RST&RES). subst ms1.
  destruct (ps_rest_eq_set_heap s sA RST) as (EN & EB & ES1).
  destruct r as [pf|].
  - destruct RES as (c & off & A & junk & Epf & EA & EC & BR & (H1 & HR1) & CH).
    lazymatch goal with |- implM _ _ _ _ ?msX => set (ms1 := msX) end.
    unfold tok_fresh.
    set (h' := mkFH (fh_m (ps_heap sA)) (fh_brk (ps_heap sA)) (N.succ (fh_next (ps_heap sA))) (<[fh_next (ps_heap sA) := (pf, n)]> (fh_blk (ps_heap sA)))).
    eapply (implM_bind ssegs _ _ _ (fun k s4 ms4 => k = fh_next (ps_heap sA) /\ s4 = set_heap h' sA /\ ms4 = ms1)).
    { eapply (implM_bind ssegs _ _ _ (fun a s' ms' => a = sA /\ s' = sA /\ ms' = ms1)); [apply implM_get; apply evt_done; repeat split; reflexivity|].
      intros sB sB' ms2 (-> & -> & ->). cbv beta zeta.
      eapply (implM_bind ssegs _ _ _ (fun _ s' ms' => s' = set_heap h' sA /\ ms' = ms1)); [apply implM_upd; apply evt_done; split; reflexivity|].
      intros [] sC ms3 [-> ->]. apply implM_ret. apply evt_done. repeat split; reflexivity. }
    intros k sD ms4 (-> & -> & ->). apply implM_ret. apply evt_done.
    unfold hmalloc_post. exists u0,u1,u2,b0,b1,b2,b3,b4,b5,b6,b7,u3,u4,u5,u6,m',errv'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|].
    split; [eapply heap_presT_of; exact PR|].
    split. { subst h'. rewrite ES1. destruct s; reflexivity. }
    set (q := fh_next (ps_heap sA)).
    assert (NI : ~ In q (map tb_tok LB)).
    { intros Hin. apply in_map_iff in Hin. destruct Hin as (t & Et & Ht).
      pose proof (CR t Ht) as E3. rewrite Et in E3.
      specialize (FR q ltac:(rewrite E3; discriminate)). subst q. rewrite EN in FR. lia. }
    exists A, junk. split; [exact EA|]. cbn [ps_heap set_heap].
    split. { unfold hf_addr. cbn [fh_blk fh_m]. subst q. rewrite lookup_insert_eq. rewrite EC. subst h'. rewrite ES1. destruct s; reflexivity. }
    split; [exact NI|]. split; [exact BR|]. split; [|exact CH].
    set (ids' := fun k => if (k =? q)%N then (c, off) else ids k).
    assert (MG : map (tgen ids') LB = map (tgen ids) LB).
    { apply map_ext_in. intros t Ht. unfold tgen, ids'. destruct (N.eqb_spec (tb_tok t) q) as [E|NE]; [|reflexivity].
      exfalso. apply NI. rewrite <- E. apply in_map. exact Ht. }
    exists H1, ids'. split; [|split; [|split]].
    + cbn [map]. rewrite MG. unfold tgen at 1, ids'. cbn [tb_tok tb_addr tb_size fst snd]. rewrite N.eqb_refl. exact HR1.
    + intros t [<-|Ht].
      * subst h'. cbn [tb_tok tb_size fst snd fh_blk]. rewrite lookup_insert_eq. unfold tgen, ids'. cbn [tb_tok fst snd]. rewrite N.eqb_refl.
        unfold blk_ptr, blk_slot, blk_id. cbn [fst snd]. rewrite <- Epf. reflexivity.
      * subst h'. cbn [fh_blk]. assert (NEt : tb_tok t <> q). { intros Eq. apply NI. rewrite <- Eq. apply in_map. exact Ht. }
        rewrite lookup_insert_ne by (intros X; apply NEt; symmetry; exact X). rewrite EB.
        unfold tgen, ids'. rewrite (proj2 (N.eqb_neq _ _) NEt). exact (CR t Ht).
    + cbn [map tb_tok fst snd]. constructor; [exact NI| exact ND].
    + subst h'. cbn [fh_blk fh_next]. intros k' Hk'. destruct (N.eq_dec k' q) as [->|NE]; [unfold q; lia|].
      rewrite lookup_insert_ne in Hk' by (intros X; apply NE; symmetry; exact X). rewrite EB in Hk'. specialize (FR k' Hk'). unfold q. rewrite EN. lia.
  - destruct RES as (EA & EEN & H1 & HR1).
    apply implM_ret. apply evt_done.
    unfold hmalloc_post. exists u0,u1,u2,b0,b1,b2,b3,b4,b5,b6,b7,u3,u4,u5,u6,m',errv'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|].
    split; [eapply heap_presT_of; exact PR|].
    split; [exact ES1|]. split; [exact EA|]. split; [exact EEN|].
    exists H1, ids. split; [exact HR1|]. split; [|split; [exact ND| rewrite EB, EN; exact FR]].
    intros t Ht. rewrite EB. exact (CR t Ht).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition hfree_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PS) (LB : list tblock) (q : hptr) (lo B : Z) (errv : word) (m : mem)
    (r : unit) (s' : PS) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp)
    /\ rw_cells ssegs m' (errno_addr tp) [C4 errv]
    /\ rauxv_ok m' B
    /\ heap_presT (bv_unsigned tp) (lbt_remove q LB) (bv_unsigned sp) m m'
    /\ s' = set_heap (ps_heap s') s
    /\ HEAPT (ps_heap s') (bv_unsigned tp) (lbt_remove q LB) m'.

Definition hfree_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PS) (LB : list tblock) (q : hptr) (A n lo B : Z) (errv : word),
  HEAPT (ps_heap s) (bv_unsigned tp) LB m -> In (q, A, n) LB ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk ssegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RFREE_STACK ->
  rw_cells ssegs m (errno_addr tp) [C4 errv] ->
  mem_inv ssegs m ->
  a0 = Z_to_bv 64 A ->
  implM ssegs (hf_free q) s
        (hfree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB q lo B errv m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RFREE_SYM) fc None m (seg_rom ssegs)).

Lemma filter_map_swap' {A B} (f : B -> bool) (g : A -> B) l : filter f (map g l) = map g (List.filter (fun a => f (g a)) l).
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts. induction l as [|x l IH]; [reflexivity|]. cbn. destruct (f (g x)); cbn; rewrite IH; reflexivity. Qed.
Lemma filter_ext_in' {A} (f g : A -> bool) l : (forall x, In x l -> f x = g x) -> List.filter f l = List.filter g l.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  induction l as [|x l IH]; intros H; [reflexivity|]. cbn. rewrite (H x (or_introl eq_refl)).
  rewrite (IH (fun y Hy => H y (or_intror Hy))). reflexivity.
Qed.
Lemma bptr_eqb_true p q : bptr_eqb p q = true <-> p = q.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  unfold bptr_eqb, aptr_eqb. rewrite !Bool.andb_true_iff, N.eqb_eq, !Z.eqb_eq.
  destruct p as [[r o] i], q as [[r' o'] i']; cbn; split; [intros [[-> ->] ->]; reflexivity| intros E; inversion E; auto].
Qed.

Lemma NoDup_filter_map' {A B} (f : A -> B) (g : A -> bool) l : List.NoDup (map f l) -> List.NoDup (map f (List.filter g l)).
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  induction l as [|x l IH]; intros ND; [constructor|]. cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND].
  cbn. destruct (g x); cbn; [| exact (IH ND)]. constructor; [| exact (IH ND)].
  intros Hin. apply NI. apply in_map_iff in Hin. destruct Hin as (y & <- & Hy). apply filter_In in Hy. apply in_map. tauto.
Qed.

Lemma hfree_of_rfree : rfree_stmt_u (PState:=PS) (AS:=fheap_AllocSt) -> (forall TB : TlsBase, RHEAP_blocks_nodup_stmt (PState:=PS) (AS:=fheap_AllocSt) (TB:=TB)) -> hfree_stmt.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros HF HND. intros until errv. intros (H & ids & HR & CR & ND & FR) HIN AUX HB ST CLO LO ERR MI Ha0.
  lazymatch goal with |- implM _ _ _ _ ?msX => set (ms0 := msX) end.
  unfold hf_free, tok_lookup.
  eapply (implM_bind ssegs _ _ _ (fun b sX msX => b = Some (blk_ptr (tgen ids (q, A, n)), n) /\ sX = s /\ msX = ms0)).
  { eapply (implM_bind ssegs _ _ _ (fun a s' ms' => a = s /\ s' = s /\ ms' = ms0)); [apply implM_get; apply evt_done; repeat split; reflexivity|].
    intros sB sB' ms2 (-> & -> & ->). apply implM_ret. apply evt_done. split; [| split; reflexivity].
    rewrite (CR _ HIN). reflexivity. }
  intros b sB msB (-> & -> & ->). cbv beta iota.
  assert (NDg : List.NoDup (map (fun x => ids (tb_tok x)) LB)).
  { pose proof (HND (TBu (bv_unsigned tp) H) (ps_init (ps_heap s) : PS) (map (tgen ids) LB) m HR) as X. rewrite map_map in X. exact X. }
  eapply (implM_bind ssegs).
  { unfold blk_ptr, tgen, blk_slot, blk_id. cbn [fst snd tb_tok].
    apply (HF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s (map (tgen ids) LB) (ids q) A n lo B errv);
      [exists H; exact HR| apply in_map_iff; exists (q, A, n); split; [reflexivity| exact HIN]| exact AUX| exact HB| exact ST| exact CLO| exact LO| exact ERR| exact MI| exact Ha0]. }
  intros [] sA ms1 PO. cbn beta in PO. unfold rfree_postu in PO.
  destruct PO as (u0&u1&u2&b0&b1&b2&b3&b4&b5&b6&b7&u3&u4&u5&u6&m'&E&MI'&ST'&ERR'&AUX'&PR&RST&(H1 & HR1)). subst ms1.
  destruct (ps_rest_eq_set_heap s sA RST) as (EN & EB & ES1).
  assert (MG : map (tgen ids) (lbt_remove q LB) = lb_remove (ids q) (map (tgen ids) LB)).
  { unfold lb_remove, lbt_remove. rewrite filter_map_swap'. f_equal. apply filter_ext_in'.
    intros t Ht. unfold tgen, blk_id. cbn [fst]. f_equal.
    destruct (N.eqb_spec (tb_tok t) q) as [Et|NEt].
    - rewrite Et. symmetry. apply (proj2 (bptr_eqb_true _ _)). reflexivity.
    - destruct (bptr_eqb (ids (tb_tok t)) (ids q)) eqn:Eb; [|reflexivity]. exfalso. apply NEt.
      apply (proj1 (bptr_eqb_true _ _)) in Eb.
      assert (t = (q, A, n)) as ->; [| reflexivity].
      apply (NoDup_map_inj' (fun x => ids (tb_tok x)) LB t (q, A, n) NDg Ht HIN). cbn [tb_tok fst]. exact Eb. }
  unfold tok_drop. apply implM_upd. apply evt_done.
  unfold hfree_post. exists u0,u1,u2,b0,b1,b2,b3,b4,b5,b6,b7,u3,u4,u5,u6,m'.
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|].
  split; [eapply (heap_presT_of ids); rewrite MG; exact PR|].
  split. { rewrite ES1. destruct s; reflexivity. }
  cbn [ps_heap set_heap]. exists H1, ids. split; [| split; [| split]].
  - cbn [fh_m fh_brk]. rewrite MG. rewrite ES1 in HR1. destruct s; cbn in HR1 |- *. exact HR1.
  - intros t Ht. cbn [fh_blk]. unfold lbt_remove in Ht. apply filter_In in Ht. destruct Ht as [Ht Hne].
    destruct (N.eqb_spec (tb_tok t) q) as [Et|NEt]; [discriminate|].
    rewrite lookup_delete_ne by (intros X; apply NEt; symmetry; exact X). rewrite EB. exact (CR t Ht).
  - unfold lbt_remove. apply NoDup_filter_map'. exact ND.
  - cbn [fh_blk fh_next]. intros k Hk. destruct (N.eq_dec k q) as [->|NE].
    + rewrite lookup_delete_eq in Hk. exfalso. apply Hk. reflexivity.
    + rewrite lookup_delete_ne in Hk by (intros X; apply NE; symmetry; exact X). rewrite EB in Hk. rewrite EN. exact (FR k Hk).
Qed.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.SFModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.HeapFull.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.TlsBaseU OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocHINV OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.Malloc_iface.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MSecret.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

#[local] Notation PS := (PState fheap hptr).
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Definition tblock : Type := (hptr * Z * Z)%type.     (* [comment removed for export] *)
Definition tb_tok (t : tblock) : hptr := fst (fst t).
Definition tb_addr (t : tblock) : Z := snd (fst t).
Definition tb_size (t : tblock) : Z := snd t.

(* [comment removed for export] *)
Definition tgen (ids : hptr -> bptr) (t : tblock) : block := (ids (tb_tok t), tb_addr t, tb_size t).

(* [comment removed for export] *)
Definition HEAPT (h : fheap) (utp : Z) (LB : list tblock) (m : mem) : Prop :=
  exists (H : tls_ok (utp - 200)) (ids : hptr -> bptr),
       RHEAPm (TB:=TBu utp H) (fh_m h) (fh_brk h) (map (tgen ids) LB) m
    /\ (forall t, In t LB -> fh_blk h !! (tb_tok t) = Some (blk_ptr (tgen ids t), tb_size t))
    /\ List.NoDup (map tb_tok LB)
    /\ (forall k, fh_blk h !! k <> None -> (k < fh_next h)%N).

Definition in_blockT (LB : list tblock) (a : Z) : Prop :=
  exists t, In t LB /\ tb_addr t <= a < tb_addr t + tb_size t.

Definition heap_presT (utp : Z) (LB : list tblock) (SP : Z) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 ->
    (SP <= a \/ (0x22000 <= a < 0x56000 /\ ~ (RMLOCK <= a < RCTX + 936) /\ ~ (utp - 164 <= a < utp - 160)) \/ in_blockT LB a
     \/ (utp - 200 <= a < utp - 200 + 4096 /\ ~ (utp - 164 <= a < utp - 160))) ->
    m' (wa a) = m (wa a) /\ (wview usegs m (wa a) <> None -> wview usegs m' (wa a) <> None).

Definition lbt_remove (q : hptr) (LB : list tblock) : list tblock :=
  List.filter (fun t => negb (N.eqb (tb_tok t) q)) LB.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_blockT_iff ids LB a : in_blockT LB a <-> in_block (map (tgen ids) LB) a.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  split.
  - intros (t & Ht & Hr). exists (tgen ids t). split; [apply in_map; exact Ht| exact Hr].
  - intros (b & Hb & Hr). apply in_map_iff in Hb. destruct Hb as (t & <- & Ht). exists t. split; [exact Ht| exact Hr].
Qed.

Lemma heap_presT_of ids utp LB SP m m' :
  rheap_presu utp (map (tgen ids) LB) SP m m' -> heap_presT utp LB SP m m'.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  intros HP a Ha Hc. apply HP; [exact Ha|].
  destruct Hc as [X|[X|[X|X]]]; [tauto|tauto| |tauto]. right; right; left. apply (proj1 (in_blockT_iff ids LB a)). exact X.
Qed.

Lemma NoDup_map_inj' {A B} (f : A -> B) l x y : List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  induction l as [|z l IH]; intros ND Hx Hy E; [destruct Hx|].
  cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND].
  destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity| | | exact (IH ND Hx Hy E)].
  - exfalso. apply NI. rewrite E. apply in_map. exact Hy.
  - exfalso. apply NI. rewrite <- E. apply in_map. exact Hx.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma HEAPT_perm : forall h utp LB LB' m, HEAPT h utp LB m -> Permutation LB LB' -> HEAPT h utp LB' m.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros h utp LB LB' m (H & ids & HR & CR & ND & FR) P.
  exists H, ids. split; [| split; [intros t Ht; apply CR; eapply Permutation_in; [apply Permutation_sym; exact P| exact Ht]| split; [| exact FR]]].
  - destruct HR as (LB0 & P0 & MR & HI). exists LB0. split; [| split; [exact MR| exact HI]].
    eapply Permutation_trans; [exact P0| apply Permutation_map; exact P].
  - eapply Permutation_NoDup; [apply Permutation_map; exact P| exact ND].
Qed.

Lemma HEAPT_nodup : forall h utp LB m, HEAPT h utp LB m -> List.NoDup (map tb_tok LB).
Proof using Type. pin_using tt. ceil_facts. msec_facts. intros h utp LB m (H & ids & HR & CR & ND & FR). exact ND. Qed.

Lemma HEAPT_addr_of : (forall TB : TlsBase, RHEAP_block_range_stmt (PState:=PS) (AS:=fheap_AllocSt) (TB:=TB)) ->
  forall h utp LB m q A n, HEAPT h utp LB m -> In (q, A, n) LB -> hf_addr h q = A.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros HBR h utp LB m q A n (H & ids & HR & CR & ND & FR) Hin.
  unfold hf_addr. rewrite (CR _ Hin). cbn [tb_tok tb_size tgen tb_addr fst snd].
  destruct (HBR (TBu utp H) (ps_init h : PS) (map (tgen ids) LB) m (ids q) A n) as [_ EA]; [exact HR| |].
  - apply in_map_iff. exists (q, A, n). split; [reflexivity| exact Hin].
  - cbn in EA. unfold blk_ptr, blk_slot, blk_id, tgen. cbn [fst snd tb_tok]. symmetry. exact EA.
Qed.

Lemma HEAPT_range_of : (forall TB : TlsBase, RHEAP_block_range_stmt (PState:=PS) (AS:=fheap_AllocSt) (TB:=TB)) ->
  forall h utp LB m q A n, HEAPT h utp LB m -> In (q, A, n) LB -> rblock_rangeu utp A n.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros HBR h utp LB m q A n (H & ids & HR & CR & ND & FR) Hin.
  destruct (HBR (TBu utp H) (ps_init h : PS) (map (tgen ids) LB) m (ids q) A n) as [BR _]; [exact HR| |].
  - apply in_map_iff. exists (q, A, n). split; [reflexivity| exact Hin].
  - exact BR.
Qed.

Definition HEAPT_disjoint_of__stmt : Prop := (forall TB : TlsBase, RHEAP_blocks_disjoint_stmt (PState:=PS) (AS:=fheap_AllocSt) (TB:=TB)) ->
  (forall TB : TlsBase, RHEAP_blocks_nodup_stmt (PState:=PS) (AS:=fheap_AllocSt) (TB:=TB)) ->
  forall h utp LB m t1 t2, HEAPT h utp LB m -> In t1 LB -> In t2 LB -> tb_tok t1 <> tb_tok t2 ->
    tb_addr t1 + tb_size t1 <= tb_addr t2 \/ tb_addr t2 + tb_size t2 <= tb_addr t1.
Section Sz5.
Variables h utp LB m t1 t2 : ltac2:(SecDiet.SzSec.tyM 'HEAPT_disjoint_of__stmt "hhvvvvvv" @h).
Lemma HEAPT_disjoint_of__body : ltac2:(SecDiet.SzSec.bodyP 'HEAPT_disjoint_of__stmt "hhvvvvvv").
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros HBD HND (H & ids & HR & CR & ND & FR) H1 H2 NE.
  apply (HBD (TBu utp H) (ps_init h : PS) (map (tgen ids) LB) m (tgen ids t1) (tgen ids t2)); [exact HR| apply in_map; exact H1| apply in_map; exact H2|].
  intros E. apply NE. cbn [blk_id tgen fst] in E.
  pose proof (HND (TBu utp H) (ps_init h : PS) (map (tgen ids) LB) m HR) as NDg. rewrite map_map in NDg. cbn [blk_id tgen fst] in NDg.
  assert (t1 = t2) as ->; [| reflexivity].
  apply (NoDup_map_inj' (fun x => ids (tb_tok x)) LB t1 t2 NDg H1 H2 E).
Qed.
End Sz5.
Lemma HEAPT_disjoint_of : ltac:(let t := eval cbv delta [HEAPT_disjoint_of__stmt] in HEAPT_disjoint_of__stmt in exact t).
Proof using Type. intros HBD HND h utp LB m t1 t2. ltac2:(SecDiet.SzSec.closeP 'HEAPT_disjoint_of__body "hhvvvvvv"). Qed.

Definition client_write_okT (utp : Z) (LB : list tblock) (iv : Z * Z) : Prop :=
  alloc_ceiling <= fst iv
  \/ (0x22000 <= fst iv /\ snd iv <= 0x56000 /\ (snd iv <= RLIBC \/ RCTX + 936 <= fst iv)
      /\ (snd iv <= RSSP_GUARD \/ RSSP_GUARD + 8 <= fst iv) /\ (snd iv <= RGOT_SSP \/ RGOT_SSP + 8 <= fst iv))
  \/ (exists t, In t LB /\ tb_addr t <= fst iv /\ snd iv <= tb_addr t + tb_size t)
  \/ (utp - 200 <= fst iv /\ snd iv <= utp - 200 + 4096).

Definition HEAPT_frame_of__stmt : Prop := (forall TB : TlsBase, RHEAP_frame_stmt (PState:=PS) (AS:=fheap_AllocSt) (TB:=TB)) ->
  forall h utp LB m m' W,
    HEAPT h utp LB m -> munch W m m' -> wmono usegs m m' -> Forall (client_write_okT utp LB) W -> HEAPT h utp LB m'.
Section Sz6.
Variables h utp LB m m' W : ltac2:(SecDiet.SzSec.tyM 'HEAPT_frame_of__stmt "hvvvvvv" @h).
Lemma HEAPT_frame_of__body : ltac2:(SecDiet.SzSec.bodyP 'HEAPT_frame_of__stmt "hvvvvvv").
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros HF (H & ids & HR & CR & ND & FR) MU WM FW.
  exists H, ids. split; [| split; [exact CR| split; [exact ND| exact FR]]].
  apply (HF (TBu utp H) (ps_init h : PS) (map (tgen ids) LB) m m' W HR MU WM).
  eapply Forall_impl; [|exact FW]. intros iv Hiv. unfold rclient_write_ok. cbn [the_tb TBu].
  destruct Hiv as [X|[X|[(t & Ht & X1 & X2)|X]]]; [left; exact X| right; left; exact X| | right; right; right; exact X].
  right; right; left. exists (tgen ids t). split; [apply in_map; exact Ht|]. cbn. lia.
Qed.
End Sz6.
Lemma HEAPT_frame_of : ltac:(let t := eval cbv delta [HEAPT_frame_of__stmt] in HEAPT_frame_of__stmt in exact t).
Proof using Type. intros HF h utp LB m m' W. ltac2:(SecDiet.SzSec.closeP 'HEAPT_frame_of__body "hvvvvvv"). Qed.

Lemma HEAPT_init_of : (forall TB : TlsBase, RHEAP_init_stmt (PState:=PS) (AS:=fheap_AllocSt) (TB:=TB)) ->
  forall utp m (H : tls_ok (utp - 200)), rheap_init_mem m ->
    HEAPT (fheap_init msecret (reservedZ usegs ++ [(utp - 200, 4096)])) utp [] m.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros HI utp m H IM. exists H, (fun _ => ((0%N, 0), 0)). split; [| split; [intros t []| split; [constructor|]]].
  - cbn [map fh_m fh_brk fheap_init].
    pose proof (HI (TBu utp H) (ps_init (fheap_init msecret (reservedZ usegs ++ [(utp - 200, 4096)])) : PS) m) as X.
    apply X; [| reflexivity| exact IM]. cbn. rewrite <- (reservedZ_ref (TB:=TBu utp H)). reflexivity.
  - cbn [fh_blk fheap_init]. intros k Hk. rewrite lookup_empty in Hk. exfalso. apply Hk. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition hmalloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PS) (LB : list tblock) (n lo B : Z) (m : mem)
    (r : option hptr) (s' : PS) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' B
    /\ heap_presT (bv_unsigned tp) LB (bv_unsigned sp) m m'
    /\ s' = set_heap (ps_heap s') s
    /\ match r with
       | None => a0 = Z_to_bv 64 0 /\ errv' = Z_to_bv 64 ENOMEM /\ HEAPT (ps_heap s') (bv_unsigned tp) LB m'
       | Some q => exists A junk,
           a0 = Z_to_bv 64 A /\ hf_addr (ps_heap s') q = A /\ ~ In q (map tb_tok LB)
           /\ rblock_rangeu (bv_unsigned tp) A n
           /\ HEAPT (ps_heap s') (bv_unsigned tp) ((q, A, n) :: LB) m'
           /\ rw_cells usegs m' A [CB (Z.to_nat n) junk]
       end.

Definition hmalloc_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PS) (LB : list tblock) (n lo B : Z) (errv : word),
  HEAPT (ps_heap s) (bv_unsigned tp) LB m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RMALLOC_STACK ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  implM usegs (hf_malloc n) s
        (hmalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RMALLOC_SYM) fc None m (seg_rom usegs)).

Lemma ps_rest_eq_set_heap (s s' : PS) :
  @ps_rest PS fheap_AllocSt s' = @ps_rest PS fheap_AllocSt s ->
  fh_next (ps_heap s') = fh_next (ps_heap s) /\ fh_blk (ps_heap s') = fh_blk (ps_heap s) /\ s' = set_heap (ps_heap s') s.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  intros E. cbn in E.
  pose proof (f_equal (fun x => fst (fst x)) E) as E1. pose proof (f_equal (fun x => snd (fst x)) E) as E2. pose proof (f_equal snd E) as E3.
  cbn [fst snd] in E1, E2, E3. split; [exact E1|]. split; [exact E2|].
  destruct s as [h l o t], s' as [h' l' o' t']. unfold set_heap in E3 |- *. cbn in E3 |- *. inversion E3. subst. reflexivity.
Qed.

Definition hmalloc_of_rmalloc__stmt : Prop := rmalloc_stmt_u (PState:=PS) (AS:=fheap_AllocSt) -> hmalloc_stmt.
Section Sz8.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv : ltac2:(SecDiet.SzSec.tyM 'hmalloc_of_rmalloc__stmt "hvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma hmalloc_of_rmalloc__body : ltac2:(SecDiet.SzSec.bodyP 'hmalloc_of_rmalloc__stmt "hvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros HM.
 intros (H & ids & HR & CR & ND & FR) AUX HB ST CLO LO ERR MI Ha0 Hn.
  unfold hf_malloc.
  eapply (implM_bind usegs).
  { apply (HM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s (map (tgen ids) LB) n lo B errv);
      [exists H; exact HR| exact AUX| exact HB| exact ST| exact CLO| exact LO| exact ERR| exact MI| exact Ha0| exact Hn]. }
  intros r sA ms1 PO. cbn beta in PO. unfold rmalloc_postu in PO.
  destruct PO as (u0&u1&u2&b0&b1&b2&b3&b4&b5&b6&b7&u3&u4&u5&u6&m'&errv'&E&MI'&ST'&ERR'&AUX'&PR&RST&RES). subst ms1.
  destruct (ps_rest_eq_set_heap s sA RST) as (EN & EB & ES1).
  destruct r as [pf|].
  - destruct RES as (c & off & A & junk & Epf & EA & EC & BR & (H1 & HR1) & CH).
    lazymatch goal with |- implM _ _ _ _ ?msX => set (ms1 := msX) end.
    unfold tok_fresh.
    set (h' := mkFH (fh_m (ps_heap sA)) (fh_brk (ps_heap sA)) (N.succ (fh_next (ps_heap sA))) (<[fh_next (ps_heap sA) := (pf, n)]> (fh_blk (ps_heap sA)))).
    eapply (implM_bind usegs _ _ _ (fun k s4 ms4 => k = fh_next (ps_heap sA) /\ s4 = set_heap h' sA /\ ms4 = ms1)).
    { eapply (implM_bind usegs _ _ _ (fun a s' ms' => a = sA /\ s' = sA /\ ms' = ms1)); [apply implM_get; apply evt_done; repeat split; reflexivity|].
      intros sB sB' ms2 (-> & -> & ->). cbv beta zeta.
      eapply (implM_bind usegs _ _ _ (fun _ s' ms' => s' = set_heap h' sA /\ ms' = ms1)); [apply implM_upd; apply evt_done; split; reflexivity|].
      intros [] sC ms3 [-> ->]. apply implM_ret. apply evt_done. repeat split; reflexivity. }
    intros k sD ms4 (-> & -> & ->). apply implM_ret. apply evt_done.
    unfold hmalloc_post. exists u0,u1,u2,b0,b1,b2,b3,b4,b5,b6,b7,u3,u4,u5,u6,m',errv'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|].
    split; [eapply heap_presT_of; exact PR|].
    split. { subst h'. rewrite ES1. destruct s; reflexivity. }
    set (q := fh_next (ps_heap sA)).
    assert (NI : ~ In q (map tb_tok LB)).
    { intros Hin. apply in_map_iff in Hin. destruct Hin as (t & Et & Ht).
      pose proof (CR t Ht) as E3. rewrite Et in E3.
      specialize (FR q ltac:(rewrite E3; discriminate)). subst q. rewrite EN in FR. lia. }
    exists A, junk. split; [exact EA|]. cbn [ps_heap set_heap].
    split. { unfold hf_addr. cbn [fh_blk fh_m]. subst q. rewrite lookup_insert_eq. rewrite EC. subst h'. rewrite ES1. destruct s; reflexivity. }
    split; [exact NI|]. split; [exact BR|]. split; [|exact CH].
    set (ids' := fun k => if (k =? q)%N then (c, off) else ids k).
    assert (MG : map (tgen ids') LB = map (tgen ids) LB).
    { apply map_ext_in. intros t Ht. unfold tgen, ids'. destruct (N.eqb_spec (tb_tok t) q) as [E|NE]; [|reflexivity].
      exfalso. apply NI. rewrite <- E. apply in_map. exact Ht. }
    exists H1, ids'. split; [|split; [|split]].
    + cbn [map]. rewrite MG. unfold tgen at 1, ids'. cbn [tb_tok tb_addr tb_size fst snd]. rewrite N.eqb_refl. exact HR1.
    + intros t [<-|Ht].
      * subst h'. cbn [tb_tok tb_size fst snd fh_blk]. rewrite lookup_insert_eq. unfold tgen, ids'. cbn [tb_tok fst snd]. rewrite N.eqb_refl.
        unfold blk_ptr, blk_slot, blk_id. cbn [fst snd]. rewrite <- Epf. reflexivity.
      * subst h'. cbn [fh_blk]. assert (NEt : tb_tok t <> q). { intros Eq. apply NI. rewrite <- Eq. apply in_map. exact Ht. }
        rewrite lookup_insert_ne by (intros X; apply NEt; symmetry; exact X). rewrite EB.
        unfold tgen, ids'. rewrite (proj2 (N.eqb_neq _ _) NEt). exact (CR t Ht).
    + cbn [map tb_tok fst snd]. constructor; [exact NI| exact ND].
    + subst h'. cbn [fh_blk fh_next]. intros k' Hk'. destruct (N.eq_dec k' q) as [->|NE]; [unfold q; lia|].
      rewrite lookup_insert_ne in Hk' by (intros X; apply NE; symmetry; exact X). rewrite EB in Hk'. specialize (FR k' Hk'). unfold q. rewrite EN. lia.
  - destruct RES as (EA & EEN & H1 & HR1).
    apply implM_ret. apply evt_done.
    unfold hmalloc_post. exists u0,u1,u2,b0,b1,b2,b3,b4,b5,b6,b7,u3,u4,u5,u6,m',errv'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|].
    split; [eapply heap_presT_of; exact PR|].
    split; [exact ES1|]. split; [exact EA|]. split; [exact EEN|].
    exists H1, ids. split; [exact HR1|]. split; [|split; [exact ND| rewrite EB, EN; exact FR]].
    intros t Ht. rewrite EB. exact (CR t Ht).
Qed.
End Sz8.
Lemma hmalloc_of_rmalloc : ltac:(let t := eval cbv delta [hmalloc_of_rmalloc__stmt] in hmalloc_of_rmalloc__stmt in exact t).
Proof using Type. intros HM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv. ltac2:(SecDiet.SzSec.closeP 'hmalloc_of_rmalloc__body "hvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition hfree_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PS) (LB : list tblock) (q : hptr) (lo B : Z) (errv : word) (m : mem)
    (r : unit) (s' : PS) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 errv]
    /\ rauxv_ok m' B
    /\ heap_presT (bv_unsigned tp) (lbt_remove q LB) (bv_unsigned sp) m m'
    /\ s' = set_heap (ps_heap s') s
    /\ HEAPT (ps_heap s') (bv_unsigned tp) (lbt_remove q LB) m'.

Definition hfree_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PS) (LB : list tblock) (q : hptr) (A n lo B : Z) (errv : word),
  HEAPT (ps_heap s) (bv_unsigned tp) LB m -> In (q, A, n) LB ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RFREE_STACK ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 A ->
  implM usegs (hf_free q) s
        (hfree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB q lo B errv m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RFREE_SYM) fc None m (seg_rom usegs)).

Lemma filter_map_swap' {A B} (f : B -> bool) (g : A -> B) l : filter f (map g l) = map g (List.filter (fun a => f (g a)) l).
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts. induction l as [|x l IH]; [reflexivity|]. cbn. destruct (f (g x)); cbn; rewrite IH; reflexivity. Qed.
Lemma filter_ext_in' {A} (f g : A -> bool) l : (forall x, In x l -> f x = g x) -> List.filter f l = List.filter g l.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  induction l as [|x l IH]; intros H; [reflexivity|]. cbn. rewrite (H x (or_introl eq_refl)).
  rewrite (IH (fun y Hy => H y (or_intror Hy))). reflexivity.
Qed.
Lemma bptr_eqb_true p q : bptr_eqb p q = true <-> p = q.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  unfold bptr_eqb, aptr_eqb. rewrite !Bool.andb_true_iff, N.eqb_eq, !Z.eqb_eq.
  destruct p as [[r o] i], q as [[r' o'] i']; cbn; split; [intros [[-> ->] ->]; reflexivity| intros E; inversion E; auto].
Qed.

Lemma NoDup_filter_map' {A B} (f : A -> B) (g : A -> bool) l : List.NoDup (map f l) -> List.NoDup (map f (List.filter g l)).
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  induction l as [|x l IH]; intros ND; [constructor|]. cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND].
  cbn. destruct (g x); cbn; [| exact (IH ND)]. constructor; [| exact (IH ND)].
  intros Hin. apply NI. apply in_map_iff in Hin. destruct Hin as (y & <- & Hy). apply filter_In in Hy. apply in_map. tauto.
Qed.

Definition hfree_of_rfree__stmt : Prop := rfree_stmt_u (PState:=PS) (AS:=fheap_AllocSt) -> (forall TB : TlsBase, RHEAP_blocks_nodup_stmt (PState:=PS) (AS:=fheap_AllocSt) (TB:=TB)) -> hfree_stmt.
Section Sz9.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB q A n lo B errv : ltac2:(SecDiet.SzSec.tyM 'hfree_of_rfree__stmt "hhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma hfree_of_rfree__body : ltac2:(SecDiet.SzSec.bodyP 'hfree_of_rfree__stmt "hhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros HF HND.
 intros (H & ids & HR & CR & ND & FR) HIN AUX HB ST CLO LO ERR MI Ha0.
  lazymatch goal with |- implM _ _ _ _ ?msX => set (ms0 := msX) end.
  unfold hf_free, tok_lookup.
  eapply (implM_bind usegs _ _ _ (fun b sX msX => b = Some (blk_ptr (tgen ids (q, A, n)), n) /\ sX = s /\ msX = ms0)).
  { eapply (implM_bind usegs _ _ _ (fun a s' ms' => a = s /\ s' = s /\ ms' = ms0)); [apply implM_get; apply evt_done; repeat split; reflexivity|].
    intros sB sB' ms2 (-> & -> & ->). apply implM_ret. apply evt_done. split; [| split; reflexivity].
    rewrite (CR _ HIN). reflexivity. }
  intros b sB msB (-> & -> & ->). cbv beta iota.
  assert (NDg : List.NoDup (map (fun x => ids (tb_tok x)) LB)).
  { pose proof (HND (TBu (bv_unsigned tp) H) (ps_init (ps_heap s) : PS) (map (tgen ids) LB) m HR) as X. rewrite map_map in X. exact X. }
  eapply (implM_bind usegs).
  { unfold blk_ptr, tgen, blk_slot, blk_id. cbn [fst snd tb_tok].
    apply (HF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s (map (tgen ids) LB) (ids q) A n lo B errv);
      [exists H; exact HR| apply in_map_iff; exists (q, A, n); split; [reflexivity| exact HIN]| exact AUX| exact HB| exact ST| exact CLO| exact LO| exact ERR| exact MI| exact Ha0]. }
  intros [] sA ms1 PO. cbn beta in PO. unfold rfree_postu in PO.
  destruct PO as (u0&u1&u2&b0&b1&b2&b3&b4&b5&b6&b7&u3&u4&u5&u6&m'&E&MI'&ST'&ERR'&AUX'&PR&RST&(H1 & HR1)). subst ms1.
  destruct (ps_rest_eq_set_heap s sA RST) as (EN & EB & ES1).
  assert (MG : map (tgen ids) (lbt_remove q LB) = lb_remove (ids q) (map (tgen ids) LB)).
  { unfold lb_remove, lbt_remove. rewrite filter_map_swap'. f_equal. apply filter_ext_in'.
    intros t Ht. unfold tgen, blk_id. cbn [fst]. f_equal.
    destruct (N.eqb_spec (tb_tok t) q) as [Et|NEt].
    - rewrite Et. symmetry. apply (proj2 (bptr_eqb_true _ _)). reflexivity.
    - destruct (bptr_eqb (ids (tb_tok t)) (ids q)) eqn:Eb; [|reflexivity]. exfalso. apply NEt.
      apply (proj1 (bptr_eqb_true _ _)) in Eb.
      assert (t = (q, A, n)) as ->; [| reflexivity].
      apply (NoDup_map_inj' (fun x => ids (tb_tok x)) LB t (q, A, n) NDg Ht HIN). cbn [tb_tok fst]. exact Eb. }
  unfold tok_drop. apply implM_upd. apply evt_done.
  unfold hfree_post. exists u0,u1,u2,b0,b1,b2,b3,b4,b5,b6,b7,u3,u4,u5,u6,m'.
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|].
  split; [eapply (heap_presT_of ids); rewrite MG; exact PR|].
  split. { rewrite ES1. destruct s; reflexivity. }
  cbn [ps_heap set_heap]. exists H1, ids. split; [| split; [| split]].
  - cbn [fh_m fh_brk]. rewrite MG. rewrite ES1 in HR1. destruct s; cbn in HR1 |- *. exact HR1.
  - intros t Ht. cbn [fh_blk]. unfold lbt_remove in Ht. apply filter_In in Ht. destruct Ht as [Ht Hne].
    destruct (N.eqb_spec (tb_tok t) q) as [Et|NEt]; [discriminate|].
    rewrite lookup_delete_ne by (intros X; apply NEt; symmetry; exact X). rewrite EB. exact (CR t Ht).
  - unfold lbt_remove. apply NoDup_filter_map'. exact ND.
  - cbn [fh_blk fh_next]. intros k Hk. destruct (N.eq_dec k q) as [->|NE].
    + rewrite lookup_delete_eq in Hk. exfalso. apply Hk. reflexivity.
    + rewrite lookup_delete_ne in Hk by (intros X; apply NE; symmetry; exact X). rewrite EB in Hk. rewrite EN. exact (FR k Hk).
Qed.
End Sz9.
Lemma hfree_of_rfree : ltac:(let t := eval cbv delta [hfree_of_rfree__stmt] in hfree_of_rfree__stmt in exact t).
Proof using Type. intros HF HND ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB q A n lo B errv. ltac2:(SecDiet.SzSec.closeP 'hfree_of_rfree__body "hhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End WithCeil.
End TwB.
End RMalloc_ifaceT.

(* [comment removed for export] *)
Module RMalloc_ifaceTB.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog HeapFull. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.HeapFull.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBase MallocHINV. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.TlsBase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocHINV OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.Malloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_ifaceB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_ifaceT.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation PS := (PState fheap hptr).

(* [comment removed for export] *)

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Definition hcalloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PS) (LB : list tblock) (n lo B : Z) (m : mem)
    (r : option hptr) (s' : PS) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp)
    /\ rw_cells ssegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' B
    /\ heap_presT (bv_unsigned tp) LB (bv_unsigned sp) m m'
    /\ s' = set_heap (ps_heap s') s
    /\ match r with
       | None => a0 = Z_to_bv 64 0 /\ errv' = Z_to_bv 64 ENOMEM /\ HEAPT (ps_heap s') (bv_unsigned tp) LB m'
       | Some q => exists A,
           a0 = Z_to_bv 64 A /\ hf_addr (ps_heap s') q = A /\ ~ In q (map tb_tok LB)
           /\ rblock_rangeu (bv_unsigned tp) A n
           /\ HEAPT (ps_heap s') (bv_unsigned tp) ((q, A, n) :: LB) m'
           /\ rw_cells ssegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))]
       end.

Definition hcalloc_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PS) (LB : list tblock) (cnt sz lo B : Z) (errv : word),
  HEAPT (ps_heap s) (bv_unsigned tp) LB m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk ssegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RCALLOC_STACK ->
  rw_cells ssegs m (errno_addr tp) [C4 errv] ->
  mem_inv ssegs m ->
  a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 sz -> 0 <= cnt < 2^64 -> 0 <= sz < 2^64 -> cnt * sz <= RCALLOC_MAX ->
  implM ssegs (hf_calloc cnt sz) s
        (hcalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB (cnt * sz) lo B m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RCALLOC_SYM) fc None m (seg_rom ssegs)).


Definition hcalloc_of_rcalloc__stmt : Prop := rcalloc_stmt_u (PState:=PS) (AS:=fheap_AllocSt) -> hcalloc_stmt.
Section Sz1.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB cnt sz lo B errv : ltac2:(SecDiet.SzSec.tyM 'hcalloc_of_rcalloc__stmt "hvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma hcalloc_of_rcalloc__body : ltac2:(SecDiet.SzSec.bodyP 'hcalloc_of_rcalloc__stmt "hvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros HM.
 intros (H & ids & HR & CR & ND & FR) AUX HB ST CLO LO ERR MI Ha0 Ha1 Hc Hs Hmax.
  unfold hf_calloc.
  eapply (implM_bind ssegs).
  { apply (HM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s (map (tgen ids) LB) cnt sz lo B errv);
      [exists H; exact HR| exact AUX| exact HB| exact ST| exact CLO| exact LO| exact ERR| exact MI| exact Ha0| exact Ha1| exact Hc| exact Hs| exact Hmax]. }
  set (n := cnt * sz) in *.
  intros r sA ms1 PO. cbn beta in PO. unfold rcalloc_postu in PO.
  destruct PO as (u0&u1&u2&b0&b1&b2&b3&b4&b5&b6&b7&u3&u4&u5&u6&m'&errv'&E&MI'&ST'&ERR'&AUX'&PR&RST&RES). subst ms1.
  destruct (ps_rest_eq_set_heap s sA RST) as (EN & EB & ES1).
  destruct r as [pf|].
  - destruct RES as (c & off & A & Epf & EA & EC & BR & (H1 & HR1) & CH).
    lazymatch goal with |- implM _ _ _ _ ?msX => set (ms1 := msX) end.
    unfold tok_fresh.
    set (h' := mkFH (fh_m (ps_heap sA)) (fh_brk (ps_heap sA)) (N.succ (fh_next (ps_heap sA))) (<[fh_next (ps_heap sA) := (pf, n)]> (fh_blk (ps_heap sA)))).
    eapply (implM_bind ssegs _ _ _ (fun k s4 ms4 => k = fh_next (ps_heap sA) /\ s4 = set_heap h' sA /\ ms4 = ms1)).
    { eapply (implM_bind ssegs _ _ _ (fun a s' ms' => a = sA /\ s' = sA /\ ms' = ms1)); [apply implM_get; apply evt_done; repeat split; reflexivity|].
      intros sB sB' ms2 (-> & -> & ->). cbv beta zeta.
      eapply (implM_bind ssegs _ _ _ (fun _ s' ms' => s' = set_heap h' sA /\ ms' = ms1)); [apply implM_upd; apply evt_done; split; reflexivity|].
      intros [] sC ms3 [-> ->]. apply implM_ret. apply evt_done. repeat split; reflexivity. }
    intros k sD ms4 (-> & -> & ->). apply implM_ret. apply evt_done.
    unfold hcalloc_post. exists u0,u1,u2,b0,b1,b2,b3,b4,b5,b6,b7,u3,u4,u5,u6,m',errv'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|].
    split; [eapply heap_presT_of; exact PR|].
    split. { subst h'. rewrite ES1. destruct s; reflexivity. }
    set (q := fh_next (ps_heap sA)).
    assert (NI : ~ In q (map tb_tok LB)).
    { intros Hin. apply in_map_iff in Hin. destruct Hin as (t & Et & Ht).
      pose proof (CR t Ht) as E3. rewrite Et in E3.
      specialize (FR q ltac:(rewrite E3; discriminate)). subst q. rewrite EN in FR. lia. }
    exists A. split; [exact EA|]. cbn [ps_heap set_heap].
    split. { unfold hf_addr. cbn [fh_blk fh_m]. subst q. rewrite lookup_insert_eq. rewrite EC. subst h'. rewrite ES1. destruct s; reflexivity. }
    split; [exact NI|]. split; [exact BR|]. split; [|exact CH].
    set (ids' := fun k => if (k =? q)%N then (c, off) else ids k).
    assert (MG : map (tgen ids') LB = map (tgen ids) LB).
    { apply map_ext_in. intros t Ht. unfold tgen, ids'. destruct (N.eqb_spec (tb_tok t) q) as [E|NE]; [|reflexivity].
      exfalso. apply NI. rewrite <- E. apply in_map. exact Ht. }
    exists H1, ids'. split; [|split; [|split]].
    + cbn [map]. rewrite MG. unfold tgen at 1, ids'. cbn [tb_tok tb_addr tb_size fst snd]. rewrite N.eqb_refl. exact HR1.
    + intros t [<-|Ht].
      * subst h'. cbn [tb_tok tb_size fst snd fh_blk]. rewrite lookup_insert_eq. unfold tgen, ids'. cbn [tb_tok fst snd]. rewrite N.eqb_refl.
        unfold blk_ptr, blk_slot, blk_id. cbn [fst snd]. rewrite <- Epf. reflexivity.
      * subst h'. cbn [fh_blk]. assert (NEt : tb_tok t <> q). { intros Eq. apply NI. rewrite <- Eq. apply in_map. exact Ht. }
        rewrite lookup_insert_ne by (intros X; apply NEt; symmetry; exact X). rewrite EB.
        unfold tgen, ids'. rewrite (proj2 (N.eqb_neq _ _) NEt). exact (CR t Ht).
    + cbn [map tb_tok fst snd]. constructor; [exact NI| exact ND].
    + subst h'. cbn [fh_blk fh_next]. intros k' Hk'. destruct (N.eq_dec k' q) as [->|NE]; [unfold q; lia|].
      rewrite lookup_insert_ne in Hk' by (intros X; apply NE; symmetry; exact X). rewrite EB in Hk'. specialize (FR k' Hk'). unfold q. rewrite EN. lia.
  - destruct RES as (EA & EEN & H1 & HR1).
    apply implM_ret. apply evt_done.
    unfold hcalloc_post. exists u0,u1,u2,b0,b1,b2,b3,b4,b5,b6,b7,u3,u4,u5,u6,m',errv'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|].
    split; [eapply heap_presT_of; exact PR|].
    split; [exact ES1|]. split; [exact EA|]. split; [exact EEN|].
    exists H1, ids. split; [exact HR1|]. split; [|split; [exact ND| rewrite EB, EN; exact FR]].
    intros t Ht. rewrite EB. exact (CR t Ht).
Qed.
End Sz1.
Lemma hcalloc_of_rcalloc : ltac:(let t := eval cbv delta [hcalloc_of_rcalloc__stmt] in hcalloc_of_rcalloc__stmt in exact t).
Proof using Type. intros HM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB cnt sz lo B errv. ltac2:(SecDiet.SzSec.closeP 'hcalloc_of_rcalloc__body "hvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition hrealloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PS) (LB : list tblock) (q : hptr) (A sz n lo B : Z) (bs : list byte) (m : mem)
    (r : option hptr) (s' : PS) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp)
    /\ rw_cells ssegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' B
    /\ heap_presT (bv_unsigned tp) (lbt_remove q LB) (bv_unsigned sp) m m'
    /\ s' = set_heap (ps_heap s') s
    /\ match r with
       | None => a0 = Z_to_bv 64 0 /\ errv' = Z_to_bv 64 ENOMEM /\ HEAPT (ps_heap s') (bv_unsigned tp) LB m'
                 /\ rw_cells ssegs m' A [CB (Z.to_nat sz) bs]
       | Some q' => exists A',
           a0 = Z_to_bv 64 A' /\ hf_addr (ps_heap s') q' = A' /\ ~ In q' (map tb_tok LB)
           /\ rblock_rangeu (bv_unsigned tp) A' n
           /\ HEAPT (ps_heap s') (bv_unsigned tp) ((q', A', n) :: lbt_remove q LB) m'
           /\ exists junk, rw_cells ssegs m' A' [CB (Z.to_nat (Z.min sz n)) (firstn (Z.to_nat (Z.min sz n)) bs);
                                               CB (Z.to_nat (n - Z.min sz n)) junk]
       end.

Definition hrealloc_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PS) (LB : list tblock) (q : hptr) (A sz n lo B : Z) (bs : list byte) (errv : word),
  HEAPT (ps_heap s) (bv_unsigned tp) LB m -> In (q, A, sz) LB ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk ssegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RREALLOC_STACK ->
  rw_cells ssegs m (errno_addr tp) [C4 errv] ->
  mem_inv ssegs m ->
  rw_cells ssegs m A [CB (Z.to_nat sz) bs] ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  implM ssegs (hf_realloc q n) s
        (hrealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB q A sz n lo B bs m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RREALLOC_SYM) fc None m (seg_rom ssegs)).

Definition hrealloc_of_rrealloc__stmt : Prop := rrealloc_stmt_u (PState:=PS) (AS:=fheap_AllocSt) -> (forall TB : TlsBase, RHEAP_blocks_nodup_stmt (PState:=PS) (AS:=fheap_AllocSt) (TB:=TB)) -> hrealloc_stmt.
Section Sz2.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB q A sz n lo B bs errv : ltac2:(SecDiet.SzSec.tyM 'hrealloc_of_rrealloc__stmt "hhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma hrealloc_of_rrealloc__body : ltac2:(SecDiet.SzSec.bodyP 'hrealloc_of_rrealloc__stmt "hhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros HM HND.
 intros (H & ids & HR & CR & ND & FR) HIN AUX HB ST CLO LO ERR MI CH Ha0 Ha1 Hn.
  lazymatch goal with |- implM _ _ _ _ ?msX => set (ms0 := msX) end.
  unfold hf_realloc, tok_lookup.
  eapply (implM_bind ssegs _ _ _ (fun b sX msX => b = Some (blk_ptr (tgen ids (q, A, sz)), sz) /\ sX = s /\ msX = ms0)).
  { eapply (implM_bind ssegs _ _ _ (fun a s' ms' => a = s /\ s' = s /\ ms' = ms0)); [apply implM_get; apply evt_done; repeat split; reflexivity|].
    intros sB sB' ms2 (-> & -> & ->). apply implM_ret. apply evt_done. split; [| split; reflexivity].
    rewrite (CR _ HIN). reflexivity. }
  intros b sB msB (-> & -> & ->). cbv beta iota.
  assert (NDg : List.NoDup (map (fun x => ids (tb_tok x)) LB)).
  { pose proof (HND (TBu (bv_unsigned tp) H) (ps_init (ps_heap s) : PS) (map (tgen ids) LB) m HR) as X. rewrite map_map in X. exact X. }
  assert (MG : map (tgen ids) (lbt_remove q LB) = lb_remove (ids q) (map (tgen ids) LB)).
  { unfold lb_remove, lbt_remove. rewrite filter_map_swap'. f_equal. apply filter_ext_in'.
    intros t Ht. unfold tgen, blk_id. cbn [fst]. f_equal.
    destruct (N.eqb_spec (tb_tok t) q) as [Et|NEt].
    - rewrite Et. symmetry. apply (proj2 (bptr_eqb_true _ _)). reflexivity.
    - destruct (bptr_eqb (ids (tb_tok t)) (ids q)) eqn:Eb; [|reflexivity]. exfalso. apply NEt.
      apply (proj1 (bptr_eqb_true _ _)) in Eb.
      assert (t = (q, A, sz)) as ->; [| reflexivity].
      apply (NoDup_map_inj' (fun x => ids (tb_tok x)) LB t (q, A, sz) NDg Ht HIN). cbn [tb_tok fst]. exact Eb. }
  eapply (implM_bind ssegs).
  { unfold blk_ptr, tgen, blk_slot, blk_id. cbn [fst snd tb_tok].
    apply (HM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s (map (tgen ids) LB) (ids q) A sz n lo B bs errv);
      [exists H; exact HR| apply in_map_iff; exists (q, A, sz); split; [reflexivity| exact HIN]| exact AUX| exact HB| exact ST| exact CLO| exact LO| exact ERR| exact MI| exact CH| exact Ha0| exact Ha1| exact Hn]. }
  intros r sA ms1 PO. cbn beta in PO. unfold rrealloc_postu in PO.
  destruct PO as (u0&u1&u2&b0&b1&b2&b3&b4&b5&b6&b7&u3&u4&u5&u6&m'&errv'&E&MI'&ST'&ERR'&AUX'&PR&RST&RES). subst ms1.
  destruct (ps_rest_eq_set_heap s sA RST) as (EN & EB & ES1).
  destruct r as [pf|].
  - (* [comment removed for export] *)
    destruct RES as (c & off & A' & Epf & EA & EC & BR & (H1 & HR1) & CH').
    lazymatch goal with |- implM _ _ _ _ ?msX => set (ms1 := msX) end.
    set (hD := mkFH (fh_m (ps_heap sA)) (fh_brk (ps_heap sA)) (fh_next (ps_heap sA)) (delete q (fh_blk (ps_heap sA)))).
    set (sD := set_heap hD sA).
    eapply (implM_bind ssegs _ _ _ (fun _ sX msX => sX = sD /\ msX = ms1)).
    { unfold tok_drop. apply implM_upd. apply evt_done. split; reflexivity. }
    intros [] sX msX [-> ->]. cbv beta.
    unfold tok_fresh.
    set (h' := mkFH (fh_m (ps_heap sD)) (fh_brk (ps_heap sD)) (N.succ (fh_next (ps_heap sD))) (<[fh_next (ps_heap sD) := (pf, n)]> (fh_blk (ps_heap sD)))).
    eapply (implM_bind ssegs _ _ _ (fun k sY msY => k = fh_next (ps_heap sD) /\ sY = set_heap h' sD /\ msY = ms1)).
    { eapply (implM_bind ssegs _ _ _ (fun a s' ms' => a = sD /\ s' = sD /\ ms' = ms1)); [apply implM_get; apply evt_done; repeat split; reflexivity|].
      intros sB sB' ms2 (-> & -> & ->). cbv beta zeta.
      eapply (implM_bind ssegs _ _ _ (fun _ s' ms' => s' = set_heap h' sD /\ ms' = ms1)); [apply implM_upd; apply evt_done; split; reflexivity|].
      intros [] sC ms3 [-> ->]. apply implM_ret. apply evt_done. repeat split; reflexivity. }
    intros k sY msY (-> & -> & ->). apply implM_ret. apply evt_done.
    unfold hrealloc_post. exists u0,u1,u2,b0,b1,b2,b3,b4,b5,b6,b7,u3,u4,u5,u6,m',errv'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|].
    split; [eapply (heap_presT_of ids); rewrite MG; exact PR|].
    split. { subst h' sD hD. rewrite ES1. destruct s; reflexivity. }
    set (q' := fh_next (ps_heap sD)).
    assert (Eq' : q' = fh_next (ps_heap sA)) by reflexivity.
    assert (NI : ~ In q' (map tb_tok LB)).
    { intros Hin. apply in_map_iff in Hin. destruct Hin as (t & Et & Ht).
      pose proof (CR t Ht) as E3. rewrite Et in E3.
      specialize (FR q' ltac:(rewrite E3; discriminate)). rewrite Eq', EN in FR. lia. }
    assert (NI' : ~ In q' (map tb_tok (lbt_remove q LB))).
    { intros Hin. apply NI. apply in_map_iff in Hin. destruct Hin as (t & Et & Ht). unfold lbt_remove in Ht. apply filter_In in Ht.
      rewrite <- Et. apply in_map. exact (proj1 Ht). }
    exists A'. split; [exact EA|]. cbn [ps_heap set_heap].
    split. { unfold hf_addr. cbn [fh_blk fh_m]. subst q'. rewrite lookup_insert_eq. rewrite EC. subst h' sD hD. rewrite ES1. destruct s; reflexivity. }
    split; [exact NI|]. split; [exact BR|]. split; [|exact CH'].
    set (ids' := fun k => if (k =? q')%N then (c, off) else ids k).
    assert (MG' : map (tgen ids') (lbt_remove q LB) = map (tgen ids) (lbt_remove q LB)).
    { apply map_ext_in. intros t Ht. unfold tgen, ids'. destruct (N.eqb_spec (tb_tok t) q') as [E|NE]; [|reflexivity].
      exfalso. apply NI'. rewrite <- E. apply in_map. exact Ht. }
    exists H1, ids'. split; [|split; [|split]].
    + cbn [map]. rewrite MG', MG. unfold tgen at 1, ids'. cbn [tb_tok tb_addr tb_size fst snd]. rewrite N.eqb_refl.
      subst h' sD hD. cbn [fh_m fh_brk]. rewrite ES1 in HR1. destruct s; cbn in HR1 |- *. exact HR1.
    + intros t [<-|Ht].
      * subst h'. cbn [tb_tok tb_size fst snd fh_blk]. rewrite lookup_insert_eq. unfold tgen, ids'. cbn [tb_tok fst snd]. rewrite N.eqb_refl.
        unfold blk_ptr, blk_slot, blk_id. cbn [fst snd]. rewrite <- Epf. reflexivity.
      * subst h'. cbn [fh_blk]. assert (NEt : tb_tok t <> q'). { intros Eq. apply NI'. rewrite <- Eq. apply in_map. exact Ht. }
        rewrite lookup_insert_ne by (intros X; apply NEt; symmetry; exact X).
        unfold lbt_remove in Ht. apply filter_In in Ht. destruct Ht as [Ht Hne].
        destruct (N.eqb_spec (tb_tok t) q) as [Et|NEq]; [discriminate|].
        subst sD hD. cbn [ps_heap set_heap fh_blk]. rewrite lookup_delete_ne by (intros X; apply NEq; symmetry; exact X). rewrite EB.
        unfold tgen, ids'. rewrite (proj2 (N.eqb_neq _ _) NEt). exact (CR t Ht).
    + cbn [map tb_tok fst snd]. constructor; [exact NI'| unfold lbt_remove; apply NoDup_filter_map'; exact ND].
    + subst h'. cbn [fh_blk fh_next]. intros k' Hk'. destruct (N.eq_dec k' q') as [->|NE]; [lia|].
      rewrite lookup_insert_ne in Hk' by (intros X; apply NE; symmetry; exact X).
      subst sD hD. cbn [ps_heap set_heap fh_blk fh_next] in Hk' |- *.
      destruct (N.eq_dec k' q) as [->|NE2]; [rewrite lookup_delete_eq in Hk'; exfalso; apply Hk'; reflexivity|].
      rewrite lookup_delete_ne in Hk' by (intros X; apply NE2; symmetry; exact X). rewrite EB in Hk'. specialize (FR k' Hk'). rewrite EN. lia.
  - destruct RES as (EA & EEN & (H1 & HR1) & CH').
    apply implM_ret. apply evt_done.
    unfold hrealloc_post. exists u0,u1,u2,b0,b1,b2,b3,b4,b5,b6,b7,u3,u4,u5,u6,m',errv'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|].
    split; [eapply (heap_presT_of ids); rewrite MG; exact PR|].
    split; [exact ES1|]. split; [exact EA|]. split; [exact EEN|]. split; [| exact CH'].
    exists H1, ids. split; [exact HR1|]. split; [|split; [exact ND| rewrite EB, EN; exact FR]].
    intros t Ht. rewrite EB. exact (CR t Ht).
Qed.
End Sz2.
Lemma hrealloc_of_rrealloc : ltac:(let t := eval cbv delta [hrealloc_of_rrealloc__stmt] in hrealloc_of_rrealloc__stmt in exact t).
Proof using Type. intros HM HND ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB q A sz n lo B bs errv. ltac2:(SecDiet.SzSec.closeP 'hrealloc_of_rrealloc__body "hhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.SFModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.HeapFull.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.TlsBaseU OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocHINV OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.Malloc_iface.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_ifaceB.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_ifaceT.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MSecret.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation PS := (PState fheap hptr).

(* [comment removed for export] *)

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Definition hcalloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PS) (LB : list tblock) (n lo B : Z) (m : mem)
    (r : option hptr) (s' : PS) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' B
    /\ heap_presT (bv_unsigned tp) LB (bv_unsigned sp) m m'
    /\ s' = set_heap (ps_heap s') s
    /\ match r with
       | None => a0 = Z_to_bv 64 0 /\ errv' = Z_to_bv 64 ENOMEM /\ HEAPT (ps_heap s') (bv_unsigned tp) LB m'
       | Some q => exists A,
           a0 = Z_to_bv 64 A /\ hf_addr (ps_heap s') q = A /\ ~ In q (map tb_tok LB)
           /\ rblock_rangeu (bv_unsigned tp) A n
           /\ HEAPT (ps_heap s') (bv_unsigned tp) ((q, A, n) :: LB) m'
           /\ rw_cells usegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))]
       end.

Definition hcalloc_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PS) (LB : list tblock) (cnt sz lo B : Z) (errv : word),
  HEAPT (ps_heap s) (bv_unsigned tp) LB m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RCALLOC_STACK ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 sz -> 0 <= cnt < 2^64 -> 0 <= sz < 2^64 -> cnt * sz <= RCALLOC_MAX ->
  implM usegs (hf_calloc cnt sz) s
        (hcalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB (cnt * sz) lo B m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RCALLOC_SYM) fc None m (seg_rom usegs)).


Definition hcalloc_of_rcalloc__stmt : Prop := rcalloc_stmt_u (PState:=PS) (AS:=fheap_AllocSt) -> hcalloc_stmt.
Section Sz1.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB cnt sz lo B errv : ltac2:(SecDiet.SzSec.tyM 'hcalloc_of_rcalloc__stmt "hvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma hcalloc_of_rcalloc__body : ltac2:(SecDiet.SzSec.bodyP 'hcalloc_of_rcalloc__stmt "hvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros HM.
 intros (H & ids & HR & CR & ND & FR) AUX HB ST CLO LO ERR MI Ha0 Ha1 Hc Hs Hmax.
  unfold hf_calloc.
  eapply (implM_bind usegs).
  { apply (HM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s (map (tgen ids) LB) cnt sz lo B errv);
      [exists H; exact HR| exact AUX| exact HB| exact ST| exact CLO| exact LO| exact ERR| exact MI| exact Ha0| exact Ha1| exact Hc| exact Hs| exact Hmax]. }
  set (n := cnt * sz) in *.
  intros r sA ms1 PO. cbn beta in PO. unfold rcalloc_postu in PO.
  destruct PO as (u0&u1&u2&b0&b1&b2&b3&b4&b5&b6&b7&u3&u4&u5&u6&m'&errv'&E&MI'&ST'&ERR'&AUX'&PR&RST&RES). subst ms1.
  destruct (ps_rest_eq_set_heap s sA RST) as (EN & EB & ES1).
  destruct r as [pf|].
  - destruct RES as (c & off & A & Epf & EA & EC & BR & (H1 & HR1) & CH).
    lazymatch goal with |- implM _ _ _ _ ?msX => set (ms1 := msX) end.
    unfold tok_fresh.
    set (h' := mkFH (fh_m (ps_heap sA)) (fh_brk (ps_heap sA)) (N.succ (fh_next (ps_heap sA))) (<[fh_next (ps_heap sA) := (pf, n)]> (fh_blk (ps_heap sA)))).
    eapply (implM_bind usegs _ _ _ (fun k s4 ms4 => k = fh_next (ps_heap sA) /\ s4 = set_heap h' sA /\ ms4 = ms1)).
    { eapply (implM_bind usegs _ _ _ (fun a s' ms' => a = sA /\ s' = sA /\ ms' = ms1)); [apply implM_get; apply evt_done; repeat split; reflexivity|].
      intros sB sB' ms2 (-> & -> & ->). cbv beta zeta.
      eapply (implM_bind usegs _ _ _ (fun _ s' ms' => s' = set_heap h' sA /\ ms' = ms1)); [apply implM_upd; apply evt_done; split; reflexivity|].
      intros [] sC ms3 [-> ->]. apply implM_ret. apply evt_done. repeat split; reflexivity. }
    intros k sD ms4 (-> & -> & ->). apply implM_ret. apply evt_done.
    unfold hcalloc_post. exists u0,u1,u2,b0,b1,b2,b3,b4,b5,b6,b7,u3,u4,u5,u6,m',errv'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|].
    split; [eapply heap_presT_of; exact PR|].
    split. { subst h'. rewrite ES1. destruct s; reflexivity. }
    set (q := fh_next (ps_heap sA)).
    assert (NI : ~ In q (map tb_tok LB)).
    { intros Hin. apply in_map_iff in Hin. destruct Hin as (t & Et & Ht).
      pose proof (CR t Ht) as E3. rewrite Et in E3.
      specialize (FR q ltac:(rewrite E3; discriminate)). subst q. rewrite EN in FR. lia. }
    exists A. split; [exact EA|]. cbn [ps_heap set_heap].
    split. { unfold hf_addr. cbn [fh_blk fh_m]. subst q. rewrite lookup_insert_eq. rewrite EC. subst h'. rewrite ES1. destruct s; reflexivity. }
    split; [exact NI|]. split; [exact BR|]. split; [|exact CH].
    set (ids' := fun k => if (k =? q)%N then (c, off) else ids k).
    assert (MG : map (tgen ids') LB = map (tgen ids) LB).
    { apply map_ext_in. intros t Ht. unfold tgen, ids'. destruct (N.eqb_spec (tb_tok t) q) as [E|NE]; [|reflexivity].
      exfalso. apply NI. rewrite <- E. apply in_map. exact Ht. }
    exists H1, ids'. split; [|split; [|split]].
    + cbn [map]. rewrite MG. unfold tgen at 1, ids'. cbn [tb_tok tb_addr tb_size fst snd]. rewrite N.eqb_refl. exact HR1.
    + intros t [<-|Ht].
      * subst h'. cbn [tb_tok tb_size fst snd fh_blk]. rewrite lookup_insert_eq. unfold tgen, ids'. cbn [tb_tok fst snd]. rewrite N.eqb_refl.
        unfold blk_ptr, blk_slot, blk_id. cbn [fst snd]. rewrite <- Epf. reflexivity.
      * subst h'. cbn [fh_blk]. assert (NEt : tb_tok t <> q). { intros Eq. apply NI. rewrite <- Eq. apply in_map. exact Ht. }
        rewrite lookup_insert_ne by (intros X; apply NEt; symmetry; exact X). rewrite EB.
        unfold tgen, ids'. rewrite (proj2 (N.eqb_neq _ _) NEt). exact (CR t Ht).
    + cbn [map tb_tok fst snd]. constructor; [exact NI| exact ND].
    + subst h'. cbn [fh_blk fh_next]. intros k' Hk'. destruct (N.eq_dec k' q) as [->|NE]; [unfold q; lia|].
      rewrite lookup_insert_ne in Hk' by (intros X; apply NE; symmetry; exact X). rewrite EB in Hk'. specialize (FR k' Hk'). unfold q. rewrite EN. lia.
  - destruct RES as (EA & EEN & H1 & HR1).
    apply implM_ret. apply evt_done.
    unfold hcalloc_post. exists u0,u1,u2,b0,b1,b2,b3,b4,b5,b6,b7,u3,u4,u5,u6,m',errv'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|].
    split; [eapply heap_presT_of; exact PR|].
    split; [exact ES1|]. split; [exact EA|]. split; [exact EEN|].
    exists H1, ids. split; [exact HR1|]. split; [|split; [exact ND| rewrite EB, EN; exact FR]].
    intros t Ht. rewrite EB. exact (CR t Ht).
Qed.
End Sz1.
Lemma hcalloc_of_rcalloc : ltac:(let t := eval cbv delta [hcalloc_of_rcalloc__stmt] in hcalloc_of_rcalloc__stmt in exact t).
Proof using Type. intros HM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB cnt sz lo B errv. ltac2:(SecDiet.SzSec.closeP 'hcalloc_of_rcalloc__body "hvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition hrealloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PS) (LB : list tblock) (q : hptr) (A sz n lo B : Z) (bs : list byte) (m : mem)
    (r : option hptr) (s' : PS) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' B
    /\ heap_presT (bv_unsigned tp) (lbt_remove q LB) (bv_unsigned sp) m m'
    /\ s' = set_heap (ps_heap s') s
    /\ match r with
       | None => a0 = Z_to_bv 64 0 /\ errv' = Z_to_bv 64 ENOMEM /\ HEAPT (ps_heap s') (bv_unsigned tp) LB m'
                 /\ rw_cells usegs m' A [CB (Z.to_nat sz) bs]
       | Some q' => exists A',
           a0 = Z_to_bv 64 A' /\ hf_addr (ps_heap s') q' = A' /\ ~ In q' (map tb_tok LB)
           /\ rblock_rangeu (bv_unsigned tp) A' n
           /\ HEAPT (ps_heap s') (bv_unsigned tp) ((q', A', n) :: lbt_remove q LB) m'
           /\ exists junk, rw_cells usegs m' A' [CB (Z.to_nat (Z.min sz n)) (firstn (Z.to_nat (Z.min sz n)) bs);
                                               CB (Z.to_nat (n - Z.min sz n)) junk]
       end.

Definition hrealloc_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PS) (LB : list tblock) (q : hptr) (A sz n lo B : Z) (bs : list byte) (errv : word),
  HEAPT (ps_heap s) (bv_unsigned tp) LB m -> In (q, A, sz) LB ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RREALLOC_STACK ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  rw_cells usegs m A [CB (Z.to_nat sz) bs] ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  implM usegs (hf_realloc q n) s
        (hrealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB q A sz n lo B bs m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RREALLOC_SYM) fc None m (seg_rom usegs)).

Definition hrealloc_of_rrealloc__stmt : Prop := rrealloc_stmt_u (PState:=PS) (AS:=fheap_AllocSt) -> (forall TB : TlsBase, RHEAP_blocks_nodup_stmt (PState:=PS) (AS:=fheap_AllocSt) (TB:=TB)) -> hrealloc_stmt.
Section Sz2.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB q A sz n lo B bs errv : ltac2:(SecDiet.SzSec.tyM 'hrealloc_of_rrealloc__stmt "hhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma hrealloc_of_rrealloc__body : ltac2:(SecDiet.SzSec.bodyP 'hrealloc_of_rrealloc__stmt "hhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros HM HND.
 intros (H & ids & HR & CR & ND & FR) HIN AUX HB ST CLO LO ERR MI CH Ha0 Ha1 Hn.
  lazymatch goal with |- implM _ _ _ _ ?msX => set (ms0 := msX) end.
  unfold hf_realloc, tok_lookup.
  eapply (implM_bind usegs _ _ _ (fun b sX msX => b = Some (blk_ptr (tgen ids (q, A, sz)), sz) /\ sX = s /\ msX = ms0)).
  { eapply (implM_bind usegs _ _ _ (fun a s' ms' => a = s /\ s' = s /\ ms' = ms0)); [apply implM_get; apply evt_done; repeat split; reflexivity|].
    intros sB sB' ms2 (-> & -> & ->). apply implM_ret. apply evt_done. split; [| split; reflexivity].
    rewrite (CR _ HIN). reflexivity. }
  intros b sB msB (-> & -> & ->). cbv beta iota.
  assert (NDg : List.NoDup (map (fun x => ids (tb_tok x)) LB)).
  { pose proof (HND (TBu (bv_unsigned tp) H) (ps_init (ps_heap s) : PS) (map (tgen ids) LB) m HR) as X. rewrite map_map in X. exact X. }
  assert (MG : map (tgen ids) (lbt_remove q LB) = lb_remove (ids q) (map (tgen ids) LB)).
  { unfold lb_remove, lbt_remove. rewrite filter_map_swap'. f_equal. apply filter_ext_in'.
    intros t Ht. unfold tgen, blk_id. cbn [fst]. f_equal.
    destruct (N.eqb_spec (tb_tok t) q) as [Et|NEt].
    - rewrite Et. symmetry. apply (proj2 (bptr_eqb_true _ _)). reflexivity.
    - destruct (bptr_eqb (ids (tb_tok t)) (ids q)) eqn:Eb; [|reflexivity]. exfalso. apply NEt.
      apply (proj1 (bptr_eqb_true _ _)) in Eb.
      assert (t = (q, A, sz)) as ->; [| reflexivity].
      apply (NoDup_map_inj' (fun x => ids (tb_tok x)) LB t (q, A, sz) NDg Ht HIN). cbn [tb_tok fst]. exact Eb. }
  eapply (implM_bind usegs).
  { unfold blk_ptr, tgen, blk_slot, blk_id. cbn [fst snd tb_tok].
    apply (HM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s (map (tgen ids) LB) (ids q) A sz n lo B bs errv);
      [exists H; exact HR| apply in_map_iff; exists (q, A, sz); split; [reflexivity| exact HIN]| exact AUX| exact HB| exact ST| exact CLO| exact LO| exact ERR| exact MI| exact CH| exact Ha0| exact Ha1| exact Hn]. }
  intros r sA ms1 PO. cbn beta in PO. unfold rrealloc_postu in PO.
  destruct PO as (u0&u1&u2&b0&b1&b2&b3&b4&b5&b6&b7&u3&u4&u5&u6&m'&errv'&E&MI'&ST'&ERR'&AUX'&PR&RST&RES). subst ms1.
  destruct (ps_rest_eq_set_heap s sA RST) as (EN & EB & ES1).
  destruct r as [pf|].
  - (* [comment removed for export] *)
    destruct RES as (c & off & A' & Epf & EA & EC & BR & (H1 & HR1) & CH').
    lazymatch goal with |- implM _ _ _ _ ?msX => set (ms1 := msX) end.
    set (hD := mkFH (fh_m (ps_heap sA)) (fh_brk (ps_heap sA)) (fh_next (ps_heap sA)) (delete q (fh_blk (ps_heap sA)))).
    set (sD := set_heap hD sA).
    eapply (implM_bind usegs _ _ _ (fun _ sX msX => sX = sD /\ msX = ms1)).
    { unfold tok_drop. apply implM_upd. apply evt_done. split; reflexivity. }
    intros [] sX msX [-> ->]. cbv beta.
    unfold tok_fresh.
    set (h' := mkFH (fh_m (ps_heap sD)) (fh_brk (ps_heap sD)) (N.succ (fh_next (ps_heap sD))) (<[fh_next (ps_heap sD) := (pf, n)]> (fh_blk (ps_heap sD)))).
    eapply (implM_bind usegs _ _ _ (fun k sY msY => k = fh_next (ps_heap sD) /\ sY = set_heap h' sD /\ msY = ms1)).
    { eapply (implM_bind usegs _ _ _ (fun a s' ms' => a = sD /\ s' = sD /\ ms' = ms1)); [apply implM_get; apply evt_done; repeat split; reflexivity|].
      intros sB sB' ms2 (-> & -> & ->). cbv beta zeta.
      eapply (implM_bind usegs _ _ _ (fun _ s' ms' => s' = set_heap h' sD /\ ms' = ms1)); [apply implM_upd; apply evt_done; split; reflexivity|].
      intros [] sC ms3 [-> ->]. apply implM_ret. apply evt_done. repeat split; reflexivity. }
    intros k sY msY (-> & -> & ->). apply implM_ret. apply evt_done.
    unfold hrealloc_post. exists u0,u1,u2,b0,b1,b2,b3,b4,b5,b6,b7,u3,u4,u5,u6,m',errv'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|].
    split; [eapply (heap_presT_of ids); rewrite MG; exact PR|].
    split. { subst h' sD hD. rewrite ES1. destruct s; reflexivity. }
    set (q' := fh_next (ps_heap sD)).
    assert (Eq' : q' = fh_next (ps_heap sA)) by reflexivity.
    assert (NI : ~ In q' (map tb_tok LB)).
    { intros Hin. apply in_map_iff in Hin. destruct Hin as (t & Et & Ht).
      pose proof (CR t Ht) as E3. rewrite Et in E3.
      specialize (FR q' ltac:(rewrite E3; discriminate)). rewrite Eq', EN in FR. lia. }
    assert (NI' : ~ In q' (map tb_tok (lbt_remove q LB))).
    { intros Hin. apply NI. apply in_map_iff in Hin. destruct Hin as (t & Et & Ht). unfold lbt_remove in Ht. apply filter_In in Ht.
      rewrite <- Et. apply in_map. exact (proj1 Ht). }
    exists A'. split; [exact EA|]. cbn [ps_heap set_heap].
    split. { unfold hf_addr. cbn [fh_blk fh_m]. subst q'. rewrite lookup_insert_eq. rewrite EC. subst h' sD hD. rewrite ES1. destruct s; reflexivity. }
    split; [exact NI|]. split; [exact BR|]. split; [|exact CH'].
    set (ids' := fun k => if (k =? q')%N then (c, off) else ids k).
    assert (MG' : map (tgen ids') (lbt_remove q LB) = map (tgen ids) (lbt_remove q LB)).
    { apply map_ext_in. intros t Ht. unfold tgen, ids'. destruct (N.eqb_spec (tb_tok t) q') as [E|NE]; [|reflexivity].
      exfalso. apply NI'. rewrite <- E. apply in_map. exact Ht. }
    exists H1, ids'. split; [|split; [|split]].
    + cbn [map]. rewrite MG', MG. unfold tgen at 1, ids'. cbn [tb_tok tb_addr tb_size fst snd]. rewrite N.eqb_refl.
      subst h' sD hD. cbn [fh_m fh_brk]. rewrite ES1 in HR1. destruct s; cbn in HR1 |- *. exact HR1.
    + intros t [<-|Ht].
      * subst h'. cbn [tb_tok tb_size fst snd fh_blk]. rewrite lookup_insert_eq. unfold tgen, ids'. cbn [tb_tok fst snd]. rewrite N.eqb_refl.
        unfold blk_ptr, blk_slot, blk_id. cbn [fst snd]. rewrite <- Epf. reflexivity.
      * subst h'. cbn [fh_blk]. assert (NEt : tb_tok t <> q'). { intros Eq. apply NI'. rewrite <- Eq. apply in_map. exact Ht. }
        rewrite lookup_insert_ne by (intros X; apply NEt; symmetry; exact X).
        unfold lbt_remove in Ht. apply filter_In in Ht. destruct Ht as [Ht Hne].
        destruct (N.eqb_spec (tb_tok t) q) as [Et|NEq]; [discriminate|].
        subst sD hD. cbn [ps_heap set_heap fh_blk]. rewrite lookup_delete_ne by (intros X; apply NEq; symmetry; exact X). rewrite EB.
        unfold tgen, ids'. rewrite (proj2 (N.eqb_neq _ _) NEt). exact (CR t Ht).
    + cbn [map tb_tok fst snd]. constructor; [exact NI'| unfold lbt_remove; apply NoDup_filter_map'; exact ND].
    + subst h'. cbn [fh_blk fh_next]. intros k' Hk'. destruct (N.eq_dec k' q') as [->|NE]; [lia|].
      rewrite lookup_insert_ne in Hk' by (intros X; apply NE; symmetry; exact X).
      subst sD hD. cbn [ps_heap set_heap fh_blk fh_next] in Hk' |- *.
      destruct (N.eq_dec k' q) as [->|NE2]; [rewrite lookup_delete_eq in Hk'; exfalso; apply Hk'; reflexivity|].
      rewrite lookup_delete_ne in Hk' by (intros X; apply NE2; symmetry; exact X). rewrite EB in Hk'. specialize (FR k' Hk'). rewrite EN. lia.
  - destruct RES as (EA & EEN & (H1 & HR1) & CH').
    apply implM_ret. apply evt_done.
    unfold hrealloc_post. exists u0,u1,u2,b0,b1,b2,b3,b4,b5,b6,b7,u3,u4,u5,u6,m',errv'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|].
    split; [eapply (heap_presT_of ids); rewrite MG; exact PR|].
    split; [exact ES1|]. split; [exact EA|]. split; [exact EEN|]. split; [| exact CH'].
    exists H1, ids. split; [exact HR1|]. split; [|split; [exact ND| rewrite EB, EN; exact FR]].
    intros t Ht. rewrite EB. exact (CR t Ht).
Qed.
End Sz2.
Lemma hrealloc_of_rrealloc : ltac:(let t := eval cbv delta [hrealloc_of_rrealloc__stmt] in hrealloc_of_rrealloc__stmt in exact t).
Proof using Type. intros HM HND ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB q A sz n lo B bs errv. ltac2:(SecDiet.SzSec.closeP 'hrealloc_of_rrealloc__body "hhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End WithCeil.
End TwB.
End RMalloc_ifaceTB.

(* [comment removed for export] *)
Module RMalloc_fp.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import TlsBase.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_enframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Export Malloc_fp.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_enframe RMallocKit_A. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_enframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocKit_A.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.

Notation RMFACTS := (MFACTS_g (resv:=ref_reserved)).

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Lemma rreserved_disjoint2 : forall b n, ranges_free ref_reserved b n = true -> 0 < n ->
  (b + n <= 0x10000 \/ 0x22000 <= b) /\ ((b + n <= 0x22000 \/ 0x55000 <= b) /\ (b + n <= the_tb \/ the_tb + 4096 <= b)).
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts. intros b n H Hn. pose proof (rreserved_disjoint b n H). pose proof (rreserved_tls b n H Hn). lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wr8_comm p q v w st : fst p = fst q -> snd p <> snd q -> wr8 p v (wr8 q w st) = wr8 q w (wr8 p v st).
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  intros Hf Hs.
  assert (E : forall (a b : aptr) x y s, fst a = fst b -> snd a <> snd b ->
     wr8 a x (wr8 b y s) = set_shadow (<[fst a := mkShadow (<[snd a := (Z.land x 255, s_tick s)]> (<[snd b := (Z.land y 255, s_tick s)]> (r_cells (get_shadow s (fst a))))) (r_hav (get_shadow s (fst a))) (r_havp (get_shadow s (fst a)))]> (s_shadow s)) s).
  { intros a b x y s Ef Ns. unfold wr8 at 1. unfold upd_shadow. rewrite Ef, get_shadow_wr8_same. cbn [r_cells r_hav r_havp].
    rewrite s_shadow_wr8, <- Ef. change (s_tick (wr8 b y s)) with (s_tick s). rewrite insert_insert_eq. reflexivity. }
  rewrite (E p q), (E q p) by (congruence || (symmetry; congruence) || auto). rewrite Hf.
  rewrite (insert_insert_ne _ (snd p) (snd q)) by exact Hs. reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Section ENFRAME.
Variables (st2 : mstate) (m4 : mem) (g b : aptr) (r : region) (k n off : Z).
Let mr := get_meta_rec st2 g.
Let stride := get_stride mr.
Let B := conc st2 b.
Let P0 := B + 16 + stride * k.

Hypothesis MR : rmrep st2 m4.
Hypothesis TK : ticks_ok st2.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hr : (s_regions st2) !! (fst b) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis B0 : 0 <= snd b.
Hypothesis K0 : 0 <= k < 32.
Hypothesis SPAN : snd b + 16 + stride * (k + 1) <= round_up_pg (r_len r).
Hypothesis S16 : 16 <= stride.
Hypothesis S31 : stride - 4 - n < 2^31.
Hypothesis NOGRP : forall b' gh, (s_groups st2) !! b' = Some gh -> fst b' = fst b ->
  snd b' + 9 <= snd b + 16 + stride * k - 4 \/ snd b + 16 + stride * k + stride - 4 <= snd b'.
Hypothesis OFF0 : 0 <= off.
Hypothesis N0 : 0 <= n.
Hypothesis FIT : 16 * off + n + 4 <= stride.
Hypothesis Q16 : (stride * k + 16 * off) / 16 < 65536.

Lemma rconc_b : B = r_base r + snd b.
Proof using CEILV Hr MSECV. pin_using (fun (CEILV Hr MSECV : unit) => tt). ceil_facts. msec_facts. unfold B. apply (conc_region' st2 b r Hr). Qed.

Lemma rsk_nonneg : 0 <= stride * k.
Proof using K0 MSECV P0 S16 TLSFACTS off. pin_using (fun (K0 MSECV P0 S16 TLSFACTS off : unit) => tt). ceil_facts. msec_facts. apply Z.mul_nonneg_nonneg; lia. Qed.

(* [comment removed for export] *)
Lemma rwr8_rep : forall stx mx (o v : Z),
  rmrep stx mx -> ticks_ok stx ->
  s_regions stx = s_regions st2 -> s_groups stx = s_groups st2 ->
  snd b + 16 + stride * k - 4 <= o < snd b + 16 + stride * k + stride - 4 ->
  0 <= v < 256 ->
  rmrep (wr8 (fst b, o) v stx) (write_to_mem mx (wa (r_base r + o)) [b8 v]) /\ ticks_ok (wr8 (fst b, o) v stx).
Proof using B0 Hk Hr K0 NOGRP OFF0 P0 S16 SPAN. pin_using (fun (B0 Hk Hr K0 NOGRP OFF0 P0 S16 SPAN : unit) => tt). ceil_facts. msec_facts.
  intros stx mx o v MRx TKx ER EG Ho Hv. pose proof rsk_nonneg.
  split; [|apply ticks_ok_wr8; exact TKx].
  apply (rmrep_wr8 stx mx (fst b, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| lia| |exact Hv].
  intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); lia.
Qed.

Lemma rwr16_rep : forall stx mx (o v : Z),
  rmrep stx mx -> ticks_ok stx ->
  s_regions stx = s_regions st2 -> s_groups stx = s_groups st2 ->
  snd b + 16 + stride * k - 4 <= o -> o + 2 <= snd b + 16 + stride * k + stride - 4 ->
  0 <= v < 65536 ->
  rmrep (wr16 (fst b, o) v stx) (write_to_mem mx (wa (r_base r + o)) (le2 (wz v))) /\ ticks_ok (wr16 (fst b, o) v stx).
Proof using B0 Hk Hr K0 NOGRP OFF0 P0 S16 SPAN. pin_using (fun (B0 Hk Hr K0 NOGRP OFF0 P0 S16 SPAN : unit) => tt). ceil_facts. msec_facts.
  intros stx mx o v MRx TKx ER EG Ho Ho2 Hv. pose proof rsk_nonneg.
  split; [|apply ticks_ok_wr16; exact TKx].
  apply (rmrep_wr16 stx mx (fst b, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| lia| lia| |exact Hv].
  intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); lia.
Qed.

Lemma rwr32_rep : forall stx mx (o v : Z),
  rmrep stx mx -> ticks_ok stx ->
  s_regions stx = s_regions st2 -> s_groups stx = s_groups st2 ->
  snd b + 16 + stride * k - 4 <= o -> o + 4 <= snd b + 16 + stride * k + stride - 4 ->
  0 <= v < 2^32 ->
  rmrep (wr32 (fst b, o) v stx) (write_to_mem mx (wa (r_base r + o)) (le4 (wz v))) /\ ticks_ok (wr32 (fst b, o) v stx).
Proof using B0 Hk Hr K0 NOGRP OFF0 P0 S16 SPAN. pin_using (fun (B0 Hk Hr K0 NOGRP OFF0 P0 S16 SPAN : unit) => tt). ceil_facts. msec_facts.
  intros stx mx o v MRx TKx ER EG Ho Ho4 Hv. pose proof rsk_nonneg.
  apply (rmrep_wr32 stx mx (fst b, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| lia| lia| |exact Hv].
  intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); lia.
Qed.

(* [comment removed for export] *)
Lemma wr16_wr8_comm p q v w st : fst p = fst q -> snd q <> snd p -> snd q <> snd p + 1 ->
  wr8 q w (wr16 p v st) = wr16 p v (wr8 q w st).
Proof using K0 MSECV P0 TLSFACTS off. pin_using (fun (K0 MSECV P0 TLSFACTS off : unit) => tt). ceil_facts. msec_facts.
  intros Hf H0 H1. unfold wr16.
  rewrite (wr8_comm q (aadd p 1)) by (unfold aadd; cbn; lia || auto).
  rewrite (wr8_comm q p) by (auto || lia). reflexivity.
Qed.

Lemma wr32_wr8_comm p q v w st : fst p = fst q -> snd q + 1 = snd p ->
  wr8 q w (wr32 p v st) = wr32 p v (wr8 q w st).
Proof using K0 MSECV P0 TLSFACTS off. pin_using (fun (K0 MSECV P0 TLSFACTS off : unit) => tt). ceil_facts. msec_facts.
  intros Hf H1. unfold wr32.
  rewrite (wr8_comm q (aadd p 3)) by (unfold aadd; cbn; lia || auto).
  rewrite (wr8_comm q (aadd p 2)) by (unfold aadd; cbn; lia || auto).
  rewrite (wr8_comm q (aadd p 1)) by (unfold aadd; cbn; lia || auto).
  rewrite (wr8_comm q p) by (auto || lia). reflexivity.
Qed.

Lemma renframe_mrep :
  let res := enframe_at st2 g k n off in
  rmrep (fst res) (renframe_tail_mem (renframe_off_mem m4 P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16))
  /\ ticks_ok (fst res)
  /\ conc st2 (snd res) = P0 + 16 * off /\ fst (snd res) = fst b /\ snd (snd res) = snd b + 16 + stride * k + 16 * off.
Proof using B0 FIT Hk Hmem Hr K0 MR N0 NOGRP OFF0 Q16 S16 S31 SPAN TK. pin_using (fun (B0 FIT Hk Hmem Hr K0 MR N0 NOGRP OFF0 Q16 S16 S31 SPAN TK : unit) => tt). ceil_facts. msec_facts.
  pose proof rconc_b as CB. pose proof rsk_nonneg as SK.
  cbv zeta. unfold enframe_at. fold mr. fold stride. rewrite Hmem. cbn [default from_option id fst snd].
  unfold aadd. cbn [fst snd].
  (* [comment removed for export] *)
  set (stC := if negb (off =? 0) then _ else _).
  assert (PRE : rmrep (fst stC) (renframe_off_mem m4 P0 off) /\ ticks_ok (fst stC)
                /\ snd stC = (fst b, snd b + (UNIT + stride * k) + UNIT * off)
                /\ s_regions (fst stC) = s_regions st2 /\ s_groups (fst stC) = s_groups st2
                /\ (forall q, conc (fst stC) q = conc st2 q)).
  { subst stC. unfold renframe_off_mem. destruct (Z.eqb_spec off 0) as [E|NE]; cbn [negb fst snd].
    - subst off. rewrite Z.mul_0_r, Z.add_0_r.
      split; [exact MR|]. split; [exact TK|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros; reflexivity.
    - (* [comment removed for export] *)
      rewrite (wr16_wr8_comm (fst b, snd b + (UNIT + stride * k) + -2) (fst b, snd b + (UNIT + stride * k) + -3)) by (cbn; lia || reflexivity).
      destruct (rwr8_rep st2 m4 (snd b + (UNIT + stride * k) + -3) 224 MR TK eq_refl eq_refl) as [M1 T1]; [unfold UNIT; lia| lia|].
      destruct (rwr16_rep _ _ (snd b + (UNIT + stride * k) + -2) off M1 T1 eq_refl eq_refl) as [M2 T2]; [unfold UNIT; lia| unfold UNIT; lia| lia|].
      destruct (rwr8_rep _ _ (snd b + (UNIT + stride * k) + UNIT * off + -4) 0 M2 T2 eq_refl eq_refl) as [M3 T3]; [unfold UNIT; lia| lia|].
      unfold UNIT in *.
      replace (P0 - 2) with (r_base r + (snd b + (16 + stride * k) + -2)) by (unfold P0; lia).
      replace (P0 - 3) with (r_base r + (snd b + (16 + stride * k) + -3)) by (unfold P0; lia).
      replace (P0 + 16 * off - 4) with (r_base r + (snd b + (16 + stride * k) + 16 * off + -4)) by (unfold P0; lia).
      split; [exact M3|]. split; [exact T3|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros; reflexivity. }
  clearbody stC. destruct stC as [stc p']. cbn [fst snd] in PRE. destruct PRE as (MC & TC & -> & ERc & EGc & CONCc).
  cbn [fst snd].
  unfold renframe_tail_mem. cbv zeta.
  (* [comment removed for export] *)
  set (po := snd b + (UNIT + stride * k) + UNIT * off).
  assert (Epo : P0 + 16 * off = r_base r + po) by (unfold po, P0, UNIT; lia).
  assert (Eq : (P0 + 16 * off - B - 16) / 16 = (po - (snd b + UNIT)) / UNIT).
  { unfold po, P0, UNIT. f_equal; lia. }
  rewrite Eq.
  assert (QB : 0 <= (po - (snd b + UNIT)) / UNIT < 65536).
  { unfold po, UNIT. replace (snd b + (16 + stride * k) + 16 * off - (snd b + 16)) with (stride * k + 16 * off) by lia.
    split; [apply Z.div_pos; lia| exact Q16]. }
  (* [comment removed for export] *)
  rewrite (wr16_wr8_comm (fst b, po + -2) (fst b, po + -3)) by (cbn; lia || reflexivity).
  destruct (rwr8_rep _ _ (po + -3) k MC TC ERc EGc) as [MD TD]; [unfold po, UNIT; lia| lia|].
  destruct (rwr16_rep _ _ (po + -2) ((po - (snd b + UNIT)) / UNIT) MD TD ERc EGc) as [ME TE]; [unfold po, UNIT; lia| unfold po, UNIT; lia| lia|].
  replace (P0 + 16 * off - 2) with (r_base r + (po + -2)) by lia.
  replace (P0 + 16 * off - 3) with (r_base r + (po + -3)) by lia.
  (* [comment removed for export] *)
  unfold set_size, aadd. cbn [fst snd id].
  set (rsv := snd b + (UNIT + stride * k) + (stride - IB) - po - n).
  assert (Ersv : P0 + stride - 4 - (P0 + 16 * off) - n = rsv) by (unfold rsv, po, P0, UNIT, IB; lia).
  rewrite Ersv.
  assert (RSV : 0 <= rsv <= stride - 4 - n) by (unfold rsv, po, UNIT, IB; lia).
  set (stF := if negb (rsv =? 0) then _ else _).
  set (mF := if rsv =? 0 then _ else _).
  assert (PF : rmrep stF mF /\ ticks_ok stF /\ s_regions stF = s_regions st2 /\ s_groups stF = s_groups st2).
  { subst stF mF. destruct (Z.eqb_spec rsv 0) as [E|NE]; cbn [negb].
    - split; [exact ME|]. split; [exact TE|]. split; assumption.
    - destruct (rwr8_rep _ _ (snd b + (UNIT + stride * k) + (stride - IB) + - rsv) 0 ME TE ERc EGc) as [MF TF]; [unfold rsv, po, UNIT, IB; lia| lia|].
      replace (P0 + stride - 4 - rsv) with (r_base r + (snd b + (UNIT + stride * k) + (stride - IB) + - rsv)) by (unfold P0, UNIT, IB; lia).
      split; [exact MF|]. split; [exact TF|]. split; assumption. }
  clearbody stF mF. destruct PF as (MF & TF & ERf & EGf).
  set (stG := if 5 <=? rsv then _ else _).
  set (mG := if 5 <=? rsv then _ else _).
  assert (PG : rmrep (fst stG) (fst mG) /\ ticks_ok (fst stG) /\ snd stG = snd mG /\ 0 <= snd mG <= 5
                /\ s_regions (fst stG) = s_regions st2 /\ s_groups (fst stG) = s_groups st2).
  { subst stG mG. destruct (Z.leb_spec 5 rsv) as [LE|GT]; cbn [fst snd].
    - (* [comment removed for export] *)
      rewrite (wr32_wr8_comm (fst b, snd b + (UNIT + stride * k) + (stride - IB) + -4) (fst b, snd b + (UNIT + stride * k) + (stride - IB) + -5)) by (cbn; lia || reflexivity).
      destruct (rwr8_rep _ _ (snd b + (UNIT + stride * k) + (stride - IB) + -5) 0 MF TF ERf EGf) as [M1 T1]; [unfold UNIT, IB; lia| lia|].
      destruct (rwr32_rep _ _ (snd b + (UNIT + stride * k) + (stride - IB) + -4) rsv M1 T1 ERf EGf) as [M2 T2]; [unfold UNIT, IB; lia| unfold UNIT, IB; lia| lia|].
      replace (P0 + stride - 4 - 4) with (r_base r + (snd b + (UNIT + stride * k) + (stride - IB) + -4)) by (unfold P0, UNIT, IB; lia).
      replace (P0 + stride - 4 - 5) with (r_base r + (snd b + (UNIT + stride * k) + (stride - IB) + -5)) by (unfold P0, UNIT, IB; lia).
      split; [exact M2|]. split; [exact T2|]. split; [reflexivity|]. split; [lia|]. split; assumption.
    - split; [exact MF|]. split; [exact TF|]. split; [reflexivity|]. split; [lia|]. split; assumption. }
  clearbody stG mG. destruct stG as [stg r1]. destruct mG as [mg r2]. cbn [fst snd] in PG |- *.
  destruct PG as (MG & TG & -> & R2 & ERg & EGg).
  assert (KV : 0 <= Z.land k 31 + Z.shiftl r2 5 < 256).
  { rewrite Z.shiftl_mul_pow2 by lia. change (2^5) with 32.
    assert (0 <= Z.land k 31 <= k) by (split; [apply Z.land_nonneg; lia| apply land_le_l; lia]). lia. }
  destruct (rwr8_rep _ _ (po + -3) (Z.land k 31 + Z.shiftl r2 5) MG TG ERg EGg) as [MH TH]; [unfold po, UNIT; lia| exact KV|].
  split; [exact MH|]. split; [exact TH|].
  split; [|split; [reflexivity| unfold po, UNIT; lia]].
  rewrite (conc_region' st2 (fst b, po) r Hr). cbn [snd]. exact (eq_sym Epo).
Qed.
End ENFRAME.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rpres_enframe : forall (C : Z -> Prop) m0 m4 P0 stride off n k B,
  rpres_except C m0 m4 ->
  0 <= off -> 0 <= n -> 16 * off + n + 4 <= stride -> 4 <= P0 -> P0 + stride <= 2^64 ->
  (forall x, P0 - 4 <= x < P0 + stride - 4 -> C x) ->
  rpres_except C m0 (renframe_tail_mem (renframe_off_mem m4 P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16)).
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros C m0 m4 P0 stride off n k B HP OFF0 N0 FIT P4 PS HC.
  assert (L2 : forall w, length (le2 w) = 2%nat) by (intros; reflexivity).
  assert (L4 : forall w, length (le4 w) = 4%nat) by (intros; reflexivity).
  assert (HO : rpres_except C m0 (renframe_off_mem m4 P0 off)).
  { unfold renframe_off_mem. destruct (off =? 0); [exact HP|].
    apply rpres_write; [| lia | cbn; lia | cbn; intros; apply HC; lia].
    apply rpres_write; [| lia | rewrite L2; lia | rewrite L2; intros; apply HC; lia].
    apply rpres_write; [exact HP| lia | cbn; lia | cbn; intros; apply HC; lia]. }
  unfold renframe_tail_mem. cbv zeta.
  set (mE := write_to_mem (write_to_mem (renframe_off_mem m4 P0 off) _ _) _ _).
  assert (HE : rpres_except C m0 mE).
  { subst mE. apply rpres_write; [| lia | rewrite L2; lia | rewrite L2; intros; apply HC; lia].
    apply rpres_write; [exact HO| lia | cbn; lia | cbn; intros; apply HC; lia]. }
  clearbody mE.
  set (rsv := P0 + stride - 4 - (P0 + 16 * off) - n).
  set (mF := if rsv =? 0 then _ else _).
  assert (HF : rpres_except C m0 mF).
  { subst mF. destruct (Z.eqb_spec rsv 0); [exact HE|]. apply rpres_write; [exact HE| lia | cbn; lia | cbn; intros; apply HC; lia]. }
  clearbody mF.
  set (mG := if 5 <=? rsv then _ else _).
  assert (HG : rpres_except C m0 (fst mG) /\ 0 <= snd mG <= 5).
  { subst mG. destruct (Z.leb_spec 5 rsv); cbn [fst snd].
    - split; [|lia]. apply rpres_write; [| lia | rewrite L4; lia | rewrite L4; intros; apply HC; lia].
      apply rpres_write; [exact HF| lia | cbn; lia | cbn; intros; apply HC; lia].
    - split; [exact HF| lia]. }
  clearbody mG. destruct mG as [mg r2]. cbn [fst snd] in HG |- *. destruct HG as [HG R2].
  apply rpres_write; [exact HG| lia | cbn; lia | cbn; intros; apply HC; lia].
Qed.

(* [comment removed for export] *)
Lemma rrdv_agree : forall st (m1 o : mem) (q : aptr) r (x : byte),
  rmrep st m1 -> unk_agree st o m1 ->
  (s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
  ~ grp_hdr_cov st (fst q) (snd q) ->
  bytes_at ssegs m1 (r_base r + snd q) [x] ->
  rdv pans_mem o st q = bv_unsigned x.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros st m1 o q r x MR UA Hr Hk Ho NG Hb.
  unfold rdv. destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h] eqn:E.
  - destruct (rmrep_shadow_read st m1 (fst q) r (snd q) v MR Hr Hk Ho E) as [RD Hv].
    pose proof (bytes_at_read ssegs m1 _ [x] 0 1 Hb ltac:(lia) ltac:(cbn; lia)) as RD'. cbn [firstn skipn Z.to_nat] in RD'.
    rewrite Z.add_0_r in RD'. rewrite RD in RD'. inversion RD'. rewrite b8_unsigned by lia. reflexivity.
  - unfold pans_mem. rewrite (conc_region' st q r Hr).
    destruct Hb as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn in HB. rewrite Z.add_0_r in HB.
    unfold mrd in HB |- *. rewrite <- (UA (fst q) r (snd q) h Hr Hk Ho E NG).
    destruct (m1 (wa (r_base r + snd q))) as [b|] eqn:EMX; [inversion HB; subst; reflexivity|].
    exfalso. pose proof MR as ((_ & WR & _) & _). destruct (WR _ _ Hr) as (RB0 & _ & _ & RBC & RF). ceil_facts.
    pose proof (rreserved_disjoint1 _ _ RF ltac:(lia)) as D.
    rewrite ref_seg_rom_none in HB; [discriminate|]. rewrite wa_unsigned by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma rmeta_chunk_facts : forall st m g,
  rmrep st m -> meta_slot st g ->
  let G := conc st g in
  rw_cells ssegs m G (meta_cells st (get_meta_rec st g))
  /\ 0 < G /\ G + 40 <= alloc_ceiling
  /\ (G + 40 <= 0x10000 \/ 0x22000 <= G) /\ ((G + 40 <= 0x22000 \/ 0x55000 <= G) /\ (G + 40 <= the_tb \/ the_tb + 4096 <= G))   (* [comment removed for export] *)
  /\ (forall rid' r', (s_regions st) !! rid' = Some r' -> r_kind r' = RKGroup ->
        G + 40 <= r_base r' \/ r_base r' + round_up_pg (r_len r') <= G)
  /\ (exists rid0 r0, (s_regions st) !! rid0 = Some r0 /\ r_kind r0 <> RKGroup
        /\ lr_lo r0 <= G /\ G + 40 <= r_base r0 + round_up_pg (r_len r0)).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros st m g MR MS G.
  split; [apply rmrep_meta_chunk; assumption|].
  pose proof MR as (WF & _). pose proof WF as (_ & WR & DISJ & _).
  destruct MS as (a & ara & kk & Ha & Hkk & Eg).
  destruct (rarea_conc st a ara WF Ha) as (rga & Hra & Ca & Sa0 & Sa1 & SaL & NK & RaB0 & RaAL & RaC).
  pose proof (rarea_lr_lo st a ara rga WF Ha Hra) as LRa.
  destruct (WR (fst a) rga Hra) as (_ & _ & _ & _ & RFa). pose proof (rreserved_disjoint2 _ _ RFa ltac:(pose proof (round_up_pg_ge (r_len rga)); lia)) as [DA1 DA2].
  assert (HG : G = r_base rga + snd a + (AREA_HDR + META_SIZE * kk)).
  { subst G. rewrite Eg, conc_aadd by (rewrite Hra; eauto). rewrite (conc_region' st a rga Hra). reflexivity. }
  unfold AREA_HDR, META_SIZE, NSLOTS in HG, Hkk. clearbody G.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split.
  - intros rid' r' Hr' Hk'. pose proof (lr_lo_group r' Hk') as LR'.
    assert (NE : rid' <> fst a) by (intros ->; rewrite Hra in Hr'; inversion Hr'; subst; congruence).
    destruct (DISJ rid' r' (fst a) rga Hr' Hra NE); lia.
  - exists (fst a), rga. split; [exact Hra|]. split; [exact NK|]. lia.
Qed.

(* [comment removed for export] *)
Lemma rregion_facts : forall st m rid r,
  rmrep st m -> (s_regions st) !! rid = Some r ->
  4096 <= r_base r /\ r_base r mod 4096 = 0 /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
  /\ (0 < round_up_pg (r_len r) -> r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x22000 <= r_base r)
  /\ (0 < round_up_pg (r_len r) -> (r_base r + round_up_pg (r_len r) <= 0x22000 \/ 0x55000 <= r_base r)
                                   /\ (r_base r + round_up_pg (r_len r) <= the_tb \/ the_tb + 4096 <= r_base r)).   (* [comment removed for export] *)
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros st m rid r (WF & _) Hr. pose proof WF as (_ & WR & _).
  destruct (WR rid r Hr) as (RB0 & RBAL & RL0 & RBC & RFr).
  split; [|split; [exact RBAL| split; [exact RBC| split; intros Hn; destruct (rreserved_disjoint2 _ _ RFr Hn); assumption]]].
  clear RFr. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Section SLOT.
Variables (st : mstate) (m1 o : mem) (g b : aptr) (r : region) (idx n : Z).
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let B := conc st b.
Let P0 := B + 16 + stride * idx.

Hypothesis MR : rmrep st m1.
Hypothesis UA : unk_agree st o m1.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hr : (s_regions st) !! (fst b) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis B0 : 0 <= snd b.
Hypothesis IDX : 0 <= idx.
Hypothesis SPAN : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r).
Hypothesis S16 : 16 <= stride.
Hypothesis B16 : snd b mod 16 = 0.
Hypothesis SMOD : stride mod 16 = 0.
Hypothesis NOGRP : forall b' gh, (s_groups st) !! b' = Some gh -> fst b' = fst b ->
  snd b' + 9 <= snd b + 16 + stride * idx - 4 \/ snd b + 16 + stride * idx + stride - 4 <= snd b'.
Hypothesis HDR0 : cell_read (get_shadow st (fst b)) (snd b + 16 + stride * idx - 4) = Known 0.

Lemma rslot_facts :
  exists x3 x2 x1 : byte,
    wr_at ssegs m1 (P0 - 4) stride
    /\ bytes_at ssegs m1 (P0 - 4) [b8 0; b8 (bv_unsigned x3); b8 (bv_unsigned x2); b8 (bv_unsigned x1)]
    /\ rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -3) = bv_unsigned x3
    /\ rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -2) = bv_unsigned x2
    /\ rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -2 + 1) = bv_unsigned x1
    /\ B = r_base r + snd b /\ 4096 <= r_base r
    /\ P0 + stride <= r_base r + round_up_pg (r_len r) /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
    /\ (r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x22000 <= r_base r).
Proof using B0 B16 HDR0 Hk Hr IDX MR S16 SMOD SPAN TLSFACTS UA. pin_using (fun (B0 B16 HDR0 Hk Hr IDX MR S16 SMOD SPAN TLSFACTS UA : unit) => tt). ceil_facts. msec_facts.
  pose proof (rregion_facts st m1 (fst b) r MR Hr) as (R4 & RAL & RC & RI1 & RI2). ceil_facts.
  assert (CB : B = r_base r + snd b) by (apply conc_region'; exact Hr).
  assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
  rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN.
  pose proof MR as (_ & _ & _ & _ & _ & SH). destruct (SH (fst b) r Hr Hk) as [HWr HB].
  assert (WRs : wr_at ssegs m1 (P0 - 4) stride) by (eapply wr_at_sub; [exact HWr| unfold P0; lia| unfold P0; lia]).
  destruct (HB (snd b + 16 + stride * idx - 4) 0 ltac:(lia) HDR0) as [Y4 _].
  assert (WR3 : wr_at ssegs m1 (P0 - 3) 3) by (eapply wr_at_sub; [exact WRs|lia|lia]).
  destruct (rwr_at_bytes_exist m1 (P0 - 3) 3 WR3 ltac:(lia) ltac:(unfold P0; lia)) as (bs & Lbs & Ybs).
  destruct bs as [|x3 [|x2 [|x1 [|? ?]]]]; try discriminate. clear Lbs.
  exists x3, x2, x1.
  assert (NG : forall d, 1 <= d <= 3 -> ~ grp_hdr_cov st (fst b) (snd b + 16 + stride * idx - d)).
  { intros d Hd (b' & gh & Hb' & Hf & Hc).
    pose proof MR as (WF' & _). destruct WF' as (_ & _ & _ & _ & WG). destruct (WG b' gh Hb') as (r' & _ & _ & _ & _ & AL').
    clear - Hd Hc AL' B16 SMOD IDX S16.
    destruct (Z.mod_divide stride 16 ltac:(lia)) as [D _]. destruct (D SMOD) as [q Hq].
    assert (E : stride * idx = 16 * (q * idx)) by (rewrite Hq; ring).
    set (w := q * idx) in E. clearbody w. Z.div_mod_to_equations. lia. }
  pose proof Ybs as (_ & _ & YB).
  assert (Y3 : bytes_at ssegs m1 (r_base r + (snd b + 16 + stride * idx - 3)) [x3]).
  { split; [lia|]. split; [change (Z.of_nat (length [x3])) with 1; lia|]. intros i Hi. destruct i; [|cbn in Hi; lia].
    pose proof (YB 0%nat ltac:(cbn; lia)) as YB0. cbn [nth_error Z.of_nat] in YB0 |- *.
    replace (r_base r + (snd b + 16 + stride * idx - 3) + 0) with (P0 - 3 + 0) by (unfold P0; lia). exact YB0. }
  assert (Y2 : bytes_at ssegs m1 (r_base r + (snd b + 16 + stride * idx - 2)) [x2]).
  { split; [lia|]. split; [change (Z.of_nat (length [x2])) with 1; lia|]. intros i Hi. destruct i; [|cbn in Hi; lia].
    pose proof (YB 1%nat ltac:(cbn; lia)) as YB1. cbn [nth_error Z.of_nat Pos.of_succ_nat Pos.succ] in YB1 |- *.
    replace (r_base r + (snd b + 16 + stride * idx - 2) + 0) with (P0 - 3 + 1) by (unfold P0; lia). exact YB1. }
  assert (Y1 : bytes_at ssegs m1 (r_base r + (snd b + 16 + stride * idx - 1)) [x1]).
  { split; [lia|]. split; [change (Z.of_nat (length [x1])) with 1; lia|]. intros i Hi. destruct i; [|cbn in Hi; lia].
    pose proof (YB 2%nat ltac:(cbn; lia)) as YB2. cbn [nth_error Z.of_nat Pos.of_succ_nat Pos.succ] in YB2 |- *.
    replace (r_base r + (snd b + 16 + stride * idx - 1) + 0) with (P0 - 3 + 2) by (unfold P0; lia). exact YB2. }
  split; [exact WRs|].
  split.
  { rewrite !b8_of_byte. change [b8 0; x3; x2; x1] with ([b8 0] ++ ([x3] ++ ([x2] ++ [x1]))).
    apply bytes_at_app. split; [eapply (bytes_at_at _ _ _ _ _ Y4); unfold P0; lia|]. cbn [length Z.of_nat Pos.of_succ_nat].
    apply bytes_at_app. split; [eapply (bytes_at_at _ _ _ _ _ Y3); unfold P0; lia|]. cbn [length Z.of_nat Pos.of_succ_nat].
    apply bytes_at_app. split; [eapply (bytes_at_at _ _ _ _ _ Y2); unfold P0; lia|]. cbn [length Z.of_nat Pos.of_succ_nat Pos.to_nat].
    eapply (bytes_at_at _ _ _ _ _ Y1); unfold P0; lia. }
  split.
  { apply (rrdv_agree st m1 o (fst b, _) r x3 MR UA Hr Hk); cbn [fst snd]; [lia| |].
    - replace (snd b + (16 + stride * idx) + -3) with (snd b + 16 + stride * idx - 3) by lia. apply NG; lia.
    - eapply bytes_at_at; [exact Y3| lia]. }
  split.
  { apply (rrdv_agree st m1 o (fst b, _) r x2 MR UA Hr Hk); cbn [fst snd]; [lia| |].
    - replace (snd b + (16 + stride * idx) + -2) with (snd b + 16 + stride * idx - 2) by lia. apply NG; lia.
    - eapply bytes_at_at; [exact Y2| lia]. }
  split.
  { apply (rrdv_agree st m1 o (fst b, _) r x1 MR UA Hr Hk); cbn [fst snd]; [lia| |].
    - replace (snd b + (16 + stride * idx) + -2 + 1) with (snd b + 16 + stride * idx - 1) by lia. apply NG; lia.
    - eapply bytes_at_at; [exact Y1| lia]. }
  split; [exact CB|]. split; [exact R4|]. split; [unfold P0; lia|]. split; [exact RC| apply RI1; unfold P0 in *; lia].
Qed.
End SLOT.

(* [comment removed for export] *)
Definition rmalloc_fp (st st' : mstate) (lo sp : Z) (a : Z) : Prop :=
  ralloc_fp (fun k => k <> RKGroup) st' lo sp a \/ new_reg_addr st st' a \/ free_slot_addr st a \/ grp_hdr_addr st a
  \/ fresh_addr st a.

Lemma rmalloc_fp_mono st sta stb lo sp a :
  (forall rid r, (s_regions sta) !! rid = Some r ->
     exists r', (s_regions stb) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r') ->
  rmalloc_fp st sta lo sp a -> rmalloc_fp st stb lo sp a.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros HR [H|[H|H]]; [| right; left | right; right; exact H].
  - destruct H as [H|[H|[H|(rid & r & Hr & Hk & Ha)]]]; [left; left; exact H| left; right; left; exact H| left; right; right; left; exact H|].
    destruct (HR rid r Hr) as (r' & Hr' & K' & B' & L').
    left. right. right. right. exists rid, r'. split; [exact Hr'|]. split; [congruence|].
    assert (LRE : lr_lo r' = lr_lo r) by (unfold lr_lo; rewrite K', B'; reflexivity).
    pose proof (round_up_pg_mono (r_len r) (r_len r') L'). lia.
  - destruct H as (rid & r & Hr & Hn & Ha). destruct (HR rid r Hr) as (r' & Hr' & K' & B' & L').
    exists rid, r'. split; [exact Hr'|]. split; [exact Hn|].
    assert (LRE : lr_lo r' = lr_lo r) by (unfold lr_lo; rewrite K', B'; reflexivity).
    pose proof (round_up_pg_mono (r_len r) (r_len r') L'). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FASTFACTS.
Variables (st : mstate) (LB : list block) (sc n : Z) (g : aptr) (k : Z) (t : N).
Let st1 := set_tick t st.
Let mr := get_meta_rec st g.
Let st2 := upd_meta g (m_set_avail (m_avail mr - 2 ^ k)) st1.
Hypothesis MF : RMFACTS st LB.
Hypothesis ACT : active st sc = Some g.
Hypothesis AV : 0 < m_avail mr.
Hypothesis K0 : 0 <= k.
Hypothesis LBK : lowbit (m_avail mr) = 2 ^ k.
Hypothesis N0 : 0 <= n.
Hypothesis NFIT : n + 4 <= 16 * size_class sc.

Lemma rget_meta_rec_st2 : get_meta_rec st2 g = m_set_avail (m_avail mr - 2 ^ k) mr.
Proof using CEILV MSECV st1. pin_using (fun (CEILV MSECV st1 : unit) => tt). ceil_facts. msec_facts. unfold st2. rewrite get_meta_rec_upd_same. reflexivity. Qed.

Lemma rfast_slot_ok : exists b r,
  slot_ok st2 g b r k n
  /\ (forall a, r_base r + snd b + 16 + get_stride mr * k - 4 <= a < r_base r + snd b + 16 + get_stride mr * k + get_stride mr - 4 ->
        free_slot_addr st a)
  /\ k < 32 /\ m_mem mr = Some b /\ (s_regions st) !! (fst b) = Some r.
Proof using ACT AV K0 LBK MF MSECV N0 NFIT TLSFACTS st1. pin_using (fun (ACT AV K0 LBK MF MSECV N0 NFIT TLSFACTS st1 : unit) => tt). ceil_facts. msec_facts.
  pose proof (mf_active _ _ MF) as FA. change (fact_active (strip st)) with (fact_active st) in FA.
  destruct (FA sc g ACT) as (SC48 & GSC & MEMnn). change (get_meta_rec st g) with mr in GSC, MEMnn.
  destruct (m_mem mr) as [b|] eqn:Hmem; [|congruence]. clear MEMnn.
  pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
  specialize (FG g b Hmem). change (get_meta_rec st g) with mr in FG. cbv zeta in FG.
  destruct FG as (MSL & AVr & FRr & LI & FB & SCr & ML0 & (ai & Hgh & AI & AVAI) & (r & Hr & Hk & B0 & B16 & SPAN) & S16 & SMOD & S31 & UND & S20).
  unfold UNIT, IB in *.
  assert (TBk : Z.testbit (m_avail mr) k = true) by (apply lowbit_testbit; assumption).
  pose proof (AVAI k K0 TBk) as KAI.
  assert (K32 : k < 32) by lia.
  assert (P2k : 0 < 2 ^ k <= m_avail mr).
  { split; [apply Z.pow_pos_nonneg; lia|]. destruct (lowbit_pow2 (m_avail mr) AV) as (k' & _ & E' & LE'). unfold lowbit in LBK.
    rewrite LBK in E'. rewrite E'. exact LE'. }
  assert (GSC48 : m_sizeclass mr < 48) by lia. specialize (S31 GSC48).
  destruct SCr as [[GS0 MPL]|[E63 _]]; [|lia].
  pose proof (mf_free_clear _ _ MF g b k Hmem K0 (or_introl TBk)) as FC. cbv zeta in FC. destruct FC as [NOGRP _].
  change (get_meta_rec (strip st) g) with mr in NOGRP. change (s_groups (strip st)) with (s_groups st) in NOGRP.
  unfold sstart_of in NOGRP. rewrite Hmem in NOGRP. cbn [default from_option id snd] in NOGRP. unfold UNIT, IB in NOGRP.
  pose proof (mf_hdr0 _ _ MF g b k Hmem ltac:(change (get_meta_rec st g) with mr; lia)) as K4.
  unfold sstart_of in K4. rewrite Hmem in K4. cbn [default from_option id fst snd] in K4.
  change (get_meta_rec st g) with mr in K4. unfold IB, UNIT in K4.
  unfold sstart_of in SPAN. rewrite Hmem in SPAN. cbn [default from_option id snd] in SPAN. unfold UNIT, IB in SPAN.
  exists b, r. pose proof rget_meta_rec_st2 as E2.
  split; [|split; [|split; [exact K32| split; [reflexivity| exact Hr]]]].
  - pose proof (UND GSC48 k K0 TBk) as U. rewrite GSC in U. specialize (S20 GSC48).
    constructor; rewrite ?E2; cbn [m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen m_set_avail];
      try change (get_stride (m_set_avail (m_avail mr - 2 ^ k) mr)) with (get_stride mr);
      fastfirst (first [ exact Hmem | exact Hr | exact Hk | exact MSL | exact K4 | exact NOGRP | exact N0 | exact SMOD
            | (pose proof (mf_slots_complete _ _ MF g b k Hmem ltac:(change (get_meta_rec (strip st) g) with mr; lia)) as SC;
               change (get_meta_rec (strip st) g) with mr in SC; unfold sstart_of in SC; rewrite Hmem in SC;
               cbn [default from_option id snd] in SC; unfold UNIT in SC; exact SC)
            | (intros off O0 OF;
               assert (get_stride mr * k + 16 * off < get_stride mr * (k + 1)) by lia;
               assert (get_stride mr * (k + 1) <= get_stride mr * (m_last_idx mr + 1)) by (apply Z.mul_le_mono_nonneg_l; lia);
               apply Z.div_lt_upper_bound; lia)
            | lia ]).
  - intros a Ha. exists g, b, r, k. split; [exact Hmem|]. split; [exact Hr|]. split; [exact Hk|]. split; [exact K0|]. split; [left; exact TBk|].
    unfold sstart_of. rewrite Hmem. cbn [default from_option id snd]. unfold UNIT, IB. fold mr.
    assert (get_stride mr * k + get_stride mr <= get_stride mr * m_last_idx mr + get_stride mr) by (apply Z.add_le_mono_r; apply Z.mul_le_mono_nonneg_l; lia).
    assert (0 <= get_stride mr * k) by (apply Z.mul_nonneg_nonneg; lia).
    lia.
Qed.
End FASTFACTS.

End PORT.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.TlsBaseU.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.SFModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_enframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A.
Export OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.Malloc_fp.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_enframe.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocKit_A.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MSecret.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.

Notation RMFACTS := (MFACTS_g (resv:=ref_reserved)).

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Lemma rreserved_disjoint2 : forall b n, ranges_free ref_reserved b n = true -> 0 < n ->
  (b + n <= 0x10000 \/ 0x22000 <= b) /\ ((b + n <= 0x22000 \/ 0x56000 <= b) /\ (b + n <= the_tb \/ the_tb + 4096 <= b)).
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts. intros b n H Hn. pose proof (rreserved_disjoint b n H). pose proof (rreserved_tls b n H Hn). lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wr8_comm p q v w st : fst p = fst q -> snd p <> snd q -> wr8 p v (wr8 q w st) = wr8 q w (wr8 p v st).
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  intros Hf Hs.
  assert (E : forall (a b : aptr) x y s, fst a = fst b -> snd a <> snd b ->
     wr8 a x (wr8 b y s) = set_shadow (<[fst a := mkShadow (<[snd a := (Z.land x 255, s_tick s)]> (<[snd b := (Z.land y 255, s_tick s)]> (r_cells (get_shadow s (fst a))))) (r_hav (get_shadow s (fst a))) (r_havp (get_shadow s (fst a)))]> (s_shadow s)) s).
  { intros a b x y s Ef Ns. unfold wr8 at 1. unfold upd_shadow. rewrite Ef, get_shadow_wr8_same. cbn [r_cells r_hav r_havp].
    rewrite s_shadow_wr8, <- Ef. change (s_tick (wr8 b y s)) with (s_tick s). rewrite insert_insert_eq. reflexivity. }
  rewrite (E p q), (E q p) by (congruence || (symmetry; congruence) || auto). rewrite Hf.
  rewrite (insert_insert_ne _ (snd p) (snd q)) by exact Hs. reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Section ENFRAME.
Variables (st2 : mstate) (m4 : mem) (g b : aptr) (r : region) (k n off : Z).
Let mr := get_meta_rec st2 g.
Let stride := get_stride mr.
Let B := conc st2 b.
Let P0 := B + 16 + stride * k.

Hypothesis MR : rmrep st2 m4.
Hypothesis TK : ticks_ok st2.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hr : (s_regions st2) !! (fst b) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis B0 : 0 <= snd b.
Hypothesis K0 : 0 <= k < 32.
Hypothesis SPAN : snd b + 16 + stride * (k + 1) <= round_up_pg (r_len r).
Hypothesis S16 : 16 <= stride.
Hypothesis S31 : stride - 4 - n < 2^31.
Hypothesis NOGRP : forall b' gh, (s_groups st2) !! b' = Some gh -> fst b' = fst b ->
  snd b' + 9 <= snd b + 16 + stride * k - 4 \/ snd b + 16 + stride * k + stride - 4 <= snd b'.
Hypothesis OFF0 : 0 <= off.
Hypothesis N0 : 0 <= n.
Hypothesis FIT : 16 * off + n + 4 <= stride.
Hypothesis Q16 : (stride * k + 16 * off) / 16 < 65536.

Lemma rconc_b : B = r_base r + snd b.
Proof using CEILV Hr MSECV. pin_using (fun (CEILV Hr MSECV : unit) => tt). ceil_facts. msec_facts. unfold B. apply (conc_region' st2 b r Hr). Qed.

Lemma rsk_nonneg : 0 <= stride * k.
Proof using K0 MSECV P0 S16 TLSFACTS off. pin_using (fun (K0 MSECV P0 S16 TLSFACTS off : unit) => tt). ceil_facts. msec_facts. apply Z.mul_nonneg_nonneg; lia. Qed.

(* [comment removed for export] *)
Lemma rwr8_rep : forall stx mx (o v : Z),
  rmrep stx mx -> ticks_ok stx ->
  s_regions stx = s_regions st2 -> s_groups stx = s_groups st2 ->
  snd b + 16 + stride * k - 4 <= o < snd b + 16 + stride * k + stride - 4 ->
  0 <= v < 256 ->
  rmrep (wr8 (fst b, o) v stx) (write_to_mem mx (wa (r_base r + o)) [b8 v]) /\ ticks_ok (wr8 (fst b, o) v stx).
Proof using B0 Hk Hr K0 NOGRP OFF0 P0 S16 SPAN. pin_using (fun (B0 Hk Hr K0 NOGRP OFF0 P0 S16 SPAN : unit) => tt). ceil_facts. msec_facts.
  intros stx mx o v MRx TKx ER EG Ho Hv. pose proof rsk_nonneg.
  split; [|apply ticks_ok_wr8; exact TKx].
  apply (rmrep_wr8 stx mx (fst b, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| lia| |exact Hv].
  intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); lia.
Qed.

Lemma rwr16_rep : forall stx mx (o v : Z),
  rmrep stx mx -> ticks_ok stx ->
  s_regions stx = s_regions st2 -> s_groups stx = s_groups st2 ->
  snd b + 16 + stride * k - 4 <= o -> o + 2 <= snd b + 16 + stride * k + stride - 4 ->
  0 <= v < 65536 ->
  rmrep (wr16 (fst b, o) v stx) (write_to_mem mx (wa (r_base r + o)) (le2 (wz v))) /\ ticks_ok (wr16 (fst b, o) v stx).
Proof using B0 Hk Hr K0 NOGRP OFF0 P0 S16 SPAN. pin_using (fun (B0 Hk Hr K0 NOGRP OFF0 P0 S16 SPAN : unit) => tt). ceil_facts. msec_facts.
  intros stx mx o v MRx TKx ER EG Ho Ho2 Hv. pose proof rsk_nonneg.
  split; [|apply ticks_ok_wr16; exact TKx].
  apply (rmrep_wr16 stx mx (fst b, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| lia| lia| |exact Hv].
  intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); lia.
Qed.

Lemma rwr32_rep : forall stx mx (o v : Z),
  rmrep stx mx -> ticks_ok stx ->
  s_regions stx = s_regions st2 -> s_groups stx = s_groups st2 ->
  snd b + 16 + stride * k - 4 <= o -> o + 4 <= snd b + 16 + stride * k + stride - 4 ->
  0 <= v < 2^32 ->
  rmrep (wr32 (fst b, o) v stx) (write_to_mem mx (wa (r_base r + o)) (le4 (wz v))) /\ ticks_ok (wr32 (fst b, o) v stx).
Proof using B0 Hk Hr K0 NOGRP OFF0 P0 S16 SPAN. pin_using (fun (B0 Hk Hr K0 NOGRP OFF0 P0 S16 SPAN : unit) => tt). ceil_facts. msec_facts.
  intros stx mx o v MRx TKx ER EG Ho Ho4 Hv. pose proof rsk_nonneg.
  apply (rmrep_wr32 stx mx (fst b, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| lia| lia| |exact Hv].
  intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); lia.
Qed.

(* [comment removed for export] *)
Lemma wr16_wr8_comm p q v w st : fst p = fst q -> snd q <> snd p -> snd q <> snd p + 1 ->
  wr8 q w (wr16 p v st) = wr16 p v (wr8 q w st).
Proof using K0 MSECV P0 TLSFACTS off. pin_using (fun (K0 MSECV P0 TLSFACTS off : unit) => tt). ceil_facts. msec_facts.
  intros Hf H0 H1. unfold wr16.
  rewrite (wr8_comm q (aadd p 1)) by (unfold aadd; cbn; lia || auto).
  rewrite (wr8_comm q p) by (auto || lia). reflexivity.
Qed.

Lemma wr32_wr8_comm p q v w st : fst p = fst q -> snd q + 1 = snd p ->
  wr8 q w (wr32 p v st) = wr32 p v (wr8 q w st).
Proof using K0 MSECV P0 TLSFACTS off. pin_using (fun (K0 MSECV P0 TLSFACTS off : unit) => tt). ceil_facts. msec_facts.
  intros Hf H1. unfold wr32.
  rewrite (wr8_comm q (aadd p 3)) by (unfold aadd; cbn; lia || auto).
  rewrite (wr8_comm q (aadd p 2)) by (unfold aadd; cbn; lia || auto).
  rewrite (wr8_comm q (aadd p 1)) by (unfold aadd; cbn; lia || auto).
  rewrite (wr8_comm q p) by (auto || lia). reflexivity.
Qed.

Lemma renframe_mrep :
  let res := enframe_at st2 g k n off in
  rmrep (fst res) (renframe_tail_mem (renframe_off_mem m4 P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16))
  /\ ticks_ok (fst res)
  /\ conc st2 (snd res) = P0 + 16 * off /\ fst (snd res) = fst b /\ snd (snd res) = snd b + 16 + stride * k + 16 * off.
Proof using B0 FIT Hk Hmem Hr K0 MR N0 NOGRP OFF0 Q16 S16 S31 SPAN TK. pin_using (fun (B0 FIT Hk Hmem Hr K0 MR N0 NOGRP OFF0 Q16 S16 S31 SPAN TK : unit) => tt). ceil_facts. msec_facts.
  pose proof rconc_b as CB. pose proof rsk_nonneg as SK.
  cbv zeta. unfold enframe_at. fold mr. fold stride. rewrite Hmem. cbn [default from_option id fst snd].
  unfold aadd. cbn [fst snd].
  (* [comment removed for export] *)
  set (stC := if negb (off =? 0) then _ else _).
  assert (PRE : rmrep (fst stC) (renframe_off_mem m4 P0 off) /\ ticks_ok (fst stC)
                /\ snd stC = (fst b, snd b + (UNIT + stride * k) + UNIT * off)
                /\ s_regions (fst stC) = s_regions st2 /\ s_groups (fst stC) = s_groups st2
                /\ (forall q, conc (fst stC) q = conc st2 q)).
  { subst stC. unfold renframe_off_mem. destruct (Z.eqb_spec off 0) as [E|NE]; cbn [negb fst snd].
    - subst off. rewrite Z.mul_0_r, Z.add_0_r.
      split; [exact MR|]. split; [exact TK|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros; reflexivity.
    - (* [comment removed for export] *)
      rewrite (wr16_wr8_comm (fst b, snd b + (UNIT + stride * k) + -2) (fst b, snd b + (UNIT + stride * k) + -3)) by (cbn; lia || reflexivity).
      destruct (rwr8_rep st2 m4 (snd b + (UNIT + stride * k) + -3) 224 MR TK eq_refl eq_refl) as [M1 T1]; [unfold UNIT; lia| lia|].
      destruct (rwr16_rep _ _ (snd b + (UNIT + stride * k) + -2) off M1 T1 eq_refl eq_refl) as [M2 T2]; [unfold UNIT; lia| unfold UNIT; lia| lia|].
      destruct (rwr8_rep _ _ (snd b + (UNIT + stride * k) + UNIT * off + -4) 0 M2 T2 eq_refl eq_refl) as [M3 T3]; [unfold UNIT; lia| lia|].
      unfold UNIT in *.
      replace (P0 - 2) with (r_base r + (snd b + (16 + stride * k) + -2)) by (unfold P0; lia).
      replace (P0 - 3) with (r_base r + (snd b + (16 + stride * k) + -3)) by (unfold P0; lia).
      replace (P0 + 16 * off - 4) with (r_base r + (snd b + (16 + stride * k) + 16 * off + -4)) by (unfold P0; lia).
      split; [exact M3|]. split; [exact T3|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros; reflexivity. }
  clearbody stC. destruct stC as [stc p']. cbn [fst snd] in PRE. destruct PRE as (MC & TC & -> & ERc & EGc & CONCc).
  cbn [fst snd].
  unfold renframe_tail_mem. cbv zeta.
  (* [comment removed for export] *)
  set (po := snd b + (UNIT + stride * k) + UNIT * off).
  assert (Epo : P0 + 16 * off = r_base r + po) by (unfold po, P0, UNIT; lia).
  assert (Eq : (P0 + 16 * off - B - 16) / 16 = (po - (snd b + UNIT)) / UNIT).
  { unfold po, P0, UNIT. f_equal; lia. }
  rewrite Eq.
  assert (QB : 0 <= (po - (snd b + UNIT)) / UNIT < 65536).
  { unfold po, UNIT. replace (snd b + (16 + stride * k) + 16 * off - (snd b + 16)) with (stride * k + 16 * off) by lia.
    split; [apply Z.div_pos; lia| exact Q16]. }
  (* [comment removed for export] *)
  rewrite (wr16_wr8_comm (fst b, po + -2) (fst b, po + -3)) by (cbn; lia || reflexivity).
  destruct (rwr8_rep _ _ (po + -3) k MC TC ERc EGc) as [MD TD]; [unfold po, UNIT; lia| lia|].
  destruct (rwr16_rep _ _ (po + -2) ((po - (snd b + UNIT)) / UNIT) MD TD ERc EGc) as [ME TE]; [unfold po, UNIT; lia| unfold po, UNIT; lia| lia|].
  replace (P0 + 16 * off - 2) with (r_base r + (po + -2)) by lia.
  replace (P0 + 16 * off - 3) with (r_base r + (po + -3)) by lia.
  (* [comment removed for export] *)
  unfold set_size, aadd. cbn [fst snd id].
  set (rsv := snd b + (UNIT + stride * k) + (stride - IB) - po - n).
  assert (Ersv : P0 + stride - 4 - (P0 + 16 * off) - n = rsv) by (unfold rsv, po, P0, UNIT, IB; lia).
  rewrite Ersv.
  assert (RSV : 0 <= rsv <= stride - 4 - n) by (unfold rsv, po, UNIT, IB; lia).
  set (stF := if negb (rsv =? 0) then _ else _).
  set (mF := if rsv =? 0 then _ else _).
  assert (PF : rmrep stF mF /\ ticks_ok stF /\ s_regions stF = s_regions st2 /\ s_groups stF = s_groups st2).
  { subst stF mF. destruct (Z.eqb_spec rsv 0) as [E|NE]; cbn [negb].
    - split; [exact ME|]. split; [exact TE|]. split; assumption.
    - destruct (rwr8_rep _ _ (snd b + (UNIT + stride * k) + (stride - IB) + - rsv) 0 ME TE ERc EGc) as [MF TF]; [unfold rsv, po, UNIT, IB; lia| lia|].
      replace (P0 + stride - 4 - rsv) with (r_base r + (snd b + (UNIT + stride * k) + (stride - IB) + - rsv)) by (unfold P0, UNIT, IB; lia).
      split; [exact MF|]. split; [exact TF|]. split; assumption. }
  clearbody stF mF. destruct PF as (MF & TF & ERf & EGf).
  set (stG := if 5 <=? rsv then _ else _).
  set (mG := if 5 <=? rsv then _ else _).
  assert (PG : rmrep (fst stG) (fst mG) /\ ticks_ok (fst stG) /\ snd stG = snd mG /\ 0 <= snd mG <= 5
                /\ s_regions (fst stG) = s_regions st2 /\ s_groups (fst stG) = s_groups st2).
  { subst stG mG. destruct (Z.leb_spec 5 rsv) as [LE|GT]; cbn [fst snd].
    - (* [comment removed for export] *)
      rewrite (wr32_wr8_comm (fst b, snd b + (UNIT + stride * k) + (stride - IB) + -4) (fst b, snd b + (UNIT + stride * k) + (stride - IB) + -5)) by (cbn; lia || reflexivity).
      destruct (rwr8_rep _ _ (snd b + (UNIT + stride * k) + (stride - IB) + -5) 0 MF TF ERf EGf) as [M1 T1]; [unfold UNIT, IB; lia| lia|].
      destruct (rwr32_rep _ _ (snd b + (UNIT + stride * k) + (stride - IB) + -4) rsv M1 T1 ERf EGf) as [M2 T2]; [unfold UNIT, IB; lia| unfold UNIT, IB; lia| lia|].
      replace (P0 + stride - 4 - 4) with (r_base r + (snd b + (UNIT + stride * k) + (stride - IB) + -4)) by (unfold P0, UNIT, IB; lia).
      replace (P0 + stride - 4 - 5) with (r_base r + (snd b + (UNIT + stride * k) + (stride - IB) + -5)) by (unfold P0, UNIT, IB; lia).
      split; [exact M2|]. split; [exact T2|]. split; [reflexivity|]. split; [lia|]. split; assumption.
    - split; [exact MF|]. split; [exact TF|]. split; [reflexivity|]. split; [lia|]. split; assumption. }
  clearbody stG mG. destruct stG as [stg r1]. destruct mG as [mg r2]. cbn [fst snd] in PG |- *.
  destruct PG as (MG & TG & -> & R2 & ERg & EGg).
  assert (KV : 0 <= Z.land k 31 + Z.shiftl r2 5 < 256).
  { rewrite Z.shiftl_mul_pow2 by lia. change (2^5) with 32.
    assert (0 <= Z.land k 31 <= k) by (split; [apply Z.land_nonneg; lia| apply land_le_l; lia]). lia. }
  destruct (rwr8_rep _ _ (po + -3) (Z.land k 31 + Z.shiftl r2 5) MG TG ERg EGg) as [MH TH]; [unfold po, UNIT; lia| exact KV|].
  split; [exact MH|]. split; [exact TH|].
  split; [|split; [reflexivity| unfold po, UNIT; lia]].
  rewrite (conc_region' st2 (fst b, po) r Hr). cbn [snd]. exact (eq_sym Epo).
Qed.
End ENFRAME.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rpres_enframe : forall (C : Z -> Prop) m0 m4 P0 stride off n k B,
  rpres_except C m0 m4 ->
  0 <= off -> 0 <= n -> 16 * off + n + 4 <= stride -> 4 <= P0 -> P0 + stride <= 2^64 ->
  (forall x, P0 - 4 <= x < P0 + stride - 4 -> C x) ->
  rpres_except C m0 (renframe_tail_mem (renframe_off_mem m4 P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16)).
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros C m0 m4 P0 stride off n k B HP OFF0 N0 FIT P4 PS HC.
  assert (L2 : forall w, length (le2 w) = 2%nat) by (intros; reflexivity).
  assert (L4 : forall w, length (le4 w) = 4%nat) by (intros; reflexivity).
  assert (HO : rpres_except C m0 (renframe_off_mem m4 P0 off)).
  { unfold renframe_off_mem. destruct (off =? 0); [exact HP|].
    apply rpres_write; [| lia | cbn; lia | cbn; intros; apply HC; lia].
    apply rpres_write; [| lia | rewrite L2; lia | rewrite L2; intros; apply HC; lia].
    apply rpres_write; [exact HP| lia | cbn; lia | cbn; intros; apply HC; lia]. }
  unfold renframe_tail_mem. cbv zeta.
  set (mE := write_to_mem (write_to_mem (renframe_off_mem m4 P0 off) _ _) _ _).
  assert (HE : rpres_except C m0 mE).
  { subst mE. apply rpres_write; [| lia | rewrite L2; lia | rewrite L2; intros; apply HC; lia].
    apply rpres_write; [exact HO| lia | cbn; lia | cbn; intros; apply HC; lia]. }
  clearbody mE.
  set (rsv := P0 + stride - 4 - (P0 + 16 * off) - n).
  set (mF := if rsv =? 0 then _ else _).
  assert (HF : rpres_except C m0 mF).
  { subst mF. destruct (Z.eqb_spec rsv 0); [exact HE|]. apply rpres_write; [exact HE| lia | cbn; lia | cbn; intros; apply HC; lia]. }
  clearbody mF.
  set (mG := if 5 <=? rsv then _ else _).
  assert (HG : rpres_except C m0 (fst mG) /\ 0 <= snd mG <= 5).
  { subst mG. destruct (Z.leb_spec 5 rsv); cbn [fst snd].
    - split; [|lia]. apply rpres_write; [| lia | rewrite L4; lia | rewrite L4; intros; apply HC; lia].
      apply rpres_write; [exact HF| lia | cbn; lia | cbn; intros; apply HC; lia].
    - split; [exact HF| lia]. }
  clearbody mG. destruct mG as [mg r2]. cbn [fst snd] in HG |- *. destruct HG as [HG R2].
  apply rpres_write; [exact HG| lia | cbn; lia | cbn; intros; apply HC; lia].
Qed.

(* [comment removed for export] *)
Lemma rrdv_agree : forall st (m1 o : mem) (q : aptr) r (x : byte),
  rmrep st m1 -> unk_agree st o m1 ->
  (s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
  ~ grp_hdr_cov st (fst q) (snd q) ->
  bytes_at usegs m1 (r_base r + snd q) [x] ->
  rdv pans_mem o st q = bv_unsigned x.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros st m1 o q r x MR UA Hr Hk Ho NG Hb.
  unfold rdv. destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h] eqn:E.
  - destruct (rmrep_shadow_read st m1 (fst q) r (snd q) v MR Hr Hk Ho E) as [RD Hv].
    pose proof (bytes_at_read usegs m1 _ [x] 0 1 Hb ltac:(lia) ltac:(cbn; lia)) as RD'. cbn [firstn skipn Z.to_nat] in RD'.
    rewrite Z.add_0_r in RD'. rewrite RD in RD'. inversion RD'. rewrite b8_unsigned by lia. reflexivity.
  - unfold pans_mem. rewrite (conc_region' st q r Hr).
    destruct Hb as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn in HB. rewrite Z.add_0_r in HB.
    unfold mrd in HB |- *. rewrite <- (UA (fst q) r (snd q) h Hr Hk Ho E NG).
    destruct (m1 (wa (r_base r + snd q))) as [b|] eqn:EMX; [inversion HB; subst; reflexivity|].
    exfalso. pose proof MR as ((_ & WR & _) & _). destruct (WR _ _ Hr) as (RB0 & _ & _ & RBC & RF). ceil_facts.
    pose proof (rreserved_disjoint1 _ _ RF ltac:(lia)) as D.
    rewrite ref_seg_rom_none in HB; [discriminate|]. rewrite wa_unsigned by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma rmeta_chunk_facts : forall st m g,
  rmrep st m -> meta_slot st g ->
  let G := conc st g in
  rw_cells usegs m G (meta_cells st (get_meta_rec st g))
  /\ 0 < G /\ G + 40 <= alloc_ceiling
  /\ (G + 40 <= 0x10000 \/ 0x22000 <= G) /\ ((G + 40 <= 0x22000 \/ 0x56000 <= G) /\ (G + 40 <= the_tb \/ the_tb + 4096 <= G))   (* [comment removed for export] *)
  /\ (forall rid' r', (s_regions st) !! rid' = Some r' -> r_kind r' = RKGroup ->
        G + 40 <= r_base r' \/ r_base r' + round_up_pg (r_len r') <= G)
  /\ (exists rid0 r0, (s_regions st) !! rid0 = Some r0 /\ r_kind r0 <> RKGroup
        /\ lr_lo r0 <= G /\ G + 40 <= r_base r0 + round_up_pg (r_len r0)).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros st m g MR MS G.
  split; [apply rmrep_meta_chunk; assumption|].
  pose proof MR as (WF & _). pose proof WF as (_ & WR & DISJ & _).
  destruct MS as (a & ara & kk & Ha & Hkk & Eg).
  destruct (rarea_conc st a ara WF Ha) as (rga & Hra & Ca & Sa0 & Sa1 & SaL & NK & RaB0 & RaAL & RaC).
  pose proof (rarea_lr_lo st a ara rga WF Ha Hra) as LRa.
  destruct (WR (fst a) rga Hra) as (_ & _ & _ & _ & RFa). pose proof (rreserved_disjoint2 _ _ RFa ltac:(pose proof (round_up_pg_ge (r_len rga)); lia)) as [DA1 DA2].
  assert (HG : G = r_base rga + snd a + (AREA_HDR + META_SIZE * kk)).
  { subst G. rewrite Eg, conc_aadd by (rewrite Hra; eauto). rewrite (conc_region' st a rga Hra). reflexivity. }
  unfold AREA_HDR, META_SIZE, NSLOTS in HG, Hkk. clearbody G.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split.
  - intros rid' r' Hr' Hk'. pose proof (lr_lo_group r' Hk') as LR'.
    assert (NE : rid' <> fst a) by (intros ->; rewrite Hra in Hr'; inversion Hr'; subst; congruence).
    destruct (DISJ rid' r' (fst a) rga Hr' Hra NE); lia.
  - exists (fst a), rga. split; [exact Hra|]. split; [exact NK|]. lia.
Qed.

(* [comment removed for export] *)
Lemma rregion_facts : forall st m rid r,
  rmrep st m -> (s_regions st) !! rid = Some r ->
  4096 <= r_base r /\ r_base r mod 4096 = 0 /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
  /\ (0 < round_up_pg (r_len r) -> r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x22000 <= r_base r)
  /\ (0 < round_up_pg (r_len r) -> (r_base r + round_up_pg (r_len r) <= 0x22000 \/ 0x56000 <= r_base r)
                                   /\ (r_base r + round_up_pg (r_len r) <= the_tb \/ the_tb + 4096 <= r_base r)).   (* [comment removed for export] *)
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros st m rid r (WF & _) Hr. pose proof WF as (_ & WR & _).
  destruct (WR rid r Hr) as (RB0 & RBAL & RL0 & RBC & RFr).
  split; [|split; [exact RBAL| split; [exact RBC| split; intros Hn; destruct (rreserved_disjoint2 _ _ RFr Hn); assumption]]].
  clear RFr. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Section SLOT.
Variables (st : mstate) (m1 o : mem) (g b : aptr) (r : region) (idx n : Z).
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let B := conc st b.
Let P0 := B + 16 + stride * idx.

Hypothesis MR : rmrep st m1.
Hypothesis UA : unk_agree st o m1.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hr : (s_regions st) !! (fst b) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis B0 : 0 <= snd b.
Hypothesis IDX : 0 <= idx.
Hypothesis SPAN : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r).
Hypothesis S16 : 16 <= stride.
Hypothesis B16 : snd b mod 16 = 0.
Hypothesis SMOD : stride mod 16 = 0.
Hypothesis NOGRP : forall b' gh, (s_groups st) !! b' = Some gh -> fst b' = fst b ->
  snd b' + 9 <= snd b + 16 + stride * idx - 4 \/ snd b + 16 + stride * idx + stride - 4 <= snd b'.
Hypothesis HDR0 : cell_read (get_shadow st (fst b)) (snd b + 16 + stride * idx - 4) = Known 0.

Lemma rslot_facts :
  exists x3 x2 x1 : byte,
    wr_at usegs m1 (P0 - 4) stride
    /\ bytes_at usegs m1 (P0 - 4) [b8 0; b8 (bv_unsigned x3); b8 (bv_unsigned x2); b8 (bv_unsigned x1)]
    /\ rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -3) = bv_unsigned x3
    /\ rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -2) = bv_unsigned x2
    /\ rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -2 + 1) = bv_unsigned x1
    /\ B = r_base r + snd b /\ 4096 <= r_base r
    /\ P0 + stride <= r_base r + round_up_pg (r_len r) /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
    /\ (r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x22000 <= r_base r).
Proof using B0 B16 HDR0 Hk Hr IDX MR S16 SMOD SPAN TLSFACTS UA. pin_using (fun (B0 B16 HDR0 Hk Hr IDX MR S16 SMOD SPAN TLSFACTS UA : unit) => tt). ceil_facts. msec_facts.
  pose proof (rregion_facts st m1 (fst b) r MR Hr) as (R4 & RAL & RC & RI1 & RI2). ceil_facts.
  assert (CB : B = r_base r + snd b) by (apply conc_region'; exact Hr).
  assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
  rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN.
  pose proof MR as (_ & _ & _ & _ & _ & SH). destruct (SH (fst b) r Hr Hk) as [HWr HB].
  assert (WRs : wr_at usegs m1 (P0 - 4) stride) by (eapply wr_at_sub; [exact HWr| unfold P0; lia| unfold P0; lia]).
  destruct (HB (snd b + 16 + stride * idx - 4) 0 ltac:(lia) HDR0) as [Y4 _].
  assert (WR3 : wr_at usegs m1 (P0 - 3) 3) by (eapply wr_at_sub; [exact WRs|lia|lia]).
  destruct (rwr_at_bytes_exist m1 (P0 - 3) 3 WR3 ltac:(lia) ltac:(unfold P0; lia)) as (bs & Lbs & Ybs).
  destruct bs as [|x3 [|x2 [|x1 [|? ?]]]]; try discriminate. clear Lbs.
  exists x3, x2, x1.
  assert (NG : forall d, 1 <= d <= 3 -> ~ grp_hdr_cov st (fst b) (snd b + 16 + stride * idx - d)).
  { intros d Hd (b' & gh & Hb' & Hf & Hc).
    pose proof MR as (WF' & _). destruct WF' as (_ & _ & _ & _ & WG). destruct (WG b' gh Hb') as (r' & _ & _ & _ & _ & AL').
    clear - Hd Hc AL' B16 SMOD IDX S16.
    destruct (Z.mod_divide stride 16 ltac:(lia)) as [D _]. destruct (D SMOD) as [q Hq].
    assert (E : stride * idx = 16 * (q * idx)) by (rewrite Hq; ring).
    set (w := q * idx) in E. clearbody w. Z.div_mod_to_equations. lia. }
  pose proof Ybs as (_ & _ & YB).
  assert (Y3 : bytes_at usegs m1 (r_base r + (snd b + 16 + stride * idx - 3)) [x3]).
  { split; [lia|]. split; [change (Z.of_nat (length [x3])) with 1; lia|]. intros i Hi. destruct i; [|cbn in Hi; lia].
    pose proof (YB 0%nat ltac:(cbn; lia)) as YB0. cbn [nth_error Z.of_nat] in YB0 |- *.
    replace (r_base r + (snd b + 16 + stride * idx - 3) + 0) with (P0 - 3 + 0) by (unfold P0; lia). exact YB0. }
  assert (Y2 : bytes_at usegs m1 (r_base r + (snd b + 16 + stride * idx - 2)) [x2]).
  { split; [lia|]. split; [change (Z.of_nat (length [x2])) with 1; lia|]. intros i Hi. destruct i; [|cbn in Hi; lia].
    pose proof (YB 1%nat ltac:(cbn; lia)) as YB1. cbn [nth_error Z.of_nat Pos.of_succ_nat Pos.succ] in YB1 |- *.
    replace (r_base r + (snd b + 16 + stride * idx - 2) + 0) with (P0 - 3 + 1) by (unfold P0; lia). exact YB1. }
  assert (Y1 : bytes_at usegs m1 (r_base r + (snd b + 16 + stride * idx - 1)) [x1]).
  { split; [lia|]. split; [change (Z.of_nat (length [x1])) with 1; lia|]. intros i Hi. destruct i; [|cbn in Hi; lia].
    pose proof (YB 2%nat ltac:(cbn; lia)) as YB2. cbn [nth_error Z.of_nat Pos.of_succ_nat Pos.succ] in YB2 |- *.
    replace (r_base r + (snd b + 16 + stride * idx - 1) + 0) with (P0 - 3 + 2) by (unfold P0; lia). exact YB2. }
  split; [exact WRs|].
  split.
  { rewrite !b8_of_byte. change [b8 0; x3; x2; x1] with ([b8 0] ++ ([x3] ++ ([x2] ++ [x1]))).
    apply bytes_at_app. split; [eapply (bytes_at_at _ _ _ _ _ Y4); unfold P0; lia|]. cbn [length Z.of_nat Pos.of_succ_nat].
    apply bytes_at_app. split; [eapply (bytes_at_at _ _ _ _ _ Y3); unfold P0; lia|]. cbn [length Z.of_nat Pos.of_succ_nat].
    apply bytes_at_app. split; [eapply (bytes_at_at _ _ _ _ _ Y2); unfold P0; lia|]. cbn [length Z.of_nat Pos.of_succ_nat Pos.to_nat].
    eapply (bytes_at_at _ _ _ _ _ Y1); unfold P0; lia. }
  split.
  { apply (rrdv_agree st m1 o (fst b, _) r x3 MR UA Hr Hk); cbn [fst snd]; [lia| |].
    - replace (snd b + (16 + stride * idx) + -3) with (snd b + 16 + stride * idx - 3) by lia. apply NG; lia.
    - eapply bytes_at_at; [exact Y3| lia]. }
  split.
  { apply (rrdv_agree st m1 o (fst b, _) r x2 MR UA Hr Hk); cbn [fst snd]; [lia| |].
    - replace (snd b + (16 + stride * idx) + -2) with (snd b + 16 + stride * idx - 2) by lia. apply NG; lia.
    - eapply bytes_at_at; [exact Y2| lia]. }
  split.
  { apply (rrdv_agree st m1 o (fst b, _) r x1 MR UA Hr Hk); cbn [fst snd]; [lia| |].
    - replace (snd b + (16 + stride * idx) + -2 + 1) with (snd b + 16 + stride * idx - 1) by lia. apply NG; lia.
    - eapply bytes_at_at; [exact Y1| lia]. }
  split; [exact CB|]. split; [exact R4|]. split; [unfold P0; lia|]. split; [exact RC| apply RI1; unfold P0 in *; lia].
Qed.
End SLOT.

(* [comment removed for export] *)
Definition rmalloc_fp (st st' : mstate) (lo sp : Z) (a : Z) : Prop :=
  ralloc_fp (fun k => k <> RKGroup) st' lo sp a \/ new_reg_addr st st' a \/ free_slot_addr st a \/ grp_hdr_addr st a
  \/ fresh_addr st a.

Lemma rmalloc_fp_mono st sta stb lo sp a :
  (forall rid r, (s_regions sta) !! rid = Some r ->
     exists r', (s_regions stb) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r') ->
  rmalloc_fp st sta lo sp a -> rmalloc_fp st stb lo sp a.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros HR [H|[H|H]]; [| right; left | right; right; exact H].
  - destruct H as [H|[H|[H|(rid & r & Hr & Hk & Ha)]]]; [left; left; exact H| left; right; left; exact H| left; right; right; left; exact H|].
    destruct (HR rid r Hr) as (r' & Hr' & K' & B' & L').
    left. right. right. right. exists rid, r'. split; [exact Hr'|]. split; [congruence|].
    assert (LRE : lr_lo r' = lr_lo r) by (unfold lr_lo; rewrite K', B'; reflexivity).
    pose proof (round_up_pg_mono (r_len r) (r_len r') L'). lia.
  - destruct H as (rid & r & Hr & Hn & Ha). destruct (HR rid r Hr) as (r' & Hr' & K' & B' & L').
    exists rid, r'. split; [exact Hr'|]. split; [exact Hn|].
    assert (LRE : lr_lo r' = lr_lo r) by (unfold lr_lo; rewrite K', B'; reflexivity).
    pose proof (round_up_pg_mono (r_len r) (r_len r') L'). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FASTFACTS.
Variables (st : mstate) (LB : list block) (sc n : Z) (g : aptr) (k : Z) (t : N).
Let st1 := set_tick t st.
Let mr := get_meta_rec st g.
Let st2 := upd_meta g (m_set_avail (m_avail mr - 2 ^ k)) st1.
Hypothesis MF : RMFACTS st LB.
Hypothesis ACT : active st sc = Some g.
Hypothesis AV : 0 < m_avail mr.
Hypothesis K0 : 0 <= k.
Hypothesis LBK : lowbit (m_avail mr) = 2 ^ k.
Hypothesis N0 : 0 <= n.
Hypothesis NFIT : n + 4 <= 16 * size_class sc.

Lemma rget_meta_rec_st2 : get_meta_rec st2 g = m_set_avail (m_avail mr - 2 ^ k) mr.
Proof using CEILV MSECV st1. pin_using (fun (CEILV MSECV st1 : unit) => tt). ceil_facts. msec_facts. unfold st2. rewrite get_meta_rec_upd_same. reflexivity. Qed.

Lemma rfast_slot_ok : exists b r,
  slot_ok st2 g b r k n
  /\ (forall a, r_base r + snd b + 16 + get_stride mr * k - 4 <= a < r_base r + snd b + 16 + get_stride mr * k + get_stride mr - 4 ->
        free_slot_addr st a)
  /\ k < 32 /\ m_mem mr = Some b /\ (s_regions st) !! (fst b) = Some r.
Proof using ACT AV K0 LBK MF MSECV N0 NFIT TLSFACTS st1. pin_using (fun (ACT AV K0 LBK MF MSECV N0 NFIT TLSFACTS st1 : unit) => tt). ceil_facts. msec_facts.
  pose proof (mf_active _ _ MF) as FA. change (fact_active (strip st)) with (fact_active st) in FA.
  destruct (FA sc g ACT) as (SC48 & GSC & MEMnn). change (get_meta_rec st g) with mr in GSC, MEMnn.
  destruct (m_mem mr) as [b|] eqn:Hmem; [|congruence]. clear MEMnn.
  pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
  specialize (FG g b Hmem). change (get_meta_rec st g) with mr in FG. cbv zeta in FG.
  destruct FG as (MSL & AVr & FRr & LI & FB & SCr & ML0 & (ai & Hgh & AI & AVAI) & (r & Hr & Hk & B0 & B16 & SPAN) & S16 & SMOD & S31 & UND & S20).
  unfold UNIT, IB in *.
  assert (TBk : Z.testbit (m_avail mr) k = true) by (apply lowbit_testbit; assumption).
  pose proof (AVAI k K0 TBk) as KAI.
  assert (K32 : k < 32) by lia.
  assert (P2k : 0 < 2 ^ k <= m_avail mr).
  { split; [apply Z.pow_pos_nonneg; lia|]. destruct (lowbit_pow2 (m_avail mr) AV) as (k' & _ & E' & LE'). unfold lowbit in LBK.
    rewrite LBK in E'. rewrite E'. exact LE'. }
  assert (GSC48 : m_sizeclass mr < 48) by lia. specialize (S31 GSC48).
  destruct SCr as [[GS0 MPL]|[E63 _]]; [|lia].
  pose proof (mf_free_clear _ _ MF g b k Hmem K0 (or_introl TBk)) as FC. cbv zeta in FC. destruct FC as [NOGRP _].
  change (get_meta_rec (strip st) g) with mr in NOGRP. change (s_groups (strip st)) with (s_groups st) in NOGRP.
  unfold sstart_of in NOGRP. rewrite Hmem in NOGRP. cbn [default from_option id snd] in NOGRP. unfold UNIT, IB in NOGRP.
  pose proof (mf_hdr0 _ _ MF g b k Hmem ltac:(change (get_meta_rec st g) with mr; lia)) as K4.
  unfold sstart_of in K4. rewrite Hmem in K4. cbn [default from_option id fst snd] in K4.
  change (get_meta_rec st g) with mr in K4. unfold IB, UNIT in K4.
  unfold sstart_of in SPAN. rewrite Hmem in SPAN. cbn [default from_option id snd] in SPAN. unfold UNIT, IB in SPAN.
  exists b, r. pose proof rget_meta_rec_st2 as E2.
  split; [|split; [|split; [exact K32| split; [reflexivity| exact Hr]]]].
  - pose proof (UND GSC48 k K0 TBk) as U. rewrite GSC in U. specialize (S20 GSC48).
    constructor; rewrite ?E2; cbn [m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen m_set_avail];
      try change (get_stride (m_set_avail (m_avail mr - 2 ^ k) mr)) with (get_stride mr);
      fastfirst (first [ exact Hmem | exact Hr | exact Hk | exact MSL | exact K4 | exact NOGRP | exact N0 | exact SMOD
            | (pose proof (mf_slots_complete _ _ MF g b k Hmem ltac:(change (get_meta_rec (strip st) g) with mr; lia)) as SC;
               change (get_meta_rec (strip st) g) with mr in SC; unfold sstart_of in SC; rewrite Hmem in SC;
               cbn [default from_option id snd] in SC; unfold UNIT in SC; exact SC)
            | (intros off O0 OF;
               assert (get_stride mr * k + 16 * off < get_stride mr * (k + 1)) by lia;
               assert (get_stride mr * (k + 1) <= get_stride mr * (m_last_idx mr + 1)) by (apply Z.mul_le_mono_nonneg_l; lia);
               apply Z.div_lt_upper_bound; lia)
            | lia ]).
  - intros a Ha. exists g, b, r, k. split; [exact Hmem|]. split; [exact Hr|]. split; [exact Hk|]. split; [exact K0|]. split; [left; exact TBk|].
    unfold sstart_of. rewrite Hmem. cbn [default from_option id snd]. unfold UNIT, IB. fold mr.
    assert (get_stride mr * k + get_stride mr <= get_stride mr * m_last_idx mr + get_stride mr) by (apply Z.add_le_mono_r; apply Z.mul_le_mono_nonneg_l; lia).
    assert (0 <= get_stride mr * k) by (apply Z.mul_nonneg_nonneg; lia).
    lia.
Qed.
End FASTFACTS.

End PORT.

End WithCeil.
End TwB.
End RMalloc_fp.

(* [comment removed for export] *)
Module RAllocSlot_iface.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import TlsBase.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_enframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import Malloc_fp.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_fp.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Definition RAS_STACK (sc : Z) : Z := 288 + 144 * Z.max 0 (27 - sc).

Lemma RAS_STACK_ge sc : 288 <= RAS_STACK sc.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts. unfold RAS_STACK. lia. Qed.
Lemma RAS_STACK_le sc : 0 <= sc -> RAS_STACK sc <= 4176.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts. unfold RAS_STACK. lia. Qed.
Lemma RAS_STACK_mono a b : a <= b -> RAS_STACK b <= RAS_STACK a.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts. unfold RAS_STACK. lia. Qed.
Lemma RAS_STACK_nest sc j : sc < j -> j <= 26 -> RAS_STACK j + 144 <= RAS_STACK sc.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts. unfold RAS_STACK. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ras_post (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (o m : mem) (st0 st : mstate) (s : PState) (lo sc req : Z)
    (st1 : mstate) (idx : Z) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp)
    /\ rw_cells ssegs m' (errno_addr tp) [C4 errv'] /\ (idx = -1 -> errv' = Z_to_bv 64 ENOMEM) /\ rauxv_ok m' (bv_unsigned sp)
    /\ rmrep st1 m' /\ ticks_ok st1 /\ unk_agree st1 o m'
    /\ rpres_except (rmalloc_fp st0 st1 lo (bv_unsigned sp)) m m'
    /\ mrel st st1 /\ brk_link_ps st1 s'
    /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ as_inv st0 st st1 sc idx
    /\ 0 <= c_mmap_counter (ctx st1) < 2^32
    /\ (idx = -1
        \/ (0 <= idx /\ exists g b r, active st1 sc = Some g /\ slot_ok st1 g b r idx req
              /\ (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st1 g) * idx - 4 <= a
                           < r_base r + snd b + 16 + get_stride (get_meta_rec st1 g) * idx + get_stride (get_meta_rec st1 g) - 4 ->
                    rmalloc_fp st0 st1 lo (bv_unsigned sp) a)
              (* [comment removed for export] *)
              /\ (s_regions st0 = ∅ -> rdv pans_mem o st1 (fst b, snd b + (16 + get_stride (get_meta_rec st1 g) * idx) + -3) = 0))).

Definition ralloc_slot_stmt (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop)
                           (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop) : Prop :=
  forall (fuel : nat) (R : Type) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem)
         (s : PState) (Q : R -> PState -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st0 st : mstate) (lo sc req : Z) (errv : word),
  as_pre st0 st sc req fuel ->
  rmrep st m -> ticks_ok st -> unk_agree st o m -> brk_link_ps st s ->
  rauxv_ok m (bv_unsigned sp) ->
  stk ssegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RAS_STACK sc ->
  rw_cells ssegs m (errno_addr tp) [C4 errv] -> mem_inv ssegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 sc -> a1 = Z_to_bv 64 req ->
  (forall st1 idx s' ms',
     ras_post as_inv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
     rimplT o (k st1 idx) s' Q ms') ->
  rimplT o (alloc_slot full_lay fuel st sc req k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom ssegs)).

End PORT.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.TlsBaseU.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.SFModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_enframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.Malloc_fp.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_fp.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MSecret.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Definition RAS_STACK (sc : Z) : Z := 288 + 144 * Z.max 0 (27 - sc).

Lemma RAS_STACK_ge sc : 288 <= RAS_STACK sc.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts. unfold RAS_STACK. lia. Qed.
Lemma RAS_STACK_le sc : 0 <= sc -> RAS_STACK sc <= 4176.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts. unfold RAS_STACK. lia. Qed.
Lemma RAS_STACK_mono a b : a <= b -> RAS_STACK b <= RAS_STACK a.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts. unfold RAS_STACK. lia. Qed.
Lemma RAS_STACK_nest sc j : sc < j -> j <= 26 -> RAS_STACK j + 144 <= RAS_STACK sc.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts. unfold RAS_STACK. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ras_post (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (o m : mem) (st0 st : mstate) (s : PState) (lo sc req : Z)
    (st1 : mstate) (idx : Z) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 errv'] /\ (idx = -1 -> errv' = Z_to_bv 64 ENOMEM) /\ rauxv_ok m' (bv_unsigned sp)
    /\ rmrep st1 m' /\ ticks_ok st1 /\ unk_agree st1 o m'
    /\ rpres_except (rmalloc_fp st0 st1 lo (bv_unsigned sp)) m m'
    /\ mrel st st1 /\ brk_link_ps st1 s'
    /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ as_inv st0 st st1 sc idx
    /\ 0 <= c_mmap_counter (ctx st1) < 2^32
    /\ (idx = -1
        \/ (0 <= idx /\ exists g b r, active st1 sc = Some g /\ slot_ok st1 g b r idx req
              /\ (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st1 g) * idx - 4 <= a
                           < r_base r + snd b + 16 + get_stride (get_meta_rec st1 g) * idx + get_stride (get_meta_rec st1 g) - 4 ->
                    rmalloc_fp st0 st1 lo (bv_unsigned sp) a)
              (* [comment removed for export] *)
              /\ (s_regions st0 = ∅ -> rdv pans_mem o st1 (fst b, snd b + (16 + get_stride (get_meta_rec st1 g) * idx) + -3) = 0))).

Definition ralloc_slot_stmt (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop)
                           (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop) : Prop :=
  forall (fuel : nat) (R : Type) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem)
         (s : PState) (Q : R -> PState -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st0 st : mstate) (lo sc req : Z) (errv : word),
  as_pre st0 st sc req fuel ->
  rmrep st m -> ticks_ok st -> unk_agree st o m -> brk_link_ps st s ->
  rauxv_ok m (bv_unsigned sp) ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RAS_STACK sc ->
  rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 sc -> a1 = Z_to_bv 64 req ->
  (forall st1 idx s' ms',
     ras_post as_inv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
     rimplT o (k st1 idx) s' Q ms') ->
  rimplT o (alloc_slot full_lay fuel st sc req k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom usegs)).

End PORT.

End WithCeil.
End TwB.
End RAllocSlot_iface.

(* [comment removed for export] *)
Module RASlot_I.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import TlsBase.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocHINV. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_enframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocHINV OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Malloc_fp. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_Bpres__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.Malloc_fp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocNat OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_AS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.ASlot_W1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.ASlot_I.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_fp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RAllocSlot_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.

Notation RAREACH := (AREACH_from ref_reserved).
Notation RISTF := (ISTF_g (resv:=ref_reserved)).
Notation RAMP_AS := (AMP_AS_g ref_reserved).


(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

(* [comment removed for export] *)

Lemma rimplT_nat2 {X Y R} o (P : forall R', (X -> Y -> Malloc.M R') -> Malloc.M R' -> Malloc.M R')
      (k : X -> Y -> Malloc.M R) bail s (QS : option (X * Y) -> PState -> machine_state -> Prop) Q ms :
  steq (P R k bail) (sbind (P _ kS bS) (KF k bail)) ->
  rimplT o (P _ kS bS) s QS ms ->
  (forall x y s' ms', QS (Some (x, y)) s' ms' -> leaf_of o (P _ kS bS) (Some (x, y)) -> rimplT o (k x y) s' Q ms') ->
  (forall s' ms', QS None s' ms' -> leaf_of o (P _ kS bS) None -> rimplT o bail s' Q ms') ->
  rimplT o (P R k bail) s Q ms.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros NAT H HK HB. eapply rimplT_steq; [apply steq_sym; exact NAT|].
  eapply rimplT_bind; [eapply rimplT_reach; exact H|].
  intros [[x y]|] s' ms' [HQ HL]; cbn [KF]; eauto.
Qed.

Definition ras_pre2 (st0 st : mstate) (sc req : Z) (fuel : nat) : Prop :=
  (exists LB, RAREACH st0 LB /\ IST st0 st) /\ ENTRY_REL st0 st /\ ALLC st
  /\ 0 <= sc < 48 /\ 0 <= req < 2^32 /\ req + 4 <= 16 * size_class sc.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ras_post2
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (o m : mem) (st0 st : mstate) (s : PState) (lo sc req : Z)
    (st1 : mstate) (idx : Z) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp)
    /\ rw_cells ssegs m' (errno_addr tp) [C4 errv'] /\ (idx = -1 -> errv' = Z_to_bv 64 ENOMEM) /\ rauxv_ok m' (bv_unsigned sp)
    /\ rmrep st1 m' /\ ticks_ok st1 /\ unk_agree st1 o m'
    /\ rpres_except (rmalloc_fp st0 st1 lo (bv_unsigned sp)) m m'
    /\ mrel st st1 /\ brk_link_ps st1 s'
    /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ as_inv2 st0 st st1 sc idx
    /\ 0 <= c_mmap_counter (ctx st1) < 2^32
    /\ (idx = -1
        \/ (0 <= idx /\ exists g b r, active st1 sc = Some g /\ slot_ok st1 g b r idx req
              /\ (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st1 g) * idx - 4 <= a
                           < r_base r + snd b + 16 + get_stride (get_meta_rec st1 g) * idx + get_stride (get_meta_rec st1 g) - 4 ->
                    rmalloc_fp st0 st1 lo (bv_unsigned sp) a)
              /\ (s_regions st0 = ∅ -> rdv pans_mem o st1 (fst b, snd b + (16 + get_stride (get_meta_rec st1 g) * idx) + -3) = 0))).

Lemma ras_post2_post : ras_post2 = ras_post as_inv2.
Proof using Type. pin_using tt. ceil_facts. msec_facts. reflexivity. Qed.

Definition ralloc_slot_stmt2 (fuel : nat) : Prop :=
  forall (R : Type) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem)
         (s : PState) (Q : R -> PState -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st0 st : mstate) (lo sc req : Z) (errv : word),
  ras_pre2 st0 st sc req fuel ->
  rmrep st m -> ticks_ok st -> unk_agree st o m -> brk_link_ps st s ->
  rauxv_ok m (bv_unsigned sp) ->
  stk ssegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RAS_STACK sc ->
  rw_cells ssegs m (errno_addr tp) [C4 errv] -> mem_inv ssegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 sc -> a1 = Z_to_bv 64 req ->
  (forall st1 idx s' ms',
     ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
     rimplT o (k st1 idx) s' Q ms') ->
  rimplT o (alloc_slot full_lay fuel st sc req k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom ssegs)).

Lemma ralloc_slot_stmt2_all : (forall fuel, ralloc_slot_stmt2 fuel) -> ralloc_slot_stmt ras_pre2 as_inv2.
Proof using Type. pin_using tt. ceil_facts. msec_facts. intros H. exact H. Qed.

(* [comment removed for export] *)
Lemma ralloc_slot_stmtL (fuel : nat) : ralloc_slot_stmt2 fuel ->
  forall (R : Type) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem)
         (s : PState) (Q : R -> PState -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st0 st : mstate) (lo sc req : Z) (errv : word),
  ras_pre2 st0 st sc req fuel ->
  rmrep st m -> ticks_ok st -> unk_agree st o m -> brk_link_ps st s ->
  rauxv_ok m (bv_unsigned sp) ->
  stk ssegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RAS_STACK sc ->
  rw_cells ssegs m (errno_addr tp) [C4 errv] -> mem_inv ssegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 sc -> a1 = Z_to_bv 64 req ->
  (forall st1 idx s' ms',
     ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
     leaf_of o (alloc_slot full_lay fuel st sc req kS bS) (Some (st1, idx)) ->
     rimplT o (k st1 idx) s' Q ms') ->
  rimplT o (alloc_slot full_lay fuel st sc req k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom ssegs)).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros ASL. intros until errv. intros PRE MR TK UA BL AUX ST CLO LO ER MI TP A0 A1 K.
  eapply (rimplT_nat2 o (fun R' k' b' => @alloc_slot _ R' full_lay fuel st sc req k' b') k bail s
            (fun r s' ms' => match r with
                             | Some (st1, idx) => ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms'
                             | None => False end)).
  - apply alloc_slot_nat.
  - eapply ASL; try eassumption. intros st1 idx s' ms' HP. apply rimplT_ret. apply evt_done. exact HP.
  - intros x y s' ms' HP HL. exact (K x y s' ms' HP HL).
  - intros s' ms' [].
Qed.

(* [comment removed for export] *)
Lemma ralloc_meta_stmtL (am_pre : mstate -> Prop) : ralloc_meta_stmt am_pre ->
  forall (R : Type) (k : mstate -> optr -> Malloc.M R) (bail : Malloc.M R) (o : mem)
         (s : PState) (Q : R -> PState -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : mstate) (lo : Z) (errv : word),
  am_pre st -> rmrep st m -> ticks_ok st -> brk_link_ps st s ->
  rauxv_ok m (bv_unsigned sp) ->
  stk ssegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RAM_STACK ->
  rw_cells ssegs m (errno_addr tp) [C4 errv] -> mem_inv ssegs m ->
  tp = Z_to_bv 64 RATP ->
  (forall st1 mo s' ms',
     ram_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s lo m st1 mo s' ms' ->
     brk_link_ps st1 s' ->
     leaf_of o (alloc_meta st kS bS) (Some (st1, mo)) ->
     rimplT o (k st1 mo) s' Q ms') ->
  rimplT o (alloc_meta st k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ralloc_meta_entry) fc None m (seg_rom ssegs)).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros AM. intros until errv. intros PRE MR TK BL AUX ST CLO LO ER MI TP K.
  eapply (rimplT_nat2 o (fun R' k' b' => @alloc_meta _ R' st k' b') k bail s
            (fun r s' ms' => match r with
                             | Some (st1, mo) => ram_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s lo m st1 mo s' ms' /\ brk_link_ps st1 s'
                             | None => False end)).
  - apply alloc_meta_nat.
  - eapply AM; try eassumption. intros st1 mo s' ms' HP HB. apply rimplT_ret. apply evt_done. split; assumption.
  - intros x y s' ms' [HP HB] HL. exact (K x y s' ms' HP HB HL).
  - intros s' ms' [].
Qed.

End PORT.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.TlsBaseU.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.SFModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_enframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocHINV OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.Malloc_fp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocNat OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_AS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.ASlot_W1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.ASlot_I.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_fp.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RAllocSlot_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MSecret.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.

Notation RAREACH := (AREACH_from ref_reserved).
Notation RISTF := (ISTF_g (resv:=ref_reserved)).
Notation RAMP_AS := (AMP_AS_g ref_reserved).


(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

(* [comment removed for export] *)

Lemma rimplT_nat2 {X Y R} o (P : forall R', (X -> Y -> Malloc.M R') -> Malloc.M R' -> Malloc.M R')
      (k : X -> Y -> Malloc.M R) bail s (QS : option (X * Y) -> PState -> machine_state -> Prop) Q ms :
  steq (P R k bail) (sbind (P _ kS bS) (KF k bail)) ->
  rimplT o (P _ kS bS) s QS ms ->
  (forall x y s' ms', QS (Some (x, y)) s' ms' -> leaf_of o (P _ kS bS) (Some (x, y)) -> rimplT o (k x y) s' Q ms') ->
  (forall s' ms', QS None s' ms' -> leaf_of o (P _ kS bS) None -> rimplT o bail s' Q ms') ->
  rimplT o (P R k bail) s Q ms.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros NAT H HK HB. eapply rimplT_steq; [apply steq_sym; exact NAT|].
  eapply rimplT_bind; [eapply rimplT_reach; exact H|].
  intros [[x y]|] s' ms' [HQ HL]; cbn [KF]; eauto.
Qed.

Definition ras_pre2 (st0 st : mstate) (sc req : Z) (fuel : nat) : Prop :=
  (exists LB, RAREACH st0 LB /\ IST st0 st) /\ ENTRY_REL st0 st /\ ALLC st
  /\ 0 <= sc < 48 /\ 0 <= req < 2^32 /\ req + 4 <= 16 * size_class sc.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ras_post2
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (o m : mem) (st0 st : mstate) (s : PState) (lo sc req : Z)
    (st1 : mstate) (idx : Z) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 errv'] /\ (idx = -1 -> errv' = Z_to_bv 64 ENOMEM) /\ rauxv_ok m' (bv_unsigned sp)
    /\ rmrep st1 m' /\ ticks_ok st1 /\ unk_agree st1 o m'
    /\ rpres_except (rmalloc_fp st0 st1 lo (bv_unsigned sp)) m m'
    /\ mrel st st1 /\ brk_link_ps st1 s'
    /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ as_inv2 st0 st st1 sc idx
    /\ 0 <= c_mmap_counter (ctx st1) < 2^32
    /\ (idx = -1
        \/ (0 <= idx /\ exists g b r, active st1 sc = Some g /\ slot_ok st1 g b r idx req
              /\ (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st1 g) * idx - 4 <= a
                           < r_base r + snd b + 16 + get_stride (get_meta_rec st1 g) * idx + get_stride (get_meta_rec st1 g) - 4 ->
                    rmalloc_fp st0 st1 lo (bv_unsigned sp) a)
              /\ (s_regions st0 = ∅ -> rdv pans_mem o st1 (fst b, snd b + (16 + get_stride (get_meta_rec st1 g) * idx) + -3) = 0))).

Lemma ras_post2_post : ras_post2 = ras_post as_inv2.
Proof using Type. pin_using tt. ceil_facts. msec_facts. reflexivity. Qed.

Definition ralloc_slot_stmt2 (fuel : nat) : Prop :=
  forall (R : Type) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem)
         (s : PState) (Q : R -> PState -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st0 st : mstate) (lo sc req : Z) (errv : word),
  ras_pre2 st0 st sc req fuel ->
  rmrep st m -> ticks_ok st -> unk_agree st o m -> brk_link_ps st s ->
  rauxv_ok m (bv_unsigned sp) ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RAS_STACK sc ->
  rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 sc -> a1 = Z_to_bv 64 req ->
  (forall st1 idx s' ms',
     ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
     rimplT o (k st1 idx) s' Q ms') ->
  rimplT o (alloc_slot full_lay fuel st sc req k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom usegs)).

Lemma ralloc_slot_stmt2_all : (forall fuel, ralloc_slot_stmt2 fuel) -> ralloc_slot_stmt ras_pre2 as_inv2.
Proof using Type. pin_using tt. ceil_facts. msec_facts. intros H. exact H. Qed.

(* [comment removed for export] *)
Lemma ralloc_slot_stmtL (fuel : nat) : ralloc_slot_stmt2 fuel ->
  forall (R : Type) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem)
         (s : PState) (Q : R -> PState -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st0 st : mstate) (lo sc req : Z) (errv : word),
  ras_pre2 st0 st sc req fuel ->
  rmrep st m -> ticks_ok st -> unk_agree st o m -> brk_link_ps st s ->
  rauxv_ok m (bv_unsigned sp) ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RAS_STACK sc ->
  rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 sc -> a1 = Z_to_bv 64 req ->
  (forall st1 idx s' ms',
     ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
     leaf_of o (alloc_slot full_lay fuel st sc req kS bS) (Some (st1, idx)) ->
     rimplT o (k st1 idx) s' Q ms') ->
  rimplT o (alloc_slot full_lay fuel st sc req k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom usegs)).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros ASL. intros until errv. intros PRE MR TK UA BL AUX ST CLO LO ER MI TP A0 A1 K.
  eapply (rimplT_nat2 o (fun R' k' b' => @alloc_slot _ R' full_lay fuel st sc req k' b') k bail s
            (fun r s' ms' => match r with
                             | Some (st1, idx) => ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms'
                             | None => False end)).
  - apply alloc_slot_nat.
  - eapply ASL; try eassumption. intros st1 idx s' ms' HP. apply rimplT_ret. apply evt_done. exact HP.
  - intros x y s' ms' HP HL. exact (K x y s' ms' HP HL).
  - intros s' ms' [].
Qed.

(* [comment removed for export] *)
Lemma ralloc_meta_stmtL (am_pre : mstate -> Prop) : ralloc_meta_stmt am_pre ->
  forall (R : Type) (k : mstate -> optr -> Malloc.M R) (bail : Malloc.M R) (o : mem)
         (s : PState) (Q : R -> PState -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : mstate) (lo : Z) (errv : word),
  am_pre st -> rmrep st m -> ticks_ok st -> brk_link_ps st s ->
  rauxv_ok m (bv_unsigned sp) ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RAM_STACK ->
  rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m ->
  tp = Z_to_bv 64 RATP ->
  (forall st1 mo s' ms',
     ram_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s lo m st1 mo s' ms' ->
     brk_link_ps st1 s' ->
     leaf_of o (alloc_meta st kS bS) (Some (st1, mo)) ->
     rimplT o (k st1 mo) s' Q ms') ->
  rimplT o (alloc_meta st k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ralloc_meta_entry) fc None m (seg_rom usegs)).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros AM. intros until errv. intros PRE MR TK BL AUX ST CLO LO ER MI TP K.
  eapply (rimplT_nat2 o (fun R' k' b' => @alloc_meta _ R' st k' b') k bail s
            (fun r s' ms' => match r with
                             | Some (st1, mo) => ram_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s lo m st1 mo s' ms' /\ brk_link_ps st1 s'
                             | None => False end)).
  - apply alloc_meta_nat.
  - eapply AM; try eassumption. intros st1 mo s' ms' HP HB. apply rimplT_ret. apply evt_done. split; assumption.
  - intros x y s' ms' [HP HB] HL. exact (K x y s' ms' HP HB HL).
  - intros s' ms' [].
Qed.

End PORT.

End WithCeil.
End TwB.
End RASlot_I.

(* [comment removed for export] *)
Module RF_malloc_enf.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import TlsBase.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_enframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Malloc_fp. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocKit_A2__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.Malloc_fp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_enf.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_get_meta__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_enframe RMallocKit_A. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_get_meta OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMallocKit_B2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_enframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocKit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_fp.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Local Unset Keyed Unification.

(* [comment removed for export] *)
Lemma renf_glue_walk : forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw gw iw rav s0v s1v s2v s3v s4v : word)
    F fc (m : mem) (st : mstate),
  rw_cells ssegs m RCTX (ctx_head_cells st) ->
  rw_cells ssegs m RMLOCK [C4 (wz 0)] ->
  rw_cells ssegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  48 <= bv_unsigned sp ->
  0 <= c_mmap_counter (ctx st) < 2^32 ->
  evt ssegs (fun ms' => ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v gw iw nw (wz (sxv (c_mmap_counter (ctx st)))) a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 renframe_entry) fc None m (seg_rom ssegs))
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK) a0 a1 a2 a3 a4 a5 a6 a7 gw iw s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19580) fc None m (seg_rom ssegs)).
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros until st. intros CH LK FR SP48 CTR.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold RCTX, RMLOCK in *. unfold ctx_head_cells in CH.
  (* [comment removed for export] *)
  step. rewrite sx32_wz_sxv by lia.
  (* [comment removed for export] *)
  step. step.
  eapply evt_cut.
  { eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
  intros ms' ->.
  replace (ret_pc (Z_to_bv 64 0x1958c)) with (Z_to_bv 64 0x1958c) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* [comment removed for export] *)
  do 12 step.
  apply evt_done. unfold renframe_entry. reflexivity.
Qed.

(* [comment removed for export] *)
Definition renf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (o m0 : mem) (C : Z -> Prop) (st1 : mstate) (g b : aptr) (idx n : Z)
    (r : mstate * optr) (ms' : machine_state) : Prop :=
  exists st' p t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    r = (st', Some p)
    /\ ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (conc st' p)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp)
    /\ rmrep st' m' /\ ticks_ok st' /\ rpres_except C m0 m'
    /\ enf_leaf o st1 g b idx n st' p.

(* [comment removed for export] *)
Lemma renf_implT :
  forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' ra s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32)
         (o m0 m1 : mem) (s : PState) (st1 : mstate) (g b : aptr) (r : region) (idx n lo : Z) (C : Z -> Prop),
  let mr := get_meta_rec st1 g in
  let stride := get_stride mr in
  let ctr := c_mmap_counter (ctx st1) in
  rmrep st1 m1 -> ticks_ok st1 -> unk_agree st1 o m1 ->
  mem_inv ssegs m1 -> stk ssegs m1 lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
  rw_cells ssegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
  rpres_except C m0 m1 -> (forall a, lo <= a < bv_unsigned sp -> C a) ->
  (forall a, r_base r + snd b + 16 + stride * idx - 4 <= a < r_base r + snd b + 16 + stride * idx + stride - 4 -> C a) ->
  0 <= ctr < 2^32 ->
  slot_ok st1 g b r idx n ->
  rimplT o (enframe_full st1 g idx n ctr (fun st2 p => ret (havoc p n st2, Some p))) s
        (fun res s' ms' => s' = s /\ renf_post ra sp gp tp s0v s1v s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 F fc lo o m0 C st1 g b idx n res ms')
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
                 a0 a1 a2 a3 a4 a5 a6 a7 (pw st1 (Some g)) (wz idx) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x19580) fc None m1 (seg_rom ssegs)).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros until C. intros mr stride ctr MR TK UA MI ST CLO LO FR PE CST CSL CTR SO.
  destruct SO as [Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD S31 N0 NS NOGRP HDR0 Q16 SSL MSL AVr FRr FBr MPL SCr].
  fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, S31, NS, NOGRP, HDR0, Q16, AVr, FRr, FBr, MPL, SCr.
  fold stride in SPAN, S16, SMOD, S31, NS, NOGRP, HDR0, Q16.
  assert (SPAN1 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)).
  { eapply Z.le_trans; [|exact SPAN]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
  clear SPAN. rename SPAN1 into SPAN.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  ceil_facts.
  (* [comment removed for export] *)
  destruct (rslot_facts st1 m1 o g b r idx MR UA Hr Hk B0 ltac:(lia) SPAN S16 B16 SMOD HDR0)
    as (x3 & x2 & x1 & WRs & Y & E3 & E2 & E1 & CB & R4 & PEND & RC & RI1).
  fold mr in WRs, Y, E3, E2, E1, PEND. fold stride in WRs, Y, E3, E2, E1, PEND.
  pose proof (rmeta_chunk_facts st1 m1 g MR MSL) as (MM & G0 & GC & GI1 & GI2 & GDJ & GRG).
  ceil_facts.
  set (G := conc st1 g) in *.
  pose proof (GDJ (fst b) r Hr Hk) as GR.
  change (get_meta_rec st1 g) with mr in MM. unfold meta_cells in MM. rewrite Hmem in MM.
  unfold pw at 3 in MM. cbn [oconc] in MM. unfold meta_word in MM.
  set (B := conc st1 b) in *.
  pose proof (byte_range x3) as X3. pose proof (byte_range x2) as X2. pose proof (byte_range x1) as X1.
  assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
  rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN.
  (* [comment removed for export] *)
  pose proof (bytes_at_read ssegs m1 _ _ 0 1 Y ltac:(lia) ltac:(cbn; lia)) as RD4. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD4.
  pose proof (bytes_at_read ssegs m1 _ _ 1 1 Y ltac:(lia) ltac:(cbn; lia)) as RD3. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD3.
  pose proof (bytes_at_read ssegs m1 _ _ 2 2 Y ltac:(lia) ltac:(cbn; lia)) as RD2. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD2.
  rewrite Z.add_0_r in RD4.
  replace (B + 16 + stride * idx - 4 + 1) with (B + 16 + stride * idx - 3) in RD3 by lia.
  replace (B + 16 + stride * idx - 4 + 2) with (B + 16 + stride * idx - 2) in RD2 by lia.
  rewrite <- (le2_lohi (bv_unsigned x2) (bv_unsigned x1)) in RD2 by lia.
  (* [comment removed for export] *)
  unfold enframe_full, enframe_read_off. change (get_meta_rec st1 g) with mr. fold stride. cbv zeta.
  assert (Hp0 : slot_start' mr idx = (fst b, snd b + (16 + stride * idx))).
  { unfold slot_start'. rewrite Hmem. cbn [default from_option id]. unfold aadd, UNIT. cbn [fst snd]. fold stride. reflexivity. }
  rewrite Hp0. unfold aadd. cbn [fst snd].
  (* [comment removed for export] *)
  assert (PA3 : peek_agrees o st1 (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
                 a0 a1 a2 a3 a4 a5 a6 a7 (pw st1 (Some g)) (wz idx) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x19580) fc None m1 (seg_rom ssegs))
                 (fst b, snd b + (16 + stride * idx) + -3)).
  { eapply (peek_agrees_of_bytes_at_b8 o st1 m1 _ _ _ 1%nat (bv_unsigned x3)); [exact Y| reflexivity| apply byte_range| | exact E3].
    rewrite (conc_region' st1 (fst b, _) r Hr). cbn [snd]. lia. }
  assert (PA2 : peek_agrees o st1 (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
                 a0 a1 a2 a3 a4 a5 a6 a7 (pw st1 (Some g)) (wz idx) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x19580) fc None m1 (seg_rom ssegs))
                 (fst b, snd b + (16 + stride * idx) + -2)).
  { eapply (peek_agrees_of_bytes_at_b8 o st1 m1 _ _ _ 2%nat (bv_unsigned x2)); [exact Y| reflexivity| apply byte_range| | exact E2].
    rewrite (conc_region' st1 (fst b, _) r Hr). cbn [snd]. lia. }
  assert (PA1 : peek_agrees o st1 (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
                 a0 a1 a2 a3 a4 a5 a6 a7 (pw st1 (Some g)) (wz idx) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x19580) fc None m1 (seg_rom ssegs))
                 (fst b, snd b + (16 + stride * idx) + -2 + 1)).
  { eapply (peek_agrees_of_bytes_at_b8 o st1 m1 _ _ _ 3%nat (bv_unsigned x1)); [exact Y| reflexivity| apply byte_range| | exact E1].
    rewrite (conc_region' st1 (fst b, _) r Hr). cbn [snd]. lia. }
  apply rimplT_rd8; [exact PA3|]. rewrite E3.
  change ((stride - IB - n) / UNIT) with ((stride - 4 - n) / 16). set (slack := (stride - 4 - n) / 16).
  set (K := fun off : Z => let '(st2, p) := enframe_at st1 g idx n off in @ret (mstate * optr) (havoc p n st2, Some p)).
  set (off0 := if bv_unsigned x3 =? 0 then Z.land ctr 255 else Z.land (bv_unsigned x2 + 256 * bv_unsigned x1 + 1) 255).
  set (off := fold_off off0 slack).
  assert (OFF0 : 0 <= off0 < 256).
  { subst off0. destruct (bv_unsigned x3 =? 0).
    - split; [apply Z.land_nonneg; lia|]. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
    - split; [apply Z.land_nonneg; lia|]. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (SL0 : 0 <= slack) by (subst slack; apply Z.div_pos; lia).
  pose proof (fold_off_le_slack off0 slack OFF0 SL0) as OFF. fold off in OFF.
  assert (FIT : 16 * off + n + 4 <= stride) by (subst slack; Z.div_mod_to_equations; lia).
  match goal with |- rimplT _ _ _ ?Q ?ms => 
  assert (GOAL : rimplT o (K off) s Q ms) end.
  2:{ assert (OFFa : bv_unsigned x3 = 0 -> fold_off (Z.land ctr 255) slack = off).
      { intros E0. unfold off, off0. rewrite (proj2 (Z.eqb_eq _ _) E0). reflexivity. }
      assert (OFFb : bv_unsigned x3 <> 0 -> fold_off (Z.land (bv_unsigned x2 + 256 * bv_unsigned x1 + 1) 255) slack = off).
      { intros E0. unfold off, off0. rewrite (proj2 (Z.eqb_neq _ _) E0). reflexivity. }
      clearbody off.
      destruct (Z.eqb_spec (bv_unsigned x3) 0) as [E0|NE0]; cbn [negb].
      - rewrite (OFFa E0). exact GOAL.
      - apply rimplT_rd16; [exact PA2| unfold aadd; cbn [fst snd]; exact PA1|]. unfold aadd; cbn [fst snd]. rewrite E2, E1. rewrite (OFFb NE0). exact GOAL. }
  subst K. cbv beta. rewrite surj_pair_let. apply rimplT_ret.
  (* [comment removed for export] *)
  pose proof MR as (WF' & CX & GL & _). destruct GL as (LK & _). destruct CX as (CH & _).
  eapply evt_cut.
  { eapply (renf_glue_walk sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' (Z_to_bv 64 n) (pw st1 (Some g)) (wz idx) ra s0v s1v s2v s3v s4v F fc m1 st1);
      [exact CH| exact LK| exact FR| lia| exact CTR]. }
  intros ms' ->.
  unfold renframe_entry.
  eapply evt_mono.
  { eapply (renframe_walk ra sp gp tp t0 t1 t2 s0v s1v a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (pw st1 (Some g)) (Z_to_bv 64 n)
              (pw st1 (m_prev mr)) (pw st1 (m_next mr)) F fc m1 B stride n idx ctr (m_avail mr) (m_freed mr)
              (m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) (bv_unsigned x3) (bv_unsigned x2 + 256 * bv_unsigned x1)).
    all: lazymatch goal with
         | |- rw_cells _ _ (bv_unsigned (pw _ _)) _ => unfold pw; cbn [oconc]; fold G; rewrite (wz_unsigned G) by lia; exact MM
         | |- mem_inv _ _ => exact MI
         | |- wr_at _ _ _ _ => exact WRs
         | |- ov_read_bytes _ _ _ 2 = _ => exact RD2
         | |- ov_read_bytes _ _ _ _ = Some [b8 0] => exact RD4
         | |- ov_read_bytes _ _ _ _ = _ => exact RD3
         | |- bv_unsigned (Z_to_bv 64 _) = _ => apply unsigned_lit; lia
         | |- _ => idtac end.
    all: try (unfold pw; cbn [oconc]; fold G; rewrite (wz_unsigned G) by lia).
    all: try lia.
    - subst stride. unfold get_stride, UNIT. reflexivity.
    - intros off' O1 O2. pose proof (Q16 off' O1 O2). lia. }
  (* [comment removed for export] *)
  intros ms' PO. cbv beta in PO. unfold ren3_post in PO.
  destruct PO as (w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & m' & -> & EM & MI').
  split; [reflexivity|].
  fold slack in EM. fold off0 in EM. fold off in EM. fold slack off0 off.
  set (res := enframe_at st1 g idx n off) in *.
  (* [comment removed for export] *)
  assert (S31n : stride - 4 - n < 2^31) by lia.
  destruct (renframe_mrep st1 m1 g b r idx n off MR TK Hmem Hr Hk B0 ltac:(clear -IDX LI32; lia) ltac:(unfold stride, mr in SPAN; clear -SPAN S16; lia) S16 S31n NOGRP (proj1 OFF) N0 FIT (Q16 off (proj1 OFF) FIT))
    as (MRr & TKr & CONCr & FSTr & SNDr).
  fold stride B res in MRr, TKr, CONCr, FSTr, SNDr.
  change (conc st1 b) with B in MRr, CONCr. change (get_stride (get_meta_rec st1 g)) with stride in MRr, CONCr, SNDr.
  fold res in MRr, TKr, CONCr, FSTr, SNDr.
  set (P0 := B + 16 + stride * idx) in *.
  rewrite <- EM in MRr.
  destruct (rmrep_havoc (fst res) m' (snd res) n MRr TKr) as [MR' TK'].
  (* [comment removed for export] *)
  assert (PE0 : rpres_except (fun a => P0 - 4 <= a < P0 + stride - 4) m1 m').
  { rewrite EM. apply (rpres_enframe _ m1 m1 P0 stride off n idx B (rpres_except_refl _ _) (proj1 OFF) N0 FIT); [unfold P0; lia| unfold P0; lia|].
    intros x Hx. exact Hx. }
  assert (ST' : stk ssegs m' lo (bv_unsigned sp + -48)).
  { eapply rpres_except_stk; [exact PE0| exact ST|]. intros a Ha. cbv beta. unfold P0. lia. }
  assert (FR' : rw_cells ssegs m' (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra]).
  { eapply rpres_except_rw_cells; [exact PE0| exact FR|]. cbn [cells_size csize Nat.add Z.of_nat]. intros a Ha. cbv beta. unfold P0. lia. }
  release_frame FR' ST' (bv_unsigned sp).
  unfold renf_post. exists (havoc (snd res) n (fst res)), (snd res). do 14 eexists. exists m'.
  split; [reflexivity|].
  split. { unfold wz. rewrite conc_havoc. rewrite <- CONCr. unfold res. rewrite conc_enframe_at. reflexivity. }
  split; [exact MI'|]. split; [exact ST'|]. split; [exact MR'|]. split; [exact TK'|].
  split.
  { rewrite EM. apply (rpres_enframe C m0 m1 _ stride off n idx B PE (proj1 OFF) N0 FIT); [unfold B; lia| unfold B; lia|].
    intros x Hx. apply CSL. unfold B in Hx. lia. }
  exists off. split; [exact (proj1 OFF)|]. split; [exact FIT|].
  split. { clear - FSTr SNDr. destruct (snd res) as [p1 p2]. cbn [fst snd] in FSTr, SNDr. subst. reflexivity. }
  split; [reflexivity|]. split; [reflexivity|].
  unfold off, off0, slack, enf_off0. fold mr. fold stride. rewrite E3, E2, E1. reflexivity.
Qed.

End PORT.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.TlsBaseU.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.SFModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_enframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.Malloc_fp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_enf.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_get_meta.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMallocKit_B2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_enframe.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocKit_A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_fp.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MSecret.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Local Unset Keyed Unification.

(* [comment removed for export] *)
Lemma renf_glue_walk : forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw gw iw rav s0v s1v s2v s3v s4v : word)
    F fc (m : mem) (st : mstate),
  rw_cells usegs m RCTX (ctx_head_cells st) ->
  rw_cells usegs m RMLOCK [C4 (wz 0)] ->
  rw_cells usegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  48 <= bv_unsigned sp ->
  0 <= c_mmap_counter (ctx st) < 2^32 ->
  evt usegs (fun ms' => ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v gw iw nw (wz (sxv (c_mmap_counter (ctx st)))) a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 renframe_entry) fc None m (seg_rom usegs))
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK) a0 a1 a2 a3 a4 a5 a6 a7 gw iw s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19d40) fc None m (seg_rom usegs)).
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros until st. intros CH LK FR SP48 CTR.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold RCTX, RMLOCK in *. unfold ctx_head_cells in CH.
  (* [comment removed for export] *)
  step. rewrite sx32_wz_sxv by lia.
  (* [comment removed for export] *)
  step. step.
  eapply evt_cut.
  { eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
  intros ms' ->.
  replace (ret_pc (Z_to_bv 64 0x19d4c)) with (Z_to_bv 64 0x19d4c) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* [comment removed for export] *)
  do 12 step.
  apply evt_done. unfold renframe_entry. reflexivity.
Qed.

(* [comment removed for export] *)
Definition renf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (o m0 : mem) (C : Z -> Prop) (st1 : mstate) (g b : aptr) (idx n : Z)
    (r : mstate * optr) (ms' : machine_state) : Prop :=
  exists st' p t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    r = (st', Some p)
    /\ ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (conc st' p)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rmrep st' m' /\ ticks_ok st' /\ rpres_except C m0 m'
    /\ enf_leaf o st1 g b idx n st' p.

(* [comment removed for export] *)
Lemma renf_implT :
  forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' ra s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32)
         (o m0 m1 : mem) (s : PState) (st1 : mstate) (g b : aptr) (r : region) (idx n lo : Z) (C : Z -> Prop),
  let mr := get_meta_rec st1 g in
  let stride := get_stride mr in
  let ctr := c_mmap_counter (ctx st1) in
  rmrep st1 m1 -> ticks_ok st1 -> unk_agree st1 o m1 ->
  mem_inv usegs m1 -> stk usegs m1 lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
  rw_cells usegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
  rpres_except C m0 m1 -> (forall a, lo <= a < bv_unsigned sp -> C a) ->
  (forall a, r_base r + snd b + 16 + stride * idx - 4 <= a < r_base r + snd b + 16 + stride * idx + stride - 4 -> C a) ->
  0 <= ctr < 2^32 ->
  slot_ok st1 g b r idx n ->
  rimplT o (enframe_full st1 g idx n ctr (fun st2 p => ret (havoc p n st2, Some p))) s
        (fun res s' ms' => s' = s /\ renf_post ra sp gp tp s0v s1v s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 F fc lo o m0 C st1 g b idx n res ms')
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
                 a0 a1 a2 a3 a4 a5 a6 a7 (pw st1 (Some g)) (wz idx) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x19d40) fc None m1 (seg_rom usegs)).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros until C. intros mr stride ctr MR TK UA MI ST CLO LO FR PE CST CSL CTR SO.
  destruct SO as [Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD S31 N0 NS NOGRP HDR0 Q16 SSL MSL AVr FRr FBr MPL SCr].
  fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, S31, NS, NOGRP, HDR0, Q16, AVr, FRr, FBr, MPL, SCr.
  fold stride in SPAN, S16, SMOD, S31, NS, NOGRP, HDR0, Q16.
  assert (SPAN1 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)).
  { eapply Z.le_trans; [|exact SPAN]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
  clear SPAN. rename SPAN1 into SPAN.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  ceil_facts.
  (* [comment removed for export] *)
  destruct (rslot_facts st1 m1 o g b r idx MR UA Hr Hk B0 ltac:(lia) SPAN S16 B16 SMOD HDR0)
    as (x3 & x2 & x1 & WRs & Y & E3 & E2 & E1 & CB & R4 & PEND & RC & RI1).
  fold mr in WRs, Y, E3, E2, E1, PEND. fold stride in WRs, Y, E3, E2, E1, PEND.
  pose proof (rmeta_chunk_facts st1 m1 g MR MSL) as (MM & G0 & GC & GI1 & GI2 & GDJ & GRG).
  ceil_facts.
  set (G := conc st1 g) in *.
  pose proof (GDJ (fst b) r Hr Hk) as GR.
  change (get_meta_rec st1 g) with mr in MM. unfold meta_cells in MM. rewrite Hmem in MM.
  unfold pw at 3 in MM. cbn [oconc] in MM. unfold meta_word in MM.
  set (B := conc st1 b) in *.
  pose proof (byte_range x3) as X3. pose proof (byte_range x2) as X2. pose proof (byte_range x1) as X1.
  assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
  rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN.
  (* [comment removed for export] *)
  pose proof (bytes_at_read usegs m1 _ _ 0 1 Y ltac:(lia) ltac:(cbn; lia)) as RD4. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD4.
  pose proof (bytes_at_read usegs m1 _ _ 1 1 Y ltac:(lia) ltac:(cbn; lia)) as RD3. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD3.
  pose proof (bytes_at_read usegs m1 _ _ 2 2 Y ltac:(lia) ltac:(cbn; lia)) as RD2. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD2.
  rewrite Z.add_0_r in RD4.
  replace (B + 16 + stride * idx - 4 + 1) with (B + 16 + stride * idx - 3) in RD3 by lia.
  replace (B + 16 + stride * idx - 4 + 2) with (B + 16 + stride * idx - 2) in RD2 by lia.
  rewrite <- (le2_lohi (bv_unsigned x2) (bv_unsigned x1)) in RD2 by lia.
  (* [comment removed for export] *)
  unfold enframe_full, enframe_read_off. change (get_meta_rec st1 g) with mr. fold stride. cbv zeta.
  assert (Hp0 : slot_start' mr idx = (fst b, snd b + (16 + stride * idx))).
  { unfold slot_start'. rewrite Hmem. cbn [default from_option id]. unfold aadd, UNIT. cbn [fst snd]. fold stride. reflexivity. }
  rewrite Hp0. unfold aadd. cbn [fst snd].
  (* [comment removed for export] *)
  assert (PA3 : peek_agrees o st1 (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
                 a0 a1 a2 a3 a4 a5 a6 a7 (pw st1 (Some g)) (wz idx) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x19d40) fc None m1 (seg_rom usegs))
                 (fst b, snd b + (16 + stride * idx) + -3)).
  { eapply (peek_agrees_of_bytes_at_b8 o st1 m1 _ _ _ 1%nat (bv_unsigned x3)); [exact Y| reflexivity| apply byte_range| | exact E3].
    rewrite (conc_region' st1 (fst b, _) r Hr). cbn [snd]. lia. }
  assert (PA2 : peek_agrees o st1 (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
                 a0 a1 a2 a3 a4 a5 a6 a7 (pw st1 (Some g)) (wz idx) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x19d40) fc None m1 (seg_rom usegs))
                 (fst b, snd b + (16 + stride * idx) + -2)).
  { eapply (peek_agrees_of_bytes_at_b8 o st1 m1 _ _ _ 2%nat (bv_unsigned x2)); [exact Y| reflexivity| apply byte_range| | exact E2].
    rewrite (conc_region' st1 (fst b, _) r Hr). cbn [snd]. lia. }
  assert (PA1 : peek_agrees o st1 (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
                 a0 a1 a2 a3 a4 a5 a6 a7 (pw st1 (Some g)) (wz idx) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x19d40) fc None m1 (seg_rom usegs))
                 (fst b, snd b + (16 + stride * idx) + -2 + 1)).
  { eapply (peek_agrees_of_bytes_at_b8 o st1 m1 _ _ _ 3%nat (bv_unsigned x1)); [exact Y| reflexivity| apply byte_range| | exact E1].
    rewrite (conc_region' st1 (fst b, _) r Hr). cbn [snd]. lia. }
  apply rimplT_rd8; [exact PA3|]. rewrite E3.
  change ((stride - IB - n) / UNIT) with ((stride - 4 - n) / 16). set (slack := (stride - 4 - n) / 16).
  set (K := fun off : Z => let '(st2, p) := enframe_at st1 g idx n off in @ret (mstate * optr) (havoc p n st2, Some p)).
  set (off0 := if bv_unsigned x3 =? 0 then Z.land ctr 255 else Z.land (bv_unsigned x2 + 256 * bv_unsigned x1 + 1) 255).
  set (off := fold_off off0 slack).
  assert (OFF0 : 0 <= off0 < 256).
  { subst off0. destruct (bv_unsigned x3 =? 0).
    - split; [apply Z.land_nonneg; lia|]. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
    - split; [apply Z.land_nonneg; lia|]. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (SL0 : 0 <= slack) by (subst slack; apply Z.div_pos; lia).
  pose proof (fold_off_le_slack off0 slack OFF0 SL0) as OFF. fold off in OFF.
  assert (FIT : 16 * off + n + 4 <= stride) by (subst slack; Z.div_mod_to_equations; lia).
  match goal with |- rimplT _ _ _ ?Q ?ms => 
  assert (GOAL : rimplT o (K off) s Q ms) end.
  2:{ assert (OFFa : bv_unsigned x3 = 0 -> fold_off (Z.land ctr 255) slack = off).
      { intros E0. unfold off, off0. rewrite (proj2 (Z.eqb_eq _ _) E0). reflexivity. }
      assert (OFFb : bv_unsigned x3 <> 0 -> fold_off (Z.land (bv_unsigned x2 + 256 * bv_unsigned x1 + 1) 255) slack = off).
      { intros E0. unfold off, off0. rewrite (proj2 (Z.eqb_neq _ _) E0). reflexivity. }
      clearbody off.
      destruct (Z.eqb_spec (bv_unsigned x3) 0) as [E0|NE0]; cbn [negb].
      - rewrite (OFFa E0). exact GOAL.
      - apply rimplT_rd16; [exact PA2| unfold aadd; cbn [fst snd]; exact PA1|]. unfold aadd; cbn [fst snd]. rewrite E2, E1. rewrite (OFFb NE0). exact GOAL. }
  subst K. cbv beta. rewrite surj_pair_let. apply rimplT_ret.
  (* [comment removed for export] *)
  pose proof MR as (WF' & CX & GL & _). destruct GL as (LK & _). destruct CX as (CH & _).
  eapply evt_cut.
  { eapply (renf_glue_walk sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' (Z_to_bv 64 n) (pw st1 (Some g)) (wz idx) ra s0v s1v s2v s3v s4v F fc m1 st1);
      [exact CH| exact LK| exact FR| lia| exact CTR]. }
  intros ms' ->.
  unfold renframe_entry.
  eapply evt_mono.
  { eapply (renframe_walk ra sp gp tp t0 t1 t2 s0v s1v a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (pw st1 (Some g)) (Z_to_bv 64 n)
              (pw st1 (m_prev mr)) (pw st1 (m_next mr)) F fc m1 B stride n idx ctr (m_avail mr) (m_freed mr)
              (m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) (bv_unsigned x3) (bv_unsigned x2 + 256 * bv_unsigned x1)).
    all: lazymatch goal with
         | |- rw_cells _ _ (bv_unsigned (pw _ _)) _ => unfold pw; cbn [oconc]; fold G; rewrite (wz_unsigned G) by lia; exact MM
         | |- mem_inv _ _ => exact MI
         | |- wr_at _ _ _ _ => exact WRs
         | |- ov_read_bytes _ _ _ 2 = _ => exact RD2
         | |- ov_read_bytes _ _ _ _ = Some [b8 0] => exact RD4
         | |- ov_read_bytes _ _ _ _ = _ => exact RD3
         | |- bv_unsigned (Z_to_bv 64 _) = _ => apply unsigned_lit; lia
         | |- _ => idtac end.
    all: try (unfold pw; cbn [oconc]; fold G; rewrite (wz_unsigned G) by lia).
    all: try lia.
    - subst stride. unfold get_stride, UNIT. reflexivity.
    - intros off' O1 O2. pose proof (Q16 off' O1 O2). lia. }
  (* [comment removed for export] *)
  intros ms' PO. cbv beta in PO. unfold ren3_post in PO.
  destruct PO as (w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & m' & -> & EM & MI').
  split; [reflexivity|].
  fold slack in EM. fold off0 in EM. fold off in EM. fold slack off0 off.
  set (res := enframe_at st1 g idx n off) in *.
  (* [comment removed for export] *)
  assert (S31n : stride - 4 - n < 2^31) by lia.
  destruct (renframe_mrep st1 m1 g b r idx n off MR TK Hmem Hr Hk B0 ltac:(clear -IDX LI32; lia) ltac:(unfold stride, mr in SPAN; clear -SPAN S16; lia) S16 S31n NOGRP (proj1 OFF) N0 FIT (Q16 off (proj1 OFF) FIT))
    as (MRr & TKr & CONCr & FSTr & SNDr).
  fold stride B res in MRr, TKr, CONCr, FSTr, SNDr.
  change (conc st1 b) with B in MRr, CONCr. change (get_stride (get_meta_rec st1 g)) with stride in MRr, CONCr, SNDr.
  fold res in MRr, TKr, CONCr, FSTr, SNDr.
  set (P0 := B + 16 + stride * idx) in *.
  rewrite <- EM in MRr.
  destruct (rmrep_havoc (fst res) m' (snd res) n MRr TKr) as [MR' TK'].
  (* [comment removed for export] *)
  assert (PE0 : rpres_except (fun a => P0 - 4 <= a < P0 + stride - 4) m1 m').
  { rewrite EM. apply (rpres_enframe _ m1 m1 P0 stride off n idx B (rpres_except_refl _ _) (proj1 OFF) N0 FIT); [unfold P0; lia| unfold P0; lia|].
    intros x Hx. exact Hx. }
  assert (ST' : stk usegs m' lo (bv_unsigned sp + -48)).
  { eapply rpres_except_stk; [exact PE0| exact ST|]. intros a Ha. cbv beta. unfold P0. lia. }
  assert (FR' : rw_cells usegs m' (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra]).
  { eapply rpres_except_rw_cells; [exact PE0| exact FR|]. cbn [cells_size csize Nat.add Z.of_nat]. intros a Ha. cbv beta. unfold P0. lia. }
  release_frame FR' ST' (bv_unsigned sp).
  unfold renf_post. exists (havoc (snd res) n (fst res)), (snd res). do 14 eexists. exists m'.
  split; [reflexivity|].
  split. { unfold wz. rewrite conc_havoc. rewrite <- CONCr. unfold res. rewrite conc_enframe_at. reflexivity. }
  split; [exact MI'|]. split; [exact ST'|]. split; [exact MR'|]. split; [exact TK'|].
  split.
  { rewrite EM. apply (rpres_enframe C m0 m1 _ stride off n idx B PE (proj1 OFF) N0 FIT); [unfold B; lia| unfold B; lia|].
    intros x Hx. apply CSL. unfold B in Hx. lia. }
  exists off. split; [exact (proj1 OFF)|]. split; [exact FIT|].
  split. { clear - FSTr SNDr. destruct (snd res) as [p1 p2]. cbn [fst snd] in FSTr, SNDr. subst. reflexivity. }
  split; [reflexivity|]. split; [reflexivity|].
  unfold off, off0, slack, enf_off0. fold mr. fold stride. rewrite E3, E2, E1. reflexivity.
Qed.

End PORT.

End WithCeil.
End TwB.
End RF_malloc_enf.

(* [comment removed for export] *)
Module RF_malloc_join.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import TlsBase.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_enframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Malloc_fp. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocKit_A2__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.Malloc_fp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_enf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_join.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocKit_A. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocKit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_fp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RF_malloc_enf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RAllocSlot_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Local Unset Keyed Unification.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition renf_hyp {R} (K : mstate -> option (aptr * Z) -> Malloc.M R) (o m0 : mem) (st : mstate) (s : PState)
    (Q : R -> PState -> machine_state -> Prop)
    (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) : Prop :=
  forall (st2 : mstate) (g b : aptr) (r : region) (idx : Z) (m1 : mem) (s' : PState) (errv : word)
         (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 ra' : word),
    rmrep st2 m1 -> ticks_ok st2 -> unk_agree st2 o m1 -> mem_inv ssegs m1 ->
    stk ssegs m1 lo (bv_unsigned sp + -48) ->
    rw_cells ssegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
    rw_cells ssegs m1 (errno_addr tp) [C4 errv] -> rauxv_ok m1 (bv_unsigned sp) ->
    rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1 ->
    (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx - 4 <= a
                 < r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) - 4 ->
       rmalloc_fp st st2 lo (bv_unsigned sp) a) ->
    0 <= c_mmap_counter (ctx st2) < 2^32 ->
    slot_ok st2 g b r idx n ->
    (expo_cond st n -> rdv pans_mem o st2 (fst b, snd b + (16 + get_stride (get_meta_rec st2 g) * idx) + -3) = 0) ->
    mrel st st2 -> brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
    rimplT o (K st2 (Some (g, idx))) s' Q
          (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
                   a0 a1 a2 a3 a4 a5 a6 a7 (pw st2 (Some g)) (wz idx) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x19580) fc None m1 (seg_rom ssegs)).

(* [comment removed for export] *)
Definition rfail_hyp {R} (K : mstate -> option (aptr * Z) -> Malloc.M R) (o m0 : mem) (st : mstate) (s : PState)
    (Q : R -> PState -> machine_state -> Prop)
    (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) : Prop :=
  forall (st2 : mstate) (m1 : mem) (s' : PState) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    rmrep st2 m1 -> ticks_ok st2 -> mem_inv ssegs m1 -> stk ssegs m1 lo (bv_unsigned sp) ->
    rw_cells ssegs m1 (errno_addr tp) [C4 errv] -> errv = Z_to_bv 64 ENOMEM -> rauxv_ok m1 (bv_unsigned sp) ->
    rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1 ->
    mrel st st2 -> brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
    rimplT o (K st2 None) s' Q
          (MS (mkR ra sp gp tp t0 t1 t2 s0v s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m1 (seg_rom ssegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rmalloc_fp_cases st st2 lo sp m0 m2 a :
  rmrep st m0 -> rmrep st2 m2 -> rmalloc_fp st st2 lo sp a ->
  lo <= a < sp \/ a < alloc_ceiling.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros (WF & _) (WF2 & _) H. pose proof WF as (_ & WR & _). pose proof WF2 as (_ & WR2 & _).
  ceil_facts.
  destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC _]]]]].
  - left; exact H.
  - right. pose proof the_tb_facts. lia.
  - right. unfold RCTX in H. lia.
  - right. destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _). ceil_facts. lia.
  - right. destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _). ceil_facts. lia.
  - right. destruct (WR (fst b) r Hr) as (_ & _ & _ & RC & _). ceil_facts. lia.
  - right. destruct (WR (fst b) r Hr) as (_ & _ & _ & RC & _). ceil_facts. lia.
  - right. ceil_facts. lia.
Qed.

Lemma rframe_after_call st st2 lo sp' m0 m m' m2 A cs :
  rmrep st m0 -> rmrep st2 m2 ->
  rpres_except (rmalloc_fp st st2 lo sp') m m' -> rw_cells ssegs m A cs ->
  sp' <= A -> alloc_ceiling <= A -> rw_cells ssegs m' A cs.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros MR0 MR2 PE H HA HC. eapply rpres_except_rw_cells; [exact PE| exact H|].
  intros a Ha Hfp. destruct (rmalloc_fp_cases st st2 lo sp' m0 m2 a MR0 MR2 Hfp); lia.
Qed.

Lemma rmalloc_fp_sp_mono st st2 lo sp1 sp2 a : sp1 <= sp2 -> rmalloc_fp st st2 lo sp1 a -> rmalloc_fp st st2 lo sp2 a.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros H [[X|X]|X]; [left; left; lia| left; right; exact X| right; exact X].
Qed.

Lemma rmalloc_fp_st_mono st sta stb lo sp a : mrel sta stb -> rmalloc_fp st sta lo sp a -> rmalloc_fp st stb lo sp a.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts. intros [HR _ _] H. eapply rmalloc_fp_mono; [exact HR| exact H]. Qed.

Lemma rmalloc_fp_image st st2 lo sp m0 m2 a :
  rmrep st m0 -> rmrep st2 m2 -> rmalloc_fp st st2 lo sp a -> alloc_ceiling <= lo ->
  0x22000 <= a < 0x55000 -> RCTX <= a < RCTX + 928 \/ RERRNO <= a < RERRNO + 4.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros (WF & _) (WF2 & _) H CLO HA. pose proof WF as (_ & WR & _). pose proof WF2 as (_ & WR2 & _).
  ceil_facts.
  assert (IMG : forall P : Prop, (forall rid r, (s_regions st) !! rid = Some r -> r_base r <= a < r_base r + round_up_pg (r_len r) -> P)
                 /\ (forall rid r, (s_regions st2) !! rid = Some r -> r_base r <= a < r_base r + round_up_pg (r_len r) -> P)).
  { intros P. split; intros rid r Hr Ha.
    - destruct (WR rid r Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint2 _ _ RF ltac:(lia)) as [D1 D2]. exfalso. lia.
    - destruct (WR2 rid r Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint2 _ _ RF ltac:(lia)) as [D1 D2]. exfalso. lia. }
  destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC FR]]]]].
  - exfalso. lia.
  - right. exact H.
  - left. exact H.
  - pose proof (lr_lo_ge r). apply (proj2 (IMG _) rid r Hr ltac:(lia)).
  - pose proof (lr_lo_ge r). apply (proj2 (IMG _) rid r Hr ltac:(lia)).
  - apply (proj1 (IMG _) (fst b) r Hr Ha).
  - apply (proj1 (IMG _) (fst b) r Hr Ha).
  - (* [comment removed for export] *)
    exfalso. pose proof WF as (RS & _). pose proof (rfresh_image st a (conj FC FR) RS). lia.
Qed.

Lemma rauxv_ok_malloc_fp st st2 lo sp m0 m2 m m' B :
  rmrep st m0 -> rmrep st2 m2 -> rauxv_ok m B -> rpres_except (rmalloc_fp st st2 lo sp) m m' ->
  alloc_ceiling <= lo -> sp <= B -> rauxv_ok m' B.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros MR0 MR2 AUX PE CLO SB. eapply rauxv_ok_pres; [exact AUX| exact PE| |].
  - intros a Ha Hfp. destruct (rmalloc_fp_cases st st2 lo sp m0 m2 a MR0 MR2 Hfp); [lia|].
    destruct AUX as (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & _ & _ & _ & HH). ceil_facts. lia.
  - intros a Ha Hfp. unfold RAUXV_CELL, RLIBC in Ha.
    pose proof the_tb_facts. destruct (rmalloc_fp_image st st2 lo sp m0 m2 a MR0 MR2 Hfp CLO ltac:(lia)) as [X|X]; unfold RCTX in X; lia.
Qed.

End PORT.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.TlsBaseU.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.SFModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_enframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.Malloc_fp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_enf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_join.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocKit_A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_fp.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RF_malloc_enf.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RAllocSlot_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MSecret.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Local Unset Keyed Unification.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition renf_hyp {R} (K : mstate -> option (aptr * Z) -> Malloc.M R) (o m0 : mem) (st : mstate) (s : PState)
    (Q : R -> PState -> machine_state -> Prop)
    (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) : Prop :=
  forall (st2 : mstate) (g b : aptr) (r : region) (idx : Z) (m1 : mem) (s' : PState) (errv : word)
         (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 ra' : word),
    rmrep st2 m1 -> ticks_ok st2 -> unk_agree st2 o m1 -> mem_inv usegs m1 ->
    stk usegs m1 lo (bv_unsigned sp + -48) ->
    rw_cells usegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
    rw_cells usegs m1 (errno_addr tp) [C4 errv] -> rauxv_ok m1 (bv_unsigned sp) ->
    rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1 ->
    (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx - 4 <= a
                 < r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) - 4 ->
       rmalloc_fp st st2 lo (bv_unsigned sp) a) ->
    0 <= c_mmap_counter (ctx st2) < 2^32 ->
    slot_ok st2 g b r idx n ->
    (expo_cond st n -> rdv pans_mem o st2 (fst b, snd b + (16 + get_stride (get_meta_rec st2 g) * idx) + -3) = 0) ->
    mrel st st2 -> brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
    rimplT o (K st2 (Some (g, idx))) s' Q
          (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
                   a0 a1 a2 a3 a4 a5 a6 a7 (pw st2 (Some g)) (wz idx) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x19d40) fc None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition rfail_hyp {R} (K : mstate -> option (aptr * Z) -> Malloc.M R) (o m0 : mem) (st : mstate) (s : PState)
    (Q : R -> PState -> machine_state -> Prop)
    (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) : Prop :=
  forall (st2 : mstate) (m1 : mem) (s' : PState) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    rmrep st2 m1 -> ticks_ok st2 -> mem_inv usegs m1 -> stk usegs m1 lo (bv_unsigned sp) ->
    rw_cells usegs m1 (errno_addr tp) [C4 errv] -> errv = Z_to_bv 64 ENOMEM -> rauxv_ok m1 (bv_unsigned sp) ->
    rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1 ->
    mrel st st2 -> brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
    rimplT o (K st2 None) s' Q
          (MS (mkR ra sp gp tp t0 t1 t2 s0v s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m1 (seg_rom usegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rmalloc_fp_cases st st2 lo sp m0 m2 a :
  rmrep st m0 -> rmrep st2 m2 -> rmalloc_fp st st2 lo sp a ->
  lo <= a < sp \/ a < alloc_ceiling.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros (WF & _) (WF2 & _) H. pose proof WF as (_ & WR & _). pose proof WF2 as (_ & WR2 & _).
  ceil_facts.
  destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC _]]]]].
  - left; exact H.
  - right. pose proof the_tb_facts. lia.
  - right. unfold RCTX in H. lia.
  - right. destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _). ceil_facts. lia.
  - right. destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _). ceil_facts. lia.
  - right. destruct (WR (fst b) r Hr) as (_ & _ & _ & RC & _). ceil_facts. lia.
  - right. destruct (WR (fst b) r Hr) as (_ & _ & _ & RC & _). ceil_facts. lia.
  - right. ceil_facts. lia.
Qed.

Lemma rframe_after_call st st2 lo sp' m0 m m' m2 A cs :
  rmrep st m0 -> rmrep st2 m2 ->
  rpres_except (rmalloc_fp st st2 lo sp') m m' -> rw_cells usegs m A cs ->
  sp' <= A -> alloc_ceiling <= A -> rw_cells usegs m' A cs.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros MR0 MR2 PE H HA HC. eapply rpres_except_rw_cells; [exact PE| exact H|].
  intros a Ha Hfp. destruct (rmalloc_fp_cases st st2 lo sp' m0 m2 a MR0 MR2 Hfp); lia.
Qed.

Lemma rmalloc_fp_sp_mono st st2 lo sp1 sp2 a : sp1 <= sp2 -> rmalloc_fp st st2 lo sp1 a -> rmalloc_fp st st2 lo sp2 a.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros H [[X|X]|X]; [left; left; lia| left; right; exact X| right; exact X].
Qed.

Lemma rmalloc_fp_st_mono st sta stb lo sp a : mrel sta stb -> rmalloc_fp st sta lo sp a -> rmalloc_fp st stb lo sp a.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts. intros [HR _ _] H. eapply rmalloc_fp_mono; [exact HR| exact H]. Qed.

Lemma rmalloc_fp_image st st2 lo sp m0 m2 a :
  rmrep st m0 -> rmrep st2 m2 -> rmalloc_fp st st2 lo sp a -> alloc_ceiling <= lo ->
  0x22000 <= a < 0x56000 -> RCTX <= a < RCTX + 928 \/ RERRNO <= a < RERRNO + 4.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros (WF & _) (WF2 & _) H CLO HA. pose proof WF as (_ & WR & _). pose proof WF2 as (_ & WR2 & _).
  ceil_facts.
  assert (IMG : forall P : Prop, (forall rid r, (s_regions st) !! rid = Some r -> r_base r <= a < r_base r + round_up_pg (r_len r) -> P)
                 /\ (forall rid r, (s_regions st2) !! rid = Some r -> r_base r <= a < r_base r + round_up_pg (r_len r) -> P)).
  { intros P. split; intros rid r Hr Ha.
    - destruct (WR rid r Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint2 _ _ RF ltac:(lia)) as [D1 D2]. exfalso. lia.
    - destruct (WR2 rid r Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint2 _ _ RF ltac:(lia)) as [D1 D2]. exfalso. lia. }
  destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC FR]]]]].
  - exfalso. lia.
  - right. exact H.
  - left. exact H.
  - pose proof (lr_lo_ge r). apply (proj2 (IMG _) rid r Hr ltac:(lia)).
  - pose proof (lr_lo_ge r). apply (proj2 (IMG _) rid r Hr ltac:(lia)).
  - apply (proj1 (IMG _) (fst b) r Hr Ha).
  - apply (proj1 (IMG _) (fst b) r Hr Ha).
  - (* [comment removed for export] *)
    exfalso. pose proof WF as (RS & _). pose proof (rfresh_image st a (conj FC FR) RS). lia.
Qed.

Lemma rauxv_ok_malloc_fp st st2 lo sp m0 m2 m m' B :
  rmrep st m0 -> rmrep st2 m2 -> rauxv_ok m B -> rpres_except (rmalloc_fp st st2 lo sp) m m' ->
  alloc_ceiling <= lo -> sp <= B -> rauxv_ok m' B.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros MR0 MR2 AUX PE CLO SB. eapply rauxv_ok_pres; [exact AUX| exact PE| |].
  - intros a Ha Hfp. destruct (rmalloc_fp_cases st st2 lo sp m0 m2 a MR0 MR2 Hfp); [lia|].
    destruct AUX as (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & _ & _ & _ & HH). ceil_facts. lia.
  - intros a Ha Hfp. unfold RAUXV_CELL, RLIBC in Ha.
    pose proof the_tb_facts. destruct (rmalloc_fp_image st st2 lo sp m0 m2 a MR0 MR2 Hfp CLO ltac:(lia)) as [X|X]; unfold RCTX in X; lia.
Qed.

End PORT.

End WithCeil.
End TwB.
End RF_malloc_join.
