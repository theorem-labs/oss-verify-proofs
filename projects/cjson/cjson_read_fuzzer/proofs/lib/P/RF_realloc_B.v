(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Image.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ZBridge.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SFModel.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ITree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Decode.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require PImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_Bpres.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_malloc_enframe.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocTree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocKit_A2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require STree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Malloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MallocCtrl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Monad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prog.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Malloc_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_malloc_entry.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RMallocRep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RRealloc_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require SspGuard.
From Stdlib Require Zify.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require HeapLiaImp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Module RF_malloc_entry.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_entry.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.
(* [comment removed for export] *)
Local Ltac step ::= step2_fast. Local Ltac stepz ::= stepz_fast.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.



(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

(* [comment removed for export] *)
Definition rDB32 : Z := 125613361.   (* [comment removed for export] *)
Definition rdbi (k : Z) : Z := ((2 ^ k * rDB32) mod 2^32) / 2^27.

Lemma rdbi_range k : 0 <= rdbi k < 32.
Proof using . unfold rdbi. pose proof (Z.mod_pos_bound (2^k * rDB32) (2^32) ltac:(lia)). Z.div_mod_to_equations. nia. Qed.

Definition rdebruijn_bytes : list byte :=
  Eval vm_compute in (match image_bytes psegs RDEBRUIJN 32 return list byte with Some bs => bs | None => [] end).  (* [comment removed for export] *)

Lemma rdebruijn_ro : forall m, mem_inv psegs m -> ro_cells psegs m RDEBRUIJN [CB 32 rdebruijn_bytes].
Proof using . intros m MI. apply (ro_cells_image psegs m); [exact MI | vm_compute; reflexivity | unfold RDEBRUIJN; lia | unfold RDEBRUIJN; cbn; lia]. Qed.

Lemma rdebruijn_read : forall m k, mem_inv psegs m -> 0 <= k < 32 ->
  ov_read_bytes psegs m (wa (RDEBRUIJN + rdbi k)) 1 = Some [b8 k].
Proof using .
  intros m k MI Hk.
  destruct (rdebruijn_ro m MI) as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  pose proof (rdbi_range k) as R.
  rewrite (bytes_at_read psegs m RDEBRUIJN rdebruijn_bytes (rdbi k) 1 B) by (cbn; lia).
  assert (Hn : exists n, k = Z.of_nat n /\ (n < 32)%nat) by (exists (Z.to_nat k); split; [lia|lia]).
  destruct Hn as (n & -> & Hn).
  Ltac solve_db := vm_compute; reflexivity.
  do 32 (destruct n as [|n]; [solve_db |]). lia.
Qed.

(* [comment removed for export] *)
Lemma mul_srliw27 k : 0 <= k < 32 ->
  bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (Z_to_bv 64 (2 ^ k * rDB32)))) 27) = rdbi k.
Proof using .
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
Lemma rclz_check_true : forallb rclz_fn (zseq 11 8181) = true.
Proof using . vm_cast_no_check (@eq_refl bool true).  (* [comment removed for export] *) Qed.
Lemma rclz_pow_eq x : 11 <= x < 8192 -> rclz_pow x = 2 ^ Z.log2 x /\ 0 <= rclz_v4 x < 2 ^ 13.
Proof using .
  intros Hx. pose proof (forallb_zseq rclz_fn 11 8181 x rclz_check_true ltac:(lia) ltac:(lia)) as X. unfold rclz_fn in X.
  apply andb_prop in X. destruct X as [X1 X2].
  apply Z.eqb_eq in X1. apply Z.ltb_lt in X2. split; [exact X1| split; [|exact X2]].
  unfold rclz_v4. repeat first [apply Z.lor_nonneg; split | apply Z.shiftr_nonneg]; lia.
Qed.

Lemma lxor_4k_124 k : 3 <= k <= 12 -> Z.lxor (k * 4) 124 = 124 - 4 * k.
Proof using . intros Hk. assert (H : k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12) by lia.
  destruct H as [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]]]; reflexivity. Qed.

Lemma lor_even_1 a : 0 <= a -> Z.even a = true -> Z.lor a 1 = a + 1.
Proof using . intros Ha He.
  assert (D : Z.land a 1 = 0). { change 1 with (Z.ones 1). rewrite Z.land_ones by lia. change (2^1) with 2. rewrite Zeven_mod in He. apply Z.eqb_eq in He. exact He. }
  rewrite <- Z.lxor_lor by exact D. rewrite <- Z.add_nocarry_lxor by exact D. reflexivity. Qed.

Definition rentry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
   (lo : Z) (m : mem) (n : Z) : machine_state -> Prop :=
  fun ms' => exists a0 a1 a2 a3 m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) a0 a1 a2 a3 a4 a5 a6 a7
                  s2 (Z_to_bv 64 RDEBRUIJN) (Z_to_bv 64 (size_to_class n)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x15ebc) fc None m' (seg_rom psegs)
    /\ rw_cells psegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk psegs m' lo (bv_unsigned sp + -48)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'.

Lemma rmalloc_entry_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (lo n : Z),
  a0 = Z_to_bv 64 n -> 0 <= n < MMAP_THRESHOLD ->
  stk psegs m lo (bv_unsigned sp) -> 0x55000 <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv psegs m ->
  rw_cells psegs m RNEED_LOCKS [C1 (b8 0)] ->
  evt psegs (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m n)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom psegs)).
Proof.
  intros until n. intros HA N ST ILO LO MI NL. subst a0.
  pose proof (size_to_class_props n N) as (SCR & SFIT & LG). unfold MMAP_THRESHOLD in N.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
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
    mem_inv psegs mj -> rw_cells psegs mj (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> stk psegs mj lo (bv_unsigned sp + -48) ->
    munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m mj -> wmono psegs m mj -> rw_cells psegs mj 342811 [C1 (b8 0)] ->
    evt psegs (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m n)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 342920) a0' a1' a2' a3' a4 a5 a6 a7
               s2 (Z_to_bv 64 67648) (Z_to_bv 64 sc) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x15ea4) fc None mj (seg_rom psegs))).
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
    lazymatch goal with HI : mem_inv psegs ?mc |- _ => pose proof (rdebruijn_read mc k HI ltac:(lia)) as DBR; unfold RDEBRUIJN in DBR end.
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
    step. step. replace (67680 + (i + 1) * 2) with (67680 + 2 * (i + 1)) by lia.
    lazymatch goal with HI : mem_inv psegs ?mc |- _ => pose proof (rsize_classes_read mc (i + 1) HI ltac:(lia)) as RS1; unfold RSIZE_CLASSES in RS1 end.
    (* [comment removed for export] *)
    step. rewrite ?zx16_wz by lia. clear RS1.
    (* [comment removed for export] *)
    assert (J1 : forall (i1 c : Z) (mj : mem),
      i1 = (if size_class (i + 1) <? x then i + 2 else i) -> c = i1 - i + 120 ->
      mem_inv psegs mj -> rw_cells psegs mj (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> stk psegs mj lo (bv_unsigned sp + -48) ->
      munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m mj -> wmono psegs m mj -> rw_cells psegs mj 342811 [C1 (b8 0)] ->
      evt psegs (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m n)
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 342920)
                 (Z_to_bv 64 (120 - i)) (Z_to_bv 64 67680) (Z_to_bv 64 c) (Z_to_bv 64 (67680 + 2 * (i + 1))) a4 a5 a6 a7
                 s2 (Z_to_bv 64 67648) (Z_to_bv 64 q) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x15e88) fc None mj (seg_rom psegs))).
    { intros i1 c mj Hi1 Hc MIj FRj STj MUj WMj NLj.
      assert (I1R : 8 <= i1 <= 46 /\ Z.even i1 = true).
      { subst i1. destruct (size_class (i + 1) <? x); (split; [lia|]); rewrite ?Z.even_add, ?IEV; reflexivity. }
      destruct I1R as [I1R I1E].
      pose proof (size_class_range i1 ltac:(lia)) as SR2.
      (* [comment removed for export] *)
      step. rewrite (unsigned_lit c), (unsigned_lit (120 - i)) by lia. replace (c - (120 - i)) with i1 by lia.
      step. rewrite (unsigned_lit i1), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
      step. replace (67680 + i1 * 2) with (67680 + 2 * i1) by lia.
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

(* [comment removed for export] *)
Definition rentry_big_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
   (lo : Z) (m : mem) (n : Z) : machine_state -> Prop :=
  fun ms' => exists a1 m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 131052) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x15d24) fc None m' (seg_rom psegs)
    /\ rw_cells psegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk psegs m' lo (bv_unsigned sp + -48)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'.

Lemma rentry_big_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (lo n : Z),
  a0 = Z_to_bv 64 n -> MMAP_THRESHOLD <= n < 2^32 ->
  stk psegs m lo (bv_unsigned sp) -> 0x55000 <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv psegs m ->
  evt psegs (rentry_big_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m n)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom psegs)).
Proof using .
  intros until n. intros HA N ST ILO LO MI. subst a0. unfold MMAP_THRESHOLD in N.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
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
  lazymatch goal with H : rw_cells psegs _ (bv_unsigned sp + -48) _ |- _ => split; [exact H|] end.
  repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed.


End CeilWrap.
End RF_malloc_entry.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Export PImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import MallocRep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_Bpres.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_malloc_enframe.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import F_malloc_entry.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import RMallocRep.
Import RF_malloc_entry.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import SspGuard.
(* [comment removed for export] *)
From Stdlib Require Import Zify Lia.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require HeapLiaImp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.
(* [comment removed for export] *)
Local Ltac step ::= step2_fast. Local Ltac stepz ::= stepz_fast.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition RR_INPLACE : Z := 0x16f58.
Definition RR_MALLOC : Z := 0x16f18.
Definition RR_BIG : Z := 0x16e30.

Section DECIDE.
Variables (ra sp' gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 gw t1v a2v a4v t4v : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : word -> option byte) (P n sc E rsv : Z).
Variable Q : machine_state -> Prop.
Let rom := seg_rom psegs.

Hypothesis HP : bv_unsigned a0 = P.
Hypothesis HN : bv_unsigned a1 = n.
Hypothesis N32 : 0 <= n < 2^32.
Hypothesis PE : 0 <= P <= E.
Hypothesis E64 : E < 2^63.
Hypothesis SC : 0 <= sc < 64.
Hypothesis SC63 : 48 <= sc -> sc = 63.
Hypothesis MI : mem_inv psegs m.

(* [comment removed for export] *)
Hypothesis KIN : n <= E - P -> n < MMAP_THRESHOLD -> sc <= size_to_class n + 1 ->
  forall t1' t2' t3' a4' a5' a7',
  evt psegs Q (MS (mkR ra sp' gp tp (Z_to_bv 64 E) t1' t2' s0 gw a0 a1 (Z_to_bv 64 (size_to_class n + 1)) (Z_to_bv 64 sc) a4' a5'
                    (Z_to_bv 64 (E + 4)) a7' (Z_to_bv 64 (E - rsv)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4v t5 t6)
                  F (Z_to_bv 64 RR_INPLACE) fc None m rom).
(* [comment removed for export] *)
Hypothesis KMAL : ~ (n <= E - P /\ n < MMAP_THRESHOLD /\ sc <= size_to_class n + 1) -> ~ (48 <= sc /\ MMAP_THRESHOLD <= n) ->
  forall t1' t2' t3' a2' a4' a5' a7',
  evt psegs Q (MS (mkR ra sp' gp tp (Z_to_bv 64 E) t1' t2' s0 gw a0 a1 a2' (Z_to_bv 64 sc) a4' a5'
                    (Z_to_bv 64 (E + 4)) a7' (Z_to_bv 64 (E - rsv)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4v t5 t6)
                  F (Z_to_bv 64 RR_MALLOC) fc None m rom).
(* [comment removed for export] *)
Hypothesis KBIG : MMAP_THRESHOLD <= n -> sc = 63 ->
  forall t2' t3' a5',
  evt psegs Q (MS (mkR ra sp' gp tp (Z_to_bv 64 E) t1v t2' s0 gw a0 a1 a2v (Z_to_bv 64 sc) a4v a5'
                    (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E + - bv_unsigned a0)) (Z_to_bv 64 (E - rsv)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4v t5 t6)
                  F (Z_to_bv 64 RR_BIG) fc None m rom).

Lemma rr_decide_walk : forall t3v,
  evt psegs Q (MS (mkR ra sp' gp tp (Z_to_bv 64 E) t1v (wz 0) s0 gw a0 a1 a2v (Z_to_bv 64 sc) a4v (Z_to_bv 64 RSIZE_CLASSES)
                    (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E + - bv_unsigned a0)) (Z_to_bv 64 (E - rsv)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3v t4v t5 t6)
                  F (Z_to_bv 64 0x16d74) fc None m rom).
Proof using E64 HN HP KBIG KIN KMAL MI N32 PE SC SC63.
  intros t3v. subst rom. unfold RR_INPLACE, RR_MALLOC, RR_BIG, MMAP_THRESHOLD in *.
  pose proof (bv_unsigned_in_range 64 a0) as A0R. unfold bv_modulus in A0R.
  assert (BIGT : forall t3' a5',
    (131052 <= n \/ E - P < n) ->
    evt psegs Q (MS (mkR ra sp' gp tp (Z_to_bv 64 E) t1v (Z_to_bv 64 131072) s0 gw a0 a1 a2v (Z_to_bv 64 sc) a4v a5'
                    (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E + - bv_unsigned a0)) (Z_to_bv 64 (E - rsv)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4v t5 t6)
                  F (Z_to_bv 64 0x16e14) fc None m (seg_rom psegs))).
  { intros t3' a5' HC.
    (* [comment removed for export] *)
    st1. st1. if_cases K3; zify_cond K3; rewrite ?unsigned_lit, ?HN in K3 by lia.
    { (* [comment removed for export] *) apply KMAL; lia. }
    (* [comment removed for export] *)
    st1. st1. if_cases K4; zify_cond K4; rewrite ?unsigned_lit in K4 by lia.
    { apply KMAL; lia. }
    (* [comment removed for export] *)
    specialize (SC63 ltac:(lia)).
    st1. st1. if_cases K5; zify_cond K5; rewrite ?unsigned_lit in K5 by lia.
    2:{ exfalso. lia. }
    apply KBIG; lia. }
  (* [comment removed for export] *)
  st1. st1. st1. if_cases K1; zify_cond K1; rewrite ?unsigned_lit, ?HN in K1 by lia.
  { apply BIGT. lia. }
  (* [comment removed for export] *)
  st1. if_cases K2; zify_cond K2; rewrite ?unsigned_lit, ?HN, ?HP in K2 by lia.
  { apply BIGT. lia. }
  pose proof (size_to_class_props n ltac:(unfold MMAP_THRESHOLD; lia)) as (SCR & SFIT & LG).
  (* [comment removed for export] *)
  assert (JOIN : forall t1' a4' a5' a7' scn, scn = size_to_class n ->
    evt psegs Q (MS (mkR ra sp' gp tp (Z_to_bv 64 E) t1' (Z_to_bv 64 131072) s0 gw a0 a1 (Z_to_bv 64 scn) (Z_to_bv 64 sc) a4' a5'
                    (Z_to_bv 64 (E + 4)) a7' (Z_to_bv 64 (E - rsv)) s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 131051) t4v t5 t6)
                  F (Z_to_bv 64 0x16f10) fc None m (seg_rom psegs))).
  { intros t1' a4' a5' a7' scn ->.
    st1. rewrite swrap32_small by lia. st1. if_cases K6; zify_cond K6; rewrite ?signed_wz_small in K6 by lia.
    - apply KIN; lia.
    - apply KMAL; lia. }
  (* [comment removed for export] *)
  st1. st1. st1. rewrite HN. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
  set (q := (n + 3) / 16) in *. assert (QR : 0 <= q < 8191) by (subst q; Z.div_mod_to_equations; lia).
  assert (STC : size_to_class n = stc_q q) by (apply size_to_class_q; lia).
  st1. if_cases K7; zify_cond K7; rewrite ?unsigned_lit, ?HN in K7 by lia.
  { (* [comment removed for export] *)
    apply JOIN. rewrite STC. unfold stc_q. replace (q <? 10) with true by (symmetry; apply Z.ltb_lt; subst q; Z.div_mod_to_equations; lia). reflexivity. }
  (* [comment removed for export] *)
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
  step.
  step. rewrite ?(unsigned_lit (w4 + 1)) by lia. rewrite ?(unsigned_lit w4) by lia. rewrite ?(unsigned_lit (Z.lxor w4 18446744073709551615)) by (rewrite zb_lxor_ones by lia; lia).
  change (Z.land (w4 + 1) (Z.lxor w4 18446744073709551615)) with (rclz_pow x). rewrite PW.
  set (k := Z.log2 x) in *.
  assert (P2 : 0 < 2 ^ k < 2 ^ 13) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
  assert (EK : k = Z.log2 x) by reflexivity. clearbody k. clear PW RV4 EW4 RW4 R5 RW3 R4 RW2 R3 RV2 RV1 R1 R2. subst w4 w3 w2 v2 v1.
  assert (EX : x = q + 1) by reflexivity. clearbody x.
  assert (K13 : 3 <= k <= 12) by (apply LG; lia).
  (* [comment removed for export] *)
  step. step. step.
  step. rewrite ?(unsigned_lit (2 ^ k)) by lia. change 125613361 with rDB32.
  step. rewrite ?(unsigned_lit (2 ^ k * rDB32)), (mul_srliw27 k) by lia.
  pose proof (rdbi_range k) as DR.
  step. rewrite ?(unsigned_lit (rdbi k)) by lia.
  pose proof (rdebruijn_read m k MI ltac:(lia)) as DBR. unfold RDEBRUIJN in DBR.
  step. rewrite ?zxb_b8 by lia. clear DBR.
  (* [comment removed for export] *)
  step. rewrite ?(wz_unsigned k), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
  step. rewrite ?(unsigned_lit (k * 4)), lxor_4k_124 by lia.
  set (i := 4 * k - 4). assert (IR : 8 <= i <= 44) by lia.
  replace (124 - 4 * k) with (120 - i) by lia.
  assert (STQ : stc_q q = (let i1 := if size_class (i + 1) <? x then i + 2 else i in if size_class i1 <? x then i1 + 1 else i1)).
  { unfold stc_q. replace (q <? 10) with false by (symmetry; apply Z.ltb_ge; lia). rewrite <- EX, <- EK. reflexivity. }
  assert (IEV : Z.even i = true) by (subst i; rewrite Z.even_sub, Z.even_mul; reflexivity).
  clearbody i. clear EK.
  pose proof (size_class_range (i + 1) ltac:(lia)) as SR1.
  step. step. rewrite ?(unsigned_lit (120 - i)) by lia. replace (121 + - (120 - i)) with (i + 1) by lia.
  step. rewrite ?(unsigned_lit (i + 1)), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
  step. unfold RSIZE_CLASSES. replace (67680 + (i + 1) * 2) with (67680 + 2 * (i + 1)) by lia.
  pose proof (rsize_classes_read m (i + 1) MI ltac:(lia)) as RS1. unfold RSIZE_CLASSES in RS1.
  step. rewrite ?zx16_wz by lia. clear RS1.
  (* [comment removed for export] *)
  assert (J1 : forall (i1 c : Z),
    i1 = (if size_class (i + 1) <? x then i + 2 else i) -> c = i1 - i + 120 ->
    evt psegs Q (MS (mkR ra sp' gp tp (Z_to_bv 64 E) (Z_to_bv 64 67648) (Z_to_bv 64 131072) s0 gw a0 a1 (Z_to_bv 64 q) (Z_to_bv 64 sc)
                    (Z_to_bv 64 (120 - i)) (Z_to_bv 64 67680) (Z_to_bv 64 (E + 4)) (Z_to_bv 64 c) (Z_to_bv 64 (E - rsv))
                    s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 131051) t4v t5 t6)
          F (Z_to_bv 64 0x16ef4) fc None m (seg_rom psegs))).
  { intros i1 c Hi1 Hc.
    assert (I1R : 8 <= i1 <= 46 /\ Z.even i1 = true).
    { subst i1. destruct (size_class (i + 1) <? x); (split; [lia|]); rewrite ?Z.even_add, ?IEV; reflexivity. }
    destruct I1R as [I1R I1E].
    pose proof (size_class_range i1 ltac:(lia)) as SR2.
    (* [comment removed for export] *)
    step. rewrite ?(unsigned_lit c), (unsigned_lit (120 - i)) by lia. replace (c + - (120 - i)) with i1 by lia.
    step. rewrite ?(unsigned_lit i1), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
    step. replace (67680 + i1 * 2) with (67680 + 2 * i1) by lia.
    pose proof (rsize_classes_read m i1 MI ltac:(lia)) as RS2. unfold RSIZE_CLASSES in RS2.
    step. rewrite ?zx16_wz by lia. clear RS2.
    (* [comment removed for export] *)
    step. rewrite v_sltu_b2z, (unsigned_lit q), (wz_unsigned (size_class i1)) by lia.
    step. step.
    destruct (Z.ltb_spec q (size_class i1)) as [LT|GE]; cbn [Z.b2z].
    * rewrite ?(unsigned_lit 1), (unsigned_lit i1) by lia. change (Z.lxor 1 1) with 0. rewrite ?(unsigned_lit 0), Z.lor_0_r by lia.
      apply JOIN. rewrite STC, STQ. cbv zeta. rewrite <- Hi1.
      replace (size_class i1 <? x) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
    * rewrite ?(unsigned_lit 0), (unsigned_lit i1) by lia. change (Z.lxor 0 1) with 1. rewrite ?(unsigned_lit 1), (lor_even_1 i1 ltac:(lia) I1E) by lia.
      apply JOIN. rewrite STC, STQ. cbv zeta. rewrite <- Hi1.
      replace (size_class i1 <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  (* [comment removed for export] *)
  step. if_cases K8; zify_cond K8; rewrite ?(unsigned_lit q), ?(wz_unsigned (size_class (i + 1))) in K8 by lia.
  + (* [comment removed for export] *)
    step. eapply J1; [reflexivity|]. replace (size_class (i + 1) <? x) with false by (symmetry; apply Z.ltb_ge; lia). lia.
  + (* [comment removed for export] *)
    step. step. eapply J1; [reflexivity|]. replace (size_class (i + 1) <? x) with true by (symmetry; apply Z.ltb_lt; lia). lia.
Qed.

End DECIDE.


End CeilWrap.
