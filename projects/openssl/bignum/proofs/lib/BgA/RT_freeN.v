(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Mem Frame Cells Step Arr Exec RzCPS MState. 
From OSSVerify.Proofs.openssl.bignum.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow R_sizeclass.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_quar_defs R_qput R_qenqueue R_qenqueue_N R_qenqueue_F R_qenqueue_M R_qenqueue_MF R_asan_free R_prim_kit R_refill RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeA2 RT_freestmt RT_freeC RT_freeD RT_freeF RT_freeG RT_freeE RT_freeH RT_freeI RT_freeJ RT_freeK RT_freeL RT_freeM RT_refillstmt RT_refillst RT_refillwf RT_rfkit RT_refillrun RT_count RT_refill RT_sys_stmt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition mf_post (Σ : rtsA) (c : Z) (i : nat) (n : Z) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (tr : list Z) (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m5 : mem) (jf : list byte),
    ms = refill_entry_st (Z_to_bv 64 qenq_refill_ret) (Z_to_bv 64 (bv_unsigned sp + -2208 + -64)) gp t0' t1' t2'
           (Z_to_bv 64 (pc_addr (l_T (lay Σ)) 24)) (Z_to_bv 64 (cacheT (l_T (lay Σ)))) a4' a5' a6' a7'
           (Z_to_bv 64 (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16)) (Z_to_bv 64 (qcacheT (l_T (lay Σ)))) (Z_to_bv 64 (bv_unsigned sp + -2128))
           (Z_to_bv 64 n) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc (l_T (lay Σ)) 24 m5
    /\ ARTc (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))) m5
    /\ (In tr T_MAIN /\ (1 <= length tr <= TR_MAX)%nat)
    /\ mem_inv bgasegs m5 /\ wmono bgasegs m m5 /\ stk bgasegs m5 lo (bv_unsigned sp + -2208 + -64)
    /\ rt_pres (live_remove (p_abeg (l_SB (lay Σ)) c i + rz_size n) (live Σ)) (frames Σ) (bv_unsigned sp) m m5
    /\ icpt_frame m5 (bv_unsigned sp) ra s0 s1 s2 s3 s4 s5
    /\ qput_frame m5 (bv_unsigned sp + -2208) (Z_to_bv 64 (l_T (lay Σ) + 208)) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 0x1c3144)
         (Z_to_bv 64 (bv_unsigned sp)) (Z_to_bv 64 (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16 + 16)) (Z_to_bv 64 0x1c30d4) (Z_to_bv 64 1)
         (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (bv_unsigned sp + -81)) s6
    /\ rw_cells bgasegs m5 (bv_unsigned sp + -2208 + -64)
         [CB 8 jf; C8 (Z_to_bv 64 (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16)); C8 (Z_to_bv 64 (l_T (lay Σ) + 208));
          C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (l_T (lay Σ) + 80)); C8 (Z_to_bv 64 QUAR);
          C8 (Z_to_bv 64 0x19f284)].

Lemma rt_eager_fp : forall Σ c i n p D', rt_eager (free_p Σ c i n p D') = rt_eager Σ.
Proof.
  intros Σ c i n p D'. apply rt_eager_ext; [|reflexivity | reflexivity]. intros k'.
  cbn [free_p pr]. destruct (Z.eqb_spec k' c) as [->|_]; [unfold upd_reg; cbn [r_muser r_mfa]|]; split; reflexivity.
Qed.

