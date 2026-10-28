(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Bs0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BZBridge BacX BSFModel BSysStep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition AFS_MALLOC_0 : Z := 0x9dae4.
Definition AFS_MALLOC_2 : Z := 0x9dde8.
Definition AFS_MALLOC_3 : Z := 0x9df84.
Definition AFS_MALLOC_5 : Z := 0x9e3f4.
Definition AFS_MALLOC_6 : Z := 0x9e2fc.
Definition AFS_MALLOC_8 : Z := 0x9e4e0.
Definition AFS_FREE_5   : Z := 0x9e600.
Definition AFS_FREE_6   : Z := 0x9e498.
Definition AFS_FREE_8   : Z := 0x9e65c.
Definition ASET_SHADOW_F8 : Z := 0xbc214.

Definition AFS_MAXLIVE_BP : nat := 64.

Definition RT_SMALL_MAX : Z := 3 * 2 ^ 29.
Definition RT_CNT_MAX : Z := 2 ^ 25.
Definition RT_LARGE_MAX : Z := 64.
Definition nsmall (n : Z) : Z := if n <=? 64512 then n else 0.
Definition nlg (n : Z) : Z := if 64512 <? n then 1 else 0.
Definition lb_small (LB : list block) : Z := fold_right (fun b acc => nsmall (blk_size b) + acc) 0 LB.
Definition nlarge (LB : list block) : Z := fold_right (fun b acc => nlg (blk_size b) + acc) 0 LB.
Lemma lb_small_cons : forall b LB, lb_small (b :: LB) = nsmall (blk_size b) + lb_small LB. Proof. reflexivity. Qed.
Lemma nlarge_cons : forall b LB, nlarge (b :: LB) = nlg (blk_size b) + nlarge LB. Proof. reflexivity. Qed.
Lemma nsmall_bounds : forall n, 0 <= n -> 0 <= nsmall n <= n. Proof. intros n H. unfold nsmall. destruct (Z.leb_spec n 64512); lia. Qed.
Lemma nlg_bounds : forall n, 0 <= nlg n <= 1. Proof. intros n. unfold nlg. destruct (Z.ltb_spec 64512 n); lia. Qed.

Section BpIface.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Abbreviation RFS := (as_RFS H).  Abbreviation FSB := (as_FSB H).

  Definition stack_malloc_stmt_bp (k entry : Z) : Prop :=
    if Z.eqb k 5 then True else
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LF : list fframe) (lo : Z),
      RFS LF m -> (length LF < AFS_MAXLIVE_BP)%nat ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AFS_STACK ->
      mem_inv asegs m -> tp = Z_to_bv 64 ATP -> ACONST m -> athr_cells m ->
      evt asegs (stack_malloc_post H k ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LF lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

  Definition stack_malloc_sz_post (k : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LF : list fframe) (lo sz : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (ff fp : Z) junk1 junk2,
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ff) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - AFS_STACK, bv_unsigned sp); (FSB, FSB + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz k); (sh ff, sh ff + fshn k)]%Z m m'
      /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ RFS ((k, ff, fp) :: LF) m'
      /\ rw_cells asegs m' ff [CB 24 junk1; C8 sp; CB (Z.to_nat (fsz k - 40)) junk2; C8 (Z_to_bv 64 fp)]
      /\ SHAD m' ff (poison_bytes (Z.to_nat (sz / 8)) 0)
      /\ rw_cells asegs m' fp [C1 (b8 1)]
      /\ ACONST m'.

  Definition stack_malloc_sz_stmt (k entry : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LF : list fframe) (lo sz : Z),
      a0 = Z_to_bv 64 sz -> 0 < sz <= fsz k -> sz mod 8 = 0 ->
      RFS LF m -> (length LF < AFS_MAXLIVE_BP)%nat ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AFS_STACK ->
      mem_inv asegs m -> tp = Z_to_bv 64 ATP -> ACONST m -> athr_cells m ->
      evt asegs (stack_malloc_sz_post k ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LF lo sz m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

  Definition stack_free_post (k : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LF : list fframe) (ff fp nsh_ret lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - AFS_STACK, bv_unsigned sp); (fp, fp + 1); (sh ff, sh ff + nsh_ret)]%Z m m'
      /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ RFS (lf_remove ff LF) m'
      /\ SHAD m' ff (poison_bytes (Z.to_nat nsh_ret) 0xf5)
      /\ ACONST m'.

  Definition stack_free_stmt (k entry : Z) : Prop :=
    if Z.eqb k 5 then True else
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LF : list fframe) (ff fp lo : Z),
      RFS LF m -> In (k, ff, fp) LF -> a0 = Z_to_bv 64 ff ->
      rw_cells asegs m (ff + fsz k - 8) [C8 (Z_to_bv 64 fp)] ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AFS_STACK ->
      mem_inv asegs m -> ACONST m ->
      evt asegs (stack_free_post k ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LF ff fp (fshn k) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

  Definition stack_free_sz_stmt (k entry : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LF : list fframe) (ff fp lo sz : Z),
      RFS LF m -> In (k, ff, fp) LF -> a0 = Z_to_bv 64 ff ->
      rw_cells asegs m (ff + fsz k - 8) [C8 (Z_to_bv 64 fp)] ->
      a1 = Z_to_bv 64 sz -> 0 < sz <= fsz k -> sz mod 8 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AFS_STACK ->
      mem_inv asegs m -> ACONST m ->
      evt asegs (stack_free_post k ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LF ff fp (sz / 8) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

  Definition asan_rt_hyps_bp_ext : Prop :=
       stack_malloc_stmt_bp 0 AFS_MALLOC_0 /\ stack_malloc_stmt_bp 2 AFS_MALLOC_2 /\ stack_malloc_stmt_bp 3 AFS_MALLOC_3
    /\ stack_malloc_stmt_bp 5 AFS_MALLOC_5 /\ stack_malloc_stmt_bp 6 AFS_MALLOC_6
    /\ stack_malloc_sz_stmt 8 AFS_MALLOC_8
    /\ stack_free_stmt 5 AFS_FREE_5 /\ stack_free_stmt 6 AFS_FREE_6 /\ stack_free_sz_stmt 8 AFS_FREE_8
    /\ set_shadow_stmt 0x00 ASET_SHADOW_00 /\ set_shadow_stmt 0xf8 ASET_SHADOW_F8.

  Definition alloc_ok_of_live_bp : Prop :=
    forall s LB m n, as_RHEAP H s LB m -> 0 <= n ->
      lb_small LB + nsmall n <= RT_SMALL_MAX -> Z.of_nat (length LB) + 1 <= RT_CNT_MAX -> nlarge LB + nlg n <= RT_LARGE_MAX ->
      as_alloc_ok H s LB n.

  Definition RHEAP_ahm : Prop :=
    forall s LB m, as_RHEAP H s LB m -> exists TB : Z,
         rw_cells asegs m 0x190888 [C8 (Z_to_bv 64 TB)] /\ 4096 <= TB /\ TB mod 4096 = 0 /\ TB + 0x38e000 <= aceil
      /\ aapp TB 0x38e000
      /\ rw_cells asegs m (TB + 0x1e34f8) [CB 96 (repeat (b8 0) 96)] /\ rw_cells asegs m (TB + 0x2cf448) [CB 96 (repeat (b8 0) 96)].

  Definition cc_gen (len mid : Z) : list byte := shadow_of mid ++ poison_bytes (Z.to_nat (nsh len - nsh mid)) 0xfc.
  Lemma cc_gen_full : forall len, cc_gen len len = shadow_of len.
  Proof. intros len. unfold cc_gen. rewrite Z.sub_diag. cbn [Z.to_nat poison_bytes repeat]. apply app_nil_r. Qed.
  Lemma cc_gen_length : forall len mid, 0 <= mid <= len -> Z.of_nat (length (cc_gen len mid)) = nsh len.
  Proof.
    intros len mid H0. unfold cc_gen, poison_bytes. rewrite length_app, repeat_length, Nat2Z.inj_add, shadow_of_length by lia.
    assert (nsh mid <= nsh len) by (unfold nsh; apply Z.div_le_mono; lia). lia.
  Qed.
  Definition annotate_gen_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (beg len oldmid newmid : Z) (lo : Z),
      a0 = Z_to_bv 64 beg -> a1 = Z_to_bv 64 (beg + len) -> a2 = Z_to_bv 64 (beg + oldmid) -> a3 = Z_to_bv 64 (beg + newmid) ->
      beg mod 8 = 0 -> 0 <= len <= 2^40 -> 0 <= oldmid <= len -> 0 <= newmid <= len ->
      aapp beg len -> beg + len <= AAPP_HI ->
      SHAD m beg (cc_gen len oldmid) ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AINTRIN_STACK ->
      mem_inv asegs m -> ACONST m ->
      in_app_mem beg (beg + len) ->
      evt asegs (fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m' (seg_rom asegs)
          /\ munch [(sh beg, sh beg + nsh len); (bv_unsigned sp - AINTRIN_STACK, bv_unsigned sp)]%Z m m'
          /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
          /\ SHAD m' beg (cc_gen len newmid)
          /\ ACONST m')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AANNOTATE_CC) fc None m (seg_rom asegs)).

  Definition ICM (n : Z) : Z := if n <=? 64512 then 0 else 4 * n.
  Definition cost_bp : Prop := (forall n, as_Cf H n = 0) /\ (forall n, as_Cm H n = ICM n).
  Lemma ICM_small : forall n, n <= 64512 -> ICM n = 0.
  Proof. intros n Hn. unfold ICM. destruct (Z.leb_spec n 64512); [reflexivity| lia]. Qed.

  Definition asan_rt_hyps_bp : Prop :=
    asan_rt_hyps H /\ asan_rt_hyps_bp_ext /\ alloc_ok_of_live_bp /\ RHEAP_ahm /\ annotate_gen_stmt /\ cost_bp.
  Lemma rt_bp_base : asan_rt_hyps_bp -> asan_rt_hyps H.          Proof. intros X. apply X. Qed.
  Lemma rt_bp_ext : asan_rt_hyps_bp -> asan_rt_hyps_bp_ext.       Proof. intros X. apply X. Qed.
  Lemma rt_bp_live : asan_rt_hyps_bp -> alloc_ok_of_live_bp.      Proof. intros X. apply X. Qed.

  Lemma rt_bp_annot : asan_rt_hyps_bp -> annotate_gen_stmt.       Proof. intros X. apply X. Qed.
  Lemma rt_bp_cost : asan_rt_hyps_bp -> cost_bp.                  Proof. intros X. apply X. Qed.

  Lemma stack_malloc_bp_of_donor : forall k entry, stack_malloc_stmt H k entry -> stack_malloc_stmt_bp k entry.
  Proof.
    intros k entry S. unfold stack_malloc_stmt_bp. destruct (Z.eqb k 5); [exact I|].
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m LF lo.
    intros R LEN. apply S; [exact R| unfold AFS_MAXLIVE, AFS_MAXLIVE_BP in *; lia].
  Qed.
End BpIface.
