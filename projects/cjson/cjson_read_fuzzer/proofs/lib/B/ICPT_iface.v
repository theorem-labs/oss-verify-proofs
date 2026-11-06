(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_iface AShadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AMEMCHR_T : Z := 0x42514.          (* [comment removed for export] *)
Definition AMEMCPY_ICPT : Z := 0x53b38.       (* [comment removed for export] *)
Definition AMEMSET_ICPT : Z := 0x53848.       (* [comment removed for export] *)
Definition AMEMMOVE_ICPT : Z := 0.            (* [comment removed for export] *)
Definition AMEMCHR_ICPT : Z := 0x44204.
Definition ASTRLEN_ICPT : Z := 0x42598.       (* [comment removed for export] *)
Definition ASTRNCMP_ICPT : Z := 0x42ff8.      (* [comment removed for export] *)
Definition AREGION_POISONED : Z := 0x56030.   (* [comment removed for export] *)
Definition AMEM_IS_ZERO : Z := 0x65d8c.       (* [comment removed for export] *)
Definition AMEMTOSHADOW : Z := 0x55ba4.       (* [comment removed for export] *)
Definition AMEMTOSHADOW_FS : Z := 0x3d7dc.
Definition APOISON_SHADOW : Z := 0x556a8.     (* [comment removed for export] *)
Definition ATRY_INIT : Z := 0x5b4c4.          (* [comment removed for export] *)
Definition AASAN_INITED_FN : Z := 0x5a5b4.    (* [comment removed for export] *)
Definition A_MUSL_MEMCHR : Z := 0x9a874.
Definition A_REAL_STRLEN_SLOT : Z := 0xa3408.
Definition A_REAL_MEMCHR_SLOT : Z := 0xa3430.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition icpt_cells (m : word -> option byte) : Prop :=
  shbase_cells m                                                     (* [comment removed for export] *)
  /\ ro_cells bsegs m 0xa1708 [C8 (Z_to_bv 64 0xaa6a8)]            (* [comment removed for export] *)
  /\ ro_cells bsegs m 0xaa6a8 [C8 (Z_to_bv 64 0)]
  /\ ro_cells bsegs m 0xa1710 [C8 (Z_to_bv 64 0xaa6b0)]            (* [comment removed for export] *)
  /\ ro_cells bsegs m 0xaa6b0 [C8 (Z_to_bv 64 0)]
  /\ ro_cells bsegs m 0xa1718 [C8 (Z_to_bv 64 0xaa6a0)]            (* [comment removed for export] *)
  /\ ro_cells bsegs m 0xaa6a0 [C8 (Z_to_bv 64 0x7fffffffffff)]
  /\ ro_cells bsegs m 0xa2268 [C8 (Z_to_bv 64 0xaa699)]            (* [comment removed for export] *)
  /\ ro_cells bsegs m 0xaa698 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]  (* [comment removed for export] *)
  /\ ro_cells bsegs m 0xa16f0 [C8 (Z_to_bv 64 0x13b4e8)]            (* [comment removed for export] *)
  /\ ro_cells bsegs m 0x13b5dd [C1 (Z_to_bv 8 0)]                     (* [comment removed for export] *)
  /\ ro_cells bsegs m 0x13b5e3 [C1 (Z_to_bv 8 1)]                     (* [comment removed for export] *)
  /\ ro_cells bsegs m 0xa3580 [C8 (Z_to_bv 64 0x9a970)]             (* [comment removed for export] *)
  /\ ro_cells bsegs m 0xa3588 [C8 (Z_to_bv 64 0x9ad74)]             (* [comment removed for export] *)
  /\ ro_cells bsegs m 0xa3408 [C8 (Z_to_bv 64 0x9afc0)]             (* [comment removed for export] *)
  /\ ro_cells bsegs m 0xa3430 [C8 (Z_to_bv 64 0x9a874)].            (* [comment removed for export] *)

(* [comment removed for export] *)
Definition icpt_cell_ivs : list (Z * Z) :=
  [(0xa16f0, 0xa1720); (0xa2268, 0xa2270); (0xa3408, 0xa3410); (0xa3430, 0xa3438);
   (0xa3580, 0xa3590); (0xa99b8, 0xa99c0); (0xaa698, 0xaa6b8); (0x13b4e8, 0x13b608)].

Lemma disjoint_from_sub : forall W a n lo k,
  disjoint_from W lo k -> lo <= a -> a + n <= lo + k -> disjoint_from W a n.
Proof.
  induction W as [|[u v] W IH]; cbn; intros a n lo k HD Ha Hn; [exact I|].
  destruct HD as [HD1 HD2]. split; [lia|]. eapply IH; eauto.
Qed.

Lemma icpt_cells_munch : forall W m m',
  icpt_cells m -> munch W m m' ->
  Forall (fun iv => disjoint_from W (fst iv) (snd iv - fst iv)) icpt_cell_ivs ->
  icpt_cells m'.
Proof.
  intros W m m' IC MU D. unfold icpt_cell_ivs in D.
  pose proof (proj1 (Forall_forall _ _) D) as DF. cbn [fst snd] in DF.
  assert (D20 : disjoint_from W 0xa16f0 0x30) by (apply (DF (0xa16f0, 0xa1720)); cbn; tauto).
  assert (D99 : disjoint_from W 0xa2268 8) by (apply (DF (0xa2268, 0xa2270)); cbn; tauto).
  assert (D28 : disjoint_from W 0xa3408 8) by (apply (DF (0xa3408, 0xa3410)); cbn; tauto).
  assert (DC0 : disjoint_from W 0xa3430 8) by (apply (DF (0xa3430, 0xa3438)); cbn; tauto).
  assert (D58 : disjoint_from W 0xa3580 16) by (apply (DF (0xa3580, 0xa3590)); cbn; tauto).
  assert (D80 : disjoint_from W 0xa99b8 8) by (apply (DF (0xa99b8, 0xa99c0)); cbn; tauto).
  assert (D60 : disjoint_from W 0xaa698 0x20) by (apply (DF (0xaa698, 0xaa6b8)); cbn; tauto).
  assert (DCF : disjoint_from W 0x13b4e8 0x120) by (apply (DF (0x13b4e8, 0x13b608)); cbn; tauto).
  destruct IC as (SB & G38 & K70 & G40 & K78 & G48 & K68 & G99 & INI & G20 & CF245 & CF251 & RMC & RMS & RSL & RMCH).
  unfold icpt_cells.
  Ltac tr H D := eapply ro_cells_transport; [exact H| eassumption| eapply disjoint_from_sub; [exact D| cbn; lia| cbn; lia]].
  split. { eapply shbase_cells_munch; [exact SB| exact MU| eapply disjoint_from_sub; [exact D20| cbn; lia| cbn; lia]
                                      | eapply disjoint_from_sub; [exact D80| cbn; lia| cbn; lia]]. }
  split; [tr G38 D20|]. split; [tr K70 D60|]. split; [tr G40 D20|]. split; [tr K78 D60|].
  split; [tr G48 D20|]. split; [tr K68 D60|]. split; [tr G99 D99|]. split; [tr INI D60|].
  split; [tr G20 D20|]. split; [tr CF245 DCF|]. split; [tr CF251 DCF|].
  split; [tr RMC D58|]. split; [tr RMS D58|]. split; [tr RSL D28|]. tr RMCH DC0.
Qed.

(* [comment removed for export] *)
Definition lowmem_range (a n : Z) : Prop := 0 <= a /\ 0 <= n /\ a + n <= KLOWSHADOW_BEG.
Definition highmem_range (a n : Z) : Prop := KHIGHMEM_BEG <= a /\ 0 <= n /\ a + n + 8 <= KHIGHMEM_END.
Definition app_range (a n : Z) : Prop := lowmem_range a n \/ highmem_range a n.

(* [comment removed for export] *)
Definition addr_in_mem (p : Z) : Prop := (0 <= p <= 0x7fff7fff) \/ (KHIGHMEM_BEG <= p <= KHIGHMEM_END).

Lemma app_range_sub : forall a n a' n', app_range a n -> a <= a' -> 0 <= n' -> a' + n' <= a + n -> app_range a' n'.
Proof. intros a n a' n' [H|H] H1 H2 H3; [left|right]; unfold lowmem_range, highmem_range in *; lia. Qed.

Lemma app_range_lt47 : forall a n, app_range a n -> 0 <= a /\ a + n < 2^47.
Proof. intros a n [H|H]; unfold lowmem_range, highmem_range, SHADOW_OFFSET, KLOWSHADOW_BEG, KHIGHMEM_BEG, KHIGHMEM_END in *; lia. Qed.

(* [comment removed for export] *)
Lemma ablk_app_range : forall lo hi a n, ablk lo hi -> lo <= a -> 0 <= n -> a + n <= hi -> app_range a n.
Proof.
  intros lo hi a n [[H1 H2]|[H1 H2]] Ha Hn Hh; [left|right]; unfold lowmem_range, highmem_range.
  - unfold AIMG_HI in H1. lia.
  - pose proof alloc_ceiling_range as R. unfold KHIGHMEM_END. lia.
Qed.
(* [comment removed for export] *)
Lemma art_block_app_range : forall (AI : art_iface) sp0 SPB LB LF TRS B m mo g A n a k,
  ART AI sp0 SPB LB LF TRS B m mo g -> In (A, n) LB -> A <= a -> 0 <= k -> a + k <= A + Z.max n 1 -> app_range a k.
Proof.
  intros AI sp0 SPB LB LF TRS B m mo g A n a k HL IN H1 H2 H3.
  eapply ablk_app_range; [exact (art_block_band AI _ _ _ _ _ _ _ _ _ _ _ HL IN)| exact H1| exact H2| exact H3].
Qed.
Lemma art_frame_app_range : forall (AI : art_iface) sp0 SPB LB LF TRS B m mo g Fr k0 a k,
  ART AI sp0 SPB LB LF TRS B m mo g -> In (Fr, k0) LF -> Fr <= a -> 0 <= k -> a + k <= Fr + fsz k0 -> app_range a k.
Proof.
  intros AI sp0 SPB LB LF TRS B m mo g Fr k0 a k HL IN H1 H2 H3.
  eapply ablk_app_range; [exact (art_frame_band AI _ _ _ _ _ _ _ _ _ _ _ HL IN)| exact H1| exact H2| exact H3].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition memtoshadow_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p : Z),
  icpt_cells m -> mem_inv bsegs m ->
  a0 = Z_to_bv 64 p -> addr_in_mem p ->
  evt bsegs (fun ms' => exists a1' a2' a3' a4' a5' a6' a7' t0',
      ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 (SH p)) a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m (seg_rom bsegs)
      /\ munch [] m m /\ wmono bsegs m m /\ mem_inv bsegs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AMEMTOSHADOW) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
Definition mem_is_zero_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).

Definition mem_is_zero_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b n lo : Z),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp ->
  a0 = Z_to_bv 64 b -> a1 = Z_to_bv 64 n -> 0 < n <= 2^40 ->
  bytes_at bsegs m b (repeat (Z_to_bv 8 0) (Z.to_nat n)) -> b + n + 16 <= 2^64 ->
  (b + n <= bv_unsigned sp - 16 \/ bv_unsigned sp <= b) ->
  evt bsegs (mem_is_zero_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AMEM_IS_ZERO) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
Definition region_is_poisoned_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).

Definition region_is_poisoned_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b n lo : Z),
  icpt_cells m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 80 <= bv_unsigned sp ->
  a0 = Z_to_bv 64 b -> a1 = Z_to_bv 64 n -> 0 < n < 2^40 ->
  app_range b n -> shadow_ok m b n ->
  evt bsegs (region_is_poisoned_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AREGION_POISONED) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition wr_range_ok (d n : Z) : Prop :=
  Forall (fun iv => d + n <= fst iv \/ snd iv <= d) icpt_cell_ivs.

Lemma wr_range_ok_high : forall d n, 0x1e4000 <= d -> wr_range_ok d n.
Proof. intros d n H. unfold wr_range_ok, icpt_cell_ivs. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. Qed.

(* [comment removed for export] *)
Lemma icpt_cells_munch_wr : forall m m' d n a b,
  icpt_cells m -> munch [(d, d + n); (a, b)] m m' -> wr_range_ok d n -> 0x1e4000 <= a -> icpt_cells m'.
Proof.
  intros m m' d n a b IC MU WR Ha. eapply icpt_cells_munch; [exact IC| exact MU|].
  unfold wr_range_ok in WR. unfold icpt_cell_ivs in *.
  repeat match type of WR with Forall _ (_ :: _) => apply Forall_cons_iff in WR; destruct WR as [? WR] end.
  cbn [fst snd] in *.
  repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
Qed.

(* [comment removed for export] *)
Definition memcpy_like_post (STK : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (d s n : Z) (src : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(d, d + n); (bv_unsigned sp - STK, bv_unsigned sp)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' d [CB (Z.to_nat n) src]
    /\ bytes_at bsegs m' s src
    /\ stk bsegs m' lo (bv_unsigned sp).

(* [comment removed for export] *)
Definition memset_like_post (STK : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (d c n : Z) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(d, d + n); (bv_unsigned sp - STK, bv_unsigned sp)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' d [CB (Z.to_nat n) (repeat (Z_to_bv 8 (c mod 256)) (Z.to_nat n))]
    /\ stk bsegs m' lo (bv_unsigned sp).

(* [comment removed for export] *)
Definition memcpy_contract (entry STK : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (d s n : Z) (src junk : list byte) (lo : Z),
  icpt_cells m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + STK <= bv_unsigned sp ->
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 n ->
  bytes_at bsegs m s src -> Z.of_nat (length src) = n ->
  rw_cells bsegs m d [CB (Z.to_nat n) junk] ->
  (s + n <= d \/ d + n <= s) ->
  n < 2^40 -> app_range s n -> app_range d n -> wr_range_ok d n ->
  (0 < n -> shadow_ok m s n) -> (0 < n -> shadow_ok m d n) ->
  (s + n <= lo \/ bv_unsigned sp <= s) -> (d + n <= lo \/ bv_unsigned sp <= d) ->
  evt bsegs (memcpy_like_post STK ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc d s n src lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom bsegs)).

Definition memset_contract (entry STK : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (d c n : Z) (junk : list byte) (lo : Z),
  icpt_cells m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + STK <= bv_unsigned sp ->
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 c -> a2 = Z_to_bv 64 n -> 0 <= c < 2^64 ->
  rw_cells bsegs m d [CB (Z.to_nat n) junk] ->
  0 <= n < 2^40 -> app_range d n -> wr_range_ok d n ->
  (0 < n -> shadow_ok m d n) ->
  (d + n <= lo \/ bv_unsigned sp <= d) ->
  evt bsegs (memset_like_post STK ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc d c n lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
Definition asan_memcpy_spec : Prop := memcpy_contract AASANMEMCPY AINTRIN_STACK.
(* [comment removed for export] *)
Definition asan_memset_spec : Prop := memset_contract AASANMEMSET AINTRIN_STACK.
(* [comment removed for export] *)
Definition memcpy_icpt_spec : Prop := memcpy_contract AMEMCPY_T AINTRIN_STACK.
(* [comment removed for export] *)
Definition memset_icpt_spec : Prop := memset_contract AMEMSET_T AINTRIN_STACK.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition strlen_icpt_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : Z) (str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length str))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - ASTRFN_STACK, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ bytes_at bsegs m' s (str ++ Z_to_bv 8 0 :: slack)
    /\ stk bsegs m' lo (bv_unsigned sp).

Definition strlen_icpt_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (s : Z) (str slack : list byte) (lo : Z),
  icpt_cells m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + ASTRFN_STACK <= bv_unsigned sp ->
  a0 = Z_to_bv 64 s ->
  bytes_at bsegs m s (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  (- (s + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  Z.of_nat (length str) + 1 < 2^40 ->
  app_range s (Z.of_nat (length str) + 1) ->
  shadow_ok m s (Z.of_nat (length str) + 1) ->
  (s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo \/ bv_unsigned sp <= s) ->
  evt bsegs (strlen_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ASTRLEN_T) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
Definition strncmp_icpt_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (x y : list byte) (n lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 (strncmp_spec (map bv_unsigned x) (map bv_unsigned y) (Z.to_nat n)))
                 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - ASTRFN_STACK, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).

Definition strncmp_icpt_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (x y : list byte) (p q n lo : Z),
  icpt_cells m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + ASTRFN_STACK <= bv_unsigned sp ->
  a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 q -> a2 = Z_to_bv 64 n -> 0 <= n < 2^40 ->
  let i := strncmp_stop (map bv_unsigned x) (map bv_unsigned y) (Z.to_nat n) in
  let r := Z.min (Z.of_nat i + 1) n in
  Z.of_nat (length x) = r -> Z.of_nat (length y) = r ->
  bytes_at bsegs m p x -> bytes_at bsegs m q y ->
  app_range p r -> app_range q r -> (0 < n -> shadow_ok m p r /\ shadow_ok m q r) ->
  (p + r <= lo \/ bv_unsigned sp <= p) -> (q + r <= lo \/ bv_unsigned sp <= q) ->
  evt bsegs (strncmp_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc x y n lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ASTRNCMP_T) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
Definition memchr_chk_len (s c n : Z) (buf : list byte) : Z :=
  let res := memchr_res s c n buf in if res =? 0 then n else res - s + 1.

Definition memchr_icpt_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s c n : Z) (buf : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (memchr_res s (c mod 256) n buf))
                 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - AINTRIN_STACK, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ bytes_at bsegs m' s buf
    /\ stk bsegs m' lo (bv_unsigned sp).

Definition memchr_icpt_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (s c n : Z) (buf : list byte) (lo : Z),
  icpt_cells m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + AINTRIN_STACK <= bv_unsigned sp ->
  a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 c -> a2 = Z_to_bv 64 n -> 0 <= c < 2^64 -> 0 <= n < 2^40 ->
  bytes_at bsegs m s buf ->
  memchr_ok s (c mod 256) n buf -> app_range s (Z.of_nat (length buf)) ->
  let len := memchr_chk_len s (c mod 256) n buf in
  (0 < len -> app_range s len /\ shadow_ok m s len) ->
  (s + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= s) ->
  evt bsegs (memchr_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s c n buf lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AMEMCHR_T) fc None m (seg_rom bsegs)).


End CeilWrap.
