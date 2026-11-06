(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/As/AllocWalkKit.v, with its module paths and module names changed; 353 of its 387 lines of code are new or changed and 128 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Tk/AW/SmLeaf.v, with its module paths, module names and addresses changed; 313 of its 517 lines of code are new or changed and 183 lines of the source are left out. *)
(* lib/B/Prog/asan_stack_mallocF_kit.v -- fuzz_ctrl image B (asan-ubsan): the class-independent part of the footprint
   (ExecF) walk of __asan_stack_malloc_{0,1,2}: lib/Lib cell helpers, the cells and footprint of the TLS callees, the
   callee walks (musl __tls_get_addr, TryAsanInitFromRtl, AsanTSDGet, GetCurrentThread, DTLS_on_tls_get_addr, the
   __tls_get_addr interceptor, MemToShadow) and shadow_stk_on.  The class files asan_stack_malloc_{0,1,2}F.v use it.
   rule 24: no function proved for the first time.  These walks are proved at the footprint level in fuzz_grant.

   DONOR.  a working branch dac1040b24ec, proofs/libreac/fuzz_grant/lib/B/Prog/asan_stack_mallocF.v
   lines 53-165 (imports, cell helpers, flag_readF) and 202-662 (leafF_cells .. m2sF_spec), the donor's own port of
   fuzz_pcap 78bd0706625 / fuzz_knock 9f8d2659177 (its header, lines 12-41).  The text is the donor's with these
   changes only:
   - the namespace fuzz_grant -> fuzz_ctrl;
   - the imports: the donor's asan_stack_mallocF_c (grant's canonical statement, the home of grant's IMG_HI) is not
     imported; IMG_LO / IMG_HI are this unit's lib/B/Prog/ImgBounds.v (0x10000 / 0x5fe000), which rng_asan.v exports.
     lib/B/ShadowRwOn.v is imported for shadow_stk_on;
   - `Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.` is `Local Unset` (settings v10);
   - not taken: rng_sh_frame0/1/2 (donor 166-200) and the probe loops LoopF0/1/2 (663-839), which are class-specific
     and are in the class files; the walks (843-1368) and their _F shapes (1369-1375);
   - new: shadow_stk_on, the region form of lib/B/Tk/AW/SmLib.v shadow_stk (its proof, with the region premise);
   - every image numeral relocated by symbol, fuzz_grant.asan-ubsan -> fuzz_ctrl.asan-ubsan of libreac v1.9.0
     (internal path, sha256 ee07e2c38d94...; raw MEASURE.md (a working note, not in this delivery) of a Theorem Labs lane):
       0x42518 -> 0x42af4   __wrap___tls_get_addr + 0           0x9e3b0 -> 0xa15d0  TLS_INDEX (.got, words 1, -2048)
       0x59b98 -> 0x5a174   TryAsanInitFromRtl + 0              0x9e3c0 -> 0xa15e0  DTLS_TPOFF (.got, word 8)
       0x97484 -> 0x99624   __tls_get_addr + 0                  0x9f470 -> 0xa2690  real___tls_get_addr + 0
       0x54ee4 -> 0x554c0   AsanTSDGet + 0                      0xa6658 -> 0xaa398  asan_inited + 0
       0x5c398 -> 0x5c974   GetCurrentThread + 0                0xa51e0 -> 0xa8f20  tsd_key_inited + 0
       0x69aac -> 0x6a088   DTLS_on_tls_get_addr + 0            0xa51e4 -> 0xa8f24  tsd_key + 0
       0x3d79c -> 0x3dd78   MemToShadow copy #2 + 0 (the jal at __asan_stack_malloc_0 + 0x12c targets it)
       0x9d6c0 -> 0xa08e0   GOT_CF (.got cell holding common_flags_dont_use)
       0x1374a8 -> 0x13b1e8 common_flags_dont_use + 0           0x137531 -> 0x13b271 common_flags_dont_use + 0x89
       0x9d720 -> 0xa0940   GOT_VERBOSITY (.got cell holding current_verbosity)
       0x135418 -> 0x139158 current_verbosity + 0
       0x9d6d0 -> 0xa08f0   .got cells holding __asan_shadow_memory_dynamic_address, kMidMemBeg, kMidMemEnd,
                            kHighMemEnd (MemToShadow's auipc at + 0 reads it)
       0xa5978 -> 0xa96b8   __asan_shadow_memory_dynamic_address    0xa6660 -> 0xaa3a0  kHighMemEnd
       0xa6668 -> 0xaa3a8   kMidMemBeg                              0xa6670 -> 0xaa3b0  kMidMemEnd
       0x5fb000 -> 0x5fe000 the image top (no symbol): ASAN_GT of asan_stack_malloc_c.v = ImgBounds.v IMG_HI
     The .got cells have no symbol: each is the same named constant of grant's and of this unit's
     asan_stack_malloc_c.v (TLS_INDEX, DTLS_TPOFF, GOT_CF, GOT_VERBOSITY) or the cell MemToShadow's own auipc names,
     and holds the same words / the same-named symbol in both images.  The callee code is the same in both images
     modulo pc-relative fields (EQUAL-mod-pcrel by comparison kit 86da41d3ef68, strictcmp3 65688e94214a, for every function above and
     __asan_stack_malloc_0).  The layout constants (0x7fff8000, 0x10007fff8000, 0x7fffffffffff, 0x800000000000,
     2147450879, 2147450880) are ASan's and stay.  Every relocated numeral equals the one this unit's plain walks
     lib/B/Tk/AW/SmLeaf.v / SmLib.v already use. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Fpu Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.AW Require Import SmLeaf SmLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import asan_stack_malloc_c rng_asan.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import StepF.
Local Unset Lia Cache. Local Unset Nia Cache. Local Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* ------------------------------------------------------------------ cells of lib.Lib

   lib/B/Tk/AW/{SmLeaf,SmLib}.v state their cell facts with the [cell] of lib/B/Tk/UL, a copy of lib/Lib's whose
   inductive type is a different one, so the ExecF walk below needs these few helpers in lib/Lib's own cells. *)

Lemma ro8F (m : word -> option byte) a v : bytes_at rsegs m a (le8 v) -> ro_cells rsegs m a [C8 v].
Proof. intros H. split; [exact (conj I I)|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H. Qed.

Lemma ro4F (m : word -> option byte) a v : bytes_at rsegs m a (le4 v) -> ro_cells rsegs m a [C4 v].
Proof. intros H. split; [exact (conj I I)|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H. Qed.

Lemma ro1F (m : word -> option byte) a b : bytes_at rsegs m a [b] -> ro_cells rsegs m a [C1 b].
Proof. intros H. split; [exact (conj I I)|]. cbn [cells_bytes cbytes app]. exact H. Qed.

Lemma ro_cons8F (m : word -> option byte) a v cs :
  bytes_at rsegs m a (le8 v) -> ro_cells rsegs m (a + 8) cs -> ro_cells rsegs m a (C8 v :: cs).
Proof.
  intros H [W B]. split; [exact (conj I W)|]. cbn [cells_bytes cbytes].
  apply (proj2 (bytes_at_app rsegs m a (le8 v) (cells_bytes cs))). split; [exact H|]. rewrite length_le8. exact B.
Qed.

Lemma ro_boundF (m : word -> option byte) a cs : ro_cells rsegs m a cs -> 0 <= a /\ a + Z.of_nat (cells_size cs) <= 2^64.
Proof. intros [W B]. apply bytes_at_bound in B. rewrite cells_bytes_length in B by exact W. exact B. Qed.

Lemma stk_rwF (m : word -> option byte) lo hi A cs : stk rsegs m lo hi -> ro_cells rsegs m A cs -> lo <= A ->
  A + Z.of_nat (cells_size cs) <= hi -> rw_cells rsegs m A cs.
Proof.
  intros (S0 & S1 & S) R H1 H2. split; [exact R|].
  pose proof (ro_boundF _ _ _ R) as B.
  split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (S (A + i) ltac:(lia))).
Qed.

Lemma stk_junkF (m : word -> option byte) lo hi A (n : nat) : stk rsegs m lo hi -> lo <= A -> A + Z.of_nat n <= hi ->
  exists bs, rw_cells rsegs m A [CB n bs].
Proof.
  intros S H1 H2. destruct (stk_split rsegs m lo (A + Z.of_nat n) hi S ltac:(lia)) as [S1 _].
  destruct (stk_carve rsegs m lo (A + Z.of_nat n) n S1 ltac:(lia)) as [_ (bs & R)].
  replace (A + Z.of_nat n - Z.of_nat n) with A in R by lia. exists bs. exact R.
Qed.

Lemma stk_subF (m : word -> option byte) lo hi a b : stk rsegs m lo hi -> lo <= a -> a <= b -> b <= hi ->
  stk rsegs m a b.
Proof.
  intros S H1 H2 H3. destruct (stk_split rsegs m lo a hi S ltac:(lia)) as [_ S1].
  destruct (stk_split rsegs m a b hi S1 ltac:(lia)) as [S2 _]. exact S2.
Qed.

Lemma rw_c8_bytesF (m : word -> option byte) A v : rw_cells rsegs m A [C8 v] -> bytes_at rsegs m A (le8 v).
Proof. intros [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B. Qed.

Lemma rw_c1_bytesF (m : word -> option byte) A b : rw_cells rsegs m A [C1 b] -> bytes_at rsegs m A [b].
Proof. intros [[_ B] _]. exact B. Qed.

Lemma le8_zeroF : le8 (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) 8.
Proof.
  first [ reflexivity | vm_compute; reflexivity
        | unfold le8; cbn; repeat (apply f_equal2; [apply bv_eq; vm_compute; reflexivity|]); reflexivity ].
Qed.

Lemma cells_bytes_zeroF n : cells_bytes (repeat (C8 (Z_to_bv 64 0)) n) = repeat (Z_to_bv 8 0) (8 * n).
Proof.
  induction n as [|n IH]; [reflexivity|]. cbn [repeat cells_bytes cbytes]. rewrite IH, le8_zeroF.
  replace (8 * S n)%nat with (8 + 8 * n)%nat by lia. rewrite repeat_app. reflexivity.
Qed.

Lemma rw_zero_cellsF (m : word -> option byte) A n : rw_cells rsegs m A (repeat (C8 (Z_to_bv 64 0)) n) ->
  bytes_at rsegs m A (repeat (Z_to_bv 8 0) (8 * n)).
Proof. intros [[_ B] _]. rewrite cells_bytes_zeroF in B. exact B. Qed.

Lemma swrap32_smallF : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma mrd_read1F (m : word -> option byte) x b : mrd rsegs m (wa x) = Some b -> 0 <= x -> x + 1 <= 2^64 ->
  ov_read_bytes rsegs m (wa x) 1 = Some [b].
Proof.
  intros H H0 H1.
  assert (B : bytes_at rsegs m x [b]).
  { split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. assert (i = 0)%nat as -> by lia. cbn.
    rewrite Z.add_0_r. exact H. }
  pose proof (bytes_at_ov_read rsegs m x [b] 0 1 B ltac:(cbn; lia)) as R.
  cbn [firstn skipn] in R. rewrite Nat2Z.inj_0, Z.add_0_r in R. exact R.
Qed.

(* One flag byte of the class's flag array, as the read the walk needs (lib/B/Tk/AW/SmLib.v flag_read). *)
Lemma flag_readF (m : word -> option byte) A (flags : list byte) pos : bytes_at rsegs m A flags ->
  0 <= pos < Z.of_nat (length flags) -> Forall (fun b => b = Z_to_bv 8 0 \/ b = Z_to_bv 8 1) flags ->
  exists b, nth_error flags (Z.to_nat pos) = Some b /\ (b = Z_to_bv 8 0 \/ b = Z_to_bv 8 1)
    /\ ov_read_bytes rsegs m (wa (A + pos)) 1 = Some [b].
Proof.
  intros (B0 & B1 & B) Hp F01.
  destruct (nth_error flags (Z.to_nat pos)) as [b|] eqn:E.
  2:{ apply nth_error_None in E. lia. }
  exists b. split; [reflexivity|]. split.
  - rewrite Forall_forall in F01. apply F01. eapply nth_error_In. exact E.
  - apply mrd_read1F; [| lia | lia]. pose proof (B (Z.to_nat pos) ltac:(lia)) as R.
    rewrite Z2Nat.id in R by lia. rewrite R. exact E.
Qed.


(* ------------------------------------------------------------------ the cells of the TLS callees *)

(* The cells the __tls_get_addr wrapper and its callees read, in lib/Lib's cells (lib/B/Tk/AW/SmLeaf.v leaf_cells). *)
Definition leafF_cells (TP DT TS C T DB k : Z) (tb te : word) (m : word -> option byte) : Prop :=
  ro_cells rsegs m 0xa15d0 [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 (2^64 - 2048))]
  /\ ro_cells rsegs m (TP + -8) [C8 (Z_to_bv 64 DT)]
  /\ ro_cells rsegs m (DT + 8) [C8 (Z_to_bv 64 (TP + 2048))]
  /\ ro_cells rsegs m 0xaa398 [C1 (Z_to_bv 8 1)]
  /\ ro_cells rsegs m 0xa8f20 [C1 (Z_to_bv 8 1)]
  /\ ro_cells rsegs m 0xa8f24 [C4 (Z_to_bv 64 k)]
  /\ ro_cells rsegs m (TP + -88) [C8 (Z_to_bv 64 TS)]
  /\ ro_cells rsegs m (TS + 8 * k) [C8 (Z_to_bv 64 C)]
  /\ ro_cells rsegs m (C + 152) [C8 (Z_to_bv 64 T)]
  /\ ro_cells rsegs m (T + 48) [C8 tb; C8 te]
  /\ ro_cells rsegs m 0xa2690 [C8 (Z_to_bv 64 0x99624)]
  /\ ro_cells rsegs m 0xa08e0 [C8 (Z_to_bv 64 0x13b1e8)]
  /\ ro_cells rsegs m 0x13b271 [C1 (Z_to_bv 8 1)]
  /\ ro_cells rsegs m 0xa0940 [C8 (Z_to_bv 64 0x139158)]
  /\ ro_cells rsegs m 0x139158 [C4 (Z_to_bv 64 0)]
  /\ ro_cells rsegs m 0xa15e0 [C8 (Z_to_bv 64 8)]
  /\ ro_cells rsegs m (TP + 8) [C8 (Z_to_bv 64 DB)]
  /\ ro_cells rsegs m (DB + 24) [C8 (Z_to_bv 64 TP)]
  /\ (88 <= TP /\ TP + 16 <= 2^64 /\ 0 <= DT /\ DT + 16 <= 2^64 /\ 0 <= k < 2^32
      /\ 0 <= TS /\ TS + 8 * k + 8 <= 2^64 /\ 0 <= C /\ C + 160 <= 2^64 /\ 0 <= T /\ T + 64 <= 2^64
      /\ 0 < DB /\ DB + 32 <= 2^64).

Definition leaf_ivsF (TP DT TS C T DB k : Z) : list (Z * Z) :=
  [(TP - 88, TP - 80); (TP - 8, TP + 16); (DT + 8, DT + 16); (TS + 8 * k, TS + 8 * k + 8);
   (C + 152, C + 160); (T + 48, T + 64); (DB + 24, DB + 32)].

Definition leaf_apartF (TP DT TS C T DB k lo hi : Z) : Prop :=
  0x5fe000 <= lo /\ lo <= hi /\ hi <= 2^64 /\ disjoint_from (leaf_ivsF TP DT TS C T DB k) lo (hi - lo).

Lemma Forall_disjF (W : list (Z * Z)) lo hi a n : Forall (fun iv => lo <= fst iv /\ snd iv <= hi) W ->
  a + n <= lo \/ hi <= a -> disjoint_from W a n.
Proof. intros F H. induction F as [|[wl wh] W' Hx F IH]; cbn in *; [exact I|]. split; [lia| exact IH]. Qed.

Lemma leaf_cells_munchF TP DT TS C T DB k tb te m m' W lo hi :
  leafF_cells TP DT TS C T DB k tb te m -> munch W m m' -> leaf_apartF TP DT TS C T DB k lo hi ->
  Forall (fun iv => lo <= fst iv /\ snd iv <= hi) W -> leafF_cells TP DT TS C T DB k tb te m'.
Proof.
  intros LC MU (A0 & A1 & A2 & D) FA. unfold leaf_ivsF in D. cbn [disjoint_from] in D.
  destruct D as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & _).
  unfold leafF_cells in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with |- _ /\ _ => split end; try assumption.
  all: try (eapply ro_cells_transport; [eassumption| exact MU| apply (Forall_disjF W lo hi); [exact FA|]]).
  all: cbv [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
  all: first [ left; lia
             | destruct D1 as [X|X]; [right|left]; lia
             | destruct D2 as [X|X]; [right|left]; lia
             | destruct D3 as [X|X]; [right|left]; lia
             | destruct D4 as [X|X]; [right|left]; lia
             | destruct D5 as [X|X]; [right|left]; lia
             | destruct D6 as [X|X]; [right|left]; lia
             | destruct D7 as [X|X]; [right|left]; lia ].
Qed.

Lemma leaf_apart_subF TP DT TS C T DB k lo hi lo' hi' :
  leaf_apartF TP DT TS C T DB k lo hi -> lo <= lo' -> lo' <= hi' -> hi' <= hi ->
  leaf_apartF TP DT TS C T DB k lo' hi'.
Proof.
  intros (A0 & A1 & A2 & D) H1 H2 H3. split; [lia|]. split; [lia|]. split; [lia|].
  unfold leaf_ivsF in *. cbn [disjoint_from] in *. repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat split; lia.
Qed.

Lemma tls_leafF (m : word -> option byte) TP DT TS C T DB k : asan_cells m -> asan_tls_cells m TP DT TS C T DB k ->
  exists tb te, leafF_cells TP (bv_unsigned DT) (bv_unsigned TS) (bv_unsigned C) (bv_unsigned T) (bv_unsigned DB) k tb te m.
Proof.
  intros (_ & _ & INI & _).
  intros (H1 & H2 & H3 & H4 & H5 & Hk & H7 & H8 & H9 & H10 & (tb & te & H11) & H12 & H13 & H14 & H15 & H16 & H17 & HDB & H19).
  exists tb, te.
  assert (R1 : ro_cells rsegs m 0xa15d0 [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 (2^64 - 2048))]).
  { replace (Z_to_bv 64 (2^64 - 2048)) with (Z_to_bv 64 (-2048)) by (apply bv_eq; vm_compute; reflexivity).
    pose proof (H1 : bytes_at rsegs m 0xa15d0 (le8 (Z_to_bv 64 1) ++ le8 (Z_to_bv 64 (-2048)))) as B.
    apply (proj1 (bytes_at_app rsegs m _ _ _)) in B as [B1 B2]. rewrite length_le8 in B2.
    apply ro_cons8F; [exact B1|]. apply ro8F. exact B2. }
  assert (R2 : ro_cells rsegs m (TP + -8) [C8 (Z_to_bv 64 (bv_unsigned DT))]) by (rewrite Z_to_bv_lit_self; apply ro8F; exact H3).
  assert (R3 : ro_cells rsegs m (bv_unsigned DT + 8) [C8 (Z_to_bv 64 (TP + 2048))]) by (apply ro8F; exact H4).
  assert (R4 : ro_cells rsegs m 0xaa398 [C1 (Z_to_bv 8 1)]) by (apply ro1F; exact INI).
  assert (R5 : ro_cells rsegs m 0xa8f20 [C1 (Z_to_bv 8 1)]) by (apply ro1F; exact H5).
  assert (R6 : ro_cells rsegs m 0xa8f24 [C4 (Z_to_bv 64 k)]) by (apply ro4F; exact H7).
  assert (R7 : ro_cells rsegs m (TP + -88) [C8 (Z_to_bv 64 (bv_unsigned TS))]) by (rewrite Z_to_bv_lit_self; apply ro8F; exact H8).
  assert (R8 : ro_cells rsegs m (bv_unsigned TS + 8 * k) [C8 (Z_to_bv 64 (bv_unsigned C))]) by (rewrite Z_to_bv_lit_self; apply ro8F; exact H9).
  assert (R9 : ro_cells rsegs m (bv_unsigned C + 152) [C8 (Z_to_bv 64 (bv_unsigned T))]) by (rewrite Z_to_bv_lit_self; apply ro8F; exact H10).
  assert (R10 : ro_cells rsegs m (bv_unsigned T + 48) [C8 tb; C8 te]).
  { pose proof (H11 : bytes_at rsegs m (bv_unsigned T + 48) (le8 tb ++ le8 te)) as B.
    apply (proj1 (bytes_at_app rsegs m _ _ _)) in B as [B1 B2]. rewrite length_le8 in B2.
    apply ro_cons8F; [exact B1|]. apply ro8F. exact B2. }
  assert (R11 : ro_cells rsegs m 0xa2690 [C8 (Z_to_bv 64 0x99624)]) by (apply ro8F; exact H2).
  assert (R12 : ro_cells rsegs m 0xa08e0 [C8 (Z_to_bv 64 0x13b1e8)]) by (apply ro8F; exact H12).
  assert (R13 : ro_cells rsegs m 0x13b271 [C1 (Z_to_bv 8 1)]) by (apply ro1F; exact H13).
  assert (R14 : ro_cells rsegs m 0xa0940 [C8 (Z_to_bv 64 0x139158)]) by (apply ro8F; exact H14).
  assert (R15 : ro_cells rsegs m 0x139158 [C4 (Z_to_bv 64 0)]) by (apply ro4F; exact H15).
  assert (R16 : ro_cells rsegs m 0xa15e0 [C8 (Z_to_bv 64 8)]) by (apply ro8F; exact H16).
  assert (R17 : ro_cells rsegs m (TP + 8) [C8 (Z_to_bv 64 (bv_unsigned DB))]) by (rewrite Z_to_bv_lit_self; apply ro8F; exact H17).
  assert (R18 : ro_cells rsegs m (bv_unsigned DB + 24) [C8 (Z_to_bv 64 TP)]) by (apply ro8F; exact H19).
  pose proof (ro_boundF _ _ _ R2) as X2. pose proof (ro_boundF _ _ _ R3) as X3. pose proof (ro_boundF _ _ _ R7) as X7.
  pose proof (ro_boundF _ _ _ R8) as X8. pose proof (ro_boundF _ _ _ R9) as X9. pose proof (ro_boundF _ _ _ R10) as X10.
  pose proof (ro_boundF _ _ _ R17) as X17. pose proof (ro_boundF _ _ _ R18) as X18.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in X2, X3, X7, X8, X9, X10, X17, X18.
  pose proof (bv_unsigned_in_range 64 DT) as UDT. pose proof (bv_unsigned_in_range 64 TS) as UTS.
  pose proof (bv_unsigned_in_range 64 C) as UC. pose proof (bv_unsigned_in_range 64 T) as UT.
  pose proof (bv_unsigned_in_range 64 DB) as UDB.
  unfold bv_modulus in UDT, UTS, UC, UT, UDB. cbn in UDT, UTS, UC, UT, UDB.
  unfold leafF_cells. repeat (split; [eassumption|]). lia.
Qed.

(* The cells MemToShadow reads on its fast path (lib/B/Tk/AW/SmLeaf.v m2s_cells). *)
Definition m2sF_cells (m : word -> option byte) : Prop :=
  ro_cells rsegs m 0xa08f0 [C8 (Z_to_bv 64 0xa96b8); C8 (Z_to_bv 64 0xaa3a8); C8 (Z_to_bv 64 0xaa3b0); C8 (Z_to_bv 64 0xaa3a0)]
  /\ ro_cells rsegs m 0xa96b8 [C8 (Z_to_bv 64 0x7fff8000)]
  /\ ro_cells rsegs m 0xaa3a0 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

Lemma Forall_lo_disjF (W : list (Z * Z)) lo a n : Forall (fun iv => lo <= fst iv) W -> a + n <= lo ->
  disjoint_from W a n.
Proof. intros F H. induction F as [|[wl wh] W' Hx F IH]; cbn in *; [exact I|]. split; [lia| exact IH]. Qed.

Lemma m2s_cells_munchF m m' W : m2sF_cells m -> munch W m m' -> Forall (fun iv => 0x5fe000 <= fst iv) W ->
  m2sF_cells m'.
Proof.
  intros (K1 & K2 & K3) MU FA.
  split; [|split]; (eapply ro_cells_transport; [eassumption| exact MU| apply (Forall_lo_disjF W 0x5fe000); [exact FA| cbn; lia]]).
Qed.

Lemma m2s_of_asanF (m : word -> option byte) : asan_cells m -> m2sF_cells m.
Proof.
  intros (K1 & K2 & _ & _ & _ & _ & _ & _ & K9 & K10 & K11 & K12 & K13 & K14 & _).
  split; [|split].
  - apply ro_cons8F; [exact K2|]. apply ro_cons8F; [exact K12|]. apply ro_cons8F; [exact K14|]. apply ro8F. exact K10.
  - apply ro8F. exact K1.
  - apply ro_cons8F; [exact K9|]. apply ro_cons8F; [exact K11|]. apply ro8F. exact K13.
Qed.

(* ------------------------------------------------------------------ the footprint of the TLS callees *)

(* The regions the TLS chain reads: the image and the thread cells reached through tp. *)
Definition leaf_rng (RNG : footprint) (TP DT TS C T DB k : Z) : Prop :=
  rng RNG IMG_LO (IMG_HI - IMG_LO) /\ rng RNG (TP - 88) 8 /\ rng RNG (TP - 8) 24 /\ rng RNG (DT + 8) 8
  /\ rng RNG (TS + 8 * k) 8 /\ rng RNG (C + 152) 8 /\ rng RNG (T + 48) 16 /\ rng RNG (DB + 24) 8.

(* The statement's image range [IMG_LO, IMG_HI) as closed literals, the form the footprint tactics compare. *)
Ltac img_rng H := unfold IMG_LO, IMG_HI in H;
  lazymatch type of H with rng _ _ (?a - ?b) =>
    let v := eval vm_compute in (a - b) in change (a - b) with v in H end.

Ltac litsF H := repeat match type of H with context [Z.add ?a ?b] => is_Zlit a; is_Zlit b;
    let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v in H end.
Tactic Notation "leafcF" integer(k) hyp(LC) ident(H) :=
  pose proof LC as H; unfold leafF_cells in H; do k (apply proj2 in H);
  lazymatch type of H with _ /\ _ => apply proj1 in H | _ => idtac end; litsF H.
Ltac leafrF LC := let X := fresh "LR" in pose proof LC as X; unfold leafF_cells in X; do 18 (apply proj2 in X).

Ltac freshLCF H :=
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
    match goal with LC : leafF_cells ?a ?b ?c ?d ?e ?f ?g ?h ?i ?m0, MU : munch _ ?m0 mx,
                    AP : leaf_apartF _ _ _ _ _ _ _ ?lo ?hi |- _ =>
      pose proof (leaf_cells_munchF a b c d e f g h i m0 mx _ lo hi LC MU AP ltac:(repeat constructor; cbn; lia)) as H
    end end.

(* ------------------------------------------------------------------ musl __tls_get_addr (0x99624) *)

Definition tgaF_post (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (TP : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1 a2 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 TP) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

Lemma tgaF_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) TP DT TS C T DB k tb te,
  a0 = Z_to_bv 64 0xa15d0 -> tp = Z_to_bv 64 TP -> leafF_cells TP DT TS C T DB k tb te m -> mem_inv rsegs m ->
  leaf_rng RNG TP DT TS C T DB k ->
  evtF rsegs RNG (tgaF_post ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc TP m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x99624) fc None m (seg_rom rsegs)).
Proof.
  intros until te. intros -> -> LC MI (RIMG & RTP88 & RTPW & RDT & RTS & RCX & RT48 & RDB).
  img_rng RIMG.
  leafcF 0 LC V. leafcF 1 LC DTV. leafcF 2 LC DTV1. leafrF LC.
  do 9 zstep. clear V DTV DTV1.
  match goal with |- context [Z_to_bv 64 (?x + (TP + 2048))] =>
    replace (Z_to_bv 64 (x + (TP + 2048))) with (Z_to_bv 64 TP) by word_eq_tac end.
  apply evtF_done. eexists _, _, m. split; [cbv delta [mkR]; reflexivity|].
  split; [apply munch_refl|]. split; [apply wmono_refl| exact MI].
Qed.

(* ------------------------------------------------------------------ TryAsanInitFromRtl (0x5a174) *)

Definition tryinitF_post (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp).

Lemma tryinitF_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) TP DT TS C T DB k tb te (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 ->
  leafF_cells TP DT TS C T DB k tb te m -> leaf_apartF TP DT TS C T DB k (bv_unsigned sp - 16) (bv_unsigned sp) ->
  mem_inv rsegs m -> leaf_rng RNG TP DT TS C T DB k -> rng RNG (bv_unsigned sp - 16) 16 ->
  evtF rsegs RNG (tryinitF_post ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x5a174) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros ST LO LC AP MI (RIMG & RTP88 & RTPW & RDT & RTS & RCX & RT48 & RDB) RFR.
  img_rng RIMG.
  leafcF 3 LC INI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct AP as (AP0 & _).
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. carve_frame 16%nat ST. do 4 zstep.
  zstep. zstep. zstep.
  zstep. if_cases K; zify_cond K; [exfalso; apply K; vm_compute; reflexivity|].
  do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  apply evtF_done. unfold tryinitF_post.
  lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end.
  split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
Qed.

(* ------------------------------------------------------------------ AsanTSDGet (0x554c0) *)

Definition tsdgetF_post (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (C : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 C) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

Lemma tsdgetF_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) TP DT TS C T DB k tb te,
  tp = Z_to_bv 64 TP -> leafF_cells TP DT TS C T DB k tb te m -> mem_inv rsegs m ->
  leaf_rng RNG TP DT TS C T DB k ->
  evtF rsegs RNG (tsdgetF_post ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc C m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x554c0) fc None m (seg_rom rsegs)).
Proof.
  intros until te. intros -> LC MI (RIMG & RTP88 & RTPW & RDT & RTS & RCX & RT48 & RDB).
  img_rng RIMG.
  leafcF 4 LC KEY. leafcF 5 LC TSD. leafcF 6 LC TSD0. leafcF 7 LC CC. leafrF LC.
  do 3 zstep. zstep. if_cases K; zify_cond K; [exfalso; lia|].
  zstep. zstep. zstep. zstep. zstep. rewrite sx32_shl32 by lia. zstep. rewrite shr29_idx by lia.
  zstep. set (Q := TS + 8 * k) in *. clearbody Q. zstep. zstep.
  apply evtF_done. eexists _, m. split; [cbv delta [mkR]; reflexivity|].
  split; [apply munch_refl|]. split; [apply wmono_refl| exact MI].
Qed.

(* ------------------------------------------------------------------ GetCurrentThread (0x5c974) *)

Definition getthreadF_post (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (T lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 T) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp).

Lemma getthreadF_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) TP DT TS C T DB k tb te (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 ->
  tp = Z_to_bv 64 TP -> leafF_cells TP DT TS C T DB k tb te m ->
  leaf_apartF TP DT TS C T DB k (bv_unsigned sp - 16) (bv_unsigned sp) -> mem_inv rsegs m ->
  leaf_rng RNG TP DT TS C T DB k -> rng RNG (bv_unsigned sp - 16) 16 ->
  evtF rsegs RNG (getthreadF_post ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                    F fc (thr_of C T) lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x5c974) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros ST LO TPE LC AP MI LRNG RFR.
  pose proof LRNG as (RIMG & RTP88 & RTPW & RDT & RTS & RCX & RT48 & RDB). img_rng RIMG.
  leafrF LC.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. carve_frame 16%nat ST. zstep.
  freshLCF LC0.
  zstep. call tsdgetF_spec; first [ exact TPE | exact LC0 | exact LRNG | assumption | idtac ]. clear LC0.
  zstep. if_cases K; zify_cond K.
  - do 2 zstep. release_frame FR ST (bv_unsigned sp). zstep.
    apply evtF_done. unfold getthreadF_post, thr_of. rewrite K. cbn [Z.eqb].
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => eexists _, mx end.
    split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; assumption.
  - freshLCF LC1. leafcF 8 LC1 THR. clear LC1.
    zstep. do 2 zstep. release_frame FR ST (bv_unsigned sp). zstep.
    apply evtF_done. unfold getthreadF_post, thr_of.
    replace (C =? 0) with false by (symmetry; apply Z.eqb_neq; exact K).
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => eexists _, mx end.
    split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; assumption.
Qed.

(* ------------------------------------------------------------------ DTLS_on_tls_get_addr (0x6a088) *)

Definition dtlsF_post (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 144, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp).

Lemma dtlsF_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) TP DT TS C T DB k tb te (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 144 ->
  a0 = Z_to_bv 64 0xa15d0 -> tp = Z_to_bv 64 TP -> leafF_cells TP DT TS C T DB k tb te m ->
  leaf_apartF TP DT TS C T DB k (bv_unsigned sp - 144) (bv_unsigned sp) -> mem_inv rsegs m ->
  leaf_rng RNG TP DT TS C T DB k -> rng RNG (bv_unsigned sp - 144) 144 ->
  evtF rsegs RNG (dtlsF_post ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x6a088) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros ST LO -> -> LC AP MI (RIMG & RTP88 & RTPW & RDT & RTS & RCX & RT48 & RDB) RFR.
  img_rng RIMG. leafrF LC.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. carve_frame 144%nat ST. do 13 zstep.
  zstep.
  freshLCF LC0. leafcF 11 LC0 GCF. leafcF 12 LC0 ICF.
  do 3 zstep. clear GCF ICF.
  zstep. if_cases K; zify_cond K; [exfalso; lia|].
  leafcF 13 LC0 GGEN. leafcF 0 LC0 DESC. leafcF 14 LC0 GEN. leafcF 15 LC0 GOFF.
  zstep. do 2 zstep.
  zstep.
  zstep. zstep. replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
  zstep. zstep. zstep. clear GGEN DESC GEN GOFF. rewrite (Z.add_comm 8 TP).
  zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
  leafcF 16 LC0 DPTR.
  zstep. clear DPTR.
  zstep. zstep.
  zstep. if_cases K3; zify_cond K3; [exfalso; lia|].
  zstep. if_cases K4; zify_cond K4; [| exfalso; lia].
  zstep. if_cases K5; zify_cond K5; [exfalso; lia|].
  clear LC0. zstep. zstep.
  freshLCF LC1.
  zstep. zstep. if_cases K6; zify_cond K6; [| exfalso; lia].
  do 3 zstep.
  leafcF 17 LC1 DTV1.
  zstep. clear DTV1.
  zstep. if_cases K7; zify_cond K7; [exfalso; lia|].
  zstep. do 13 zstep. release_frame FR ST (bv_unsigned sp). zstep. zstep.
  apply evtF_done. unfold dtlsF_post.
  lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => eexists _, mx end.
  split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; assumption.
Qed.

(* ------------------------------------------------------------------ the __tls_get_addr interceptor (0x42af4) *)

Definition icptF_post (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (TP lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 TP) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 176, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp).

Lemma icptF_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) TP DT TS C T DB k tb te (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 176 ->
  a0 = Z_to_bv 64 0xa15d0 -> tp = Z_to_bv 64 TP -> leafF_cells TP DT TS C T DB k tb te m ->
  leaf_apartF TP DT TS C T DB k (bv_unsigned sp - 176) (bv_unsigned sp) -> mem_inv rsegs m ->
  leaf_rng RNG TP DT TS C T DB k -> rng RNG (bv_unsigned sp - 176) 176 ->
  evtF rsegs RNG (icptF_post ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc TP lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x42af4) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros ST LO A0 TPE LC AP MI LRNG RFR.
  pose proof LRNG as (RIMG & RTP88 & RTPW & RDT & RTS & RCX & RT48 & RDB). img_rng RIMG.
  leafrF LC.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep.
  zstep. carve_frame 32%nat ST. do 4 zstep. zstep.
  freshLCF LCa.
  zstep. call_sp tryinitF_spec;
    first [ exact ST | exact LCa | exact LRNG
          | eapply leaf_apart_subF; [exact AP| lia ..] | solve_rng | lia | assumption | idtac ].
  rename POST into ST. clear LCa.
  freshLCF LC0. leafcF 10 LC0 RREAL. do 2 zstep. clear RREAL.
  do 2 zstep.
  zstep. subst a0.
  call tgaF_spec; first [ reflexivity | exact TPE | exact LC0 | exact LRNG | assumption | idtac ]. clear LC0.
  zstep.
  zstep. if_cases K; zify_cond K; [exfalso; lia|].
  freshLCF LC1.
  zstep. call_sp getthreadF_spec;
    first [ exact ST | exact TPE | exact LC1 | exact LRNG
          | eapply leaf_apart_subF; [exact AP| lia ..] | solve_rng | lia | assumption | idtac ].
  rename POST into ST. clear LC1.
  assert (TR : 0 <= thr_of C T < 2^64) by (unfold thr_of; destruct (C =? 0); lia).
  zstep. if_cases K2; zify_cond K2.
  - zstep. zstep. do 2 zstep. zstep.
    freshLCF LC2.
    call_sp dtlsF_spec;
      first [ exact ST | reflexivity | exact TPE | exact LC2 | exact LRNG
            | eapply leaf_apart_subF; [exact AP| lia ..] | solve_rng | lia | assumption | idtac ].
    rename POST into ST. clear LC2.
    zstep. do 4 zstep. release_frame FR ST (bv_unsigned sp). zstep. zstep.
    apply evtF_done. unfold icptF_post.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => eexists _, _, _, mx end.
    split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; assumption.
  - assert (ET : thr_of C T = T) by (unfold thr_of in *; destruct (C =? 0); [lia| reflexivity]).
    rewrite ET in *. freshLCF LC2. leafcF 9 LC2 TLSB.
    do 2 zstep. clear TLSB. zstep.
    do 2 zstep.
    zstep. call_sp dtlsF_spec;
      first [ exact ST | reflexivity | exact TPE | exact LC2 | exact LRNG
            | eapply leaf_apart_subF; [exact AP| lia ..] | solve_rng | lia | assumption | idtac ].
    rename POST into ST. clear LC2.
    zstep. do 4 zstep. release_frame FR ST (bv_unsigned sp). zstep. zstep.
    apply evtF_done. unfold icptF_post.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => eexists _, _, _, mx end.
    split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; assumption.
Qed.

(* ------------------------------------------------------------------ MemToShadow (0x3dd78) *)

Definition m2sF_post (ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (A : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 a1 a2 a3 a4 a5 a6 a7 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (A / 8 + 0x7fff8000)) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

Lemma m2sF_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (A : Z),
  a0 = Z_to_bv 64 A ->
  (0 <= A < 0x7fff8000) \/ (0x10007fff8000 <= A < 0x800000000000) ->
  m2sF_cells m -> mem_inv rsegs m -> rng RNG IMG_LO (IMG_HI - IMG_LO) ->
  evtF rsegs RNG (m2sF_post ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc A m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x3dd78) fc None m (seg_rom rsegs)).
Proof.
  intros until A. intros -> HA (G1 & SB & KH) MI RIMG. img_rng RIMG.
  do 3 zstep. clear SB.
  do 4 zstep.
  try (replace (Z.land ((Z.b2z (2147450880 <? 2147450879) + -1) mod 18446744073709551616) 2147450879)
         with 2147450879 by reflexivity).
  zstep. if_cases K1; zify_cond K1.
  { destruct HA as [HA|HA]; [| exfalso; revert K1; rewrite ?unsigned_lit by lia; lia].
    do 3 zstep.
    match goal with |- context [Z_to_bv 64 (?x + Z.shiftr A 3)] =>
      replace (x + Z.shiftr A 3) with (A / 8 + 0x7fff8000) by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia) end.
    apply evtF_done. unfold m2sF_post.
    eexists _, _, _, _, _, _, _, _, m.
    split; [cbv delta [mkR]; reflexivity| split; [apply munch_refl| split; [apply wmono_refl| exact MI]]]. }
  destruct HA as [HA|HA]; [exfalso; revert K1; rewrite ?unsigned_lit by lia; lia|].
  do 4 zstep. zstep. zstep.
  zstep.
  zstep. if_cases K2; zify_cond K2; [| exfalso; revert K2; rewrite ?unsigned_lit by lia; lia].
  do 2 zstep. zstep.
  do 2 zstep.
  zstep. if_cases K3; zify_cond K3; [exfalso; revert K3; rewrite ?unsigned_lit by lia; lia|].
  zstep. if_cases K4; zify_cond K4; [exfalso; revert K4; rewrite ?unsigned_lit by lia; lia|].
  do 3 zstep.
  match goal with |- context [Z_to_bv 64 (?x + Z.shiftr A 3)] =>
    replace (x + Z.shiftr A 3) with (A / 8 + 0x7fff8000) by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia) end.
  apply evtF_done. unfold m2sF_post.
  eexists _, _, _, _, _, _, _, _, m.
  split; [cbv delta [mkR]; reflexivity| split; [apply munch_refl| split; [apply wmono_refl| exact MI]]].
Qed.

(* ------------------------------------------------------------------ the shadow of a frame area, from a region

   lib/B/Tk/AW/SmLib.v shadow_stk with shadow_rw_on P m (lib/B/ShadowRwOn.v) in place of shadow_rw m: the n shadow
   bytes from shadow_addr A are present and readable when P holds each of them.  The proof is shadow_stk's; its last
   step takes the byte from the region premise. *)
Lemma shadow_stk_on (m : word -> option byte) (P : Z -> Prop) A n : shadow_rw_on P m ->
  (forall y, shadow_addr A <= y < shadow_addr A + n -> P y) -> 0 <= A -> A mod 8 = 0 -> 0 < n ->
  (forall x, A <= x < A + 8 * n -> app_mem x) -> stk rsegs m (shadow_addr A) (shadow_addr A + n).
Proof.
  intros SRW HP HA HM Hn APP.
  assert (E : forall y, shadow_addr A <= y < shadow_addr A + n -> shadow_addr (A + 8 * (y - shadow_addr A)) = y).
  { intros y Hy. rewrite shadow_addr_add. lia. }
  assert (S : forall y, shadow_addr A <= y < shadow_addr A + n -> in_shadow y).
  { intros y Hy. rewrite <- (E y Hy). apply app_in_shadow, APP. lia. }
  pose proof (app_in_shadow _ (APP (A + 8 * (n - 1)) ltac:(lia))) as SL. rewrite shadow_addr_add in SL.
  assert (S0 : 0 <= shadow_addr A) by (unfold shadow_addr, ASAN_K; pose proof (Z.div_pos A 8 HA ltac:(lia)); lia).
  split; [exact S0|]. split.
  - unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in SL.
    change (2 ^ 64) with 18446744073709551616. lia.
  - intros y Hy. exact (SRW y (HP y Hy) (S y Hy)).
Qed.
