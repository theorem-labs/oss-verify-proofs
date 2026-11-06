(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AM_memcpy AF_kit AF_kit2 AF_free_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::= LiaA.liaA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition REA_FN : Z := 0x33634.          (* [comment removed for export] *)
Definition REA_ALLOC_RET : Z := 0x336a0.   (* [comment removed for export] *)
Definition ALLOCATE_FN : Z := 0x32c00.      (* [comment removed for export] *)
Definition AINST : Z := 0xaa518.           (* [comment removed for export] *)
Definition REA_MEMCPY_RET : Z := 0x33718.   (* [comment removed for export] *)
Definition DEALLOCATE_FN : Z := 0x328ec.    (* [comment removed for export] *)
Definition REA_DEALLOC_RET : Z := 0x33734.  (* [comment removed for export] *)
Definition GOT_REAL_MEMCPY : Z := 0xa49d8.  (* [comment removed for export] *)
Definition REAL_MEMCPY_VAR : Z := 0xa6820.  (* [comment removed for export] *)
Definition MUSL_MEMCPY : Z := 0x9dcdc.

Lemma zx32_lit : forall x, zx32 (Z_to_bv 64 x) = Z_to_bv 64 (x mod 2^32).
Proof.
  intros x. unfold zx32. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^32 * 2^32).
  rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm, Z_mod_plus_full. apply Z.mod_mod. lia.
Qed.

Section REA.
Variable P : acc -> Prop.
Variables (gp tp t2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variable Q : machine_state -> Prop.
Variables (lo TSD CTX T : Z).
Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis HTSD : 0xa4000 <= TSD /\ TSD + 8 <= 0x603000.
Hypothesis HCTX : 0 < CTX /\ CTX + 4096 <= alloc_ceiling.
Hypothesis HT : (0x1000 <= T /\ (T + 4096 <= 0x10000 \/ 0x603000 <= T)) /\ T + 4096 <= alloc_ceiling.   (* [comment removed for export] *)
Hypothesis HTC : CTX + 160 <= T \/ T + 4096 <= CTX.
Hypothesis HTP : 0xa4000 + 88 <= bv_unsigned tp < 0x603000.
Hypothesis PDAT : forall a k, 0xa4000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PCTX : P (Z_to_bv 64 (CTX + 152), 8%nat).
Hypothesis PT : forall a k, T <= a -> a + Z.of_nat k <= T + 4096 -> P (Z_to_bv 64 a, k).

(* [comment removed for export] *)
Lemma rea_A : forall (ra t0 t1 s0 s1 a4 a5 a6 a7 s2 s3 s4 : word) (m : mem) (sp p n B : Z) (st5 st6 : Z),
  stk asegs m lo sp -> lo <= sp - 80 -> sp <= 2^47 -> sp mod 16 = 0 -> mem_inv asegs m ->
  0 < p < 2^64 -> 0 < n < 2^64 -> 0 <= B < 2^64 ->
  thread_cells m tp TSD CTX T ->
  rw_cells asegs m (T + 2856) [C8 (Z_to_bv 64 st5); C8 (Z_to_bv 64 st6)] ->       (* [comment removed for export] *)
  (forall a k, lo <= a -> a + Z.of_nat k <= sp -> P (Z_to_bv 64 a, k)) ->
  (forall m' (t0' t1' a6' a7' : word),
     mem_inv asegs m' -> stk asegs m' lo (sp - 48) -> wmono asegs m m' ->
     munch [(sp - 80, sp); (T + 2856, T + 2872)] m m' ->
     thread_cells m' tp TSD CTX T ->
     rw_cells asegs m' (T + 2856) [C8 (Z_to_bv 64 (st5 + 1)); C8 (Z_to_bv 64 (st6 + n))] ->
     rw_cells asegs m' (sp - 48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
     evtA asegs P Q (MS (mkR (Z_to_bv 64 REA_ALLOC_RET) (Z_to_bv 64 (sp - 48)) gp tp t0' t1' t2 (Z_to_bv 64 B) (Z_to_bv 64 p)
                             (Z_to_bv 64 AINST) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 B) (Z_to_bv 64 1) (Z_to_bv 64 1) a6' a7'
                             (Z_to_bv 64 AINST) (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 ALLOCATE_FN) fc None m' (seg_rom asegs))) ->
  evtA asegs P Q (MS (mkR ra (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 AINST) (Z_to_bv 64 p) (Z_to_bv 64 n) (Z_to_bv 64 B) a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 REA_FN) fc None m (seg_rom asegs)).
Proof.
  intros until st6. intros SK LO SPH SPA MI Hp Hn HB TC STATS PSTK CONT. unfold REA_FN, REA_ALLOC_RET, ALLOCATE_FN, AINST in *.
  destruct TC as (TC1 & TC2 & TC3 & TC4 & TC5).
  pose proof LOC as LOC0. aceil.
  pose proof HT as [[HT' _] HT'']. pose proof HCTX as HC'. aceil.
  assert (MU : munch [(sp - 80, sp); (T + 2856, T + 2872)] m m) by apply munch_refl.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  carve_frame 48%nat SK.
  do 7 zstepA.   (* [comment removed for export] *)
  zstepA. if_cases K1; zify_cond K1; [exfalso; revert K1; rewrite ?unsigned_lit by (clear -Hp; lia); clear -Hp; lia|]. clear K1.   (* [comment removed for export] *)
  zstepA.        (* [comment removed for export] *)
  zstepA. if_cases K2; zify_cond K2; [exfalso; revert K2; rewrite ?unsigned_lit by (clear -Hn; lia); clear -Hn; lia|]. clear K2.   (* [comment removed for export] *)
  do 3 zstepA.   (* [comment removed for export] *)
  zstepA.        (* [comment removed for export] *)
  pose proof (unsigned_lit (sp + -48) ltac:(lia)) as Hsp.
  callA (gcts_walk P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo TSD CTX T); rewrite ?Hsp;
    [exact SK| exact LOC0| lia| lia| exact MI| exact (conj TC1 (conj TC2 (conj TC3 (conj TC4 TC5))))| lia| lia| lia| lia| lia| exact HTP| intros; apply PSTK; lia| exact PDAT| exact PCTX|].
  rewrite ?Hsp in *. match goal with H : stk _ _ lo _ |- _ => rename H into SK end.
  zstepA. zstepA.   (* [comment removed for export] *)
  zstepA. zstepA.   (* [comment removed for export] *)
  zstepA. zstepA.   (* [comment removed for export] *)
  do 6 zstepA.      (* [comment removed for export] *)
  zstepA.           (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with H : rw_cells asegs mx (T + 2856) _ |- _ => rename H into STATS' end;
    lazymatch goal with H : mem_inv asegs mx |- _ => rename H into MI' end end.
  eapply CONT; [exact MI'| exact SK| eassumption| eassumption| exact (conj TC1 (conj TC2 (conj TC3 (conj TC4 TC5))))| exact STATS'| exact FR].
Qed.

(* [comment removed for export] *)
Lemma rea_B : forall (t0 t1 a1 a2 a3 a4 a5 a6 a7 s4 : word) (m : mem) (sp p n B r oldn : Z) (hb1 : byte) (hid : word)
                     (old : list byte) (junk rest : list byte),
  mem_inv asegs m ->
  0 < p -> p + oldn < 2^64 -> 0 < n < 2^64 -> 0 < r -> r + n < 2^64 -> 0 <= oldn < 2^40 ->
  rw_cells asegs m (p + -16) [C1 (Z_to_bv 8 2); C1 hb1; C2 (Z_to_bv 64 (oldn / 2^32)); C4 (Z_to_bv 64 oldn); C8 hid] ->   (* [comment removed for export] *)
  rw_cells asegs m GOT_REAL_MEMCPY [C8 (Z_to_bv 64 REAL_MEMCPY_VAR)] -> rw_cells asegs m REAL_MEMCPY_VAR [C8 (Z_to_bv 64 MUSL_MEMCPY)] ->
  bytes_at asegs m p old -> length old = Z.to_nat oldn ->
  rw_cells asegs m r [CB (Z.to_nat (Z.min n oldn)) junk; CB (Z.to_nat (n - Z.min n oldn)) rest] ->
  (p + oldn <= r \/ r + n <= p) ->
  (forall a k, p - 16 <= a -> a + Z.of_nat k <= p + oldn -> P (Z_to_bv 64 a, k)) ->
  (forall a k, r <= a -> a + Z.of_nat k <= r + n -> P (Z_to_bv 64 a, k)) ->
  (forall m' (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word),
     mem_inv asegs m' -> wmono asegs m m' -> munch [(r, r + Z.min n oldn)] m m' ->
     rw_cells asegs m' r [CB (Z.to_nat (Z.min n oldn)) (firstn (Z.to_nat (Z.min n oldn)) old); CB (Z.to_nat (n - Z.min n oldn)) rest] ->
     bytes_at asegs m' p old ->
     evtA asegs P Q (MS (mkR (Z_to_bv 64 REA_DEALLOC_RET) (Z_to_bv 64 sp) gp tp t0' t1' t2' (Z_to_bv 64 B) (Z_to_bv 64 p)
                             (Z_to_bv 64 AINST) (Z_to_bv 64 p) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 B) (Z_to_bv 64 1) a6' a7'
                             (Z_to_bv 64 AINST) (Z_to_bv 64 (Z.min n oldn)) (Z_to_bv 64 r) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (Z_to_bv 64 DEALLOCATE_FN) fc None m' (seg_rom asegs))) ->
  evtA asegs P Q (MS (mkR (Z_to_bv 64 REA_ALLOC_RET) (Z_to_bv 64 sp) gp tp t0 t1 t2 (Z_to_bv 64 B) (Z_to_bv 64 p)
                          (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
                          (Z_to_bv 64 AINST) (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 REA_ALLOC_RET) fc None m (seg_rom asegs)).
Proof.
  intros until rest. intros MI Hp Hpo Hn Hr Hrn Hon HDR GOTM RMV OLD LOLD NEW SEP PHB PNEW CONT.
  unfold REA_ALLOC_RET, REA_DEALLOC_RET, DEALLOCATE_FN, AINST, GOT_REAL_MEMCPY, REAL_MEMCPY_VAR, MUSL_MEMCPY in *.
  assert (MU : munch [(r, r + Z.min n oldn)] m m) by apply munch_refl.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  zstepA.           (* [comment removed for export] *)
  zstepA. if_cases K0; zify_cond K0; [exfalso; revert K0; rewrite ?unsigned_lit by (clear -Hr Hrn Hn; lia); clear -Hr; lia|]. clear K0.   (* [comment removed for export] *)
  zstepA.           (* [comment removed for export] *)
  zstepA. zstepA.   (* [comment removed for export] *)
  cstep.            (* [comment removed for export] *)
  zstepA. zstepA.   (* [comment removed for export] *)
  zstepA.           (* [comment removed for export] *)
  cstep.            (* [comment removed for export] *)
  assert (HHI : 0 <= oldn / 2^32 < 2^8) by (clear -Hon; Z.div_mod_to_equations; lia).
  zstepA. rewrite fzx16_small by (clear -HHI; lia).   (* [comment removed for export] *)
  zstepA. rewrite zx32_lit.  (* [comment removed for export] *)
  zstepA. zstepA.   (* [comment removed for export] *)
  rewrite ?unsigned_lit by (clear -HHI Hon; lia).
  change (2^32) with 4294967296 in HHI |- *.
  rewrite (Z.mod_small (Z.shiftl (oldn / 4294967296) 32) 18446744073709551616) by (rewrite Z.shiftl_mul_pow2 by lia; clear -HHI Hon; lia).
  rewrite (lor_shiftl (oldn / 4294967296) (oldn mod 4294967296) 32) by (clear -HHI Hon; Z.div_mod_to_equations; lia).
  replace (oldn / 4294967296 * 2^32 + oldn mod 4294967296) with oldn by (clear -Hon; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  assert (STEPMIN : forall mc, evtA asegs P Q (MS (mkR (Z_to_bv 64 0x336a0) (Z_to_bv 64 sp) gp tp t0 t1 t2 (Z_to_bv 64 B) (Z_to_bv 64 p)
                             (Z_to_bv 64 oldn) (Z_to_bv 64 (oldn mod 4294967296)) a2 (Z_to_bv 64 MUSL_MEMCPY) a4 a5 a6 a7
                             (Z_to_bv 64 AINST) (Z_to_bv 64 (Z.min n oldn)) (Z_to_bv 64 r) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x33708) fc None mc (seg_rom asegs)) ->
            mc = m ->
            evtA asegs P Q (MS (mkR (Z_to_bv 64 0x336a0) (Z_to_bv 64 sp) gp tp t0 t1 t2 (Z_to_bv 64 B) (Z_to_bv 64 p)
                             (Z_to_bv 64 oldn) (Z_to_bv 64 (oldn mod 4294967296)) a2 (Z_to_bv 64 MUSL_MEMCPY) a4 a5 a6 a7
                             (Z_to_bv 64 AINST) (Z_to_bv 64 n) (Z_to_bv 64 r) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x33700) fc None mc (seg_rom asegs))).
  { intros mc K ->. unfold REAL_MEMCPY_VAR, MUSL_MEMCPY, AINST in K.
    zstepA; if_cases Kmin; zify_cond Kmin; rewrite ?unsigned_lit in Kmin by lia.
    - replace (Z.min n oldn) with n in K by lia. exact K.
    - zstepA. replace (Z.min n oldn) with oldn in K by lia. exact K. }
  unfold REAL_MEMCPY_VAR, MUSL_MEMCPY, AINST in STEPMIN. apply STEPMIN; [| reflexivity]. clear STEPMIN.
  assert (HM : 0 <= Z.min n oldn <= oldn /\ Z.min n oldn <= n) by lia.
  do 3 zstepA.      (* [comment removed for export] *)
  zstepA.           (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (OLD1 : bytes_at asegs m p (firstn (Z.to_nat (Z.min n oldn)) old)).
  { rewrite <- (firstn_skipn (Z.to_nat (Z.min n oldn)) old) in OLD. apply (proj1 (bytes_at_app _ _ _ _ _)) in OLD. exact (proj1 OLD). }
  assert (LEN1 : length (firstn (Z.to_nat (Z.min n oldn)) old) = Z.to_nat (Z.min n oldn)) by (rewrite length_firstn; lia).
  pose proof NEW as NEW2. change (rw_cells asegs m r ([CB (Z.to_nat (Z.min n oldn)) junk] ++ [CB (Z.to_nat (n - Z.min n oldn)) rest])) in NEW2. apply rwc_split in NEW2. destruct NEW2 as [DST REST]. cbn [cells_size csize Nat.add] in REST.
  eapply evtA_cut.
  { eapply (memcpy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (firstn (Z.to_nat (Z.min n oldn)) old) junk P);
      rewrite ?unsigned_lit by lia;
      [ intros a k Ha Hk; apply PHB; lia
      | intros a k Ha Hk; apply PNEW; lia
      | exact OLD1 | exact LEN1 | exact DST | lia | eassumption ]. }
  cbv beta. intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & DST2 & SRC2).
  pose proof (unsigned_lit (Z.min n oldn) ltac:(clear -HM Hon Hn; lia)) as UM. pose proof (unsigned_lit r ltac:(clear -Hr Hrn Hn; lia)) as UR. pose proof (unsigned_lit p ltac:(clear -Hp Hpo Hon; lia)) as UP.
  rewrite ?UM, ?UR, ?UP in MU2. rewrite ?UM, ?UR, ?UP in DST2. rewrite ?UM, ?UR, ?UP in SRC2. ret_pc_lit.
  eapply (rw_cells_transport asegs) in REST; [| exact MU2| exact WM2| cbn [disjoint_from cells_size csize Nat.add length]; clear -HM Hn Hon; lia].
  assert (OLD2 : bytes_at asegs m2 p old).
  { eapply bytes_at_transport; [| exact MU2|]; [exact OLD| cbn [disjoint_from length]; rewrite LOLD; lia]. }
  clear MU WM. repeat match goal with H : rw_cells asegs m _ _ |- _ => clear H | H : bytes_at asegs m _ _ |- _ => clear H | H : mem_inv asegs m |- _ => clear H end.
  do 6 zstepA.      (* [comment removed for export] *)
  zstepA.           (* [comment removed for export] *)
  eapply CONT; [exact MI2| exact WM2| exact MU2| | exact OLD2].
  eapply (rwc_join_at asegs m2 _ _ _ _ DST2 REST). cbn [cells_size csize Nat.add]. clear -HM; lia.
Qed.

(* [comment removed for export] *)
Lemma asan_rea_pro : forall (ra t0 t1 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 : word) (m : mem) (sp p n B : Z),
  stk asegs m lo sp -> lo <= sp - 16 -> sp <= 2^47 -> mem_inv asegs m -> 0 < p < 2^64 -> 0 < n < 2^64 ->
  (forall a k, lo <= a -> a + Z.of_nat k <= sp -> P (Z_to_bv 64 a, k)) ->
  (forall m' (j8 : list byte), mem_inv asegs m' -> stk asegs m' lo (sp - 16) -> wmono asegs m m' -> munch [(sp - 16, sp)] m m' ->
     rw_cells asegs m' (sp - 16) [CB 8 j8; C8 ra] ->
     evtA asegs P Q (MS (mkR (Z_to_bv 64 0x33624) (Z_to_bv 64 (sp - 16)) gp tp t0 t1 t2 s0 s1
                             (Z_to_bv 64 AINST) (Z_to_bv 64 p) (Z_to_bv 64 n) (Z_to_bv 64 B) a4 a5 (Z_to_bv 64 B) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 REA_FN) fc None m' (seg_rom asegs))) ->
  evtA asegs P Q (MS (mkR ra (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 n) (Z_to_bv 64 B) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x33588) fc None m (seg_rom asegs)).
Proof.
  intros until B. intros SK LO SPH MI Hp Hn PSTK CONT. unfold REA_FN, AINST in *.
  pose proof LOC as LOC0. aceil.
  assert (MU : munch [(sp - 16, sp)] m m) by apply munch_refl. assert (WM : wmono asegs m m) by apply wmono_refl.
  carve_frame 16%nat SK.
  zstepA. zstepA.      (* [comment removed for export] *)
  zstepA. zstepA.      (* [comment removed for export] *)
  zstepA. if_cases K1; zify_cond K1; [exfalso; revert K1; rewrite ?unsigned_lit by (clear -Hp; lia); clear -Hp; lia|]. clear K1.   (* [comment removed for export] *)
  zstepA.              (* [comment removed for export] *)
  zstepA. if_cases K2; zify_cond K2; [| exfalso; revert K2; rewrite ?unsigned_lit by (clear -Hn; lia); clear -Hn; lia]. clear K2.   (* [comment removed for export] *)
  zstepA. zstepA.      (* [comment removed for export] *)
  zstepA. zstepA.      (* [comment removed for export] *)
  zstepA.              (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with H : mem_inv asegs mx |- _ => rename H into MI' end;
    lazymatch goal with H : rw_cells asegs mx _ _ |- _ => rename H into FR' end end.
  eapply CONT; [exact MI'| exact SK| eassumption| eassumption|].
  first [exact FR' | eapply rw_cells_reshape; [| | exact FR']; [cbn; tauto| reflexivity]].
Qed.

(* [comment removed for export] *)
Lemma rea_epi : forall (ra t0 t1 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 : word) (rav sv0 sv1 sv2 sv3 sv4 : word) (m : mem) (sp : Z),
  stk asegs m lo (sp - 48) -> lo <= sp - 48 -> sp <= 2^47 -> mem_inv asegs m ->
  rw_cells asegs m (sp - 48) [C8 sv4; C8 sv3; C8 sv2; C8 sv1; C8 sv0; C8 rav] ->
  (forall a k, lo <= a -> a + Z.of_nat k <= sp -> P (Z_to_bv 64 a, k)) ->
  (forall m', mem_inv asegs m' -> stk asegs m' lo sp -> wmono asegs m m' -> munch [(sp - 48, sp)] m m' ->
     evtA asegs P Q (MS (mkR rav (Z_to_bv 64 sp) gp tp t0 t1 t2 sv0 sv1 s4 a1 a2 a3 a4 a5 a6 a7 sv2 sv3 sv4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (ret_pc rav) fc None m' (seg_rom asegs))) ->
  evtA asegs P Q (MS (mkR ra (Z_to_bv 64 (sp - 48)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 REA_DEALLOC_RET) fc None m (seg_rom asegs)).
Proof.
  intros until sp. intros SK LO SPH MI FR PSTK CONT. unfold REA_DEALLOC_RET in *.
  pose proof LOC as LOC0. aceil.
  assert (MU : munch [(sp - 48, sp)] m m) by apply munch_refl. assert (WM : wmono asegs m m) by apply wmono_refl.
  zstepA.              (* [comment removed for export] *)
  do 6 zstepA.         (* [comment removed for export] *)
  zstepA.              (* [comment removed for export] *)
  release_frame FR SK sp.
  zstepA.              (* [comment removed for export] *)
  replace (sp - 48 + 48) with sp by lia.
  eapply CONT; [exact MI| exact SK| exact WM| exact MU].
Qed.

(* [comment removed for export] *)
Lemma rea_ret : forall (ra t0 t1 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 : word) (rav sv0 sv1 sv2 sv3 sv4 sv5 sv6 bpw : word)
                       (m : mem) (usp : Z) (j8a j8b j8c j1800 : list byte) (ws : list word) (len : Z),
  stk asegs m lo (usp + -2160) -> lo <= usp + -2160 -> usp <= 2^47 -> mem_inv asegs m ->
  rw_cells asegs m (usp + -2160) [CB 8 j8a; C8 (Z_to_bv 64 0x54648)] ->
  rw_cells asegs m (usp + -2144) [CB 8 j8b] ->
  rw_cells asegs m (usp + -2136) [C8 (Z_to_bv 64 (usp + -2120)); C4 (Z_to_bv 64 len); C4 (Z_to_bv 64 0)] ->
  u64arr asegs m (usp + -2120) ws -> length ws = 30%nat ->
  rw_cells asegs m (usp + -1880) [CB 1800 j1800] -> rw_cells asegs m (usp + -80) [C8 bpw] -> rw_cells asegs m (usp + -72) [CB 8 j8c] ->
  rw_cells asegs m (usp + -64) [C8 sv6; C8 sv5; C8 sv4; C8 sv3; C8 sv2; C8 sv1; C8 sv0; C8 rav] ->
  (forall a k, lo <= a -> a + Z.of_nat k <= usp -> P (Z_to_bv 64 a, k)) ->
  (forall m', mem_inv asegs m' -> stk asegs m' lo usp -> wmono asegs m m' -> munch [(usp + -2160, usp)] m m' ->
     evtA asegs P Q (MS (mkR rav (Z_to_bv 64 usp) gp tp t0 t1 t2 sv0 sv1 a0 a1 a2 a3 a4 a5 a6 a7 sv2 sv3 sv4 sv5 sv6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (ret_pc rav) fc None m' (seg_rom asegs))) ->
  evtA asegs P Q (MS (mkR ra (Z_to_bv 64 (usp + -2160)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x33628) fc None m (seg_rom asegs)).
Proof.
  intros until len. intros SK LO SPH MI FRA FJ8B OBJ ARR LEN FJ1800 FBP FJ8 FRX PSTK CONT.
  pose proof LOC as LOC0. aceil.
  assert (MU : munch [(usp + -2160, usp)] m m) by apply munch_refl. assert (WM : wmono asegs m m) by apply wmono_refl.
  zstepA. zstepA.      (* [comment removed for export] *)
  zstepA.              (* [comment removed for export] *)
  zstepA.              (* [comment removed for export] *)
  do 8 zstepA.         (* [comment removed for export] *)
  zstepA.              (* [comment removed for export] *)
  pose proof (cb_of_u64arr asegs _ _ _ ARR) as FBUF. rewrite LEN in FBUF. clear ARR.
  release_frame FRA SK (usp + -2144). release_frame FJ8B SK (usp + -2136). release_frame OBJ SK (usp + -2120). release_frame FBUF SK (usp + -1880).
  release_frame FJ1800 SK (usp + -80). release_frame FBP SK (usp + -72). release_frame FJ8 SK (usp + -64). release_frame FRX SK usp.
  zstepA.              (* [comment removed for export] *)
  replace (usp + -2160 + 16 + 112 + 2032) with usp by lia. replace (usp + - (2160) + 16 + 112 + 2032) with usp by lia.
  eapply CONT; [exact MI| exact SK| exact WM| exact MU].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma asan_rea0_pro : forall (ra t0 t1 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 : word) (m : mem) (sp n B : Z),
  stk asegs m lo sp -> lo <= sp - 16 -> sp <= 2^47 -> mem_inv asegs m -> 0 <= n < 2^64 -> 0 <= B < 2^64 ->
  (forall a k, lo <= a -> a + Z.of_nat k <= sp -> P (Z_to_bv 64 a, k)) ->
  (forall m' (j8 : list byte), mem_inv asegs m' -> stk asegs m' lo (sp - 16) -> wmono asegs m m' -> munch [(sp - 16, sp)] m m' ->
     rw_cells asegs m' (sp - 16) [CB 8 j8; C8 ra] ->
     evtA asegs P Q (MS (mkR (Z_to_bv 64 0x33600) (Z_to_bv 64 (sp - 16)) gp tp t0 t1 t2 s0 s1
                             (Z_to_bv 64 AINST) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 B) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 B) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 ALLOCATE_FN) fc None m' (seg_rom asegs))) ->
  evtA asegs P Q (MS (mkR ra (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 n) (Z_to_bv 64 B) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x33588) fc None m (seg_rom asegs)).
Proof.
  intros until B. intros SK LO SPH MI Hn HB PSTK CONT. unfold ALLOCATE_FN, AINST in *.
  pose proof LOC as LOC0. aceil.
  assert (MU : munch [(sp - 16, sp)] m m) by apply munch_refl. assert (WM : wmono asegs m m) by apply wmono_refl.
  carve_frame 16%nat SK.
  zstepA. zstepA.      (* [comment removed for export] *)
  zstepA. zstepA.      (* [comment removed for export] *)
  cstep.               (* [comment removed for export] *)
  do 7 zstepA.         (* [comment removed for export] *)
  zstepA.              (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with H : mem_inv asegs mx |- _ => rename H into MI' end;
    lazymatch goal with H : rw_cells asegs mx _ _ |- _ => rename H into FR' end end.
  eapply CONT; [exact MI'| exact SK| eassumption| eassumption| first [exact FR' | eapply rw_cells_reshape; [| | exact FR']; [cbn; tauto| reflexivity]]].
Qed.

(* [comment removed for export] *)
Lemma rea0_after_ok : forall (t0 t1 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 : word) (m : mem) (sp r : Z),
  0 < r < 2^64 ->
  evtA asegs P Q (MS (mkR (Z_to_bv 64 0x33600) (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x33628) fc None m (seg_rom asegs)) ->
  evtA asegs P Q (MS (mkR (Z_to_bv 64 0x33600) (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x33600) fc None m (seg_rom asegs)).
Proof.
  intros until r. intros Hr K.
  zstepA. if_cases K1; zify_cond K1; [exact K| exfalso; revert K1; rewrite ?unsigned_lit by (clear -Hr; lia); clear -Hr; lia].
Qed.
Lemma rea0_after_fail : forall (t0 t1 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 : word) (m : mem) (sp : Z),
  evtA asegs P Q (MS (mkR (Z_to_bv 64 0x33600) (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x33604) fc None m (seg_rom asegs)) ->
  evtA asegs P Q (MS (mkR (Z_to_bv 64 0x33600) (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x33600) fc None m (seg_rom asegs)).
Proof. intros until sp. intros K. cstep. exact K. Qed.

(* [comment removed for export] *)
Lemma rea_after_ok : forall (t0 t1 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 : word) (m : mem) (sp r : Z),
  0 < r < 2^64 ->
  evtA asegs P Q (MS (mkR (Z_to_bv 64 0x33624) (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x33628) fc None m (seg_rom asegs)) ->
  evtA asegs P Q (MS (mkR (Z_to_bv 64 0x33624) (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x33624) fc None m (seg_rom asegs)).
Proof.
  intros until r. intros Hr K.
  zstepA. if_cases K1; zify_cond K1; [exfalso; revert K1; rewrite ?unsigned_lit by (clear -Hr; lia); clear -Hr; lia| exact K].
Qed.
Lemma rea_after_fail : forall (t0 t1 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 : word) (m : mem) (sp : Z),
  evtA asegs P Q (MS (mkR (Z_to_bv 64 0x33624) (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x33604) fc None m (seg_rom asegs)) ->
  evtA asegs P Q (MS (mkR (Z_to_bv 64 0x33624) (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x33624) fc None m (seg_rom asegs)).
Proof. intros until sp. intros K. cstep. exact K. Qed.

(* [comment removed for export] *)
Lemma rea_A0 : forall (t0 t1 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 : word) (m : mem) (sp : Z),
  evtA asegs P Q (MS (mkR (Z_to_bv 64 REA_ALLOC_RET) (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 0) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 REA_DEALLOC_RET) fc None m (seg_rom asegs)) ->
  evtA asegs P Q (MS (mkR (Z_to_bv 64 REA_ALLOC_RET) (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 REA_ALLOC_RET) fc None m (seg_rom asegs)).
Proof. intros until sp. intros K. unfold REA_ALLOC_RET, REA_DEALLOC_RET in *. zstepA. cstep. exact K. Qed.
End REA.
End RC__1.
