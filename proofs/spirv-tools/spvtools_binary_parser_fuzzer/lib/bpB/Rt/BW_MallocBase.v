(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocRep BsAtomics B_memset BsDepotInv BsDepotHash BsDepotPut BsUnwind BidBits BW_Combined BW_PoisonShadow BW_Leaves BW_DepotFrame BW_AllocBase BW_Allocate BllocWalkKit.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

Lemma bytes_le_to_Z_range8 : forall bs : list byte, length bs = 8%nat -> 0 <= bytes_le_to_Z bs < 2^64.
Proof.
  intros bs L. rewrite BBytes.bytes_le_to_Z_le_val. pose proof (BBytes.le_val_range (map bv_unsigned bs) (BBytes.bytes_ok_map bs)) as R.
  rewrite length_map, L in R. change (256 ^ Z.of_nat 8) with (2^64) in R. exact R.
Qed.

Lemma Z_to_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb.
  assert (NN : 0 <= bytes_le_to_Z bs).
  { clear IH. induction bs as [|c cs IHc]; cbn; [lia|]. apply Z.lor_nonneg. split; [apply bv_unsigned_in_range|]. apply Z.shiftl_nonneg. exact IHc. }
  rewrite BBytes.lor_shiftl8_add by lia. f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?x) with (x mod 256). Z.div_mod_to_equations. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
    replace ((bv_unsigned b + 256 * bytes_le_to_Z bs) / 256) with (bytes_le_to_Z bs) by (Z.div_mod_to_equations; lia). exact IH.
Qed.

Lemma le8_surj : forall bs : list byte, length bs = 8%nat -> exists w : word, le8 w = bs.
Proof.
  intros bs L. exists (le_bytes_to_word bs). unfold le8, word_to_le_bytes, le_bytes_to_word.
  rewrite Z_to_bv_unsigned. pose proof (bytes_le_to_Z_range8 bs L).
  change (bv_wrap 64 ?x) with (x mod 2^64). rewrite Z.mod_small by lia. rewrite <- L. apply Z_to_le_bytes_to_Z.
Qed.

Lemma u64s_surj : forall k (bs : list byte), length bs = (8 * k)%nat -> exists ws, u64s ws = bs /\ length ws = k.
Proof.
  induction k as [|k IH]; intros bs L.
  - exists []. destruct bs; [split; reflexivity| cbn in L; lia].
  - destruct (le8_surj (firstn 8 bs)) as [w Hw]. { rewrite firstn_length. lia. }
    destruct (IH (skipn 8 bs)) as [ws [Hws Lws]]. { rewrite skipn_length. lia. }
    exists (w :: ws). split; [| cbn; lia]. cbn [u64s]. rewrite Hw, Hws. apply firstn_skipn.
Qed.

Lemma u64arr_of_junk : forall m A k bs, rw_cells asegs m A [CB (8 * k)%nat bs] -> exists ws, u64arr asegs m A ws /\ length ws = k.
Proof.
  intros m A k bs R. pose proof (u8arr_of_rw_cells asegs m A _ bs R) as U.
  assert (L : length bs = (8 * k)%nat) by (destruct R as [[[L _] _] _]; exact L).
  destruct (u64s_surj k bs L) as [ws [E Lws]]. exists ws. split; [| exact Lws].
  apply (u64arr_u8arr asegs). rewrite E. exact U.
Qed.

Lemma rw_cells_C8_zero_split : forall m A cs, rw_cells asegs m A (C8 (wz 0) :: cs) -> rw_cells asegs m A (C4 (wz 0) :: C4 (wz 0) :: cs).
Proof. intros m A cs [[[_ W] B] R]. exact (conj (conj (conj I (conj I W)) B) R). Qed.

Lemma le4_app_le8 : forall a, 0 <= a < 2^32 -> le4 (wz a) ++ le4 (wz 0) = le8 (wz a).
Proof.
  intros a Ha. unfold le4, le8, word_to_le_bytes, wz. rewrite !Z_to_bv_unsigned.
  change (bv_wrap 64 a) with (a mod 2^64). change (bv_wrap 64 0) with (0 mod 2^64). rewrite !Z.mod_small by lia.
  cbn [Z_to_le_bytes app]. rewrite !Z.shiftr_shiftr by lia. cbn [Z.add Pos.add Pos.succ].
  assert (E : forall k, 32 <= k -> Z.shiftr a k = 0).
  { intros k Hk. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. split; [lia|]. eapply Z.lt_le_trans; [apply (proj2 Ha)|]. apply Z.pow_le_mono_r; lia. }
  replace (8+8) with 16 by reflexivity. replace (16+8) with 24 by reflexivity. replace (24+8) with 32 by reflexivity.
  replace (32+8) with 40 by reflexivity. replace (40+8) with 48 by reflexivity. replace (48+8) with 56 by reflexivity.
  rewrite (E 32), (E 40), (E 48), (E 56) by lia. reflexivity.
Qed.

Lemma rw_cells_C4C4_C8 : forall m A a cs, 0 <= a < 2^32 ->
  rw_cells asegs m A (C4 (wz a) :: C4 (wz 0) :: cs) -> rw_cells asegs m A (C8 (wz a) :: cs).
Proof.
  intros m A a cs Ha [[[_ [_ W]] B] R]. refine (conj (conj (conj I W) _) R).
  cbn [cells_bytes cbytes] in B |- *. rewrite <- le4_app_le8 by exact Ha. rewrite <- app_assoc. exact B.
Qed.

Lemma utrace_range' : forall pc0 bp top bot md CH,
  (goodframe bot bp top = true -> Forall (fun rv : Z * Z => 0 <= fst rv < 2^64) CH) -> 0 <= pc0 < 2^64 ->
  Forall (fun x => 0 <= x < 2^64) (utrace pc0 bp top bot md CH).
Proof.
  intros pc0 bp top bot md CH HC Hpc. destruct (goodframe bot bp top) eqn:G.
  - apply utrace_range; [apply HC; reflexivity| exact Hpc].
  - unfold utrace. rewrite G. destruct (top <? KPAGE); constructor; try lia; constructor.
Qed.

Section Leaves2.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z).
  Hypothesis MI : mem_inv asegs m.

  Hypothesis CMCS : rw_cells asegs m 0x191d3c [C4 (wz 30)].
  Theorem malloc_context_size_spec :
    evt asegs (leaf_post ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m 30)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xc275c) fc None m (seg_rom asegs)).
  Proof.
    step. step. rewrite sx32_wz by lia. step. step.
    apply evt_done. unfold leaf_post. split; [reflexivity| split; [apply munch_refl| split; [apply wmono_refl| exact MI]]].
  Qed.

End Leaves2.
Section Leaves3.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z).
  Hypothesis MI : mem_inv asegs m.

  Hypothesis CINIT : rw_cells asegs m AINITED [C1 (b8 1)].
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 16 <= bv_unsigned sp.
  Theorem try_asan_init_spec :
    evt asegs (rzlog_post ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo 1)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xc19d4) fc None m (seg_rom asegs)).
  Proof.
    unfold AINITED in *.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. acb.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    step. carve_frame 16%nat ST. step. step. step. step. step. step. step.
    step. if_cases K. { exfalso. revert K. vm_compute. discriminate. } clear K.
    step. step. step. step. release_frame FR ST (bv_unsigned sp). finish.
  Qed.
End Leaves3.

Record IENV (tp : word) (TSD CTX TH sb TOP BOT : Z) (m : mem) : Prop := mkIENV {
  i_tsdi : rw_cells asegs m 1640608 [C1 (b8 1); CB 3 [b8 0; b8 0; b8 0]; C4 (wz 0)];
  i_tp   : rw_cells asegs m (bv_unsigned tp + -88) [C8 (wz TSD)];
  i_tsd  : rw_cells asegs m TSD [C8 (wz CTX)];
  i_ctx  : rw_cells asegs m (CTX + 152) [C8 (wz TH)];
  i_lsan : rw_cells asegs m (bv_unsigned tp + 16) [C4 (wz 0)];
  i_got2 : rw_cells asegs m 0x185d00 [C8 (wz 0x10)];
  i_thr  : rw_cells asegs m TH [C8 (wz CTX)];
  i_tid  : rw_cells asegs m (CTX + 8) [C4 (wz 0)];
  i_init : rw_cells asegs m 1645848 [C1 (b8 1)];
  i_afl  : rw_cells asegs m 2175648 [C1 (b8 0); C1 (b8 1); C1 (b8 0)];
  i_can  : rw_cells asegs m 1640604 [C1 (b8 1)];
  i_got  : rw_cells asegs m 1593472 (map (fun v => C8 (wz v)) AGOT_VALS);
  i_shb  : rw_cells asegs m 1642552 [C8 (wz 2147450880)];
  i_hme  : rw_cells asegs m 1645856 [C8 (wz 140737488355327); C8 (wz 0); C8 (wz 0)];
  i_thresh : rw_cells asegs m 2239456 [C8 (wz 0xffffffffffffffff)];
  i_rms  : rw_cells asegs m 1601864 [C8 (wz 1535652)];
  i_fill : rw_cells asegs m 1632356 [C4 (wz 4096); C4 (wz 0); C4 (wz 0xbe)];
  i_part : rw_cells asegs m 1632397 [C1 (b8 1)];
  i_hooks : rw_cells asegs m 2239232 (repeat (C8 (wz 0)) 10);
  i_inst1 : rw_cells asegs m 1628664 [C8 (wz sb)];
  i_inst2 : rw_cells asegs m 1632248 [C8 (wz (2^40)); C2 (wz 16); C2 (wz 2048); C1 (b8 1); CB 3 [b8 0; b8 0; b8 0]];

  i_mcs  : rw_cells asegs m 0x191d3c [C4 (wz 30)];
  i_psc  : rw_cells asegs m 0x220ae0 [C8 (wz 4096)];
  i_cfu  : rw_cells asegs m (0x222b68 + 34) [C1 (b8 1)];
  i_stk  : rw_cells asegs m (TH + 8) [C8 (wz TOP); C8 (wz BOT)];
  i_t40  : rw_cells asegs m (TH + 40) [C1 (b8 0)]
}.

End HCW.

Ltac open_ienv E :=
  destruct E as [Etsdi Etp Etsd Ectx Elsan Egot2 Ethr Etid Einit Eafl Ecan Egot Eshb Ehme Ethresh Erms Efill Epart Ehooks Einst1 Einst2
                 Emcs Epsc Ecfu Estk Et40];
  unfold AGOT_VALS in Egot; cbn [map] in Egot; cbn [repeat] in Ehooks.

Section HCW2.
  Context {HCEIL : HeapCeil}.

Definition icpt_chain (rav s0v sp0 TOP : Z) (CH : list (Z * Z)) : list (Z * Z) :=
  if goodframe sp0 s0v TOP then (rav, s0v) :: CH else [(rav, s0v)].

Definition malloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (W : list ivl) (lo size AB U rz csz P cnt mc TH id : Z) (chunks : list Z) (d' : depot) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (j0 j1 j2 j3 : word) (b1 : Z) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz U) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' P [C4 (wz (cnt - 1)); C4 (wz mc)]
    /\ u32arr asegs m' (P + 16) (wlist (rev (tl chunks)))
    /\ stk asegs m' (P + 16 + 4 * (cnt - 1)) (P + 80)
    /\ rw_cells asegs m' (TH + 208 + 2560) [C8 j0; C8 j1; C8 j2; C8 j3]
    /\ rw_cells asegs m' (U + -16) [C1 (b8 2); C1 (b8 b1); C2 (wz 0); C4 (wz size); C8 (wz id)] /\ b1_ok b1
    /\ (rz = 16 \/ (rw_cells asegs m' AB [C8 (wz kAllocBegMagic); C8 (wz (U + -16))] /\ stk asegs m' (AB + 16) (U + -16)))
    /\ u8arr asegs m' U (repeat (b8 0xbe) (Z.to_nat (Z.min size 4096)))
    /\ stk asegs m' (U + Z.min size 4096) (AB + csz)
    /\ u8arr asegs m' (sh AB) (alloc_shadow rz size csz)
    /\ stk asegs m' (TH + 2800) (TH + 3168)
    /\ rw_cells asegs m' (TH + 3168) [C1 (b8 0)]
    /\ DEPOT asegs d' m'.

End HCW2.

Ltac post_callUI segs m :=
  let ms := fresh "ms" in let PO := fresh "PO" in
  intros ms PO; unfold ui_post, ui_W, OFF_UNWINDING in PO;
  rewrite ?unsigned_lit in PO by lia; rewrite ?Z.add_0_r in PO; revert ms PO; post_call segs m.
Ltac post_callA segs m :=
  let ms := fresh "ms" in let PO := fresh "PO" in
  intros ms PO; unfold allocate_post, depot_W in PO;
  rewrite ?unsigned_lit in PO by lia; rewrite ?Z.add_0_r in PO; revert ms PO; post_call segs m.
