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
From Stdlib Require Permutation.
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require BImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_phex4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_conv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pvalue_lemmas.
Module CJ_fp_lemmas.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_conv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_parse_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pvalue_lemmas.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac fix_lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
      change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => mem_after_store
  | _ => idtac
  end.

(* [comment removed for export] *)
Ltac sbstep := step; rewrite le1_lit; mem_after_store.

(* [comment removed for export] *)
Lemma land_align32 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551584 = x / 32 * 32.
Proof.
  intros x Hx.
  replace 18446744073709551584 with (Z.lxor (Z.ones 64) (Z.ones 5)) by reflexivity.
  replace (x / 32 * 32) with (Z.shiftl (Z.shiftr x 5) 5).
  2:{ rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity. }
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.lxor_spec, Z.shiftl_spec by lia.
  destruct (Z.lt_ge_cases i 5) as [Hi3|Hi3].
  - rewrite (Z.testbit_neg_r (Z.shiftr x 5)) by lia. rewrite !Z.ones_spec_low by lia. cbn. apply andb_false_r.
  - rewrite Z.shiftr_spec by lia. replace (i - 5 + 5) with i by lia. rewrite (Z.ones_spec_high 5 i) by lia.
    destruct (Z.lt_ge_cases i 64) as [Hi64|Hi64].
    + rewrite Z.ones_spec_low by lia. cbn. apply andb_true_r.
    + rewrite Z.ones_spec_high by lia. cbn.
      replace (Z.testbit x i) with false; [reflexivity|]. symmetry.
      destruct (Z.eq_dec x 0) as [->|Hx0]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia| lia].
Qed.

(* [comment removed for export] *)
Definition art_flag_high_stmt (AI : art_iface) : Prop :=
  forall sp0 SPB LB LF TRS B m mo g Fr k fl,
    ART AI sp0 SPB LB LF TRS B m mo g -> In (Fr, k) LF -> cells_at bsegs m (Fr + fsz k - 8) [C8 (wz fl)] -> 0 <= fl < 2^64 ->
    ablk fl (fl + 1).        (* [comment removed for export] *)

Lemma art_flag_high_holds : forall AI, art_flag_high_stmt AI.
Proof. intros AI. unfold art_flag_high_stmt. intros. eapply (art_flag_high AI); eauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition SHCW (m : word -> option byte) (Fr : Z) (b : list byte) : Prop :=
  rw_cells bsegs m (Z.shiftr Fr 3 + 2147450880) (map C1 b).

Lemma SHCW_sh_bytes : forall m Fr vs, SHCW m Fr (map zb vs) -> sh_bytes m Fr vs.
Proof.
  intros m Fr vs H. unfold SHCW in H. rewrite SH_shiftr in H. apply rw_cells_sh_bytes. unfold shcells.
  rewrite map_map in H. exact H.
Qed.

Lemma cells_size_mapC1 : forall b : list byte, cells_size (map C1 b) = length b.
Proof. induction b as [|x b IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma chain_trace_one : forall f r s, chain_trace 2 [(f, r, s)] = [r].
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma chain_cells_frame1 : forall m f (s0w raw : word),
  rw_cells bsegs m (f + -16) [C8 s0w; C8 raw] -> chain_cells m [(f, bv_unsigned raw, bv_unsigned s0w)].
Proof.
  intros m f s0w raw [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  cbn. split; [| exact I]. unfold wz. rewrite !Z_to_bv_bv_unsigned. replace (f - 16) with (f + -16) by lia. exact HB.
Qed.

(* [comment removed for export] *)
Lemma frame_join : forall m SA cs hi,
  rw_cells bsegs m SA cs -> stk bsegs m (SA + Z.of_nat (cells_size cs)) hi -> SA + Z.of_nat (cells_size cs) <= hi ->
  exists cpre, rw_cells bsegs m SA cpre /\ SA + Z.of_nat (cells_size cpre) = hi.
Proof.
  intros m SA cs hi H ST LE.
  destruct (stk_carve bsegs m _ hi (Z.to_nat (hi - (SA + Z.of_nat (cells_size cs)))) ST ltac:(lia)) as [_ [junk J]].
  replace (hi - Z.of_nat (Z.to_nat (hi - (SA + Z.of_nat (cells_size cs))))) with (SA + Z.of_nat (cells_size cs)) in J by lia.
  exists (cs ++ [CB (Z.to_nat (hi - (SA + Z.of_nat (cells_size cs)))) junk]). split.
  - apply (proj2 (rw_cells_split_app _ _ _ _)). split; [exact H| exact J].
  - rewrite cells_size_app. cbn [cells_size Cells.csize]. lia.
Qed.


(* [comment removed for export] *)
Lemma stkmalloc_stmt'_holds : forall AI k, (k = 1 \/ k = 2) -> stkmalloc_stmt' AI k.
Proof.
  intros AI k Hk. unfold stkmalloc_stmt'. intros.
  destruct Hk as [-> | ->].
  - eapply (art_stkmalloc1 AI); eauto.
  - eapply (art_stkmalloc2 AI); eauto.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac fix_lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
      change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => mem_after_store
  | _ => idtac
  end.
Ltac sbstep := step; rewrite le1_lit; mem_after_store.
End CJ_fp_lemmas.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_bandM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_skipws.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_skipws.CJ_band.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs CJ_iface AShadow CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_pbuf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_conv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_parse_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_pvalue_lemmas.
Import CJ_fp_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_fuzz_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_fuzz_iface.CJ_print_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.CJ_print_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import StoreCache.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import LiaOn.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition PV_EPI       : Z := 0x84b8c.   (* [comment removed for export] *)
Definition PV_RET1      : Z := 0x846e0.   (* [comment removed for export] *)
Definition PV_RET0      : Z := 0x840ec.   (* [comment removed for export] *)
Definition PV_RET0_C2C  : Z := 0x849e0.   (* [comment removed for export] *)
Definition PV_NUM_X     : Z := 0x84b74.   (* [comment removed for export] *)
Definition PV_FALSE_ENTRY : Z := 0x840cc.  (* [comment removed for export] *)
Definition PV_TRUE_ENTRY  : Z := 0x846c0.
Definition PV_NULL_ENTRY  : Z := 0x845f0.
Definition PV_NUM_ENTRY   : Z := 0x8460c.
Definition PV_STR_ENTRY   : Z := 0x846e8.
Definition PV_ARR_ENTRY   : Z := 0x8470c.
Definition PV_OBJ_ENTRY   : Z := 0x84144.
Definition PV_RAW_ENTRY   : Z := 0x840fc.
Definition PV_JT          : Z := 0x20e4c.    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition FMAGIC     : Z := 0x41b58ab3.
Definition FMAGIC_RET : Z := 0x45e0360e.
Definition FDESC      : Z := 0x13d5a.
Definition SHP_IDLE : list Z := [-15; -15; -15; -15; -8; -8; -8; -8; -14; -14; -14; -14; -8; -13; -13; -13].
Definition SHP_NUM  : list Z := [-15; -15; -15; -15; 0; 0; 0; 2; -14; -14; -14; -14; 0; -13; -13; -13].

(* [comment removed for export] *)
Definition SHR (a : Z) : word := Z_to_bv 64 (Z.shiftr a 3 + 2147450880).

(* [comment removed for export] *)
Definition FAG18 (F Fc : bvmap 5 word) : Prop := forall k : bv 5, 18 <= bv_unsigned k <= 27 -> reg_get Fc k = reg_get F k.

Lemma FAG18_refl : forall F, FAG18 F F.
Proof. intros F k _. reflexivity. Qed.

Lemma FAG18_trans : forall F1 F2 F3, FAG18 F1 F2 -> FAG18 F2 F3 -> FAG18 F1 F3.
Proof. intros F1 F2 F3 A B k Hk. rewrite (B k Hk). apply A. exact Hk. Qed.

(* [comment removed for export] *)
Lemma FAG18_callee : forall F F1 F2, FAG18 F F1 -> (forall k : bv 5, fp_callee_saved k -> reg_get F2 k = reg_get F1 k) -> FAG18 F F2.
Proof. intros F F1 F2 A B k Hk. rewrite (B k ltac:(unfold fp_callee_saved; lia)). apply A. exact Hk. Qed.

(* [comment removed for export] *)
Lemma FAG18_but10 : forall F F1 F2, FAG18 F F1 -> (forall k : bv 5, bv_unsigned k <> 10 -> reg_get F2 k = reg_get F1 k) -> FAG18 F F2.
Proof. intros F F1 F2 A B k Hk. rewrite (B k ltac:(lia)). apply A. exact Hk. Qed.

Lemma FAG18_restore : forall F Fc, FAG18 F Fc ->
  forall k : bv 5, fp_callee_saved k ->
    reg_get (bvmap_set 8 (reg_get F (Z_to_bv 5 8)) (bvmap_set 9 (reg_get F (Z_to_bv 5 9)) Fc)) k = reg_get F k.
Proof.
  intros F Fc FA k Hk. unfold fp_callee_saved in Hk.
  destruct (Z.eq_dec (bv_unsigned k) 8) as [E8|N8].
  { rewrite freg_get_same by (rewrite E8; reflexivity). replace k with (Z_to_bv 5 8 : bv 5) by (apply bv_eq; rewrite E8; reflexivity). reflexivity. }
  rewrite freg_get_other by (unfold bv_eqb; apply Z.eqb_neq; replace (bv_unsigned (8%bv : bv 5)) with 8%Z by reflexivity; lia).
  destruct (Z.eq_dec (bv_unsigned k) 9) as [E9|N9].
  { rewrite freg_get_same by (rewrite E9; reflexivity). replace k with (Z_to_bv 5 9 : bv 5) by (apply bv_eq; rewrite E9; reflexivity). reflexivity. }
  rewrite freg_get_other by (unfold bv_eqb; apply Z.eqb_neq; replace (bv_unsigned (9%bv : bv 5)) with 9%Z by reflexivity; lia).
  apply FA. lia.
Qed.

(* [comment removed for export] *)
Lemma KHIGH_eqs : KHIGHMEM_BEG = 0x10007fff8000 /\ KHIGHMEM_END = 0x7fffffffffff /\ AIMG_HI = 0x5ff000
                  /\ AMALLOC_STACK = 8192 /\ AINTRIN_STACK = 2304 /\ ASTRFN_STACK = 2400 /\ AFORMAT_STACK = 16384 /\ ASTKMALLOC_STACK = 512.
Proof. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma pv_agree_weaken_lf : forall sp0 LR LF LF' SP PB m m',
  pv_agree sp0 LR LF SP PB m m' -> (forall f, In f LF' -> In f LF) -> pv_agree sp0 LR LF' SP PB m m'.
Proof.
  intros sp0 LR LF LF' SP PB m m' H HF. eapply magree_mono; [exact H|]. cbv beta.
  intros a [Hc Hn]. split; [|exact Hn].
  destruct Hc as [Hc|[Hc|[Hc|[(Fr & k & Hb & Hr)|Hc]]]]; [left; lia| right; left; exact Hc| right; right; left; exact Hc| do 3 right; left| do 4 right; exact Hc].
  exists Fr, k. split; [apply HF; exact Hb| exact Hr].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record pvi : Type := mkPVI {
  q_ai : art_iface; q_ti : trs_iface;
  (* [comment removed for export] *)
  q_ra : word; q_sp : word; q_gp : word; q_tp : word;
  q_s0 : word; q_s1 : word; q_s2 : word; q_s3 : word; q_s4 : word; q_s5 : word; q_s6 : word; q_s7 : word;
  q_s8 : word; q_s9 : word; q_s10 : word; q_s11 : word; q_F : bvmap 5 word;
  (* [comment removed for export] *)
  q_m : word -> option byte; q_g : lghost;
  (* [comment removed for export] *)
  q_sp0 : Z; q_SPB : Z; q_LR : list cblock; q_B : list cblock; q_LF : list fframe; q_np0 : Z; q_BB : Z;
  q_CH : list (Z * Z * Z); q_n : nat; q_p : Z; q_PB : Z; q_len0 : Z; q_dep : Z; q_fw : word; q_lo : Z;
  (* [comment removed for export] *)
  q_SA : Z; q_Fr : Z }.

Section PV.
  Variable Q : pvi.
  Local Notation AI := (q_ai Q).    Local Notation TI := (q_ti Q).
  Local Notation ra := (q_ra Q).    Local Notation sp := (q_sp Q).    Local Notation gp := (q_gp Q).    Local Notation tp := (q_tp Q).
  Local Notation s0 := (q_s0 Q).    Local Notation s1 := (q_s1 Q).    Local Notation s2 := (q_s2 Q).    Local Notation s3 := (q_s3 Q).
  Local Notation s4 := (q_s4 Q).    Local Notation s5 := (q_s5 Q).    Local Notation s6 := (q_s6 Q).    Local Notation s7 := (q_s7 Q).
  Local Notation s8 := (q_s8 Q).    Local Notation s9 := (q_s9 Q).    Local Notation s10 := (q_s10 Q).  Local Notation s11 := (q_s11 Q).
  Local Notation F := (q_F Q).      Local Notation m := (q_m Q).      Local Notation g := (q_g Q).
  Local Notation sp0 := (q_sp0 Q).  Local Notation SPB := (q_SPB Q).  Local Notation LR := (q_LR Q).    Local Notation B := (q_B Q).
  Local Notation LF := (q_LF Q).    Local Notation np0 := (q_np0 Q).  Local Notation BB := (q_BB Q).    Local Notation CH := (q_CH Q).
  Local Notation n := (q_n Q).      Local Notation p := (q_p Q).      Local Notation PB := (q_PB Q).    Local Notation len0 := (q_len0 Q).
  Local Notation dep := (q_dep Q).  Local Notation fw := (q_fw Q).    Local Notation lo := (q_lo Q).
  Local Notation SA := (q_SA Q).    Local Notation Fr := (q_Fr Q).

  Notation SP := (bv_unsigned sp).

  (* [comment removed for export] *)
  Definition pvl : Prop :=
    pb_place SP PB SPB /\ PB mod 8 = 0 /\ SP mod 16 = 0
    /\ sp0 <= 2^47 /\ SP + 16 < ASTACK_TOP sp0 /\ ASTACK_BOTTOM sp0 <= lo /\ PB + 80 <= 2^47
    /\ alloc_ceiling <= lo /\ lo <= SP - APV_STACK n /\ tp = wz ATP
    /\ (1 <= n)%nat /\ (forall b, In b B -> In b LR) /\ dep + Z.of_nat n <= 2^40 /\ 0 <= dep /\ p <> 0
    /\ chain_ok (SP + 16) CH (ASTACK_TOP sp0) /\ chain_link (bv_unsigned s0) SP CH /\ Forall (fun x => fr_f x <= PB) CH
    /\ (4096 <= bv_unsigned ra < AIMG_HI) /\ ~ is_pc0 (bv_unsigned ra)
    /\ np0 + pb_npallow len0 <= NPMAX TI /\ pb_allow len0 <= BB /\ 0 <= len0 <= INT_MAX
    /\ lf_room 1 LF (Z.of_nat n)
    /\ (SP - 208 <= SA <= SP - 192 /\ SA mod 32 = 0)
    /\ (Fr mod 128 = 0 /\ AIMG_HI <= Fr /\ Fr + 128 <= alloc_ceiling /\ ~ In Fr (map fst LF))
    /\ sclr Fr 128                                                      (* [comment removed for export] *)
    /\ cj_chain CJ_PRINTABLE m n p B.                                   (* [comment removed for export] *)

  Lemma pvl_lits : pvl ->
    (SP <= PB /\ PB + 64 <= SPB /\ SPB < 2^62) /\ PB mod 8 = 0 /\ SP mod 16 = 0
    /\ sp0 <= 2^47 /\ SP + 16 < ASTACK_TOP sp0 /\ ASTACK_BOTTOM sp0 <= lo /\ PB + 80 <= 2^47
    /\ alloc_ceiling <= lo /\ lo <= SP - (272 * Z.of_nat n + 24576) /\ tp = wz ATP
    /\ (1 <= n)%nat /\ (forall b, In b B -> In b LR) /\ dep + Z.of_nat n <= 2^40 /\ 0 <= dep /\ p <> 0
    /\ chain_ok (SP + 16) CH (ASTACK_TOP sp0) /\ chain_link (bv_unsigned s0) SP CH /\ Forall (fun x => fr_f x <= PB) CH
    /\ (4096 <= bv_unsigned ra < 0x5ff000) /\ ~ is_pc0 (bv_unsigned ra)
    /\ np0 + pb_npallow len0 <= NPMAX TI /\ pb_allow len0 <= BB /\ 0 <= len0 <= 2147483647
    /\ lf_room 1 LF (Z.of_nat n)
    /\ (SP - 208 <= SA <= SP - 192 /\ SA mod 32 = 0)
    /\ (Fr mod 128 = 0 /\ 0x5ff000 <= Fr /\ Fr + 128 <= alloc_ceiling /\ ~ In Fr (map fst LF))
    /\ 0 <= SP < 2^64 /\ 0 <= bv_unsigned ra < 2^64 /\ 0 <= bv_unsigned s0 < 2^64
    /\ (sp0 - 0xa0 <= ASTACK_TOP sp0 <= sp0 - 0xa0 + 4095 /\ ASTACK_BOTTOM sp0 = ASTACK_TOP sp0 - 0x800000
        (* [comment removed for export] *)
        /\ (Fr + 128 <= 0x7fff7000 \/ 0x10007fff8000 <= Fr))
    /\ cj_chain CJ_PRINTABLE m n p B.
  Proof.
    intros H. unfold sclr, pvl, pb_place, APV_STACK, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG, INT_MAX in H. try rewrite alloc_ceiling_eq in H.
    pose proof (bv_unsigned_in_range 64 sp) as R1. change (bv_modulus 64) with (2^64) in R1.
    pose proof (bv_unsigned_in_range 64 ra) as R2. change (bv_modulus 64) with (2^64) in R2.
    pose proof (bv_unsigned_in_range 64 s0) as R3. change (bv_modulus 64) with (2^64) in R3.
    pose proof (ASTACK_TOP_le sp0) as T.
    decompose [and] H. repeat (split; [first [assumption | repeat split; assumption | lia]|]).
    split; [| assumption]. split; [exact T|]. split; [unfold ASTACK_BOTTOM; lia| assumption].
  Qed.

  (* [comment removed for export] *)
  Definition SAVEDV : list cell :=
    [C8 (reg_get F (Z_to_bv 5 9)); C8 (reg_get F (Z_to_bv 5 8)); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5;
     C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition PBS (mm : word -> option byte) (buf len off depc : Z) : Prop :=
    rw_cells bsegs mm PB [C8 (wz buf); C8 (wz len); C8 (wz off); C8 (wz depc); C4 (wz 0); C4 fw;
                         C8 (wz AMALLOC); C8 (wz AFREE); C8 (wz AREALLOC)].

  (* [comment removed for export] *)
  Definition FHDR (mm : word -> option byte) : Prop :=
    rw_cells bsegs mm Fr [C8 (wz FMAGIC); C8 (wz FDESC); C8 (wz PVALUE_ENTRY)].
  Definition FBODY (mm : word -> option byte) (jb : list byte) : Prop := rw_cells bsegs mm (Fr + 24) [CB 96 jb].
  Definition SHCV (mm : word -> option byte) (shp : list Z) : Prop := SHCW mm Fr (map zb shp).

  (* [comment removed for export] *)
  Definition CSTV (pc : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x27 x28 x29 x30 x31 : word)
      (Fx : bvmap 5 word) (fcx : bv 32) (mm : word -> option byte) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) x10 x11 x12 x13 x14 x15 x16 x17
            x18 (Z_to_bv 64 PB) x20 x21 x22 x23 x24 (SHR Fr) (Z_to_bv 64 Fr) x27 x28 x29 x30 x31)
       Fx (Z_to_bv 64 pc) fcx None mm (seg_rom bsegs).

  (* [comment removed for export] *)
  Definition PVMs (depc : Z) (mm : word -> option byte) (mo1 : Model) (g1 : lghost) (LB1 : list cblock) (TRS1 : list (list Z))
      (B1 np1 : Z) (errv1 : word) (sbuf slen buf len off : Z) (bs : list byte) : Prop :=
    ART AI sp0 SPB LB1 ((Fr, 1) :: LF) TRS1 B1 mm mo1 g1
    /\ Permutation ((buf, len) :: LR) LB1 /\ PBS mm sbuf slen off depc /\ u8arr bsegs mm buf bs /\ Z.of_nat (length bs) = len
    /\ pb_nums len off depc
    /\ rw_cells bsegs mm AERRNO [C4 errv1] /\ mem_inv bsegs mm
    /\ pv_agree sp0 LR LF SP PB m mm /\ cj_chain CJ_PRINTABLE mm n p B /\ chain_cells mm CH /\ sh_zero mm alloc_ceiling (2^47)
    /\ (SP + 16 <= PB -> pb_below mm PB) /\ (PB = SP + 8 -> exists w : word, bytes_at bsegs mm SP (le8 w))
    /\ gmono g g1 /\ TINV TI np1 TRS1
    /\ len0 <= len /\ BB - (pb_pot len - pb_pot len0) <= B1 /\ np1 <= np0 + (pb_npot len - pb_npot len0).

  Definition PVM (depc : Z) (mm : word -> option byte) (mo1 : Model) (g1 : lghost) (LB1 : list cblock) (TRS1 : list (list Z))
      (B1 np1 : Z) (errv1 : word) (buf len off : Z) (bs : list byte) : Prop :=
    PVMs depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len buf len off bs.

  (* [comment removed for export] *)
  Definition PVFR (mm : word -> option byte) (loc : list word) (jb : list byte) (shp : list Z) (Fx : bvmap 5 word) (fcx : bv 32) : Prop :=
    rw_cells bsegs mm (SP + -120) SAVEDV /\ rw_cells bsegs mm SA (map C8 loc) /\ length loc = 9%nat
    /\ stk bsegs mm (SA + 72) (SP + -120) /\ stk bsegs mm lo SA
    /\ FHDR mm /\ FBODY mm jb /\ SHCV mm shp /\ length shp = 16%nat
    /\ frm0 fcx /\ FAG18 F Fx.

  Definition PVX depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb shp Fx fcx : Prop :=
    PVM depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs /\ PVFR mm loc jb shp Fx fcx.

  Hypothesis PVL : pvl.

  Ltac lits := pose proof (pvl_lits PVL) as ((PL1 & PL2 & PL3) & PB8 & AL & S47 & TOP & BOT & PB80 & CEIL & LO & TP & N1 & BLR & DEPN & DEP0 & PNZ
                                              & CHOK & CHL & CHB & RA1 & RA2 & NPM & BBA & LEN0 & LFR & (GSA1 & GSA2) & (FAL & FLO & FHI & FNEW)
                                              & SPR & RAR & S0R & (TOPR & BOTE) & CHN0);
               pose proof (Z.shiftr_div_pow2 Fr 3 ltac:(lia)) as SHFR; change (2^3) with 8 in SHFR;
               pose proof alloc_ceiling_eq as ACE; pose proof KHIGH_eqs as KHE.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma pvm_buf_range : forall depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs,
    PVM depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs ->
    0x5ff000 <= buf /\ buf mod 16 = 0 /\ 0 <= len /\ buf + Z.max len 1 <= alloc_ceiling.
  Proof.
    intros until bs. intros nelH_; (nelim nelH_ 3%nat; intros HL HP _).
    pose proof (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) as R.
    unfold sclr, ablock_range, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R. try rewrite alloc_ceiling_eq in R. exact R.
  Qed.

  Lemma pvm_LR_range : forall depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs,
    PVM depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs ->
    forall A k, In (A, k) LR -> 0x5ff000 <= A /\ A mod 16 = 0 /\ 0 <= k /\ A + Z.max k 1 <= alloc_ceiling.
  Proof.
    intros until bs. intros (HL & HP & _) A k Hin.
    pose proof (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL ltac:(eapply Permutation_in; [exact HP| right; exact Hin])) as R.
    unfold sclr, ablock_range, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R. try rewrite alloc_ceiling_eq in R. exact R.
  Qed.

  (* [comment removed for export] *)
  Lemma pvm_buf_apart : forall depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs,
    PVM depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs ->
    forall A k, In (A, k) LR -> A <> buf /\ (A + k <= buf \/ buf + len <= A).
  Proof. intros until bs. intros (HL & HP & _) A k Hin. eapply (lheap_perm_apart AI); eauto. Qed.

  (* [comment removed for export] *)
  Lemma pvm_frame_apart : forall depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs,
    PVM depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs ->
    (forall A k, In (A, k) LB1 -> A + k + 16 <= Fr \/ Fr + 128 <= A - 16)
    /\ (forall F' k', In (F', k') LF -> Fr + 128 <= F' \/ F' + fsz k' <= Fr).
  Proof.
    intros until bs. intros (HL & _). lits. bandM. sepM. split.
    - intros A k Hin. (nelimp (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL ltac:(left; reflexivity)) 8%nat; intros _ _ _ _ _ _ _ D).
      change (fsz 1) with 128 in D. apply D. exact Hin.
    - intros F' k' Hin.
      assert (NE : Fr <> F') by (intros E; apply FNEW; rewrite E; apply (in_map fst) in Hin; exact Hin).
      pose proof (art_frames_disjoint AI _ _ _ _ _ _ _ _ _ _ _ _ _ HL ltac:(left; reflexivity) ltac:(right; exact Hin) NE) as D.
      change (fsz 1) with 128 in D. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma pvm_magree_B : forall depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs,
    PVM depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs -> magree (in_cblock B) m mm.
  Proof.
    intros until bs. intros CTX. (nelimp CTX 10%nat; intros HL HP _ _ _ _ _ _ PVA _). lits. bandM. sepM.
    eapply magree_mono; [exact PVA|]. cbv beta. intros a nelH_; (nelim nelH_ 4%nat; intros A' n' Hin Hr).
    split; [right; right; left; exists A', n'; split; [apply BLR; exact Hin| exact Hr]|].
    pose proof (pvm_LR_range _ _ _ _ _ _ _ _ _ _ _ _ _ CTX A' n' (BLR _ Hin)). lia.
  Qed.

  Lemma pvm_chain : forall depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs T d q Bq,
    PVM depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs -> cj_chain T m d q Bq -> (forall b, In b Bq -> In b B) ->
    cj_chain T mm d q Bq.
  Proof.
    intros until Bq. intros CTX CHq SUB. eapply cj_chain_magree; [exact CHq| eapply pvm_magree_B; exact CTX|].
    intros a Ha. eapply in_cblock_mono; [exact SUB| exact Ha].
  Qed.

  Lemma pvm_str : forall depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs q Bq,
    PVM depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs -> cj_str m q Bq -> (forall b, In b Bq -> In b B) -> cj_str mm q Bq.
  Proof.
    intros until Bq. intros CTX SV SUB. eapply cj_str_magree; [eapply pvm_magree_B; exact CTX| exact SV|].
    intros a Ha. eapply in_cblock_mono; [exact SUB| exact Ha].
  Qed.

  Lemma pvm_node : forall depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs q cells,
    PVM depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs -> rw_cells bsegs m q cells -> cells_size cells = 64%nat ->
    In (q, 64) B -> rw_cells bsegs mm q cells.
  Proof.
    intros until cells. intros CTX ND SZ HIN. eapply rw_cells_magree; [eapply pvm_magree_B; exact CTX| exact ND|].
    rewrite SZ. intros a Ha. exists q, 64. split; [exact HIN| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma pvm_tree : forall depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs,
    PVM depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs -> cj_chain CJ_PRINTABLE mm n p B.
  Proof. intros until bs. intros CTX. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CTX)))))))))). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma pvm_allow : forall depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs,
    PVM depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs -> pb_allow len <= B1 /\ np1 + pb_npallow len <= NPMAX TI.
  Proof.
    intros until bs. intros CTX. lits. bandM. sepM.
    pose proof CTX as (_ & _ & _ & _ & _ & (PN1 & PN2 & PN3) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L0 & HB & HNP).
    assert (LI : len <= INT_MAX) by (unfold INT_MAX; lia).
    split.
    - eapply pb_allow_grow; [exact HB| exact BBA].
    - pose proof (pb_npot_mono len0 len ltac:(lia) LI). unfold pb_npallow in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pvm_pot_grow : forall len B1 np1 len' B2 np2,
    len0 <= len -> BB - (pb_pot len - pb_pot len0) <= B1 -> np1 <= np0 + (pb_npot len - pb_npot len0) ->
    B1 - (pb_pot len' - pb_pot len) <= B2 -> np2 <= np1 + (pb_npot len' - pb_npot len) -> len <= len' ->
    len0 <= len' /\ BB - (pb_pot len' - pb_pot len0) <= B2 /\ np2 <= np0 + (pb_npot len' - pb_npot len0).
  Proof. intros. lia. Qed.

  (* [comment removed for export] *)
  Lemma pvm_pot_fail : forall len B1 np1 B2 np2,
    len0 <= len -> len <= INT_MAX -> BB - (pb_pot len - pb_pot len0) <= B1 -> np1 <= np0 + (pb_npot len - pb_npot len0) ->
    B1 - pb_allow len <= B2 -> np2 <= np1 + pb_npallow len ->
    BB - pb_allow len0 <= B2 /\ np2 <= np0 + pb_npallow len0.
  Proof. intros. lits. bandM. sepM. unfold pb_allow, pb_npallow in *. lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition pv_own_iv (iv : Z * Z) : Prop :=
    snd iv <= fst iv
    \/ (lo <= fst iv /\ snd iv <= SP)                                  (* [comment removed for export] *)
    \/ (PB <= fst iv /\ snd iv <= PB + 32)                             (* [comment removed for export] *)
    \/ (Fr <= fst iv /\ snd iv <= Fr + 120)                            (* [comment removed for export] *)
    \/ (Z.shiftr Fr 3 + 2147450880 <= fst iv /\ snd iv <= Z.shiftr Fr 3 + 2147450880 + 16).  (* [comment removed for export] *)

  Lemma pv_own_write_ok : forall LB1 iv, pv_own_iv iv -> cj_write_ok sp0 SPB LB1 ((Fr, 1) :: LF) iv.
  Proof.
    intros LB1 [u v] H. lits. bandM. sepM. unfold pv_own_iv in H. cbn [fst snd] in H. unfold cj_write_ok. cbn [fst snd].
    destruct H as [H|[H|[H|[H|H]]]].
    - left. exact H.
    - right; left. try rewrite alloc_ceiling_eq. lia.
    - right; left. try rewrite alloc_ceiling_eq. lia.
    - do 8 right. left. exists Fr, 1. split; [left; reflexivity|]. change (fsz 1) with 128. lia.
    - do 9 right. exists Fr, 1. split; [left; reflexivity|]. rewrite SH_shiftr in H. change (fsz 1) with 128. lia.
  Qed.

  Lemma pvm_art_store : forall W LB1 TRS1 B1 mm mm' mo1 g1,
    ART AI sp0 SPB LB1 ((Fr, 1) :: LF) TRS1 B1 mm mo1 g1 -> munch W mm mm' -> wmono bsegs mm mm' ->
    Forall pv_own_iv W -> ART AI sp0 SPB LB1 ((Fr, 1) :: LF) TRS1 B1 mm' mo1 g1.
  Proof.
    intros W LB1 TRS1 B1 mm mm' mo1 g1 HL MU WM HW. eapply (art_frame AI); [exact HL| exact MU| exact WM|].
    eapply Forall_impl; [| exact HW]. intros iv Hiv. apply pv_own_write_ok. exact Hiv.
  Qed.

  (* [comment removed for export] *)
  Lemma pv_own_not_client : forall LB1 TRS1 B1 mm mo1 g1 a u v,
    ART AI sp0 SPB LB1 ((Fr, 1) :: LF) TRS1 B1 mm mo1 g1 -> (forall b, In b LR -> In b LB1) ->
    pv_own_iv (u, v) -> cj_client_addr sp0 LR LF SP a -> ~ (PB <= a < PB + 64) -> ~ (u <= a < v).
  Proof.
    intros LB1 TRS1 B1 mm mo1 g1 a u v HL HLR H Hc Hn. lits. bandM. sepM. unfold pv_own_iv in H. cbn [fst snd] in H. rewrite SHFR in H.
    unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM.
    (* [comment removed for export] *)
    assert (CL : SP <= a
                 \/ a < 0x5ff000
                 \/ (exists A' n', In (A', n') LB1 /\ A' <= a < A' + n' /\ 0x5ff000 <= A' /\ A' + Z.max n' 1 <= alloc_ceiling
                                    /\ (A' + n' + 16 <= Fr \/ Fr + 128 <= A' - 16)
                                    /\ (A' + Z.max n' 1 <= 0x7fff7000 \/ 0x10007fff8000 <= A'))
                 \/ (exists F' k, (fsz k = 128 \/ fsz k = 256) /\ 0x5ff000 <= F' /\ F' + fsz k <= alloc_ceiling
                                   /\ (Fr + 128 <= F' \/ F' + fsz k <= Fr)
                                   /\ (F' <= a < F' + fsz k - 8 \/ 2147450880 + F' / 8 <= a < 2147450880 + F' / 8 + fsz k / 8)
                                   /\ (F' + fsz k <= 0x7fff7000 \/ 0x10007fff8000 <= F'))
                 \/ (2147450880 + alloc_ceiling / 8 <= a < 0x10007fff8000)).   (* [comment removed for export] *)
    { destruct Hc as [Hs|[Hi|[(A' & n' & Hin & Hr)|[(F' & k & Hin & Hr)|Hsh]]]].
      - left. lia.
      - right; left. pose proof (aclient_image_lt a Hi). lia.
      - right; right; left. exists A', n'.
        (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (HLR _ Hin)) 4%nat; intros R1 _ _ R4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
        (nelimp (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL ltac:(left; reflexivity)) 8%nat; intros _ _ _ _ _ _ _ D).
        pose proof (D A' n' (HLR _ Hin)) as D'. change (fsz 1) with 128 in D'.
        split; [apply HLR; exact Hin|]. split; [exact Hr|]. split; [exact R1|]. split; [exact R4|]. split; [exact D'|].
        pose proof (art_block_sclr AI _ _ _ _ _ _ _ _ _ A' n' A' (Z.max n' 1) HL (HLR _ Hin) ltac:(lia) ltac:(lia)) as SC. unfold sclr, KHIGHMEM_BEG, KLOWSHADOW_BEG in SC. exact SC.
      - do 3 right; left. exists F', k.
        assert (NE : Fr <> F') by (intros E; apply FNEW; rewrite E; apply (in_map fst) in Hin; exact Hin).
        pose proof (art_frames_disjoint AI _ _ _ _ _ _ _ _ _ _ _ _ _ HL ltac:(left; reflexivity) ltac:(right; exact Hin) NE) as D.
        (nelimp (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL ltac:(right; exact Hin)) 5%nat; intros Hk _ HF1 HF2 _).
        unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in HF1. bandM. sepM. try rewrite alloc_ceiling_eq in HF2. change (fsz 1) with 128 in D.
        assert (K : fsz k = 128 \/ fsz k = 256) by (destruct Hk as [-> | ->]; [left| right]; reflexivity).
        split; [exact K|]. split; [exact HF1|]. split; [exact HF2|]. split; [lia|].
        unfold SH, SHADOW_OFFSET in Hr. split; [exact Hr|].
        pose proof (art_frame_sclr AI _ _ _ _ _ _ _ _ _ F' k F' (fsz k) HL ltac:(right; exact Hin) ltac:(lia) ltac:(lia)) as SC. unfold sclr, KHIGHMEM_BEG, KLOWSHADOW_BEG in SC. exact SC.
      - do 4 right. unfold astack_shadow in Hsh. assert (Rb : SH (2^47) = 0x10007fff8000) by reflexivity. rewrite Rb in Hsh.
        unfold SH, SHADOW_OFFSET in Hsh. lia. }
    pose proof (art_frame_sclr AI _ _ _ _ _ _ _ _ _ Fr 1 Fr 128 HL ltac:(left; reflexivity) ltac:(lia) ltac:(change (fsz 1) with 128; lia)) as FSC.
    unfold sclr, KHIGHMEM_BEG, KLOWSHADOW_BEG in FSC. bandM. sepM.
    clear Hc HL HLR.
    destruct H as [H|[H|[H|[H|H]]]]; [lia| | lia| |].
    all: destruct CL as [X|[X|[(A' & n' & _ & X1 & X2 & X3 & X4)|[(F' & k & K & X1 & X2 & X3 & X4)|X]]]].
    all: sepM.
    all: try (lia_on H CEIL FLO X X1 X3 X2 X4 LO FHI BMf).
    all: try (Z.div_mod_to_equations; lia).
    all: destruct K as [K|K]; rewrite K in *; Z.div_mod_to_equations; lia.
  Qed.

  Lemma pvm_agree_store : forall W LB1 TRS1 B1 mm mm' mo1 g1,
    ART AI sp0 SPB LB1 ((Fr, 1) :: LF) TRS1 B1 mm mo1 g1 -> (forall b, In b LR -> In b LB1) ->
    munch W mm mm' -> wmono bsegs mm mm' -> Forall pv_own_iv W ->
    pv_agree sp0 LR LF SP PB m mm -> pv_agree sp0 LR LF SP PB m mm'.
  Proof.
    intros W LB1 TRS1 B1 mm mm' mo1 g1 HL HLR MU WM HW PVA.
    eapply pv_agree_trans; [exact PVA|]. eapply magree_of_munch; [exact MU| exact WM|].
    intros a Ha [Hc Hn]. clear MU WM PVA. induction W as [|[u v] W IH]; [exact I|].
    apply Forall_cons_iff in HW as [H1 H2]. cbn. split; [| apply IH; exact H2].
    eapply pv_own_not_client; eauto.
  Qed.

  (* [comment removed for export] *)
  Lemma chain_cells_ext_below : forall mm mm' fl ch top,
    chain_cells mm ch -> chain_ok fl ch top -> Forall (fun x => fr_f x <= PB) ch ->
    (forall a, fl - 16 <= a < PB -> mm' (wa a) = mm (wa a)) -> chain_cells mm' ch.
  Proof.
    intros mm mm' fl ch. induction ch as [|[[f r] s] ch IH]; intros top CC CO FB E; [exact I|]. cbn in CC, CO |- *.
    destruct CC as [BY CC]. (nelim CO 8%nat; intros H1 H2 H3 H4 H5 H6 H7 H8).
    apply Forall_cons_iff in FB as [Hf FB]. unfold fr_f in Hf. cbn [fst snd] in Hf. split.
    - (nelim BY 3%nat; intros B0 B1 B2). split; [exact B0|]. split; [exact B1|]. intros i Hi.
      rewrite <- (B2 i Hi). unfold mrd. rewrite E; [reflexivity|].
      assert (Hi16 : (i < 16)%nat) by (clear -Hi; first [rewrite length_app, !length_le8 in Hi | idtac]; cbn in Hi; lia). lia.
    - eapply IH; eauto.
  Qed.

  Lemma pvm_chain_cells_store : forall W mm mm',
    chain_cells mm CH -> munch W mm mm' -> Forall pv_own_iv W -> chain_cells mm' CH.
  Proof.
    intros W mm mm' CC MU HW. lits. bandM. sepM. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM.
    eapply (chain_cells_ext_below mm mm' (SP + 16) CH (ASTACK_TOP sp0)); [exact CC| exact CHOK| exact CHB|].
    intros a Ha. apply MU. rewrite wa_unsigned by lia. clear MU CC.
    induction W as [|[u v] W IH]; [exact I|]. apply Forall_cons_iff in HW as [H1 H2]. cbn. split; [| apply IH; exact H2].
    unfold pv_own_iv in H1. cbn [fst snd] in H1. rewrite ?SHFR in H1. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pvm_sh_zero_store : forall W mm mm',
    sh_zero mm alloc_ceiling (2^47) -> munch W mm mm' -> Forall pv_own_iv W -> sh_zero mm' alloc_ceiling (2^47).
  Proof.
    intros W mm mm' SZ MU HW. lits. bandM. sepM. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM.
    eapply sh_zero_ext; [exact SZ|]. intros j Hj. apply MU.
    (nelimp SH_ceiling_bounds 3%nat; intros SC1 SC2 SC3). assert (R2 : SH (2^47 - 1) = 0x10007fff7fff) by reflexivity.   (* [comment removed for export] *)
    rewrite R2 in Hj. rewrite wa_unsigned by lia. unfold SH, SHADOW_OFFSET in Hj, SC1, SC2, SC3. clear MU SZ.
    induction W as [|[u v] W IH]; [exact I|]. apply Forall_cons_iff in HW as [H1 H2]. cbn. split; [| apply IH; exact H2].
    unfold pv_own_iv in H1. cbn [fst snd] in H1. rewrite ?SHFR in H1. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pvm_below_store : forall W mm mm',
    (SP + 16 <= PB -> pb_below mm PB) -> (PB = SP + 8 -> exists w : word, bytes_at bsegs mm SP (le8 w)) ->
    munch W mm mm' -> Forall pv_own_iv W ->
    (SP + 16 <= PB -> pb_below mm' PB) /\ (PB = SP + 8 -> exists w : word, bytes_at bsegs mm' SP (le8 w)).
  Proof.
    intros W mm mm' HB HW8 MU HW. lits. bandM. sepM. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM.
    assert (AG : forall a, SP <= a < PB -> mm' (wa a) = mm (wa a)).
    { intros a Ha. apply MU. rewrite wa_unsigned by lia. clear MU.
      induction W as [|[u v] W IH]; [exact I|]. apply Forall_cons_iff in HW as [H1 H2]. cbn. split; [| apply IH; exact H2].
      unfold pv_own_iv in H1. cbn [fst snd] in H1. rewrite ?SHFR in H1. Z.div_mod_to_equations. lia. }
    split.
    - intros H16. (nelim (HB H16) 4%nat; intros w1 w2 BY LE). exists w1, w2. split; [| exact LE].
      (nelim BY 3%nat; intros B0 B1 B2). split; [exact B0|]. split; [exact B1|]. intros i Hi.
      rewrite <- (B2 i Hi). unfold mrd. rewrite AG; [reflexivity|].
      assert (Hi16 : (i < 16)%nat) by (clear -Hi; first [rewrite length_app, !length_le8 in Hi | idtac]; cbn in Hi; lia). lia.
    - intros H8. (nelim (HW8 H8) 4%nat; intros w B0 B1 B2). exists w. split; [exact B0|]. split; [exact B1|]. intros i Hi.
      rewrite <- (B2 i Hi). unfold mrd. rewrite AG; [reflexivity|].
      assert (Hi8 : (i < 8)%nat) by (clear -Hi; first [rewrite length_le8 in Hi | idtac]; cbn in Hi; lia). lia.
  Qed.
End PV.


End CeilWrap.
