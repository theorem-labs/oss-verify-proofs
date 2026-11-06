(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel SFW1_lemmas InitMem Arr Mem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UMallocRep UMallocTree UMalloc_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RYajlRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UYajlAlign UYajl_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UY_rz UY_kit2 UF_strlen.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import RawAlloc Prelim YajlBase YajlBuf YajlLex YajlDecode YajlLeaf YajlFactsBuf YajlFactsLex YajlFactsDecode YajlFactsBits.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_secinst.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Export UY_decode3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma zbytes_firstn : forall k l, zbytes (firstn k l) = firstn k (zbytes l).
Proof. intros k l. unfold zbytes. rewrite firstn_map. reflexivity. Qed.
Lemma zbytes_skipn : forall k l, zbytes (skipn k l) = skipn k (zbytes l).
Proof. intros k l. unfold zbytes. rewrite skipn_map. reflexivity. Qed.

Lemma bytes_at_sub : forall m A bs i k,
  bytes_at usegs m A bs -> (i <= length bs)%nat -> bytes_at usegs m (A + Z.of_nat i) (firstn k (skipn i bs)).
Proof.
  intros m A bs i k HB Hi.
  rewrite <- (firstn_skipn i bs) in HB. apply bytes_at_app in HB. destruct HB as [_ HB].
  rewrite length_firstn, Nat.min_l in HB by lia.
  rewrite <- (firstn_skipn k (skipn i bs)) in HB. apply bytes_at_app in HB. destruct HB as [HB _]. exact HB.
Qed.

Lemma bytes_at_zslice : forall m A str i k,
  bytes_at usegs m A (zbytes str) -> 0 <= i <= zlength str -> bytes_at usegs m (A + i) (zbytes (zslice str i k)).
Proof.
  intros m A str i k HB Hi. unfold zslice. rewrite zbytes_firstn, zbytes_skipn.
  replace i with (Z.of_nat (Z.to_nat i)) at 1 by lia. apply bytes_at_sub; [exact HB|]. rewrite zbytes_length. unfold zlength in Hi. lia.
Qed.

Lemma Forall_firstn : forall {A} (P : A -> Prop) k l, Forall P l -> Forall P (firstn k l).
Proof. intros A P k l H. rewrite <- (firstn_skipn k l) in H. apply Forall_app in H. tauto. Qed.
Lemma Forall_skipn : forall {A} (P : A -> Prop) k l, Forall P l -> Forall P (skipn k l).
Proof. intros A P k l H. rewrite <- (firstn_skipn k l) in H. apply Forall_app in H. tauto. Qed.
Lemma Forall_zslice : forall (P : Z -> Prop) str i k, Forall P str -> Forall P (zslice str i k).
Proof. intros P str i k HF. unfold zslice. apply Forall_firstn, Forall_skipn. exact HF. Qed.

(* [comment removed for export] *)
Lemma yzext32_idiom : forall x, 0 <= x < 2^32 ->
  (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) ≪ 32)) ≫ 32) = x.
Proof.
  intros x Hx. rewrite (unsigned_lit x) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite unsigned_lit by (change (2^64) with (2^32 * 2^32); nia).
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.
Lemma yswrap32_small : forall x, -2^31 <= x < 2^31 -> bv_swrap 32 x = x.
Proof. intros x Hx. rewrite ybv_swrap32_eq. rewrite Z.mod_small by lia. lia. Qed.

(* [comment removed for export] *)
End RC__1.
Open Scope yprog_scope.

Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section S.
Variable HK : RawAlloc.PState -> list block -> (word -> option byte) -> Model -> Prop.
Hypothesis HKS : HK_silent_stmt HK.
Hypothesis HKP : HK_perm_stmt HK.
Hypothesis HKF : HK_frame_stmt HK.
Hypothesis HKB : HK_blocks_stmt HK.
Hypothesis YAP : ybuf_append_stmt HK.
Hypothesis YHX : yhexToDigit_stmt.

Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia; rewrite ?signed_of_Z by lia;
  try (change 18446744073709551615 with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia); lia.
(* [comment removed for export] *)
Ltac sb_store := unfold wz; rewrite le1_wz by lia; mem_after_store.
Ltac zle := apply Z.leb_le; vm_compute; reflexivity.
Ltac lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       end).

(* [comment removed for export] *)
#[local] Definition decode_exit := ltac2:(inst_sec '@UY_decode1.decode_exit).
#[local] Definition head_ok := ltac2:(inst_sec '@UY_decode1.head_ok).
#[local] Definition decode_step := ltac2:(inst_sec '@UY_decode3.decode_step).

Lemma ystring_decode_spec : ystring_decode_stmt HK.
Proof.
  unfold ystring_decode_stmt. intros REST mbd db AF S str n lo B errv K. intros until s.
  intros K0 UA RY BR BI U0 YAF AFIN TB SF NL N26 SNZ S62 SB TR YR FP A0 A1 A2 CONT.
  destruct FP as (AX & SPB & STK & CEIL & LO & ERR & MI & TP).
  apply RYST_split in RY. destruct RY as [HK0 YS].
  pose proof (proj1 STK) as LO0.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  destruct (HK_blocks HK HKB _ _ _ _ HK0) as [RNG SEP].
  rewrite (ry_errno_lit tp TP) in ERR. unfold RERRNO in ERR.
  pose proof (zlength_nonneg str) as NL0. pose proof (proj1 TB) as S0.
  subst a0 a1 a2. unfold RY_STRING_DECODE, RY_DECODE_STACK, RY_BUF_APPEND_STACK, RY_WRAP_STACK, alloc_ceiling, wz in *.
  (* [comment removed for export] *)
  assert (AFC : AF + 32 <= (Z.max 0x7fff80000000 (Z.min 0x800000000000 rc_sp) - 8388608)).
  { destruct AFIN as (hb & HBI & HB1 & HB2).
    pose proof (all_range_In _ _ RNG ltac:(apply in_or_app; right; exact HBI)) as Hbr. unfold rblock_range, alloc_ceiling in Hbr. lia. }
  assert (STXT : 0 < n -> S + n <= (Z.max 0x7fff80000000 (Z.min 0x800000000000 rc_sp) - 8388608)).
  { intros NP. destruct TR as [(bt & HBT & T1 & T2)|N0]; [| lia].
    pose proof (all_range_In _ _ RNG ltac:(apply in_or_app; right; exact HBT)) as Hbr. unfold rblock_range, alloc_ceiling in Hbr. lia. }
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -208)) = bv_unsigned sp + -208) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(bv_unsigned sp + -208, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  (* [comment removed for export] *)
  assert (OWN : forall mx, munch [(bv_unsigned sp + -208, bv_unsigned sp)] m mx -> wmono usegs m mx ->
            (HK s (buf_blocks mbd db ++ REST) mx mo /\ rauxv_ok mx B) /\ ystatics mx /\ ry_pres REST (bv_unsigned sp) [] m mx
            /\ buf_rep usegs mx mbd db AF /\ bytes_at usegs mx S (zbytes str)
            /\ rw_cells usegs mx 218620 [C4 errv] /\ rw_cells usegs mx AF (alloc_cells ryc)).
  { intros mx MU1 WM1. split; [| split; [| split; [| split; [| split; [| split]]]]].
    - eapply (yown_writes HK HKF); [exact HK0| exact AX| exact MU1| exact WM1| |].
      + constructor; [left; cbn; unfold alloc_ceiling; lia| constructor].
      + constructor; [cbn; unfold RAUXV_CELL; lia| constructor].
    - eapply ystatics_munch; [exact YS| exact MU1| exact WM1|]. constructor; [cbn; unfold RY_CALLBACKS; lia| constructor].
    - eapply ryajl_pres_of_munch; [exact MU1| exact WM1|]. intros a Ha Hc _. cbn. split; [| exact I].
      destruct Hc as [Hc|[Hc|(bq & Hb & Hr)]]; [lia| unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in Hc; lia|].
      pose proof (all_range_In _ _ RNG ltac:(apply in_or_app; right; exact Hb)) as Hbr. unfold rblock_range, alloc_ceiling in Hbr. lia.
    - eapply (buf_rep_transport_hi _ _ _ _ _ _ _ BR MU1 WM1); [exact RNG| intros bq Hq; apply in_or_app; left; exact Hq|].
      constructor; [cbn; unfold alloc_ceiling; lia| constructor].
    - destruct str as [|c0 str'] eqn:ES.
      + destruct TB as (B0 & B1 & _). split; [exact B0|]. split; [exact B1|]. intros i Hi. cbn in Hi. lia.
      + eapply (bytes_at_transport usegs); [exact TB| exact MU1|]. rewrite zbytes_length.
        assert (NP : 0 < n) by (rewrite NL; unfold zlength; cbn; lia). specialize (STXT NP). rewrite NL in STXT. unfold zlength in STXT.
        apply disjoint_from_above. constructor; [cbn [fst]; lia| constructor].
    - eapply (rw_cells_transport usegs); [exact ERR| exact MU1| exact WM1|]. cbv [disjoint_from fst snd]. cbn [cells_size csize Nat.add length]. lia.
    - eapply (rw_cells_transport usegs); [exact YAF| exact MU1| exact WM1|]. cbv [disjoint_from fst snd]. cbn [cells_size csize Nat.add length]. unfold alloc_cells. cbn [cells_size csize Nat.add length]. lia. }
  yhide TB. yhide YAF. yhide ERR. clear AX.
  rz_seg HKS HK0.
  step. carve_frame 208%nat STK.
  step. step. step. step. step. step. step. step. step. step. step. step. step.
  step. step.
  step. if_cases K1; zify_cond K1.
  - (* [comment removed for export] *)
    step. step. apply evt_done.
    destruct (OWN _ MU WM) as ([HK1 AX1] & YS1 & PRES1 & BR1 & TB1 & ERR1 & YAF1). clear OWN TB YAF ERR.
    lazymatch goal with |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
      eapply (decode_exit REST mbd db AF S str n lo B errv K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
        with (m1 := mx) (mo1 := mo) (s1' := s) (b := db) (mb := mbd) (LK := []) (errv1 := errv) end.
    all: lazymatch goal with
         | |- forall bf, yleaf _ bf -> _ => intros bf Hbf; unfold ystring_decode; eapply yleaf_bind; [apply dlf_exit; lia|]; cbv beta iota; exact Hbf
         | |- mb_same _ _ => split; reflexivity
         | |- HK _ _ _ _ => exact HK1
         | |- _ => first [ exact CONT | exact UA | reflexivity | eassumption | lia ]
         end.
  - (* [comment removed for export] *)
    step. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step.
    step. step. lit_store. step. step. lit_store. step. step. lit_store. step. step. lit_store. step. step. lit_store.
    step. step. lit_store. step. step. lit_store. step. step. lit_store. step. step. lit_store. step. step. lit_store.
    apply evt_done.
    destruct (OWN _ MU WM) as ([HK1 AX1] & YS1 & PRES1 & BR1 & TB1 & ERR1 & YAF1). clear OWN TB YAF ERR.
    assert (HOK : forall f, head_ok REST mbd db AF S str n lo B K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f).
    { induction f as [|f IH].
      - unfold head_ok, UY_decode1.head_ok, UY_decode2.head_ok, UY_decode3.head_ok. intros. exfalso. lia.
      - eapply (decode_step REST mbd db AF S str n lo B errv K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m).
        all: first [ exact IH | exact CONT | exact UA | eassumption | lia ]. }
    rewrite !(unsigned_lit S) by lia. rewrite zb_lxor_ones by lia. rewrite v_sltu_b2z. rewrite (unsigned_lit 0), (unsigned_lit S) by lia.
    replace (0 <? S) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
    lazymatch goal with FR : rw_cells _ ?mx (bv_unsigned sp + -208) (CB 8 ?a :: _) |- _ =>
      lazymatch type of FR with context [CB 16 ?c] =>
        eapply (HOK (decode_fuel n) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx mo s errv db mbd [] 0 0 a c);
          [ reflexivity | exact HK1 | exact YS1 | exact FR | | | exact AX1 | exact ERR1 | exact PRES1 | exact YAF1 | exact TB1
          | exact BR1 | exact BI | split; reflexivity | lia | lia | lia | exact SB | unfold decode_fuel; lia | intros r Hr; exact Hr ]
      end end.
    all: assumption.
Qed.
End S.
End RC__2.
