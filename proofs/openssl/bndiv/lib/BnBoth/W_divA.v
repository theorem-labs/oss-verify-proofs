(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA ZBridge RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Malloc Prog BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import BnDivWords BnDivLoop BnSpecs2 BnDivSpec.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require StrFun.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnMem BnTacX BnArith.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnKit2 BnArr BnLeaves ShiftPure DivModel DivLoopPure DivTop.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA BnRepX ImplA ImplAX BnIfaceA UnwindA EdgesA AsStruct RtCallA W_cryptoA W_expandA W_smallA BnAKitA BnCallA AsStruct2 AW_num_bits_word AW_div_la W_lshiftA W_rshiftA W_copyA W_ctxA W_ctx_endA W_ctx_getA W_div_tailA W_div_padA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import UbKit UbStruct.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2434852 => 1
  | 2434856 => 2
  | 2434912 => 2
  | 2434924 => 1
  | 2434932 => 2
  | 2434940 => 1
  | 2434944 => 1
  | 2434948 => 1
  | 2434952 => 2
  | 2434956 => 2
  | 2434960 => 1
  | 2434964 => 2
  | 2435000 => 1
  | 2435004 => 2
  | 2435064 => 2
  | 2435088 => 2
  | 2435116 => 2
  | 2435192 => 1
  | 2435196 => 2
  | 2435200 => 1
  | 2435204 => 1
  | 2435208 => 2
  | 2435276 => 2
  | 2435328 => 1
  | 2435336 => 2
  | 2435340 => 1
  | 2435344 => 1
  | 2435348 => 1
  | 2435352 => 1
  | 2435356 => 2
  | 2435368 => 1
  | 2435372 => 2
  | 2435376 => 1
  | 2435384 => 2
  | 2435428 => 1
  | 2435436 => 2
  | 2435472 => 1
  | 2435480 => 1
  | 2435484 => 2
  | 2435488 => 1
  | 2435492 => 1
  | 2435496 => 1
  | 2435500 => 1
  | 2435504 => 1
  | 2435508 => 1
  | 2435512 => 2
  | 2435520 => 2
  | 2435536 => 1
  | 2435540 => 2
  | 2435544 => 1
  | 2435548 => 1
  | 2435552 => 1
  | 2435556 => 1
  | 2435560 => 1
  | 2435564 => 2
  | 2435588 => 2
  | 2435608 => 1
  | 2435616 => 2
  | 2435620 => 1
  | 2435624 => 1
  | 2435628 => 1
  | 2435632 => 1
  | 2435636 => 2
  | 2435640 => 2
  | 2435644 => 1
  | 2435648 => 2
  | 2435696 => 2
  | 2435708 => 2
  | 2435712 => 1
  | 2435720 => 1
  | 2435724 => 1
  | 2435728 => 2
  | 2435732 => 1
  | 2435736 => 2
  | 2435784 => 1
  | 2435788 => 2
  | 2435792 => 1
  | 2435796 => 1
  | 2435800 => 2
  | 2435828 => 2
  | 2435832 => 1
  | 2435836 => 2
  | 2435840 => 2
  | 2435844 => 1
  | 2435848 => 2
  | 2435964 => 1
  | 2435968 => 1
  | 2435972 => 2
  | 2435976 => 1
  | 2435980 => 1
  | 2435984 => 1
  | 2435988 => 2
  | 2436148 => 2
  | 2436152 => 1
  | 2436156 => 2
  | 2436176 => 1
  | 2436180 => 2
  | 2436236 => 1
  | 2436240 => 2
  | 2436244 => 1
  | 2436248 => 2
  | 2436464 => 1
  | 2436468 => 2
  | 2436536 => 1
  | 2436540 => 1
  | 2436544 => 2
  | 2436548 => 1
  | 2436556 => 1
  | 2436560 => 1
  | 2436564 => 2
  | 2436568 => 2
  | 2436572 => 1
  | 2436576 => 2
  | 2436600 => 1
  | 2436604 => 1
  | 2436608 => 2
  | 2436696 => 2
  | 2436700 => 1
  | 2436704 => 1
  | 2436708 => 2
  | 2436712 => 2
  | 2436748 => 2
  | 2436752 => 1
  | 2436756 => 1
  | 2436760 => 1
  | 2436764 => 2
  | 2436768 => 2
  | 2436772 => 1
  | 2436776 => 1
  | 2436780 => 2
  | 2436876 => 1
  | 2436880 => 2
  | 2436884 => 1
  | 2436888 => 2
  | 2436928 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.
Ltac hide_ors := repeat match goal with H : _ \/ _ |- _ => apply hide_intro in H end.
Ltac unhide := repeat match goal with H : hide (_ \/ _) |- _ => apply hide_elim in H end.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma la_run : forall r (ls : lstate bptr),
  bn_left_align (tree_ops bptr) r ls =
  TRet (64 - num_bits_word (nth (bn_top (getbn r ls) - 1) (bn_buf (getbn r ls)) 0),
        setbn r (bn_with_buf (getbn r ls) (splice (bn_buf (getbn r ls)) 0
                   (fst (lshift_limbs (firstn (bn_top (getbn r ls)) (bn_buf (getbn r ls))) (64 - num_bits_word (nth (bn_top (getbn r ls) - 1) (bn_buf (getbn r ls)) 0)) 0)))) ls).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma shr3_shad : forall X, 0 <= X -> X ≫ 3 + SHB = shad X.
Proof. intros X HX. unfold shad. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. lia. Qed.

(* [comment removed for export] *)
Lemma dv_ble_range : forall bs : list byte, 0 <= bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat (length bs)).
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z length]; [cbn; lia|].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8) with (2 ^ 8) in Hb.
  assert (Hs : 0 <= Z.shiftl (bytes_le_to_Z bs) 8) by (apply Z.shiftl_nonneg; lia).
  split. { apply Z.lor_nonneg. lia. }
  pose proof (Z.add_lor_land (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as E.
  pose proof (Z.land_nonneg (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as L.
  rewrite Z.shiftl_mul_pow2 in * by lia.
  assert (LD : Z.land (bv_unsigned b) (bytes_le_to_Z bs * 2 ^ 8) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases n 8) as [Hlt|Hge].
    - rewrite (Z.mul_pow2_bits_low _ 8 n) by lia. apply andb_false_r.
    - replace (Z.testbit (bv_unsigned b) n) with false; [reflexivity|]. symmetry. apply Z.bits_above_log2; [lia|].
      assert (Z.log2 (bv_unsigned b) < 8); [|lia]. destruct (Z.eq_dec (bv_unsigned b) 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
  rewrite LD in E. replace (8 * Z.of_nat (S (length bs))) with (8 + 8 * Z.of_nat (length bs)) by lia. rewrite Z.pow_add_r by lia. nia.
Qed.
Lemma dv_le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (dv_ble_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply StrFun.Z_to_le_bytes_to_Z.
Qed.
Lemma rw_cells_CB8_hd : forall segs m A bs rest, rw_cells segs m A (CB 8 bs :: rest) -> rw_cells segs m A (C8 (le_bytes_to_word bs) :: rest).
Proof.
  intros segs m A bs rest H. pose proof H as [[[L W] _] _].
  eapply bk_rw_cells_recast; [exact H | cbn; split; [exact I | exact W] | cbn [cells_bytes cbytes]; rewrite dv_le8_of_bytes by exact L; reflexivity | reflexivity].
Qed.

Definition BN_DIV_FT_COST : Z := 10 * MC.
Definition nonpool (r : bnref) : Prop := forall i, r <> RPool i.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Notation E_dv_start := (E_bn_div_fixed_top_24f27c : uk_call BN_DIV_FIXED_TOP 0x2526d8 BN_CTX_START).
Local Notation E_dv_get2 := (E_bn_div_fixed_top_24f294 : uk_call BN_DIV_FIXED_TOP 0x2526f0 BN_CTX_GET).
Local Notation E_dv_get3 := (E_bn_div_fixed_top_24f2a0 : uk_call BN_DIV_FIXED_TOP 0x2526fc BN_CTX_GET).
Local Notation E_dv_get4 := (E_bn_div_fixed_top_24f2ac : uk_call BN_DIV_FIXED_TOP 0x252708 BN_CTX_GET).
Local Notation E_dv_copy := (E_bn_div_fixed_top_24f2bc : uk_call BN_DIV_FIXED_TOP 0x25271c BN_COPY).
Local Notation E_dv_lshift := (E_bn_div_fixed_top_24f3bc : uk_call BN_DIV_FIXED_TOP 0x252868 BN_LSHIFT).
Local Notation E_dv_wexp2 := (E_bn_div_fixed_top_24f4e8 : uk_call BN_DIV_FIXED_TOP 0x252ac4 BN_WEXPAND).
Local Notation E_dv_wexp3 := (E_bn_div_fixed_top_24f580 : uk_call BN_DIV_FIXED_TOP 0x252bac BN_WEXPAND).

Lemma bn_div_fixed_top_walkA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
    (lo : Z) (ras : list Z) (dv rm num dvs : bnref) (adv arm anum advs : Z),
  bn_preA Σ ls m OW LB AD EA sp lo BN_DIV_FT_STACK BN_DIV_FT_COST ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_DIV_FIXED_TOP (bv_unsigned ra :: ras) ->
  tp = wz TP_A ->
  ref_at ls OW AD dv adv -> ref_at ls OW AD rm arm -> ref_at ls OW AD num anum -> ref_at ls OW AD dvs advs ->
  a0 = wz adv -> a1 = wz arm -> a2 = wz anum -> a3 = wz advs -> a4 = wz (ad_ctx AD) ->
  nonpool dv -> nonpool rm -> nonpool num -> nonpool dvs -> dv <> num -> dv <> dvs ->
  (1 <= bn_top (getbn dvs ls))%nat -> nth (bn_top (getbn dvs ls) - 1) (bn_buf (getbn dvs ls)) 0 <> 0 ->
  implA (bn_div_fixed_top (tree_ops bptr) dv rm num dvs ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m AD EA BN_DIV_FT_COST (fun _ _ _ a0' => a0' = wz 1))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_DIV_FIXED_TOP) fc None m (seg_rom bsegs)).
Proof.
  intros until advs. intros PRE UW CTX -> HAdv HArm HAnum HAdvs -> -> -> -> -> NPdv NPrm NPnum NPdvs NEdn NEdd HTOPD HTOPNZ.
  pose proof PRE as (HEAP & LS & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED).
  pose proof LO as LO'.
  unfold BN_DIV_FT_STACK, BN_LSHIFT_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK in LO.
  unfold BN_DIV_FIXED_TOP, MallocRep.wz.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, SPT.
  unfold bn_div_fixed_top.
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  pose proof (munch_refl [(bv_unsigned sp - 304, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  apply implA_from_evt.
  carve_frame 304%nat ST. do 15 step. do 2 step. do 2 step. do 3 step. do 3 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -304)) = bv_unsigned sp + -304) by (apply unsigned_lit; lia).
  assert (HWL : Forall (w_lib OW lo (bv_unsigned sp)) [(bv_unsigned sp + -304, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
  assert (WOK : Forall (w_ok OW LB ls AD EA []) [(bv_unsigned sp + -304, bv_unsigned sp)]).
  { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
  pose proof (lib_state_frame Σ LB [] ls m m1 OW AD EA _ HEAP LS MU WM WOK) as LS1.
  lazymatch type of FR with rw_cells _ _ _ (?fr ++ _) => idtac | rw_cells _ _ _ ?fr =>
    let pre := drop2 fr in
    assert (ENV : cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -304) s0 ra (Some ras) BN_DIV_FT_COST Σ ls OW m pre 0 Σ ls m1 OW)
  end.
  { unfold cenvA, cenv_ok. split; [repeat split; try assumption; try (unfold USTACK_TOP; lia); clear - SP16; Z.div_mod_to_equations; lia|].
    split; [exact (seg_heap _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia))|].
    split; [exact ST|]. split; [exact MI|].
    split; [exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ HEAP MU HWL CEIL ltac:(lia))|].
    split; [lia|]. split; [apply cnt_eq_refl|]. split; [apply refs_stable_refl|].
    split; [cbn [app]; exact FR|]. split; [cbn; lia|]. unfold uw_opt.
    eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor]. }
  pose proof ENV as (OK & HEAP1 & _).
  assert (HWLs : forall OWx, Forall (w_lib OWx lo (bv_unsigned sp)) [(bv_unsigned sp + -304, bv_unsigned sp)]) by (intros OWx; constructor; [left; cbn; lia| constructor]).
  assert (WOKs : forall OWx lsx, Forall (w_ok OWx LB lsx AD EA []) [(bv_unsigned sp + -304, bv_unsigned sp)]).
  { intros OWx lsx; constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
  clear HEAP LS ST MI MU WM HWL WOK FR PRE SHB1 SHB2.
  (* [comment removed for export] *)
  apply evt_done. unfold bbind at 1. cbn [bind tree_ops].
  eapply implA_bind.
  { eapply implA_leaves; [apply (BN_CTX_start_leaves ls)|].
    eapply (BN_CTX_start_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW) (LB := LB) (AD := AD) (EA := EA); [| | | reflexivity | reflexivity].
    - eapply cenv_preA; [exact ENV | exact LS1 | unfold BN_CTX_START_STACK, CRYPTO_MALLOC_ARRAY_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO; lia | unfold BN_DIV_FT_COST, MC; lia].
    - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ENV).
    - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_dv_start CTX). }
  cbv beta. intros [u1 ls2] Σ2 ms2 [PO LEAF2].
  apply (bn_postA_cpost LB AD EA lo (bv_unsigned sp) (bv_unsigned sp + -304) BN_DIV_FT_COST Σ ls OW) in PO; [| exact OK | exact HEAP1].
  cbn [fst snd] in *.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F2 & fc2 & m2 & OW2 & -> & CP2 & _).
  lazymatch type of ENV with cenvA _ _ _ _ _ _ _ _ _ _ _ _ _ ?pre _ _ _ _ _ =>
    assert (E2 : cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -304) s0 ra (Some ras) BN_DIV_FT_COST Σ ls OW m pre (0 + MC) Σ2 ls2 m2 OW2 /\ lib_state ls2 m2 OW2 AD EA)
      by (eapply cenv_postA; [exact ENV | exact CP2]) end.
  destruct E2 as (ENV2 & LS2).
  pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP2) as RS2.
  rewrite (ret_pc_even 0x2526d8) by lia. unfold MallocRep.wz.
  clear ENV LS1 CP2 HEAP1 m1.
  (* [comment removed for export] *)
  destruct (lib_state_h_parts _ _ _ _ _ _ LS2) as (IDS2 & ADB2 & ERRB2 & SOK2).
  assert (HAdv2 : ref_at ls2 OW2 AD dv adv) by (apply RS2; exact HAdv).
  destruct (ref_at_inb _ _ _ _ _ ADB2 HAdv2) as (qd & Ad & nd & _ & Hind & Rd1 & Rd2).
  pose proof (AH_range _ _ _ _ _ _ _ (proj1 (proj2 ENV2)) Hind) as (DA0 & _ & _ & DAC & _).
  apply implA_from_evt.
  zstep. if_cases KD; zify_cond KD. 2:{ exfalso. rewrite ?unsigned_lit in KD by lia. unfold BnHeapA.ACEIL in *. lia. }
  clear KD qd Ad nd Hind Rd1 Rd2 DA0 DAC.
  do 2 zstep.
  (* [comment removed for export] *)
  destruct SOK2 as (_ & _ & _ & _ & _ & _ & CK2).
  apply evt_done. unfold bbind at 1. cbn [bind tree_ops].
  eapply implA_bind.
  { eapply implA_leaves; [apply (BN_CTX_get_leaves ls2); exact (proj1 (proj2 (proj2 CK2)))|].
    eapply (BN_CTX_get_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW2) (LB := LB) (AD := AD) (EA := EA); [| | | reflexivity | reflexivity].
    - eapply cenv_preA; [exact ENV2 | exact LS2 | unfold BN_CTX_GET_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO; lia | unfold BN_DIV_FT_COST, MC; lia].
    - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ENV2).
    - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_dv_get2 CTX). }
  cbv beta. intros [tmp ls3] Σ3 ms3 [PO LEAF3].
  apply (bn_postA_cpost LB AD EA lo (bv_unsigned sp) (bv_unsigned sp + -304) BN_DIV_FT_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 ENV2))].
  cbn [fst snd] in *.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F3 & fc3 & m3 & OW3 & -> & CP3 & ((atmp & HAtmp & ->) & _)).
  lazymatch type of ENV2 with cenvA _ _ _ _ _ _ _ _ _ _ _ _ _ ?pre _ _ _ _ _ =>
    assert (E3 : cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -304) s0 ra (Some ras) BN_DIV_FT_COST Σ ls OW m pre (0 + MC + MC) Σ3 ls3 m3 OW3 /\ lib_state ls3 m3 OW3 AD EA)
      by (eapply cenv_postA; [exact ENV2 | exact CP3]) end.
  destruct E3 as (ENV3 & LS3).
  pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP3) as RS3.
  rewrite (ret_pc_even 0x2526f0) by lia. unfold MallocRep.wz.
  clear ENV2 LS2 CP3 m2 CK2 IDS2 ADB2 ERRB2.
  (* [comment removed for export] *)
  apply implA_from_evt.
  do 3 zstep.
  (* [comment removed for export] *)
  destruct (lib_state_h_parts _ _ _ _ _ _ LS3) as (_ & _ & _ & (_ & _ & _ & _ & _ & _ & CK4)).
  apply evt_done. unfold bbind at 1. cbn [bind tree_ops].
  eapply implA_bind.
  { eapply implA_leaves; [apply (BN_CTX_get_leaves ls3); exact (proj1 (proj2 (proj2 CK4)))|].
    eapply (BN_CTX_get_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW3) (LB := LB) (AD := AD) (EA := EA); [| | | reflexivity | reflexivity].
    - eapply cenv_preA; [exact ENV3 | exact LS3 | unfold BN_CTX_GET_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO; lia | unfold BN_DIV_FT_COST, MC; lia].
    - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ENV3).
    - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_dv_get3 CTX). }
  cbv beta. intros [snum ls4] Σ4 ms4 [PO LEAF4].
  apply (bn_postA_cpost LB AD EA lo (bv_unsigned sp) (bv_unsigned sp + -304) BN_DIV_FT_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 ENV3))].
  cbn [fst snd] in *.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F4 & fc4 & m4 & OW4 & -> & CP4 & ((asnum & HAsnum & ->) & _)).
  lazymatch type of ENV3 with cenvA _ _ _ _ _ _ _ _ _ _ _ _ _ ?pre ?u _ _ _ _ =>
    assert (E4 : cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -304) s0 ra (Some ras) BN_DIV_FT_COST Σ ls OW m pre (u + MC) Σ4 ls4 m4 OW4 /\ lib_state ls4 m4 OW4 AD EA)
      by (eapply cenv_postA; [exact ENV3 | exact CP4]) end.
  destruct E4 as (ENV4 & LS4).
  pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP4) as RS4.
  rewrite (ret_pc_even 0x2526fc) by lia. unfold MallocRep.wz.
  clear CP4 CK4.
  (* [comment removed for export] *)
  env_openA ENV4. apply implA_from_evt.
  step. do 2 zstep.
  env_closeA HWLs WOKs ENV4 LS4 ENV4' LS4'.
  (* [comment removed for export] *)
  destruct (lib_state_h_parts _ _ _ _ _ _ LS4') as (_ & _ & _ & (_ & _ & _ & _ & _ & _ & CK5)).
  apply evt_done. unfold bbind at 1. cbn [bind tree_ops].
  eapply implA_bind.
  { eapply implA_leaves; [apply (BN_CTX_get_leaves ls4); exact (proj1 (proj2 (proj2 CK5)))|].
    eapply (BN_CTX_get_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW4) (LB := LB) (AD := AD) (EA := EA); [| | | reflexivity | reflexivity].
    - eapply cenv_preA; [exact ENV4' | exact LS4' | unfold BN_CTX_GET_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO; lia | unfold BN_DIV_FT_COST, MC; lia].
    - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ENV4').
    - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_dv_get4 CTX). }
  cbv beta. intros [sdiv ls5] Σ5 ms5 [PO LEAF5].
  apply (bn_postA_cpost LB AD EA lo (bv_unsigned sp) (bv_unsigned sp + -304) BN_DIV_FT_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 ENV4'))].
  cbn [fst snd] in *.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F5 & fc5 & m5 & OW5 & -> & CP5 & ((asdiv & HAsdiv & ->) & _)).
  lazymatch type of ENV4' with cenvA _ _ _ _ _ _ _ _ _ _ _ _ _ ?pre ?u _ _ _ _ =>
    assert (E5 : cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -304) s0 ra (Some ras) BN_DIV_FT_COST Σ ls OW m pre (u + MC) Σ5 ls5 m5 OW5 /\ lib_state ls5 m5 OW5 AD EA)
      by (eapply cenv_postA; [exact ENV4' | exact CP5]) end.
  destruct E5 as (ENV5 & LS5).
  pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP5) as RS5.
  rewrite (ret_pc_even 0x252708) by lia. unfold MallocRep.wz.
  clear CP5 CK5.
  (* [comment removed for export] *)
  destruct LEAF2 as (L2a & L2b & _ & _). destruct LEAF3 as (L3a & L3b & _ & L3d). destruct LEAF4 as (L4a & L4b & _ & L4d). destruct LEAF5 as (L5a & L5b & _ & L5d).
  cbn [fst snd] in *.
  set (p0 := cx_pused (ls_ctx ls2)) in *.
  rewrite L3b in L4a. rewrite L4b, L3b in L5a.
  assert (NPget : forall r, nonpool r -> getbn r ls5 = getbn r ls).
  { intros r NP. rewrite L5d by (rewrite L4b, L3b; apply NP). rewrite L4d by (rewrite L3b; apply NP). rewrite L3d by apply NP. apply L2a. }
  assert (Etmp5 : getbn tmp ls5 = getbn tmp ls3).
  { rewrite L5d by (rewrite L4b, L3b, L3a; intros E; injection E; lia). rewrite L4d by (rewrite L3b, L3a; intros E; injection E; lia). reflexivity. }
  pose proof (RS5 _ _ (RS4 _ _ (RS3 _ _ (RS2 _ _ HAdv)))) as HAdv5. pose proof (RS5 _ _ (RS4 _ _ (RS3 _ _ (RS2 _ _ HArm)))) as HArm5.
  pose proof (RS5 _ _ (RS4 _ _ (RS3 _ _ (RS2 _ _ HAnum)))) as HAnum5. pose proof (RS5 _ _ (RS4 _ _ (RS3 _ _ (RS2 _ _ HAdvs)))) as HAdvs5.
  pose proof (RS5 _ _ (RS4 _ _ HAtmp)) as HAtmp5. pose proof (RS5 _ _ HAsnum) as HAsnum5.
  assert (NEts : tmp <> snum) by (rewrite L3a, L4a; intros E; injection E; lia).
  assert (NEtd : tmp <> sdiv) by (rewrite L3a, L5a; intros E; injection E; lia).
  assert (NEsd : snum <> sdiv) by (rewrite L4a, L5a; intros E; injection E; lia).
  assert (NPt : forall r, nonpool r -> r <> tmp) by (intros r NP; rewrite L3a; apply NP).
  assert (NPs : forall r, nonpool r -> r <> snum) by (intros r NP; rewrite L4a; apply NP).
  assert (NPd : forall r, nonpool r -> r <> sdiv) by (intros r NP; rewrite L5a; apply NP).
  clear L2a L2b L3a L3b L3d L4a L4b L4d L5a L5b L5d p0 RS2 RS3 RS4 RS5 HAdv2 HAtmp HAsnum ENV3 LS3 ENV4 LS4 ENV4' LS4'.
  clear HAdv HArm HAnum HAdvs.
  (* [comment removed for export] *)
  destruct (lib_state_h_parts _ _ _ _ _ _ LS5) as (IDS5 & ADB5 & ERRB5 & SOK5).
  destruct (ref_at_inb _ _ _ _ _ ADB5 HAsdiv) as (qd & Ad & nd & _ & Hind & Rd1 & Rd2).
  pose proof (AH_range _ _ _ _ _ _ _ (proj1 (proj2 ENV5)) Hind) as (DA0 & _ & _ & DAC & _).
  env_openA ENV5. apply implA_from_evt.
  step.
  zstep. if_cases KD; zify_cond KD. { exfalso. rewrite ?unsigned_lit in KD by lia. unfold BnHeapA.ACEIL in *. lia. }
  clear KD qd Ad nd Hind Rd1 Rd2 DA0 DAC.
  step. do 2 zstep.
  env_closeA HWLs WOKs ENV5 LS5 ENV5' LS5'.
  clear LS5. rename LS5' into LS5.
  (* [comment removed for export] *)
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS5 HAsdiv) as HVsd5. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS5 HAdvs5) as HVdvs5.
  pose proof (st_okm_getbn sdiv ls5 SOK5 HVsd5) as (_ & OKsd2 & _). pose proof (st_okm_getbn dvs ls5 SOK5 HVdvs5) as (OKdv1 & OKdv2 & OKdv3 & _).
  apply evt_done. unfold bbind at 1. cbn [bind tree_ops].
  eapply implA_bind.
  { eapply implA_leaves; [apply (BN_copy_leaves sdiv dvs ls5 (fun E => NPd dvs NPdvs (eq_sym E)) HVsd5 OKsd2 OKdv2)|].
    eapply (BN_copy_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW5) (LB := LB) (AD := AD) (EA := EA) (rx := sdiv) (ry := dvs) (ax := asdiv) (ay := advs);
      [| | | reflexivity | exact HAsdiv | exact HAdvs5 | reflexivity | reflexivity].
    - eapply cenv_preA; [exact ENV5' | exact LS5 | unfold BN_COPY_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO; lia | unfold BN_DIV_FT_COST, MC; lia].
    - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ENV5').
    - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_dv_copy CTX). }
  cbv beta. intros [u6 ls6] Σ6 ms6 [PO LEAF6].
  apply (bn_postA_cpost LB AD EA lo (bv_unsigned sp) (bv_unsigned sp + -304) BN_DIV_FT_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 ENV5'))].
  cbn [fst snd] in *.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F6 & fc6 & m6 & OW6 & -> & CP6 & (-> & _)).
  lazymatch type of ENV5' with cenvA _ _ _ _ _ _ _ _ _ _ _ _ _ ?pre ?u _ _ _ _ =>
    assert (E6 : cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -304) s0 ra (Some ras) BN_DIV_FT_COST Σ ls OW m pre (u + MC) Σ6 ls6 m6 OW6 /\ lib_state ls6 m6 OW6 AD EA)
      by (eapply cenv_postA; [exact ENV5' | exact CP6]) end.
  destruct E6 as (ENV6 & LS6).
  pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP6) as RS6.
  rewrite (ret_pc_even 0x25271c) by lia. unfold MallocRep.wz.
  clear CP6.
  (* [comment removed for export] *)
  destruct LEAF6 as (C6a & C6b & C6c & C6d & C6e & _). cbn [snd] in *.
  pose proof (RS6 _ _ HAdv5) as HAdv6. pose proof (RS6 _ _ HArm5) as HArm6. pose proof (RS6 _ _ HAnum5) as HAnum6. pose proof (RS6 _ _ HAdvs5) as HAdvs6.
  pose proof (RS6 _ _ HAtmp5) as HAtmp6. pose proof (RS6 _ _ HAsnum5) as HAsnum6. pose proof (RS6 _ _ HAsdiv) as HAsdiv6.
  assert (NPget6 : forall r, nonpool r -> getbn r ls6 = getbn r ls) by (intros r NP; rewrite C6a by (apply not_eq_sym, NPd, NP); apply NPget; exact NP).
  rewrite (NPget dvs NPdvs) in C6b, C6c, C6d, C6e, OKdv1, OKdv2, OKdv3.
  set (bd := getbn dvs ls) in *. set (dn := bn_top bd) in *.
  clear RS6 HAdv5 HArm5 HAnum5 HAdvs5 HAtmp5 HAsnum5 HAsdiv ENV5 ENV5' LS5 IDS5 ADB5 ERRB5 SOK5 HVsd5 HVdvs5 OKsd2 NPget.
  pose proof (AH_nodup_l _ _ _ _ (proj1 (proj2 ENV6))) as ND6.
  destruct (lib_state_h_parts _ _ _ _ _ _ LS6) as (IDS6 & ADB6 & ERRB6 & SOK6).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS6 HAsdiv6) as HVsd6.
  destruct (lib_state_open [] ls6 m6 OW6 AD EA sdiv asdiv LS6 ND6 HAsdiv6 ltac:(intros [])) as ((Dsd & BNsd & ARRsd) & (OKs1 & OKs2 & OKs3 & OKs4) & LSH6).
  set (b6 := getbn sdiv ls6) in *.
  destruct (bn_arr_facts Σ6 OW6 LB m6 (proj1 (proj2 ENV6)) ls6 AD EA IDS6 ADB6 sdiv Dsd HVsd6 ARRsd) as (Usd & LENsd & Dsd0 & DsdC & DsdI & DSEPsd).
  fold b6 in Usd, LENsd, DsdC, DsdI, DSEPsd.
  pose proof (DSEPsd sdiv asdiv HAsdiv6) as SEPsd. clear DSEPsd.
  destruct (ref_at_inb _ _ _ _ _ ADB6 HAsdiv6) as (qsd & Asd & nsd & _ & Hinsd & Rsd1 & Rsd2).
  pose proof (AH_range _ _ _ _ _ _ _ (proj1 (proj2 ENV6)) Hinsd) as (SDA0 & _ & _ & SDAC & SDAI).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ (proj1 (proj2 ENV6)) LS6 HAsdiv6) as (ACVA & ALVA & OFVA).
  destruct (arr_shA _ _ _ _ _ _ (proj1 (proj2 ENV6)) ARRsd) as (ACV & ALV & OFV). fold b6 in ACV, OFV.
  assert (HDsd : exists psd, bn_d b6 = Some psd /\ In (psd, Dsd, 8 * Z.of_nat (bn_dmax b6)) OW6).
  { unfold bn_arr in ARRsd. destruct (bn_d b6) as [psd|]; [exists psd; split; [reflexivity| exact (proj1 ARRsd)]|].
    exfalso. destruct ARRsd as [_ E]. unfold bn_dmax in C6e. rewrite E in C6e. cbn in C6e. lia. }
  destruct HDsd as (psd & Edsd & Hinpsd).
  pose proof (AH_range _ _ _ _ _ _ _ (proj1 (proj2 ENV6)) Hinpsd) as (PSD0 & PSD16 & _ & _ & _).
  unfold bn_cells in BNsd. rewrite C6b, C6c in BNsd. unfold BN_WORDS_MAX in OKs3, OKdv3.
  assert (ASD : 0 < asdiv /\ asdiv + 24 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - SDA0 Rsd1 Rsd2 SDAC CEIL LO SPR SPT; lia).
  assert (BDSD : 0 <= Dsd /\ Dsd + 8 * Z.of_nat (bn_dmax b6) <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - Dsd0 DsdC CEIL LO SPR SPT; lia).
  assert (DN1 : (1 <= dn <= bn_dmax b6)%nat) by (unfold bn_dmax in *; clear - HTOPD OKs2 C6b; subst dn; lia).
  env_openA ENV6.
  match goal with MUx : munch _ m6 m6 |- _ => clear MUx end. match goal with WMx : wmono _ m6 m6 |- _ => clear WMx end.
  pose proof (munch_refl [(bv_unsigned sp - 320, bv_unsigned sp); (asdiv, asdiv + 24); (Dsd, Dsd + 8 * Z.of_nat (bn_dmax b6))]%Z m6) as MU6.
  pose proof (wmono_refl bsegs m6) as WM6.
  assert (OFF6 : offshW [(bv_unsigned sp - 320, bv_unsigned sp); (asdiv, asdiv + 24); (Dsd, Dsd + 8 * Z.of_nat (bn_dmax b6))]).
  { cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. clear - OFVA OFV C2 CEIL LO. lia. }
  apply hide_intro in OFVA. apply hide_intro in OFV. apply hide_intro in SDAI. apply hide_intro in DsdI. apply hide_intro in SEPsd.
  unfold MallocRep.wz in *. apply implA_from_evt.
  zstep. if_cases KD; zify_cond KD. { exfalso. rewrite ?unsigned_lit in KD by lia. clear - KD ASD. lia. }
  clear KD.
  step.                                                      (* [comment removed for export] *)
  hide_ors. ub. unhide.                                      (* [comment removed for export] *)
  do 2 zstep.                                                (* [comment removed for export] *)
  step.                                                      (* [comment removed for export] *)
  shl_with ACVA ALVA. chk0.                                  (* [comment removed for export] *)
  do 3 zstep.                                                (* [comment removed for export] *)
  shl_with ACVA ALVA.                                        (* [comment removed for export] *)
  step.                                                      (* [comment removed for export] *)
  chk0.
  step. rewrite (sx32_small (Z.of_nat dn)) by lia.           (* [comment removed for export] *)
  zstep. rewrite (bk_swrap32_small (Z.of_nat dn + -1)) by lia. (* [comment removed for export] *)
  hide_ors. ub. unhide.                                      (* [comment removed for export] *)
  do 2 zstep.
  replace ((Z.of_nat dn + -1) ≪ 3) with (8 * Z.of_nat dn - 8) by (rewrite Z.shiftl_mul_pow2 by lia; lia).

  hide_ors. ub. zstep. ub. zstep. ub. unhide.

  set (dtop := nth (dn - 1) (bn_buf bd) 0) in *.
  assert (Edtop : nth (dn - 1) (bn_buf b6) 0 = dtop).
  { unfold dtop. rewrite <- (firstn_skipn dn (bn_buf b6)), <- (firstn_skipn dn (bn_buf bd)), C6d.
    rewrite !app_nth1 by (rewrite length_firstn; unfold bn_dmax in *; lia). reflexivity. }
  assert (Rdtop : 0 < dtop < 18446744073709551616).
  { assert (L : limb dtop) by (apply limbs_nth; exact OKdv1). unfold limb in L. rewrite BW_lit in L. lia. }
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    destruct (proj1 (limbarr_limbs_at bsegs mx Dsd (bn_buf b6)) Usd) as (LAsd & WRsd) end.
  assert (Ntop : nth_error (bn_buf b6) (dn - 1) = Some dtop) by (rewrite <- Edtop; apply nth_error_nth'; unfold bn_dmax in *; lia).
  do 2 zstep.                                               (* [comment removed for export] *)
  shl_with ACV ALV. chk0.                                   (* [comment removed for export] *)
  let ad := cur_mem_addr in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (limbs_at_read_nth bsegs mx Dsd (bn_buf b6) (dn - 1) dtop ad LAsd Ntop ltac:(unfold wa; f_equal; lia)) as RD end.
  zstep. clear RD.
  zstep.
  assert (Edt : bv_unsigned (Z_to_bv 64 dtop) = dtop) by (apply unsigned_lit; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m7 end.
  eapply evt_cut.
  { match goal with STx : stk _ m7 _ _, MIx : mem_inv _ m7 |- _ =>
      eapply BN_num_bits_word_aspec with (lo := lo) (m := m7); [rewrite ESP; exact STx | rewrite ESP; lia | exact MIx] end. }
  intros ms' PO. unfold nbw_post in PO.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m8 & E & MUc & WMc & MIc & STc).
  subst ms'. rewrite ESP, Edt in *.
  rewrite (ret_pc_even 0x2527b0) by lia.
  assert (LAsd8 : limbs_at bsegs m8 Dsd (bn_buf b6)).
  { eapply limbs_at_transport; [exact LAsd | exact MUc |]. cbn [disjoint_from]. fold (bn_dmax b6). split; [|exact I]. unfold BnHeapA.ACEIL in *. lia. }
  clear LAsd WRsd.
  match goal with STx : stk _ m7 _ _ |- _ => clear STx end.
  transport_after_call bsegs m7 m8 MUc WMc.
  clear MUc WMc. match goal with MIx : mem_inv _ m7 |- _ => clear MIx end. try clear m7.
  (* [comment removed for export] *)
  set (nb := num_bits_word dtop) in *.
  assert (NB : 1 <= nb <= 64).
  { destruct (num_bits_word_spec dtop ltac:(lia)) as (B1 & _). pose proof (num_bits_word_le dtop 64 ltac:(lia) ltac:(change (2 ^ 64) with 18446744073709551616; lia)). fold nb in B1, H. lia. }
  set (af := firstn dn (bn_buf b6)).
  assert (Laf : length af = dn) by (unfold af; apply firstn_length_le; unfold bn_dmax in *; lia).
  assert (LAaf : limbs_at bsegs m8 Dsd af).
  { rewrite <- (firstn_skipn dn (bn_buf b6)) in LAsd8. apply limbs_at_app in LAsd8. exact (proj1 LAsd8). }
  assert (LArest : limbs_at bsegs m8 (Dsd + 8 * Z.of_nat dn) (skipn dn (bn_buf b6))).
  { rewrite <- (firstn_skipn dn (bn_buf b6)) in LAsd8. apply limbs_at_app in LAsd8. destruct LAsd8 as [_ X]. fold af in X. rewrite Laf in X. exact X. }
  destruct (proj1 (limbarr_limbs_at bsegs m8 Dsd (bn_buf b6)) Usd) as (_ & WRsd8).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  replace (Z_to_bv 64 (Z.of_nat dn)) with (Z_to_bv 64 (Z.of_nat (length af))) by (rewrite Laf; reflexivity).
  pose proof (acc_munch bsegs _ m6 m8 _ _ ACV MU6 OFF6 ltac:(clear - BDSD; lia) ltac:(clear - BDSD; lia)) as ACV8.
  lazymatch goal with FRx : rw_cells _ m8 (bv_unsigned sp + -304) ?fr |- _ =>
    eapply la_blockA with (m := m8) (D := Dsd) (SP := bv_unsigned sp) (lo := lo) (a := af) (lb := 64 - nb) (FS := 304) (FB := bv_unsigned sp + -304) (FCELLS := fr) (nb := nb);
    [ reflexivity
    | clear; lia
    | clear - NB; lia
    | rewrite Laf; left; unfold BnHeapA.ACEIL in *; unfold bn_dmax in *; clear - DsdC CEIL LO OKs2 C6b; lia
    | rewrite Laf; eapply acc_sub; [exact ACV8 | clear; lia | unfold bn_dmax in *; clear - OKs2 C6b; lia]
    | exact ALV
    | rewrite Laf; cbn [offshW]; cbn [offshW] in OFF6; unfold bn_dmax in *; clear - OFF6 OKs2 C6b Dsd0; lia
    | exact NB
    | reflexivity
    | rewrite Laf; lia
    | unfold af; apply limbs_firstn; exact OKs1
    | exact LAaf
    | rewrite Laf; apply (wr_at_sub bsegs m8 Dsd (8 * Z.of_nat (length (bn_buf b6))) 0 (8 * Z.of_nat dn)) in WRsd8; [rewrite Z.add_0_r in WRsd8; exact WRsd8 | lia | lia | unfold bn_dmax in *; lia]
    | exact FRx
    | exact STc
    | exact MIc
    | ]
  end.
  intros m9 w5 w6 w10 w11 w13 w14 w15 w16 w17 w22 HRES FR9 ST9 MI9 MU9 WM9. rewrite Laf in MU9.
  set (sh := 64 - nb) in *.
  set (resl := fst (lshift_limbs af sh 0)) in *.
  assert (Lres : length resl = dn) by (unfold resl; rewrite lshift_limbs_len; exact Laf).
  assert (DJ9 : forall A k, (A + k <= Dsd \/ Dsd + 8 * Z.of_nat (bn_dmax b6) <= A) -> A + k <= bv_unsigned sp - 304 ->
            disjoint_from [(Dsd, Dsd + 8 * Z.of_nat dn); (bv_unsigned sp - 304, bv_unsigned sp)] A k).
  { intros A k H1 H2. cbn [disjoint_from]. unfold bn_dmax in *. lia. }
  try apply hide_elim in SEPsd.
  eapply (rw_cells_transport bsegs _ m8 m9) in BNsd; [| exact MU9 | exact WM9 | apply DJ9; cbn; unfold BnHeapA.ACEIL in *; lia].
  assert (LArest9 : limbs_at bsegs m9 (Dsd + 8 * Z.of_nat dn) (skipn dn (bn_buf b6))).
  { eapply limbs_at_transport; [exact LArest | exact MU9 |]. cbn [disjoint_from]. rewrite length_skipn. unfold bn_dmax in *. lia. }
  set (nbuf := splice (bn_buf b6) 0 resl).
  assert (Lnbuf : length nbuf = bn_dmax b6) by (unfold nbuf, bn_dmax in *; rewrite splice_length by lia; reflexivity).
  assert (U9 : u64arr bsegs m9 Dsd (wlimbs nbuf)).
  { apply limbarr_limbs_at. split.
    - unfold nbuf, splice. change (firstn 0 (bn_buf b6)) with (@nil Z). change (0 + length resl)%nat with (length resl).
      change ([] ++ resl ++ skipn (length resl) (bn_buf b6)) with (resl ++ skipn (length resl) (bn_buf b6)).
      apply limbs_at_app. split; [exact HRES|]. rewrite Lres. exact LArest9.
    - rewrite Lnbuf. eapply wr_at_transport; [exact WRsd8 | exact WM9]. }
  assert (MU6' : munch [(bv_unsigned sp - 320, bv_unsigned sp); (asdiv, asdiv + 24); (Dsd, Dsd + 8 * Z.of_nat (bn_dmax b6))]%Z m6 m9).
  { eapply munch_trans; [exact MU6|]. eapply munch_weaken; [|exact MU9]. unfold sub_fp. intros xx Hxx. cbn [outside] in *. unfold bn_dmax in *. lia. }
  assert (WM6' : wmono bsegs m6 m9) by (eapply wmono_trans; eauto).
  assert (LENnb : Z.of_nat (length (wlimbs nbuf)) = Z.of_nat (bn_dmax b6)) by (rewrite wlimbs_len, Lnbuf; reflexivity).
  clear MU6 MU9 WM9 Usd LENsd LAsd8 LAaf LArest LArest9 HRES WRsd8 DJ9 STc MIc ACV8.
  (* [comment removed for export] *)

  do 3 zstep.                                                (* [comment removed for export] *)
  shl_with ACVA ALVA. chk0.                                  (* [comment removed for export] *)
  zstep.                                                     (* [comment removed for export] *)
  step. step.                                                (* [comment removed for export] *)
  step.                                                      (* [comment removed for export] *)
  step.                                                      (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m10 end.
  apply evt_done. unfold bbind at 1. cbn [bind tree_ops]. rewrite la_run. cbn [tbind fst snd]. rewrite bbind_get_set.
  fold b6. rewrite C6b. fold dn. rewrite Edtop. fold nb. fold sh. fold af. fold resl. fold nbuf.
  rewrite (getbn_setbn_same_m sdiv _ ls6 HVsd6), setbn_setbn_same.
  set (sd3 := bn_with_neg (bn_with_buf b6 nbuf) false).
  unfold bbind at 1. cbn [bind tree_ops].
  assert (HWL6 : Forall (w_lib OW6 lo (bv_unsigned sp)) [(bv_unsigned sp - 320, bv_unsigned sp); (asdiv, asdiv + 24); (Dsd, Dsd + 8 * Z.of_nat (bn_dmax b6))]).
  { constructor; [left; cbn; lia|]. constructor; [right; exists (qsd, Asd, nsd); cbn; auto|].
    constructor; [right; exists (psd, Dsd, 8 * Z.of_nat (bn_dmax b6)); cbn; split; [exact Hinpsd| lia]| constructor]. }
  assert (WOK6 : Forall (w_ok OW6 LB ls6 AD EA [sdiv]) [(bv_unsigned sp - 320, bv_unsigned sp); (asdiv, asdiv + 24); (Dsd, Dsd + 8 * Z.of_nat (bn_dmax b6))]).
  { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia|]. constructor; [eapply (w_struct OW6 LB ls6 AD EA false [sdiv] _ sdiv asdiv); [left; reflexivity| exact HAsdiv6| cbn; lia| cbn; lia]|].
    constructor; [eapply (w_limbs OW6 LB ls6 AD EA false [sdiv] _ sdiv psd Dsd); [left; reflexivity| exact HVsd6| exact Edsd| exact Hinpsd| cbn [fst snd]; fold b6; lia| cbn [fst snd]; fold b6; lia]| constructor]. }
  pose proof (left_align_value af ltac:(unfold af; apply limbs_firstn; exact OKs1) ltac:(rewrite Laf; lia)) as LAV.
  rewrite Laf in LAV.
  assert (Eaft : nth (dn - 1) af 0 = dtop) by (unfold af; rewrite nth_firstn; destruct (Nat.ltb_spec (dn - 1) dn); [exact Edtop | lia]).
  rewrite Eaft in LAV. specialize (LAV ltac:(lia)). cbv zeta in LAV. fold nb in LAV. fold sh in LAV. fold resl in LAV.
  destruct LAV as (SH & LRES & _ & VRES & D0N).
  match goal with HEAPx : @BnHeapA.AHEAP _ Σ6 OW6 LB _, STx : stk _ m10 _ _, MIx : mem_inv _ m10, FRx : rw_cells _ m10 (bv_unsigned sp + -304) _ |- _ =>
    rename HEAPx into HEAP6; rename STx into ST10; rename MIx into MI10; rename FRx into FR10 end.
  assert (LS7 : lib_state (setbn sdiv sd3 ls6) m10 OW6 AD EA).
  { unfold lib_state. eapply (lib_state_close [] ls6 m10 OW6 AD EA sdiv asdiv); [| exact ND6| exact HAsdiv6| | |].
    - exact (lib_state_frame Σ6 LB [sdiv] ls6 _ _ OW6 AD EA _ HEAP6 LSH6 MU6' WM6' WOK6).
    - exists Dsd. split.
      + unfold bn_cells, sd3, bn_dmax. cbn [bn_with_neg bn_with_buf bn_top bn_buf bn_neg bn_flags Z.b2z]. rewrite Lnbuf, C6b. fold dn. exact BNsd.
      + unfold bn_arr, sd3, bn_dmax. cbn [bn_with_neg bn_with_buf bn_d bn_buf]. rewrite Edsd, Lnbuf. split; [exact Hinpsd| exact U9].
    - unfold bn_okm, sd3, bn_dmax. cbn [bn_with_neg bn_with_buf bn_buf bn_top bn_flags]. rewrite Lnbuf. unfold BN_WORDS_MAX.
      split; [unfold nbuf; apply splice_limbs; [exact OKs1| exact LRES]|]. split; [exact OKs2|]. split; [lia| exact OKs4].
    - apply ids_ok_setbn_same; [exact IDS6| exact HVsd6|]. unfold bn_blocks, sd3, bn_dmax. cbn [bn_with_neg bn_with_buf bn_d bn_buf]. rewrite Lnbuf. reflexivity. }
  lazymatch type of ENV6 with cenvA _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?u _ _ _ _ =>
    lazymatch type of FR10 with rw_cells _ _ _ ?fr' =>
      let pre' := drop2 fr' in
      assert (ENV7 : cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -304) s0 ra (Some ras) BN_DIV_FT_COST Σ ls OW m pre' u Σ6 (setbn sdiv sd3 ls6) m10 OW6);
      [ apply cenv_setbnA; [| exact HVsd6 | fold b6; unfold bn_blocks, sd3; cbn [bn_with_neg bn_with_buf bn_d bn_buf bn_dmax bn_top]; rewrite ?Edsd; reflexivity];
        eapply (cenv_silentA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -304) s0 ra (Some ras) BN_DIV_FT_COST Σ ls OW m);
          [exact ENV6 | exact MU6' | exact WM6' | exact HWL6 | exact ST10 | exact MI10 | cbn [app]; exact FR10 | cbn; lia]
      | ] end end.
  set (ls7 := setbn sdiv sd3 ls6) in *.
  assert (HAsnum7 : ref_at ls7 OW6 AD snum asnum) by (apply ref_at_setbn; exact HAsnum6).
  assert (HAnum7 : ref_at ls7 OW6 AD num anum) by (apply ref_at_setbn; exact HAnum6).
  destruct (lib_state_h_parts _ _ _ _ _ _ LS7) as (_ & _ & _ & SOK7).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS7 HAsnum7) as HVsn7. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS7 HAnum7) as HVnum7.
  pose proof (st_okm_getbn snum ls7 SOK7 HVsn7) as (_ & OKsn2 & _). pose proof (st_okm_getbn num ls7 SOK7 HVnum7) as (OKn1 & OKn2 & OKn3 & _).
  eapply implA_bind.
  { eapply implA_leaves; [apply (bn_lshift_leaves snum num sh ls7 (fun E => NPs num NPnum (eq_sym E)) SH HVsn7 OKsn2 OKn2)|].
    eapply (bn_lshift_fixed_top_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW6) (LB := LB) (AD := AD) (EA := EA) (rr := snum) (rx := num) (ar := asnum) (ax := anum) (n := sh);
      [| | | reflexivity | exact HAsnum7 | exact HAnum7 | reflexivity | reflexivity | reflexivity | exact SH].
    - eapply cenv_preA; [exact ENV7 | exact LS7 | unfold BN_LSHIFT_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO; lia | unfold BN_DIV_FT_COST, MC; lia].
    - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ENV7).
    - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_dv_lshift CTX). }
  cbv beta. intros [u8 ls8] Σ8 ms8 [PO LEAF8].
  apply (bn_postA_cpost LB AD EA lo (bv_unsigned sp) (bv_unsigned sp + -304) BN_DIV_FT_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 ENV7))].
  cbn [fst snd] in *.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F8 & fc8 & m11 & OW8 & -> & CP8 & ->).
  lazymatch type of ENV7 with cenvA _ _ _ _ _ _ _ _ _ _ _ _ _ ?pre ?u _ _ _ _ =>
    assert (E8 : cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -304) s0 ra (Some ras) BN_DIV_FT_COST Σ ls OW m pre (u + MC) Σ8 ls8 m11 OW8 /\ lib_state ls8 m11 OW8 AD EA)
      by (eapply cenv_postA; [exact ENV7 | exact CP8]) end.
  destruct E8 as (ENV8 & LS8).
  pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP8) as RS8.
  rewrite (ret_pc_even 0x252868) by lia. unfold MallocRep.wz.
  clear CP8.
  (* [comment removed for export] *)
  destruct LEAF8 as (L8a & L8b & L8c & L8d & L8e & _). cbn [snd] in *.
  assert (Enum7 : getbn num ls7 = getbn num ls) by (unfold ls7; rewrite getbn_setbn_other by (apply not_eq_sym, NPd, NPnum); apply NPget6; exact NPnum).
  rewrite Enum7 in L8b, L8c, L8d, L8e, OKn1, OKn2, OKn3.
  set (bnum := getbn num ls) in *. set (tn := bn_top bnum) in *.
  assert (Esd8 : getbn sdiv ls8 = sd3) by (rewrite L8a by exact NEsd; unfold ls7; apply getbn_setbn_same_m; exact HVsd6).
  assert (NPget8 : forall r, nonpool r -> getbn r ls8 = getbn r ls).
  { intros r NP. rewrite L8a by (apply not_eq_sym, NPs, NP). unfold ls7. rewrite getbn_setbn_other by (apply not_eq_sym, NPd, NP). apply NPget6. exact NP. }
  assert (Etmp8 : getbn tmp ls8 = getbn tmp ls6) by (rewrite L8a by (apply not_eq_sym; exact NEts); unfold ls7; apply getbn_setbn_other; apply not_eq_sym; exact NEtd).
  pose proof (RS8 _ _ (proj2 (ref_at_setbn ls6 OW6 AD sdiv sd3 _ _) HAdv6)) as HAdv8. pose proof (RS8 _ _ (proj2 (ref_at_setbn ls6 OW6 AD sdiv sd3 _ _) HArm6)) as HArm8.
  pose proof (RS8 _ _ HAnum7) as HAnum8. pose proof (RS8 _ _ (proj2 (ref_at_setbn ls6 OW6 AD sdiv sd3 _ _) HAdvs6)) as HAdvs8.
  pose proof (RS8 _ _ (proj2 (ref_at_setbn ls6 OW6 AD sdiv sd3 _ _) HAtmp6)) as HAtmp8. pose proof (RS8 _ _ HAsnum7) as HAsnum8.
  pose proof (RS8 _ _ (proj2 (ref_at_setbn ls6 OW6 AD sdiv sd3 _ _) HAsdiv6)) as HAsdiv8.
  clear RS8 HAdv6 HArm6 HAnum6 HAdvs6 HAtmp6 HAsnum6 HAsdiv6 HAsnum7 HAnum7 ENV6 LS6 ENV7 LS7 LSH6 HWL6 WOK6 MU6' WM6' U9 BNsd SOK7 HVsn7 HVnum7 OKsn2 NPget6
        IDS6 ADB6 ERRB6 SOK6 ND6 Hinsd Hinpsd SEPsd DsdI DsdC Dsd0 SDA0 SDAC SDAI Rsd1 Rsd2 ARRsd LENnb Enum7 HEAP6 ST10 MI10 FR10 ACVA ALVA OFVA ACV ALV OFV OFF6 ASD BDSD PSD0 PSD16.
  (* [comment removed for export] *)
  pose proof (AH_nodup_l _ _ _ _ (proj1 (proj2 ENV8))) as ND8.
  destruct (lib_state_open [] ls8 m11 OW8 AD EA sdiv asdiv LS8 ND8 HAsdiv8 ltac:(intros [])) as ((Dsd8 & BNsd8 & _) & _ & _).
  destruct (lib_state_open [] ls8 m11 OW8 AD EA snum asnum LS8 ND8 HAsnum8 ltac:(intros [])) as ((Dsn8 & BNsn8 & _) & (OKsn1 & OKsn2 & OKsn3 & OKsn4) & _).
  rewrite Esd8 in BNsd8. unfold bn_cells in BNsd8, BNsn8. unfold sd3 in BNsd8. cbn [bn_with_neg bn_with_buf bn_top bn_dmax bn_buf bn_neg bn_flags] in BNsd8.
  rewrite C6b in BNsd8. rewrite L8b in BNsn8. unfold BN_WORDS_MAX in OKsn3, OKn3.
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ (proj1 (proj2 ENV8)) LS8 HAsdiv8) as (ACVA & ALVA & OFVA).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ (proj1 (proj2 ENV8)) LS8 HAsnum8) as (ACSA & ALSA & OFSA).
  destruct (ref_at_inb _ _ _ _ _ (proj1 (proj2 (lib_state_h_parts _ _ _ _ _ _ LS8))) HAsnum8) as (qs8 & As8 & ns8 & _ & Hins8 & Rs81 & Rs82).
  pose proof (AH_range _ _ _ _ _ _ _ (proj1 (proj2 ENV8)) Hins8) as (SA80 & _ & _ & SAC8 & _).
  assert (ASN : 0 < asnum /\ asnum + 24 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - SA80 Rs81 Rs82 SAC8 CEIL LO SPR SPT; lia).
  destruct (ref_at_inb _ _ _ _ _ (proj1 (proj2 (lib_state_h_parts _ _ _ _ _ _ LS8))) HAsdiv8) as (qd8 & Ad8 & nd8 & _ & Hind8 & Rd81 & Rd82).
  pose proof (AH_range _ _ _ _ _ _ _ (proj1 (proj2 ENV8)) Hind8) as (SD80 & _ & _ & SDC8 & _).
  assert (ASD : 0 < asdiv /\ asdiv + 24 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - SD80 Rd81 Rd82 SDC8 CEIL LO SPR SPT; lia).
  env_openA ENV8.
  assert (OFF8 : offshW [(bv_unsigned sp + -304, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; clear - C2 CEIL LO; lia).
  apply hide_intro in OFVA. apply hide_intro in OFSA.
  unfold MallocRep.wz in *. apply implA_from_evt.
  zstep. if_cases KZ; zify_cond KZ. { exfalso. rewrite ?unsigned_lit in KZ by lia. clear - KZ. lia. }
  clear KZ.
  step.
  shl_with ACVA ALVA. chk0.
  hide_ors. ub. unhide.                                 (* [comment removed for export] *)
  step.                                                     (* [comment removed for export] *)
  do 3 zstep.                                               (* [comment removed for export] *)
  step.                                                     (* [comment removed for export] *)
  shl_with ACSA ALSA.                                       (* [comment removed for export] *)
  step. rewrite (zx32_small (Z.of_nat dn)) by (unfold bn_dmax in *; lia).       (* [comment removed for export] *)
  chk0.
  step.                                                      (* [comment removed for export] *)
  step. rewrite (sx32_small (Z.of_nat (tn + 1))) by (unfold bn_dmax in *; lia). (* [comment removed for export] *)
  zstep. rewrite Z.add_0_r, (bk_swrap32_small (Z.of_nat dn)) by (unfold bn_dmax in *; lia). (* [comment removed for export] *)
  do 2 zstep.                                                (* [comment removed for export] *)
  step.                                                      (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m12 end.
  env_closeA HWLs WOKs ENV8 LS8 ENV9 LS9.
  clear LS8. rename LS9 into LS8.
  apply evt_done. rewrite !bbind_get. rewrite Esd8. change (bn_top sd3) with (bn_top b6). rewrite C6b, L8b.
  lazymatch type of ENV9 with cenvA _ _ _ _ _ _ _ _ _ _ _ _ _ ?FR8 ?used8 _ _ _ _ =>
   lazymatch goal with |- implA (bbind _ _ ?REST0 _) _ ?Q _ =>
    assert (CONT : forall ΣP lsP mP OWP (nP : nat) (usedP : Z) (FP : bvmap 5 word) (fcP : bv 32) x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31,
               cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -304) s0 ra (Some ras) BN_DIV_FT_COST Σ ls OW m FR8 usedP ΣP lsP mP OWP -> usedP + 3 * MC <= BN_DIV_FT_COST ->
               lib_state lsP mP OWP AD EA ->
               ref_at lsP OWP AD dv adv -> ref_at lsP OWP AD rm arm -> ref_at lsP OWP AD num anum -> ref_at lsP OWP AD dvs advs ->
               ref_at lsP OWP AD tmp atmp -> ref_at lsP OWP AD snum asnum -> ref_at lsP OWP AD sdiv asdiv ->
               getbn sdiv lsP = sd3 -> (forall r, nonpool r -> getbn r lsP = getbn r ls) ->
               bn_top (getbn snum lsP) = nP -> (dn + 1 <= nP)%nat -> (tn + 1 <= nP)%nat -> (nP <= dn + 1 \/ nP = tn + 1)%nat -> bn_neg (getbn snum lsP) = bn_neg bnum ->
               firstn nP (bn_buf (getbn snum lsP)) = lsh_res bnum sh ++ repeat 0%Z (nP - (tn + 1)) ->
               implA (REST0 tt lsP) ΣP Q
                 (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -304)) gp (Z_to_bv 64 TP_A) x5 x6 x7 sp (Z_to_bv 64 (Z.of_nat nP))
                          (Z_to_bv 64 (Z.of_nat dn)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (asnum ≫ 3)) (Z_to_bv 64 advs) (Z_to_bv 64 atmp)
                          (Z_to_bv 64 (Z.of_nat (tn + 1))) x22 (Z_to_bv 64 adv) (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.of_nat dn)) s10 (Z_to_bv 64 (ad_ctx AD)) x28 x29 x30 x31)
                     FP (Z_to_bv 64 0x252960) fcP None mP (seg_rom bsegs)))
   end end.
  { intros ΣP lsP mP OWP nP usedP FP fcP q1 q5 q6 q7 q11 q12 q13 q14 q15 q16 q17 q22 q28 q29 q30 q31
           ENVP USEDP LSP HAdvP HArmP HAnumP HAdvsP HAtmpP HAsnumP HAsdivP GSP NPgP TNP NP1 NP2 NP3 NEGP FNP.
    clear ENV8 HAdv8 HArm8 HAnum8 HAdvs8 HAtmp8 HAsnum8 HAsdiv8 ND8 BNsd8 BNsn8 Dsd8 Dsn8 OKsn1 OKsn2 OKsn3 OKsn4 L8a L8b L8c L8d L8e Esd8 NPget8 Etmp8 ENV9 LS8 ACVA ALVA OFVA ACSA ALSA OFSA.
    cbv beta. rewrite bbind_get, TNP.
    (* [comment removed for export] *)
    pose proof (AH_nodup_l _ _ _ _ (proj1 (proj2 ENVP))) as NDP.
    destruct (lib_state_h_parts _ _ _ _ _ _ LSP) as (IDSP & ADBP & ERRBP & SOKP).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LSP HAsdivP) as HVsdP. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LSP HAsnumP) as HVsnP.
    destruct (lib_state_open [] lsP mP OWP AD EA sdiv asdiv LSP NDP HAsdivP ltac:(intros [])) as ((DsdP & BNsdP & ARRsdP) & _ & _).
    destruct (lib_state_open [] lsP mP OWP AD EA snum asnum LSP NDP HAsnumP ltac:(intros [])) as ((DsnP & BNsnP & ARRsnP) & (OKp1 & OKp2 & OKp3 & OKp4) & _).
    destruct (bn_arr_facts ΣP OWP LB mP (proj1 (proj2 ENVP)) lsP AD EA IDSP ADBP sdiv DsdP HVsdP ARRsdP) as (UsdP & _ & DsdP0 & DsdPC & _ & _).
    destruct (bn_arr_facts ΣP OWP LB mP (proj1 (proj2 ENVP)) lsP AD EA IDSP ADBP snum DsnP HVsnP ARRsnP) as (UsnP & LENsn & DsnP0 & DsnPC & _ & SEPsnP).
    destruct (arr_shA _ _ _ _ _ _ (proj1 (proj2 ENVP)) ARRsdP) as (ACV & ALV & OFV).
    destruct (arr_shA _ _ _ _ _ _ (proj1 (proj2 ENVP)) ARRsnP) as (ACS & ALS & OFS).
    rewrite GSP in BNsdP, UsdP, DsdPC, ACV, OFV. unfold bn_cells in BNsdP, BNsnP.
    unfold sd3 in BNsdP, UsdP, DsdPC, ACV, OFV. cbn [bn_with_neg bn_with_buf bn_top bn_dmax bn_buf bn_neg bn_flags] in BNsdP, UsdP, DsdPC, ACV, OFV.
    rewrite C6b in BNsdP. rewrite TNP in BNsnP. unfold BN_WORDS_MAX in OKp3.
    unfold bn_dmax in DsdPC, ACV, OFV. cbn [bn_buf] in DsdPC, ACV, OFV. rewrite Lnbuf in DsdPC, ACV, OFV.
    assert (LENnbP : Z.of_nat (length (wlimbs nbuf)) = Z.of_nat (bn_dmax b6)) by (rewrite wlimbs_len, Lnbuf; reflexivity).
    set (d0 := nth (dn - 1) nbuf 0).
    set (d1 := if (dn =? 1)%nat then 0 else nth (dn - 2) nbuf 0).
    assert (Lnb2 : (dn <= length nbuf)%nat) by (rewrite Lnbuf; unfold bn_dmax in *; lia).
    assert (LIMnb : limbs nbuf) by (unfold nbuf; apply splice_limbs; [exact OKs1 | exact LRES]).
    assert (Rd0 : 9223372036854775808 <= d0 < 18446744073709551616).
    { assert (L : limb d0) by (apply limbs_nth; exact LIMnb). unfold limb in L. rewrite BW_lit in L. split; [|lia].
      unfold d0, nbuf, splice. change (firstn 0 (bn_buf b6)) with (@nil Z). cbn [app]. rewrite app_nth1 by lia.
      change (2 ^ 63) with 9223372036854775808 in D0N. exact D0N. }
    assert (Rd1 : 0 <= d1 < 18446744073709551616).
    { unfold d1. destruct (dn =? 1)%nat; [lia|]. assert (L : limb (nth (dn - 2) nbuf 0)) by (apply limbs_nth; exact LIMnb). unfold limb in L. rewrite BW_lit in L. lia. }
    destruct (ref_at_inb _ _ _ _ _ ADBP HAsdivP) as (qsP & AsP & nsP & _ & HinsP & RsP1 & RsP2).
    pose proof (AH_range _ _ _ _ _ _ _ (proj1 (proj2 ENVP)) HinsP) as (SP0 & _ & _ & SPC & SPI).
    destruct (ref_at_inb _ _ _ _ _ ADBP HAsnumP) as (qnP & AnP & nnP & _ & HinnP & RnP1 & RnP2).
    pose proof (AH_range _ _ _ _ _ _ _ (proj1 (proj2 ENVP)) HinnP) as (NP0 & _ & _ & NPC & NPI).
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ (proj1 (proj2 ENVP)) LSP HAsdivP) as (ACVA & ALVA & OFVA).
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ (proj1 (proj2 ENVP)) LSP HAsnumP) as (ACSA & ALSA & OFSA).

    assert (HSN : exists psn, bn_d (getbn snum lsP) = Some psn /\ In (psn, DsnP, 8 * Z.of_nat (bn_dmax (getbn snum lsP))) OWP).
    { unfold bn_arr in ARRsnP. destruct (bn_d (getbn snum lsP)) as [psn|]; [exists psn; split; [reflexivity| exact (proj1 ARRsnP)]|].
      exfalso. destruct ARRsnP as [_ E]. unfold bn_dmax in OKp2. rewrite E in OKp2. cbn in OKp2. clear - OKp2 TNP NP1. lia. }
    destruct HSN as (psn & Edsn & HinsnP).
    pose proof (AH_range _ _ _ _ _ _ _ (proj1 (proj2 ENVP)) HinsnP) as (PSN0 & PSN16 & _ & _ & _).
    assert (BDSN : 0 < DsnP /\ DsnP + 8 * Z.of_nat (bn_dmax (getbn snum lsP)) <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - PSN0 DsnPC CEIL LO SPR SPT; lia).
    assert (HinsdP : In (psd, DsdP, 8 * Z.of_nat (bn_dmax b6)) OWP).
    { unfold bn_arr in ARRsdP. rewrite GSP in ARRsdP. unfold sd3, bn_dmax in ARRsdP. cbn [bn_with_neg bn_with_buf bn_d bn_buf] in ARRsdP.
      rewrite Edsd, Lnbuf in ARRsdP. exact (proj1 ARRsdP). }
    pose proof (AH_range _ _ _ _ _ _ _ (proj1 (proj2 ENVP)) HinsdP) as (PSDP0 & PSDP16 & _ & _ & _).
    env_openA ENVP.
    assert (OFFP : offshW [(bv_unsigned sp + -304, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; clear - C2 CEIL LO; lia).
    assert (BDQ : 0 <= DsdP /\ DsdP + 8 * Z.of_nat dn + 8 < 18446744073709551616) by (unfold bn_dmax, BnHeapA.ACEIL in *; clear - DsdP0 DsdPC CEIL LO SPR OKs2 C6b; lia).
    assert (NPB : Z.of_nat nP <= Z.of_nat (bn_dmax (getbn snum lsP)) < 8388608) by (clear - OKp2 OKp3 TNP; lia).
    apply hide_intro in OFVA. apply hide_intro in OFSA. apply hide_intro in OFV. apply hide_intro in OFS. apply hide_intro in SPI. apply hide_intro in NPI. apply hide_intro in NP3.
    unfold MallocRep.wz in *. apply implA_from_evt.
    zstep. rewrite (bk_swrap32_small (Z.of_nat nP - Z.of_nat dn)) by lia. (* [comment removed for export] *)
    replace (Z.of_nat nP - Z.of_nat dn) with (Z.of_nat (nP - dn)) by lia. (* [comment removed for export] *)
    set (loop := (nP - dn)%nat) in *.                        (* [comment removed for export] *)
    hide_ors. ub. unhide.                                    (* [comment removed for export] *)
    step.                                                    (* [comment removed for export] *)
    hide_ors. ub. unhide.                                    (* [comment removed for export] *)
    zstep.                                                   (* [comment removed for export] *)
    shl_with ACSA ALSA. chk0.                                (* [comment removed for export] *)
    step.                                                    (* [comment removed for export] *)
    step.                                                    (* [comment removed for export] *)
    step.
    zstep. replace (Z.of_nat loop ≪ 3) with (8 * Z.of_nat loop) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep.
    hide_ors. ub. unhide.
    step.
    hide_ors. ub. unhide.
    zstep. rewrite (bk_swrap32_small (Z.of_nat nP + -1)) by lia.
    hide_ors. ub. unhide.
    do 2 zstep.
    replace (DsnP + (Z.of_nat nP + -1) ≪ 3) with (DsnP + 8 * Z.of_nat nP - 8) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    step.
    hide_ors. ub. unhide.
    step.
    shl_with ACVA ALVA. chk0.
    step.
    zstep. rewrite (bk_swrap32_small (Z.of_nat dn + -1)) by lia.
    hide_ors. ub. unhide.
    step.
    step.
    do 2 zstep.
    replace (DsdP + (Z.of_nat dn + -1) ≪ 3) with (DsdP + 8 * Z.of_nat dn - 8) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mQ end.
    destruct (proj1 (limbarr_limbs_at bsegs mQ DsdP nbuf) UsdP) as (LAnb & _).
    hide_ors. ub. zstep. ub. unhide.                         (* [comment removed for export] *)
    do 2 zstep.                                              (* [comment removed for export] *)
    hide_ors. shl_with ACV ALV. chk0. unhide.                (* [comment removed for export] *)
    assert (N0 : nth_error nbuf (dn - 1) = Some d0) by (unfold d0; apply nth_error_nth'; lia).
    let ad := cur_mem_addr in
      pose proof (limbs_at_read_nth bsegs mQ DsdP nbuf (dn - 1) d0 ad LAnb N0 ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD.                                         (* [comment removed for export] *)
    zstep.                                                   (* [comment removed for export] *)
    step.                                                    (* [comment removed for export] *)
    setreg 26%Z (Z_to_bv 64 0) ltac:(f_equal; symmetry; rewrite ub_lxor_sign63 by lia; rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity).

    lazymatch goal with |- evt _ ?P (MS _ _ _ _ _ ?mx _) =>
     lazymatch goal with FRx : rw_cells _ mx (bv_unsigned sp + -304) (CB 16 ?jA :: _) |- _ =>
      assert (JOIN : forall mJ (j1a j1b : list byte) (x10 x11 x12 x13 x14 : word),
        rw_cells bsegs mJ (bv_unsigned sp + -304)
          ([CB 16 jA; C8 (Z_to_bv 64 ((asnum + 8) ≫ 3 + SHB)); C8 (Z_to_bv 64 (asnum + 8)); C8 (Z_to_bv 64 sh); C8 (Z_to_bv 64 (ad_ctx AD)); C8 (Z_to_bv 64 arm);
            CB 32 j1a; C8 (Z_to_bv 64 d1); CB 40 j1b; C8 (Z_to_bv 64 asnum); C8 (Z_to_bv 64 (Z.of_nat loop)); C8 (Z_to_bv 64 (asdiv ≫ 3 + SHB));
            C8 (Z_to_bv 64 (DsnP + 8 * Z.of_nat nP - 8)); C8 (Z_to_bv 64 asdiv); C8 (Z_to_bv 64 anum); C8 (Z_to_bv 64 (Z.of_nat dn)); C8 (Z_to_bv 64 (DsnP + 8 * Z.of_nat loop));
            C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) ->
        stk bsegs mJ lo (bv_unsigned sp + -304) -> mem_inv bsegs mJ -> munch [(bv_unsigned sp + -304, bv_unsigned sp)] mP mJ -> wmono bsegs mP mJ ->
        evt bsegs P
          (MS (mkR q1 (Z_to_bv 64 (bv_unsigned sp + -304)) gp (Z_to_bv 64 TP_A) q5 q6 q7 sp (Z_to_bv 64 (Z.of_nat nP))
                   x10 x11 x12 x13 x14 q15 q16 q17 (Z_to_bv 64 d0) (Z_to_bv 64 advs) (Z_to_bv 64 atmp) (Z_to_bv 64 DsnP) (Z_to_bv 64 (8 * Z.of_nat loop))
                   (Z_to_bv 64 adv) (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.of_nat dn)) (Z_to_bv 64 0) (Z_to_bv 64 (ad_ctx AD)) q28 q29 q30 q31)
              FP (Z_to_bv 64 0x252ab4) fcP None mJ (seg_rom bsegs)))
     end end.
    2:{ zstep. if_cases K1; zify_cond K1.
        +                                                    (* [comment removed for export] *)
          zstep. rewrite (bk_swrap32_small (Z.of_nat dn + -2)) by lia. (* [comment removed for export] *)
          hide_ors. ub. unhide.                              (* [comment removed for export] *)
          do 2 zstep.
          replace (DsdP + (Z.of_nat dn + -2) ≪ 3) with (DsdP + 8 * Z.of_nat dn - 16) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
          hide_ors. ub. zstep. ub. unhide.
          do 2 zstep.
          hide_ors. shl_with ACV ALV. chk0. unhide.
          assert (N1 : nth_error nbuf (dn - 2) = Some d1)
            by (unfold d1; replace (dn =? 1)%nat with false by (symmetry; apply Nat.eqb_neq; lia); apply nth_error_nth'; lia).
          let ad := cur_mem_addr in
            pose proof (limbs_at_read_nth bsegs mQ DsdP nbuf (dn - 2) d1 ad LAnb N1 ltac:(unfold wa; f_equal; clear - K1 DN1; lia)) as RD. (* [comment removed for export] *)
          zstep. clear RD.                                   (* [comment removed for export] *)
          step.                                              (* [comment removed for export] *)
          match goal with FRx : rw_cells _ ?mx (bv_unsigned sp + -304) _, STx : stk _ ?mx _ _, MIx : mem_inv _ ?mx, MUx : munch _ mP ?mx, WMx : wmono _ mP ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) => (* [comment removed for export] *)
            eapply JOIN; [exact FRx | exact STx | exact MIx | exact MUx | exact WMx] end.
        +                                                    (* [comment removed for export] *)
          step.                                              (* [comment removed for export] *)
          step.                                              (* [comment removed for export] *)
        (* [comment removed for export] *)
        (* [comment removed for export] *)
          replace (Z_to_bv 64 d1) with (Z_to_bv 64 0) in JOIN by (unfold d1; replace (dn =? 1)%nat with true by (symmetry; apply Nat.eqb_eq; lia); reflexivity).
          match goal with FRx : rw_cells _ ?mx (bv_unsigned sp + -304) _, STx : stk _ ?mx _ _, MIx : mem_inv _ ?mx, MUx : munch _ mP ?mx, WMx : wmono _ mP ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
            eapply JOIN; [exact FRx | exact STx | exact MIx | exact MUx | exact WMx] end. }
    intros mJ j1a j1b r10 r11 r12 r13 r14 FRJ STJ MIJ MUJ WMJ.
    match goal with FRx : rw_cells _ mQ (bv_unsigned sp + -304) _ |- _ => clear FRx | _ => idtac end.
    match goal with STx : stk _ mQ _ _ |- _ => clear STx | _ => idtac end. match goal with MIx : mem_inv _ mQ |- _ => clear MIx | _ => idtac end.
    match goal with MUx : munch _ mP mQ |- _ => clear MUx | _ => idtac end. match goal with WMx : wmono _ mP mQ |- _ => clear WMx | _ => idtac end.
    step.
    zstep.
    step.                                                   (* [comment removed for export] *)
    step.                                                   (* [comment removed for export] *)
    (* [comment removed for export] *)
    env_closeA HWLs WOKs ENVP LSP ENVQ LSQ.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LSP HAdvP) as HVdvP.
    pose proof (st_okm_getbn dv lsP SOKP HVdvP) as (_ & OKdvP2 & _).
    apply evt_done. unfold bbind at 1. cbn [bind tree_ops].
    eapply implA_bind.
    { eapply implA_leaves; [apply (bn_wexpand_leaves2 dv loop lsP HVdvP OKdvP2)|].
      eapply (bn_wexpand_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (r := dv) (a := adv) (OW := OWP) (LB := LB) (AD := AD) (EA := EA);
        [| | | reflexivity | exact HAdvP | reflexivity | reflexivity | unfold bn_dmax in *; lia].
      - eapply cenv_preA; [exact ENVQ | exact LSQ | unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO; lia | clear - USEDP; unfold MC in *; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ENVQ).
      - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_dv_wexp2 CTX). }
    cbv beta. intros [uR lsR] ΣR msR [PO LEAFR].
    apply (bn_postA_cpost LB AD EA lo (bv_unsigned sp) (bv_unsigned sp + -304) BN_DIV_FT_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 ENVQ))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & FR_ & fcR & mS & OWR & -> & CPR & (-> & HDMR & _ & BLKR)).
    lazymatch type of ENVQ with cenvA _ _ _ _ _ _ _ _ _ _ _ _ _ ?pre ?u _ _ _ _ =>
      assert (ER : cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -304) s0 ra (Some ras) BN_DIV_FT_COST Σ ls OW m pre (u + MC) ΣR lsR mS OWR /\ lib_state lsR mS OWR AD EA)
        by (eapply cenv_postA; [exact ENVQ | exact CPR]) end.
    destruct ER as (ENVR & LSR).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPR) as RSR.
    rewrite (ret_pc_even 0x252ac4) by lia. unfold MallocRep.wz.
    clear CPR.
    (* [comment removed for export] *)
    destruct LEAFR as ((R1 & R2 & R3 & R4 & R5) & RD & _). cbn [snd] in *.
    pose proof (RSR _ _ HAdvP) as HAdvR. pose proof (RSR _ _ HArmP) as HArmR. pose proof (RSR _ _ HAnumP) as HAnumR. pose proof (RSR _ _ HAdvsP) as HAdvsR.
    pose proof (RSR _ _ HAtmpP) as HAtmpR. pose proof (RSR _ _ HAsnumP) as HAsnumR. pose proof (RSR _ _ HAsdivP) as HAsdivR.
    assert (GSR : getbn sdiv lsR = sd3) by (rewrite R1 by (apply NPd; exact NPdv); exact GSP).
    assert (GNR : getbn snum lsR = getbn snum lsP) by (apply R1, NPs; exact NPdv).
    assert (GnumR : getbn num lsR = bnum) by (rewrite R1 by exact NEdn; apply NPgP; exact NPnum).
    assert (GdvsR : getbn dvs lsR = bd) by (rewrite R1 by exact NEdd; apply NPgP; exact NPdvs).
    (* [comment removed for export] *)
    assert (HinsnR : In (psn, DsnP, 8 * Z.of_nat (bn_dmax (getbn snum lsP))) OWR).
    { apply BLKR; [exact HinsnP|]. intros E.
      eapply (ids_bn_neq dv snum lsP psn psn (ids_m_nodup _ _ _ IDSP) HVdvP HVsnP (NPs dv NPdv) E Edsn). reflexivity. }
    clear BLKR RSR HAdvP HArmP HAnumP HAdvsP HAtmpP HAsnumP HAsdivP ENVP LSP ENVQ LSQ NDP IDSP ADBP ERRBP SOKP HVsdP HVsnP HVdvP OKdvP2
          BNsdP BNsnP ARRsdP ARRsnP UsdP UsnP HinsP HinnP HinsnP HinsdP LAnb ACV ALV OFV ACS ALS OFS ACVA ALVA OFVA ACSA ALSA OFSA SEPsnP.
    pose proof (AH_nodup_l _ _ _ _ (proj1 (proj2 ENVR))) as NDR.
    destruct (lib_state_h_parts _ _ _ _ _ _ LSR) as (IDSR & ADBR & ERRBR & SOKR).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LSR HAdvR) as HVdvR.
    destruct (lib_state_open [] lsR mS OWR AD EA num anum LSR NDR HAnumR ltac:(intros [])) as ((DnumR & BNnumR & _) & _ & _).
    destruct (lib_state_open [] lsR mS OWR AD EA dvs advs LSR NDR HAdvsR ltac:(intros [])) as ((DdvsR & BNdvsR & _) & _ & _).
    destruct (lib_state_open [] lsR mS OWR AD EA dv adv LSR NDR HAdvR ltac:(intros [])) as ((Ddv & BNdv & ARRdv) & (OKv1 & OKv2 & OKv3 & OKv4) & LSHR).
    rewrite GnumR in BNnumR. rewrite GdvsR in BNdvsR. unfold bn_cells in BNnumR, BNdvsR, BNdv.
    set (bv := getbn dv lsR) in *.
    destruct (ref_at_inb _ _ _ _ _ ADBR HAdvR) as (qv & Av & nv & _ & Hinv & Rv1 & Rv2).
    pose proof (AH_range _ _ _ _ _ _ _ (proj1 (proj2 ENVR)) Hinv) as (V0 & _ & _ & VC & VI).
    destruct (ref_at_inb _ _ _ _ _ ADBR HAnumR) as (qn & An & nn & _ & Hinn & Rn1 & Rn2).
    pose proof (AH_range _ _ _ _ _ _ _ (proj1 (proj2 ENVR)) Hinn) as (N0' & _ & _ & NC' & NI').
    destruct (ref_at_inb _ _ _ _ _ ADBR HAdvsR) as (qdR & AdR & ndR & _ & HindR & RdR1 & RdR2).
    pose proof (AH_range _ _ _ _ _ _ _ (proj1 (proj2 ENVR)) HindR) as (D0' & _ & _ & DC' & DI').
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ (proj1 (proj2 ENVR)) LSR HAnumR) as (ACNU & ALNU & OFNU).
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ (proj1 (proj2 ENVR)) LSR HAdvsR) as (ACDV & ALDV & OFDV).
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ (proj1 (proj2 ENVR)) LSR HAdvR) as (ACR & ALR & OFR).
    assert (ANUM : 0 < anum /\ anum + 24 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - N0' Rn1 Rn2 NC' CEIL LO SPR SPT; lia).
    assert (ADVS : 0 < advs /\ advs + 24 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - D0' RdR1 RdR2 DC' CEIL LO SPR SPT; lia).
    assert (ADV : 0 < adv /\ adv + 24 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - V0 Rv1 Rv2 VC CEIL LO SPR SPT; lia).

    assert (HDV : exists pv, bn_d bv = Some pv /\ In (pv, Ddv, 8 * Z.of_nat (bn_dmax bv)) OWR).
    { unfold bn_arr in ARRdv. destruct (bn_d bv) as [pv|]; [exists pv; split; [reflexivity| exact (proj1 ARRdv)]|].
      exfalso. destruct ARRdv as [_ E]. unfold bn_dmax in RD. rewrite E in RD. cbn in RD. clear - RD NP1. unfold loop in *. lia. }
    destruct HDV as (pv & Edv & Hinpv).
    pose proof (AH_range _ _ _ _ _ _ _ (proj1 (proj2 ENVR)) Hinpv) as (PV0 & PV16 & _ & PVC & _).
    assert (BDV : 0 < Ddv /\ Ddv + 8 * Z.of_nat (bn_dmax bv) <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - PV0 PVC CEIL LO SPR SPT; lia).
    assert (LOOPB : Z.of_nat loop <= Z.of_nat (bn_dmax bv) < 8388608) by (try unfold BN_WORDS_MAX in OKv3; clear - RD OKv3; lia).
    env_openA ENVR.
    match goal with MUx : munch _ mS mS |- _ => clear MUx end.
    pose proof (munch_refl [(bv_unsigned sp + -304, bv_unsigned sp); (adv, adv + 24)]%Z mS) as MUR.
    assert (OFFR : offshW [(bv_unsigned sp + -304, bv_unsigned sp); (adv, adv + 24)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; clear - OFR C2 CEIL LO; lia).
    apply hide_intro in OFNU. apply hide_intro in OFDV. apply hide_intro in OFR. apply hide_intro in VI. apply hide_intro in NI'. apply hide_intro in DI'.
    unfold MallocRep.wz in *. apply implA_from_evt.
    zstep. if_cases KZ; zify_cond KZ. { exfalso. rewrite ?unsigned_lit in KZ by lia. clear - KZ ADV. lia. }
    clear KZ.
    hide_ors. ub. unhide.                                    (* [comment removed for export] *)
    step.                                                    (* [comment removed for export] *)
    do 3 zstep.                                              (* [comment removed for export] *)
    shl_with ACNU ALNU. chk0.                                (* [comment removed for export] *)
    hide_ors. ub. unhide.                                    (* [comment removed for export] *)
    do 3 zstep.                                              (* [comment removed for export] *)
    shl_with ACDV ALDV.                                      (* [comment removed for export] *)
    step. rewrite (sx32_small (Z.b2z (bn_neg bnum))) by (destruct (bn_neg bnum); cbn; lia).
    chk0.
    do 3 zstep.                                             (* [comment removed for export] *)
    shl_with ACR ALR.                                       (* [comment removed for export] *)
    step. rewrite (sx32_small (Z.b2z (bn_neg bd))) by (destruct (bn_neg bd); cbn; lia).       (* [comment removed for export] *)
    chk0.
    zstep.                                                  (* [comment removed for export] *)
    setreg 11%Z (Z_to_bv 64 (Z.b2z (xorb (bn_neg bnum) (bn_neg bd)))) ltac:(f_equal; destruct (bn_neg bnum), (bn_neg bd); reflexivity).
    clear BNnumR BNdvsR Rn1 Rn2 RdR1 RdR2 N0' NC' D0' DC' DnumR DdvsR.
    zstep.                                                   (* [comment removed for export] *)
    zstep.                                                   (* [comment removed for export] *)
    do 2 zstep.                                              (* [comment removed for export] *)
    shl_with ACR ALR. chk0.                                  (* [comment removed for export] *)
    step.                                                    (* [comment removed for export] *)
    zstep.                                                   (* [comment removed for export] *)
    do 2 zstep.                                              (* [comment removed for export] *)
    shl_with ACR ALR. chk0.                                  (* [comment removed for export] *)
    step.                                                    (* [comment removed for export] *)
    step.                                                    (* [comment removed for export] *)
    zstep.                                                   (* [comment removed for export] *)
    setreg 19%Z (Z_to_bv 64 (Ddv + 8 * Z.of_nat loop)) ltac:(f_equal; lia). (* [comment removed for export] *)
    hide_ors. ub. unhide.                                    (* [comment removed for export] *)
    step.                                                    (* [comment removed for export] *)
    zstep. rewrite (bk_swrap32_small (Z.of_nat dn + 1)) by (unfold bn_dmax in *; lia). (* [comment removed for export] *)
    do 2 zstep.
    step.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mT end.
    apply evt_done. rewrite !bbind_get. rewrite GnumR, GdvsR. rewrite bbind_get_set. fold bv.
    set (q2 := mkBN (bn_d bv) (bn_buf bv) loop (xorb (bn_neg bnum) (bn_neg bd)) (bn_flags bv)).
    assert (WOKR : Forall (w_ok OWR LB lsR AD EA [dv]) [(bv_unsigned sp + -304, bv_unsigned sp); (adv, adv + 24)]).
    { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia|]. constructor; [eapply (w_struct OWR LB lsR AD EA false [dv] _ dv adv); [left; reflexivity| exact HAdvR| cbn; lia| cbn; lia]| constructor]. }
    assert (HWLR : Forall (w_lib OWR lo (bv_unsigned sp)) [(bv_unsigned sp + -304, bv_unsigned sp); (adv, adv + 24)]).
    { constructor; [left; cbn; lia|]. constructor; [right; exists (qv, Av, nv); cbn; auto| constructor]. }
    match goal with HEAPx : @BnHeapA.AHEAP _ ΣR OWR LB mS, STx : stk _ mT _ _, MIx : mem_inv _ mT, FRx : rw_cells _ mT (bv_unsigned sp + -304) _, WMx : wmono _ mS mT |- _ =>
      rename HEAPx into HEAPR; rename STx into STT; rename MIx into MIT; rename FRx into FRT; rename WMx into WMT end.
    assert (LST : lib_state (setbn dv q2 lsR) mT OWR AD EA).
    { unfold lib_state. eapply (lib_state_close [] lsR mT OWR AD EA dv adv); [| exact NDR| exact HAdvR| | |].
      - exact (lib_state_frame ΣR LB [dv] lsR mS mT OWR AD EA _ HEAPR LSHR MUR WMT WOKR).
      - exists Ddv. split.
        + unfold bn_cells, q2, bn_dmax. cbn [bn_top bn_buf bn_neg bn_flags]. exact BNdv.
        + unfold bn_arr, q2 in *. cbn [bn_d bn_buf bn_dmax] in *. rewrite Edv in ARRdv |- *.
          destruct ARRdv as [Hin Uarr]. split; [exact Hin|].
          eapply u64arr_transport; [exact Uarr | exact MUR | exact WMT |].
          pose proof (AH_range _ _ _ _ _ _ _ HEAPR Hin) as (_ & _ & _ & PC & _).
          pose proof (struct_limbs_disj ΣR OWR LB mS HEAPR lsR AD EA IDSR ADBR dv dv adv pv Ddv _ HAdvR HVdvR Edv Hin) as SLD.
          cbn [disjoint_from]. rewrite wlimbs_len. fold (bn_dmax bv). unfold BnHeapA.ACEIL in *. lia.
      - unfold bn_okm, q2, bn_dmax in *. cbn [bn_buf bn_top bn_flags]. split; [exact OKv1|]. split; [exact RD|]. split; [exact OKv3| exact OKv4].
      - apply ids_ok_setbn_same; [exact IDSR| exact HVdvR| reflexivity]. }
    lazymatch type of ENVR with cenvA _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?u _ _ _ _ =>
      lazymatch type of FRT with rw_cells _ _ _ ?fr' =>
        let pre' := drop2 fr' in
        assert (ENVT : cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -304) s0 ra (Some ras) BN_DIV_FT_COST Σ ls OW m pre' u ΣR (setbn dv q2 lsR) mT OWR);
        [ apply cenv_setbnA; [| exact HVdvR | reflexivity];
          eapply (cenv_silentA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -304) s0 ra (Some ras) BN_DIV_FT_COST Σ ls OW m);
            [exact ENVR | exact MUR | exact WMT | exact HWLR | exact STT | exact MIT | cbn [app]; exact FRT | cbn; lia]
        | ] end end.
    set (lsT := setbn dv q2 lsR) in *.
    assert (HAtmpT : ref_at lsT OWR AD tmp atmp) by (apply ref_at_setbn; exact HAtmpR).
    destruct (lib_state_h_parts _ _ _ _ _ _ LST) as (IDST & _ & _ & SOKT).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LST HAtmpT) as HVtT.
    pose proof (st_okm_getbn tmp lsT SOKT HVtT) as (_ & OKtT2 & _).
    (* [comment removed for export] *)
    unfold bbind at 1. cbn [bind tree_ops].
    eapply implA_bind.
    { eapply implA_leaves; [apply (bn_wexpand_leaves2 tmp (dn + 1) lsT HVtT OKtT2)|].
      eapply (bn_wexpand_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (r := tmp) (a := atmp) (OW := OWR) (LB := LB) (AD := AD) (EA := EA);
        [| | | reflexivity | exact HAtmpT | reflexivity | f_equal; f_equal; lia | unfold bn_dmax in *; lia].
      - eapply cenv_preA; [exact ENVT | exact LST | unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO; lia | clear - USEDP; unfold MC in *; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ENVT).
      - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_dv_wexp3 CTX). }
    cbv beta. intros [uU lsU] ΣU msU [PO LEAFU].
    apply (bn_postA_cpost LB AD EA lo (bv_unsigned sp) (bv_unsigned sp + -304) BN_DIV_FT_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 ENVT))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & FU & fcU & mU & OWU & -> & CPU & (-> & HDMU & _ & BLKU)).
    lazymatch type of ENVT with cenvA _ _ _ _ _ _ _ _ _ _ _ _ _ ?pre ?u _ _ _ _ =>
      assert (EU : cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -304) s0 ra (Some ras) BN_DIV_FT_COST Σ ls OW m pre (u + MC) ΣU lsU mU OWU /\ lib_state lsU mU OWU AD EA)
        by (eapply cenv_postA; [exact ENVT | exact CPU]) end.
    destruct EU as (ENVU & LSU).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPU) as RSU.
    rewrite (ret_pc_even 0x252bac) by lia. unfold MallocRep.wz.
    clear CPU.
    (* [comment removed for export] *)
    destruct LEAFU as ((U1 & U2 & U3 & U4 & U5) & UD & _). cbn [snd] in *.
    pose proof (RSU _ _ (proj2 (ref_at_setbn lsR OWR AD dv q2 _ _) HAdvR)) as HAdvU. pose proof (RSU _ _ (proj2 (ref_at_setbn lsR OWR AD dv q2 _ _) HArmR)) as HArmU.
    pose proof (RSU _ _ HAtmpT) as HAtmpU. pose proof (RSU _ _ (proj2 (ref_at_setbn lsR OWR AD dv q2 _ _) HAsnumR)) as HAsnumU.
    pose proof (RSU _ _ (proj2 (ref_at_setbn lsR OWR AD dv q2 _ _) HAsdivR)) as HAsdivU.
    assert (GSU : getbn sdiv lsU = sd3) by (rewrite U1 by exact NEtd; unfold lsT; rewrite getbn_setbn_other by (apply NPd; exact NPdv); exact GSR).
    assert (GNU : getbn snum lsU = getbn snum lsP) by (rewrite U1 by exact NEts; unfold lsT; rewrite getbn_setbn_other by (apply NPs; exact NPdv); exact GNR).
    assert (GVU : getbn dv lsU = q2) by (rewrite U1 by (apply not_eq_sym, NPt; exact NPdv); unfold lsT; apply getbn_setbn_same_m; exact HVdvR).
    assert (HinsnU : In (psn, DsnP, 8 * Z.of_nat (bn_dmax (getbn snum lsP))) OWU).
    { apply BLKU; [exact HinsnR|]. intros E.
      assert (HVsT : valid_refm snum lsT) by (apply valid_refm_setbn; destruct snum; try exact I; apply (ref_at_valid _ _ _ _ _ _ _ _ LSR HAsnumR)).
      eapply (ids_bn_neq tmp snum lsT psn psn (ids_m_nodup _ _ _ IDST) HVtT HVsT NEts E); [|reflexivity].
      unfold lsT. rewrite getbn_setbn_other by (apply NPs; exact NPdv). rewrite GNR. exact Edsn. }
    assert (HinpvU : In (pv, Ddv, 8 * Z.of_nat (bn_dmax bv)) OWU).
    { apply BLKU; [exact Hinpv|]. intros E.
      assert (HVvT : valid_refm dv lsT) by (apply valid_refm_setbn; exact HVdvR).
      eapply (ids_bn_neq tmp dv lsT pv pv (ids_m_nodup _ _ _ IDST) HVtT HVvT (fun E' => NPt dv NPdv (eq_sym E')) E); [|reflexivity].
      unfold lsT. rewrite getbn_setbn_same_m by exact HVdvR. exact Edv. }
    set (bsn := getbn snum lsP) in *.
    clear BLKU RSU HAdvR HArmR HAnumR HAdvsR HAtmpR HAsnumR HAsdivR HAtmpT ENVR LSR ENVT LST LSHR NDR IDSR ADBR ERRBR SOKR IDST SOKT HVtT OKtT2 HVdvR
          HinsnR Hinpv Hinv WOKR HWLR MUR BNdv ARRdv GSR GNR GnumR GdvsR R1 R2 R3 R4 R5 V0 VC VI Rv1 Rv2 HEAPR STT MIT FRT WMT ACNU ALNU OFNU ACDV ALDV OFDV ACR ALR OFR OFFR.
    assert (LOOP1 : (1 <= loop)%nat) by (unfold loop; lia).
    destruct (ref_at_inb _ _ _ _ _ (proj1 (proj2 (lib_state_h_parts _ _ _ _ _ _ LSU))) HAtmpU) as (qt & At & nt & _ & Hint & Rt1 & Rt2).
    pose proof (AH_range _ _ _ _ _ _ _ (proj1 (proj2 ENVU)) Hint) as (T0' & _ & _ & TC' & _).
    assert (ATMP : 0 < atmp /\ atmp + 24 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - T0' Rt1 Rt2 TC' CEIL LO SPR SPT; lia).
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ (proj1 (proj2 ENVU)) LSU HAtmpU) as (_ & ALTA & _).
    assert (RDN : 0 <= Z.of_nat dn < 4294967296) by (unfold bn_dmax in *; lia).
    env_openA ENVU.
    unfold MallocRep.wz in *. apply implA_from_evt.
    step.
    zstep. if_cases KZ; zify_cond KZ. { exfalso. rewrite ?unsigned_lit in KZ by lia. clear - KZ ATMP. lia. }
    clear KZ.
    step.                                                    (* [comment removed for export] *)
    zstep.                                                   (* [comment removed for export] *)
    step.                                                    (* [comment removed for export] *)
    do 2 zstep.                                              (* [comment removed for export] *)
    step.                                                    (* [comment removed for export] *)
    zstep.                                                   (* [comment removed for export] *)
    setreg 12%Z (Z_to_bv 64 1) ltac:(f_equal; symmetry; replace (0 <? atmp) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity). (* [comment removed for export] *)
    zstep.
    setreg 13%Z (Z_to_bv 64 0) ltac:(f_equal; symmetry; apply land7; exact ALTA).
    step.
    zstep. replace (Z.of_nat dn ≪ 3) with (8 * Z.of_nat dn) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    step.
    zstep.
    setreg 9%Z (Z_to_bv 64 0) ltac:(f_equal; symmetry; apply land7; clear - PV16; Z.div_mod_to_equations; lia).
    step.
    zstep.
    setreg 15%Z (Z_to_bv 64 0) ltac:(f_equal; symmetry; apply land7; clear - PSN16; Z.div_mod_to_equations; lia).
    step.
    zstep. replace (Z.of_nat dn ≪ 3) with (8 * Z.of_nat dn) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep.
    zstep.
    setreg 14%Z (Z_to_bv 64 0) ltac:(f_equal; symmetry; rewrite ub_lxor_sign63 by lia; rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity).
    step.
    zstep.
    remember (Z_to_bv 64 4294967295) as mask32 eqn:Emask.
    step. subst mask32.                                      (* [comment removed for export] *)
    zstep.                                                   (* [comment removed for export] *)
    step.                                                    (* [comment removed for export] *)
    zstep.                                                   (* [comment removed for export] *)
    zstep.                                                   (* [comment removed for export] *)
    setreg 21%Z (Z_to_bv 64 (shad atmp)) ltac:(f_equal; symmetry; apply shr3_shad; lia). (* [comment removed for export] *)
    zstep.                                                   (* [comment removed for export] *)
    setreg 10%Z (Z_to_bv 64 1) ltac:(reflexivity).
    step.
    step.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mL end.
    match goal with FRx : rw_cells _ mL (bv_unsigned sp + -304) _ |- _ => rename FRx into FRL end.
    replace (Z.land d1 4294967295) with (d1 mod 4294967296) in FRL by (change 4294967295 with (Z.ones 32); rewrite Z.land_ones by lia; reflexivity).
    rewrite (shr3_shad (asnum + 8)) in FRL by lia. rewrite (shr3_shad asdiv) in FRL by lia.
    env_closeA HWLs WOKs ENVU LSU ENVV LSV.
    apply evt_done.
    eapply (div_tailA) with (dv := dv) (rm := rm) (tmp := tmp) (snum := snum) (sdiv := sdiv) (adv := adv) (arm := arm) (atmp := atmp) (asnum := asnum) (asdiv := asdiv)
                            (psn := psn) (pv := pv) (sdbuf := nbuf) (negn := bn_neg bnum) (dn := dn) (loop := loop) (nP := nP) (d0 := d0) (d1 := d1) (sh := sh)
                            (DsnP := DsnP) (Ddv := Ddv) (ras := ras).
    { exact LO'. }
    { exact ENVV. }
    { clear - USEDP. unfold MC in *. lia. }
    { exact CTX. }
    { exact LSV. }
    { exact HAdvU. }
    { exact HArmU. }
    { exact HAtmpU. }
    { exact HAsnumU. }
    { exact HAsdivU. }
    { exact NEts. }
    { exact NEtd. }
    { exact NEsd. }
    { apply NPt. exact NPdv. }
    { apply NPs. exact NPdv. }
    { apply NPd. exact NPdv. }
    { rewrite GSU. reflexivity. }
    { rewrite GSU. exact C6b. }
    { exact HTOPD. }
    { reflexivity. }
    { reflexivity. }
    { exact (proj1 Rd0). }
    { rewrite GNU. exact TNP. }
    { unfold loop. lia. }
    { exact LOOP1. }
    { rewrite GNU. exact Edsn. }
    { rewrite GNU. exact HinsnU. }
    { rewrite GNU.
      apply (div_top_init (bn_buf bsn) (firstn tn (bn_buf bnum)) (firstn dn nbuf) sh dn tn nP).
      - exact OKp1.
      - rewrite <- TNP. exact OKp2.
      - exact HTOPD.
      - exact NP1.
      - exact NP2.
      - exact SH.
      - apply limbs_firstn. exact OKn1.
      - apply firstn_length_le. exact OKn2.
      - exact FNP.
      - apply limbs_firstn. exact LIMnb.
      - apply firstn_length_le. exact Lnb2.
      - rewrite nth_firstn. destruct (Nat.ltb_spec (dn - 1) dn); [exact (proj1 Rd0) | lia]. }
    { rewrite GVU. exact Edv. }
    { rewrite GVU. exact HinpvU. }
    { rewrite GVU. reflexivity. }
    { rewrite GVU. exact RD. }
    { exact UD. }
    { exact SH. } }
  apply implA_from_evt.
  zstep. rewrite lts_signed by (unfold bn_dmax in *; lia). if_cases KB; zify_cond KB.
  - (* [comment removed for export] *)
    apply evt_done.
    replace (tn + 1 <=? dn)%nat with false by (symmetry; apply Nat.leb_gt; lia).
    unfold bbind at 1. unfold bret at 1. cbn [bind ret tree_ops tbind fst snd].
    eapply (CONT Σ8 ls8 m12 OW8 (tn + 1)%nat); [exact ENV9 | unfold BN_DIV_FT_COST, MC; lia | exact LS8 | exact HAdv8 | exact HArm8 | exact HAnum8 | exact HAdvs8 | exact HAtmp8 | exact HAsnum8 | exact HAsdiv8
      | exact Esd8 | exact NPget8 | exact L8b | lia | lia | right; reflexivity | exact L8c | ].
    rewrite Nat.sub_diag. cbn [repeat]. rewrite app_nil_r. exact L8d.
  - (* [comment removed for export] *)
    apply evt_done.
    replace (tn + 1 <=? dn)%nat with true by (symmetry; apply Nat.leb_le; lia).
    lazymatch goal with |- implA (bbind _ _ ?REST0 _) _ ?Q _ =>
      eapply (div_padA REST0 Q) with (snum := snum) (asnum := asnum) (dn := dn) (tnp := (tn + 1)%nat) (lo := lo) (LB := LB) (AD := AD) (EA := EA) (ras := ras)
    end.
    { exact LO'. }
    { exact ENV9. }
    { unfold BN_DIV_FT_COST, MC. lia. }
    { exact CTX. }
    { exact LS8. }
    { exact HAsnum8. }
    { exact L8b. }
    { lia. }
    { unfold bn_dmax in *. lia. }
    intros ΣP lsP mP OWP FP' fcP' q1 q5 q6 q7 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 ENVP LSP RSP OTH TOPP NEGP FNP.
    eapply (CONT ΣP lsP mP OWP (dn + 1)%nat); [exact ENVP | unfold BN_DIV_FT_COST, MC; lia | exact LSP | apply RSP; exact HAdv8 | apply RSP; exact HArm8 | apply RSP; exact HAnum8
      | apply RSP; exact HAdvs8 | apply RSP; exact HAtmp8 | apply RSP; exact HAsnum8 | apply RSP; exact HAsdiv8 | | | exact TOPP | lia | lia | left; lia | | ].
    + rewrite OTH by (intros E; apply NEsd; symmetry; exact E). exact Esd8.
    + intros r NP. rewrite OTH by (apply NPs; exact NP). apply NPget8. exact NP.
    + rewrite NEGP. exact L8c.
    + rewrite FNP, L8d. reflexivity.
Qed.

End WithRT.
