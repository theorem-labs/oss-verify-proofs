(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA ZBridge RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Malloc Prog BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv BnDivSpec.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnMem BnTacX BnCalls.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnKit2 BnArr BnLeaves ShiftPure DivModel.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA BnRepX ImplA ImplAX BnIfaceA UnwindA EdgesA AsStruct RtCallA W_cryptoA W_expandA BnAKitA BnCallA AsStruct2 W_lshiftA W_div_tailA.
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
Ltac unhide := repeat match goal with H : hide _ |- _ => apply hide_elim in H end.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition pad_model (snum : bnref) (dn tnp : nat) : lstate bptr -> btree bptr (unit * lstate bptr) :=
  bbind (tree_ops bptr) (bn_wexpand (tree_ops bptr) snum (dn + 1)) (fun _ =>
  bbind (tree_ops bptr) (bget (tree_ops bptr) snum) (fun sn' =>
  bset (tree_ops bptr) snum (mkBN (bn_d sn') (splice (bn_buf sn') tnp (repeat 0 (dn - tnp + 1))) (dn + 1) (bn_neg sn') (bn_flags sn')))).

(* [comment removed for export] *)
Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Notation E_dv_wexp1 := (E_bn_div_fixed_top_24f418 : uk_call BN_DIV_FIXED_TOP 0x2528dc BN_WEXPAND).

(* [comment removed for export] *)
Section EnvI.
  Variables (LB : list block) (AD : bn_addrs) (EA : err_addrs) (lo SPv FB : Z) (s0w raw : word) (rasO : option (list Z)) (TOTAL : Z).
  Variables (Σ0 : rts RT) (ls0 : lstate bptr) (OW0 : list block) (m0 : mem).

  Lemma cenv_icallA : forall pre used Σ ls m m' OW d n b,
    cenvA LB AD lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m OW ->
    In b OW -> blk_addr b <= d -> d + n <= blk_addr b + blk_size b ->
    AHEAP Σ OW LB m' -> stk bsegs m' lo FB -> mem_inv bsegs m' ->
    agree_on (fun a => aclient_addr (OW ++ LB) FB a /\ ~ (d <= a < d + n)) m m' ->
    cenvA LB AD lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m' OW.
  Proof.
    intros pre used Σ ls m m' OW d n b (OK & HEAP & ST & MI & AXP & CR & CNT & RS & FR & FSZ & UW) Hb H1 H2 HEAP' ST' MI' AG.
    pose proof OK as (CEIL & LOFB & FBSP & SPT & _).
    pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_introl Hb))) as (_ & _ & _ & BC & _).
    assert (AG' : agree_on (fun a => FB <= a < USTACK_TOP) m m').
    { eapply agree_on_mono; [exact AG|]. intros a Ha. cbv beta in Ha. split; [left; exact Ha|]. unfold BnHeapA.ACEIL in *. lia. }
    unfold cenvA. split; [exact OK|]. split; [exact HEAP'|]. split; [exact ST'|]. split; [exact MI'|].
    split. { eapply ax_pres_trans; [exact AXP|]. eapply ax_pres_weaken; [eapply (ax_pres_of_icall Σ OW LB m m' FB LIBW_A d n b HEAP Hb H1 H2 ltac:(lia) AG) | clear - FBSP; lia]. }
    split; [exact CR|]. split; [exact CNT|]. split; [exact RS|].
    split. { eapply rw_cells_agree; [exact AG' | exact FR |]. intros a Ha. rewrite cells_size_app in Ha. cbn [cells_size csize Nat.add] in Ha.
             unfold USTACK_TOP in *. lia. }
    split; [exact FSZ|].
    unfold uw_opt in *. destruct rasO as [ras|]; [|exact I].
    apply (uw_chain_agree m m' ras SPv (bv_unsigned s0w) UW). eapply agree_on_mono; [exact AG'|]. intros a Ha. cbv beta in *. lia.
  Qed.
End EnvI.

Lemma div_padA : forall {Y : Type} (REST : unit -> lstate bptr -> btree bptr (Y * lstate bptr)) (Q : Y * lstate bptr -> rts RT -> machine_state -> Prop)
    (ra sp gp s0 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (Σ : rts RT) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs) (lo : Z) (ras : list Z) (TOTAL used : Z)
    (snum : bnref) (asnum ac : Z)
    (j0 : list byte) (sh arm : Z) (j1 j2 : list byte) (asdiv : Z) (j3 : list byte) (anum : Z) (j4 : list byte)
    (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 : word)
    (Σ8 : rts RT) (ls8 : lstate bptr) (m8 : mem) (OW8 : list block) (dn tnp : nat)
    (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word),
  lo <= bv_unsigned sp - BN_DIV_FT_STACK ->
  cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -304) s0 ra (Some ras) TOTAL Σ ls OW m
        (div_pre9 j0 asnum sh ac arm j1 j2 asdiv j3 anum dn j4 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) used Σ8 ls8 m8 OW8 ->
  used + MC <= TOTAL ->
  uk_ctx BN_DIV_FIXED_TOP (bv_unsigned ra :: ras) ->
  lib_state ls8 m8 OW8 AD EA ->
  ref_at ls8 OW8 AD snum asnum ->
  bn_top (getbn snum ls8) = tnp -> (tnp <= dn)%nat -> Z.of_nat dn + 1 < 2147483648 ->
  (forall ΣP lsP mP OWP (F' : bvmap 5 word) (fc' : bv 32) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
     cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -304) s0 ra (Some ras) TOTAL Σ ls OW m
        (div_pre9 j0 asnum sh ac arm j1 j2 asdiv j3 anum dn j4 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) (used + MC) ΣP lsP mP OWP ->
     lib_state lsP mP OWP AD EA -> refs_stable ls8 OW8 lsP OWP AD ->
     (forall r, r <> snum -> getbn r lsP = getbn r ls8) ->
     bn_top (getbn snum lsP) = (dn + 1)%nat -> bn_neg (getbn snum lsP) = bn_neg (getbn snum ls8) ->
     firstn (dn + 1) (bn_buf (getbn snum lsP)) = firstn tnp (bn_buf (getbn snum ls8)) ++ repeat 0 (dn + 1 - tnp) ->
     implA (REST tt lsP) ΣP Q
       (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -304)) gp (Z_to_bv 64 TP_A) y5 y6 y7 sp (Z_to_bv 64 (Z.of_nat (dn + 1)))
                (Z_to_bv 64 (Z.of_nat dn)) y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (asnum ≫ 3)) x19 x20 (Z_to_bv 64 (Z.of_nat tnp)) x22 x23 (Z_to_bv 64 SHB)
                x25 x26 (Z_to_bv 64 ac) y28 y29 y30 y31)
           F' (Z_to_bv 64 0x252960) fc' None mP (seg_rom bsegs))) ->
  implA (bbind (tree_ops bptr) (pad_model snum dn tnp) REST ls8) Σ8 Q
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -304)) gp (Z_to_bv 64 TP_A) x5 x6 x7 sp (Z_to_bv 64 (Z.of_nat tnp))
             (Z_to_bv 64 (Z.of_nat dn)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (asnum ≫ 3)) x19 x20 (Z_to_bv 64 (Z.of_nat tnp)) x22 x23 (Z_to_bv 64 SHB)
             x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x2528c8) fc None m8 (seg_rom bsegs)).
Proof.
  intros until x31. intros LO ENV8 USED CTX LS8 HAsn Etop HPAD HDN K.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  unfold BN_DIV_FT_STACK, BN_LSHIFT_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK in LO.
  pose proof ENV8 as (OK & HEAP8 & ST8 & MI8 & _).
  pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & CNT0 & CRED0).
  pose proof (AH_ceil _ _ _ _ HEAP8) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, SPT.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -304)) = bv_unsigned sp + -304) by (apply unsigned_lit; lia).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS8 HAsn) as HVsn.
  destruct (lib_state_h_parts _ _ _ _ _ _ LS8) as (IDS8 & ADB8 & ERRB8 & SOK8).
  pose proof (st_okm_getbn snum ls8 SOK8 HVsn) as (OK1 & OK2 & OK3 & OK4).
  destruct (ref_at_inb _ _ _ _ _ ADB8 HAsn) as (qs0 & As0 & ns0 & _ & Hins0 & Rs01 & Rs02).
  pose proof (AH_range _ _ _ _ _ _ _ HEAP8 Hins0) as (SA00 & _ & _ & SAC0 & _).
  assert (ASN : 0 < asnum /\ asnum + 24 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - SA00 Rs01 Rs02 SAC0 CEIL LO SPR SPT; lia).
  clear qs0 As0 ns0 Hins0 Rs01 Rs02 SA00 SAC0.
  env_openA ENV8.
  apply implA_from_evt.
  (* [comment removed for export] *)
  zstep. rewrite (bk_swrap32_small (Z.of_nat dn + 1)) by (clear - HDN; lia).
  hide_ors. ub. unhide.                                    (* [comment removed for export] *)
  step. do 2 zstep.
  match goal with FRx : rw_cells _ m8 (bv_unsigned sp + -304) _, STx : stk _ m8 _ _, MIx : mem_inv _ m8, MUx : munch _ m8 m8, WMx : wmono _ m8 m8, HEAPx : @BnHeapA.AHEAP _ Σ8 OW8 LB m8 |- _ =>
    clear FRx STx MIx MUx WMx HEAPx end.
  apply evt_done. unfold pad_model. unfold bbind at 1 2. cbn [bind tree_ops].
  apply implA_assoc.
  eapply implA_bind.
  { eapply implA_leaves; [apply (bn_wexpand_leaves2 snum (dn + 1) ls8 HVsn OK2)|].
    eapply (bn_wexpand_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (r := snum) (a := asnum) (OW := OW8) (LB := LB) (AD := AD) (EA := EA);
      [| | | reflexivity | exact HAsn | reflexivity | f_equal; f_equal; clear; lia | clear - HDN; lia].
    - eapply cenv_preA; [exact ENV8 | exact LS8 | unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO; lia | lia].
    - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ENV8).
    - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_dv_wexp1 CTX). }
  cbv beta. intros [u9 ls9] Σ9 ms9 [PO LEAF9].
  apply (bn_postA_cpost LB AD EA lo (bv_unsigned sp) (bv_unsigned sp + -304) TOTAL Σ ls OW) in PO; [| exact OK | exact HEAP8].
  cbn [fst snd] in *.
  destruct PO as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & F9 & fc9 & m9 & OW9 & -> & CP9 & (-> & HDM9 & _ & _)).
  assert (E9 : cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -304) s0 ra (Some ras) TOTAL Σ ls OW m
                 (div_pre9 j0 asnum sh ac arm j1 j2 asdiv j3 anum dn j4 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) (used + MC) Σ9 ls9 m9 OW9
               /\ lib_state ls9 m9 OW9 AD EA) by (eapply cenv_postA; [exact ENV8 | exact CP9]).
  destruct E9 as (ENV9 & LS9).
  pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP9) as RS9.
  rewrite (ret_pc_even 0x2528dc) by lia. unfold MallocRep.wz.
  clear CP9.
  destruct LEAF9 as ((W1 & W2 & W3 & W4 & W5) & _ & _). cbn [snd] in *. rewrite Etop in W2, W5.
  (* [comment removed for export] *)
  unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd].
  set (b9 := getbn snum ls9) in *.
  set (k := (dn - tnp + 1)%nat).
  (* [comment removed for export] *)
  pose proof (RS9 _ _ HAsn) as HAsn9.
  pose proof ENV9 as (_ & HEAP9 & ST9 & MI9 & _ & _ & _ & _ & FR9 & _ & _). unfold div_pre9 in FR9. cbn [app] in FR9.
  pose proof (AH_nodup_l _ _ _ _ HEAP9) as ND9.
  destruct (lib_state_h_parts _ _ _ _ _ _ LS9) as (IDS9 & ADB9 & ERRB9 & SOK9).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS9 HAsn9) as HVsn9.
  destruct (lib_state_open [] ls9 m9 OW9 AD EA snum asnum LS9 ND9 HAsn9 ltac:(intros [])) as ((D9 & BN9 & ARR9) & (OKa & OKb & OKc & OKd) & LSH9).
  fold b9 in BN9, ARR9, OKa, OKb, OKc, OKd.
  destruct (bn_arr_facts Σ9 OW9 LB m9 HEAP9 ls9 AD EA IDS9 ADB9 snum D9 HVsn9 ARR9) as (U9 & _ & D90 & D9C & D9I & SEP9).
  fold b9 in U9, D9C, D9I, SEP9.
  pose proof (SEP9 snum asnum HAsn9) as SEPs. clear SEP9.
  destruct (ref_at_inb _ _ _ _ _ ADB9 HAsn9) as (qs & As & ns & _ & Hins & Rs1 & Rs2).
  pose proof (AH_range _ _ _ _ _ _ _ HEAP9 Hins) as (SA0 & _ & _ & SAC & SAI).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP9 LS9 HAsn9) as (ACSA & ALSA & OFSA).
  destruct (arr_shA _ _ _ _ _ _ HEAP9 ARR9) as (ACS & ALS & OFS). fold b9 in ACS, OFS.
  assert (HD9 : exists p9, bn_d b9 = Some p9 /\ In (p9, D9, 8 * Z.of_nat (bn_dmax b9)) OW9).
  { unfold bn_arr in ARR9. destruct (bn_d b9) as [p9|]; [exists p9; split; [reflexivity| exact (proj1 ARR9)]|].
    exfalso. destruct ARR9 as [_ E]. unfold bn_dmax in HDM9. rewrite E in HDM9. cbn in HDM9. lia. }
  destruct HD9 as (p9 & Ed9 & Hinp9).
  pose proof (AH_range _ _ _ _ _ _ _ HEAP9 Hinp9) as (P90 & P916 & _ & _ & _).
  unfold bn_cells in BN9. unfold MallocRep.wz in *. unfold BN_WORDS_MAX in OKc.
  assert (Lb9 : length (bn_buf b9) = bn_dmax b9) by reflexivity.
  assert (Kk : (tnp + k <= bn_dmax b9)%nat) by (unfold k; clear - HDM9 HPAD; lia).
  assert (Ek : Z.of_nat k = Z.of_nat dn + 1 - Z.of_nat tnp) by (unfold k; clear - HPAD; lia).
  (* [comment removed for export] *)
  assert (BD9 : 0 <= D9 /\ D9 + 8 * Z.of_nat (bn_dmax b9) <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - D90 D9C CEIL LO SPR SPT; lia).
  destruct (proj1 (limbarr_split bsegs m9 D9 (bn_buf b9) tnp ltac:(rewrite Lb9; clear - Kk; lia)) U9) as (Ulo & Urest).
  destruct (proj1 (limbarr_split bsegs m9 (D9 + 8 * Z.of_nat tnp) (skipn tnp (bn_buf b9)) k ltac:(rewrite length_skipn, Lb9; clear - Kk; lia)) Urest) as (_ & Uhi).
  clear Urest U9.
  pose proof (munch_refl [(bv_unsigned sp + -304, bv_unsigned sp); (asnum, asnum + 24); (D9, D9 + 8 * Z.of_nat (bn_dmax b9))]%Z m9) as MU9.
  pose proof (wmono_refl bsegs m9) as WM9.
  assert (OFF9 : offshW [(bv_unsigned sp + -304, bv_unsigned sp); (asnum, asnum + 24); (D9, D9 + 8 * Z.of_nat (bn_dmax b9))]).
  { cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. clear - OFSA OFS C2 CEIL LO. lia. }
  assert (OFFa : offshW [(asnum, asnum + 24)]) by (cbn [offshW]; unfold SHLO, SHHI in *; clear - OFSA; lia).
  apply implA_from_evt.
  step.
  zstep. if_cases KZ; zify_cond KZ. { exfalso. rewrite ?unsigned_lit in KZ by lia. clear - KZ ASN. lia. }
  clear KZ.
  zstep.                                                   (* [comment removed for export] *)
  shl_with ACSA ALSA. chk0.                                (* [comment removed for export] *)
  step.                                                    (* [comment removed for export] *)
  step.                                                    (* [comment removed for export] *)
  do 2 zstep.                                              (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  replace (D9 + Z.of_nat tnp ≪ 3) with (D9 + 8 * Z.of_nat tnp) by (rewrite Z.shiftl_mul_pow2 by lia; lia).

  hide_ors. ub. zstep. ub. unhide.
  step.
  zstep.
  hide_ors. ub.
  zstep. rewrite (bk_swrap32_small (Z.of_nat dn - Z.of_nat tnp + 1)) by (clear - HDN HPAD; lia).
  ub. unhide.
  do 2 zstep.

  replace ((Z.of_nat dn - Z.of_nat tnp + 1) ≪ 3) with (8 * Z.of_nat k) by (rewrite Z.shiftl_mul_pow2 by lia; clear - Ek; lia).
  step.                                                    (* [comment removed for export] *)
  assert (INP9 : In (p9, D9, 8 * Z.of_nat (bn_dmax b9)) (OW9 ++ LB)) by (apply in_or_app; left; exact Hinp9).
  hide_ors.
  apply evt_done.
  eapply implA_step_same.
  { eapply (asan_memset_cpsA) with (d := D9 + 8 * Z.of_nat tnp) (n := 8 * Z.of_nat k) (c := Z_to_bv 8 0) (bd := (p9, D9, 8 * Z.of_nat (bn_dmax b9)))
                                   (lo := lo) (OW := OW9) (LB := LB); try reflexivity.
    - exact HEAP9.
    - rewrite ESP. exact ST9.
    - exact CEIL.
    - rewrite ESP. unfold RT_STACK. clear - LO; lia.
    - rewrite ESP. unfold USTACK_TOP. clear - SPT; lia.
    - rewrite ESP. exact FB16.
    - exact MI9.
    - exact INP9.
    - cbn [blk_addr blk_size fst snd]. clear; lia.
    - cbn [blk_addr blk_size fst snd]. clear - Kk; lia.
    - clear - Kk OKc Lb9; lia. }
  intros ms10 PO. unfold icall_post in PO. rewrite ?ESP in PO.
  destruct PO as (v0 & v1 & v2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & v3 & v4 & v5 & v6 & F10 & fc10 & m10 & -> & MI10 & ST10 & HEAP10 & WM10 & AG10 & BZ & WR10).
  rewrite (ret_pc_even 0x252948) by lia. unfold MallocRep.wz.
  unhide.
  (* [comment removed for export] *)
  pose proof (cenv_icallA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -304) s0 ra (Some ras) TOTAL Σ ls OW m _ _ _ _ _ _ _ (D9 + 8 * Z.of_nat tnp) (8 * Z.of_nat k) _
                ENV9 Hinp9 ltac:(cbn [blk_addr blk_size fst snd]; clear; lia) ltac:(cbn [blk_addr blk_size fst snd]; clear - Kk; lia) HEAP10 ST10 MI10 AG10) as ENV10.
  assert (LSH10 : lib_state_h [snum] ls9 m10 OW9 AD EA).
  { eapply (lib_state_h_icall Σ9 LB false [snum] ls9 m9 m10 OW9 AD EA _ (D9 + 8 * Z.of_nat tnp) (8 * Z.of_nat k) HEAP9 LSH9 AG10).
    eapply (w_limbs OW9 LB ls9 AD EA false [snum] _ snum p9 D9); [left; reflexivity| exact HVsn9| exact Ed9| exact Hinp9| cbn [fst snd]; clear; lia| cbn [fst snd]; fold b9; clear - Kk; lia]. }
  eapply (rw_cells_agree _ _ _ _ _ AG10) in FR9; [| intros x Hx; cbn in Hx; split; [left; unfold USTACK_TOP; clear - Hx SPT; lia | unfold BnHeapA.ACEIL in *; clear - Hx D9C CEIL LO Kk; lia]].
  eapply (rw_cells_agree _ _ _ _ _ AG10) in BN9; [| intros x Hx; cbn in Hx; split;
     [right; right; exists (qs, As, ns); split; [apply in_or_app; left; exact Hins | cbn; clear - Hx Rs1 Rs2; lia] | clear - Hx SEPs Kk; lia]].
  eapply (u64arr_agree _ _ _ _ _ AG10) in Ulo; [| intros x Hx; rewrite wlimbs_len, firstn_length_le in Hx by (rewrite Lb9; clear - Kk; lia); split;
     [right; right; exists (p9, D9, 8 * Z.of_nat (bn_dmax b9)); split; [exact INP9 | cbn [blk_addr blk_size fst snd]; clear - Hx Kk; lia] | clear - Hx; lia]].
  eapply (u64arr_agree _ _ _ _ _ AG10) in Uhi; [| intros x Hx; rewrite wlimbs_len, !length_skipn, Lb9 in Hx; split;
     [right; right; exists (p9, D9, 8 * Z.of_nat (bn_dmax b9)); split; [exact INP9 | cbn [blk_addr blk_size fst snd]; clear - Hx Kk; lia] | clear - Hx Kk; lia]].
  (* [comment removed for export] *)
  assert (POST : u64arr bsegs m10 (D9 + 8 * Z.of_nat tnp) (wlimbs (repeat 0 k))).
  { apply limbarr_limbs_at. rewrite repeat_length. split; [|exact WR10].
    unfold limbs_at. rewrite BnCalls.lbytes_repeat0. replace (8 * k)%nat with (Z.to_nat (8 * Z.of_nat k)) by (clear; lia). exact BZ. }
  assert (U10 : u64arr bsegs m10 D9 (wlimbs (splice (bn_buf b9) tnp (repeat 0 k)))).
  { unfold splice. rewrite repeat_length.
    apply limbarr_app. split; [exact Ulo|]. rewrite firstn_length_le by (rewrite Lb9; clear - Kk; lia).
    apply limbarr_app. split; [exact POST|]. rewrite repeat_length.
    replace (skipn (tnp + k) (bn_buf b9)) with (skipn k (skipn tnp (bn_buf b9))) by (rewrite skipn_skipn; f_equal; clear; lia).
    exact Uhi. }
  clear Ulo Uhi POST BZ WR10.
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP10 LSH10 HAsn9) as (ACSA10 & _ & _).
  (* [comment removed for export] *)
  apply hide_intro in SEPs. apply hide_intro in SAI. apply hide_intro in U10.
  pose proof (munch_refl [(asnum, asnum + 24)]%Z m10) as MUa. pose proof (wmono_refl bsegs m10) as WMa.
  clear MU9 WM9 ACSA ACS HEAP9 ST9 MI9 LSH9.
  apply implA_from_evt.
  step.                                                    (* [comment removed for export] *)
  shl_with ACSA10 ALSA. chk0.                              (* [comment removed for export] *)
  step.                                                    (* [comment removed for export] *)
  zstep.                                                   (* [comment removed for export] *)
  step.                                                    (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m11 end.
  apply hide_elim in U10. apply hide_elim in SEPs.
  eapply (u64arr_transport bsegs _ m10 m11) in U10; [| exact MUa | match goal with WMx : wmono _ m10 m11 |- _ => exact WMx end |
    cbn [disjoint_from]; rewrite wlimbs_len, splice_length by (rewrite repeat_length, Lb9; exact Kk); rewrite Lb9; split; [clear - SEPs; lia | exact I] ].
  (* [comment removed for export] *)
  set (SN := mkBN (bn_d b9) (splice (bn_buf b9) tnp (repeat 0 k)) (dn + 1) (bn_neg b9) (bn_flags b9)).
  assert (Lspl : length (splice (bn_buf b9) tnp (repeat 0 k)) = bn_dmax b9) by (rewrite splice_length by (rewrite repeat_length, Lb9; exact Kk); exact Lb9).
  assert (WOK : Forall (w_ok OW9 LB ls9 AD EA [snum]) [(asnum, asnum + 24)]).
  { constructor; [eapply (w_struct OW9 LB ls9 AD EA false [snum] _ snum asnum); [left; reflexivity| exact HAsn9| cbn; lia| cbn; lia]| constructor]. }
  assert (HWL : Forall (w_lib OW9 lo (bv_unsigned sp)) [(asnum, asnum + 24)]).
  { constructor; [right; exists (qs, As, ns); cbn; auto| constructor]. }
  match goal with MUx : munch _ m10 m11, WMx : wmono _ m10 m11, STx : stk _ m11 _ _, MIx : mem_inv _ m11, FRx : rw_cells _ m11 (bv_unsigned sp + -304) _ |- _ =>
    rename MUx into MUaF; rename WMx into WMaF; rename STx into ST11; rename MIx into MI11; rename FRx into FR11 end.
  assert (LSP : lib_state (setbn snum SN ls9) m11 OW9 AD EA).
  { unfold lib_state. eapply (lib_state_close [] ls9 m11 OW9 AD EA snum asnum); [| exact ND9 | exact HAsn9 | | |].
    - exact (lib_state_frame Σ9 LB [snum] ls9 m10 m11 OW9 AD EA _ HEAP10 LSH10 MUaF WMaF WOK).
    - exists D9. split.
      + unfold bn_cells, SN, bn_dmax, MallocRep.wz. cbn [bn_top bn_buf bn_neg bn_flags]. rewrite Lspl.
        replace (Z.of_nat (dn + 1)) with (Z.of_nat dn + 1) by (clear; lia). exact BN9.
      + unfold bn_arr, SN, bn_dmax. cbn [bn_d bn_buf]. rewrite Ed9, Lspl. split; [exact Hinp9 | exact U10].
    - try apply hide_elim in OKd. unfold bn_okm, SN, bn_dmax, BN_WORDS_MAX. cbn [bn_top bn_buf bn_flags]. rewrite Lspl.
      split; [apply splice_limbs; [exact OKa | apply limbs_repeat; exact limb_0]|]. split; [exact HDM9|]. split; [exact OKc| exact OKd].
    - apply ids_ok_setbn_same; [exact IDS9 | exact HVsn9 |]. fold b9. unfold bn_blocks, SN, bn_dmax. cbn [bn_d bn_buf]. rewrite Lspl. reflexivity. }
  assert (ENVP : cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -304) s0 ra (Some ras) TOTAL Σ ls OW m
                   (div_pre9 j0 asnum sh ac arm j1 j2 asdiv j3 anum dn j4 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) (used + MC) Σ9 (setbn snum SN ls9) m11 OW9).
  { apply cenv_setbnA; [| exact HVsn9 | fold b9; unfold bn_blocks, SN; cbn [bn_d bn_buf bn_dmax bn_top]; rewrite ?Ed9; reflexivity].
    eapply (cenv_silentA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -304) s0 ra (Some ras) TOTAL Σ ls OW m);
      [exact ENV10 | exact MUaF | exact WMaF | exact HWL | exact ST11 | exact MI11 | unfold div_pre9; cbn [app]; exact FR11 | cbn; lia]. }
  apply evt_done.
  replace (Z.of_nat dn + 1) with (Z.of_nat (dn + 1)) by (clear; lia).
  eapply K; [exact ENVP | exact LSP | | | | |].
  - intros r0 a0 H0. apply ref_at_setbn. apply RS9. exact H0.
  - intros r0 Hr0. rewrite getbn_setbn_other by (apply not_eq_sym; exact Hr0). apply W1. apply not_eq_sym. exact Hr0.
  - rewrite getbn_setbn_same_m by exact HVsn9. reflexivity.
  - rewrite getbn_setbn_same_m by exact HVsn9. cbn [SN bn_neg]. exact W3.
  - rewrite getbn_setbn_same_m by exact HVsn9. cbn [SN bn_buf].
    replace (dn + 1)%nat with (tnp + k)%nat by (unfold k; clear - HPAD; lia).
    rewrite firstn_pad_zeros by (rewrite Lb9; exact Kk). rewrite W5.
    replace (tnp + k - tnp)%nat with k by (clear; lia). reflexivity.
Qed.

End WithRT.
