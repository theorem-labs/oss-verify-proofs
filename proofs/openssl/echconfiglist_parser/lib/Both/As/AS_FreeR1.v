(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics F_memset
     AsDepotInv AsDepotHash AsDepotPut AsUnwind CidBits AW_Combined AW_PoisonShadow AW_Leaves AW_DepotFrame AW_AllocBase AllocWalkKit.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AW_MallocBase AW_FreeLeaves AW_IAInit AW_DeallocR AW_PutR1 AW_ReallocRet AS_Free1 AllocTacX.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

(* [comment removed for export] *)
Definition free_headR_post (sp gp tp cs0 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo U size b1 actx qcache TSD CTX TH sb TOP BOT : Z) (T : list Z) (d : depot) (RF : mem -> Prop) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR (wz 0x19b46c) (Z_to_bv 64 (bv_unsigned sp + -2288)) gp tp t0 t1 t2 (wz (AINST + OI_Q)) (wz (TH + OT_TQ))
                  (wz (TH + OT_TQ)) (wz (TH + OT_CACHE)) (Z_to_bv 64 (bv_unsigned sp + -2136)) (wz (U + -16)) (wz size) a5 a6 a7
                  (wz size) (Z_to_bv 64 (bv_unsigned sp + -2136)) (wz (TH + OT_CACHE)) (wz (U + -16)) (wz qcache) s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x19b478) fc None m' (seg_rom asegs)
    /\ munch (free_head_W lo (bv_unsigned sp) TH U size d) m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ IENV tp TSD CTX TH sb TOP BOT m'
    /\ stk asegs m' lo (bv_unsigned sp + -2288)
    /\ rw_cells asegs m' (bv_unsigned sp + -2288) (put_frameR sp cs0 cs2 cs3 cs4 cs5 s6 U TH)
    /\ RF m'
    (* [comment removed for export] *)
    /\ rw_cells asegs m' (U + -16) [C1 (b8 3); C1 (b8 b1); C2 (wz 0); C4 (wz size); C8 (wz actx)]
    /\ rw_cells asegs m' U [C8 (wz (d_putid d (depot_hash T)))]
    /\ stk asegs m' (TH + 2800) (TH + 3168)
    /\ DEPOT asegs (d_put d (depot_hash T) (Z.of_nat (length T))) m'
    /\ u8arr asegs m' (sh U) (repeat (b8 kAsanHeapFreeMagic) (Z.to_nat (nsh size))).
End HCW.

Section HeadR.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.
  Variables (sp gp tp x3 x4 x5 x12 x13 x14 x15 x16 x17 cs0 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo : Z) (d : depot).
  Variables (TSD CTX TH TOP BOT : Z) (sb : Z).
  Variables (U size b1 actx : Z) (ub : list byte) (qmax qmin qcache : Z) (sbs : list byte).
  Variables (T : list Z) (rest : list word) (RF : mem -> Prop).
  Let POST := free_headR_post sp gp tp cs0 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 F fc m lo U size b1 actx qcache TSD CTX TH sb TOP BOT T d RF.

  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 3024 <= bv_unsigned sp.
  Hypothesis SPA : hidden (bv_unsigned sp mod 16 = 0).
  Hypothesis SPT : hidden (bv_unsigned sp + 16 <= 2^47).
  Hypothesis TPR : hidden (12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP).
  Hypothesis RNG : hidden (12109808 <= TSD /\ TSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj TH 4096 /\ TH + 4096 <= aceil /\ TH mod 16 = 0).
  Hypothesis PLC : hidden ((TH + 4096 <= sb \/ sb + kSpaceSize + 4096 <= TH) /\ (CTX + 160 <= sb \/ sb + kSpaceSize + 4096 <= CTX)
                /\ (CTX + 160 <= TH \/ TH + 4096 <= CTX)).
  Hypothesis PLCD : hidden ((TH + 4096 <= d_nb d \/ d_nb d + 16 * 65536 <= TH) /\ (TH + 4096 <= d_sb d \/ d_sb d + 8 * 131072 <= TH)
                /\ (sb + kSpaceSize + 4096 <= d_nb d \/ d_nb d + 16 * 65536 <= sb) /\ (sb + kSpaceSize + 4096 <= d_sb d \/ d_sb d + 8 * 131072 <= sb)
                /\ (CTX + 160 <= d_nb d \/ d_nb d + 16 * 65536 <= CTX) /\ (CTX + 160 <= d_sb d \/ d_sb d + 8 * 131072 <= CTX)
                /\ aapp (d_nb d) (16 * 65536) /\ aapp (d_sb d) (8 * 131072)).
  Hypothesis PLU : hidden ((TH + 4096 <= U - 16 \/ U + 8 <= TH) /\ (CTX + 160 <= U - 16 \/ U + 8 <= CTX)
                /\ (d_nb d + 16 * 65536 <= U - 16 \/ U + 8 <= d_nb d) /\ (d_sb d + 8 * 131072 <= U - 16 \/ U + 8 <= d_sb d)).
  Hypothesis TBR : hidden (4096 <= TOP <= 2^47 /\ 0 <= BOT < TOP).
  Hypothesis DLO : d_nb d + 16 * 65536 <= lo /\ d_sb d + 8 * 131072 <= lo.
  Hypothesis DCAP : d_ids d + 1 < 65536 /\ d_frames d + 31 <= 131072.
  Hypothesis UR : hidden (aapp U (round_up size 8) /\ AIMG_TOP + 16 <= U /\ U + round_up size 8 <= aceil /\ U mod 16 = 0).
  Hypothesis SZ : 1 <= size < 2^32.
  Hypothesis B1 : 0 <= b1 < 256 /\ (b1 mod 128 = 17 \/ b1 mod 128 = 65).
  Hypothesis ACR : 0 <= actx < 2^64.
  Hypothesis QR : 0 < qcache < 2^64 /\ size <= qmax < 2^64 /\ 0 <= qmin < 2^64.
  Hypothesis SBS : Z.of_nat (length sbs) = nsh size.
  (* [comment removed for export] *)
  Hypothesis NR : (1 <= length T <= 30)%nat. Hypothesis TRNG : Forall (fun x => 0 <= x < 2^64) T.
  Hypothesis LR : length rest = (255 - length T)%nat.
  (* [comment removed for export] *)
  Hypothesis RFT : forall W m0 m1, RF m0 -> munch W m0 m1 -> wmono asegs m0 m1 -> disjoint_from W (bv_unsigned sp + -2208) 2208 ->
                   disjoint_from W (TH + 3168) 1 -> disjoint_from W AIAINIT 4 -> disjoint_from W AIAINST 0x81030 -> RF m1.
  Hypothesis RFE : forall m0, RF m0 ->
       rw_cells asegs m0 (bv_unsigned sp + -2136) [C8 (wz (bv_unsigned sp + -2136 + 16)); C8 (wz (Z.of_nat (length T)))]
    /\ u64arr asegs m0 (bv_unsigned sp + -2136 + 16) (map wz T ++ rest).

  Theorem free_headR :
    IENV tp TSD CTX TH sb TOP BOT m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -2208) ->
    RF m -> DEPOT asegs d m ->
    rw_cells asegs m (U + -16) [C1 (b8 2); C1 (b8 b1); C2 (wz 0); C4 (wz size); C8 (wz actx)] ->
    rw_cells asegs m U [CB 8 ub] ->
    stk asegs m (TH + 2800) (TH + 3168) ->
    rw_cells asegs m (AINST + OI_QMAX) [C8 (wz qmax); C8 (wz qmin); C8 (wz qcache)] ->
    u8arr asegs m (sh U) sbs ->
    evt asegs POST
      (MS (mkR (wz 0x197a10) (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp x3 x4 x5 cs0 (wz U) (wz AINST) (wz U) (wz 0) (wz 0)
               (Z_to_bv 64 (bv_unsigned sp + -2136)) (wz 1) x12 x13 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 x14 x15 x16 x17)
          F (Z_to_bv 64 0x196ae8) fc None m (seg_rom asegs)).
  Proof.
    intros ENV MI ST RF0 DEP HDR UB TST QC SH.
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR.
    assert (BND : aceil <= lo /\ 12599296 <= CTX /\ CTX + 160 <= aceil /\ 4096 <= TH /\ TH + 4096 <= aceil
               /\ bv_unsigned sp + 16 <= 140737488355328 /\ 12599312 <= U /\ U + round_up size 8 <= aceil /\ 140735193776128 <= aceil /\ size <= round_up size 8 /\ 8 <= round_up size 8
               /\ 12599296 <= d_nb d /\ 12599296 <= d_sb d).
    { clear - LO RNG SPT UR PLCD SZ; try acb. destruct RNG as [RNG']; destruct UR as [UR']; destruct PLCD as [PLCD']; destruct SPT as [SPT'].
      unfold AHI_LO, round_up in *; acb. change (2^47)%Z with 140737488355328%Z in SPT'. aunf. repeat split; try lia; Z.div_mod_to_equations; lia. }
    region_sides. name_bands.
    assert (PLUb : (TH + 4096 <= U - 16 \/ U + 8 <= TH)) by (destruct PLU as [X]; clear - X; tauto).
    assert (PLDb : (TH + 4096 <= d_nb d \/ d_nb d + 16 * 65536 <= TH) /\ (TH + 4096 <= d_sb d \/ d_sb d + 8 * 131072 <= TH)) by (destruct PLCD as [X]; clear - X; tauto).
    assert (SHR : 2148314624 <= sh U /\ sh U + nsh size <= 17594333495296) by (unfold sh, nsh, ASHADOW_BASE; clear - BND SZ; try acb; Z.div_mod_to_equations; lia).
    assert (USH : sh U + nsh size <= U - 16 \/ U + round_up size 8 <= sh U) by (destruct UR as [[UA UX]]; clear - UA UX; acb; unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, ALOWSH_LO, AHI_LO, sh, nsh, round_up, ASHADOW_BASE in *; Z.div_mod_to_equations; lia).
    pose proof SHR as SHR'. rewrite <- (Z2Nat.id (nsh size)) in SHR' by (unfold nsh; clear - SZ; Z.div_mod_to_equations; lia). rewrite <- SBS in SHR'.
    destruct (RFE _ RF0) as [ESO TRB].
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply (@deallocR_seg _ sp gp tp x3 x4 x5 x12 x13 x14 x15 x16 x17 s6 s7 s8 s9 s10 s11 cs0 cs2 cs3 cs4 cs5 F fc m lo U size b1 actx ub T rest d TSD CTX TH TOP BOT sb).
      all: try eassumption.
      - clear - HI; try acb; lia.
      - destruct UR as [X]. constructor. destruct X as [XA X]. split; [apply (aapp_sub _ _ _ _ XA); clear - BND; lia| clear - X BND; lia].
      - destruct PLC as [X]. constructor. clear - X. tauto.
      - destruct PLCD as [X]. constructor. clear - X. tauto.
      - clear - DCAP NR. lia. }
    cbv beta. intros ms2 PO2.
    destruct PO2 as (t0_2 & t1_2 & t2_2 & a6_2 & a7_2 & t3_2 & t4_2 & t5_2 & t6_2 & m2 & -> & MU2 & WM2 & MI2 & ST2 & HDR2 & UW2 & TST2 & DEP2).
    (* [comment removed for export] *)
    assert (ENV2 : IENV tp TSD CTX TH sb TOP BOT m2).
    { eapply (@AW_DeallocR.ienv_now_d _ sp tp m lo U b1 T rest d TSD CTX TH TOP BOT sb); try eassumption.
      - destruct UR as [X]. constructor. destruct X as [XA X]. split; [apply (aapp_sub _ _ _ _ XA); clear - BND; lia| clear - X BND; lia].
      - destruct PLC as [X]. constructor. clear - X. tauto.
      - destruct PLCD as [X]. constructor. clear - X. tauto. }
    unfold depot_W in MU2.
    assert (QC2 : rw_cells asegs m2 (AINST + OI_QMAX) [C8 (wz qmax); C8 (wz qmin); C8 (wz qcache)])
      by (eapply rw_cells_transport; [exact QC| exact MU2| exact WM2| unfold AINST, OI_QMAX; cbn [disjoint_from cells_size csize length Nat.add Nat.mul app]; region_decide]).
    assert (SH2 : u8arr asegs m2 (sh U) sbs)
      by (eapply u8arr_transport; [exact SH| exact MU2| exact WM2| cbn [disjoint_from app]; region_decide]).
    assert (RF2 : RF m2) by (eapply (RFT _ _ _ RF0 MU2 WM2); unfold AIAINIT, AIAINST; cbn [disjoint_from app]; match goal with TB : akobj TH 4096 |- _ => clear - BND HI DLO SPR PLUb PLDb TB end; try acb; aunf; lia).
    clear QC SH.
    eapply evt_cut.
    { eapply (@put_headR _ sp gp tp t0_2 t1_2 t2_2 a6_2 a7_2 t3_2 t4_2 t5_2 t6_2 s6 s7 s8 s9 s10 s11 cs0 cs2 cs3 cs4 cs5 F fc m2 lo U size b1 actx qmax qmin qcache sbs TSD CTX TH TOP BOT sb).
      all: try eassumption. clear - HI; try acb; lia. }
    cbv beta. intros ms3 PO3.
    destruct PO3 as (t0_3 & t1_3 & t2_3 & a5_3 & a6_3 & a7_3 & t3_3 & t4_3 & t5_3 & t6_3 & m3 & -> & MU3 & WM3 & MI3 & ST3 & PFR3 & SHD3).
    assert (ENV3 : IENV tp TSD CTX TH sb TOP BOT m3).
    { eapply (@ienv_now_pR _ sp tp m2 lo U size sbs TSD CTX TH TOP BOT sb); try eassumption. }
    assert (RF3 : RF m3) by (eapply (RFT _ _ _ RF2 MU3 WM3); unfold AIAINIT, AIAINST; cbn [disjoint_from app]; match goal with TB : akobj TH 4096 |- _ => clear - BND HI SHR SPR USH PLUb TB end; try acb; aunf; lia).
    apply evt_done. unfold POST, free_headR_post.
    exists t0_3, t1_3, t2_3, a5_3, a6_3, a7_3, t3_3, t4_3, t5_3, t6_3, m3.
    split; [reflexivity|].
    (* [comment removed for export] *)
    assert (SUB2 : sub_fp ([(lo, bv_unsigned sp + -2208); (U + -16, U + -12); (U, U + 8); (TH + 2800, TH + 3168)] ++
                           [(7915480, 12109800 + 8); (7849928, 7849928 + 28); (d_nb d, d_nb d + 16 * 65536); (d_sb d, d_sb d + 8 * 131072)])
                          (free_head_W lo (bv_unsigned sp) TH U size d)).
    { unfold free_head_W, depot_W, AIAINIT, AIAINST, sub_fp. intros x Hx. cbn [outside app] in *.
      destruct Hx as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & _). clear - X1 X5 X6 X7 X9 X10 X11 X12.
      repeat split; try assumption. clear - X1. lia. }
    assert (SUB3 : sub_fp [(lo, bv_unsigned sp + -2208); (sh U, sh U + nsh size)] (free_head_W lo (bv_unsigned sp) TH U size d)).
    { unfold free_head_W, depot_W, AIAINIT, AIAINST, sub_fp. intros x Hx. cbn [outside app] in *.
      destruct Hx as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & _). clear - X1 X8. repeat split; try assumption. clear - X1. lia. }
    split. { eapply munch_trans; [eapply munch_weaken; [exact SUB2| exact MU2]| eapply munch_weaken; [exact SUB3| exact MU3]]. }
    split. { eapply wmono_trans; [exact WM2| exact WM3]. }
    split; [exact MI3|]. split; [exact ENV3|]. split; [exact ST3|]. split; [exact PFR3|]. split; [exact RF3|].
    eapply rw_cells_transport in HDR2; [| exact MU3| exact WM3| cbn [disjoint_from cells_size csize length Nat.add Nat.mul app]; region_decide].
    split; [exact HDR2|].
    eapply rw_cells_transport in UW2; [| exact MU3| exact WM3| cbn [disjoint_from cells_size csize length Nat.add Nat.mul app]; region_decide].
    split; [exact UW2|].
    split. { eapply stk_transport_disjoint; [exact TST2| exact MU3| exact WM3| cbn [disjoint_from app]; region_decide]. }
    split. { eapply (DEPOT_transport asegs _ _ m3) in DEP2; [exact DEP2| exact MU3 | exact WM3 |].
             unfold depot_avoid, avoids. rewrite ?d_nb_put, ?d_sb_put. cbn [fst snd].
             repeat split; repeat (first [apply Forall_nil | apply Forall_cons; [cbn [fst snd]; first [clear - BND SHR DLO; try acb; lia | region_decide] |]]). }
    exact SHD3.
  Qed.
End HeadR.
