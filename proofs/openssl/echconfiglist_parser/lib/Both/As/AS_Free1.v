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
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AW_MallocBase AW_FreeLeaves AW_IAInit AW_FreePre AW_Dealloc AW_Put1 AllocTacX.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

(* [comment removed for export] *)
Definition free_head_W (lo spv TH U size : Z) (d : depot) : list ivl :=
  [(lo, spv); (TH + 3168, TH + 3169); (AIAINIT, AIAINIT + 4); (AIAINST, AIAINST + 0x81030);
   (U + -16, U + -12); (U, U + 8); (TH + 2800, TH + 3168); (sh U, sh U + nsh size)] ++ depot_W d.

(* [comment removed for export] *)
Definition free_head_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo U size b1 actx qcache TSD CTX TH sb TOP BOT : Z) (T : list Z) (d : depot) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) (jk : list byte) (rest : list word) m',
    ms' = MS (mkR (wz 0x19b46c) (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp t0 t1 t2 (wz (AINST + OI_Q)) (wz (TH + OT_TQ))
                  (wz (TH + OT_TQ)) (wz (TH + OT_CACHE)) (Z_to_bv 64 (bv_unsigned sp + -2128)) (wz (U + -16)) (wz size) a5 a6 a7
                  (wz size) (Z_to_bv 64 (bv_unsigned sp + -2128)) (wz (TH + OT_CACHE)) (wz (U + -16)) (wz qcache) s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x19b478) fc None m' (seg_rom asegs)
    /\ munch (free_head_W lo (bv_unsigned sp) TH U size d) m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ IENV tp TSD CTX TH sb TOP BOT m'
    /\ stk asegs m' lo (bv_unsigned sp + -2208)
    /\ rw_cells asegs m' (bv_unsigned sp + -2208) (put_frame sp s6 U TH)
    (* [comment removed for export] *)
    /\ rw_cells asegs m' (bv_unsigned sp + -2128) [C8 (wz (bv_unsigned sp + -2128 + 16)); C8 (wz (Z.of_nat (length T)))]
    /\ u64arr asegs m' (bv_unsigned sp + -2128 + 16) (map wz T ++ rest) /\ length rest = (255 - length T)%nat
    /\ rw_cells asegs m' (bv_unsigned sp + -72) [C8 sp]
    /\ rw_cells asegs m' (bv_unsigned sp + -64) [CB 8 jk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ Forall (fun x => 0 <= x < 2^64) T /\ (1 <= length T <= 30)%nat
    (* [comment removed for export] *)
    /\ rw_cells asegs m' (U + -16) [C1 (b8 3); C1 (b8 b1); C2 (wz 0); C4 (wz size); C8 (wz actx)]
    /\ rw_cells asegs m' U [C8 (wz (d_putid d (depot_hash T)))]
    /\ stk asegs m' (TH + 2800) (TH + 3168)
    /\ rw_cells asegs m' (TH + 3168) [C1 (b8 0)]
    /\ rw_cells asegs m' AIAINIT [C1 (b8 1); C1 (b8 0); C2 (wz 0)] /\ ia_after m'
    /\ DEPOT asegs (d_put d (depot_hash T) (Z.of_nat (length T))) m'
    /\ u8arr asegs m' (sh U) (repeat (b8 kAsanHeapFreeMagic) (Z.to_nat (nsh size))).
End HCW.

Section Head.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo : Z) (d : depot) (inited : bool).
  Variables (TSD CTX TH TOP BOT : Z) (CH : list (Z * Z)) (sb : Z).
  Variables (U size b1 actx : Z) (ub : list byte) (qmax qmin qcache : Z) (sbs : list byte).
  Let CHI := icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) TOP CH.
  Let T := utrace 0x1bf2bc (bv_unsigned sp) TOP BOT 30 CHI.
  Let POST := free_head_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo U size b1 actx qcache TSD CTX TH sb TOP BOT T d.

  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 2944 <= bv_unsigned sp.
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
  Hypothesis FCH : goodframe BOT (bv_unsigned sp) TOP = true -> goodframe (bv_unsigned sp) (bv_unsigned s0) TOP = true ->
                   bv_unsigned sp + 16 <= bv_unsigned s0 /\ frame_chain asegs m TOP (bv_unsigned s0) CH.
  Hypothesis Ha0 : a0 = wz U.
  Hypothesis UR : hidden (aapp U (round_up size 8) /\ AIMG_TOP + 16 <= U /\ U + round_up size 8 <= aceil /\ U mod 16 = 0).   (* [comment removed for export] *)
  Hypothesis SZ : 1 <= size < 2^32.
  Hypothesis B1 : 0 <= b1 < 256 /\ (b1 mod 128 = 17 \/ b1 mod 128 = 65).
  Hypothesis ACR : 0 <= actx < 2^64.
  Hypothesis QR : 0 < qcache < 2^64 /\ size <= qmax < 2^64 /\ 0 <= qmin < 2^64.
  Hypothesis SBS : Z.of_nat (length sbs) = nsh size.

  Theorem free_head :
    IENV tp TSD CTX TH sb TOP BOT m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) ->
    rw_cells asegs m (TH + 3168) [C1 (b8 0)] ->
    rw_cells asegs m AIAINIT [C1 (b8 (if inited then 1 else 0)); C1 (b8 0); C2 (wz 0)] ->
    (if inited then ia_after m else ia_pristine m) ->
    DEPOT asegs d m ->
    rw_cells asegs m (U + -16) [C1 (b8 2); C1 (b8 b1); C2 (wz 0); C4 (wz size); C8 (wz actx)] ->
    rw_cells asegs m U [CB 8 ub] ->
    stk asegs m (TH + 2800) (TH + 3168) ->
    rw_cells asegs m (AINST + OI_QMAX) [C8 (wz qmax); C8 (wz qmin); C8 (wz qcache)] ->
    u8arr asegs m (sh U) sbs ->
    evt asegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1bf184) fc None m (seg_rom asegs)).
  Proof.
    intros ENV MI ST UNW FLG IA DEP HDR UB TST QC SH.
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR.
    assert (BND : aceil <= lo /\ 12599296 <= CTX /\ CTX + 160 <= aceil /\ 4096 <= TH /\ TH + 4096 <= aceil
               /\ bv_unsigned sp + 16 <= 140737488355328 /\ 12599312 <= U /\ U + round_up size 8 <= aceil /\ 140735193776128 <= aceil /\ size <= round_up size 8 /\ 8 <= round_up size 8
               /\ 12599296 <= d_nb d /\ 12599296 <= d_sb d).
    { clear - LO RNG SPT UR PLCD SZ; try acb. destruct RNG as [RNG']; destruct UR as [UR']; destruct PLCD as [PLCD']; destruct SPT as [SPT'].
      unfold AHI_LO, round_up in *; acb. change (2^47)%Z with 140737488355328%Z in SPT'. aunf. repeat split; try lia; Z.div_mod_to_equations; lia. }   (* [comment removed for export] *)
    assert (P47 : bv_unsigned a0 < 2^47) by (rewrite Ha0; unfold wz; rewrite unsigned_lit by (clear - BND SZ; try acb; lia); clear - BND SZ; try acb; lia).
    region_sides. name_bands.
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply (@free_pre _ ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo d inited TSD CTX TH TOP BOT CH sb).
      all: try eassumption. clear - HI; try acb; lia. }
    cbv beta. intros ms1 PO1.
    destruct PO1 as (x3 & x4 & x5 & x12 & x13 & x14 & x15 & x16 & x17 & jk & rest & m1 & -> & MU1 & WM1 & MI1 & ENV1 & ST1 & ESO1 & TRB1 & LR1 & TFB1 & F41
                     & UNW1 & DEP1 & TRNG & NR & FLG1 & IA1).
    fold CHI in ESO1, TRB1, LR1, TRNG, NR. fold T in ESO1, TRB1, LR1, TRNG, NR.
    (* [comment removed for export] *)
    unfold AIAINIT, AIAINST in MU1.
    assert (PLUb : (TH + 4096 <= U - 16 \/ U + 8 <= TH)) by (destruct PLU as [X]; clear - X; tauto).
    assert (PLDb : (TH + 4096 <= d_nb d \/ d_nb d + 16 * 65536 <= TH) /\ (TH + 4096 <= d_sb d \/ d_sb d + 8 * 131072 <= TH)) by (destruct PLCD as [X]; clear - X; tauto).
    assert (SHR : 2148314624 <= sh U /\ sh U + nsh size <= 17594333495296) by (unfold sh, nsh, ASHADOW_BASE; clear - BND SZ; try acb; Z.div_mod_to_equations; lia).
    assert (USH : sh U + nsh size <= U - 16 \/ U + round_up size 8 <= sh U) by (destruct UR as [[UA UX]]; clear - UA UX; acb; unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, ALOWSH_LO, AHI_LO, sh, nsh, round_up, ASHADOW_BASE in *; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
    pose proof SHR as SHR'. rewrite <- (Z2Nat.id (nsh size)) in SHR' by (unfold nsh; clear - SZ; Z.div_mod_to_equations; lia). rewrite <- SBS in SHR'.
    assert (HDR1 : rw_cells asegs m1 (U + -16) [C1 (b8 2); C1 (b8 b1); C2 (wz 0); C4 (wz size); C8 (wz actx)])
      by (eapply rw_cells_transport; [exact HDR| exact MU1| exact WM1| cbn [disjoint_from cells_size csize length Nat.add Nat.mul]; region_decide]).
    assert (UB1 : rw_cells asegs m1 U [CB 8 ub])
      by (eapply rw_cells_transport; [exact UB| exact MU1| exact WM1| cbn [disjoint_from cells_size csize length Nat.add Nat.mul]; region_decide]).
    assert (TST1 : stk asegs m1 (TH + 2800) (TH + 3168))
      by (eapply stk_transport_disjoint; [exact TST| exact MU1| exact WM1| cbn [disjoint_from]; match goal with TB : akobj TH 4096 |- _ => clear - BND TB end; try acb; aunf; lia]).   (* [comment removed for export] *)
    assert (QC1 : rw_cells asegs m1 (AINST + OI_QMAX) [C8 (wz qmax); C8 (wz qmin); C8 (wz qcache)])
      by (eapply rw_cells_transport; [exact QC| exact MU1| exact WM1| unfold AINST, OI_QMAX; cbn [disjoint_from cells_size csize length Nat.add Nat.mul]; region_decide]).
    assert (SH1 : u8arr asegs m1 (sh U) sbs)
      by (eapply u8arr_transport; [exact SH| exact MU1| exact WM1| cbn [disjoint_from]; region_decide]).
    clear HDR UB TST QC SH.
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply (@dealloc_seg _ sp gp tp x3 x4 x5 x12 x13 x14 x15 x16 x17 s6 s7 s8 s9 s10 s11 a0 F fc m1 lo U size b1 actx ub T rest d TSD CTX TH TOP BOT sb).
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
    { eapply (@ienv_now_d _ sp tp m1 lo U b1 T rest d TSD CTX TH TOP BOT sb); try eassumption.
      - destruct UR as [X]. constructor. destruct X as [XA X]. split; [apply (aapp_sub _ _ _ _ XA); clear - BND; lia| clear - X BND; lia].
      - destruct PLC as [X]. constructor. clear - X. tauto.
      - destruct PLCD as [X]. constructor. clear - X. tauto. }
    unfold depot_W in MU2.
    assert (QC2 : rw_cells asegs m2 (AINST + OI_QMAX) [C8 (wz qmax); C8 (wz qmin); C8 (wz qcache)])
      by (eapply rw_cells_transport; [exact QC1| exact MU2| exact WM2| unfold AINST, OI_QMAX; cbn [disjoint_from cells_size csize length Nat.add Nat.mul app]; region_decide]).
    assert (SH2 : u8arr asegs m2 (sh U) sbs)
      by (eapply u8arr_transport; [exact SH1| exact MU2| exact WM2| cbn [disjoint_from app]; region_decide]).
    clear QC1 SH1.
    eapply evt_cut.
    { eapply (@put_head _ sp gp tp t0_2 t1_2 t2_2 a6_2 a7_2 t3_2 t4_2 t5_2 t6_2 s6 s7 s8 s9 s10 s11 F fc m2 lo U size b1 actx qmax qmin qcache sbs TSD CTX TH TOP BOT sb).
      all: try eassumption. clear - HI; try acb; lia. }
    cbv beta. intros ms3 PO3.
    destruct PO3 as (t0_3 & t1_3 & t2_3 & a5_3 & a6_3 & a7_3 & t3_3 & t4_3 & t5_3 & t6_3 & m3 & -> & MU3 & WM3 & MI3 & ST3 & PFR3 & SHD3).
    (* [comment removed for export] *)
    assert (ENV3 : IENV tp TSD CTX TH sb TOP BOT m3).
    { eapply (@ienv_now_p _ sp tp m2 lo U size sbs TSD CTX TH TOP BOT sb); try eassumption. }
    apply evt_done. unfold POST, free_head_post.
    exists t0_3, t1_3, t2_3, a5_3, a6_3, a7_3, t3_3, t4_3, t5_3, t6_3, jk, rest, m3.
    split; [reflexivity|].
    (* [comment removed for export] *)
    assert (SUB1 : sub_fp [(lo, bv_unsigned sp); (TH + 3168, TH + 3169); (7578504, 7578504 + 4); (6994688, 6994688 + 528432)]
                          (free_head_W lo (bv_unsigned sp) TH U size d)).
    { unfold free_head_W, depot_W, AIAINIT, AIAINST, sub_fp. intros x Hx. cbn [outside app] in *. clear - Hx. tauto. }
    assert (SUB2 : sub_fp ([(lo, bv_unsigned sp + -2128); (U + -16, U + -12); (U, U + 8); (TH + 2800, TH + 3168)] ++
                           [(7915480, 12109800 + 8); (7849928, 7849928 + 28); (d_nb d, d_nb d + 16 * 65536); (d_sb d, d_sb d + 8 * 131072)])
                          (free_head_W lo (bv_unsigned sp) TH U size d)).
    { unfold free_head_W, depot_W, AIAINIT, AIAINST, sub_fp. intros x Hx. cbn [outside app] in *.
      destruct Hx as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & _). clear - X1 X5 X6 X7 X9 X10 X11 X12.
      repeat split; try assumption. clear - X1. lia. }
    assert (SUB3 : sub_fp [(lo, bv_unsigned sp + -2128); (sh U, sh U + nsh size)] (free_head_W lo (bv_unsigned sp) TH U size d)).
    { unfold free_head_W, depot_W, AIAINIT, AIAINST, sub_fp. intros x Hx. cbn [outside app] in *.
      destruct Hx as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & _). clear - X1 X8. repeat split; try assumption. clear - X1. lia. }
    split. { eapply munch_trans; [eapply munch_weaken; [exact SUB1| exact MU1]|].
             eapply munch_trans; [eapply munch_weaken; [exact SUB2| exact MU2]| eapply munch_weaken; [exact SUB3| exact MU3]]. }
    split. { eapply wmono_trans; [exact WM1|]. eapply wmono_trans; [exact WM2| exact WM3]. }
    split; [exact MI3|]. split; [exact ENV3|]. split; [exact ST3|]. split; [exact PFR3|].
    (* [comment removed for export] *)
    Ltac tr23 H MU2 WM2 MU3 WM3 tac :=
      eapply rw_cells_transport in H; [| exact MU2| exact WM2| cbn [disjoint_from cells_size csize length Nat.add Nat.mul app]; tac];
      eapply rw_cells_transport in H; [| exact MU3| exact WM3| cbn [disjoint_from cells_size csize length Nat.add Nat.mul app]; tac].
    tr23 ESO1 MU2 WM2 MU3 WM3 ltac:(match goal with TB : akobj TH 4096 |- _ => clear - BND SHR SPR HI DLO SZ TB end; try acb; aunf; lia).
    split; [exact ESO1|].
    split. { eapply u64arr_transport; [eapply u64arr_transport; [exact TRB1| exact MU2| exact WM2|]| exact MU3| exact WM3|].
             all: cbn [disjoint_from app]; rewrite length_app, length_map, LR1; clear - BND SHR SPR HI NR DLO SZ; try acb; lia. }
    split; [exact LR1|].
    tr23 TFB1 MU2 WM2 MU3 WM3 ltac:(match goal with TB : akobj TH 4096 |- _ => clear - BND SHR SPR HI DLO SZ TB end; try acb; aunf; lia). split; [exact TFB1|].
    tr23 F41 MU2 WM2 MU3 WM3 ltac:(match goal with TB : akobj TH 4096 |- _ => clear - BND SHR SPR HI DLO SZ TB end; try acb; aunf; lia). split; [exact F41|].
    split; [exact TRNG|]. split; [exact NR|].
    eapply rw_cells_transport in HDR2; [| exact MU3| exact WM3| cbn [disjoint_from cells_size csize length Nat.add Nat.mul app]; region_decide].
    split; [exact HDR2|].
    eapply rw_cells_transport in UW2; [| exact MU3| exact WM3| cbn [disjoint_from cells_size csize length Nat.add Nat.mul app]; region_decide].
    split; [exact UW2|].
    split. { eapply stk_transport_disjoint; [exact TST2| exact MU3| exact WM3| cbn [disjoint_from app]; region_decide]. }
    tr23 UNW1 MU2 WM2 MU3 WM3 ltac:(match goal with TB : akobj TH 4096 |- _ => clear - BND SHR PLUb PLDb DLO HI TB end; try acb; aunf; lia). split; [exact UNW1|].
    unfold AIAINIT in FLG1. tr23 FLG1 MU2 WM2 MU3 WM3 ltac:(match goal with TB : akobj TH 4096 |- _ => clear - BND SHR DLO HI TB end; try acb; aunf; lia). split; [exact FLG1|].
    split. { pose proof (ia_if_transport true _ m1 m2 IA1 MU2 WM2 ltac:(hci; cbn [disjoint_from app]; region_decide)) as IA2.
             exact (ia_if_transport true _ m2 m3 IA2 MU3 WM3 ltac:(hci; cbn [disjoint_from app]; clear - BND SHR; try acb; lia)). }
    split. { eapply (DEPOT_transport asegs _ _ m3) in DEP2; [exact DEP2| exact MU3 | exact WM3 |].
             unfold depot_avoid, avoids. rewrite ?d_nb_put, ?d_sb_put. cbn [fst snd].
             repeat split; repeat (first [apply Forall_nil | apply Forall_cons; [cbn [fst snd]; first [clear - BND SHR DLO; try acb; lia | region_decide] |]]). }   (* [comment removed for export] *)
    exact SHD3.
  Qed.
End Head.
