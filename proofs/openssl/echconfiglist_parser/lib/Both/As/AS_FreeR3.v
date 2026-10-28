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
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AW_MallocBase AW_FreeLeaves AW_IAInit AW_FreePre AW_DeallocR AW_PutR1
     AW_EnqueueR1 AW_EnqueueR2 AW_PutR2 AW_ReallocRet AS_Free1 AS_Free2 AS_FreeR1 AllocTacX.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

(* [comment removed for export] *)
Definition free_head_refillR_post (sp gp tp cs0 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo U size b1 actx qcache TSD CTX TH sb TOP BOT k hdq LA qbytes : Z) (T : list Z) (d : depot) (RF : mem -> Prop) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) (jke : list byte) m',
    ms' = MS (mkR (wz 0x19b5cc) (Z_to_bv 64 (bv_unsigned sp + -2352)) gp tp t0 t1 t2 (wz (TH + 2128)) (wz (TH + OT_CACHE))
                  (wz (TH + OT_CACHE)) (wz (TH + 2128)) (wz AINST) (wz kBatchClass) (wz size) (wz AINST) a6 a7
                  (wz (U + -16)) (wz (TH + OT_TQ)) (Z_to_bv 64 (bv_unsigned sp + -2136)) (wz size) (wz qcache) s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x19bdac) fc None m' (seg_rom asegs)
    /\ munch (free_head_W lo (bv_unsigned sp) TH U size d) m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ IENV tp TSD CTX TH sb TOP BOT m'
    /\ stk asegs m' lo (bv_unsigned sp + -2352)
    /\ rw_cells asegs m' (bv_unsigned sp + -2352)
         [CB 8 jke; C8 (wz (U + -16)); C8 (wz (TH + OT_CACHE)); C8 (Z_to_bv 64 (bv_unsigned sp + -2136)); C8 (wz size);
          C8 (wz (TH + OT_TQ)); C8 (wz (AINST + OI_Q)); C8 (wz 0x19b46c)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2288) (put_frameR sp cs0 cs2 cs3 cs4 cs5 s6 U TH)
    /\ RF m'
    /\ rw_cells asegs m' (U + -16) [C1 (b8 3); C1 (b8 b1); C2 (wz 0); C4 (wz size); C8 (wz actx)]
    /\ rw_cells asegs m' U [C8 (wz (d_putid d (depot_hash T)))]
    /\ stk asegs m' (TH + 2800) (TH + 3168)
    /\ DEPOT asegs (d_put d (depot_hash T) (Z.of_nat (length T))) m'
    /\ u8arr asegs m' (sh U) (repeat (b8 kAsanHeapFreeMagic) (Z.to_nat (nsh size)))
    /\ rw_cells asegs m' (TH + OT_TQ) [C8 (wz k); C8 (wz hdq); C8 (wz LA); C8 (wz qbytes)]
    /\ rw_cells asegs m' (TH + 2128) [C4 (wz 0)]
    /\ (k <> 0 -> rw_cells asegs m' LA [C8 (wz 0)] /\ rw_cells asegs m' (LA + 16) [C8 (wz kBatchCount)]).
End HCW.

Section HeadRefillR.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.
  Variables (sp gp tp x3 x4 x5 x12 x13 x14 x15 x16 x17 cs0 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo : Z) (d : depot).
  Variables (TSD CTX TH TOP BOT : Z) (sb : Z).
  Variables (U size b1 actx : Z) (ub : list byte) (qmax qmin qcache : Z) (sbs : list byte).
  Variables (k hdq LA qbytes : Z).
  Variables (T : list Z) (rest : list word) (RF : mem -> Prop).
  Let Wh := free_head_W lo (bv_unsigned sp) TH U size d.

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
  Hypothesis UR : hidden (aapp U (round_up size 8) /\ AIMG_TOP + 16 <= U /\ U + round_up size 8 <= aceil /\ U mod 16 = 0).   (* [comment removed for export] *)
  Hypothesis SZ : 1 <= size < 2^32.
  Hypothesis B1 : 0 <= b1 < 256 /\ (b1 mod 128 = 17 \/ b1 mod 128 = 65).
  Hypothesis ACR : 0 <= actx < 2^64.
  Hypothesis QR : 0 < qcache < 2^64 /\ size <= qmax < 2^64 /\ 0 <= qmin < 2^64.
  Hypothesis SBS : Z.of_nat (length sbs) = nsh size.
  Hypothesis KR : 0 <= k /\ k + 1 < 2^64. Hypothesis HDQ : 0 <= hdq < 2^64. Hypothesis QB0 : 0 <= qbytes.
  Hypothesis SBR : hidden (AHI_LO <= sb /\ sb + kSpaceSize + kPageSize <= aceil /\ sb mod 65536 = 0).
  Hypothesis NR : (1 <= length T <= 30)%nat. Hypothesis TRNG : Forall (fun x => 0 <= x < 2^64) T.
  Hypothesis LR : length rest = (255 - length T)%nat.
  Hypothesis RFT : forall W m0 m1, RF m0 -> munch W m0 m1 -> wmono asegs m0 m1 -> disjoint_from W (bv_unsigned sp + -2208) 2208 ->
                   disjoint_from W (TH + 3168) 1 -> disjoint_from W AIAINIT 4 -> disjoint_from W AIAINST 0x81030 -> RF m1.
  Hypothesis RFE : forall m0, RF m0 ->
       rw_cells asegs m0 (bv_unsigned sp + -2136) [C8 (wz (bv_unsigned sp + -2136 + 16)); C8 (wz (Z.of_nat (length T)))]
    /\ u64arr asegs m0 (bv_unsigned sp + -2136 + 16) (map wz T ++ rest).
  Hypothesis ENV : IENV tp TSD CTX TH sb TOP BOT m.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp + -2208).
  Hypothesis RF0 : RF m.
  Hypothesis DEP : DEPOT asegs d m.
  Hypothesis HDR : rw_cells asegs m (U + -16) [C1 (b8 2); C1 (b8 b1); C2 (wz 0); C4 (wz size); C8 (wz actx)].
  Hypothesis UB : rw_cells asegs m U [CB 8 ub].
  Hypothesis TST : stk asegs m (TH + 2800) (TH + 3168).
  Hypothesis QC : rw_cells asegs m (AINST + OI_QMAX) [C8 (wz qmax); C8 (wz qmin); C8 (wz qcache)].
  Hypothesis SH : u8arr asegs m (sh U) sbs.
  Hypothesis TQ : rw_cells asegs m (TH + OT_TQ) [C8 (wz k); C8 (wz hdq); C8 (wz LA); C8 (wz qbytes)].
  (* [comment removed for export] *)
  Hypothesis PC1 : rw_cells asegs m (TH + 2128) [C4 (wz 0)].
  Hypothesis LAh : k <> 0 -> (rw_cells asegs m LA [C8 (wz 0)] /\ rw_cells asegs m (LA + 16) [C8 (wz kBatchCount)])
                   /\ AHI_LO <= LA /\ LA + kBatchSize <= aceil /\ (TH + 4096 <= LA \/ LA + kBatchSize <= TH)
                   /\ (LA + kBatchSize <= U - 16 \/ U + 8 <= LA)
                   /\ (d_nb d + 16 * 65536 <= LA \/ LA + kBatchSize <= d_nb d) /\ (d_sb d + 8 * 131072 <= LA \/ LA + kBatchSize <= d_sb d).

  Theorem free_head_refillR :
    evt asegs (free_head_refillR_post sp gp tp cs0 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 F fc m lo U size b1 actx qcache TSD CTX TH sb TOP BOT k hdq LA qbytes T d RF)
      (MS (mkR (wz 0x197a10) (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp x3 x4 x5 cs0 (wz U) (wz AINST) (wz U) (wz 0) (wz 0)
               (Z_to_bv 64 (bv_unsigned sp + -2136)) (wz 1) x12 x13 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 x14 x15 x16 x17)
          F (Z_to_bv 64 0x196ae8) fc None m (seg_rom asegs)).
  Proof.
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR.
    assert (BND : aceil <= lo /\ 12599296 <= CTX /\ CTX + 160 <= aceil /\ 4096 <= TH /\ TH + 4096 <= aceil
               /\ bv_unsigned sp + 16 <= 140737488355328 /\ 12599312 <= U /\ U + round_up size 8 <= aceil /\ 140735193776128 <= aceil /\ size <= round_up size 8 /\ 8 <= round_up size 8
               /\ 12599296 <= d_nb d /\ 12599296 <= d_sb d)
      by (clear - LO RNG SPT UR PLCD SZ; try acb; destruct RNG as [RNG']; destruct UR as [UR']; destruct PLCD as [PLCD']; destruct SPT as [SPT'];
          unfold AHI_LO, round_up in *; acb; change (2^47)%Z with 140737488355328%Z in SPT'; aunf; repeat split; try lia; Z.div_mod_to_equations; lia).
    region_sides. name_bands.
    assert (PLUb : (TH + 4096 <= U - 16 \/ U + 8 <= TH)) by (destruct PLU as [X]; clear - X; tauto).
    assert (PLDb : (TH + 4096 <= d_nb d \/ d_nb d + 16 * 65536 <= TH) /\ (TH + 4096 <= d_sb d \/ d_sb d + 8 * 131072 <= TH)) by (destruct PLCD as [X]; clear - X; tauto).
    assert (SHR : 2148314624 <= sh U /\ sh U + nsh size <= 17594333495296) by (unfold sh, nsh, ASHADOW_BASE; clear - BND SZ; try acb; Z.div_mod_to_equations; lia).
    assert (USH : sh U + nsh size <= U - 16 \/ U + round_up size 8 <= sh U) by (destruct UR as [[UA UX]]; clear - UA UX; acb; unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, ALOWSH_LO, AHI_LO, sh, nsh, round_up, ASHADOW_BASE in *; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
    assert (THR : hidden (akobj TH 4096 /\ TH + 4096 <= aceil /\ TH mod 16 = 0)) by (destruct RNG as [X]; constructor; clear - X; tauto).
    assert (UR8 : hidden (aapp U 8 /\ AIMG_TOP + 16 <= U /\ U + 8 <= aceil)) by (destruct UR as [X]; constructor; destruct X as [XA X]; split; [apply (aapp_sub _ _ _ _ XA); clear - BND; lia| clear - X BND; lia]).
    eapply evt_cut;
    [ eapply (@free_headR _ sp gp tp x3 x4 x5 x12 x13 x14 x15 x16 x17 cs0 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 F fc m lo d TSD CTX TH TOP BOT sb
                U size b1 actx ub qmax qmin qcache sbs T rest RF); eassumption
    | cbv beta; intros ms3 PO3;
      destruct PO3 as (t0_3 & t1_3 & t2_3 & a5_3 & a6_3 & a7_3 & t3_3 & t4_3 & t5_3 & t6_3 & m3 & -> & MU3 & WM3 & MI3 & ENV3 & ST3 & PFR3
                       & RF3 & HDR3 & UW3 & TST3 & DEP3 & SHD3) ].
    pose proof MU3 as MU3'. unfold free_head_W, depot_W, AIAINIT, AIAINST in MU3'.
    unfold OT_TQ, kBatchSize, kBatchCount in *.
    Ltac tr3 H MU WM tac := eapply rw_cells_transport in H; [| exact MU| exact WM| cbn [disjoint_from cells_size csize length Nat.add Nat.mul app]; tac].
    tr3 TQ MU3' WM3 ltac:(match goal with TB : akobj TH 4096 |- _ => clear - BND PLUb PLDb SHR DLO HI SZ TB end; try acb; aunf; lia).
    tr3 PC1 MU3' WM3 ltac:(match goal with TB : akobj TH 4096 |- _ => clear - BND PLUb PLDb SHR DLO HI SZ TB end; try acb; aunf; lia).
    assert (LAh3 : k <> 0 -> (rw_cells asegs m3 LA [C8 (wz 0)] /\ rw_cells asegs m3 (LA + 16) [C8 (wz 1021)])
                   /\ AHI_LO <= LA /\ LA + 8192 <= aceil /\ (TH + 4096 <= LA \/ LA + 8192 <= TH)).
    { intros NZ. destruct (LAh NZ) as ([LC LCC] & LA1 & LA2 & LA3 & LA5 & LA6 & LA7).
      assert (LAD : disjoint_from Wh LA 8192).
      { unfold Wh, free_head_W, depot_W, AIAINIT, AIAINST. cbn [disjoint_from app]. unfold AHI_LO in LA1. clear - LA1 LA2 LA3 LA5 LA6 LA7 BND SHR DLO HI. lia. }
      split; [| clear - LA1 LA2 LA3; repeat split; assumption]. split.
      - eapply rw_cells_transport; [exact LC| exact MU3| exact WM3| eapply disjoint_from_sub; [exact LAD| clear; lia| cbn; clear; lia]].
      - eapply rw_cells_transport; [exact LCC| exact MU3| exact WM3| eapply disjoint_from_sub; [exact LAD| clear; lia| cbn; clear; lia]]. }
    eapply evt_cut.
    { eapply (@enq_refillR_pre _ sp gp tp t0_3 t1_3 t2_3 a5_3 a6_3 a7_3 t3_3 t4_3 t5_3 t6_3 s7 s8 s9 s10 s11 F fc m3 lo U size TH qcache sb k hdq LA qbytes).
      all: try eassumption. }
    cbv beta. intros ms4 (jke & PO4).
    destruct PO4 as (t0_4 & t1_4 & t2_4 & a6_4 & a7_4 & t3_4 & t4_4 & t5_4 & t6_4 & m4 & -> & MU4 & WM4 & MI4 & ST4 & FR4).
    apply evt_done. unfold free_head_refillR_post.
    exists t0_4, t1_4, t2_4, a6_4, a7_4, t3_4, t4_4, t5_4, t6_4, jke, m4.
    split; [reflexivity|].
    assert (SUB4 : sub_fp [(lo, bv_unsigned sp + -2288)] Wh).
    { unfold Wh, free_head_W, sub_fp. intros x Hx. cbn [outside app] in *. destruct Hx as (X1 & _). split; [clear - X1; lia| exact I]. }
    split; [exact (munch_trans _ _ _ _ MU3 (munch_weaken _ _ _ _ SUB4 MU4))|]. split; [exact (wmono_trans _ _ _ _ WM3 WM4)|]. split; [exact MI4|].
    split. { eapply (@ienv_now_pR _ sp tp m3 lo U size sbs TSD CTX TH TOP BOT sb); try eassumption.
             eapply munch_weaken; [| exact MU4]. intros x Hx. cbn [outside] in *. destruct Hx as (X1 & _). split; [clear - X1; lia| exact I]. }
    split; [exact ST4|]. split; [exact FR4|].
    Ltac tr4 H MU WM tac := eapply rw_cells_transport in H; [| exact MU| exact WM| cbn [disjoint_from cells_size csize length Nat.add Nat.mul app]; tac].
    unfold put_frameR in PFR3 |- *. tr4 PFR3 MU4 WM4 ltac:(clear - SPR; lia). split; [exact PFR3|].
    split. { eapply (RFT _ _ _ RF3 MU4 WM4); unfold AIAINIT, AIAINST; cbn [disjoint_from app]; match goal with TB : akobj TH 4096 |- _ => clear - BND SPR HI TB end; try acb; aunf; lia. }
    tr4 HDR3 MU4 WM4 ltac:(clear - SPR BND HI SZ; try acb; lia). split; [exact HDR3|].
    tr4 UW3 MU4 WM4 ltac:(clear - SPR BND HI SZ; try acb; lia). split; [exact UW3|].
    split. { eapply stk_transport_disjoint; [exact TST3| exact MU4| exact WM4| cbn [disjoint_from app]; region_decide]. }
    split. { eapply (DEPOT_transport asegs _ _ m4) in DEP3; [exact DEP3| exact MU4 | exact WM4 |].
             unfold depot_avoid, avoids. rewrite ?d_nb_put, ?d_sb_put. cbn [fst snd].
             repeat split; repeat (first [apply Forall_nil | apply Forall_cons; [cbn [fst snd]; first [clear - BND HI DLO; try acb; lia | region_decide] |]]). }
    split. { eapply u8arr_transport; [exact SHD3| exact MU4| exact WM4| cbn [disjoint_from app]]. rewrite repeat_length, Z2Nat.id by (clear - SZ; unfold nsh; Z.div_mod_to_equations; lia).
             clear - BND SHR HI; try acb; lia. }
    tr4 TQ MU4 WM4 ltac:(clear - SPR BND HI; try acb; lia). split; [exact TQ|].
    tr4 PC1 MU4 WM4 ltac:(clear - SPR BND HI; try acb; lia). split; [exact PC1|].
    intros NZ. destruct (LAh3 NZ) as ([LC LCC] & LA1 & LA2 & LA3). unfold AHI_LO in LA1.
    tr4 LC MU4 WM4 ltac:(clear - SPR BND HI LA1 LA2; try acb; lia). tr4 LCC MU4 WM4 ltac:(clear - SPR BND HI LA1 LA2; try acb; lia).
    exact (conj LC LCC).
  Qed.
End HeadRefillR.

(* [comment removed for export] *)
Section TailRefillR.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.
  Variables (sp cs0 cs2 cs3 cs4 cs5 gp tp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (t0 t1 t2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 t3 t4 t5 t6 xra : word) (m : mem).
  Variables (lo : Z) (jke : list byte) (RF : mem -> Prop).
  Variables (U size TH qcache sb : Z) (k hdq LA qbytes : Z) (cnt : Z) (chunks : list Z) (B : Z) (j0 j1 j2 j3 : word).
  Let Wn := enq_newR_W lo (bv_unsigned sp) TH B LA.

  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 3024 <= bv_unsigned sp.
  Hypothesis SPT : hidden (bv_unsigned sp + 16 <= 2^47).
  Hypothesis UR : hidden (aapp U 8 /\ AIMG_TOP + 16 <= U /\ U + 8 <= aceil).   (* [comment removed for export] *)
  Hypothesis SZ : 1 <= size < 2^32.
  Hypothesis THR : hidden (akobj TH 4096 /\ TH + 4096 <= aceil /\ TH mod 16 = 0).
  Hypothesis SBR : hidden (AHI_LO <= sb /\ sb + kSpaceSize + kPageSize <= aceil /\ sb mod 65536 = 0).
  Hypothesis CNT : cnt = zlen chunks. Hypothesis HIT : 1 <= cnt <= 2.
  Hypothesis CPS : Forall (fun cp => 0 <= cp < 2^32) chunks.
  Hypothesis HB : B = sb + kBatchClass * 2^32 + hd 0 chunks * 16.
  Hypothesis BR : hidden (AHI_LO <= B /\ B + kBatchSize <= aceil /\ (TH + 4096 <= B \/ B + kBatchSize <= TH)).
  Hypothesis BU : B + kBatchSize <= U - 16 \/ U + 8 <= B.
  Hypothesis KR : 0 <= k /\ k + 1 < 2^64. Hypothesis QB : 0 <= qbytes /\ qbytes + size + kBatchSize <= qcache.
  Hypothesis HDQ : 0 <= hdq < 2^64. Hypothesis QCR : 0 <= qcache < 2^64.
  Hypothesis LAh : k <> 0 -> rw_cells asegs m LA [C8 (wz 0)]
                   /\ AHI_LO <= LA /\ LA + kBatchSize <= aceil /\ (TH + 4096 <= LA \/ LA + kBatchSize <= TH) /\ (B + kBatchSize <= LA \/ LA + kBatchSize <= B)
                   /\ (LA + kBatchSize <= U - 16 \/ U + 8 <= LA).
  Hypothesis LA0 : k = 0 -> LA = 0.
  Hypothesis RFT : forall W m0 m1, RF m0 -> munch W m0 m1 -> wmono asegs m0 m1 -> disjoint_from W (bv_unsigned sp + -2208) 2208 ->
                   disjoint_from W (TH + 3168) 1 -> disjoint_from W AIAINIT 4 -> disjoint_from W AIAINST 0x81030 -> RF m1.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp + -2352).
  Hypothesis FR : rw_cells asegs m (bv_unsigned sp + -2352)
      [CB 8 jke; C8 (wz (U + -16)); C8 (wz (TH + OT_CACHE)); C8 (Z_to_bv 64 (bv_unsigned sp + -2136)); C8 (wz size);
       C8 (wz (TH + OT_TQ)); C8 (wz (AINST + OI_Q)); C8 (wz 0x19b46c)].
  Hypothesis TQ : rw_cells asegs m (TH + OT_TQ) [C8 (wz k); C8 (wz hdq); C8 (wz LA); C8 (wz qbytes)].
  Hypothesis PC1 : rw_cells asegs m (TH + 2128) [C4 (wz cnt)].
  Hypothesis PC2 : rw_cells asegs m (TH + 2136) [C8 (wz kBatchSize)].
  Hypothesis PC3 : u32arr asegs m (TH + 2144) (wlist (rev chunks)).
  Hypothesis PC4 : stk asegs m (TH + 2144 + 4 * cnt) (TH + 2208).
  Hypothesis STATS : rw_cells asegs m (TH + 2768) [C8 j0; C8 j1; C8 j2; C8 j3].
  Hypothesis INST : rw_cells asegs m (AINST + OI_SPACEBEG) [C8 (wz sb)].
  Hypothesis BJ : stk asegs m B (B + kBatchSize).
  Hypothesis PFR : rw_cells asegs m (bv_unsigned sp + -2288) (put_frameR sp cs0 cs2 cs3 cs4 cs5 s6 U TH).
  Hypothesis RF0 : RF m.

  Definition free_tail_refillR_post : machine_state -> Prop := fun ms' =>
    exists (j2' : word) m', put_retR_post sp cs0 cs2 cs3 cs4 cs5 gp tp s6 s7 s8 s9 s10 s11 F fc lo U m' ms'
    /\ munch Wn m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ RF m'
    /\ rw_cells asegs m' (TH + OT_TQ) [C8 (wz (k + 1)); C8 (wz (if k =? 0 then B else hdq)); C8 (wz B); C8 (wz (qbytes + (size + kBatchSize)))]
    /\ (k <> 0 -> rw_cells asegs m' LA [C8 (wz B)])
    /\ rw_cells asegs m' B [C8 (wz 0); C8 (wz (size + kBatchSize)); C8 (wz 1); C8 (wz (U + -16))]
    /\ stk asegs m' (B + 32) (B + kBatchSize)
    /\ rw_cells asegs m' (TH + 2128) [C4 (wz (cnt - 1))]
    /\ u32arr asegs m' (TH + 2144) (wlist (rev (tl chunks)))
    /\ stk asegs m' (TH + 2144 + 4 * (cnt - 1)) (TH + 2208)
    /\ rw_cells asegs m' (TH + 2768) [C8 j0; C8 j1; C8 j2'; C8 j3].

  Theorem free_tail_refillR :
    evt asegs free_tail_refillR_post
      (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2352)) gp tp t0 t1 t2 (wz (TH + 2128)) (wz (TH + OT_CACHE))
               (wz 1) xa1 xa2 xa3 xa4 xa5 xa6 xa7
               (wz (U + -16)) (wz (TH + OT_TQ)) (Z_to_bv 64 (bv_unsigned sp + -2136)) (wz size) (wz qcache) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19b5cc) fc None m (seg_rom asegs)).
  Proof.
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR.
    assert (BND : aceil <= lo /\ 4096 <= TH /\ TH + 4096 <= aceil /\ bv_unsigned sp + 16 <= 140737488355328
               /\ 12599312 <= U /\ U + 8 <= aceil /\ 140735193776128 <= aceil /\ 17594333495296 <= B /\ B + 8192 <= aceil /\ (TH + 4096 <= B \/ B + 8192 <= TH))
      by (clear - LO THR SPT UR BR; try acb; destruct THR as [THR']; destruct UR as [UR']; destruct BR as [BR']; destruct SPT as [SPT'];
          unfold AHI_LO, kBatchSize in *; acb; change (2^47)%Z with 140737488355328%Z in SPT'; aunf; repeat split; lia).
    region_sides. name_bands.
    eapply evt_cut.
    { eapply (@enq_refillR_post _ sp gp tp t0 t1 t2 xa6 xa7 t3 t4 t5 t6 xra s7 s8 s9 s10 s11 F fc m m lo U size TH qcache sb k hdq LA qbytes cnt chunks B jke j0 j1 j2 j3).
      all: try eassumption. all: try apply munch_refl. all: try apply wmono_refl.
      intros NZ; destruct (LAh NZ) as (A1 & A2 & A3 & A4 & A5 & A6). split; [exact A1| split; [exact A2| split; [exact A3| split; [exact A4| exact A5]]]]. }
    cbv beta. intros ms4 PO4.
    destruct PO4 as (t0_4 & t1_4 & t2_4 & a1_4 & a2_4 & a3_4 & a4_4 & a5_4 & a6_4 & a7_4 & t3_4 & t4_4 & t5_4 & t6_4 & j2' & m4 & -> & MU4 & WM4 & MI4 & ST4
                     & TQ4 & LA4 & BC4 & BJ4 & PC14 & PC34 & PC44 & STATS4).
    unfold enq_newR_W, kBatchSize, OT_TQ in MU4, BJ4, TQ4, BC4 |- *.
    Ltac tr4 H MU WM tac := eapply rw_cells_transport in H; [| exact MU| exact WM| cbn [disjoint_from cells_size csize length Nat.add Nat.mul app]; tac].
    assert (LAX : LA = 0 \/ (17594333495296 <= LA /\ LA + 8192 <= aceil /\ (TH + 4096 <= LA \/ LA + 8192 <= TH) /\ (B + 8192 <= LA \/ LA + 8192 <= B)
                             /\ (LA + 8192 <= U - 16 \/ U + 8 <= LA))).
    { destruct (Z.eq_dec k 0) as [KZ|KNZ]; [left; exact (LA0 KZ)| right].
      destruct (LAh KNZ) as (_ & Y1 & Y2 & Y3 & Y4 & Y5). unfold AHI_LO in Y1. clear - Y1 Y2 Y3 Y4 Y5. split; [exact Y1| split; [exact Y2| split; [exact Y3| split; [exact Y4| exact Y5]]]]. }
    Ltac slv LAX := destruct LAX as [LAZ|LAF]; [rewrite ?LAZ in *; clear LAZ | ]; try acb; lia.
    unfold put_frameR in PFR. tr4 PFR MU4 WM4 ltac:(clear - BND SPR HI LAX; slv LAX).
    assert (RF4 : RF m4) by (eapply (RFT _ _ _ RF0 MU4 WM4); unfold AIAINIT, AIAINST; cbn [disjoint_from app]; match goal with TB : akobj TH 4096 |- _ => clear - BND SPR HI LAX TB end;
                              (destruct LAX as [LAZ|LAF]; [rewrite ?LAZ in *; clear LAZ | ]); try acb; aunf; lia).
    eapply evt_cut.
    { eapply (@put_tailR _ sp cs0 cs2 cs3 cs4 cs5 gp tp s6 s7 s8 s9 s10 s11 F fc lo); try eassumption.
      - clear - HI; try acb; lia.
      - destruct THR as [XT]; constructor; clear - XT; tauto.
      - unfold kBatchSize in QB; clear - QB SZ; lia. }
    cbv beta. intros ms5 PO5.
    apply evt_done. exists j2', m4. split; [exact PO5|].
    split; [exact MU4|]. split; [exact WM4|]. split; [exact MI4|]. split; [exact RF4|].
    split; [exact TQ4|]. split; [exact LA4|]. split; [exact BC4|]. split; [exact BJ4|]. split; [exact PC14|]. split; [exact PC34|]. split; [exact PC44| exact STATS4].
  Qed.
End TailRefillR.
