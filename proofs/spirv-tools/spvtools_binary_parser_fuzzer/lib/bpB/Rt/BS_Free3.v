(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BW_0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocRep BsAtomics B_memset BsDepotInv BsDepotHash BsDepotPut BsUnwind BidBits BW_Combined BW_PoisonShadow BW_Leaves BW_DepotFrame BW_AllocBase BllocWalkKit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BW_MallocBase BW_FreeLeaves BW_IAInit BW_FreePre BW_Dealloc BW_Put1 BW_Enqueue1 BW_Enqueue2 BW_Put2 BS_Free1 BS_Free2 BllocTacX.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

Definition free_head_refill_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo U size b1 actx qcache TSD CTX TH sb TOP BOT k hdq LA qbytes : Z) (T : list Z) (d : depot) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) (jk jke : list byte) (rest : list word) m',
    ms' = MS (mkR (wz 0x96b64) (Z_to_bv 64 (bv_unsigned sp + -2272)) gp tp t0 t1 t2 (wz (TH + 2128)) (wz (TH + OT_CACHE))
                  (wz (TH + OT_CACHE)) (wz (TH + 2128)) (wz AINST) (wz kBatchClass) (wz size) (wz AINST) a6 a7
                  (wz (U + -16)) (wz (TH + OT_TQ)) (Z_to_bv 64 (bv_unsigned sp + -2128)) (wz size) (wz qcache) s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x97344) fc None m' (seg_rom asegs)
    /\ munch (free_head_W lo (bv_unsigned sp) TH U size d) m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ IENV tp TSD CTX TH sb TOP BOT m'
    /\ stk asegs m' lo (bv_unsigned sp + -2272)
    /\ rw_cells asegs m' (bv_unsigned sp + -2272)
         [CB 8 jke; C8 (wz (U + -16)); C8 (wz (TH + OT_CACHE)); C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 (wz size);
          C8 (wz (TH + OT_TQ)); C8 (wz (AINST + OI_Q)); C8 (wz 0x96a04)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2208) (put_frame sp s6 U TH)
    /\ rw_cells asegs m' (bv_unsigned sp + -2128) [C8 (wz (bv_unsigned sp + -2128 + 16)); C8 (wz (Z.of_nat (length T)))]
    /\ u64arr asegs m' (bv_unsigned sp + -2128 + 16) (map wz T ++ rest) /\ length rest = (255 - length T)%nat
    /\ rw_cells asegs m' (bv_unsigned sp + -72) [C8 sp]
    /\ rw_cells asegs m' (bv_unsigned sp + -64) [CB 8 jk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ Forall (fun x => 0 <= x < 2^64) T /\ (1 <= length T <= 30)%nat
    /\ rw_cells asegs m' (U + -16) [C1 (b8 3); C1 (b8 b1); C2 (wz 0); C4 (wz size); C8 (wz actx)]
    /\ rw_cells asegs m' U [C8 (wz (d_putid d (depot_hash T)))]
    /\ stk asegs m' (TH + 2800) (TH + 3168)
    /\ rw_cells asegs m' (TH + 3168) [C1 (b8 0)]
    /\ rw_cells asegs m' AIAINIT [C1 (b8 1); C1 (b8 0); C2 (wz 0)] /\ ia_after m'
    /\ DEPOT asegs (d_put d (depot_hash T) (Z.of_nat (length T))) m'
    /\ u8arr asegs m' (sh U) (repeat (b8 kAsanHeapFreeMagic) (Z.to_nat (nsh size)))
    /\ rw_cells asegs m' (TH + OT_TQ) [C8 (wz k); C8 (wz hdq); C8 (wz LA); C8 (wz qbytes)]
    /\ rw_cells asegs m' (TH + 2128) [C4 (wz 0)]
    /\ (k <> 0 -> rw_cells asegs m' LA [C8 (wz 0)] /\ rw_cells asegs m' (LA + 16) [C8 (wz kBatchCount)]).

Section HeadRefill.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo : Z) (d : depot) (inited : bool).
  Variables (TSD CTX TH TOP BOT : Z) (CH : list (Z * Z)) (sb : Z).
  Variables (U size b1 actx : Z) (ub : list byte) (qmax qmin qcache : Z) (sbs : list byte).
  Variables (k hdq LA qbytes : Z).
  Let CHI := icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) TOP CH.
  Let T := utrace 0xba24c (bv_unsigned sp) TOP BOT 30 CHI.
  Let Wh := free_head_W lo (bv_unsigned sp) TH U size d.

  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 2912 <= bv_unsigned sp.
  Hypothesis SPA : hidden (bv_unsigned sp mod 16 = 0).
  Hypothesis SPT : hidden (bv_unsigned sp + 16 <= 2^47).
  Hypothesis TPR : hidden (6762376 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP).
  Hypothesis RNG : hidden (6762288 <= TSD /\ TSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj TH 4096 /\ TH + 4096 <= aceil /\ TH mod 16 = 0).
  Hypothesis PLC : hidden ((TH + 4096 <= sb \/ sb + kSpaceSize + 4096 <= TH) /\ (CTX + 160 <= sb \/ sb + kSpaceSize + 4096 <= CTX)
                /\ (CTX + 160 <= TH \/ TH + 4096 <= CTX)).
  Hypothesis PLCD : hidden ((TH + 4096 <= d_nb d \/ d_nb d + 16 * 65536 <= TH) /\ (TH + 4096 <= d_sb d \/ d_sb d + 8 * 32768 <= TH)
                /\ (sb + kSpaceSize + 4096 <= d_nb d \/ d_nb d + 16 * 65536 <= sb) /\ (sb + kSpaceSize + 4096 <= d_sb d \/ d_sb d + 8 * 32768 <= sb)
                /\ (CTX + 160 <= d_nb d \/ d_nb d + 16 * 65536 <= CTX) /\ (CTX + 160 <= d_sb d \/ d_sb d + 8 * 32768 <= CTX)
                /\ aapp (d_nb d) (16 * 65536) /\ aapp (d_sb d) (8 * 32768)).
  Hypothesis PLU : hidden ((TH + 4096 <= U - 16 \/ U + 8 <= TH) /\ (CTX + 160 <= U - 16 \/ U + 8 <= CTX)
                /\ (d_nb d + 16 * 65536 <= U - 16 \/ U + 8 <= d_nb d) /\ (d_sb d + 8 * 32768 <= U - 16 \/ U + 8 <= d_sb d)).
  Hypothesis TBR : hidden (4096 <= TOP <= 2^47 /\ 0 <= BOT < TOP).
  Hypothesis DLO : d_nb d + 16 * 65536 <= lo /\ d_sb d + 8 * 32768 <= lo.
  Hypothesis DCAP : d_ids d + 1 < 65536 /\ d_frames d + 31 <= 32768.
  Hypothesis FCH : goodframe BOT (bv_unsigned sp) TOP = true -> goodframe (bv_unsigned sp) (bv_unsigned s0) TOP = true ->
                   bv_unsigned sp + 16 <= bv_unsigned s0 /\ frame_chain asegs m TOP (bv_unsigned s0) CH.
  Hypothesis Ha0 : a0 = wz U.
  Hypothesis UR : hidden (aapp U (round_up size 8) /\ AIMG_TOP + 16 <= U /\ U + round_up size 8 <= aceil /\ U mod 16 = 0).
  Hypothesis SZ : 1 <= size < 2^32.
  Hypothesis B1 : 0 <= b1 < 256 /\ b1 mod 128 = 17.
  Hypothesis ACR : 0 <= actx < 2^64.
  Hypothesis QR : 0 < qcache < 2^64 /\ size <= qmax < 2^64 /\ 0 <= qmin < 2^64.
  Hypothesis SBS : Z.of_nat (length sbs) = nsh size.
  Hypothesis KR : 0 <= k /\ k + 1 < 2^64. Hypothesis HDQ : 0 <= hdq < 2^64. Hypothesis QB0 : 0 <= qbytes.
  Hypothesis SBR : hidden (AHI_LO <= sb /\ sb + kSpaceSize + kPageSize <= aceil /\ sb mod 65536 = 0).
  Hypothesis ENV : IENV tp TSD CTX TH sb TOP BOT m.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis UNW : rw_cells asegs m (TH + 3168) [C1 (b8 0)].
  Hypothesis FLG : rw_cells asegs m AIAINIT [C1 (b8 (if inited then 1 else 0)); C1 (b8 0); C2 (wz 0)].
  Hypothesis IA : if inited then ia_after m else ia_pristine m.
  Hypothesis DEP : DEPOT asegs d m.
  Hypothesis HDR : rw_cells asegs m (U + -16) [C1 (b8 2); C1 (b8 b1); C2 (wz 0); C4 (wz size); C8 (wz actx)].
  Hypothesis UB : rw_cells asegs m U [CB 8 ub].
  Hypothesis TST : stk asegs m (TH + 2800) (TH + 3168).
  Hypothesis QC : rw_cells asegs m (AINST + OI_QMAX) [C8 (wz qmax); C8 (wz qmin); C8 (wz qcache)].
  Hypothesis SH : u8arr asegs m (sh U) sbs.
  Hypothesis TQ : rw_cells asegs m (TH + OT_TQ) [C8 (wz k); C8 (wz hdq); C8 (wz LA); C8 (wz qbytes)].

  Hypothesis PC1 : rw_cells asegs m (TH + 2128) [C4 (wz 0)].
  Hypothesis LAh : k <> 0 -> (rw_cells asegs m LA [C8 (wz 0)] /\ rw_cells asegs m (LA + 16) [C8 (wz kBatchCount)])
                   /\ AHI_LO <= LA /\ LA + kBatchSize <= aceil /\ (TH + 4096 <= LA \/ LA + kBatchSize <= TH)
                   /\ (LA + kBatchSize <= U - 16 \/ U + 8 <= LA)
                   /\ (d_nb d + 16 * 65536 <= LA \/ LA + kBatchSize <= d_nb d) /\ (d_sb d + 8 * 32768 <= LA \/ LA + kBatchSize <= d_sb d).

  Theorem free_head_refill :
    evt asegs (free_head_refill_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo U size b1 actx qcache TSD CTX TH sb TOP BOT k hdq LA qbytes T d)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xba114) fc None m (seg_rom asegs)).
  Proof.
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR.
    assert (BND : aceil <= lo /\ 7241728 <= CTX /\ CTX + 160 <= aceil /\ 4096 <= TH /\ TH + 4096 <= aceil
               /\ bv_unsigned sp + 16 <= 140737488355328 /\ 7241744 <= U /\ U + round_up size 8 <= aceil /\ 140735193776128 <= aceil /\ size <= round_up size 8 /\ 8 <= round_up size 8
               /\ 7241728 <= d_nb d /\ 7241728 <= d_sb d)
      by (clear - LO RNG SPT UR PLCD SZ; try acb; destruct RNG as [RNG']; destruct UR as [UR']; destruct PLCD as [PLCD']; destruct SPT as [SPT'];
          unfold AHI_LO, round_up in *; acb; change (2^47)%Z with 140737488355328%Z in SPT'; aunf; repeat split; try lia; Z.div_mod_to_equations; lia).
    region_sides. name_bands.
    assert (PLUb : (TH + 4096 <= U - 16 \/ U + 8 <= TH)) by (destruct PLU as [X]; clear - X; tauto).
    assert (PLDb : (TH + 4096 <= d_nb d \/ d_nb d + 16 * 65536 <= TH) /\ (TH + 4096 <= d_sb d \/ d_sb d + 8 * 32768 <= TH)) by (destruct PLCD as [X]; clear - X; tauto).
    assert (SHR : 2148356096 <= sh U /\ sh U + nsh size <= 17594333495296) by (unfold sh, nsh, ASHADOW_BASE; clear - BND SZ; try acb; Z.div_mod_to_equations; lia).
    assert (USH : sh U + nsh size <= U - 16 \/ U + round_up size 8 <= sh U) by (destruct UR as [[UA UX]]; clear - UA UX; acb; unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, ALOWSH_LO, AHI_LO, sh, nsh, round_up, ASHADOW_BASE in *; Z.div_mod_to_equations; lia).
    assert (THR : hidden (akobj TH 4096 /\ TH + 4096 <= aceil /\ TH mod 16 = 0)) by (destruct RNG as [X]; constructor; clear - X; tauto).
    assert (UR8 : hidden (aapp U 8 /\ AIMG_TOP + 16 <= U /\ U + 8 <= aceil)) by (destruct UR as [X]; constructor; destruct X as [XA X]; split; [apply (aapp_sub _ _ _ _ XA); clear - BND; lia| clear - X BND; lia]).
    eapply evt_cut;
    [ eapply (@free_head _ ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo d inited TSD CTX TH TOP BOT CH sb
                U size b1 actx ub qmax qmin qcache sbs); eassumption
    | cbv beta; intros ms3 PO3;
      destruct PO3 as (t0_3 & t1_3 & t2_3 & a5_3 & a6_3 & a7_3 & t3_3 & t4_3 & t5_3 & t6_3 & jk & rest & m3 & -> & MU3 & WM3 & MI3 & ENV3 & ST3 & PFR3
                       & ESO3 & TRB3 & LR3 & TFB3 & F43 & TRNG & NR & HDR3 & UW3 & TST3 & UNW3 & FLG3 & IA3 & DEP3 & SHD3) ].
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
    { eapply (@enq_refill_pre _ sp gp tp t0_3 t1_3 t2_3 a5_3 a6_3 a7_3 t3_3 t4_3 t5_3 t6_3 s7 s8 s9 s10 s11 F fc m3 lo U size TH qcache sb k hdq LA qbytes).
      all: try eassumption. }
    cbv beta. intros ms4 (jke & PO4).
    destruct PO4 as (t0_4 & t1_4 & t2_4 & a6_4 & a7_4 & t3_4 & t4_4 & t5_4 & t6_4 & m4 & -> & MU4 & WM4 & MI4 & ST4 & FR4).
    apply evt_done. unfold free_head_refill_post.
    exists t0_4, t1_4, t2_4, a6_4, a7_4, t3_4, t4_4, t5_4, t6_4, jk, jke, rest, m4.
    split; [reflexivity|].
    assert (SUB4 : sub_fp [(lo, bv_unsigned sp + -2208)] Wh).
    { unfold Wh, free_head_W, sub_fp. intros x Hx. cbn [outside app] in *. destruct Hx as (X1 & _). split; [clear - X1; lia| exact I]. }
    split; [exact (munch_trans _ _ _ _ MU3 (munch_weaken _ _ _ _ SUB4 MU4))|]. split; [exact (wmono_trans _ _ _ _ WM3 WM4)|]. split; [exact MI4|].
    split. { eapply (@ienv_now_p _ sp tp m3 lo U size sbs TSD CTX TH TOP BOT sb); try eassumption.
             eapply munch_weaken; [| exact MU4]. intros x Hx. cbn [outside] in *. destruct Hx as (X1 & _). split; [clear - X1; lia| exact I]. }
    split; [exact ST4|]. split; [exact FR4|].
    Ltac tr4 H MU WM tac := eapply rw_cells_transport in H; [| exact MU| exact WM| cbn [disjoint_from cells_size csize length Nat.add Nat.mul app]; tac].
    unfold put_frame in PFR3 |- *. tr4 PFR3 MU4 WM4 ltac:(clear - SPR; lia). split; [exact PFR3|].
    tr4 ESO3 MU4 WM4 ltac:(clear - SPR; lia). split; [exact ESO3|].
    split. { eapply u64arr_transport; [exact TRB3| exact MU4| exact WM4| cbn [disjoint_from app]; clear - SPR; lia]. }
    split; [exact LR3|].
    tr4 TFB3 MU4 WM4 ltac:(clear - SPR; lia). split; [exact TFB3|].
    tr4 F43 MU4 WM4 ltac:(clear - SPR; lia). split; [exact F43|].
    split; [exact TRNG|]. split; [exact NR|].
    tr4 HDR3 MU4 WM4 ltac:(clear - SPR BND HI SZ; try acb; lia). split; [exact HDR3|].
    tr4 UW3 MU4 WM4 ltac:(clear - SPR BND HI SZ; try acb; lia). split; [exact UW3|].
    split. { eapply stk_transport_disjoint; [exact TST3| exact MU4| exact WM4| cbn [disjoint_from app]; region_decide]. }
    tr4 UNW3 MU4 WM4 ltac:(clear - SPR BND HI; try acb; lia). split; [exact UNW3|].
    unfold AIAINIT in FLG3 |- *. tr4 FLG3 MU4 WM4 ltac:(clear - SPR BND HI; try acb; lia). split; [exact FLG3|].
    split; [exact (ia_if_transport true _ m3 m4 IA3 MU4 WM4 ltac:(hci; cbn [disjoint_from app]; region_decide))|].
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
End HeadRefill.

Section TailRefill.
  Variables (sp ra0 s0v s1v s2v s3v s4v s5v gp tp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (t0 t1 t2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 t3 t4 t5 t6 xra : word) (m : mem).
  Variables (lo : Z) (T : list Z) (rest : list word) (jk jke : list byte).
  Variables (U size TH qcache sb : Z) (k hdq LA qbytes : Z) (cnt : Z) (chunks : list Z) (B : Z) (j0 j1 j2 j3 : word).
  Let Wn := enq_new_W lo (bv_unsigned sp) TH B LA.

  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 2912 <= bv_unsigned sp.
  Hypothesis SPT : hidden (bv_unsigned sp + 16 <= 2^47).
  Hypothesis UR : hidden (aapp U 8 /\ AIMG_TOP + 16 <= U /\ U + 8 <= aceil).
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
  Hypothesis LR  : length rest = (255 - length T)%nat.
  Hypothesis NR  : (1 <= length T <= 30)%nat.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp + -2272).
  Hypothesis FR : rw_cells asegs m (bv_unsigned sp + -2272)
      [CB 8 jke; C8 (wz (U + -16)); C8 (wz (TH + OT_CACHE)); C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 (wz size);
       C8 (wz (TH + OT_TQ)); C8 (wz (AINST + OI_Q)); C8 (wz 0x96a04)].
  Hypothesis TQ : rw_cells asegs m (TH + OT_TQ) [C8 (wz k); C8 (wz hdq); C8 (wz LA); C8 (wz qbytes)].
  Hypothesis PC1 : rw_cells asegs m (TH + 2128) [C4 (wz cnt)].
  Hypothesis PC2 : rw_cells asegs m (TH + 2136) [C8 (wz kBatchSize)].
  Hypothesis PC3 : u32arr asegs m (TH + 2144) (wlist (rev chunks)).
  Hypothesis PC4 : stk asegs m (TH + 2144 + 4 * cnt) (TH + 2208).
  Hypothesis STATS : rw_cells asegs m (TH + 2768) [C8 j0; C8 j1; C8 j2; C8 j3].
  Hypothesis INST : rw_cells asegs m (AINST + OI_SPACEBEG) [C8 (wz sb)].
  Hypothesis BJ : stk asegs m B (B + kBatchSize).
  Hypothesis PFR : rw_cells asegs m (bv_unsigned sp + -2208) (put_frame sp s6 U TH).
  Hypothesis ESO : rw_cells asegs m (bv_unsigned sp + -2128) [C8 (wz (bv_unsigned sp + -2128 + 16)); C8 (wz (Z.of_nat (length T)))].
  Hypothesis TRB : u64arr asegs m (bv_unsigned sp + -2128 + 16) (map wz T ++ rest).
  Hypothesis TFB : rw_cells asegs m (bv_unsigned sp + -72) [C8 sp].
  Hypothesis F4  : rw_cells asegs m (bv_unsigned sp + -64) [CB 8 jk; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0].

  Definition free_tail_refill_post : machine_state -> Prop := fun ms' =>
    exists (j2' : word) m', free_ret_post sp ra0 s0v s1v s2v s3v s4v s5v gp tp s6 s7 s8 s9 s10 s11 F fc lo m' ms'
    /\ munch Wn m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (TH + OT_TQ) [C8 (wz (k + 1)); C8 (wz (if k =? 0 then B else hdq)); C8 (wz B); C8 (wz (qbytes + (size + kBatchSize)))]
    /\ (k <> 0 -> rw_cells asegs m' LA [C8 (wz B)])
    /\ rw_cells asegs m' B [C8 (wz 0); C8 (wz (size + kBatchSize)); C8 (wz 1); C8 (wz (U + -16))]
    /\ stk asegs m' (B + 32) (B + kBatchSize)
    /\ rw_cells asegs m' (TH + 2128) [C4 (wz (cnt - 1))]
    /\ u32arr asegs m' (TH + 2144) (wlist (rev (tl chunks)))
    /\ stk asegs m' (TH + 2144 + 4 * (cnt - 1)) (TH + 2208)
    /\ rw_cells asegs m' (TH + 2768) [C8 j0; C8 j1; C8 j2'; C8 j3].

  Theorem free_tail_refill :
    evt asegs free_tail_refill_post
      (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2272)) gp tp t0 t1 t2 (wz (TH + 2128)) (wz (TH + OT_CACHE))
               (wz 1) xa1 xa2 xa3 xa4 xa5 xa6 xa7
               (wz (U + -16)) (wz (TH + OT_TQ)) (Z_to_bv 64 (bv_unsigned sp + -2128)) (wz size) (wz qcache) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x96b64) fc None m (seg_rom asegs)).
  Proof.
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR.
    assert (BND : aceil <= lo /\ 4096 <= TH /\ TH + 4096 <= aceil /\ bv_unsigned sp + 16 <= 140737488355328
               /\ 7241744 <= U /\ U + 8 <= aceil /\ 140735193776128 <= aceil /\ 17594333495296 <= B /\ B + 8192 <= aceil /\ (TH + 4096 <= B \/ B + 8192 <= TH))
      by (clear - LO THR SPT UR BR; try acb; destruct THR as [THR']; destruct UR as [UR']; destruct BR as [BR']; destruct SPT as [SPT'];
          unfold AHI_LO, kBatchSize in *; acb; change (2^47)%Z with 140737488355328%Z in SPT'; aunf; repeat split; lia).
    region_sides. name_bands.
    eapply evt_cut.
    { eapply (@enq_refill_post _ sp gp tp t0 t1 t2 xa6 xa7 t3 t4 t5 t6 xra s7 s8 s9 s10 s11 F fc m m lo U size TH qcache sb k hdq LA qbytes cnt chunks B jke j0 j1 j2 j3).
      all: try eassumption. all: try apply munch_refl. all: try apply wmono_refl.
      intros NZ; destruct (LAh NZ) as (A1 & A2 & A3 & A4 & A5 & A6). split; [exact A1| split; [exact A2| split; [exact A3| split; [exact A4| exact A5]]]]. }
    cbv beta. intros ms4 PO4.
    destruct PO4 as (t0_4 & t1_4 & t2_4 & a1_4 & a2_4 & a3_4 & a4_4 & a5_4 & a6_4 & a7_4 & t3_4 & t4_4 & t5_4 & t6_4 & j2' & m4 & -> & MU4 & WM4 & MI4 & ST4
                     & TQ4 & LA4 & BC4 & BJ4 & PC14 & PC34 & PC44 & STATS4).
    unfold enq_new_W, kBatchSize, OT_TQ in MU4, BJ4, TQ4, BC4 |- *.
    Ltac tr4 H MU WM tac := eapply rw_cells_transport in H; [| exact MU| exact WM| cbn [disjoint_from cells_size csize length Nat.add Nat.mul app]; tac].
    assert (LAX : LA = 0 \/ (17594333495296 <= LA /\ LA + 8192 <= aceil /\ (TH + 4096 <= LA \/ LA + 8192 <= TH) /\ (B + 8192 <= LA \/ LA + 8192 <= B)
                             /\ (LA + 8192 <= U - 16 \/ U + 8 <= LA))).
    { destruct (Z.eq_dec k 0) as [KZ|KNZ]; [left; exact (LA0 KZ)| right].
      destruct (LAh KNZ) as (_ & Y1 & Y2 & Y3 & Y4 & Y5). unfold AHI_LO in Y1. clear - Y1 Y2 Y3 Y4 Y5. split; [exact Y1| split; [exact Y2| split; [exact Y3| split; [exact Y4| exact Y5]]]]. }
    Ltac slv LAX := destruct LAX as [LAZ|LAF]; [rewrite ?LAZ in *; clear LAZ | ]; try acb; lia.
    unfold put_frame in PFR. tr4 PFR MU4 WM4 ltac:(clear - BND SPR HI LAX; slv LAX).
    tr4 ESO MU4 WM4 ltac:(clear - BND SPR HI LAX; slv LAX).
    eapply u64arr_transport in TRB; [| exact MU4| exact WM4| cbn [disjoint_from app]; rewrite length_app, length_map, LR; clear - BND SPR HI NR LAX; slv LAX].
    tr4 TFB MU4 WM4 ltac:(clear - BND SPR HI LAX; slv LAX).
    tr4 F4 MU4 WM4 ltac:(clear - BND SPR HI LAX; slv LAX).
    eapply evt_cut.
    { eapply (@put_tail _ sp ra0 s0v s1v s2v s3v s4v s5v gp tp s6 s7 s8 s9 s10 s11 F fc lo T rest jk); try eassumption.
      - clear - HI; try acb; lia.
      - destruct THR as [XT]; constructor; clear - XT; tauto.
      - unfold kBatchSize in QB; clear - QB SZ; lia. }
    cbv beta. intros ms5 PO5.
    apply evt_done. exists j2', m4. split; [exact PO5|].
    split; [exact MU4|]. split; [exact WM4|]. split; [exact MI4|].
    split; [exact TQ4|]. split; [exact LA4|]. split; [exact BC4|]. split; [exact BJ4|]. split; [exact PC14|]. split; [exact PC34|]. split; [exact PC44| exact STATS4].
  Qed.
End TailRefill.
End HCW.
