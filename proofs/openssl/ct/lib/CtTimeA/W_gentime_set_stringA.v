(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog BnBase BnModel BnTree ApBase ApLogic ApPrim CtTime.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit R_cache_defs R_prim_defs R_sec_defs D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA AsStruct RtCallA ImplA ImplAX BnIfaceA UnwindA EdgesA UnwindX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall AFrameTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import RtGenStmtA W_crypto_reallocA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import I_lkit R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac ApRepDefs ApRep ApFrame W_akit W_prefix_create W_strdup.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Printf_lib.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeP Require Import TimeDefs TimeKit TimeKit2 TimeFmtPure TimeToTmDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import TimeDefsA TimeKitA Fr_ossl_asn1_time_to_tm W_time_to_tm_frontA TimeToTmDefsA W_time_to_tmA W_crypto_reallocIA W_asn1_string_copyA Fr_ASN1_GENERALIZEDTIME_set_string.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac rstep := OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.      (* [comment removed for export] *)
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
Local Ltac plia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP, RT_STACK in *; cbn [ar_FR ar_RT ar_SP0 ar_PMc push amb] in *; lia.
Import ListNotations.
Open Scope Z_scope.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  end.

(* [comment removed for export] *)
Ltac brc :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) =>
    let v := eval vm_compute in c in
    lazymatch v with
    | true => replace (if c then a else b) with a by (vm_compute; reflexivity)
    | false => replace (if c then a else b) with b by (vm_compute; reflexivity)
    end
  end.

Lemma genstr_len : forall ts, length (zb (genstr ts)) = if printable ts then 19%nat else 11%nat.
Proof. intros ts. unfold zb. rewrite length_map. apply genstr_length. Qed.

(* [comment removed for export] *)
Definition GENTIME_SETSTR_STACK_A : Z := 112 + T2T_STACK_A.

Section Kit.
Context {AR0 : ARun}.
(* [comment removed for export] *)
Lemma strlen_slk_cpsA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts (@ar_RT AR0)) (OW LB : list block) (lo s : Z) (str slack : list byte) (bsrc : block),
  @BnHeapA.AHEAP AR0 Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> @BnHeapA.ACEIL AR0 <= lo -> lo + RT_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A ->
  In bsrc (OW ++ LB) -> blk_addr bsrc <= s -> s + Z.of_nat (length str) + 1 <= blk_addr bsrc + blk_size bsrc ->
  s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo ->
  bytes_at ctasegs m s (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) < 2^40 ->
  (- (s + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  a0 = wz s ->
  cps ctasegs (ASTA (@ar_RT AR0) Σ (@ar_PMc AR0) (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (wz e_strlen) fc None m (seg_rom ctasegs))))
            (ASTA (@ar_RT AR0) Σ (@ar_PMc AR0) (icall_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz (Z.of_nat (length str))) Σ OW LB lo 0 0 m (fun _ => True))).
Proof.
  intros until bsrc. intros HEAP ST CEIL LO SPT SP16 MI -> INS S1 S2 SLO HS NONUL HN PAD ->.
  unfold MallocRep.wz in *.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (AH_range_gen _ _ _ _ bsrc HEAP INS) as (BS0 & _ & _ & BSC & _).
  eapply cps_conseq; [ eapply (rc_strlen (@ar_RT AR0) (@ar_RC AR0) Σ (@ar_PMc AR0)) with (s := s) (str := str) (slack := slack) (lo := lo); try reflexivity | intros c Hc; exact Hc | ].
  - exact ar_PMc_fdfs.
  - exact ar_PMc_ms.
  - exact HS.
  - exact NONUL.
  - exact HN.
  - exact PAD.
  - unfold BnHeapA.ACEIL in *. lia.
  - left. exact SLO.
  - exact (blk_checked_src Σ OW LB m sp lo bsrc s (Z.of_nat (length str) + 1) HEAP INS S1 ltac:(lia) CEIL).
  - exact (AH_art _ _ _ _ HEAP).
  - exact MI.
  - rewrite <- (Z_to_bv_bv_unsigned sp). eapply call_okA; [exact HEAP | exact ST | exact CEIL | exact LO | unfold USTACK_TOP; lia | exact SP16].
  - intros c Hc. eapply ASTA_conseq; [exact Hc|]. clear Hc.
    intros ms (m2 & RS & (ART2 & MI2 & WM2 & ST2) & PRES & _).
    destruct RS as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
    unfold icall_post, MallocRep.wz. do 16 eexists. exists m2. split; [reflexivity|].
    split; [exact MI2|]. split; [exact ST2|].
    split. { eapply AH_same_ex; [exact HEAP| exact ART2| exact WM2| exact PRES| right; right; lia]. }
    split; [exact WM2|].
    split; [pose proof (AH_frames _ _ _ _ HEAP) as HF; eapply (AH_agree_ex _ _ _ _ _ _ _ _ _ HEAP); rewrite <- HF; exact PRES |].
    exact I.
Qed.
End Kit.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RTS := (@ar_RT AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FRM := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Lemma gtss_open_t : forall Σ1 OW LB m3 f q jst,
  @BnHeapA.AHEAP (push AR f 1) Σ1 OW LB m3 -> (forall b, In b (OW ++ LB) -> off_fr f 1 b) -> @fr_geo (push AR f 1) f 1 ->
  rw_cells ctasegs m3 (shad f) (gtss_shadow_pro jst) -> ~ In q (map blk_id (OW ++ LB)) ->
  @BnHeapA.AHEAP (push AR f 1) Σ1 OW ((q, f + 32, 24) :: LB) m3.
Proof.
  intros Σ1 OW LB m3 f q jst HEAP FRESH GEO FRS Hq.
  destruct GEO as (G1 & G2 & G3 & G4 & G5).
  assert (F8 : f mod 8 = 0) by (clear - G2; Z.div_mod_to_equations; lia).
  apply (@frame_obj_open (push AR f 1) Σ1 OW LB m3 f 1%nat q (f + 32) 24 (or_introl eq_refl) HEAP); [clear; lia| change (fs_size 1) with 128; clear; lia| clear; lia| | exact Hq|].
  - apply (acc_of_shadow_cells m3 (shad f) (gtss_shadow_pro jst) 4%nat (f + 32) 24 FRS ltac:(clear - F8; Z.div_mod_to_equations; lia) ltac:(clear - G1; lia) ltac:(clear; lia));
      [rewrite (shad_aligned_add f 32 F8) by (clear; lia); clear; cbn; lia| clear; cbn; lia| reflexivity].
  - intros b Hb. pose proof (FRESH b (in_or_app _ _ _ (or_intror Hb))) as O. unfold off_fr in O. unfold blk_apart. change (fs_size 1) with 128 in O.
    cbn [blk_addr blk_size fst snd]. clear - O. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gentime_setstr_failA : forall (Q : config -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Σ : rts RTS) (OW LB : list block) (lo : Z)
    (bs : block) (G GS ts : Z) (gtail : list byte),
  AHEAP Σ OW LB m -> stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + GENTIME_SETSTR_STACK_A <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> (S (length FRM) < FRAMES_MAX)%nat -> 2 <= rt_credit RTS Σ ->
  In bs (OW ++ LB) -> blk_addr bs <= GS -> GS + 20 <= blk_addr bs + blk_size bs ->
  rw_cells ctasegs m GS [CB 20%nat (zb (genstr ts) ++ Z_to_bv 8 0 :: gtail)] ->
  printable ts = false -> 0 <= ts < 2^64 -> 0 <= G < 2^64 ->
  a0 = Z_to_bv 64 G -> a1 = Z_to_bv 64 GS ->
  (forall (Σ' : rts RTS) (m' : word -> option byte) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
     AHEAP Σ' OW LB m' -> rt_credit RTS Σ' = rt_credit RTS Σ - 2 -> rt_live RTS Σ' = rt_live RTS Σ ->
     stk ctasegs m' lo (bv_unsigned sp) -> mem_inv ctasegs m' ->
     agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m' ->
     cps ctasegs (ASTA RTS Σ' PMc (eq
       (MS (mkR ra sp gp (wz TP_A) t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
           F' (ret_pc ra) fc' None m' (seg_rom ctasegs)))) Q) ->
  cps ctasegs (ASTA RTS Σ PMc (eq
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ASN1_GENERALIZEDTIME_SET_STRING_A) fc None m (seg_rom ctasegs)))) Q.
Proof.
  intros until gtail. intros HEAP ST CEIL LO TOP AL16 MI -> FLEN CRED HINS S1 S2 HGS PR TSR GR -> -> K.
  unfold GENTIME_SETSTR_STACK_A, T2T_STACK_A, RT_STACK in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3. unfold USTACK_TOP in TOP.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HINS) as (B0 & _ & _ & BC & BI).
  assert (E63 : 2^63 = 9223372036854775808) by reflexivity. assert (E64 : 2^64 = 18446744073709551616) by reflexivity.
  pose proof (genstr_len ts) as GL. rewrite PR in GL.
  assert (TL : length gtail = 8%nat).
  { destruct HGS as [[[WF _] _] _]. cbn in WF. rewrite length_app in WF. cbn [length] in WF. rewrite GL in WF. clear - WF. lia. }
  change (Z_to_bv 64 ASN1_GENERALIZEDTIME_SET_STRING_A) with (wz GTSS_ENTRY).
  eapply (gtss_pro_cps Q) with (lo := lo) (OW := OW) (LB := LB);
    [exact HEAP| exact ST| exact CEIL| unfold GTSS_FRAME, RT_STACK; clear - LO; lia| unfold USTACK_TOP; exact TOP| exact AL16| exact MI| reflexivity| clear - FLEN; lia| clear - CRED; lia|].
  intros Σ1 m3 f spa g junk gj ra' t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' F1 fc1 j0 j8 jf24 jf32 jf56 jst
         HEAP3 FRESH GEO CR1 LIVE1 ST3 MI3 AGF LOW HIGH FRC SHC SPA32 SPAL SPAH GSZ SAVJ.
  unfold GTSS_BODY, MallocRep.wz.
  pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 1) with 128 in G3, G5. unfold BnHeapA.ACEIL in G3. cbn [ar_SP0 push amb] in G3. unfold SEGTOP_A in G4.
  pose proof CEIL as CEILu. unfold BnHeapA.ACEIL in CEILu.
  assert (F8 : f mod 8 = 0) by (clear - G2; Z.div_mod_to_equations; lia).
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - SPAL SPAH SPR LO CEIL C1; alia).
  pose proof (FRESH _ HINS) as OFS. unfold off_fr in OFS. change (fs_size 1) with 128 in OFS.
  (* [comment removed for export] *)
  apply (rw_cells_agree _ _ _ _ _ AGF) in HGS; [| intros xa Hxa; right; right; exists bs; split; [exact HINS| cbn in Hxa; lia]].
  (* [comment removed for export] *)
  destruct (bptr_fresh (map blk_id (OW ++ LB))) as [q Hq].
  pose proof (gtss_open_t Σ1 OW LB m3 f q jst HEAP3 FRESH GEO SHC Hq) as HEAPo.
  assert (HINS' : In bs (OW ++ (q, f + 32, 24) :: LB)) by (apply in_app_or in HINS as [?|?]; apply in_or_app; [left; assumption| right; right; assumption]).
  assert (HINT : In (q, f + 32, 24) (OW ++ (q, f + 32, 24) :: LB)) by (apply in_or_app; right; left; reflexivity).
  (* [comment removed for export] *)
  destruct (proj1 (rw_cells_app m3 f [_; _; _; _] _) FRC) as [FRC1 FRC2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in FRC2.
  destruct (proj1 (rw_cells_app m3 (f + 32) [_] _) FRC2) as [TT FRC3]. clear FRC FRC1 FRC2 FRC3 SHC.
  (* [comment removed for export] *)
  apply cps_from_evt'. step. apply evt_done.
  eapply cps_step_same.
  { eapply (@strlen_cpsA (push AR f 1) _ (Z_to_bv 64 spa)) with (lo := lo) (OW := OW) (LB := (q, f + 32, 24) :: LB) (s := GS) (str := zb (genstr ts)) (slack := gtail) (bsrc := bs);
      rewrite ?ESPA; try reflexivity.
    - exact HEAPo.
    - exact ST3.
    - unfold BnHeapA.ACEIL. cbn [ar_SP0 push amb]. exact CEILu.
    - unfold RT_STACK. clear - LO SPAL. lia.
    - unfold USTACK_TOP. clear - TOP SPAH. lia.
    - clear - SPA32. Z.div_mod_to_equations. lia.
    - exact MI3.
    - exact HINS'.
    - exact S1.
    - rewrite GL, TL. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. clear - S2. lia.
    - destruct HGS as [[_ BY] _]. cbn [cells_bytes cbytes app] in BY. rewrite app_nil_r in BY. exact BY.
    - apply genstr_nonul.
    - rewrite GL. cbn. clear; lia.
    - rewrite GL, TL. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. clear. Z.div_mod_to_equations. lia. }
  intros msL PO. unfold icall_post in PO. rewrite ?ESPA in PO.
  destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F3 & fc3 & mL & -> & MIL & STL & HEAPL & WML & AGL & _).
  rewrite (ret_pc_even 0x270b38) by (clear; lia). unfold MallocRep.wz. cbn [ar_PMc push amb]. rewrite GL. cbn [Z.of_nat Pos.of_succ_nat Pos.succ].
  (* [comment removed for export] *)
  apply (rw_cells_agree _ _ _ _ _ AGL) in LOW; [| intros xa Hxa; cbn in Hxa; split; [left; unfold USTACK_TOP; clear - Hxa TOP SPAH GSZ; lia| clear; lia]].
  apply (rw_cells_agree _ _ _ _ _ AGL) in HIGH; [| intros xa Hxa; cbn in Hxa; split; [left; unfold USTACK_TOP; clear - Hxa TOP SPAH; lia| clear; lia]].
  apply (rw_cells_agree _ _ _ _ _ AGL) in TT; [| intros xa Hxa; cbn in Hxa; split; [right; right; exists (q, f + 32, 24); split; [exact HINT| cbn; clear - Hxa; lia]| clear; lia]].
  clear HEAPo ST3 MI3.
  ablock HEAPL HINT ACCT OFFT.
  destruct (@AH_shb (push AR f 1) _ _ _ _ HEAPL) as [SHB1 SHB2].
  pose proof (munch_refl [(spa, spa + 40); (f + 32, f + 32 + 24)]%Z mL) as MUL. pose proof (wmono_refl ctasegs mL) as WML'.
  assert (OFFL : offshW [(spa, spa + 40); (f + 32, f + 32 + 24)]%Z) by (cbn [offshW]; clear - SPAL SPAH CEILu LO C1 C2 C3 G1 G3 G4 G5; plia).
  assert (AWO : Forall (@aclient_write_ok (push AR f 1) (OW ++ (q, f + 32, 24) :: LB)) [(spa, spa + 40); (f + 32, f + 32 + 24)]%Z).
  { constructor; [left; cbn [fst snd]; clear - CEILu LO SPAL SPAH TOP GSZ; plia|].
    constructor; [right; right; exists (q, f + 32, 24); split; [exact HINT| cbn; clear; lia]| constructor]. }
  apply (rw_cells_split_CB ctasegs mL _ [] 24 _ [] [4; 4; 8; 8]%nat) in TT; [| reflexivity]. cbn [mk_CB_cells app] in TT.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  step. zstep. step. brc.
  step. step. step. step. step. step. step. step. step.
  name_mem m4.
  match goal with H : munch _ mL m4 |- _ => rename H into MU4 end. match goal with H : wmono ctasegs mL m4 |- _ => rename H into WM4 end.
  match goal with H : stk ctasegs m4 _ _ |- _ => rename H into ST4 end. match goal with H : mem_inv ctasegs m4 |- _ => rename H into MI4 end.
  assert (HEAP4 : @BnHeapA.AHEAP (push AR f 1) Σ1 OW ((q, f + 32, 24) :: LB) m4) by (eapply (@AH_frame (push AR f 1)); [exact HEAPL| exact MU4| exact WM4| exact AWO]).
  (* [comment removed for export] *)
  lazymatch type of TT with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: _) =>
    pose proof (rw_cells_app_l m4 _ [c0; c1; c2] _ TT) as TD end.
  apply evt_done.
  (* [comment removed for export] *)
  eapply (@t2t_rejectA (push AR f 1) Q _ (Z_to_bv 64 spa)) with (lo := lo) (OW := OW) (LB := (q, f + 32, 24) :: LB) (bd := (q, f + 32, 24)) (DA := f + 32) (l := 11) (GS := GS) (tm := 0);
    rewrite ?ESPA; try reflexivity.
  - exact HEAP4.
  - exact ST4.
  - unfold BnHeapA.ACEIL. cbn [ar_SP0 push amb]. exact CEILu.
  - unfold T2T_STACK_A, RT_STACK. clear - LO SPAL. lia.
  - unfold USTACK_TOP. clear - TOP SPAH. lia.
  - clear - SPA32. Z.div_mod_to_equations. lia.
  - exact MI4.
  - cbn [ar_FR push amb length]. clear - FLEN. lia.
  - cbn [ar_RT push amb]. rewrite CR1. clear - CRED. lia.
  - exact HINT.
  - cbn [blk_addr blk_size fst snd]. clear; lia.
  - clear - F8. uchk_open. Z.div_mod_to_equations. lia.
  - exact TD.
  - clear; lia.
  - clear; lia.
  - intros Σ5 m5 w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 w3 w4 w5 w6 F5 fc5 HEAP5 CR5 LIVE5 ST5 MI5 AG5.
    cbn [ar_RT ar_PMc ar_FR push amb] in HEAP5, CR5, LIVE5, AG5 |- *.
    rewrite (ret_pc_even 0x270b70) by (clear; lia). unfold MallocRep.wz.
    (* [comment removed for export] *)
    apply (rw_cells_agree _ _ _ _ _ AG5) in LOW; [| intros xa Hxa; cbn in Hxa; left; unfold USTACK_TOP; clear - Hxa TOP SPAH GSZ; lia].
    apply (rw_cells_agree _ _ _ _ _ AG5) in HIGH; [| intros xa Hxa; cbn in Hxa; left; unfold USTACK_TOP; clear - Hxa TOP SPAH; lia].
    eapply (@frame_obj_close (push AR f 1)) in HEAP5; [| left; reflexivity| unfold in_fr; cbn [blk_addr blk_size fst snd]; change (fs_size 1) with 128; clear; lia].
    clear ACCT OFFT SHB1 SHB2 HEAPL HEAP4 TT TD.
    pose proof (munch_refl [(spa, spa + 40)]%Z m5) as MU5. pose proof (wmono_refl ctasegs m5) as WM5.
    apply cps_from_evt'.
    (* [comment removed for export] *)
    step. brc.
    apply evt_done.
    change (Z_to_bv 64 0x270b8c) with (wz GTSS_EXIT).
    eapply (gtss_epi_cps Q) with (lo := lo) (LB := LB) (gj := gj) (hrest := []);
      [exact HEAP5| intros b Hb; exact (FRESH b (in_or_app _ _ _ (or_intror Hb)))| first [exact ST5| rewrite <- ?ESPA; exact ST5]| exact CEIL| clear - LO SPAL; lia
      | unfold USTACK_TOP; exact TOP| exact SPAL| exact SPAH| exact GSZ| exact SAVJ| exact MI5
      | first [exact LOW| eapply (rw_cells_recast m5 spa _ _ LOW); [| reflexivity| reflexivity]; pose proof (proj1 (proj1 LOW)) as WF; cbn in WF; cbn; repeat split; try reflexivity; repeat match goal with H : _ /\ _ |- _ => destruct H end; assumption]
      | exact HIGH| reflexivity|].
    intros Σ' m' x11' HEAP' CR' LIVE' ST' MI' AG'.
    eapply K; [exact HEAP'| rewrite CR', CR5; cbn [ar_RT push amb]; rewrite CR1; clear; lia| rewrite LIVE', LIVE5; cbn [ar_RT push amb]; exact LIVE1| exact ST'| exact MI'|].
    (* [comment removed for export] *)
    assert (STKW : forall a, aclient_addr (OW ++ LB) (bv_unsigned sp) a -> outside [(spa, spa + 40); (f + 32, f + 32 + 24)]%Z a).
    { intros a Ha. cbn [outside fst snd]. split; [| split; [| exact I]].
      - destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha SPAH GSZ; lia| |].
        + destruct Ha as [(lw & hi & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr CEIL LO SPAL C1; alia.
        + pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & B3' & _). clear - Hr B3' CEIL LO SPAL. alia.
      - destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha G3 CEILu LO; lia| |].
        + destruct Ha as [(lw & hi & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr G4; lia.
        + pose proof (FRESH b Hb) as O. unfold off_fr in O. change (fs_size 1) with 128 in O. destruct b as [[bq bA] bn]; cbn [blk_addr blk_size fst snd] in Hr, O. clear - Hr O. lia. }
    assert (LIFT : forall a, aclient_addr (OW ++ LB) (bv_unsigned sp) a -> aclient_addr (OW ++ (q, f + 32, 24) :: LB) spa a).
    { intros a Ha. destruct Ha as [Ha|[Ha|Ha]]; [left; clear - Ha SPAH; unfold USTACK_TOP in *; lia| right; left; exact Ha| right; right].
      destruct Ha as (b & Hb & Hr). exists b. split; [| exact Hr]. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb| right; right; exact Hb]. }
    eapply agree_on_trans; [eapply agree_on_mono; [exact AGF| intros a Ha; exact Ha]|].
    eapply agree_on_trans; [eapply agree_on_mono; [exact AGL| intros a Ha; pose proof (STKW a Ha) as O; cbn [outside fst snd] in O; split; [exact (LIFT a Ha)| clear - O; lia]]|].
    eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU4)| exact STKW]|].
    eapply agree_on_trans; [eapply agree_on_mono; [exact AG5| exact LIFT]|].
    eapply agree_on_mono; [exact AG'|]. intros a Ha.
    destruct Ha as [Ha|[Ha|Ha]]; [left; clear - Ha SPAH; unfold USTACK_TOP in *; lia| right; left; exact Ha| right; right; exact Ha].
Qed.

(* [comment removed for export] *)
Local Notation E_gtss_copy := (E_ASN1_GENERALIZEDTIME_set_string_275f70 : uk_call 0x270a34 0x270b84 0x2242a0).

(* [comment removed for export] *)
Lemma wr_at_bytes : forall m a n, wr_at ctasegs m a (Z.of_nat n) -> exists bs, length bs = n /\ bytes_at ctasegs m a bs.
Proof.
  intros m a n (A0 & A1 & W). induction n as [|n IH].
  - exists []. split; [reflexivity|]. split; [exact A0|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - destruct IH as (bs & L & B); [lia| intros i Hi; apply W; lia|].
    destruct (wview_mrd_A m (wa (a + Z.of_nat n)) (W (Z.of_nat n) ltac:(lia))) as [b Hb].
    exists (bs ++ [b]). split; [rewrite length_app; cbn; lia|]. destruct B as (_ & _ & BB).
    split; [exact A0|]. split; [rewrite length_app; cbn; lia|].
    intros i Hi. rewrite length_app in Hi. cbn in Hi.
    destruct (Nat.lt_ge_cases i (length bs)) as [LT|GE].
    + rewrite nth_error_app1 by exact LT. apply BB. exact LT.
    + assert (E : i = length bs) by lia. subst i. rewrite nth_error_app2, Nat.sub_diag by lia. cbn. rewrite L. exact Hb.
Qed.

Lemma nodup_app_notin : forall {A : Type} (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof.
  induction l1 as [|a l1 IH]; cbn; intros l2 x ND H; [tauto|].
  inversion ND as [|a' l' NI ND']; subst. destruct H as [<-|H]; [intros K; apply NI; apply in_or_app; right; exact K| exact (IH l2 x ND' H)].
Qed.

Hypothesis REA : realloc_contract_gen RTS.


(* [comment removed for export] *)
Definition gentime_setstr_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RTS) (OW LB : list block) (G : Z) (dp : bptr) (lo : Z) (ts : Z) (m : mem)
    (p' : bptr) (Σ' : rts RTS) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' D',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (wz 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp)
    /\ apres_but LB (lb_remove dp OW) (bv_unsigned sp) G ASN1_STRING_SIZE m m'
    /\ rt_credit RTS Σ - 2 - mcost 19 <= rt_credit RTS Σ'
    /\ ablock_range D' 19 /\ AHEAP Σ' ((p', D', 19) :: lb_remove dp OW) LB m'
    /\ rw_cells ctasegs m' G (asn1_string_cells 19 V_ASN1_GENERALIZEDTIME D' 0)
    /\ rw_cells ctasegs m' D' [CB 19%nat (zb (genstr ts))].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gentime_setstr_okA : forall {X : Type}
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RTS) (OW LB : list block) (lo : Z)
    (gb dp qs : bptr) (G D fq : Z) (ts : Z) (t : tm6) (djunk : list byte) (ras : list Z)
    (k : option bptr -> aprog bptr X) (Q : X -> rts RTS -> machine_state -> Prop),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - GENTIME_SETSTR_STACK_A ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> realloc_statics m -> (S (length FRM) < FRAMES_MAX)%nat -> 2 + mcost 19 <= rt_credit RTS Σ ->
  In (gb, G, ASN1_STRING_SIZE) OW -> In (dp, D, 20) OW -> gb <> dp ->
  rw_cells ctasegs m G (asn1_string_cells 15 V_ASN1_GENERALIZEDTIME D 0) -> rw_cells ctasegs m D [CB 20%nat djunk] ->
  In (fq, 1%nat) FRM -> In (qs, fq + 32, 20) LB ->
  rw_cells ctasegs m (fq + 32) [CB 20%nat (zb (genstr ts) ++ [Z_to_bv 8 0])] ->
  gentime_adj ts = Some t -> 0 <= ts < 2^64 ->
  a0 = Z_to_bv 64 G -> a1 = Z_to_bv 64 (fq + 32) ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx ASN1_GENERALIZEDTIME_SET_STRING_A (bv_unsigned ra :: ras) ->
  (forall p' Σ' ms', ~ In p' (map blk_id (OW ++ LB)) ->
     gentime_setstr_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB G dp lo ts m p' Σ' ms' ->
     implAp (k (Some p')) Σ' Q ms') ->
  implAp (AReallocI dp 19 k) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ASN1_GENERALIZEDTIME_SET_STRING_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until Q. intros HEAP ST CEIL LO TOP AL16 MI TP RS FLEN CRED HGIN HDIN NE HG HD HFQ HQS HGS GA TSR -> -> UW CTX KOK. subst tp.
  pose proof LO as LO'. unfold GENTIME_SETSTR_STACK_A, T2T_STACK_A, RT_STACK in LO'.
  unfold ASN1_STRING_SIZE in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3. pose proof TOP as TOPu. unfold USTACK_TOP in TOPu.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (E63 : 2^63 = 9223372036854775808) by reflexivity. assert (E64 : 2^64 = 18446744073709551616) by reflexivity.
  assert (HGIN' : In (gb, G, 24) (OW ++ LB)) by (apply in_or_app; left; exact HGIN).
  assert (HQS' : In (qs, fq + 32, 20) (OW ++ LB)) by (apply in_or_app; right; exact HQS).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HGIN') as (BG0 & _ & _ & BGC & BGI). cbn [blk_addr blk_size fst snd] in BG0, BGC, BGI.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HQS') as (BS0 & _ & _ & BSC & BSI). cbn [blk_addr blk_size fst snd] in BS0, BSC, BSI.
  pose proof (AH_fr_geo _ _ _ _ fq 1%nat HEAP HFQ) as (Q1 & Q2 & Q3 & Q4 & Q5). change (fs_size 1) with 128 in Q3, Q5.
  assert (FQ8 : (fq + 32) mod 8 = 0) by (clear - Q2; Z.div_mod_to_equations; lia).
  assert (PR : printable ts = true) by (unfold printable; rewrite GA; reflexivity).
  pose proof (genstr_len ts) as GL. rewrite PR in GL.
  pose proof (gentime_adj_valid ts t GA) as TV. pose proof (ts_ms_range ts) as MSR.
  assert (MC0 : mcost 19 = 0) by reflexivity.
  intros XX Φ Dl SAFE LINK.
  change (Z_to_bv 64 ASN1_GENERALIZEDTIME_SET_STRING_A) with (wz GTSS_ENTRY).
  eapply (gtss_pro_cps _) with (lo := lo) (OW := OW) (LB := LB);
    [exact HEAP| exact ST| exact CEIL| unfold GTSS_FRAME, RT_STACK; clear - LO'; lia| exact TOP| exact AL16| exact MI| reflexivity| clear - FLEN; lia| clear - CRED MC0; lia|].
  intros Σ1 m3 f spa g junk gj ra' t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' F1 fc1 j0 j8 jf24 jf32 jf56 jst
         HEAP3 FRESH GEO CR1 LIVE1 ST3 MI3 AGF LOW HIGH FRC SHC SPA32 SPAL SPAH GSZ SAVJ.
  unfold GTSS_BODY, MallocRep.wz.
  pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 1) with 128 in G3, G5. unfold BnHeapA.ACEIL in G3. cbn [ar_SP0 push amb] in G3. unfold SEGTOP_A in G4.
  pose proof CEIL as CEILu. unfold BnHeapA.ACEIL in CEILu.
  assert (F8 : f mod 8 = 0) by (clear - G2; Z.div_mod_to_equations; lia).
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - SPAL SPAH SPR LO' CEIL C1; alia).
  pose proof (FRESH _ HQS') as OFS. unfold off_fr in OFS. change (fs_size 1) with 128 in OFS. cbn [blk_addr blk_size fst snd] in OFS.
  pose proof (FRESH _ HGIN') as OFG. unfold off_fr in OFG. change (fs_size 1) with 128 in OFG. cbn [blk_addr blk_size fst snd] in OFG.
  (* [comment removed for export] *)
  apply (rw_cells_agree _ _ _ _ _ AGF) in HGS; [| intros xa Hxa; right; right; exists (qs, fq + 32, 20); split; [exact HQS'| cbn; cbn in Hxa; clear - Hxa; lia]].
  apply (rw_cells_agree _ _ _ _ _ AGF) in HG; [| intros xa Hxa; right; right; exists (gb, G, 24); split; [exact HGIN'| cbn; cbn in Hxa; unfold asn1_string_cells in Hxa; cbn in Hxa; clear - Hxa; lia]].
  apply (rw_cells_agree _ _ _ _ _ AGF) in HD; [| intros xa Hxa; right; right; exists (dp, D, 20); split; [apply in_or_app; left; exact HDIN| cbn; cbn in Hxa; clear - Hxa; lia]].
  unfold asn1_string_cells, MallocRep.wz in HG.
  pose proof (FRESH _ (in_or_app _ _ _ (or_introl HDIN))) as OFD. unfold off_fr in OFD. change (fs_size 1) with 128 in OFD. cbn [blk_addr blk_size fst snd] in OFD.
  assert (AGL3 : agree_on (lib_addr OW) m m3) by (eapply agree_on_mono; [exact AGF|]; intros a HL; exact (lib_addr_aclient OW LB (bv_unsigned sp) a HL)).
  pose proof (realloc_statics_agree OW m m3 RS AGL3) as RS3.
  (* [comment removed for export] *)
  destruct (bptr_fresh (map blk_id (OW ++ LB))) as [q Hq].
  pose proof (gtss_open_t Σ1 OW LB m3 f q jst HEAP3 FRESH GEO SHC Hq) as HEAPo.
  assert (HQSo : In (qs, fq + 32, 20) (OW ++ (q, f + 32, 24) :: LB)) by (apply in_or_app; right; right; exact HQS).
  assert (HINT : In (q, f + 32, 24) (OW ++ (q, f + 32, 24) :: LB)) by (apply in_or_app; right; left; reflexivity).
  destruct (proj1 (rw_cells_app m3 f [_; _; _; _] _) FRC) as [FRC1 FRC2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in FRC2.
  destruct (proj1 (rw_cells_app m3 (f + 32) [_] _) FRC2) as [TT FRC3]. clear FRC FRC1 FRC2 FRC3 SHC.
  (* [comment removed for export] *)
  assert (HFQ1 : In (fq, 1%nat) (@ar_FR (push AR f 1))) by (cbn [ar_FR push amb]; right; exact HFQ).
  destruct (@AH_fr_wr (push AR f 1) _ _ _ _ fq 1%nat HEAPo HFQ1) as [(W0 & W1 & W2) _]. change (fs_size 1) with 128 in W1, W2.
  destruct (wr_at_bytes m3 (fq + 52) 4 ltac:(split; [clear - Q1; lia| split; [clear - W1; lia| intros i Hi; replace (fq + 52 + i) with (fq + (52 + i)) by lia; apply W2; lia]])) as (slk & SL & HSLK).
  assert (HSTR : bytes_at ctasegs m3 (fq + 32) (zb (genstr ts) ++ Z_to_bv 8 0 :: slk)).
  { destruct HGS as [[_ BY] _]. cbn [cells_bytes cbytes app] in BY. rewrite app_nil_r in BY.
    destruct BY as (BY0 & BY1 & BY2). destruct HSLK as (SK0 & SK1 & SK2). rewrite length_app, GL in BY1, BY2. cbn [length Nat.add] in BY1, BY2.
    split; [exact BY0|]. split; [rewrite length_app, GL; cbn [length]; clear - SK1 SL; lia|].
    intros i Hi. rewrite length_app, GL in Hi. cbn [length Nat.add] in Hi. rewrite SL in Hi.
    replace (zb (genstr ts) ++ Z_to_bv 8 0 :: slk) with ((zb (genstr ts) ++ [Z_to_bv 8 0]) ++ slk) by (rewrite <- app_assoc; reflexivity).
    destruct (Nat.lt_ge_cases i 20) as [LT|GE].
    - rewrite nth_error_app1 by (rewrite length_app, GL; cbn; lia). exact (BY2 i LT).
    - rewrite nth_error_app2 by (rewrite length_app, GL; cbn; lia). rewrite length_app, GL. cbn [length Nat.add].
      replace (fq + 32 + Z.of_nat i) with (fq + 52 + Z.of_nat (i - 20)) by lia. apply SK2. lia. }
  (* [comment removed for export] *)
  apply cps_from_evt'. step. apply evt_done.
  eapply cps_step_same.
  { eapply (@strlen_slk_cpsA (push AR f 1) _ (Z_to_bv 64 spa)) with (lo := lo) (OW := OW) (LB := (q, f + 32, 24) :: LB) (s := fq + 32) (str := zb (genstr ts)) (slack := slk) (bsrc := (qs, fq + 32, 20));
      rewrite ?ESPA; try reflexivity.
    - exact HEAPo.
    - exact ST3.
    - unfold BnHeapA.ACEIL. cbn [ar_SP0 push amb]. exact CEILu.
    - unfold RT_STACK. clear - LO' SPAL. lia.
    - unfold USTACK_TOP. clear - TOPu SPAH. lia.
    - clear - SPA32. Z.div_mod_to_equations. lia.
    - exact MI3.
    - exact HQSo.
    - rewrite GL. cbn. clear; lia.
    - rewrite GL, SL. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. clear - Q3 CEILu. unfold BnHeapA.ACEIL in *. lia.
    - exact HSTR.
    - apply genstr_nonul.
    - rewrite GL. cbn. clear; lia.
    - rewrite GL, SL. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. clear - Q2. Z.div_mod_to_equations. lia. }
  intros msL PO. unfold icall_post in PO. rewrite ?ESPA in PO.
  destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F3 & fc3 & mL & -> & MIL & STL & HEAPL & WML & AGL & _).
  rewrite (ret_pc_even 0x270b38) by (clear; lia). unfold MallocRep.wz. cbn [ar_PMc push amb]. rewrite GL. cbn [Z.of_nat Pos.of_succ_nat Pos.succ].
  apply (rw_cells_agree _ _ _ _ _ AGL) in LOW; [| intros xa Hxa; cbn in Hxa; split; [left; unfold USTACK_TOP; clear - Hxa TOPu SPAH GSZ; lia| clear; lia]].
  apply (rw_cells_agree _ _ _ _ _ AGL) in HIGH; [| intros xa Hxa; cbn in Hxa; split; [left; unfold USTACK_TOP; clear - Hxa TOPu SPAH; lia| clear; lia]].
  apply (rw_cells_agree _ _ _ _ _ AGL) in TT; [| intros xa Hxa; cbn in Hxa; split; [right; right; exists (q, f + 32, 24); split; [exact HINT| cbn; clear - Hxa; lia]| clear; lia]].
  apply (rw_cells_agree _ _ _ _ _ AGL) in HGS; [| intros xa Hxa; cbn in Hxa; split; [right; right; exists (qs, fq + 32, 20); split; [exact HQSo| cbn; clear - Hxa; lia]| clear; lia]].
  apply (rw_cells_agree _ _ _ _ _ AGL) in HG; [| intros xa Hxa; unfold asn1_string_cells in Hxa; cbn in Hxa; split; [right; right; exists (gb, G, 24); split; [apply in_or_app; left; exact HGIN| cbn; clear - Hxa; lia]| clear; lia]].
  apply (rw_cells_agree _ _ _ _ _ AGL) in HD; [| intros xa Hxa; cbn in Hxa; split; [right; right; exists (dp, D, 20); split; [apply in_or_app; left; exact HDIN| cbn; clear - Hxa; lia]| clear; lia]].
  assert (AGL3L : agree_on (lib_addr OW) m3 mL).
  { eapply agree_on_mono; [exact AGL|]. intros a HL. split; [| clear; lia]. pose proof (lib_addr_aclient OW LB (bv_unsigned sp) a HL) as Hc.
    destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; clear - Hc SPAH; unfold USTACK_TOP in *; lia| right; left; exact Hc| right; right; exists b; split; [| exact Hr]].
    apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb| right; right; exact Hb]. }
  pose proof (realloc_statics_agree OW m3 mL RS3 AGL3L) as RSL.
  clear HEAPo ST3 MI3 HSTR HSLK W0 W1 W2.
  ablock HEAPL HINT ACCT OFFT.
  destruct (@AH_shb (push AR f 1) _ _ _ _ HEAPL) as [SHB1 SHB2].
  pose proof (munch_refl [(spa, spa + 40); (f + 32, f + 32 + 24)]%Z mL) as MUL. pose proof (wmono_refl ctasegs mL) as WML'.
  assert (OFFL : offshW [(spa, spa + 40); (f + 32, f + 32 + 24)]%Z) by (cbn [offshW]; clear - SPAL SPAH CEILu LO' C1 C2 C3 G1 G3 G4 G5; plia).
  assert (AWO : Forall (@aclient_write_ok (push AR f 1) (OW ++ (q, f + 32, 24) :: LB)) [(spa, spa + 40); (f + 32, f + 32 + 24)]%Z).
  { constructor; [left; cbn [fst snd]; clear - CEILu LO' SPAL SPAH TOPu GSZ; plia|].
    constructor; [right; right; exists (q, f + 32, 24); split; [exact HINT| cbn; clear; lia]| constructor]. }
  apply (rw_cells_split_CB ctasegs mL _ [] 24 _ [] [4; 4; 8; 8]%nat) in TT; [| reflexivity]. cbn [mk_CB_cells app] in TT.
  (* [comment removed for export] *)
  lazymatch type of BGI with ?T => change (frozen T) in BGI end. lazymatch type of BSI with ?T => change (frozen T) in BSI end.
  lazymatch type of Q5 with ?T => change (frozen T) in Q5 end. lazymatch type of G5 with ?T => change (frozen T) in G5 end.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  step. zstep. step. brc.
  step. step. step. step. step. step. step. step. step.
  name_mem m4.
  match goal with H : munch _ mL m4 |- _ => rename H into MU4 end. match goal with H : wmono ctasegs mL m4 |- _ => rename H into WM4 end.
  match goal with H : stk ctasegs m4 _ _ |- _ => rename H into ST4 end. match goal with H : mem_inv ctasegs m4 |- _ => rename H into MI4 end.
  assert (HEAP4 : @BnHeapA.AHEAP (push AR f 1) Σ1 OW ((q, f + 32, 24) :: LB) m4) by (eapply (@AH_frame (push AR f 1)); [exact HEAPL| exact MU4| exact WM4| exact AWO]).
  lazymatch type of TT with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: _) =>
    pose proof (rw_cells_app_l m4 _ [c0; c1; c2] _ TT) as TD end.
  (* [comment removed for export] *)
  assert (HGC : rw_cells ctasegs m4 (fq + 32) (gcells t (ts_ms ts) ++ [Cells.C1 (Z_to_bv 8 0)])).
  { eapply rw_cells_recast; [exact HGS| | | reflexivity].
    - unfold gcells, zb8. cbn [cells_wf cell_wf app]. repeat split; exact I.
    - rewrite cells_bytes_app, <- (genstr_gcells ts t GA). unfold zb. cbn [cells_bytes cbytes app map]. rewrite app_nil_r. reflexivity. }
  pose proof (proj1 (rw_cells_app _ _ _ _) HGC) as [HGC1 _].
  apply evt_done.
  (* [comment removed for export] *)
  eapply (@t2t_acceptA (push AR f 1) _ _ (Z_to_bv 64 spa)) with (lo := lo) (OW := OW) (LB := (q, f + 32, 24) :: LB) (bd := (q, f + 32, 24)) (bs := (qs, fq + 32, 20)) (btm := (qs, fq + 32, 20))
        (DA := f + 32) (GS := fq + 32) (tm := 0) (ms := ts_ms ts) (t := t) (tjunk := []);
    rewrite ?ESPA; try reflexivity.
  - exact HEAP4.
  - exact ST4.
  - unfold BnHeapA.ACEIL. cbn [ar_SP0 push amb]. exact CEILu.
  - unfold T2T_STACK_A, RT_STACK. clear - LO' SPAL. lia.
  - unfold USTACK_TOP. clear - TOPu SPAH. lia.
  - clear - SPA32. Z.div_mod_to_equations. lia.
  - exact MI4.
  - cbn [ar_FR push amb length]. clear - FLEN. lia.
  - cbn [ar_RT push amb]. rewrite CR1. clear - CRED MC0. lia.
  - exact HINT.
  - cbn [blk_addr blk_size fst snd]. clear; lia.
  - clear - F8. uchk_open. Z.div_mod_to_equations. lia.
  - exact TD.
  - exact HQSo.
  - cbn [blk_addr blk_size fst snd]. clear; lia.
  - first [exact FQ8| uchk_open; exact FQ8| revert FQ8; uchk_open; intros FQ8; exact FQ8].
  - exact HGC1.
  - exact TV.
  - clear - MSR; lia.
  - clear; lia.
  - intros NZ. exfalso. apply NZ. reflexivity.
  - intros Σ5 m5 w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 w3 w4 w5 w6 F5 fc5 HEAP5 CR5 LIVE5 ST5 MI5 AG5 _.
    cbn [ar_RT ar_PMc ar_FR push amb] in HEAP5, CR5, LIVE5, AG5 |- *.
    rewrite (ret_pc_even 0x270b70) by (clear; lia). unfold MallocRep.wz.
    assert (AG5' : agree_on (aclient_addr (OW ++ (q, f + 32, 24) :: LB) spa) m4 m5) by (eapply agree_on_mono; [exact AG5|]; intros a Ha; split; [exact Ha| left; reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ AG5') in LOW; [| intros xa Hxa; cbn in Hxa; left; unfold USTACK_TOP; clear - Hxa TOPu SPAH GSZ; lia].
    apply (rw_cells_agree _ _ _ _ _ AG5') in HIGH; [| intros xa Hxa; cbn in Hxa; left; unfold USTACK_TOP; clear - Hxa TOPu SPAH; lia].
    apply (rw_cells_agree _ _ _ _ _ AG5') in TT; [| intros xa Hxa; cbn in Hxa; right; right; exists (q, f + 32, 24); split; [exact HINT| cbn; clear - Hxa; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG5') in HGS; [| intros xa Hxa; cbn in Hxa; right; right; exists (qs, fq + 32, 20); split; [exact HQSo| cbn; clear - Hxa; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG5') in HG; [| intros xa Hxa; unfold asn1_string_cells in Hxa; cbn in Hxa; right; right; exists (gb, G, 24); split; [apply in_or_app; left; exact HGIN| cbn; clear - Hxa; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG5') in HD; [| intros xa Hxa; cbn in Hxa; right; right; exists (dp, D, 20); split; [apply in_or_app; left; exact HDIN| cbn; clear - Hxa; lia]].
    assert (AGL45 : agree_on (lib_addr OW) m4 m5).
    { eapply agree_on_mono; [exact AG5'|]. intros a HL. pose proof (lib_addr_aclient OW LB (bv_unsigned sp) a HL) as Hc.
      destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; clear - Hc SPAH; unfold USTACK_TOP in *; lia| right; left; exact Hc| right; right; exists b; split; [| exact Hr]].
      apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb| right; right; exact Hb]. }
    assert (RS4 : realloc_statics m4) by (unfold realloc_statics in *; eapply ro_cells_agree; [apply (agree_on_of_munch_nw _ _ _ MU4)| exact RSL|]; intros a Ha; cbn in Ha; unfold CR_REALLOC_IMPL in Ha; cbn [outside]; clear - Ha CEILu LO' SPAL G4 C1; unfold BnHeapA.ACEIL in *; repeat split; try exact I; lia).
    pose proof (realloc_statics_agree OW m4 m5 RS4 AGL45) as RS5.
    clear ACCT OFFT SHB1 SHB2 HEAPL HEAP4 TD HGC HGC1.
    destruct (@AH_shb (push AR f 1) _ _ _ _ HEAP5) as [SHB1 SHB2].
    pose proof (munch_refl [(spa, spa + 40)]%Z m5) as MU5. pose proof (wmono_refl ctasegs m5) as WM5.
    (* [comment removed for export] *)
    lazymatch type of TT with rw_cells _ _ _ [?c0; ?c1; ?c2; ?c3] =>
      assert (TT4 : rw_cells ctasegs m5 (f + 32) (asn1_string_cells 19 24 (fq + 32) 0)) by (unfold asn1_string_cells, MallocRep.wz; exact TT) end.
    apply cps_from_evt'.
    (* [comment removed for export] *)
    step. brc.
    step. if_cases KG; zify_cond KG; [exfalso; rewrite ?unsigned_lit in KG by (clear - BG0 BGC C3; lia); clear - KG BG0; lia|]. clear KG.
    step. step. step.
    apply evt_done.
    (* [comment removed for export] *)
    eapply (implAp_elim (AReallocI dp 19 k)); [| exact SAFE| exact LINK| rewrite LIVE5; cbn [ar_RT push amb]; exact LIVE1].
    pose proof (@ASN1_STRING_copy_walkA (push AR f 1) UK BE REA X) as CW. cbn [ar_RT ar_PMc ar_FR push amb] in CW.
    eapply CW with (lo := lo) (OW := OW) (LB := (q, f + 32, 24) :: LB) (gb := gb) (dp := dp) (bstr := (q, f + 32, 24)) (bsrc := (qs, fq + 32, 20))
                   (G := G) (dl := 15) (ty0 := V_ASN1_GENERALIZEDTIME) (D0 := D) (n0 := 20) (STR := f + 32) (n := 19) (ty := 24) (GS := fq + 32) (src := zb (genstr ts))
                   (ras := bv_unsigned ra :: ras);
      rewrite ?ESPA; try reflexivity; clear CW.
    + exact HEAP5.
    + exact ST5.
    + unfold BnHeapA.ACEIL. cbn [ar_SP0 push amb]. exact CEILu.
    + unfold ASN1_STRING_COPY_STACK_A, SINT_COPY_STACK_A, CRYPTO_REALLOC2_STACK, RT_STACK. clear - LO' SPAL. lia.
    + unfold USTACK_TOP. clear - TOPu SPAH. lia.
    + clear - SPA32. Z.div_mod_to_equations. lia.
    + exact MI5.
    + exact RS5.
    + exact HGIN.
    + exact HG.
    + clear; lia.
    + clear; lia.
    + exact HDIN.
    + exact NE.
    + exact HINT.
    + cbn. intros E. apply Hq. rewrite E. apply in_map_iff. exists (gb, G, 24). split; [reflexivity| exact HGIN'].
    + cbn. intros E. apply Hq. rewrite E. apply in_map_iff. exists (dp, D, 20). split; [reflexivity| apply in_or_app; left; exact HDIN].
    + exact TT4.
    + clear - F8. uchk_open. Z.div_mod_to_equations. lia.
    + clear; lia.
    + exact HQSo.
    + cbn. intros E. pose proof (AH_nodup _ _ _ _ HEAP) as ND. rewrite map_app in ND.
      apply (nodup_app_notin _ _ gb ND); [apply in_map_iff; exists (gb, G, 24); split; [reflexivity| exact HGIN]| rewrite <- E; apply in_map_iff; exists (qs, fq + 32, 20); split; [reflexivity| exact HQS]].
    + cbn. intros E. pose proof (AH_nodup _ _ _ _ HEAP) as ND. rewrite map_app in ND.
      apply (nodup_app_notin _ _ dp ND); [apply in_map_iff; exists (dp, D, 20); split; [reflexivity| exact HDIN]| rewrite <- E; apply in_map_iff; exists (qs, fq + 32, 20); split; [reflexivity| exact HQS]].
    + cbn [blk_addr blk_size fst snd]. clear; lia.
    + destruct HGS as [[_ BY] _]. cbn [cells_bytes cbytes app] in BY. rewrite app_nil_r in BY. apply bytes_at_app in BY. destruct BY as [BY _]. exact BY.
    + unfold zb. rewrite length_map, genstr_length, PR. reflexivity.
    + clear; lia.
    + cbn [ar_RT push amb]. rewrite CR5, CR1. clear - CRED MC0. lia.
    + (* [comment removed for export] *)
      eapply (uw_call m m5 spa (bv_unsigned sp) 16 [] (bv_unsigned ra) (bv_unsigned s0) ras);
        [ exact UW
        | eapply agree_on_trans; [eapply agree_on_mono; [exact AGF| intros a Ha; left; exact Ha]|];
          eapply agree_on_trans; [eapply agree_on_mono; [exact AGL| intros a Ha; split; [left; clear - Ha SPAH; lia| clear; lia]]|];
          eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU4)| intros a Ha; cbn [outside fst snd]; clear - Ha SPAH G3 CEILu LO'; repeat split; try exact I; lia]|];
          eapply agree_on_mono; [exact AG5'| intros a Ha; left; clear - Ha SPAH; lia]
        | reflexivity | clear - SPAH; lia | clear - AL16; uchk_open; Z.div_mod_to_equations; lia | clear - TOPu; unfold USTACK_TOP; lia
        | apply bv_unsigned_in_range | rewrite !Z_to_bv_bv_unsigned; cbn [app]; exact HIGH ].
    + rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_gtss_copy CTX).
    + intros p' Σ6 ms6 Hp PO6. unfold ascopy_postA in PO6. rewrite ?ESPA in PO6.
      destruct PO6 as (q0 & q1 & q2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & q3 & q4 & q5 & q6 & F6 & fc6 & m6 & D' & -> & MI6 & ST6 & AP6 & CR6 & BR6 & HEAP6 & HG6 & HD6).
      rewrite (ret_pc_even 0x270b84) by (clear; lia). unfold MallocRep.wz.
      unfold apres_but, ASN1_STRING_SIZE in AP6.
      apply (rw_cells_agree _ _ _ _ _ AP6) in LOW; [| intros xa Hxa; cbn in Hxa; split; [left; unfold USTACK_TOP; clear - Hxa TOPu SPAH GSZ; lia| clear - Hxa BGC CEILu LO' SPAL; unfold BnHeapA.ACEIL in BGC; lia]].
      apply (rw_cells_agree _ _ _ _ _ AP6) in HIGH; [| intros xa Hxa; cbn in Hxa; split; [left; unfold USTACK_TOP; clear - Hxa TOPu SPAH; lia| clear - Hxa BGC CEILu LO' SPAL SPAH; unfold BnHeapA.ACEIL in BGC; lia]].
      (* [comment removed for export] *)
      pose proof HEAP6 as HEAP6c.
      eapply (@frame_obj_close (push AR f 1)) in HEAP6c; [| left; reflexivity| unfold in_fr; cbn [blk_addr blk_size fst snd]; change (fs_size 1) with 128; clear; lia].
      lazymatch goal with |- @implAp _ ?X0 ?t0 ?S0 ?Q0 ?ms0 => change (@implAp AR X0 t0 S0 Q0 ms0) end.
      intros X3 Φ3 D3 SAFE3 LINK3.
      pose proof (munch_refl [(spa, spa + 40)]%Z m6) as MU6. pose proof (wmono_refl ctasegs m6) as WM6.
      apply cps_from_evt'. step. brc. step. apply evt_done.
      change (Z_to_bv 64 0x270b8c) with (wz GTSS_EXIT).
      eapply (gtss_epi_cps _) with (lo := lo) (LB := LB) (gj := gj) (hrest := []);
        [exact HEAP6c| intros b Hb; exact (FRESH b (in_or_app _ _ _ (or_intror Hb)))| exact ST6| exact CEIL| clear - LO' SPAL; lia
        | exact TOP| exact SPAL| exact SPAH| exact GSZ| exact SAVJ| exact MI6
        | first [exact LOW| eapply (rw_cells_recast m6 spa _ _ LOW); [| reflexivity| reflexivity]; pose proof (proj1 (proj1 LOW)) as WF; cbn in WF; cbn; repeat split; try reflexivity; repeat match goal with H : _ /\ _ |- _ => destruct H end; assumption]
        | exact HIGH| reflexivity|].
      intros Σ7 m7 x11 HEAP7 CR7 LIVE7 ST7 MI7 AG7.
      eapply (implAp_elim (k (Some p'))); [| exact SAFE3| exact LINK3| exact LIVE7].
      apply (KOK p' Σ7).
      { intros Hin. apply Hp. rewrite map_app, in_app_iff in Hin |- *. destruct Hin as [Hin|Hin]; [left; exact Hin| right; cbn; right; exact Hin]. }
      unfold gentime_setstr_postA, MallocRep.wz.
      do 16 eexists. exists m7, D'. split; [reflexivity|].
      split; [exact MI7|]. split; [exact ST7|].
      split.
      { unfold apres_but, ASN1_STRING_SIZE.
        assert (LIFT : forall a, aclient_addr (lb_remove dp OW ++ LB) (bv_unsigned sp) a -> aclient_addr (OW ++ LB) (bv_unsigned sp) a).
        { intros a [Ha|[Ha|(b & Hb & Hr)]]; [left; exact Ha| right; left; exact Ha| right; right; exists b; split; [exact (lb_remove_app_incl1 _ _ _ _ Hb)| exact Hr]]. }
        assert (LIFT2 : forall a, aclient_addr (OW ++ LB) (bv_unsigned sp) a -> aclient_addr (OW ++ (q, f + 32, 24) :: LB) spa a).
        { intros a Ha. destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [left; clear - Ha SPAH; unfold USTACK_TOP in *; lia| right; left; exact Ha| right; right; exists b; split; [| exact Hr]].
          apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb| right; right; exact Hb]. }
        assert (STKW : forall a, aclient_addr (OW ++ LB) (bv_unsigned sp) a -> outside [(spa, spa + 40); (f + 32, f + 32 + 24)]%Z a).
        { intros a Ha. cbn [outside fst snd]. split; [| split; [| exact I]].
          - destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha SPAH GSZ; lia| |].
            + destruct Ha as [(lw & hi & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr CEIL LO' SPAL C1; alia.
            + pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & B3' & _). clear - Hr B3' CEIL LO' SPAL. alia.
          - destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha G3 CEILu LO'; lia| |].
            + destruct Ha as [(lw & hi & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr G4; lia.
            + pose proof (FRESH b Hb) as O. unfold off_fr in O. change (fs_size 1) with 128 in O. destruct b as [[bq bA] bn]; cbn [blk_addr blk_size fst snd] in Hr, O. clear - Hr O. lia. }
        eapply agree_on_trans; [eapply agree_on_mono; [exact AGF| intros a [Ha _]; exact (LIFT a Ha)]|].
        eapply agree_on_trans; [eapply agree_on_mono; [exact AGL| intros a [Ha _]; split; [exact (LIFT2 a (LIFT a Ha))| clear; lia]]|].
        eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU4)| intros a [Ha _]; exact (STKW a (LIFT a Ha))]|].
        eapply agree_on_trans; [eapply agree_on_mono; [exact AG5'| intros a [Ha _]; exact (LIFT2 a (LIFT a Ha))]|].
        eapply agree_on_trans.
        { eapply agree_on_mono; [exact AP6|]. intros a [Ha Hn]. split; [| exact Hn].
          destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [left; clear - Ha SPAH; unfold USTACK_TOP in *; lia| right; left; exact Ha| right; right].
          exists b. split; [| exact Hr]. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb| right; right; exact Hb]. }
        eapply agree_on_mono; [exact AG7|]. intros a [Ha Hn].
        destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [left; clear - Ha SPAH; unfold USTACK_TOP in *; lia| right; left; exact Ha| right; right].
        exists b. split; [| exact Hr]. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; right; exact Hb| right; exact Hb]. }
      split; [rewrite CR7; cbn [ar_RT ar_PMc ar_FR push amb] in CR6; clear - CR6 CR5 CR1; lia|]. split; [exact BR6|]. split; [exact HEAP7|].
      split.
      { apply (rw_cells_agree _ _ _ _ _ AG7); [exact HG6|]. intros xa Hxa. right; right. exists (gb, G, 24). split; [right; apply in_or_app; left; apply lb_remove_In_map; [exact HGIN| cbn; exact NE]| cbn; unfold asn1_string_cells in Hxa; cbn in Hxa; clear - Hxa; lia]. }
      apply (rw_cells_agree _ _ _ _ _ AG7); [exact HD6|]. intros xa Hxa. right; right. exists (p', D', 19). split; [left; reflexivity| cbn; cbn in Hxa; clear - Hxa; lia].
Qed.

End WithRT.
