(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog BnBase BnModel BnTree ApBase ApLogic CtTime PrintfModel PrintfModelX.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit R_cache_defs R_prim_defs R_sec_defs D_defs D_cs I_vsnstmt F_pop_arg.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA ImplAX BnIfaceA AsStruct RtCallA UnwindA EdgesA UnwindX W_cryptoA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall AFrameTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac ApRepDefs ApRep ApFrame W_prefix_create W_strdup W_asn1_stringA W_bio_printf.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Printf_lib Printf_ctfmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeP Require Import TimeDefs TimeKit TimeKit2 TimeFmtPure TimeMagic W_posix_to_tm.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import TimeDefsA TimeKitA W_posix_to_tmA W_gmtimeA W_gmtime_adjA W_snprintfA W_time_from_tmA Fr_ASN1_GENERALIZEDTIME_adj.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
Local Ltac plia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP, RT_STACK in *; cbn [ar_FR ar_RT ar_SP0 ar_PMc push amb] in *; lia.
Import ListNotations.
Open Scope Z_scope.

Ltac brc :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) =>
    let v := eval vm_compute in c in
    lazymatch v with
    | true => replace (if c then a else b) with a by (vm_compute; reflexivity)
    | false => replace (if c then a else b) with b by (vm_compute; reflexivity)
    end
  end.

Local Notation E_gtadj_fromtm := (E_ASN1_GENERALIZEDTIME_adj_2761dc : uk_call 0x270c5c 0x270df0 0x26f848).   (* [comment removed for export] *)

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FRM := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Definition GENTIME_ADJ_STACK_A : Z := 112 + FROM_TM_STACK_A.

(* [comment removed for export] *)
Definition gtadj_LB (f : Z) (qd qt : bptr) (LB : list block) : list block := (qd, f + 64, 56) :: (qt, f + 32, 8) :: LB.

Lemma gtadj_open : forall Σ1 OW LB m3 f qt qd,
  @BnHeapA.AHEAP (push AR f 2) Σ1 OW LB m3 -> (forall b, In b (OW ++ LB) -> off_fr f 2 b) -> @fr_geo (push AR f 2) f 2 ->
  (forall jst, rw_cells ctasegs m3 (shad f) (gtadj_shadow_pro jst) -> 
   ~ In qt (map blk_id (OW ++ LB)) -> ~ In qd (map blk_id (OW ++ (qt, f + 32, 8) :: LB)) ->
   @BnHeapA.AHEAP (push AR f 2) Σ1 OW (gtadj_LB f qd qt LB) m3).
Proof.
  intros Σ1 OW LB m3 f qt qd HEAP FRESH GEO jst FRS Hqt Hqd.
  destruct GEO as (G1 & G2 & G3 & G4 & G5).
  assert (F8 : f mod 8 = 0) by (clear - G2; Z.div_mod_to_equations; lia).
  assert (APL : forall q A n b, f + 32 <= A -> A + n <= f + 248 -> In b LB -> blk_apart (q, A, n) b).
  { intros q A n b HA HA2 Hb. pose proof (FRESH b (in_or_app _ _ _ (or_intror Hb))) as O. unfold off_fr in O. unfold blk_apart. change (fs_size 2) with 256 in O.
    cbn [blk_addr blk_size fst snd]. clear - O HA HA2. lia. }
  assert (HEAPt : @BnHeapA.AHEAP (push AR f 2) Σ1 OW ((qt, f + 32, 8) :: LB) m3).
  { apply (@frame_obj_open (push AR f 2) Σ1 OW LB m3 f 2%nat qt (f + 32) 8 (or_introl eq_refl) HEAP); [clear; lia| change (fs_size 2) with 256; clear; lia| clear; lia| | exact Hqt|].
    - apply (acc_of_shadow_cells m3 (shad f) (gtadj_shadow_pro jst) 4%nat (f + 32) 8 FRS ltac:(clear - F8; Z.div_mod_to_equations; lia) ltac:(clear - G1; lia) ltac:(clear; lia));
        [rewrite (shad_aligned_add f 32 F8) by (clear; lia); clear; cbn; lia| clear; cbn; lia| reflexivity].
    - intros b Hb. apply APL; [clear; lia| clear; lia| exact Hb]. }
  apply (@frame_obj_open (push AR f 2) Σ1 OW ((qt, f + 32, 8) :: LB) m3 f 2%nat qd (f + 64) 56 (or_introl eq_refl) HEAPt); [clear; lia| change (fs_size 2) with 256; clear; lia| clear; lia| | exact Hqd|].
  - apply (acc_of_shadow_cells m3 (shad f) (gtadj_shadow_pro jst) 8%nat (f + 64) 56 FRS ltac:(clear - F8; Z.div_mod_to_equations; lia) ltac:(clear - G1; lia) ltac:(clear; lia));
      [rewrite (shad_aligned_add f 64 F8) by (clear; lia); clear; cbn; lia| clear; cbn; lia| reflexivity].
  - intros b [<-|Hb]; [unfold blk_apart; cbn; clear; lia| apply APL; [clear; lia| clear; lia| exact Hb]].
Qed.

(* [comment removed for export] *)
Lemma gtadj_frontA : forall (Q : config -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z),
  AHEAP Σ OW LB m -> stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - GENTIME_ADJ_STACK_A ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> (length FRM < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  a1 = wz 0 ->
  (forall (Σ1 : rts RT) (m4 : mem) (f spa : Z) (g : nat) (junk gj : list byte) (qd qt : bptr)
          (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
     @BnHeapA.AHEAP (push AR f 2) Σ1 OW (gtadj_LB f qd qt LB) m4 -> (forall b, In b (OW ++ LB) -> off_fr f 2 b) -> @fr_geo (push AR f 2) f 2 ->
     ~ In qt (map blk_id (OW ++ LB)) -> ~ In qd (map blk_id (OW ++ (qt, f + 32, 8) :: LB)) ->
     rt_credit RT Σ1 = rt_credit RT Σ - 1 -> rt_live RT Σ1 = rt_live RT Σ ->
     stk ctasegs m4 lo spa -> mem_inv ctasegs m4 ->
     agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m4 ->
     rw_cells ctasegs m4 spa [C8 (Z_to_bv 64 f); CB g junk] ->
     rw_cells ctasegs m4 (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
     spa mod 32 = 0 -> bv_unsigned sp - 112 <= spa -> spa <= bv_unsigned sp - 96 ->
     Z.of_nat g = bv_unsigned sp - spa - 24 -> junk = gj ++ cells_bytes [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] ->
     rw_cells ctasegs m4 (f + 64) (tm_cells epoch_tm) -> rw_cells ctasegs m4 (f + 32) [C8 (Z_to_bv 64 0)] ->
     cps ctasegs (ASTA RT Σ1 PMc (eq
       (MS (mkR ra' (Z_to_bv 64 spa) gp (wz TP_A) t0' t1' t2' sp (Z_to_bv 64 spa) (Z_to_bv 64 (f + 64)) a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 f) a3 a0 a2 a1 (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 (-8)) s10 s11 t3' t4' t5' t6')
           F' (Z_to_bv 64 0x270dc0) fc' None m4 (seg_rom ctasegs)))) Q) ->
  cps ctasegs (ASTA RT Σ PMc (eq
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ASN1_GENERALIZEDTIME_ADJ_A) fc None m (seg_rom ctasegs)))) Q.
Proof.
  intros until lo. intros HEAP ST CEIL LO TOP AL16 MI -> FLEN CRED Ea1 K.
  pose proof LO as LO'. unfold GENTIME_ADJ_STACK_A, FROM_TM_STACK_A, ASN1_STRING_SET_STACK, CRYPTO_MALLOC_STACK, RT_STACK in LO'.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3. unfold USTACK_TOP in TOP.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  change (wz ASN1_GENERALIZEDTIME_ADJ_A) with (wz GTADJ_ENTRY).
  eapply (gtadj_pro_cps Q) with (lo := lo) (OW := OW) (LB := LB);
    [exact HEAP| exact ST| exact CEIL| unfold GTADJ_FRAME, RT_STACK; clear - LO'; lia| unfold USTACK_TOP; exact TOP| exact AL16| exact MI| reflexivity| exact FLEN| exact CRED|].
  intros Σ1 m3 f spa g junk gj ra' t0' t1' t2' a6' a7' t3' t4' t5' t6' F1 fc1 jf24 jf40 jf64 jf120 jst
         HEAP3 FRESH GEO CR1 LIVE1 ST3 MI3 AGF LOW HIGH FRC SHC SPA32 SPAL SPAH GSZ SAVJ.
  unfold GTADJ_BODY, MallocRep.wz. subst a1. unfold MallocRep.wz in FRC.
  pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 2) with 256 in G3, G5. unfold BnHeapA.ACEIL in G3. cbn [ar_SP0 push amb] in G3. unfold SEGTOP_A in G4.
  pose proof CEIL as CEILu. unfold BnHeapA.ACEIL in CEILu.
  assert (F8 : f mod 8 = 0) by (clear - G2; Z.div_mod_to_equations; lia).
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - SPAL SPAH SPR LO' LO0; lia).
  (* [comment removed for export] *)
  destruct (bptr_fresh (map blk_id (OW ++ LB))) as [qt Hqt].
  destruct (bptr_fresh (map blk_id (OW ++ (qt, f + 32, 8) :: LB))) as [qd Hqd].
  pose proof (gtadj_open Σ1 OW LB m3 f qt qd HEAP3 FRESH GEO jst SHC Hqt Hqd) as HEAPo.
  assert (HINT : In (qt, f + 32, 8) (OW ++ gtadj_LB f qd qt LB)) by (apply in_or_app; right; right; left; reflexivity).
  assert (HIND : In (qd, f + 64, 56) (OW ++ gtadj_LB f qd qt LB)) by (apply in_or_app; right; left; reflexivity).
  (* [comment removed for export] *)
  destruct (proj1 (rw_cells_app m3 f [_; _; _; _] _) FRC) as [_ FRC2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in FRC2.
  destruct (proj1 (rw_cells_app m3 (f + 32) [_] _) FRC2) as [PT FRC3]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in FRC3.
  destruct (proj1 (rw_cells_app m3 (f + 32 + 8) [_] _) FRC3) as [_ FRC4]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in FRC4.
  destruct (proj1 (rw_cells_app m3 (f + 32 + 8 + 24) [_] _) FRC4) as [PD _].
  replace (f + 32 + 8 + 24) with (f + 64) in PD by (clear; lia). clear FRC FRC2 FRC3 FRC4.
  pose proof (munch_refl [(spa - 32, spa)]%Z m3) as MU3. pose proof (wmono_refl ctasegs m3) as WM3.
  assert (AWO : Forall (@aclient_write_ok (push AR f 2) (OW ++ gtadj_LB f qd qt LB)) [(spa - 32, spa)]%Z).
  { constructor; [left; cbn [fst snd]; clear - CEILu LO' SPAL SPAH TOP; plia| constructor]. }
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep.
  apply evt_done. eapply cps_step_same.
  { eapply (@OPENSSL_gmtime_specA (push AR f 2)) with (lo := lo) (OW := OW) (LB := gtadj_LB f qd qt LB) (pt := qt) (pd := qd) (TP := f + 32) (tv := 0) (D := f + 64);
      rewrite ?ESPA; try reflexivity.
    - exact HEAPo.
    - exact ST3.
    - unfold BnHeapA.ACEIL. cbn [ar_SP0 push amb]. exact CEILu.
    - unfold OPENSSL_GMTIME_STACK_A, OPENSSL_POSIX_TO_TM_STACK_A, RT_STACK. clear - LO' SPAL. lia.
    - unfold USTACK_TOP. clear - TOP SPAH. lia.
    - clear - SPA32. Z.div_mod_to_equations. lia.
    - exact MI3.
    - exact HINT.
    - clear - F8. uchk_open. Z.div_mod_to_equations. lia.
    - exact PT.
    - clear; lia.
    - exact HIND.
    - clear - F8. uchk_open. Z.div_mod_to_equations. lia.
    - exact PD.
    - clear; lia. }
  intros msM PO. unfold gmtime_postA in PO. rewrite ?ESPA in PO.
  destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F3 & fc3 & m4 & -> & MI4 & ST4 & HEAP4 & WM4 & AG4 & TM4).
  rewrite (ret_pc_even 0x270dbc) by (clear; lia). unfold MallocRep.wz.
  unfold p2tm_ret in *. unfold p2tm_cells in TM4. rewrite utc_from_posix_0 in *. cbn [Z.eqb] in *.
  assert (Ef : bv_unsigned (Z_to_bv 64 (f + 64)) = f + 64) by (apply unsigned_lit; clear - G1 G3 CEILu LO' SPR; lia).
  apply (rw_cells_agree _ _ _ _ _ AG4) in LOW; [| intros xa Hxa; cbn in Hxa; split; [left; unfold USTACK_TOP; clear - Hxa TOP SPAH GSZ; lia| clear - Hxa G3 CEILu LO' SPAL; lia]].
  apply (rw_cells_agree _ _ _ _ _ AG4) in HIGH; [| intros xa Hxa; cbn in Hxa; split; [left; unfold USTACK_TOP; clear - Hxa TOP SPAH; lia| clear - Hxa G3 CEILu LO' SPAL SPAH; lia]].
  apply (rw_cells_agree _ _ _ _ _ AG4) in PT; [| intros xa Hxa; cbn in Hxa; split; [right; right; exists (qt, f + 32, 8); split; [exact HINT| cbn; clear - Hxa; lia]| clear - Hxa; lia]].
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?Ef in K0; clear - K0 G1; lia|]. try clear K0.
  apply evt_done.
  eapply K; [exact HEAP4| exact FRESH| exact GEO| exact Hqt| exact Hqd| exact CR1| exact LIVE1| exact ST4| exact MI4| | exact LOW| exact HIGH| exact SPA32| exact SPAL| exact SPAH| exact GSZ| exact SAVJ| exact TM4| exact PT].
  (* [comment removed for export] *)
  eapply agree_on_trans; [exact AGF|].
  eapply agree_on_mono; [exact AG4|]. intros a Ha. split.
  - destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [left; clear - Ha SPAH; unfold USTACK_TOP in *; lia| right; left; exact Ha| right; right].
    exists b. split; [| exact Hr]. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb| right; right; right; exact Hb].
  - destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha G3 CEILu LO'; lia| |].
    + destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr G4; lia.
    + pose proof (FRESH b Hb) as O. unfold off_fr in O. change (fs_size 2) with 256 in O. destruct b as [[bq bA] bn]; cbn [blk_addr blk_size fst snd] in Hr, O. clear - Hr O. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithPFC.
Hypothesis PFC : printf_contracts RT.

(* [comment removed for export] *)
Local Ltac adj_callA dv f qd qt HEAPx STx MIx DATA CEILu LO' SPAL SPAH TOP SPA32 FLEN CR1 ESPA CRED MC0 F8 :=
  do 3 zstep; zstep;
  apply evt_done;
  eapply (@OPENSSL_gmtime_adj_cpsA (push AR f 2)) with (lo := _) (pa := qd) (A := f + 64) (d := dv); rewrite ?ESPA;
  [ exact HEAPx | exact STx | unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; exact CEILu
  | unfold OPENSSL_GMTIME_ADJ_STACK_A, RT_STACK; clear - LO' SPAL; lia
  | unfold USTACK_TOP; clear - TOP SPAH; lia | clear - SPA32; Z.div_mod_to_equations; lia | exact MIx | reflexivity
  | cbn [ar_FR push amb length]; clear - FLEN; lia | cbn [ar_RT ar_FR push amb]; clear - CR1 CRED MC0; lia
  | apply in_or_app; right; left; reflexivity | clear - F8; uchk_open; Z.div_mod_to_equations; lia | exact DATA | idtac | idtac | reflexivity | idtac | reflexivity | ].

Lemma gentime_adj_okA : forall {X : Type}
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z)
    (gb : bptr) (G : Z) (ts : Z) (t : tm6) (ras : list Z)
    (k : option bptr -> aprog bptr X) (Q : X -> rts RT -> machine_state -> Prop),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - GENTIME_ADJ_STACK_A ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> crypto_statics m -> realloc_statics m ->
  (S (length FRM) < FRAMES_MAX)%nat -> 2 + mcost 20 <= rt_credit RT Σ ->
  In (gb, G, ASN1_STRING_SIZE) OW -> rw_cells ctasegs m G (asn1_string_cells 0 V_ASN1_GENERALIZEDTIME 0 0) ->
  0 <= ts < 2^64 -> gentime_adj ts = Some t ->
  a0 = wz G -> a1 = wz 0 -> a2 = wz (ts_day ts) -> a3 = wz (ts_sec ts) ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx ASN1_GENERALIZEDTIME_ADJ_A (bv_unsigned ra :: ras) ->
  (forall p Σ' ms', ~ In p (map blk_id (OW ++ LB)) ->
     gentime_adj_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB G lo m t (2 + mcost 20) p Σ' ms' ->
     implAp (k (Some p)) Σ' Q ms') ->
  implAp (AMalloc 20 k) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ASN1_GENERALIZEDTIME_ADJ_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until Q. intros HEAP ST CEIL LO TOP AL16 MI TP CS RS FLEN CRED HGIN HG TSR GA -> Ea1 -> -> UW CTX KOK.
  pose proof LO as LO'. unfold GENTIME_ADJ_STACK_A, FROM_TM_STACK_A, ASN1_STRING_SET_STACK, CRYPTO_MALLOC_STACK, RT_STACK in LO'.
  unfold ASN1_STRING_SIZE in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
  pose proof TOP as TOPu. unfold USTACK_TOP in TOPu.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (HGIN' : In (gb, G, 24) (OW ++ LB)) by (apply in_or_app; left; exact HGIN).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HGIN') as (BG0 & _ & _ & BGC & BGI). cbn [blk_addr blk_size fst snd] in BG0, BGC, BGI.
  pose proof (ts_day_range ts) as DR. pose proof (ts_sec_range ts) as SR.
  pose proof (gentime_adj_valid _ _ GA) as TV.
  assert (MC0 : mcost 20 = 0) by reflexivity.
  intros XX Φ Dl SAFE LINK.
  eapply (gtadj_frontA _) with (lo := lo) (OW := OW) (LB := LB);
    [exact HEAP| exact ST| exact CEIL| exact LO| exact TOP| exact AL16| exact MI| exact TP| clear - FLEN; lia| clear - CRED MC0; lia| exact Ea1|].
  intros Σ1 m4 f spa g junk gj qd qt ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F1 fc1
         HEAP4 FRESH GEO Hqt Hqd CR1 LIVE1 ST4 MI4 AG4 LOW HIGH SPA32 SPAL SPAH GSZ SAVJ TM4 PT4.
  pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 2) with 256 in G3, G5. unfold BnHeapA.ACEIL in G3. cbn [ar_SP0 push amb] in G3. unfold SEGTOP_A in G4.
  pose proof CEIL as CEILu. unfold BnHeapA.ACEIL in CEILu.
  assert (F8 : f mod 8 = 0) by (clear - G2; Z.div_mod_to_equations; lia).
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - SPAL SPAH SPR LO' LO0; lia).
  pose proof (FRESH _ HGIN') as OFG. unfold off_fr in OFG. change (fs_size 2) with 256 in OFG. cbn [blk_addr blk_size fst snd] in OFG.
  assert (HIND : In (qd, f + 64, 56) (OW ++ gtadj_LB f qd qt LB)) by (apply in_or_app; right; left; reflexivity).
  (* [comment removed for export] *)
  apply (rw_cells_agree _ _ _ _ _ AG4) in HG; [| intros xa Hxa; right; right; exists (gb, G, 24); split; [exact HGIN'| cbn; cbn in Hxa; clear - Hxa; lia]].
  assert (AGL4 : agree_on (lib_addr OW) m m4).
  { eapply agree_on_mono; [exact AG4|]. intros a HL. exact (lib_addr_aclient OW LB (bv_unsigned sp) a HL). }
  pose proof (crypto_statics_agree' OW m m4 CS AGL4) as CS4. pose proof (realloc_statics_agree OW m m4 RS AGL4) as RS4.
  (* [comment removed for export] *)
  assert (TAIL : forall (Σx : rts RT) (mx : mem) (rax t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x : word) (Fx : bvmap 5 word) (fcx : bv 32),
    @BnHeapA.AHEAP (push AR f 2) Σx OW (gtadj_LB f qd qt LB) mx -> rt_credit RT Σ - 2 <= rt_credit RT Σx -> rt_live RT Σx = rt_live RT Σ ->
    stk ctasegs mx lo spa -> mem_inv ctasegs mx ->
    agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m mx ->
    rw_cells ctasegs mx spa [C8 (Z_to_bv 64 f); CB g junk] -> rw_cells ctasegs mx (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
    rw_cells ctasegs mx (f + 64) (tm_cells t) ->
    cps ctasegs (ASTA RT Σx PMc (eq
       (MS (mkR rax (Z_to_bv 64 spa) gp (wz TP_A) t0x t1x t2x sp (Z_to_bv 64 spa) a0x a1x a2x a3x a4x a5x a6x a7x
                 (Z_to_bv 64 f) (Z_to_bv 64 (ts_sec ts)) (Z_to_bv 64 G) (Z_to_bv 64 (ts_day ts)) (Z_to_bv 64 (f + 64)) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 (-8)) s10 s11 t3x t4x t5x t6x)
           Fx (Z_to_bv 64 0x270de0) fcx None mx (seg_rom ctasegs))))
      (fun c => exists a X' Σ', Φ a X' /\ linked Dl Σ' X' /\ ASTA RT Σ' PMc (Q a Σ') c)).
  { intros Σx mx rax t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x Fx fcx HEAPx CRx LIVEx STx MIx AGx LOWx HIGHx DATAx.
    assert (AGLx : agree_on (lib_addr OW) m mx).
    { eapply agree_on_mono; [exact AGx|]. intros a HL. exact (lib_addr_aclient OW LB (bv_unsigned sp) a HL). }
    assert (AG4x : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m4 mx).
    { intros a Ha Hc. rewrite (AGx a Ha Hc). symmetry. exact (AG4 a Ha Hc). }
    pose proof HG as HGx.
    apply (rw_cells_agree _ _ _ _ _ AG4x) in HGx; [| intros xa Hxa; right; right; exists (gb, G, 24); split; [exact HGIN'| cbn; cbn in Hxa; clear - Hxa; lia]].
    apply cps_from_evt'.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    apply evt_done.
    eapply (implAp_elim (AMalloc 20 k)); [| exact SAFE| exact LINK| exact LIVEx].
    pose proof (@ossl_asn1_time_from_tm_walkA (push AR f 2) UK BE PFC X) as FT. cbn [ar_RT ar_PMc ar_FR push amb] in FT.
    eapply FT with (lo := lo) (OW := OW) (LB := gtadj_LB f qd qt LB) (gb := gb) (pt := qd) (G := G) (TS := f + 64) (t := t) (ras := bv_unsigned ra :: ras);
      rewrite ?ESPA; try reflexivity; clear FT.
    - exact HEAPx.
    - exact STx.
    - unfold BnHeapA.ACEIL. cbn [ar_SP0 push amb]. exact CEILu.
    - unfold FROM_TM_STACK_A, ASN1_STRING_SET_STACK, CRYPTO_MALLOC_STACK, RT_STACK. clear - LO' SPAL. lia.
    - unfold USTACK_TOP. clear - TOPu SPAH. lia.
    - clear - SPA32. Z.div_mod_to_equations. lia.
    - exact MIx.
    - exact CS4 || (eapply crypto_statics_agree'; [exact CS| exact AGLx]).
    - exact (realloc_statics_agree OW m mx RS AGLx).
    - exact HGIN.
    - exact HGx.
    - exact HIND.
    - clear - F8. uchk_open. Z.div_mod_to_equations. lia.
    - destruct DATAx as [DR' _]. exact DR'.
    - exact TV.
    - unfold ASN1_STRING_SIZE. clear - OFG. lia.
    - clear - CRED CRx MC0. lia.
    - (* [comment removed for export] *)
      eapply (uw_call m mx spa (bv_unsigned sp) 16 [] (bv_unsigned ra) (bv_unsigned s0) ras);
        [ exact UW
        | eapply agree_on_mono; [exact AGx|]; intros a Ha; left; exact Ha
        | reflexivity | clear - SPAH; lia | clear - AL16; uchk_open; Z.div_mod_to_equations; lia | clear - TOPu; unfold USTACK_TOP; lia
        | apply bv_unsigned_in_range | rewrite !Z_to_bv_bv_unsigned; cbn [app]; exact HIGHx ].
    - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_gtadj_fromtm CTX).
    - intros p Σ6 ms6 Hp PO6. unfold gentime_adj_postA in PO6. rewrite ?ESPA in PO6.
      destruct PO6 as (q0 & q1 & q2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & q3 & q4 & q5 & q6 & F6 & fc6 & m6 & D & junk4
                       & -> & MI6 & ST6 & AP6 & CR6 & BR6 & HEAP6 & HG6 & HD6 & JL).
      rewrite (ret_pc_even 0x270df0) by (clear; lia). unfold MallocRep.wz.
      unfold apres_but, ASN1_STRING_SIZE in AP6.
      apply (rw_cells_agree _ _ _ _ _ AP6) in LOWx; [| intros xa Hxa; cbn in Hxa; split; [left; unfold USTACK_TOP; clear - Hxa TOPu SPAH GSZ; lia| clear - Hxa BGC CEILu LO' SPAL; unfold BnHeapA.ACEIL in BGC; lia]].
      apply (rw_cells_agree _ _ _ _ _ AP6) in HIGHx; [| intros xa Hxa; cbn in Hxa; split; [left; unfold USTACK_TOP; clear - Hxa TOPu SPAH; lia| clear - Hxa BGC CEILu LO' SPAL SPAH; unfold BnHeapA.ACEIL in BGC; lia]].
      (* [comment removed for export] *)
      pose proof HEAP6 as HEAP6c.
      eapply (@frame_obj_close (push AR f 2)) in HEAP6c; [| left; reflexivity| unfold in_fr; cbn [blk_addr blk_size fst snd]; change (fs_size 2) with 256; clear; lia].
      eapply (@frame_obj_close (push AR f 2)) in HEAP6c; [| left; reflexivity| unfold in_fr; cbn [blk_addr blk_size fst snd]; change (fs_size 2) with 256; clear; lia].
      lazymatch goal with |- @implAp _ ?X0 ?t0 ?S0 ?Q0 ?ms0 => change (@implAp AR X0 t0 S0 Q0 ms0) end.
      intros X3 Φ3 D3 SAFE3 LINK3.
      change (Z_to_bv 64 0x270df0) with (wz GTADJ_EXIT).
      eapply (@gtadj_epi_cps AR _) with (lo := lo) (LB := LB) (gj := gj) (hrest := []);
        [exact HEAP6c| intros b Hb; exact (FRESH b (in_or_app _ _ _ (or_intror Hb)))| exact ST6| exact CEIL| clear - LO' SPAL; lia
        | exact TOP| exact SPAL| exact SPAH| exact GSZ| exact SAVJ| exact MI6| exact LOWx| exact HIGHx| reflexivity|].
      intros Σ7 m7 x11 HEAP7 CR7 LIVE7 ST7 MI7 AG7.
      eapply (implAp_elim (k (Some p))); [| exact SAFE3| exact LINK3| exact LIVE7].
      apply (KOK p Σ7).
      { intros Hin. apply Hp. rewrite map_app, in_app_iff in Hin |- *. destruct Hin as [Hin|Hin]; [left; exact Hin| right; cbn; right; right; exact Hin]. }
      unfold gentime_adj_postA, MallocRep.wz.
      do 16 eexists. exists m7, D, junk4. split; [reflexivity|].
      split; [exact MI7|]. split; [exact ST7|].
      split.
      { unfold apres_but.
        eapply agree_on_trans; [eapply agree_on_mono; [exact AGx| intros a [Ha _]; exact Ha]|].
        eapply agree_on_trans.
        { eapply agree_on_mono; [exact AP6|]. intros a [Ha Hn]. split; [| exact Hn].
          destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [left; clear - Ha SPAH; unfold USTACK_TOP in *; lia| right; left; exact Ha| right; right].
          exists b. split; [| exact Hr]. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb| right; right; right; exact Hb]. }
        eapply agree_on_mono; [exact AG7|]. intros a [Ha Hn].
        destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [left; clear - Ha SPAH; unfold USTACK_TOP in *; lia| right; left; exact Ha| right; right].
        exists b. split; [| exact Hr]. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; right; exact Hb| right; exact Hb]. }
      split; [rewrite CR7; cbn [ar_RT ar_PMc ar_FR push amb] in CR6; clear - CR6 CRx; lia|]. split; [exact BR6|]. split; [exact HEAP7|].
      split.
      { apply (rw_cells_agree _ _ _ _ _ AG7); [exact HG6|]. intros xa Hxa. right; right. exists (gb, G, 24). split; [right; apply in_or_app; left; exact HGIN| cbn; unfold asn1_string_cells in Hxa; cbn in Hxa; clear - Hxa; lia]. }
      split; [| exact JL].
      apply (rw_cells_agree _ _ _ _ _ AG7); [exact HD6|]. intros xa Hxa. right; right. exists (p, D, 20). split; [left; reflexivity| cbn; cbn in Hxa; clear - Hxa; lia]. }
  (* [comment removed for export] *)
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep.
  destruct (Z.eq_dec (ts_day ts) 0) as [D0|DN].
  - zstep. if_cases K1; zify_cond K1; [exfalso; apply K1; rewrite D0; reflexivity|]. try clear K1.
    destruct (Z.eq_dec (ts_sec ts) 0) as [S0|SN].
    + (* [comment removed for export] *)
      zstep. if_cases K2; zify_cond K2; [| exfalso; apply K2; rewrite S0; reflexivity]. try clear K2.
      assert (Et : t = epoch_tm) by (unfold gentime_adj in GA; rewrite D0, S0 in GA; cbn in GA; congruence). subst t.
      apply evt_done. eapply TAIL; [exact HEAP4| clear - CR1; lia| exact LIVE1| exact ST4| exact MI4| exact AG4| exact LOW| exact HIGH| exact TM4].
    + zstep. if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by (clear - SR; lia); clear - K2 SN; lia|]. try clear K2.
      destruct (rw_cells_forget _ _ _ _ TM4) as [junk56 TMJ]. cbn [cells_size csize Nat.add tm_cells] in TMJ.
      adj_callA 0 f qd qt HEAP4 ST4 MI4 TM4 CEILu LO' SPAL SPAH TOPu SPA32 FLEN CR1 ESPA CRED MC0 F8.
      all: try (clear - SR; lia).
      { rewrite D0. reflexivity. }
      intros Σ5 m5 t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F5 fc5 HEAP5 CR5 LIVE5 ST5 MI5 AG5 DATA5.
      rewrite (ret_pc_even 0x270ddc) by (clear; lia). unfold MallocRep.wz.
      assert (UV : utc_from_posix (0 * 86400 + ts_sec ts) = Some t).
      { unfold gentime_adj, SECS_PER_DAY in GA. rewrite D0 in GA. replace (ts_sec ts =? 0) with false in GA by (symmetry; apply Z.eqb_neq; exact SN). exact GA. }
      unfold p2tm_ret, p2tm_cells in *. rewrite UV in *.
      apply (rw_cells_agree _ _ _ _ _ AG5) in LOW; [| intros xa Hxa; cbn in Hxa; split; [left; unfold USTACK_TOP; clear - Hxa TOPu SPAH GSZ; lia| clear - Hxa G3 CEILu LO' SPAL; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG5) in HIGH; [| intros xa Hxa; cbn in Hxa; split; [left; unfold USTACK_TOP; clear - Hxa TOPu SPAH; lia| clear - Hxa G3 CEILu LO' SPAL SPAH; lia]].
      apply cps_from_evt'. zstep. brc. apply evt_done. cbn [ar_RT ar_PMc ar_FR push amb].
      cbn [ar_RT ar_PMc ar_FR push amb] in CR5, LIVE5, HEAP5, AG5.
      eapply TAIL; [exact HEAP5| rewrite CR5; clear - CR1; lia| rewrite LIVE5; exact LIVE1| exact ST5| exact MI5| | exact LOW| exact HIGH| exact DATA5].
      eapply agree_on_trans; [exact AG4|]. eapply agree_on_mono; [exact AG5|]. intros a Ha. split.
      * destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [left; clear - Ha SPAH; unfold USTACK_TOP in *; lia| right; left; exact Ha| right; right].
        exists b. split; [| exact Hr]. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb| right; right; right; exact Hb].
      * destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha G3 CEILu LO'; lia| |].
        -- destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr G4; lia.
        -- pose proof (FRESH b Hb) as O. unfold off_fr in O. change (fs_size 2) with 256 in O. destruct b as [[bq bA] bn]; cbn [blk_addr blk_size fst snd] in Hr, O. clear - Hr O. lia.
  - zstep. if_cases K1; zify_cond K1; [| exfalso; revert K1; clear - DR DN; unfold MallocRep.wz; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; intros K1;
             assert (E64 : 2 ^ Z.of_N 64 = 18446744073709551616) by reflexivity; rewrite E64 in K1; Z.to_euclidean_division_equations; lia]. try clear K1.
    destruct (rw_cells_forget _ _ _ _ TM4) as [junk56 TMJ]. cbn [cells_size csize Nat.add tm_cells] in TMJ.
    adj_callA (ts_day ts) f qd qt HEAP4 ST4 MI4 TM4 CEILu LO' SPAL SPAH TOPu SPA32 FLEN CR1 ESPA CRED MC0 F8.
    all: try (clear - SR DR; lia).
    { reflexivity. }
    intros Σ5 m5 t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F5 fc5 HEAP5 CR5 LIVE5 ST5 MI5 AG5 DATA5.
    rewrite (ret_pc_even 0x270ddc) by (clear; lia). unfold MallocRep.wz.
    assert (UV : utc_from_posix (ts_day ts * 86400 + ts_sec ts) = Some t).
    { unfold gentime_adj, SECS_PER_DAY in GA. replace (ts_day ts =? 0) with false in GA by (symmetry; apply Z.eqb_neq; exact DN). exact GA. }
    unfold p2tm_ret, p2tm_cells in *. rewrite UV in *.
    apply (rw_cells_agree _ _ _ _ _ AG5) in LOW; [| intros xa Hxa; cbn in Hxa; split; [left; unfold USTACK_TOP; clear - Hxa TOPu SPAH GSZ; lia| clear - Hxa G3 CEILu LO' SPAL; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG5) in HIGH; [| intros xa Hxa; cbn in Hxa; split; [left; unfold USTACK_TOP; clear - Hxa TOPu SPAH; lia| clear - Hxa G3 CEILu LO' SPAL SPAH; lia]].
    apply cps_from_evt'. zstep. brc. apply evt_done. cbn [ar_RT ar_PMc ar_FR push amb].
    cbn [ar_RT ar_PMc ar_FR push amb] in CR5, LIVE5, HEAP5, AG5.
    eapply TAIL; [exact HEAP5| rewrite CR5; clear - CR1; lia| rewrite LIVE5; exact LIVE1| exact ST5| exact MI5| | exact LOW| exact HIGH| exact DATA5].
    eapply agree_on_trans; [exact AG4|]. eapply agree_on_mono; [exact AG5|]. intros a Ha. split.
    * destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [left; clear - Ha SPAH; unfold USTACK_TOP in *; lia| right; left; exact Ha| right; right].
      exists b. split; [| exact Hr]. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb| right; right; right; exact Hb].
    * destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha G3 CEILu LO'; lia| |].
      -- destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr G4; lia.
      -- pose proof (FRESH b Hb) as O. unfold off_fr in O. change (fs_size 2) with 256 in O. destruct b as [[bq bA] bn]; cbn [blk_addr blk_size fst snd] in Hr, O. clear - Hr O. lia.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gentime_adj_failA : forall (Q : config -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z) (G : Z) (ts : Z),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - GENTIME_ADJ_STACK_A ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> (S (length FRM) < FRAMES_MAX)%nat -> 2 <= rt_credit RT Σ ->
  0 <= ts < 2^64 -> gentime_adj ts = None ->
  a0 = wz G -> a1 = wz 0 -> a2 = wz (ts_day ts) -> a3 = wz (ts_sec ts) ->
  (forall (Σ' : rts RT) (m' : mem) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
     AHEAP Σ' OW LB m' -> rt_credit RT Σ - 2 <= rt_credit RT Σ' -> rt_live RT Σ' = rt_live RT Σ ->
     stk ctasegs m' lo (bv_unsigned sp) -> mem_inv ctasegs m' ->
     agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m' ->
     cps ctasegs (ASTA RT Σ' PMc (eq
       (MS (mkR ra sp gp (wz TP_A) t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
           F' (ret_pc ra) fc' None m' (seg_rom ctasegs)))) Q) ->
  cps ctasegs (ASTA RT Σ PMc (eq
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ASN1_GENERALIZEDTIME_ADJ_A) fc None m (seg_rom ctasegs)))) Q.
Proof.
  intros until ts. intros HEAP ST CEIL LO TOP AL16 MI TP FLEN CRED TSR GA -> Ea1 -> -> K.
  pose proof LO as LO'. unfold GENTIME_ADJ_STACK_A, FROM_TM_STACK_A, ASN1_STRING_SET_STACK, CRYPTO_MALLOC_STACK, RT_STACK in LO'.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
  pose proof TOP as TOPu. unfold USTACK_TOP in TOPu.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (ts_day_range ts) as DR. pose proof (ts_sec_range ts) as SR.
  assert (MC0 : mcost 20 = 0) by reflexivity.
  assert (CRED' : 2 + mcost 20 <= rt_credit RT Σ) by (rewrite MC0; clear - CRED; lia).
  eapply (gtadj_frontA _) with (lo := lo) (OW := OW) (LB := LB);
    [exact HEAP| exact ST| exact CEIL| exact LO| exact TOP| exact AL16| exact MI| exact TP| clear - FLEN; lia| clear - CRED; lia| exact Ea1|].
  intros Σ1 m4 f spa g junk gj qd qt ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F1 fc1
         HEAP4 FRESH GEO Hqt Hqd CR1 LIVE1 ST4 MI4 AG4 LOW HIGH SPA32 SPAL SPAH GSZ SAVJ TM4 PT4.
  pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 2) with 256 in G3, G5. unfold BnHeapA.ACEIL in G3. cbn [ar_SP0 push amb] in G3. unfold SEGTOP_A in G4.
  pose proof CEIL as CEILu. unfold BnHeapA.ACEIL in CEILu.
  assert (F8 : f mod 8 = 0) by (clear - G2; Z.div_mod_to_equations; lia).
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - SPAL SPAH SPR LO' LO0; lia).
  (* [comment removed for export] *)
  assert (FTAIL : forall (Σx : rts RT) (mx : mem) (t0x t1x t2x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x : word) (Fx : bvmap 5 word) (fcx : bv 32),
    @BnHeapA.AHEAP (push AR f 2) Σx OW (gtadj_LB f qd qt LB) mx -> rt_credit RT Σ - 2 <= rt_credit RT Σx -> rt_live RT Σx = rt_live RT Σ ->
    stk ctasegs mx lo spa -> mem_inv ctasegs mx ->
    agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m mx ->
    rw_cells ctasegs mx spa [C8 (Z_to_bv 64 f); CB g junk] -> rw_cells ctasegs mx (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
    cps ctasegs (ASTA RT Σx PMc (eq
       (MS (mkR (Z_to_bv 64 0x270ddc) (Z_to_bv 64 spa) gp (wz TP_A) t0x t1x t2x sp (Z_to_bv 64 spa) (Z_to_bv 64 0) a1x a2x a3x a4x a5x a6x a7x
                 (Z_to_bv 64 f) (Z_to_bv 64 (ts_sec ts)) (Z_to_bv 64 G) (Z_to_bv 64 (ts_day ts)) (Z_to_bv 64 (f + 64)) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 (-8)) s10 s11 t3x t4x t5x t6x)
           Fx (Z_to_bv 64 0x270ddc) fcx None mx (seg_rom ctasegs)))) Q).
  { intros Σx mx t0x t1x t2x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x Fx fcx HEAPx CRx LIVEx STx MIx AGx LOWx HIGHx.
    apply cps_from_evt'. zstep. brc. apply evt_done.
    pose proof HEAPx as HEAPc.
    eapply (@frame_obj_close (push AR f 2)) in HEAPc; [| left; reflexivity| unfold in_fr; cbn [blk_addr blk_size fst snd]; change (fs_size 2) with 256; clear; lia].
    eapply (@frame_obj_close (push AR f 2)) in HEAPc; [| left; reflexivity| unfold in_fr; cbn [blk_addr blk_size fst snd]; change (fs_size 2) with 256; clear; lia].
    change (Z_to_bv 64 0x270df0) with (wz GTADJ_EXIT).
    eapply (@gtadj_epi_cps AR _) with (lo := lo) (LB := LB) (gj := gj) (hrest := []);
      [exact HEAPc| intros b Hb; exact (FRESH b (in_or_app _ _ _ (or_intror Hb)))| exact STx| exact CEIL| clear - LO' SPAL; lia
      | exact TOP| exact SPAL| exact SPAH| exact GSZ| exact SAVJ| exact MIx| exact LOWx| exact HIGHx| reflexivity|].
    intros Σ7 m7 x11 HEAP7 CR7 LIVE7 ST7 MI7 AG7.
    eapply K; [exact HEAP7| rewrite CR7; exact CRx| rewrite LIVE7; exact LIVEx| exact ST7| exact MI7|].
    eapply agree_on_trans; [exact AGx|]. eapply agree_on_mono; [exact AG7|]. intros a Ha.
    destruct Ha as [Ha|[Ha|Ha]]; [left; clear - Ha SPAH; unfold USTACK_TOP in *; lia| right; left; exact Ha| right; right; exact Ha]. }
  (* [comment removed for export] *)
  apply cps_from_evt'.
  zstep.
  destruct (rw_cells_forget _ _ _ _ TM4) as [junk56 TMJ]. cbn [cells_size csize Nat.add tm_cells] in TMJ.
  assert (POSTADJ : forall dv, gentime_adj ts = utc_from_posix (dv * 86400 + ts_sec ts) ->
    forall (Σ5 : rts (@ar_RT (push AR f 2))) (m5 : mem) (t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' : word) (F5 : bvmap 5 word) (fc5 : bv 32),
     @BnHeapA.AHEAP (push AR f 2) Σ5 OW (gtadj_LB f qd qt LB) m5 -> rt_credit RT Σ5 = rt_credit RT Σ1 - 1 -> rt_live RT Σ5 = rt_live RT Σ1 ->
     stk ctasegs m5 lo spa -> mem_inv ctasegs m5 ->
     agree_on (fun a => aclient_addr (OW ++ gtadj_LB f qd qt LB) spa a /\ ~ (f + 64 <= a < f + 64 + 56)) m4 m5 ->
     rw_cells ctasegs m5 (f + 64) (p2tm_cells (dv * 86400 + ts_sec ts)) ->
     cps ctasegs (ASTA RT Σ5 PMc (eq
       (MS (mkR (Z_to_bv 64 0x270ddc) (Z_to_bv 64 spa) gp (wz TP_A) t0'' t1'' t2'' sp (Z_to_bv 64 spa) (Z_to_bv 64 (p2tm_ret (dv * 86400 + ts_sec ts))) a1'' a2'' a3'' a4'' a5'' a6'' a7''
                (Z_to_bv 64 f) (Z_to_bv 64 (ts_sec ts)) (Z_to_bv 64 G) (Z_to_bv 64 (ts_day ts)) (Z_to_bv 64 (f + 64)) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 (-8)) s10 s11 t3'' t4'' t5'' t6'')
           F5 (ret_pc (Z_to_bv 64 0x270ddc)) fc5 None m5 (seg_rom ctasegs)))) Q).
  { intros dv GAd Σ5 m5 t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F5 fc5 HEAP5 CR5 LIVE5 ST5 MI5 AG5 DATA5.
    rewrite (ret_pc_even 0x270ddc) by (clear; lia). unfold p2tm_ret. rewrite <- GAd, GA.
    apply (rw_cells_agree _ _ _ _ _ AG5) in LOW; [| intros xa Hxa; cbn in Hxa; split; [left; unfold USTACK_TOP; clear - Hxa TOPu SPAH GSZ; lia| clear - Hxa G3 CEILu LO' SPAL; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG5) in HIGH; [| intros xa Hxa; cbn in Hxa; split; [left; unfold USTACK_TOP; clear - Hxa TOPu SPAH; lia| clear - Hxa G3 CEILu LO' SPAL SPAH; lia]].
    eapply FTAIL; [exact HEAP5| rewrite CR5; clear - CR1; lia| rewrite LIVE5; exact LIVE1| exact ST5| exact MI5| | exact LOW| exact HIGH].
    eapply agree_on_trans; [exact AG4|]. eapply agree_on_mono; [exact AG5|]. intros a Ha. split.
    - destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [left; clear - Ha SPAH; unfold USTACK_TOP in *; lia| right; left; exact Ha| right; right].
      exists b. split; [| exact Hr]. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb| right; right; right; exact Hb].
    - destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha G3 CEILu LO'; lia| |].
      + destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr G4; lia.
      + pose proof (FRESH b Hb) as O. unfold off_fr in O. change (fs_size 2) with 256 in O. destruct b as [[bq bA] bn]; cbn [blk_addr blk_size fst snd] in Hr, O. clear - Hr O. lia. }
  destruct (Z.eq_dec (ts_day ts) 0) as [D0|DN].
  - zstep. if_cases K1; zify_cond K1; [exfalso; apply K1; rewrite D0; reflexivity|]. try clear K1.
    assert (SN : ts_sec ts <> 0) by (intros S0; unfold gentime_adj in GA; rewrite D0, S0 in GA; cbn in GA; discriminate).
    zstep. if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by (clear - SR; lia); clear - K2 SN; lia|]. try clear K2.
    adj_callA 0 f qd qt HEAP4 ST4 MI4 TM4 CEILu LO' SPAL SPAH TOPu SPA32 FLEN CR1 ESPA CRED' MC0 F8.
    all: try (clear - SR DR; lia).
    { rewrite D0. reflexivity. }
    apply (POSTADJ 0). unfold gentime_adj, SECS_PER_DAY in GA |- *. rewrite D0 in GA |- *.
    replace (ts_sec ts =? 0) with false by (symmetry; apply Z.eqb_neq; exact SN). reflexivity.
  - zstep. if_cases K1; zify_cond K1; [| exfalso; revert K1; clear - DR DN; unfold MallocRep.wz; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; intros K1;
             assert (E64 : 2 ^ Z.of_N 64 = 18446744073709551616) by reflexivity; rewrite E64 in K1; Z.to_euclidean_division_equations; lia]. try clear K1.
    adj_callA (ts_day ts) f qd qt HEAP4 ST4 MI4 TM4 CEILu LO' SPAL SPAH TOPu SPA32 FLEN CR1 ESPA CRED' MC0 F8.
    all: try (clear - SR DR; lia).
    { reflexivity. }
    apply (POSTADJ (ts_day ts)). unfold gentime_adj, SECS_PER_DAY in GA |- *.
    replace (ts_day ts =? 0) with false by (symmetry; apply Z.eqb_neq; exact DN). reflexivity.
Qed.

End WithPFC.

End WithRT.
