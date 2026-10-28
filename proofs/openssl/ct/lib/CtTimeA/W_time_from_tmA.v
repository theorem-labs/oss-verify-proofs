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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac ApRepDefs ApRep W_prefix_create W_strdup W_asn1_stringA W_bio_printf.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Printf_lib Printf_ctfmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeP Require Import TimeDefs TimeKit TimeKit2 TimeFmtPure W_posix_to_tm.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import TimeDefsA TimeKitA W_snprintfA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac rstep := OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
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

Local Notation E_fromtm_set1 := (E_ossl_asn1_time_from_tm_274c58 : uk_call 0x26f848 0x26f928 0x2249e8).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition FROM_TM_STACK_A : Z := 80 + ASN1_STRING_SET_STACK.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Definition gentime_adj_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (G lo : Z) (m : mem) (t : tm6) (cost : Z) (p : bptr) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' D (junk : list byte),
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (wz G) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp)
    /\ apres_but LB OW (bv_unsigned sp) G ASN1_STRING_SIZE m m'
    /\ rt_credit RT Σ - cost <= rt_credit RT Σ'
    /\ ablock_range D 20 /\ AHEAP Σ' ((p, D, 20) :: OW) LB m'
    /\ rw_cells ctasegs m' G (asn1_string_cells 15 V_ASN1_GENERALIZEDTIME D 0)
    /\ rw_cells ctasegs m' D [CB 20%nat (zb (gen15 t) ++ Z_to_bv 8 0 :: junk)] /\ length junk = 4%nat.

Section WithPFC.
Hypothesis PFC : printf_contracts RT.

Lemma ossl_asn1_time_from_tm_walkA : forall {X : Type}
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z)
    (gb pt : bptr) (G TS : Z) (t : tm6) (ras : list Z)
    (k : option bptr -> aprog bptr X) (Q : X -> rts RT -> machine_state -> Prop),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - FROM_TM_STACK_A ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> crypto_statics m -> realloc_statics m ->
  In (gb, G, ASN1_STRING_SIZE) OW -> rw_cells ctasegs m G (asn1_string_cells 0 V_ASN1_GENERALIZEDTIME 0 0) ->
  In (pt, TS, 56) (OW ++ LB) -> TS mod 8 = 0 -> ro_cells ctasegs m TS (tm_cells t) -> tm_valid t -> (TS + 56 <= G \/ G + ASN1_STRING_SIZE <= TS) ->
  a0 = wz G -> a1 = wz TS -> a2 = wz V_ASN1_GENERALIZEDTIME ->
  mcost 20 <= rt_credit RT Σ ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx OSSL_ASN1_TIME_FROM_TM_A (bv_unsigned ra :: ras) ->
  (forall p Σ' ms', ~ In p (map blk_id (OW ++ LB)) ->
     gentime_adj_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB G lo m t (mcost 20) p Σ' ms' ->
     implAp (k (Some p)) Σ' Q ms') ->
  implAp (AMalloc 20 k) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz OSSL_ASN1_TIME_FROM_TM_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until Q. intros HEAP ST CEIL LO SPT SP16 MI -> CS RS HGIN HG HTIN ALT HTM TV DJT -> -> -> CRED UW CTX K.
  pose proof LO as LO'. unfold FROM_TM_STACK_A, ASN1_STRING_SET_STACK, CRYPTO_MALLOC_STACK, RT_STACK in LO'.
  unfold OSSL_ASN1_TIME_FROM_TM_A, V_ASN1_GENERALIZEDTIME, ASN1_STRING_SIZE, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3. unfold USTACK_TOP in SPT.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (HGIN' : In (gb, G, 24) (OW ++ LB)) by (apply in_or_app; left; exact HGIN).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HGIN') as (BG0 & _ & _ & BGC & BGI). cbn [blk_addr blk_size fst snd] in BG0, BGC, BGI.
  pose proof (AH_range _ _ _ _ _ _ _ HEAP HGIN) as BRG.      (* [comment removed for export] *)
  pose proof (AH_range_gen _ _ _ _ _ HEAP HTIN) as (BT0 & _ & _ & BTC & BTI). cbn [blk_addr blk_size fst snd] in BT0, BTC, BTI.
  pose proof TV as (VY & VMO & VMD & VHH & VMI & VSS). pose proof (days_in_month_le31 (t_year t) (t_mon t)) as DM.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; clear - SPR LO' LO0; lia).
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFFW : offshW [(bv_unsigned sp - 80, bv_unsigned sp)]%Z) by (cbn [offshW]; alia).
  assert (SEPG0 : G + 24 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= G) by (clear - BGC CEIL LO'; alia).
  assert (SEPT0 : TS + 56 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= TS) by (clear - BTC CEIL LO'; alia).
  pose proof HTM as HTMc. unfold tm_cells in HTM. unfold asn1_string_cells, MallocRep.wz in HG.
  apply implAp_from_evt.
  (* [comment removed for export] *)
  carve_frame 80%nat ST. do 10 step. do 2 step. step. step.      (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0; [| exfalso; apply K0; reflexivity]. try clear K0.
  (* [comment removed for export] *)
  step. step. step.
  step. if_cases K1; zify_cond K1; [| exfalso; rewrite ?unsigned_lit in K1 by (clear - BG0 BGC C3; alia); clear - K1 BG0; lia]. try clear K1.
  do 4 step.
  name_mem m1.
  match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs m m1 |- _ => rename H into WM1 end.
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply AH_frame; [exact HEAP| exact MU1| exact WM1|]. constructor; [left; cbn; alia | constructor]. }
  assert (AGL1 : agree_on (lib_addr OW) m m1).
  { eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU1)|]. intros a Ha. cbn. split; [| exact I].
    destruct Ha as [Ha|(b & Hb & Hr)]; [revert Ha; unfold LIBW_S; cbn [rin_ivs fst snd]; clear - C1 CEIL LO'; unfold BnHeapA.ACEIL in *; lia|].
    pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_introl Hb))) as (_ & _ & _ & BC & _). clear - Hr BC CEIL LO'. unfold BnHeapA.ACEIL in *. lia. }
  assert (CS1 : crypto_statics m1) by (exact (crypto_statics_agree' OW m m1 CS AGL1)).
  assert (RS1 : realloc_statics m1) by (exact (realloc_statics_agree OW m m1 RS AGL1)).
  apply evt_done.
  eapply (ASN1_STRING_set1_data_nosrc_walkA) with (n := 20) (lo := lo) (OW := OW) (LB := LB) (pblk := gb) (ty := 24) (ras := bv_unsigned ra :: ras); try reflexivity.
  - exact HEAP1.
  - rewrite ESP. exact ST.
  - exact CEIL.
  - rewrite ESP. unfold ASN1_STRING_SET_STACK, CRYPTO_MALLOC_STACK, RT_STACK. clear - LO'; lia.
  - rewrite ESP. clear - SPT LO' LO0; unfold USTACK_TOP; lia.
  - rewrite ESP. uchk_open. clear - SP16 SPR. Z.div_mod_to_equations. lia.
  - exact MI.
  - exact CS1.
  - exact RS1.
  - exact HGIN.
  - unfold asn1_string_cells, MallocRep.wz. exact HG.
  - clear; lia.
  - clear; lia.
  - clear; lia.
  - exact CRED.
  - rewrite ESP. uw_call_mu_tac m 80 UW MU1 FR; [intros a Ha; cbn [outside fst snd]; lia | lia | uchk_open; clear - SP16 SPR; Z.div_mod_to_equations; lia | unfold USTACK_TOP in *; lia].
  - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_fromtm_set1 CTX).
  - intros p Σ' ms' Hp PO. unfold oalloc_postA in PO. rewrite ?ESP in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & m2 & C & -> & MI2 & ST2 & AP2 & CR2 & BR2 & HEAP2 & ACC2 & ((junkC & BLK) & HG2)).
    unfold MallocRep.wz, ASN1_STRING_SIZE in *.
    rewrite (ret_pc_even 0x26f928) by (clear; lia).
    pose proof BR2 as (C0 & C16 & _ & CCE & CIMG).
    assert (EC : bv_unsigned (Z_to_bv 64 C) = C) by (apply unsigned_lit; clear - C0 CCE C3; alia).
    assert (HCIN : In (p, C, 20) (((p, C, 20) :: OW) ++ LB)) by (left; reflexivity).
    assert (HGIN2 : In (gb, G, 24) (((p, C, 20) :: OW) ++ LB)) by (right; exact HGIN').
    assert (HTIN2 : In (pt, TS, 56) (((p, C, 20) :: OW) ++ LB)) by (cbn [app]; right; exact HTIN).
    assert (NEC : p <> gb) by (intros E; apply Hp; rewrite E; apply in_map_iff; exists (gb, G, 24); split; [reflexivity| exact HGIN']).
    assert (NET : p <> pt) by (intros E; apply Hp; rewrite E; apply in_map_iff; exists (pt, TS, 56); split; [reflexivity| exact HTIN]).
    pose proof (AH_disjoint_gen _ _ _ _ (gb, G, 24) (p, C, 20) HEAP2 HGIN2 HCIN ltac:(cbn; exact (fun E => NEC (eq_sym E)))) as DJC. cbn in DJC.
    pose proof (AH_disjoint_gen _ _ _ _ (pt, TS, 56) (p, C, 20) HEAP2 HTIN2 HCIN ltac:(cbn; exact (fun E => NET (eq_sym E)))) as DJT2. cbn in DJT2.
    pose proof (AH_offsh _ _ _ _ (p, C, 20) HEAP2 HCIN) as OSHC. cbn [blk_addr blk_size fst snd] in OSHC.
    (* [comment removed for export] *)
    apply (rw_cells_agree _ _ _ _ _ AP2) in FR; [| intros a Ha; cbn in Ha; split; [left; unfold USTACK_TOP; clear - Ha SPT; lia| clear - Ha BGC CEIL LO'; alia]].
    apply (ro_cells_agree _ _ _ _ _ AP2) in HTM; [| intros a Ha; cbn in Ha; split; [right; right; exists (pt, TS, 56); split; [exact HTIN| cbn; clear - Ha; lia]| clear - Ha DJT; lia]].
    clear ST MI CS1 RS1 HEAP1 AGL1 HG. try clear HTMc.
    assert (JL : length junkC = 20%nat) by (destruct BLK as [[[WF _] _] _]; exact WF).
    ablock HEAP2 HGIN2 ACCG OFFG. ablock HEAP2 HTIN2 ACCT OFFT.
    destruct (AH_shb _ _ _ _ HEAP2) as [SHB1 SHB2].
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (G, G + 24); (C, C + 20)]%Z m2) as MU2. pose proof (wmono_refl ctasegs m2) as WM2.
    assert (OFF2 : offshW [(bv_unsigned sp - 80, bv_unsigned sp); (G, G + 24); (C, C + 20)]%Z) by (cbn [offshW]; clear - C1 C2 C3 CEIL LO' SPT OSHC OFFG; alia).
    assert (AWO : Forall (aclient_write_ok (((p, C, 20) :: OW) ++ LB)) [(bv_unsigned sp - 80, bv_unsigned sp); (G, G + 24); (C, C + 20)]%Z).
    { constructor; [left; cbn; clear - CEIL LO' SPT; alia|].
      constructor; [right; right; exists (gb, G, 24); split; [exact HGIN2| cbn; clear; lia]|].
      constructor; [right; right; exists (p, C, 20); split; [exact HCIN| cbn; clear; lia]| constructor]. }
    assert (SEPG : G + 24 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= G) by (clear - BGC CEIL LO'; alia).
    assert (SEPC : C + 20 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= C) by (clear - CCE CEIL LO'; alia).
    assert (SEPT : TS + 56 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= TS) by (clear - BTC CEIL LO'; alia).
    unfold asn1_string_cells, MallocRep.wz in HG2. change (Z.to_nat 20) with 20%nat in BLK.
    apply implAp_from_evt.
    (* [comment removed for export] *)
    step. brc.
    step.
    step. step. step. ab_shload 4.
    step. step. brc.
    (* [comment removed for export] *)
    step. rewrite (sx32_small (t_mon t - 1)) by (clear - VMO; lia).
    step. step.
    step. if_cases K3; zify_cond K3; [exfalso; rewrite ?unsigned_lit in K3 by (clear - VMO; lia); clear - K3 VMO; lia|]. try clear K3.
    (* [comment removed for export] *)
    step. rewrite (sx32_signed (t_year t - 1900)) by (clear - VY; lia).
    step. brc.
    step. step. step. brF ltsz.
    (* [comment removed for export] *)
    step. step. step. ab_shload 4.
    step. rewrite (sx32_small (t_mday t)) by (clear - VMD DM; lia). step. brc.
    step. step. step. ab_shload 4.
    step. rewrite (sx32_small (t_hour t)) by (clear - VHH; lia). step. brc.
    step. step. ab_shload 4.
    step. rewrite (sx32_small (t_min t)) by (clear - VMI; lia). step. brc.
    step. rewrite (sx32_small (t_sec t)) by (clear - VSS; lia).
    (* [comment removed for export] *)
    step. setreg 13%Z (Z_to_bv 64 (t_year t)) ltac:(f_equal; rewrite addiw_small by (clear - VY; lia); clear - VY; lia).
    step. setreg 14%Z (Z_to_bv 64 (t_mon t)) ltac:(f_equal; rewrite addiw_small by (clear - VMO; lia); clear - VMO; lia).
    step. step. step.
    step. step. step.
    name_mem m3.
    match goal with H : munch _ m2 m3 |- _ => rename H into MU3 end. match goal with H : wmono ctasegs m2 m3 |- _ => rename H into WM3 end.
    match goal with H : mem_inv ctasegs m3 |- _ => rename H into MI3 end. match goal with H : stk ctasegs m3 lo _ |- _ => rename H into ST3 end.
    assert (HEAP3 : AHEAP Σ' ((p, C, 20) :: OW) LB m3) by (eapply AH_frame; [exact HEAP2| exact MU3| exact WM3| exact AWO]).
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?rest) =>
      pose proof (proj1 (rw_cells_app m3 _ [c0] rest) FR) as [HST FRH] end.
    cbn [cells_size csize Nat.add] in FRH.
    apply evt_done. eapply implAp_step_same.
    { eapply (snprintf_ints_cpsA PFC) with (D := C) (nD := 20) (A := A_C17_A) (bd := (p, C, 20)) (lo := lo) (OW := (p, C, 20) :: OW) (LB := LB)
        (fmt := FMT_C17) (stkw := [Z_to_bv 64 (t_sec t)]) (ints := [t_year t; t_mon t; t_mday t; t_hour t; t_min t; t_sec t]) (o := gen15 t);
        rewrite ?ESP; try reflexivity.
      - exact HEAP3.
      - exact ST3.
      - exact CEIL.
      - unfold RT_STACK. clear - LO'. lia.
      - change (zlength [Z_to_bv 64 (t_sec t)]) with 1. unfold USTACK_TOP. clear - SPT LO' LO0. lia.
      - uchk_open. clear - SP16 SPR. Z.div_mod_to_equations. lia.
      - exact MI3.
      - exact HCIN.
      - exact (vfmtA_C17 t TV).
      - rewrite gen15_zlength. clear; lia.
      - clear; lia.
      - destruct HST as [[_ HB] _]. exact HB.
      - cbn [int_slots_ok app]. rewrite !unsigned_lit by (clear - VY VMO VMD DM VHH VMI VSS; lia).
        rewrite !(Z.mod_small _ (2^32)) by (clear - VY VMO VMD DM VHH VMI VSS; lia). clear - VY VMO VMD DM VHH VMI VSS. repeat split; lia. }
    intros msS PS. unfold snp_postA in PS. rewrite ?ESP in PS.
    destruct PS as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F4 & fc4 & m4 & -> & MI4 & ST4 & HEAP4 & WM4 & AG4 & BZ4).
    rewrite (ret_pc_even 0x26fab0) by (clear; lia). unfold MallocRep.wz. rewrite gen15_zlength. rewrite gen15_zlength in AG4.
    (* [comment removed for export] *)
    apply (rw_cells_agree _ _ _ _ _ AG4) in HST; [| intros a Ha; cbn in Ha; split; [left; unfold USTACK_TOP; clear - Ha SPT; lia| clear - Ha SEPC; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG4) in FRH; [| intros a Ha; cbn in Ha; split; [left; unfold USTACK_TOP; clear - Ha SPT; lia| clear - Ha SEPC; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG4) in HG2; [| intros a Ha; cbn in Ha; split; [right; right; exists (gb, G, 24); split; [exact HGIN2| cbn; clear - Ha; lia]| clear - Ha DJC; lia]].
    apply (rw_cells_split_CB ctasegs m3 C [] 20 junkC [] [16; 4]%nat) in BLK; [| reflexivity]. cbn [mk_CB_cells app] in BLK.
    destruct (proj1 (rw_cells_app m3 C [_] _) BLK) as [_ BLKT]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in BLKT.
    rewrite firstn_all2 in BLKT by (rewrite length_skipn, JL; clear; lia).
    apply (rw_cells_agree _ _ _ _ _ AG4) in BLKT; [| intros a Ha; cbn in Ha; split; [right; right; exists (p, C, 20); split; [exact HCIN| cbn; clear - Ha; lia]| clear - Ha; lia]].
    assert (BLK4 : rw_cells ctasegs m4 C [CB 20%nat (zb (gen15 t) ++ Z_to_bv 8 0 :: skipn 16 junkC)]).
    { pose proof (rw_cells_of_bytes m4 C _ BZ4) as H16.
      assert (L16 : length (zb (gen15 t) ++ [Z_to_bv 8 0]) = 16%nat) by (rewrite length_app; unfold zb; rewrite length_map, gen15_length; reflexivity).
      rewrite L16 in H16. specialize (H16 ltac:(destruct (proj1 (AH_acc _ _ _ _ (p, C, 20) HEAP4 HCIN)) as (W1 & W2 & W3); cbn [blk_addr blk_size fst snd] in W1, W2, W3; split; [clear - W1; lia| split; [clear - W2; lia| intros i Hi; apply W3; clear - Hi; lia]])).
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in BLKT.
      pose proof (proj2 (rw_cells_app m4 C [CB 16%nat (FX_lib.zb (gen15 t) ++ [Z_to_bv 8 0])] [CB 4%nat (skipn 16 junkC)]) (conj H16 BLKT)) as H20.
      pose proof (rw_cells_merge ctasegs m4 C [] [CB 16%nat (FX_lib.zb (gen15 t) ++ [Z_to_bv 8 0]); CB 4%nat (skipn 16 junkC)] [] H20) as H20'.
      cbn [app cells_size csize cells_bytes cbytes Nat.add] in H20'. rewrite app_nil_r, <- app_assoc in H20'. cbn [app] in H20'. exact H20'. }
    clear BLK BLKT BZ4.
    clear ACCG OFFG ACCT OFFT SHB1 SHB2.
    ablock HEAP4 HGIN2 ACCG OFFG.
    destruct (AH_shb _ _ _ _ HEAP4) as [SHB1 SHB2].
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (G, G + 24); (C, C + 20)]%Z m4) as MU4'. pose proof (wmono_refl ctasegs m4) as WM4'.
    apply implAp_from_evt.
    (* [comment removed for export] *)
    step. step. brc.
    step. step. step.
    replace (bv_unsigned sp + -80 + 8) with (bv_unsigned sp + -80 + Z.of_nat (cells_size [C8 (Z_to_bv 64 (t_sec t))])) in FRH by (cbn; clear; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (proj2 (rw_cells_app mx _ [C8 (Z_to_bv 64 (t_sec t))] _) (conj HST FRH)) as FR' end.
    clear HST FRH. cbn [app] in FR'.
    do 8 step. step. release_frame FR' ST4 (bv_unsigned sp). step.      (* [comment removed for export] *)
    name_mem m5.
    match goal with H : munch _ m4 m5 |- _ => rename H into MU5 end. match goal with H : wmono ctasegs m4 m5 |- _ => rename H into WM5 end.
    apply evt_done. apply (K p Σ' _ Hp).
    unfold gentime_adj_postA, MallocRep.wz.
    assert (HEAP5 : AHEAP Σ' ((p, C, 20) :: OW) LB m5) by (eapply AH_frame; [exact HEAP4| exact MU5| exact WM5| exact AWO]).
    do 16 eexists. exists m5, C, (skipn 16 junkC). split; [reflexivity|].
    split; [assumption|]. split; [assumption|].
    split.
    { (* [comment removed for export] *)
      unfold apres_but.
      assert (MW : forall ma mb, munch [(bv_unsigned sp - 80, bv_unsigned sp); (G, G + 24); (C, C + 20)]%Z ma mb ->
                   agree_on (fun a => aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ ~ (G <= a < G + 24)) ma mb).
      { intros ma mb MUx. eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MUx)|]. intros a [Ha Hn]. cbn [outside fst snd].
        split; [| split; [clear - Hn; lia| split; [| exact I]]].
        - destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha; lia| |].
          + destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr C1 CEIL LO'; alia.
          + pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & B3' & _). clear - Hr B3' CEIL LO'; alia.
        - destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha CCE CEIL LO'; alia| |].
          + intros HC. eapply (blk_not_static _ ((p, C, 20) :: OW) LB m2 (p, C, 20) a HEAP2 (or_introl eq_refl)); [cbn; clear - HC; lia | exact Ha].
          + assert (NE : blk_id b <> p) by (intros E; apply Hp; rewrite <- E; apply in_map; exact Hb).
            pose proof (AH_disjoint_gen _ _ _ _ b (p, C, 20) HEAP2 (or_intror Hb) HCIN NE) as DJ. cbn in DJ. clear - Hr DJ. lia. }
      eapply agree_on_trans.
      { eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU1)|]. intros a [Ha Hn]. cbn [outside fst snd]. split; [| exact I].
        destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha; lia| |].
        + destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr C1 CEIL LO'; alia.
        + pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & B3' & _). clear - Hr B3' CEIL LO'; alia. }
      eapply agree_on_trans; [eapply agree_on_mono; [exact AP2| intros a [Ha Hn]; split; [| exact Hn]; destruct Ha as [Ha|[Ha|Ha]]; [left; clear - Ha; lia| right; left; exact Ha| right; right; exact Ha]]|].
      eapply agree_on_trans; [exact (MW _ _ MU3)|].
      eapply agree_on_trans.
      { eapply agree_on_mono; [exact AG4|]. intros a [Ha Hn]. split.
        - destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [left; clear - Ha; lia| right; left; exact Ha| right; right; exists b; split; [cbn [app]; right; exact Hb| exact Hr]].
        - destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha CCE CEIL LO'; alia| |].
          + intros HC. eapply (blk_not_static _ ((p, C, 20) :: OW) LB m2 (p, C, 20) a HEAP2 (or_introl eq_refl)); [cbn; clear - HC; lia | exact Ha].
          + assert (NE : blk_id b <> p) by (intros E; apply Hp; rewrite <- E; apply in_map; exact Hb).
            pose proof (AH_disjoint_gen _ _ _ _ b (p, C, 20) HEAP2 (or_intror Hb) HCIN NE) as DJ. cbn in DJ. clear - Hr DJ. lia. }
      exact (MW _ _ MU5). }
    split; [exact CR2|]. split; [exact BR2|]. split; [exact HEAP5|].
    split; [unfold asn1_string_cells, MallocRep.wz; assumption|].
    split; [| rewrite length_skipn, JL; reflexivity].
    match goal with H : rw_cells ctasegs m5 C _ |- _ => exact H end.
Qed.
End WithPFC.
End WithRT.
