(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel Target Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_h_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Definition SJ_DOC_DTOR : Z := 0x40520.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition docdtor_R (LB : list block) (q DOC : Z) (dcap : word) (m : mem) : word -> PState -> mem -> Prop :=
  fun _ s' m' => RHEAP s' LB m' /\ lx_pres LB q [(DOC, DOC + 16)] m m'
                 /\ rw_cells usegs m' DOC [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 dcap].

Section Proofs.
  Hypothesis HF : rfree_stmt.

  Lemma docdtor_cps : forall {A} (k : M PState A) (Q : A -> PState -> machine_state -> Prop)
      (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (q lo B : Z) (errv : word)
      (DOC TAPE SBUF ntp nsb : Z) (psb ptp : bptr) (dcap : word),
    RHEAP s ((psb, SBUF, nsb) :: (ptp, TAPE, ntp) :: LB) m -> rauxv_ok m B -> q <= B ->
    stk usegs m lo q -> alloc_ceiling <= lo -> lo <= q - (16 + RFREE_STACK) ->
    rw_cells usegs m LX_ERRNO [C4 errv] -> mem_inv usegs m -> 0 <= q < 2^64 ->
    q <= DOC -> DOC + 24 <= B ->
    rw_cells usegs m DOC [C8 (Z_to_bv 64 TAPE); C8 (Z_to_bv 64 SBUF); C8 dcap] ->
    (forall s' ms', hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s lo B (docdtor_R LB q DOC dcap m) s' ms' ->
                    implM usegs k s' Q ms') ->
    implM usegs (mbind (del lops psb) (fun _ => mbind (del lops ptp) (fun _ => k))) s Q
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 DOC) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SJ_DOC_DTOR) fc None m (seg_rom usegs)).
  Proof.
    intros A k Q. intros until dcap. intros HEAP AUX QB ST CEIL LO ERR MI Hq QD DB DOCC HK.
    unfold SJ_DOC_DTOR, RFREE_STACK in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    pose proof (LH_block_range _ _ _ _ HEAP ltac:(left; reflexivity)) as BR1. cbn [blk_addr blk_size fst snd] in BR1.
    pose proof (LH_block_range _ _ _ _ HEAP ltac:(right; left; reflexivity)) as BR2. cbn [blk_addr blk_size fst snd] in BR2.
    pose proof (munch_refl [(q - 16, q); (DOC, DOC + 16)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (ELX : LX_ERRNO = 977220) by reflexivity. rewrite ELX in ERR.
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client LB q [(DOC, DOC + 16)] a -> outside [(q - 16, q); (DOC, DOC + 16)] a).
    { intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [|split; [lia| exact I]].
      destruct HC as [HC|[(b & Hb & Hr)|HC]]; [lia| | lia].
      pose proof (LH_block_range _ _ _ _ HEAP ltac:(right; right; exact Hb)) as (_ & _ & _ & BC & _).
      unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in BC. lia. }
    unfold implM. iprefix.
    step. carve_frame 16%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 16 junk [] [8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    step. step. step. step. hstep. step.
    destruct BR1 as (SB0 & _ & SBn & SBC & _). destruct BR2 as (TP0 & _ & TPn & TPC & _).
    if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|]. clear K1.

    step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HEAP1 : RHEAP s ((psb, SBUF, nsb) :: (ptp, TAPE, ntp) :: LB) m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|].
      constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
      constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (ND : List.NoDup (map blk_id ((psb, SBUF, nsb) :: (ptp, TAPE, ntp) :: LB))) by (eapply LH_nodup; exact HEAP).
    ihere. to_implM. eapply implM_bind.
    { eapply (opdel_arr_proof HF) with (B := B) (lo := lo) (A := SBUF) (n := nsb);
        [exact HEAP1| left; reflexivity| exact AUX1| lia| exact ST| exact CEIL'| unfold RFREE_STACK; lia| rewrite ELX; exact ERR| exact MI| lia]. }
    cbv beta. intros [] s1' ms1 PO. unfold free_postZ in PO.
    destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3
                    & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA & SO & HEAP3).
    rewrite (lb_remove_hd _ _ _ _ ND) in HP, HEAP3.
    replace (ret_pc (Z_to_bv 64 0x40540)) with (Z_to_bv 64 0x40540) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in DOCC; [| intros a Ha; left; cbn in Ha; lia].
    assert (PRES3 : lx_pres LB q [(DOC, DOC + 16)] m m3).
    { eapply lx_pres_trans; [eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]|].
      apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP| lia| intros b Hb; right; exact Hb]. }
    clear MU WM HEAP1 AUX1 HP.
    pose proof (munch_refl [(q - 16, q); (DOC, DOC + 16)]%Z m3) as MU. pose proof (wmono_refl usegs m3) as WM.
    assert (ND3 : List.NoDup (map blk_id ((ptp, TAPE, ntp) :: LB))) by (eapply LH_nodup; exact HEAP3).
    rewrite ELX in ERR3.
    unfold implM. iprefix.

    step. hstep. step.
    if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by lia; lia|]. clear K2.
    step. step. step. release_frame FR ST3 q. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    assert (HEAP4 : RHEAP s1' ((ptp, TAPE, ntp) :: LB) m4).
    { eapply LH_frame; [exact HEAP3| exact MU| exact WM|].
      constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX4 : rauxv_ok m4 B).
    { eapply rauxv_ok_frame; [exact AUX3| exact MU| exact WM|].
      constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    ihere. to_implM. eapply implM_bind.
    { eapply (opdel_arr_proof HF) with (B := B) (lo := lo) (A := TAPE) (n := ntp);
        [exact HEAP4| left; reflexivity| exact AUX4| lia| exact ST3| exact CEIL'| unfold RFREE_STACK; lia| rewrite ELX; exact ERR3| exact MI3| lia]. }
    cbv beta. intros [] s2' ms2 PO. unfold free_postZ in PO.
    destruct PO as (u5 & u6 & u7 & u10 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m5
                    & -> & MI5 & ST5 & ERR5 & AUX5 & HP5 & FA5 & SO5 & HEAP5).
    rewrite (lb_remove_hd _ _ _ _ ND3) in HP5, HEAP5.
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP5)) in DOCC; [| intros a Ha; left; cbn in Ha; lia].
    apply HK. unfold hpost. do 15 eexists. exists m5.
    split; [reflexivity|]. split; [exact MI5|]. split; [exact ST5|]. split; [exists errv; exact ERR5|]. split; [exact AUX5|].
    split; [congruence|]. split; [congruence|].
    unfold docdtor_R. split; [exact HEAP5|]. split; [| exact DOCC].
    eapply lx_pres_trans; [exact PRES3|].
    eapply lx_pres_trans; [eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]|].
    apply lx_pres_of_heap_pres. exact HP5.
  Qed.

  Lemma dpidtor_cps : forall {A} (k : M PState A) (Q : A -> PState -> machine_state -> Prop)
      (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (q lo B : Z) (errv : word)
      (THIS IDX OC IA nix noc nia : Z) (pim pix poc pia : bptr)
      (vptr nsi nxt cap md bufv lenv docv : word) (b48 b49 : byte) (p12 p28 p50 : list byte),
    RHEAP s ((pia, IA, nia) :: (poc, OC, noc) :: (pix, IDX, nix) :: (pim, THIS, 96) :: LB) m -> rauxv_ok m B -> q <= B ->
    stk usegs m lo q -> alloc_ceiling <= lo -> lo <= q - (16 + RFREE_STACK) ->
    rw_cells usegs m LX_ERRNO [C4 errv] -> mem_inv usegs m -> 0 <= q < 2^64 ->
    rw_cells usegs m THIS (impl_cells16 vptr nsi p12 (Z_to_bv 64 IDX) nxt p28 cap md b48 b49 p50 (Z_to_bv 64 OC) (Z_to_bv 64 IA) bufv lenv docv) ->
    (forall s' ms', hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s lo B
                          (fun _ s' m' => RHEAP s' LB m' /\ lx_pres LB q [] m m') s' ms' ->
                    implM usegs k s' Q ms') ->
    implM usegs (mbind (del lops pia) (fun _ => mbind (del lops poc) (fun _ => mbind (del lops pix) (fun _ => mbind (del lops pim) (fun _ => k))))) s Q
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 THIS) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SJ_DPI_DTOR_DEL) fc None m (seg_rom usegs)).
  Proof.
    intros A k Q. intros until p50. intros HEAP AUX QB ST CEIL LO ERR MI Hq THISC HK.
    unfold SJ_DPI_DTOR_DEL, RFREE_STACK, impl_cells16 in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    pose proof (LH_block_range _ _ _ _ HEAP ltac:(left; reflexivity)) as (IA0 & _ & IAn & IAC & _).
    pose proof (LH_block_range _ _ _ _ HEAP ltac:(right; left; reflexivity)) as (OC0 & _ & OCn & OCC & _).
    pose proof (LH_block_range _ _ _ _ HEAP ltac:(right; right; left; reflexivity)) as (IX0 & _ & IXn & IXC & _).
    pose proof (LH_block_range _ _ _ _ HEAP ltac:(right; right; right; left; reflexivity)) as (TH0 & _ & _ & THC & THS).
    cbn [blk_addr blk_size fst snd] in *. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in *.
    pose proof (LH_head_disj _ _ _ _ _ _ (RHEAP_pull s [(pia, IA, nia); (poc, OC, noc); (pix, IDX, nix)] (pim, THIS, 96) LB m HEAP)) as DJ.
    pose proof (munch_refl [(q - 16, q); (THIS, THIS + 96)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (ELX : LX_ERRNO = 977220) by reflexivity. rewrite ELX in ERR.
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client LB q [] a -> outside [(q - 16, q); (THIS, THIS + 96)] a).
    { intros a Ha [_ HC]. cbn [outside]. split; [|split; [| exact I]].
      - destruct HC as [HC|[(b & Hb & Hr)|HC]]; [lia| | lia].
        pose proof (LH_block_range _ _ _ _ HEAP ltac:(right; right; right; right; exact Hb)) as (_ & _ & _ & BC & _).
        unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in BC. lia.
      - destruct HC as [HC|[HC|HC]]; [lia| | lia].
        apply DJ. cbn [app]. eapply in_block_incl; [| exact HC]. intros b Hb. right; right; right; exact Hb. }
    unfold implM. iprefix.
    step. carve_frame 16%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 16 junk [] [8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.

    step. step. step. step. hstep. step.
    if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|]. clear K1.
    step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HEAP1 : RHEAP s ((pia, IA, nia) :: (poc, OC, noc) :: (pix, IDX, nix) :: (pim, THIS, 96) :: LB) m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|].
      constructor; [apply W_ok_stack; cbn; lia|].
      constructor; [eapply (W_ok_block _ (pim, THIS, 96)); [right; right; right; left; reflexivity| cbn; lia| cbn; lia]| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
      constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (ND : List.NoDup (map blk_id ((pia, IA, nia) :: (poc, OC, noc) :: (pix, IDX, nix) :: (pim, THIS, 96) :: LB))) by (eapply LH_nodup; exact HEAP).
    ihere. to_implM. eapply implM_bind.
    { eapply (opdel_arr_proof HF) with (B := B) (lo := lo) (A := IA) (n := nia);
        [exact HEAP1| left; reflexivity| exact AUX1| lia| exact ST| exact CEIL'| unfold RFREE_STACK; lia| rewrite ELX; exact ERR| exact MI| lia]. }
    cbv beta. intros [] s1' ms1 PO. unfold free_postZ in PO.
    destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3
                    & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA & SO & HEAP3).
    rewrite (lb_remove_hd _ _ _ _ ND) in HP, HEAP3.
    replace (ret_pc (Z_to_bv 64 0x5b1e4)) with (Z_to_bv 64 0x5b1e4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in THISC;
      [| intros a Ha; right; right; exists (pim, THIS, 96); split; [right; right; left; reflexivity| cbn in Ha |- *; lia]].
    assert (PRES3 : lx_pres LB q [] m m3).
    { eapply lx_pres_trans; [eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]|].
      apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP| lia| intros b Hb; right; right; right; exact Hb]. }
    clear MU WM HEAP1 AUX1 HP ND.
    pose proof (munch_refl [(q - 16, q); (THIS, THIS + 96)]%Z m3) as MU. pose proof (wmono_refl usegs m3) as WM.
    rewrite ELX in ERR3.
    unfold implM. iprefix.

    step. hstep. step.
    if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by lia; lia|]. clear K2.
    step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    assert (HEAP4 : RHEAP s1' ((poc, OC, noc) :: (pix, IDX, nix) :: (pim, THIS, 96) :: LB) m4).
    { eapply LH_frame; [exact HEAP3| exact MU| exact WM|].
      constructor; [apply W_ok_stack; cbn; lia|].
      constructor; [eapply (W_ok_block _ (pim, THIS, 96)); [right; right; left; reflexivity| cbn; lia| cbn; lia]| constructor]. }
    assert (AUX4 : rauxv_ok m4 B).
    { eapply rauxv_ok_frame; [exact AUX3| exact MU| exact WM|].
      constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (ND4 : List.NoDup (map blk_id ((poc, OC, noc) :: (pix, IDX, nix) :: (pim, THIS, 96) :: LB))) by (eapply LH_nodup; exact HEAP3).
    ihere. to_implM. eapply implM_bind.
    { eapply (opdel_arr_proof HF) with (B := B) (lo := lo) (A := OC) (n := noc);
        [exact HEAP4| left; reflexivity| exact AUX4| lia| exact ST3| exact CEIL'| unfold RFREE_STACK; lia| rewrite ELX; exact ERR3| exact MI3| lia]. }
    cbv beta. intros [] s2' ms2 PO. unfold free_postZ in PO.
    destruct PO as (u5 & u6 & u7 & u10 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m5
                    & -> & MI5 & ST5 & ERR5 & AUX5 & HP5 & FA5 & SO5 & HEAP5).
    rewrite (lb_remove_hd _ _ _ _ ND4) in HP5, HEAP5.
    replace (ret_pc (Z_to_bv 64 0x5b1f4)) with (Z_to_bv 64 0x5b1f4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP5)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP5)) in THISC;
      [| intros a Ha; right; right; exists (pim, THIS, 96); split; [right; left; reflexivity| cbn in Ha |- *; lia]].
    assert (PRES5 : lx_pres LB q [] m m5).
    { eapply lx_pres_trans; [exact PRES3|].
      eapply lx_pres_trans; [eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]|].
      apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP5| lia| intros b Hb; right; right; exact Hb]. }
    clear MU WM HEAP4 AUX4 HP5 ND4 PRES3.
    pose proof (munch_refl [(q - 16, q); (THIS, THIS + 96)]%Z m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    rewrite ELX in ERR5.
    unfold implM. iprefix.

    step. step. step. hstep. hstep. step.
    if_cases K3; zify_cond K3; [exfalso; rewrite ?unsigned_lit in K3 by lia; lia|]. clear K3.
    step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    assert (HEAP6 : RHEAP s2' ((pix, IDX, nix) :: (pim, THIS, 96) :: LB) m6).
    { eapply LH_frame; [exact HEAP5| exact MU| exact WM|].
      constructor; [apply W_ok_stack; cbn; lia|].
      constructor; [eapply (W_ok_block _ (pim, THIS, 96)); [right; left; reflexivity| cbn; lia| cbn; lia]| constructor]. }
    assert (AUX6 : rauxv_ok m6 B).
    { eapply rauxv_ok_frame; [exact AUX5| exact MU| exact WM|].
      constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (ND6 : List.NoDup (map blk_id ((pix, IDX, nix) :: (pim, THIS, 96) :: LB))) by (eapply LH_nodup; exact HEAP5).
    ihere. to_implM. eapply implM_bind.
    { eapply (opdel_arr_proof HF) with (B := B) (lo := lo) (A := IDX) (n := nix);
        [exact HEAP6| left; reflexivity| exact AUX6| lia| exact ST5| exact CEIL'| unfold RFREE_STACK; lia| rewrite ELX; exact ERR5| exact MI5| lia]. }
    cbv beta. intros [] s3' ms3 PO. unfold free_postZ in PO.
    destruct PO as (v5 & v6 & v7 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v28 & v29 & v30 & v31 & m7
                    & -> & MI7 & ST7 & ERR7 & AUX7 & HP7 & FA7 & SO7 & HEAP7).
    rewrite (lb_remove_hd _ _ _ _ ND6) in HP7, HEAP7.
    replace (ret_pc (Z_to_bv 64 0x5b210)) with (Z_to_bv 64 0x5b210) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP7)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    assert (PRES7 : lx_pres LB q [] m m7).
    { eapply lx_pres_trans; [exact PRES5|].
      eapply lx_pres_trans; [eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]|].
      apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP7| lia| intros b Hb; right; exact Hb]. }
    clear MU WM HEAP6 AUX6 HP7 ND6 PRES5 THISC.
    pose proof (munch_refl [(q - 16, q); (THIS, THIS + 96)]%Z m7) as MU. pose proof (wmono_refl usegs m7) as WM.
    rewrite ELX in ERR7.
    unfold implM. iprefix.

    step. step. step. step. step. release_frame FR ST7 q. step.
    assert (ND8 : List.NoDup (map blk_id ((pim, THIS, 96) :: LB))) by (eapply LH_nodup; exact HEAP7).
    ihere. to_implM. eapply implM_bind.
    { eapply (opdel_sized_proof HF) with (B := B) (lo := lo) (A := THIS) (n := 96);
        [exact HEAP7| left; reflexivity| exact AUX7| lia| exact ST7| exact CEIL'| unfold RFREE_STACK; lia| rewrite ELX; exact ERR7| exact MI7| lia]. }
    cbv beta. intros [] s4' ms4 PO. unfold free_postZ in PO.
    destruct PO as (w5 & w6 & w7 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & m9
                    & -> & MI9 & ST9 & ERR9 & AUX9 & HP9 & FA9 & SO9 & HEAP9).
    rewrite (lb_remove_hd _ _ _ _ ND8) in HP9, HEAP9.
    apply HK. unfold hpost. do 15 eexists. exists m9.
    split; [reflexivity|]. split; [exact MI9|]. split; [exact ST9|]. split; [exists errv; exact ERR9|]. split; [exact AUX9|].
    split; [congruence|]. split; [congruence|].
    split; [exact HEAP9|].
    eapply lx_pres_trans; [exact PRES7|].
    eapply lx_pres_trans; [eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]|].
    apply lx_pres_of_heap_pres. exact HP9.
  Qed.

End Proofs.
End WithCeiling0.
