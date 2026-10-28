(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun SjModel AtpModel Target Prog AtpImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_num_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import F_memchr F_memcmp F_strlen F_memcpy F_memmove_t2 Atp_defs Atp_kitu Atp_arrl Atp_str Atp_strr Atp_objk Atp_obju Atp_objt Atp_objs Atp_obje.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Notation ae_T E := (Tf (ae_tws E)).
Notation ae_S E := (Tf (ae_sbs E)).
Notation ae_n E := (Z.of_nat (length (ae_tws E))).
Notation ae_sn E := (Z.of_nat (length (ae_sbs E))).

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Obj.
  Variable E : aenv.
  Hypothesis OK : aenv_ok E.
  Variable d : nat.
  Hypothesis HELEM : atp_elem_stmt E d.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma obj_esc_heap : forall (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (out node i e c P L0 L e0 sl : Z) (rest0 k : list Z) (REST : list (list Z)) (m0 m1 : mem) (j0 j8 j16 j24 j28 js j4 jo : list byte) (errv : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
    obj_mid E d m0 m1 s ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 out node i e c P L0 L sl rest0 k REST j0 j8 j16 j24 j28 js j4 jo errv ->
    0 <= e0 < L -> has_tilde k = true -> 23 <= L ->
    implM usegs (atp_walk lops (k :: REST)) s
      (fun _ => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m0))
      (MS (mkR x1 (Z_to_bv 64 (q + -208)) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 out) (Z_to_bv 64 sl) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 node) (Z_to_bv 64 e0) (Z_to_bv 64 (P + 1)) (Z_to_bv 64 L) x22 x23 x24 x25 x26 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x3f1b8) fc None m1 (seg_rom usegs)).
  Proof.
    intros until x31. intros PRE E0 HT L23.
    destruct PRE as (SCR & STRS & REC & FRK & FRSV & FRB & OUTR & QO & OB & QD & OD & AI & NODE & QN & NB & TY & NXT & TILES & I0 & EN & KEYB & KEYF & ZL0 & EK
                     & LL0 & L040 & P0 & PAT & RC & HEAP & AUX & ST & LO & Q16 & ERR & MI & PRES).
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L BT BS BP PP0 [CEIL GLO] B63 [DL DB] [AL8D AL8T]].
    pose proof (zlength_nonneg rest0) as ZL0N. pose proof LO as LOF. unfold obj_need, elem_need, ATP_LEAFX, RMALLOC_STACK, GLOBALS_TOP in *. unfold obj_savedU in FRB.
    assert (LO0 : 0 <= ae_lo E) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    assert (ELX : LX_ERRNO = 980196) by reflexivity. rewrite ELX in ERR.
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    pose proof (aenv_ranges E s m1 OK HEAP) as (TR & SR & PR).
    assert (BLB : forall a, in_block (ae_LB E) a -> a < alloc_ceiling) by (intros a Ha; exact (proj2 (blocks_below _ _ _ _ HEAP Ha))).
    assert (PIN : ae_PTR E <= P + 1 /\ P + 1 + L0 <= ae_PTR E + zlength (ae_p1 E)).
    { destruct PAT as (pre & Ep & EP). rewrite EP, Ep. unfold zlength in *. rewrite length_app. cbn [length]. lia. }
    assert (L026 : L0 < 2^26) by lia.
    destruct BP as [E0p|BPx]; [exfalso; rewrite E0p in PIN; unfold zlength in PIN; cbn in PIN; lia|].
    pose proof (in_blocks_range _ _ _ _ _ HEAP BPx ltac:(unfold zlength; lia)) as PRANGE.
    assert (PCEIL : P + 1 + L0 <= alloc_ceiling) by lia.
    assert (ZLK : zlength k = L) by (rewrite EK; unfold zlength in *; rewrite firstn_length_le by lia; lia).
    pose proof (str_sz_bound L ltac:(lia)) as SZB. pose proof (str_sz_even L ltac:(lia)) as SZE.
    hide AI. hide KEYB.
    pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    unfold implM. iprefix.

    pose proof (lor7_eq L ltac:(lia)) as L7. pose proof (Z.mod_pos_bound L 8 ltac:(lia)) as M8.
    assert (AT38 : forall xa0 : word,
      evt usegs (fun ms' => impl usegs (at_node usegs) (atp_walk lops (k :: REST) s)
                  (epost (fun p => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m0) (snd p))) ms')
        (MS (mkR x1 (Z_to_bv 64 (q + -208)) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 out) (Z_to_bv 64 sl) xa0 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 node) (Z_to_bv 64 e0) (Z_to_bv 64 (P + 1)) (Z_to_bv 64 L) x22 (Z_to_bv 64 (str_sz L)) x24 x25 x26 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x3f1d0) fc None m1 (seg_rom usegs))).
    2:{ astep. rewrite L7. astep. step. if_cases KS; zify_cond KS.
        - astep. replace (L - L mod 8 + 8) with (str_sz L) by (unfold str_sz; destruct (Z.eqb_spec L 23) as [E23|N23]; [exfalso; subst; cbn in KS; lia| rewrite L7; lia]).
          eapply evt_eq; [| apply AT38]; [atp_st_eq].
        - astep. step. replace (Z_to_bv 64 26) with (Z_to_bv 64 (str_sz L)) by (unfold str_sz; destruct (Z.eqb_spec L 23) as [E23|N23]; [reflexivity| exfalso; lia]).
          eapply evt_eq; [| apply AT38]; [atp_st_eq]. }
    intros xa0. step. step.
    apply evt_done. to_implM_at (fun _ : unit => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m0)).
    apply implM_atp_walk_string; [exact HT| rewrite ZLK; unfold SSO_MAX; lia|]. rewrite ZLK.
    eapply implM_bind.
    { eapply (opnew_body HM) with (B := ae_B E) (lo := ae_lo E);
        [exact HEAP| exact AUX| lia| exact ST| exact CEIL'| unfold RMALLOC_STACK; lia| rewrite ELX; exact ERR| exact MI| lia| lia]. }
    cbv beta. intros pb s1' ms1 PO. unfold opnew_postZ in PO.
    destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3 & errv3 & A & junk & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA3 & SO3 & BR & HEAP3 & BLK).
    replace (ret_pc (Z_to_bv 64 0x3f1d8)) with (Z_to_bv 64 0x3f1d8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (agree_of_heap_pres _ _ _ _ HP) as AG3.
    apply (rw_cells_agree _ _ _ _ _ AG3) in SCR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG3) in STRS; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG3) in REC; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG3) in FRK; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG3) in FRSV; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG3) in FRB; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG3) in OUTR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG3) in NODE; [| intros a Ha; left; cbn in Ha; lia].
    assert (AI3 : AINV E m3).
    { unhide AI. eapply AINV_agree; [exact AI| exact AG3| | | exact OK].
      - intros a Ha. right. right. exact Ha.
      - intros a Ha. left. lia. }
    assert (KEYB3 : bytes_at usegs m3 (P + 1) (map (Z_to_bv 8) rest0)).
    { unhide KEYB. eapply bytes_at_agree; [exact AG3| exact KEYB|]. intros a Ha. rewrite length_map in Ha. unfold zlength in ZL0.
      right. right. eapply in_blocks_in_block; [exact BPx| lia]. }
    hide KEYB3.
    assert (PRES3 : lx_pres (ae_LB E) q [(out, out + 24)] m0 m3).
    { eapply lx_pres_trans; [exact PRES|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP| lia| auto]. }
    clear AG3 HP MU WM. rewrite ELX in ERR3.
    pose proof BR as (BA0 & BA16 & _ & BAC & BAS). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in BAC.
    assert (NBLK : forall a, A <= a < A + str_sz L -> ~ in_block (ae_LB E) a) by (intros a Ha; eapply fresh_block_sep; [exact HEAP3| exact Ha]).

    pose proof (munch_refl [(q - 336, q - 112); (A, A + str_sz L)]%Z m3) as MU. pose proof (wmono_refl usegs m3) as WM.
    unfold implM. iprefix.
    apply (rw_cells_split_CB usegs _ _ [] 24 js [] [8;8;8]%nat) in STRS; [|reflexivity]. cbn [mk_CB_cells app] in STRS.
    step. astep. hstep. hstep. hstep. name_mem m4.
    set (KK := fun ms' : machine_state => impl usegs (at_node usegs) (mbind (del lops pb) (fun _ : unit => atp_walk lops REST) s1')
                (epost (fun p => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m0) (snd p))) ms') in *.
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client (ae_LB E) q [(out, out + 24)] a -> outside [(q - 336, q - 112); (A, A + str_sz L)] a).
    { intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| split; [| exact I]].
      - destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia].
      - destruct HC as [HC|[HC|HC]]; [lia| intros R; exact (NBLK a R HC)| lia]. }
    assert (AI4 : AINV E m4).
    { eapply AINV_agree; [exact AI3| eapply agree_on_of_munch; [exact MU| exact WM]| | | exact OK].
      - intros a Ha. pose proof (BLB a Ha). cbn [outside]. split; [lia|]. split; [| exact I]. intros R. exact (NBLK a R Ha).
      - intros a Ha. cbn [outside]. lia. }
    assert (KEYB4 : bytes_at usegs m4 (P + 1) (map (Z_to_bv 8) rest0)).
    { unhide KEYB3. eapply bytes_at_agree; [eapply agree_on_of_munch; [exact MU| exact WM]| exact KEYB3|]. intros a Ha. rewrite length_map in Ha. unfold zlength in ZL0.
      cbn [outside]. split; [lia|]. split; [| exact I]. intros R. apply (NBLK a R). eapply in_blocks_in_block; [exact BPx| lia]. }
    assert (HDR4 : shdr m4 (q + -176) true A (str_sz L) L).
    { unfold shdr. split; [| exact SZE].
      lazymatch type of STRS with rw_cells _ _ _ [C8 (Z_to_bv 64 ?x); _; _] => replace x with (str_sz L + 1) in STRS by lia end. exact STRS. }
    destruct (rw_cells_forget _ _ _ _ FRK) as [jk FRK']. cbn [cells_size csize Nat.add] in FRK'.
    eapply evt_eq; [| eapply (obj_str_phase E OK d KK m4 F fc q true A (str_sz L) L e0 P L0 sl rest0 i e c node out);
      [ exact HDR4| exact BLK| lia| lia| lia| lia| lia| intros _; split; lia| intros X; discriminate X| left; lia
      | exact NBLK| exact BLB| exact PIN| exact KEYB4| exact KEYF| exact ZL0| lia| exact L040| exact P0| lia| exact PCEIL| exact E0
      | exact SCR| exact REC| exact FRK'| exact AI4| exact NODE| exact QN| exact NB| exact QD| exact TY| exact NXT| exact TILES| exact I0| exact EN| exact TR| exact SR
      | exact ST3| lia| exact CEIL'| unfold GLOBALS_TOP; lia| exact QO| exact OB| exact B63| exact MI3| | ] ]; [atp_st_eq| |].

    all: assert (CLI3 : forall a, 0 <= a < 2^64 -> lx_client (ae_LB E) q [(out, out + 24)] a -> outside [(q - 336, q - 112); (A, A + str_sz L); (out, out + 24)] a)
      by (intros a Ha HC; pose proof (CLI a Ha HC) as X; destruct HC as [HX _]; cbn [rin_ivs fst snd] in HX; cbn [outside] in X |- *; tauto).
    all: assert (WOK3 : Forall (rclient_write_ok ((pb, A, str_sz L) :: ae_LB E)) [(q - 336, q - 112); (A, A + str_sz L); (out, out + 24)])
      by (constructor; [apply W_ok_stack; cbn; lia|]; constructor; [eapply W_ok_block; [left; reflexivity| cbn; lia| cbn; lia]|];
          constructor; [apply W_ok_stack; cbn; lia| constructor]).
    -
      intros m' sz ja' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y28 y29 y30 y31 LS' HA0 SCR' REC' FRK2 MI' ST' MU' WM'.
      rewrite (HA0 eq_refl). unfold objs_W in MU'.
      pose proof (rw_cells_transport _ _ _ _ _ _ FRB MU' WM' ltac:(cbn; lia)) as FRB'.
      pose proof (rw_cells_transport _ _ _ _ _ _ FRSV MU' WM' ltac:(cbn; lia)) as FRSV'.
      pose proof (rw_cells_transport _ _ _ _ _ _ OUTR MU' WM' ltac:(cbn; lia)) as OUTR'.
      pose proof (rw_cells_transport _ _ _ _ _ _ ERR3 MU' WM' ltac:(cbn; lia)) as ERR'.
      pose proof LS' as (SZ0' & SZC' & CAP' & A0' & AC' & _ & [HDR' EV']).
      pose proof (munch_refl [(out, out + 24)]%Z m') as MUo. pose proof (wmono_refl usegs m') as WMo. hide MU'.
      pose proof (rw_cells_C8_read1 _ _ _ _ HDR') as RD0.
      apply (rw_cells_split_CB usegs _ _ [] 24 _ [] [8;8;4;4]%nat) in OUTR'; [|reflexivity]. cbn [mk_CB_cells app] in OUTR'.
      step. if_lia. astep. rewrite zx8_lit by lia. astep. astep. rewrite long_byte0 by lia. hstep. hstep. hstep. step. if_false. step. astep. rewrite long_capmask by lia. step.
      name_mem m5. unhide MU'.
      lazymatch goal with H : rw_cells usegs m5 out _ |- _ => rename H into OUT5 end.
      assert (MU35 : munch [(q - 336, q - 112); (A, A + str_sz L); (out, out + 24)] m3 m5).
      { eapply munch_trans; [eapply munch_weaken; [| exact MU]|]. 2: eapply munch_trans; [eapply munch_weaken; [| exact MU']| eapply munch_weaken; [| exact MUo]].
        all: unfold sub_fp; cbn [outside]; intros x' Hx; lia. }
      assert (WM35 : wmono usegs m3 m5) by (eapply wmono_trans; [exact WM| exact WM']).
      assert (HEAP5 : RHEAP s1' ((pb, A, str_sz L) :: ae_LB E) m5) by (eapply LH_frame; [exact HEAP3| exact MU35| exact WM35| exact WOK3]).
      assert (AUX5 : rauxv_ok m5 (ae_B E)).
      { eapply rauxv_ok_frame; [exact AUX3| exact MU35| exact WM35|].
        constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      pose proof (LH_nodup _ _ _ HEAP5) as ND.
      subst KK. apply evt_done. to_implM_at (fun _ : unit => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m0)).
      eapply implM_bind.
      { eapply (opdel_sz_proof HF) with (B := ae_B E) (lo := ae_lo E) (A := A) (n := str_sz L);
          [exact HEAP5| left; reflexivity| exact AUX5| lia| exact ST'| exact CEIL'| unfold RFREE_STACK; lia| rewrite ELX; exact ERR'| exact MI'| lia]. }
      cbv beta. intros [] s2' ms2 PO. unfold free_postZ in PO.
      destruct PO as (u5 & u6 & u7 & u10 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m6 & -> & MI6 & ST6 & ERR6 & AUX6 & HP6 & FA6 & SO6 & HEAP6).
      rewrite (lb_remove_hd _ _ _ _ ND) in HP6, HEAP6.
      replace (ret_pc (Z_to_bv 64 0x3f2dc)) with (Z_to_bv 64 0x3f2dc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (agree_of_heap_pres _ _ _ _ HP6) as AG6.
      apply (rw_cells_agree _ _ _ _ _ AG6) in SCR'; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG6) in REC'; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG6) in FRK2; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG6) in FRSV'; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG6) in FRB'; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG6) in OUT5; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG6) in HDR'; [| intros a Ha; left; cbn in Ha; lia].
      pose proof (munch_refl ([] : list (Z * Z)) m6) as MU6. pose proof (wmono_refl usegs m6) as WM6.
      unfold implM. iprefix. step. stop_now.
      destruct (rw_cells_forget _ _ _ _ HDR') as [jj SL]. cbn [cells_size csize Nat.add] in SL.
      destruct (frame112 m6 q _ _ _ _ _ _ SCR' SL REC' eq_refl FRK2 eq_refl FRSV') as [ja3 FRA].
      eapply (obj_epi E); [exact FRA| unfold obj_savedU; exact FRB'| exact MI6| exact ST6| lia| exists errv3; rewrite ELX; exact ERR6| exact AUX6
                       | rewrite FA6; exact FA3| rewrite SO6; exact SO3| exact HEAP6| |].
      + eapply lx_pres_trans; [exact PRES3|]. eapply lx_pres_trans; [eapply lx_pres_of_munch; [exact MU35| exact WM35| exact CLI3]|].
        apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP6| lia| auto].
      + exists (Z_to_bv 64 0), 0, 22. eexists. split; [exact OUT5|]. split; [lia|]. intros C0. exfalso. lia.
    -
      intros m' sz err ja' w0 w1 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y25 y26 y28 y29 y30 y31 LS' SCR' REC' FRK2 HERR MI' ST' MU' WM'.
      split; [intros X; discriminate X| intros _].
      unfold objs_W in MU'.
      pose proof (rw_cells_transport _ _ _ _ _ _ FRB MU' WM' ltac:(cbn; lia)) as FRB'.
      pose proof (rw_cells_transport _ _ _ _ _ _ FRSV MU' WM' ltac:(cbn; lia)) as FRSV'.
      pose proof (rw_cells_transport _ _ _ _ _ _ OUTR MU' WM' ltac:(cbn; lia)) as OUTR'.
      pose proof (rw_cells_transport _ _ _ _ _ _ ERR3 MU' WM' ltac:(cbn; lia)) as ERR'.
      pose proof (rw_cells_transport _ _ _ _ _ _ NODE MU' WM' ltac:(cbn; lia)) as NODE'.
      pose proof LS' as (SZ0' & SZC' & CAP' & A0' & AC' & _ & [HDR' EV']).
      assert (MU3' : munch [(q - 336, q - 112); (A, A + str_sz L); (out, out + 24)] m3 m').
      { eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MU']]; unfold sub_fp; cbn [outside]; intros x' Hx; lia. }
      assert (WM3' : wmono usegs m3 m') by (eapply wmono_trans; [exact WM| exact WM']).
      assert (HEAP' : RHEAP s1' ((pb, A, str_sz L) :: ae_LB E) m') by (eapply LH_frame; [exact HEAP3| exact MU3'| exact WM3'| exact WOK3]).
      assert (AUX' : rauxv_ok m' (ae_B E)).
      { eapply rauxv_ok_frame; [exact AUX3| exact MU3'| exact WM3'|].
        constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      assert (AI' : AINV E m').
      { eapply AINV_agree; [exact AI3| eapply agree_on_of_munch; [exact MU3'| exact WM3']| | | exact OK].
        - intros a Ha. pose proof (BLB a Ha). cbn [outside]. split; [lia|]. split; [intros R; exact (NBLK a R Ha)|]. split; [lia| exact I].
        - intros a Ha. cbn [outside]. lia. }
      pose proof (LH_nodup _ _ _ HEAP') as ND.
      subst KK. apply evt_done. to_implM_at (fun _ : unit => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m0)).
      eapply implM_bind.
      { eapply (opdel_sz_proof HF) with (B := ae_B E) (lo := ae_lo E) (A := A) (n := str_sz L);
          [exact HEAP'| left; reflexivity| exact AUX'| lia| exact ST'| exact CEIL'| unfold RFREE_STACK; lia| rewrite ELX; exact ERR'| exact MI'| lia]. }
      cbv beta. intros [] s2' ms2 PO. unfold free_postZ in PO.
      destruct PO as (u5 & u6 & u7 & u10 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m6 & -> & MI6 & ST6 & ERR6 & AUX6 & HP6 & FA6 & SO6 & HEAP6).
      rewrite (lb_remove_hd _ _ _ _ ND) in HP6, HEAP6.
      replace (ret_pc (Z_to_bv 64 0x3f330)) with (Z_to_bv 64 0x3f330) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (agree_of_heap_pres _ _ _ _ HP6) as AG6.
      apply (rw_cells_agree _ _ _ _ _ AG6) in SCR'; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG6) in REC'; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG6) in FRK2; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG6) in FRSV'; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG6) in FRB'; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG6) in OUTR'; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG6) in HDR'; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG6) in NODE'; [| intros a Ha; left; cbn in Ha; lia].
      assert (AI6 : AINV E m6).
      { eapply AINV_agree; [exact AI'| exact AG6| | | exact OK]; [intros a Ha; right; right; exact Ha| intros a Ha; left; lia]. }
      assert (PRES6 : lx_pres (ae_LB E) q [(out, out + 24)] m0 m6).
      { eapply lx_pres_trans; [exact PRES3|]. eapply lx_pres_trans; [eapply lx_pres_of_munch; [exact MU3'| exact WM3'| exact CLI3]|].
        apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP6| lia| auto]. }
      rewrite ELX in ERR6.
      destruct (rw_cells_forget _ _ _ _ HDR') as [jj SL]. cbn [cells_size csize Nat.add] in SL.
      eapply (obj_tail E OK d HELEM ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s s2' out P L0 sl e err w0 w1 REST m0 m6);
        [exact SCR'| exact SL| exact REC'| exact FRK2| exact FRSV'| unfold obj_savedU; exact FRB'| exact OUTR'| exact QO| exact OB| exact QD| exact AI6| exact HERR
        | exact EN| exact P0| lia| lia| exact RC| exact HEAP6| exact AUX6| exact ST6| exact LOF| exact Q16| exists errv3; rewrite ELX; exact ERR6| exact MI6
        | rewrite FA6; exact FA3| rewrite SO6; exact SO3| exact PRES6].
  Qed.

End Obj.
End WithCeiling0.
