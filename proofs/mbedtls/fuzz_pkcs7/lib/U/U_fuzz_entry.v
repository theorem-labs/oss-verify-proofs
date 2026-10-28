(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AEvt AStep HeapIface Asn1Aux CellsX Cells Mem Step Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import SymExec2 SymExec2Sound.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_layout U_heap U_string. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_top.
Import SX2. Import SX2S.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import TopContract SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
#[local] Existing Instance PropExec.fx0.
Open Scope Z_scope.
Set Printing Width 200.

(* [comment removed for export] *)
Ltac mem_after_store ::=
  lazymatch goal with
  | |- ?EVHD (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) (seg_rom ?segs)) =>
    let c' := cell_of_bytes bs in
    let n := eval cbv in (csize c') in
    lazymatch goal with
    | H : rw_cells segs m A ?cs0 |- _ =>
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          let HB := fresh "HB" in
          pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
          try lazymatch goal with
          | HI : mem_inv segs m |- _ =>
              apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
              [ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
          end;
          change bs with (cbytes c');
          let H' := fresh "CH" in
          pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
          clear H;
          cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
          transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
          footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
          let m' := fresh "m" in
          remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
          clear Heqm; clear HB; try clear m; try rename H' into H
        end
    end
  end.

Ltac mem_after_store_opt ::=
  lazymatch goal with
  | |- ?EVHD (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) (seg_rom ?segs)) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac   (* [comment removed for export] *)
      end
  | _ => idtac
  end.


Section Fuzz.
  Variable sp0 : word.
  Variable P7T : Type.
  Variable p7rep : P7T -> mem -> list blk -> list blk -> Z -> Prop.
  Variable SI : sinv (U_layout sp0).
  Hypothesis PARSE : pkcs7_parse_der_stmt usegs (U_layout sp0) (U_HI sp0) P7T p7rep SI 0x1d748.
  Hypothesis FREE : pkcs7_free_stmt usegs (U_layout sp0) (U_HI sp0) P7T p7rep 0x1dcbc.

  #[using="P7T p7rep PARSE FREE"] Theorem fuzz_entry : fuzz_entry_stmt usegs (U_layout sp0) (U_HI sp0) SI 0x1d6ec.
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo h LB DATA n lo bs
           HH BY LEN Hn HD CR DLO ST CEIL SLO SPA TOP MI SO SIP TP A0 A1.
    pose proof (heap_mok usegs (U_layout sp0) (U_HI sp0) _ _ _ _ HH) as MK.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2 ^ 64) in SPR.
    subst a0 a1.
    pose proof CEIL as CEILn. pose proof (@alloc_ceiling_bounds (U_layout sp0)) as ACB_CEILn.
    assert (DLH : hl_data_lo (U_layout sp0) = 0x48000 /\ hl_data_hi (U_layout sp0) = 0x7e000 /\ hl_stack (U_layout sp0) = 8224 /\ hl_tp (U_layout sp0) = 0x5d0c8) by (repeat split; reflexivity).
    pose proof (munch_refl [(bv_unsigned sp - 1472, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    step.                                              (* [comment removed for export] *)
    carve_frame 1472%nat ST.
    eapply (rw_cells_split_CB usegs _ _ [] 1472%nat _ [] [8;1440;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    step. step. step.                                  (* [comment removed for export] *)
    step. step.                                        (* [comment removed for export] *)
    step. step.                                        (* [comment removed for export] *)
    step. step. step.                                  (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with
    | FRH : rw_cells _ ?mm (bv_unsigned sp + -1472) (CB 8 ?j0 :: CB 1440 ?j1 :: ?rest) |- _ =>
        pose proof (rw_cells_split3 usegs mm (bv_unsigned sp + -1472) [CB 8 j0] [CB 1440 j1] rest FRH) as SPL;
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SPL;
        ddestruct SPL as (FR0 & P7C & FR2); clear FRH
    end.
    replace (bv_unsigned sp + -1472 + 8 + 1440) with (bv_unsigned sp + -24) in FR2 by lia.
    lazymatch type of P7C with rw_cells _ ?mm _ [CB _ ?j1] =>
      replace (bv_unsigned sp + -1472 + Z.of_nat 8) with (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -1464))) in P7C by (rewrite u_small by lia; lia);
      change (CB 1440 j1) with (CB (Z.to_nat (bv_unsigned (Z_to_bv 64 1440))) j1) in P7C
    end.
    lazymatch goal with HMI : mem_inv usegs ?mm |- aevtM _ _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply aevtM_cut_evt; [exact MK | eapply U_memset_spec; [exact P7C | exact HMI] |] end.
    intros ms' PO. ddestruct PO as (v0 & v1 & v2 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & v3 & v4 & v5 & v6 & m1 & -> & MU1 & WM1 & MI1 & ZC).
    rewrite !u_small in MU1 by lia. rewrite (u_small (bv_unsigned sp + -1464)) in ZC by lia.
    change (Z.to_nat (bv_unsigned (Z_to_bv 64 1440))) with 1440%nat in ZC.
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) with (Z_to_bv 8 0) in ZC.
    replace (ret_pc (Z_to_bv 64 0x1d70c)) with (Z_to_bv 64 0x1d70c : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    lazymatch type of MU1 with munch _ ?mm0 _ =>
      (pose proof (rw_cells_transport usegs _ mm0 m1 _ _ FR0 MU1 WM1 ltac:(cbn; lia)) as FR0');
      (pose proof (rw_cells_transport usegs _ mm0 m1 _ _ FR2 MU1 WM1 ltac:(cbn; lia)) as FR2');
      (pose proof (bytes_at_transport usegs _ mm0 m1 _ _ BY MU1 ltac:(cbn; lia)) as BY1);
      lazymatch goal with
      | STH : stk usegs mm0 ?lo' ?hi', HH0 : HEAP _ _ _ _ _ mm0 _, SO0 : statics_ok _ _ mm0, MU0 : munch _ m mm0, WM0 : wmono _ m mm0 |- _ =>
          pose proof (stk_transport_disjoint usegs _ mm0 m1 _ _ STH MU1 WM1 ltac:(cbn; lia)) as ST1;
          pose proof (statics_ok_munch usegs (U_layout sp0) _ mm0 m1 SO0 MU1 ltac:(intros a Ha Hna; cbn [outside]; lia)) as SO1;
          assert (HH1 : HEAP usegs (U_layout sp0) (U_HI sp0) h LB m1 mo)
            by (eapply (heap_frame usegs (U_layout sp0) (U_HI sp0)) with (SP := lo); [exact HH0 | exact CEIL | | exact WM1];
                intros a Ha Hnc; apply MU1; cbn [outside]; unfold wa; rewrite u_small by lia; split; [|exact I];
                intros C; apply Hnc; left; lia);
          assert (SUBW : sub_fp [(bv_unsigned sp + -1464, bv_unsigned sp + -1464 + 1440)] [(bv_unsigned sp - 1472, bv_unsigned sp)])
            by (intros x Hx; cbn [outside] in Hx |- *; split; [lia | exact I]);
          pose proof (munch_trans _ _ _ _ MU0 (munch_weaken _ _ _ _ SUBW MU1)) as MU2;
          pose proof (wmono_trans usegs _ _ _ WM0 WM1) as WM2;
          clear STH HH0 SO0 MU0 WM0 FR0 FR2 BY P7C MU1 WM1
      end
    end.
    lazymatch goal with H : mem_inv usegs ?mmx |- _ => lazymatch mmx with m1 => idtac | _ => clear H end end.
    (* [comment removed for export] *)
    step. step. step. step.
    eapply aevtM_cut.
    { eapply PARSE with (lo := lo) (A := bv_unsigned sp + -1464) (DATA := DATA) (n := n) (bs := bs) (h := h) (LB := LB);
        [ exact HH1 | exact ZC | clear - SPA SPR; Z.div_mod_to_equations; lia | exact BY1 | exact LEN | lia | lia
        | intros a Ha; destruct (CR a Ha) as [C|C]; [left; rewrite u_small by lia; lia | right; exact C]
        | rewrite u_small by lia; lia
        | unfold PKCS7_SIZE; lia
        | rewrite u_small by lia; lia
        | unfold PKCS7_SIZE; lia
        | rewrite u_small by lia; exact ST1 | exact CEIL
        | rewrite u_small by lia; unfold PKCS7_PARSE_STACK; lia
        | rewrite u_small by lia; clear - SPA SPR; Z.div_mod_to_equations; lia
        | rewrite u_small by lia; lia
        | exact MI1 | exact SO1
        | (eapply (si_munch_offdata (U_layout sp0) SI); [exact SIP| exact MU2| intros a Da Wa; cbn [hl_data_lo hl_data_hi U_layout] in Da; cbn [outside]; lia])
        | exact TP | reflexivity | reflexivity | reflexivity ]. }
    intros ms2 mo2x PO.
    ddestruct PO as (w0 & w1 & w2 & wa0 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & m2 & mo2 & h2 & st & LBn
                    & E2 & MI2 & SO2 & SI2 & ST2 & MF2 & HT2 & REP2 & HH2 & HPX2).
    injection E2; clear E2; intros Emo Ems. subst ms2 mo2x.
    rewrite u_small in ST2, HPX2 by lia.
    replace (ret_pc (Z_to_bv 64 0x1d71c)) with (Z_to_bv 64 0x1d71c : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    pose proof (heap_mok usegs (U_layout sp0) (U_HI sp0) _ _ _ _ HH2) as MK2.
    (* [comment removed for export] *)
    step. step.
    eapply aevtM_cut.
    { eapply FREE with (lo := lo) (A := bv_unsigned sp + -1464) (h := h2) (LB := LB) (LBn := LBn) (st := st);
        [ exact HH2 | exact REP2
        | rewrite u_small by lia; lia
        | unfold PKCS7_SIZE; rewrite HT2; lia
        | rewrite u_small by lia; exact ST2 | exact CEIL
        | rewrite u_small by lia; unfold PKCS7_FREE_STACK; lia
        | rewrite u_small by lia; clear - SPA SPR; Z.div_mod_to_equations; lia
        | rewrite u_small by lia; rewrite HT2; lia
        | exact MI2 | exact SO2 | exact TP | reflexivity ]. }
    intros ms3 mo3x PO.
    ddestruct PO as (x0 & x1 & x2 & xa0 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & x3 & x4 & x5 & x6 & m3 & mo3 & h3 & LBx
                    & E3 & MI3 & SO3 & ST3 & MF3 & HT3 & ZC3 & HH3 & HPX3).
    injection E3; clear E3; intros Emo Ems. subst ms3 mo3x.
    rewrite u_small in ST3, HPX3 by lia.
    replace (ret_pc (Z_to_bv 64 0x1d724)) with (Z_to_bv 64 0x1d724 : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    pose proof (heap_mok usegs (U_layout sp0) (U_HI sp0) _ _ _ _ HH3) as MK3.
    (* [comment removed for export] *)
    assert (FR23 : rw_cells usegs m3 (bv_unsigned sp + -24) [C8 s1; C8 s0; C8 ra]).
    { eapply heap_presx_rw_cells; [exact HPX3 | | apply client_range_stack; cbn; lia | cbn; unfold PKCS7_SIZE; lia].
      eapply heap_presx_rw_cells; [exact HPX2 | exact FR2' | apply client_range_stack; cbn; lia | apply disjoint_from_app_intro; [cbn; unfold PKCS7_SIZE; lia| apply (si_fp_disjoint_hi (U_layout sp0) SI); cbn [hl_data_hi U_layout]; lia]]. }
    assert (FR03 : rw_cells usegs m3 (bv_unsigned sp + -1472) [CB 8 (firstn 8 junk)]).
    { eapply heap_presx_rw_cells; [exact HPX3 | | apply client_range_stack; cbn; lia | cbn; unfold PKCS7_SIZE; lia].
      eapply heap_presx_rw_cells; [exact HPX2 | exact FR0' | apply client_range_stack; cbn; lia | apply disjoint_from_app_intro; [cbn; unfold PKCS7_SIZE; lia| apply (si_fp_disjoint_hi (U_layout sp0) SI); cbn [hl_data_hi U_layout]; lia]]. }
    step.                                              (* [comment removed for export] *)
    step. step. step.                                  (* [comment removed for export] *)
    step.                                              (* [comment removed for export] *)
    step.                                              (* [comment removed for export] *)
    apply aevtM_done.
    unfold fuzz_entry_post.
    deexists 15. dexists m3, mo3, h3, LBx.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact MI3|]. split; [exact SO3|].
    split; [eapply (si_heap_presx usegs (U_layout sp0) SI); [exact SI2| exact HPX3| intros a NO; pose proof (si_below (U_layout sp0) SI a NO); cbn [hl_data_hi U_layout] in *; cbn [outside]; unfold PKCS7_SIZE; lia] |].
    split.
    { (* [comment removed for export] *)
      pose proof (stk_of_rw_cells usegs m3 _ _ FR03) as K0. pose proof (stk_of_rw_cells usegs m3 _ _ ZC3) as K1.
      pose proof (stk_of_rw_cells usegs m3 _ _ FR23) as K2. cbn [cells_size csize Nat.add] in K0, K1, K2.
      eapply stk_merge; [exact ST3 | | lia].
      eapply stk_merge; [exact K0 | | lia].
      eapply stk_merge; [| replace (bv_unsigned sp) with (bv_unsigned sp + -24 + Z.of_nat 24) by lia; exact K2 | lia].
      replace (bv_unsigned sp + -1472 + Z.of_nat 8) with (bv_unsigned sp + -1464) by lia.
      replace (bv_unsigned sp + -24) with (bv_unsigned sp + -1464 + Z.of_nat 1440) by lia. exact K1. }
    split; [eapply mo_frame_trans; [exact MF2 | exact MF3] |].
    split.
    { (* [comment removed for export] *)
      intros a Ha HC HO.
      assert (OW : outside [(bv_unsigned sp - 1472, bv_unsigned sp)] a).
      { cbn [outside]. split; [|exact I]. destruct HC as [C|[C|C]]; [lia | cbn [hl_data_lo hl_data_hi U_layout] in C; lia |].
        ddestruct C as ([B k] & HB & Hr). cbn in Hr.
        pose proof (heap_blocks usegs (U_layout sp0) (U_HI sp0) _ _ _ _ HH1) as [FB _].
        pose proof (proj1 (List.Forall_forall _ _) FB _ HB) as (_ & _ & _ & B4 & _). cbn [fst snd] in B4. lia. }
      assert (HC' : client_addr (U_layout sp0) LB (bv_unsigned sp + -1472) a) by (destruct HC as [C|[C|C]]; [left; lia | right; left; exact C | right; right; exact C]).
      assert (OX : outside [(bv_unsigned sp + -1464, bv_unsigned sp + -1464 + PKCS7_SIZE)] a).
      { cbn [outside]. unfold PKCS7_SIZE. split; [|exact I]. cbn [outside] in OW. lia. }
      destruct (HPX2 a Ha HC' (outside_app_intro _ _ a OX HO)) as [E2 W2]. destruct (HPX3 a Ha HC' OX) as [E3 W3].
      pose proof (MU2 (wa a) ltac:(unfold wa; rewrite u_small by lia; exact OW)) as E1.
      split; [rewrite E3, E2, E1; reflexivity|].
      intros Wa. apply W3, W2. apply WM2. exact Wa. }
    split; [exact HH3|]. rewrite HT3, HT2. reflexivity.
  Qed.
End Fuzz.
