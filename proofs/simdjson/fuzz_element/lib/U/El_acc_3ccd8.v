From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun SjModel AtpModel ElModel Target Prog AtpImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit Atp_defs Atp_kitu El_defs.
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

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation ae_T E := (Tf (ae_tws E)).
Notation ae_S E := (Tf (ae_sbs E)).
Notation ae_n E := (Z.of_nat (length (ae_tws E))).
Notation ae_sn E := (Z.of_nat (length (ae_sbs E))).

Section A3ccd8.
  Variable E : aenv.
  Hypothesis OK : aenv_ok E.

  Definition acc_3ccd8_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (lo : Z) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
      ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom usegs)
      /\ munch [(q - 16, q)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo q /\ frm0 fc'
      /\ bv_unsigned a0 < 64
      /\ (bv_unsigned a0 =? 0) = ((ae_T E 1 =? tword t_dbl 0) || (ae_T E 1 =? tword t_u64 0) || (ae_T E 1 =? tword t_i64 0)).

  Lemma acc_3ccd8_spec : forall (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (q node : Z),
    AINV E m -> el_root E m node -> RHEAP s (ae_LB E) m -> mem_inv usegs m -> frm0 fc ->
    stk usegs m (ae_lo E) q -> ae_lo E <= q - 16 -> q <= node -> node + 16 <= ae_B E -> q <= ae_DOC E ->
    evt usegs (acc_3ccd8_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (ae_lo E) m)
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 node) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x3ccd8) fc None m (seg_rom usegs)).
  Proof.
    intros until node. intros AI ROOT HEAP MI FRM ST LOQ QN NB QD.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L BT BS BP P0 [CEIL GLO] B63 [DL DB] [D8 T8]].
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    pose proof (aenv_ranges E s m OK HEAP) as ((T0 & TH) & _ & _).
    pose proof (el_root_elem E OK) as [EL NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (elem_word_range _ _ _ _ _ _ EL ltac:(lia) ltac:(lia) HSN) as TIR.
    destruct AI as (TB & _ & _ & DOCC). unfold el_root in ROOT. unfold GLOBALS_TOP in GLO.
    pose proof (munch_refl [(q - 16, q)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    hide TB.

    step. carve_frame 16%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 16 junk [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    hstep. hstep. step.
    unhide TB. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    apply (bytes_at_agree _ _ _ _ _ (agree_on_of_munch _ _ _ MU WM)) in TB; [| rewrite u64s_length, length_map; intros a Ha; cbn [outside]; clear - Ha T0 TH GLO CEIL LOQ; lia].
    pose proof (tape_read m1 (ae_TAPE E) (ae_tws E) 1 TB ltac:(lia)) as RDT. rewrite Z.mul_1_r in RDT.
    pose proof (tape_read m1 (ae_TAPE E) (ae_tws E) 2 TB ltac:(lia)) as RDT2.
    lazymatch goal with H : rw_cells usegs m1 (ae_DOC E) _ |- _ => rename H into DOCC1 end.
    lazymatch goal with H : rw_cells usegs m1 node _ |- _ => rename H into ROOT1 end.

    step. step. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|]. clear K1.
    zstep. rewrite (land7_mod8 (ae_DOC E) ltac:(lia) D8). step. if_false.
    step. step.
    Ltac tix i ra DOCC1 T8 := eapply (tix_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ae_DOC E) (ae_TAPE E) i ra [C8 (Z_to_bv 64 (ae_SBUF E))]);
      [exact DOCC1| lia| lia| lia| lia| exact T8| lia| lia| reflexivity| lia| reflexivity|].
    Ltac fin FRM := apply evt_done; unfold acc_3ccd8_post; do 18 eexists; split; [cbv delta [mkR]; reflexivity|];
      split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
      split; [first [exact FRM| apply frm0_slice_set_fflags; exact FRM]|]; split; [rewrite ?unsigned_lit by lia; lia|]; rewrite ?unsigned_lit by lia.
    Ltac ret_path FR ST q := step; step; step; release_frame FR ST q; step.
    tix 1 0x3cd00 DOCC1 T8.
    intros xa1 xa2 xa3 xa4. rewrite Z.mul_1_r.
    step. step. step. step. astep. zstep. rewrite (land7_mod8 (ae_DOC E) ltac:(lia) D8). astep. astep. astep.
    replace (0 <? ae_DOC E) with true by (symmetry; apply Z.ltb_lt; lia). change (Z.land (Z.b2z true) (Z.b2z (0 <? 1))) with 1.
    step. if_cases K2; zify_cond K2.
    -
      step. if_false. step. step.
      tix 1 0x3cd5c DOCC1 T8.
      intros ya1 ya2 ya3 ya4. rewrite Z.mul_1_r.
      step. step. step. step. astep. zstep. rewrite (land7_mod8 (ae_DOC E) ltac:(lia) D8). astep. astep. astep.
      replace (0 <? ae_DOC E) with true by (symmetry; apply Z.ltb_lt; lia). change (Z.land (Z.b2z true) (Z.b2z (0 <? 1))) with 1.
      step. if_cases K3; zify_cond K3.
      +
        step. if_false. step. step.
        tix 1 0x3cdb4 DOCC1 T8.
        intros za1 za2 za3 za4. rewrite Z.mul_1_r.
        step. step. astep. step. if_cases K4; zify_cond K4.
        *
          step. step. step.
          ret_path FR ST q.
          fin FRM.
          assert (N1 : (ae_T E 1 =? tword t_dbl 0) = false) by (apply Z.eqb_neq; unfold tword, t_dbl; lia).
          assert (N2 : (ae_T E 1 =? tword t_u64 0) = false) by (apply Z.eqb_neq; unfold tword, t_u64; lia).
          assert (N3 : (ae_T E 1 =? tword t_i64 0) = false) by (apply Z.eqb_neq; unfold tword, t_i64; lia).
          rewrite N1, N2, N3. reflexivity.
        *
          step. step. if_cases K5; zify_cond K5; [exfalso; rewrite ?unsigned_lit in K5 by lia; lia|]. clear K5.
          zstep. rewrite (land7_mod8 (ae_DOC E) ltac:(lia) D8). step. if_false.
          step. astep. step.
          tix 2 0x3cde0 DOCC1 T8.
          intros wa1 wa2 wa3 wa4.
          step. step. step. step. step.
          ret_path FR ST q.
          fin FRM. rewrite K4. reflexivity.
      +
        step. if_false. step. astep. step.
        tix 2 0x3cd94 DOCC1 T8.
        intros za1 za2 za3 za4.
        step. step. step. step. step.
        ret_path FR ST q.
        fin FRM. rewrite K3. reflexivity.
    -
      step. if_false. step. astep. step.
      tix 2 0x3cd38 DOCC1 T8.
      intros ya1 ya2 ya3 ya4.
      step. step. step. step. step. release_frame FR ST q. step.
      fin FRM. rewrite K2. reflexivity.
  Qed.
End A3ccd8.
End WithCeiling0.
