From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun SjModel AtpModel ElModel Target Prog AtpImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Atp_objl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit Atp_defs Atp_kitu Atp_objk El_defs.
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

Lemma acc_3da20_u8 : forall x, 0 <= x < 256 -> bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 x))) = x.
Proof.
  intros x Hx. rewrite (Z_to_bv_unsigned 8 x). unfold bv_wrap. change (bv_modulus 8) with 256.
  rewrite Z.mod_small by lia. apply unsigned_lit. lia.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation ae_T E := (Tf (ae_tws E)).
Notation ae_S E := (Tf (ae_sbs E)).
Notation ae_n E := (Z.of_nat (length (ae_tws E))).
Notation ae_sn E := (Z.of_nat (length (ae_sbs E))).

Lemma acc_3da20_obj : forall E, aenv_ok E -> ttype (ae_T E 1) = t_obj ->
  exists d e c, ty (ae_T E) 1 = t_obj /\ tnext (ae_T E 1) = e + 1
    /\ tiles (field (ae_T E) (ae_S E) (ae_sn E) (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d)) (1 + 1) e c /\ e + 1 <= ae_n E - 1.
Proof.
  intros E OK HT. pose proof (el_root_elem E OK) as [EL NR].
  assert (SC : scalar (ae_T E) (ae_S E) (ae_sn E) 1 (ae_n E - 1) -> False).
  { assert (HSN : ae_sn E < 2^56) by (destruct (ok_wf E OK) as (_ & ? & _); lia).
    intros [[_ [H|[H|H]]]|[[_ [H|[H|H]]]|[_ (o & l & H & SA)]]];
      [..| pose proof (str_at_bounds (ae_S E) (ae_sn E) HSN o l SA) as (O0 & _ & _ & _ & O56)];
      rewrite H, ttype_tword in HT by lia;
      unfold t_obj, t_true, t_false, t_null, t_i64, t_u64, t_dbl, t_str in HT; lia. }
  destruct TAPE_MAX_DEPTH as [|d'] eqn:HD; cbn [elem] in EL.
  - destruct EL as [EL|[]]. exfalso. exact (SC EL).
  - destruct EL as [EL|(e & c & cv & Ej & CK & [(H1 & H2 & H3)|(H1 & H2 & H3)])]; [exfalso; exact (SC EL)| |].
    + unfold ck_any in CK. rewrite H1, ttype_cword in HT by lia. unfold t_obj, t_arr in HT. lia.
    + exists d', e, c. unfold ty. unfold ck_any in CK.
      split; [rewrite H1; apply ttype_cword; lia|]. split; [rewrite H1; apply tnext_cword; lia|]. split; [exact H3| lia].
Qed.

Section A3da20.
  Variable E : aenv.
  Hypothesis OK : aenv_ok E.

  Definition acc_3da20_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (OUT lo : Z) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
      ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom usegs)
      /\ munch [(q - 192, q); (OUT, OUT + 24)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo q /\ frm0 fc'
      /\ exists (w0 w1 : word) (code : Z) (od : list byte), rw_cells usegs m' OUT [C8 w0; C8 w1; C4 (Z_to_bv 64 code); CB 4 od]
           /\ (code = 0 \/ code = 17 \/ code = 20).

  Lemma acc_3da20_spec : forall (ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (q node OUT lo : Z) (jo : list byte),
    AINV E m -> el_root E m node -> RHEAP s (ae_LB E) m -> mem_inv usegs m -> frm0 fc ->
    rw_cells usegs m OUT [CB 24 jo] -> q <= OUT -> OUT + 24 <= ae_B E -> q <= node -> node + 16 <= ae_B E -> q <= ae_DOC E ->
    stk usegs m lo q -> ae_lo E <= lo -> lo + 192 <= q -> (0 < zlength (ae_p1 E) -> 0 < ae_PTR E) -> ae_PTR E + zlength (ae_p1 E) <= ae_lo E ->
    evt usegs (acc_3da20_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 OUT lo m)
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 OUT) (Z_to_bv 64 node) (Z_to_bv 64 (ae_PTR E))
               (Z_to_bv 64 (zlength (ae_p1 E))) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x3da20) fc None m (seg_rom usegs)).
  Proof.
    intros until jo. intros AI ROOT HEAP MI FRM SLOT QO OB QN NB QD ST LOLO LOQ KP0 KPL.
    pose proof (rw_cells_bound _ _ _ _ SLOT) as RB. cbn [cells_size csize] in RB.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L BT BS BP P0 [CEIL GLO] B63 [DL DB] [D8 T8]].
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    pose proof (aenv_ranges E s m OK HEAP) as (TR & SR & _).
    pose proof (el_root_elem E OK) as [EL NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (elem_word_range _ _ _ _ _ _ EL ltac:(lia) ltac:(lia) HSN) as TIR.
    assert (TTR : 0 <= ttype (ae_T E 1) < 256) by (unfold ttype; lia).
    destruct AI as (TB & SB & PB & DOCC). unfold el_root in ROOT. unfold GLOBALS_TOP in GLO.
    pose proof (munch_refl [(q - 192, q); (OUT, OUT + 24)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    apply (rw_cells_split_CB usegs _ _ [] 24 jo [] [8; 8; 4; 4]%nat) in SLOT; [| reflexivity]. cbn [mk_CB_cells app] in SLOT.
    hide TB. hide SB. hide PB.

    step. carve_frame 64%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 64 junk [] [8; 8; 4; 4; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    do 5 hstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    lazymatch goal with H : rw_cells usegs m1 (ae_DOC E) _ |- _ => rename H into DOCC1 end.
    Ltac tix i ra DOCC1 T8 := eapply (tix_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ae_DOC E) (ae_TAPE E) i ra [C8 (Z_to_bv 64 (ae_SBUF E))]);
      [exact DOCC1| lia| lia| lia| lia| exact T8| lia| lia| reflexivity| lia| reflexivity|].
    unhide TB.
    assert (TB1 : bytes_at usegs m1 (ae_TAPE E) (u64s (map (Z_to_bv 64) (ae_tws E))))
      by (eapply bytes_at_agree; [exact (agree_on_of_munch _ _ _ MU WM)| exact TB| rewrite u64s_length, length_map; intros a Ha; cbn [outside]; clear - Ha TR GLO CEIL LOLO LOQ QO; lia]).
    pose proof (tape_read_type m1 (ae_TAPE E) (ae_tws E) 1 TB1 ltac:(lia) TIR) as RTY. rewrite Z.mul_1_r in RTY.
    clear TB1. hide TB.

    step. step. step. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|]. clear K1.
    step. zstep. rewrite (land7_mod8 (ae_DOC E) ltac:(lia) D8). step. if_false.
    step. step. step. step. step.
    tix 1 0x3da64 DOCC1 T8.
    intros xa1 xa2 xa3 xa4. rewrite Z.mul_1_r.
    step. step. step. if_cases K2; zify_cond K2; rewrite acc_3da20_u8 in K2 by exact TTR.
    -
      clear RTY DOCC1. lazymatch goal with H : rw_cells usegs _ node _ |- _ => clear H end.
      step. if_cases K3; zify_cond K3; [exfalso; rewrite ?unsigned_lit in K3 by lia; lia|]. clear K3.
      step. hstep. hstep. hstep.
      step. step. step. step. step. step. release_frame FR ST q. step.
      apply evt_done. unfold acc_3da20_post. do 18 eexists. split; [cbv delta [mkR]; reflexivity|].
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [exact FRM|].
      do 4 eexists. split; [eassumption| right; left; reflexivity].
    -
      assert (K2' : ttype (ae_T E 1) = t_obj) by (unfold t_obj; exact K2).
      destruct (acc_3da20_obj E OK K2') as (d & e & c & TY & NXT & TILES & EN).
      step. step. hstep. hstep. hstep. step. step. step. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
      unhide TB. unhide SB. unhide PB. clear RTY.
      apply (bytes_at_agree _ _ _ _ _ (agree_on_of_munch _ _ _ MU WM)) in TB; [| rewrite u64s_length, length_map; intros a Ha; cbn [outside]; clear - Ha TR GLO CEIL LOLO LOQ QO; lia].
      apply (bytes_at_agree _ _ _ _ _ (agree_on_of_munch _ _ _ MU WM)) in SB; [| rewrite length_map; intros a Ha; cbn [outside]; clear - Ha SR GLO CEIL LOLO LOQ QO; lia].
      apply (bytes_at_agree _ _ _ _ _ (agree_on_of_munch _ _ _ MU WM)) in PB; [| rewrite length_map; intros a Ha; cbn [outside]; unfold zlength in KPL; clear - Ha KPL KP0 GLO CEIL LOLO LOQ QO; lia].
      lazymatch goal with H : rw_cells usegs m2 (ae_DOC E) _ |- _ => rename H into DOCC2 end.
      lazymatch goal with H : stk usegs m2 lo _ |- _ => rename H into ST2 end.
      lazymatch goal with H : mem_inv usegs m2 |- _ => rename H into MI2 end.
      apply (proj1 (rw_cells_app _ _ [_; _] _)) in FR. destruct FR as [N2C FRR].
      eapply evt_cut.
      { eapply (atkey_spec E OK d) with (lo := lo) (kb := map (Z_to_bv 8) (ae_p1 E)) (i := 1) (e := e) (c := c);
          [exact N2C| lia| lia| exact TB| exact SB| exact DOCC2| exact TY| exact NXT| exact TILES| lia| lia
          | exact PB| unfold zlength; rewrite length_map; reflexivity| exact KP0| unfold zlength in *; lia| left; unfold zlength in *; lia
          | left; unfold zlength in *; lia| exact SLOT| lia| lia| exact TR| exact SR| exact ST2| lia| exact LOLO| exact MI2| lia| lia]. }
      cbv beta. intros ms' PO. unfold atkey_post in PO.
      destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m3 & r0 & it & code & -> & MU3 & WM3 & MI3 & ST3 & OUTC & CODE).
      replace (ret_pc (Z_to_bv 64 252568)) with (Z_to_bv 64 252568) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (agree_on_of_munch _ _ _ MU3 WM3) as AG3.
      apply (rw_cells_agree _ _ _ _ _ AG3) in N2C; [| intros a Ha; cbn in Ha; cbn [outside]; lia].
      apply (rw_cells_agree _ _ _ _ _ AG3) in FRR; [| intros a Ha; cbn in Ha; cbn [outside]; lia].
      pose proof (proj2 (rw_cells_app _ _ _ _) (conj N2C FRR)) as FR. cbn [app] in FR. clear N2C FRR AG3.
      assert (MU' : munch [(q - 192, q); (OUT, OUT + 24)] m m3)
        by (eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU3]; unfold sub_fp; cbn [outside]; intros x Hx; lia]).
      assert (WM' : wmono usegs m m3) by (eapply wmono_trans; [exact WM| exact WM3]).
      clear MU WM MU3 WM3. rename MU' into MU. rename WM' into WM.
      clear TB SB PB DOCC2.
      step. step. step. step. step. step. step. release_frame FR ST3 q. step.
      apply evt_done. unfold acc_3da20_post. do 18 eexists. split; [cbv delta [mkR]; reflexivity|].
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [exact FRM|].
      do 4 eexists. split; [exact OUTC|].
      destruct CODE as [(-> & _)|(-> & _)]; [left; reflexivity| right; right; reflexivity].
  Qed.
End A3da20.
End WithCeiling0.
