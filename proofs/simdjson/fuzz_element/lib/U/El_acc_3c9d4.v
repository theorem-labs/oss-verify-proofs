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

Lemma acc_3c9d4_tval : forall o, 0 <= o < 2^56 -> Z.land (tword t_str o) 72057594037927935 = o.
Proof.
  intros o Ho. change 72057594037927935 with (Z.ones 56). rewrite Z.land_ones by (unfold tword, t_str; lia).
  unfold tword, t_str. rewrite Z.add_comm, Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma acc_3c9d4_u8 : forall x, 0 <= x < 256 -> bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 x))) = x.
Proof.
  intros x Hx. rewrite (Z_to_bv_unsigned 8 x). unfold bv_wrap. change (bv_modulus 8) with 256.
  rewrite Z.mod_small by lia. apply unsigned_lit. lia.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation ae_T E := (Tf (ae_tws E)).
Notation ae_S E := (Tf (ae_sbs E)).
Notation ae_n E := (Z.of_nat (length (ae_tws E))).
Notation ae_sn E := (Z.of_nat (length (ae_sbs E))).

Lemma acc_3c9d4_str : forall E, aenv_ok E -> ttype (ae_T E 1) = t_str ->
  exists o l, ae_T E 1 = tword t_str o /\ str_at (ae_S E) (ae_sn E) o l.
Proof.
  intros E OK HT. pose proof (el_root_elem E OK) as [EL NR].
  pose proof (el_elem_cases E _ _ _ OK EL) as CS. cbv zeta in CS.
  destruct CS as [[_ [H|[H|H]]]|[[_ [H|[H|H]]]|[(_ & (o & l & X & SA) & _)|(e & cv & He & Hj & Hcv & [H|H])]]];
    try (rewrite H in HT; rewrite ttype_tword in HT by lia;
         unfold t_str, t_true, t_false, t_null, t_i64, t_u64, t_dbl in HT; lia).
  - exists o, l. auto.
  - rewrite H, ttype_cword in HT by lia. unfold t_str, t_arr in HT. lia.
  - rewrite H, ttype_cword in HT by lia. unfold t_str, t_obj in HT. lia.
Qed.

Section A3c9d4.
  Variable E : aenv.
  Hypothesis OK : aenv_ok E.

  Definition acc_3c9d4_post (r : Z) (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (lo : Z) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
      ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom usegs)
      /\ munch [(q - 48, q); (r, r + 24)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo q /\ frm0 fc'
      /\ exists (j1 j2 : list byte) (err : Z), rw_cells usegs m' r [CB 16 j1; C4 (Z_to_bv 64 err); CB 4 j2]
           /\ 0 <= err < 64 /\ (err =? 0) = (ttype (ae_T E 1) =? t_str).

  Lemma acc_3c9d4_spec : forall (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (q node r : Z) (jr : list byte),
    AINV E m -> el_root E m node -> RHEAP s (ae_LB E) m -> mem_inv usegs m -> frm0 fc ->
    stk usegs m (ae_lo E) q -> ae_lo E <= q - 48 -> q <= node -> node + 16 <= ae_B E -> q <= ae_DOC E ->
    rw_cells usegs m r [CB 24 jr] -> q <= r ->
    evt usegs (acc_3c9d4_post r ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (ae_lo E) m)
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 r) (Z_to_bv 64 node) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x3c9d4) fc None m (seg_rom usegs)).
  Proof.
    intros until jr. intros AI ROOT HEAP MI FRM ST LOQ QN NB QD SLOT QR.
    pose proof (rw_cells_bound _ _ _ _ SLOT) as RB. cbn [cells_size csize] in RB.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L BT BS BP P0 [CEIL GLO] B63 [DL DB] [D8 T8]].
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    pose proof (aenv_ranges E s m OK HEAP) as ((T0 & TH) & (S0 & SH) & _).
    pose proof (el_root_elem E OK) as [EL NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (elem_word_range _ _ _ _ _ _ EL ltac:(lia) ltac:(lia) HSN) as TIR.
    destruct AI as (TB & SB & _ & DOCC). unfold el_root in ROOT. unfold GLOBALS_TOP in GLO.
    pose proof (munch_refl [(q - 48, q); (r, r + 24)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    hide TB. hide SB.

    step. carve_frame 48%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 48 junk [] [8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    do 5 hstep.
    unhide TB. unhide SB. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    apply (bytes_at_agree _ _ _ _ _ (agree_on_of_munch _ _ _ MU WM)) in TB; [| rewrite u64s_length, length_map; intros a Ha; cbn [outside]; clear - Ha T0 TH GLO CEIL LOQ QR; lia].
    apply (bytes_at_agree _ _ _ _ _ (agree_on_of_munch _ _ _ MU WM)) in SB; [| rewrite length_map; intros a Ha; cbn [outside]; clear - Ha S0 SH GLO CEIL LOQ QR; lia].
    pose proof (tape_read_type m1 (ae_TAPE E) (ae_tws E) 1 TB ltac:(lia) TIR) as RTY. rewrite Z.mul_1_r in RTY.
    pose proof (tape_read m1 (ae_TAPE E) (ae_tws E) 1 TB ltac:(lia)) as RDT. rewrite Z.mul_1_r in RDT.
    lazymatch goal with H : rw_cells usegs m1 (ae_DOC E) _ |- _ => rename H into DOCC1 end.
    Ltac tix i ra DOCC1 T8 := eapply (tix_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ae_DOC E) (ae_TAPE E) i ra [C8 (Z_to_bv 64 (ae_SBUF E))]);
      [exact DOCC1| lia| lia| lia| lia| exact T8| lia| lia| reflexivity| lia| reflexivity|].

    step. step. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|]. clear K1.
    step. zstep. rewrite (land7_mod8 (ae_DOC E) ltac:(lia) D8). step. if_false. step. step. step. step.
    tix 1 0x3ca10 DOCC1 T8.
    intros xa1 xa2 xa3 xa4. rewrite Z.mul_1_r.
    step. step. step. if_cases K2; zify_cond K2.
    all: assert (TTR : 0 <= ttype (ae_T E 1) < 256) by (unfold ttype; lia); rewrite acc_3c9d4_u8 in K2 by exact TTR.
    Ltac fin3 FRM SLOT := apply evt_done; unfold acc_3c9d4_post; do 18 eexists; split; [cbv delta [mkR]; reflexivity|];
      split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [exact FRM|];
      pose proof (rw_cells_merge usegs _ _ [] [C8 _; C8 _] [C4 _; CB 4 _] SLOT) as SLM; cbn [app cells_size csize Nat.add] in SLM;
      do 3 eexists; split; [exact SLM|].
    -
      clear TB SB RDT RTY DOCC1.
      lazymatch goal with H : rw_cells usegs _ node _ |- _ => clear H end.
      apply (rw_cells_split_CB usegs _ _ [] 24 jr [] [8; 8; 4; 4]%nat) in SLOT; [| reflexivity]. cbn [mk_CB_cells app] in SLOT.
      step. if_cases K3; zify_cond K3; [exfalso; rewrite ?unsigned_lit in K3 by lia; lia|]. clear K3.
      hstep. hstep. step. hstep.
      step. step. step. step. step. step. release_frame FR ST q. step.
      fin3 FRM SLOT. split; [lia|].
      replace (ttype (ae_T E 1) =? t_str) with false by (symmetry; apply Z.eqb_neq; unfold t_str; lia). reflexivity.
    -
      assert (K2' : ttype (ae_T E 1) = t_str) by (unfold t_str; exact K2).
      destruct (acc_3c9d4_str E OK K2') as (o & l & TY & SA).
      pose proof (str_at_bounds _ _ HSN _ _ SA) as (O0 & L0 & OL & LE & O56).
      rewrite TY in RDT.
      step. step. if_cases K3; zify_cond K3; [exfalso; rewrite ?unsigned_lit in K3 by lia; lia|]. clear K3.
      zstep. rewrite (land7_mod8 (ae_DOC E) ltac:(lia) D8). step. if_false. step. step.
      tix 1 0x3ca34 DOCC1 T8.
      intros ya1 ya2 ya3 ya4. rewrite Z.mul_1_r.
      step. step. if_cases K4; zify_cond K4; [exfalso; rewrite ?unsigned_lit in K4 by lia; lia|]. clear K4.
      zstep. rewrite (land7_mod8 (ae_DOC E) ltac:(lia) D8). step. if_false.
      step. step. if_cases K5; zify_cond K5; [exfalso; rewrite ?unsigned_lit in K5 by lia; lia|]. clear K5.
      step. step. astep. astep. rewrite acc_3c9d4_tval by lia. astep. astep.
      pose proof (sbuf_read1 m1 (ae_SBUF E) (ae_sbs E) o SB ltac:(lia)) as RB0.
      pose proof (sbuf_read1 m1 (ae_SBUF E) (ae_sbs E) (o + 1) SB ltac:(lia)) as RB1.
      pose proof (sbuf_read1 m1 (ae_SBUF E) (ae_sbs E) (o + 2) SB ltac:(lia)) as RB2.
      pose proof (sbuf_read1 m1 (ae_SBUF E) (ae_sbs E) (o + 3) SB ltac:(lia)) as RB3.
      assert (B0 : 0 <= ae_S E o < 256) by (unfold Tf; apply Forall_nth_Z; [exact SBS| lia]).
      assert (B1 : 0 <= ae_S E (o + 1) < 256) by (unfold Tf; apply Forall_nth_Z; [exact SBS| lia]).
      assert (B2 : 0 <= ae_S E (o + 2) < 256) by (unfold Tf; apply Forall_nth_Z; [exact SBS| lia]).
      assert (B3 : 0 <= ae_S E (o + 3) < 256) by (unfold Tf; apply Forall_nth_Z; [exact SBS| lia]).
      step. if_cases K6; zify_cond K6; [exfalso; rewrite ?unsigned_lit in K6 by lia; lia|]. clear K6.
      step. if_cases K7; zify_cond K7; [exfalso; rewrite ?unsigned_lit in K7 by lia; lia|]. clear K7.
      step. step. step.
      tix 1 0x3ca78 DOCC1 T8.
      intros za1 za2 za3 za4. rewrite Z.mul_1_r.
      step. step. if_cases K8; zify_cond K8; [exfalso; rewrite ?unsigned_lit in K8 by lia; lia|]. clear K8.
      zstep. rewrite (land7_mod8 (ae_DOC E) ltac:(lia) D8). step. if_false.
      step. step. astep. rewrite acc_3c9d4_tval by lia. astep.
      step. if_cases K9; zify_cond K9; [exfalso; rewrite ?unsigned_lit in K9 by lia; lia|]. clear K9.
      astep. astep. astep.
      replace (0 <? ae_SBUF E) with true by (symmetry; apply Z.ltb_lt; lia). replace (ae_SBUF E + o <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
      change (Z.lxor (Z.b2z true) (Z.b2z false)) with 1.
      step. if_false. step. if_cases K10; zify_cond K10; [exfalso; rewrite ?unsigned_lit in K10 by lia; lia|]. clear K10.
      step. if_cases K11; zify_cond K11; [exfalso; rewrite ?unsigned_lit in K11 by lia; lia|]. clear K11.
      step.
      step. step. step. step. astep. astep. astep. astep. astep. astep.
      rewrite !land64_shl_small by lia. rewrite le32_of_lbu4 by lia.
      change (ae_S E o + 2 ^ 8 * ae_S E (o + 1) + 2 ^ 16 * ae_S E (o + 2) + 2 ^ 24 * ae_S E (o + 3)) with (le32 (ae_S E) o). rewrite LE.
      clear TB SB RDT RTY DOCC1 RB0 RB1 RB2 RB3.
      repeat lazymatch goal with H : rw_cells usegs _ node _ |- _ => clear H end.
      apply (rw_cells_split_CB usegs _ _ [] 24 jr [] [8; 8; 4; 4]%nat) in SLOT; [| reflexivity]. cbn [mk_CB_cells app] in SLOT.
      hstep. hstep. step. hstep.
      step. step. step. step. step. step. release_frame FR ST q. step.
      fin3 FRM SLOT. split; [lia|]. rewrite K2'. reflexivity.
  Qed.
End A3c9d4.
End WithCeiling0.
