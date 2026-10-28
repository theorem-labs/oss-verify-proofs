(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface RAligned_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG PrintfModel PrintfModelX ApBase ApState CtSizes CtWire CtTime CtModel.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Printf_ctfmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit Printf_lib F_pop_arg F_printf_iface F_vsnprintf.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApWalkTac ApErrKit ApIface W_prefix_create W_obj_free W_obj_lookup W_asn1_string W_bio_push W_bio_write W_bio_printf W_snprintf.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnU Require Import MagicDiv PrnKit PrnLeaf PrnTimeIface W_sct_print_nv1 W_sct_print_A W_sct_print_B1.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

(* [comment removed for export] *)
Local Ltac xport H MU WM :=
  lazymatch type of MU with munch ?W ?ma ?mb => apply (rw_cells_transport ctusegs W ma mb) in H; [| exact MU| exact WM|] end.

(* [comment removed for export] *)
Lemma clo_split {CE__ : Ceiling} : forall m A clo, rw_cells ctusegs m A clo -> cells_size clo = 32%nat ->
  rw_cells ctusegs m A [CB 12%nat (firstn 12 (cells_bytes clo))] /\ rw_cells ctusegs m (A + 12) [CB 20%nat (skipn 12 (cells_bytes clo))].
Proof.
  intros m A clo H SZ.
  assert (LEN : length (cells_bytes clo) = 32%nat) by (destruct H as [[W _] _]; rewrite (cells_bytes_length clo W); exact SZ).
  assert (H' : rw_cells ctusegs m A ([CB 12%nat (firstn 12 (cells_bytes clo))] ++ [CB 20%nat (skipn 12 (cells_bytes clo))])).
  { eapply Lib_kit.rw_cells_recast; [exact H| | |].
    - cbn. rewrite firstn_length, skipn_length, LEN. cbn. tauto.
    - cbn [cells_bytes cbytes app]. rewrite app_nil_r. apply firstn_skipn.
    - cbn. rewrite SZ. reflexivity. }
  apply rw_cells_app in H'. destruct H' as [H1 H2]. cbn [cells_size csize Nat.add] in H2. replace (A + Z.of_nat 12) with (A + 12) in H2 by lia.
  split; [exact H1| exact H2].
Qed.

Section SPB. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Variables (sp gp : word) (m1 : mem) (s : PState) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z) (lo B : Z) (canary : word).
Variables (K KS : list block) (pbio : bptr) (out pv ts TSTK : Z).

Hypothesis LOB : lo <= bv_unsigned sp - 96 - Z.max 8320 TSTK.
Hypothesis SPB63 : bv_unsigned sp <= B /\ B < 2^63.
Hypothesis HBIN : In (pbio, out, BIO_SIZE) OW.
Hypothesis NI : ~ In pbio (es_ids st ++ env_ids E).
Hypothesis HK : frozen (forall b, In b K -> In b (OW ++ LB) /\ blk_id b <> pbio).
Hypothesis HKS : frozen (forall b, In b KS -> In b (OW ++ LB) /\ blk_id b <> pbio).
Hypothesis TSW : 0 <= ts < 2^64.
Hypothesis HM : rmalloc_stmt.
Hypothesis HF : rfree_stmt.
Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
Hypothesis T_ADJ_FAIL : gentime_adj_fail_stmt TSTK.
Hypothesis T_SETSTR_FAIL : gentime_setstr_fail_stmt TSTK.

Local Notation pb_invN := (pb_inv sp m1 s st OW LB E bo lo B canary K KS out pv).
Local Notation pb_step_munchN := (pb_step_munch sp m1 s st OW LB E bo lo B canary K KS pbio out pv ts TSTK LOB SPB63 HBIN NI HK HKS TSW).
Local Notation pb_step_nodeN := (pb_step_node sp m1 s st OW LB E bo lo B canary K KS pbio out pv ts TSTK LOB SPB63 HBIN NI HK HKS TSW).
Local Notation pb_openN := (pb_open sp m1 s st OW LB E bo lo B canary K KS pbio out pv ts TSTK LOB SPB63 HBIN NI HK HKS TSW).
Local Notation pb_blocksN := (pb_blocks sp m1 s st OW LB E bo lo B canary K KS pbio out pv ts TSTK LOB SPB63 HBIN NI HK HKS TSW).

(* [comment removed for export] *)
Lemma seg_B_fail : forall {X : Type} (x1 t0 t1 t2 a4 a5 a6 a7 x18 x19 x20 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
    (Fc : bvmap 5 word) (fc : bv 32) (s2 : PState) (m2 : mem) (errv2 : word) (clo : list cell) (nw : Z) (g : bptr) (G : Z)
    (k : lprog X) (Q : X -> PState -> machine_state -> Prop),
  pb_invN s2 m2 [(g, G, 24)] errv2 clo nw -> frm0 fc -> rblock_range G 24 ->
  rw_cells ctusegs m2 G (asn1_string_cells 0 V_ASN1_GENERALIZEDTIME 0 0) ->
  gentime_adj ts = None ->
  (forall (s3 : PState) (m3 : mem) (errv3 x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x21' t3' t4' t5' t6' : word) (Fc' : bvmap 5 word) (fc' : bv 32) (clo' : list cell),
     pb_invN s3 m3 [] errv3 clo' nw -> frm0 fc' -> sp_F Fc Fc' ->
     implM ctusegs (interp k) s3 Q
       (MS (mkR x1' (Z_to_bv 64 (bv_unsigned sp + -96)) gp (wz RATP) t0' t1' t2' sp (Z_to_bv 64 out) a0' a1' a2' a3' a4' a5' a6' a7'
                x18 x19 x20 x21' (Z_to_bv 64 ts) x23 x24 x25 x26 x27 t3' t4' t5' t6')
           Fc' (Z_to_bv 64 SCT_PRINT_TAIL) fc' None m3 (seg_rom ctusegs))) ->
  implM ctusegs (interp (LFree g k)) s2 Q
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp (wz RATP) t0 t1 t2 sp (Z_to_bv 64 out)
             (Z_to_bv 64 G) (Z_to_bv 64 0) (Z_to_bv 64 (ts_day ts)) (Z_to_bv 64 (ts_sec ts)) a4 a5 a6 a7
             x18 x19 x20 (Z_to_bv 64 G) (Z_to_bv 64 ts) x23 x24 x25 x26 x27 t3 t4 t5 t6)
        Fc (Z_to_bv 64 SCT_PRINT_ADJ) fc None m2 (seg_rom ctusegs)).
Proof using HBIN HF HK HKS LOB NI SP16 SPB63 TSW T_ADJ_FAIL T_SETSTR_FAIL.
  intros until Q. intros INV FRM BRG HG ADJ KONT.
  pose proof (pb_blocksN _ _ _ _ _ _ INV) as (OB0 & OB1 & OB2 & KSB & CEIL & GLO). unfold GLOBALS_TOP in GLO.
  pose proof (pb_openN _ _ _ _ _ _ INV) as (HEAP & AS & AUX & QB & B63 & ST & _ & _ & ERR & SSP & MI & CS & RS & NM & FRL & SZ & NW & HB).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; lia).
  pose proof BRG as (G0 & G16 & _ & GC & GI).
  assert (PRF : printable ts = false) by (unfold printable; rewrite ADJ; reflexivity).
  assert (HFC : sp_F Fc Fc) by (intros r Hr; reflexivity).
  unfold SCT_PRINT_ADJ, MallocRep.wz. unfold asn1_string_cells, MallocRep.wz in HG.
  pose proof (munch_refl [(lo, bv_unsigned sp + -96)] m2) as MU. pose proof (wmono_refl ctusegs m2) as WM.
  unfold implM. iprefix.
  (* [comment removed for export] *)
  zstep.
  eapply evt_cut.
  { eapply (T_ADJ_FAIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc fc m2 lo G ts canary);
      [rewrite ESP; exact ST| exact MI| unfold GLOBALS_TOP; lia| rewrite ESP; lia| rewrite ESP; clear - SP16; Z.div_mod_to_equations; lia| rewrite ESP; lia| exact SSP| reflexivity| exact FRM
      | unfold asn1_string_cells, MallocRep.wz; exact HG| lia| exact TSW| exact ADJ| reflexivity| reflexivity| reflexivity| reflexivity]. }
  cbv beta. unfold gentime_leaf_post. intros ms' PO. rewrite ?ESP in PO.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & -> & MU3 & WM3 & MI3 & ST3).
  replace (ret_pc (Z_to_bv 64 1694388)) with (Z_to_bv 64 1694388) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  assert (INV3 : pb_invN s2 m3 [(g, G, 24)] errv2 clo nw).
  { eapply (pb_step_munchN s2 m2 m3); [exact INV| exact MU3| exact WM3| | exact MI3| exact ST3| | exact SZ| exact NW|].
    - constructor; [left; cbn; lia| constructor].
    - eapply rw_cells_transport; [exact FRL| exact MU3| exact WM3| cbn [disjoint_from]; split; [right; lia| exact I]].
    - eapply rw_cells_transport; [exact HB| exact MU3| exact WM3| cbn [disjoint_from]; rewrite bio_cells_size; unfold BIO_SIZE; split; [left; clear - OB1 CEIL; lia| exact I]]. }
  xport HG MU3 WM3; [| cbn [disjoint_from cells_size csize Nat.add length]; split; [left; clear - GC CEIL; lia| exact I]].
  clear HEAP AS AUX ST ERR SSP MI CS RS NM FRL HB MU WM INV MU3 WM3 MI3 ST3. clear m2.
  pose proof (pb_openN _ _ _ _ _ _ INV3) as (HEAP & AS & AUX & _ & _ & ST & _ & _ & ERR & SSP & MI & CS & RS & NM & FRL & _ & _ & HB).
  pose proof (munch_refl [(lo, bv_unsigned sp + -96)] m3) as MU. pose proof (wmono_refl ctusegs m3) as WM.
  (* [comment removed for export] *)
  zstep. zstep.
  eapply evt_cut.
  { eapply (get0_data_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc fc m3 lo G 0 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 24)] [C8 (Z_to_bv 64 0)]);
      [rewrite ESP; exact ST| exact MI| unfold GLOBALS_TOP; lia| rewrite ESP; lia| exact (proj1 HG)| reflexivity| lia| clear - G16; Z.div_mod_to_equations; lia| lia| lia| reflexivity]. }
  cbv beta. unfold leaf16_post. intros ms' PO. rewrite ?ESP in PO.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & -> & MU4 & WM4 & MI4 & ST4).
  replace (ret_pc (Z_to_bv 64 1694396)) with (Z_to_bv 64 1694396) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  assert (INV4 : pb_invN s2 m4 [(g, G, 24)] errv2 clo nw).
  { eapply (pb_step_munchN s2 m3 m4); [exact INV3| exact MU4| exact WM4| | exact MI4| exact ST4| | exact SZ| exact NW|].
    - constructor; [left; cbn; lia| constructor].
    - eapply rw_cells_transport; [exact FRL| exact MU4| exact WM4| cbn [disjoint_from]; split; [right; lia| exact I]].
    - eapply rw_cells_transport; [exact HB| exact MU4| exact WM4| cbn [disjoint_from]; rewrite bio_cells_size; unfold BIO_SIZE; split; [left; clear - OB1 CEIL LOB; lia| exact I]]. }
  xport HG MU4 WM4; [| cbn [disjoint_from cells_size csize Nat.add length]; split; [left; clear - GC CEIL LOB; lia| exact I]].
  clear HEAP AS AUX ST ERR SSP MI CS RS NM FRL HB MU WM INV3 MU4 WM4 MI4 ST4. clear m3.
  pose proof (pb_openN _ _ _ _ _ _ INV4) as (HEAP & AS & AUX & _ & _ & ST & _ & _ & ERR & SSP & MI & CS & RS & NM & FRL & _ & _ & HB).
  destruct (magic_lits m4 MI) as [ML1 ML2]. unfold A_MAGIC1, A_MAGIC2 in ML1, ML2.
  pose proof (munch_refl [(lo, bv_unsigned sp + -96)] m4) as MU. pose proof (wmono_refl ctusegs m4) as WM.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  rewrite (ms_reg' ts) by exact TSW.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.
  destruct (clo_split m4 _ clo FRL SZ) as [FR12 FR20]. replace (bv_unsigned sp + -96 + 12) with (bv_unsigned sp + -84) in FR20 by lia.
  assert (MSR : 0 <= ts_ms ts < 1000) by (pose proof (ts_ms_range ts); lia).
  zstep. zstep.
  eapply evt_cut.
  { eapply (snprintf_gen_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc fc m4 (bv_unsigned sp + -84) 20 A_C18 lo 20%nat _ canary FMT_C18 [PA_sn; PA_i (ts_ms ts)] (ct_genstr_null (ts_ms ts)));
      [rewrite ESP; exact ST| exact MI| unfold GLOBALS_TOP; lia| rewrite ESP; unfold SNPRINTF_STACK, VSN_DEPTH; lia| rewrite ESP; lia| exact SSP| exact FRM
      | exact FR20| rewrite ESP; lia| unfold GLOBALS_TOP; lia| lia
      | rewrite (zlength_ct_genstr_null _ MSR); lia| lia
      | rewrite ESP; apply sng_C18_null; [exact MI| unfold STATIC_SPLIT; lia| exact MSR| reflexivity| rewrite unsigned_lit by lia; apply Z.mod_small; lia]
      | reflexivity| reflexivity| reflexivity]. }
  cbv beta. unfold sng_post. intros ms' PO. rewrite ?ESP in PO.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Fc5 & fc5 & m5 & -> & MU5 & WM5 & MI5 & FRM5 & FREG5 & ST5 & SSP5 & GEN5).
  replace (ret_pc (Z_to_bv 64 1694456)) with (Z_to_bv 64 1694456) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  rewrite (genstr_none ts ADJ) in GEN5.
  replace (bv_unsigned sp + -84 + Z.of_nat 20) with (bv_unsigned sp + -64) in MU5 by lia.
  xport FR12 MU5 WM5; [| cbn [disjoint_from cells_size csize Nat.add length]; clear -LOB; lia].
  assert (INV5 : pb_invN s2 m5 [(g, G, 24)] errv2 ([CB 12%nat (firstn 12 (cells_bytes clo))] ++ [CB 20%nat (zb (genstr ts) ++ Z_to_bv 8 0 :: skipn (S (length (genstr ts))) (skipn 12 (cells_bytes clo)))]) nw).
  { eapply (pb_step_munchN s2 m4 m5); [exact INV4| exact MU5| exact WM5| | exact MI5| exact ST5| | reflexivity| exact NW|].
    - constructor; [left; cbn; lia|]. constructor; [left; cbn; lia| constructor].
    - apply rw_cells_app. split; [exact FR12|]. cbn [cells_size csize Nat.add]. replace (bv_unsigned sp + -96 + Z.of_nat 12) with (bv_unsigned sp + -84) by lia. exact GEN5.
    - eapply rw_cells_transport; [exact HB| exact MU5| exact WM5| cbn [disjoint_from]; rewrite bio_cells_size; unfold BIO_SIZE; split; [left; clear - OB1 CEIL; lia| split; [left; clear - OB1 CEIL LOB; lia| exact I]]]. }
  xport HG MU5 WM5; [| cbn [disjoint_from cells_size csize Nat.add length]; split; [left; clear - GC CEIL; lia| split; [left; clear - GC CEIL LOB; lia| exact I]]].
  assert (HFC5 : sp_F Fc Fc5) by (intros r Hr; rewrite (FREG5 r Hr); reflexivity).
  clear HEAP AS AUX ST ERR SSP MI CS RS NM FRL HB MU WM INV4 MU5 WM5 MI5 ST5 SSP5 FR12 FR20 ML1 ML2. clear m4.
  pose proof (pb_openN _ _ _ _ _ _ INV5) as (HEAP & AS & AUX & _ & _ & ST & _ & _ & ERR & SSP & MI & CS & RS & NM & FRL & _ & _ & HB).
  pose proof (munch_refl [(lo, bv_unsigned sp + -96)] m5) as MU. pose proof (wmono_refl ctusegs m5) as WM.
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  eapply evt_cut.
  { eapply (T_SETSTR_FAIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc5 fc5 m5 lo G (bv_unsigned sp + -84) ts _ canary);
      [rewrite ESP; exact ST| exact MI| unfold GLOBALS_TOP; lia| rewrite ESP; lia| rewrite ESP; clear - SP16; Z.div_mod_to_equations; lia| rewrite ESP; lia| exact SSP| reflexivity| exact FRM5
      | exact PRF| exact TSW| exact GEN5| rewrite ESP; lia| lia| reflexivity| reflexivity]. }
  cbv beta. unfold gentime_leaf_post. intros ms' PO. rewrite ?ESP in PO.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m6 & -> & MU6 & WM6 & MI6 & ST6).
  replace (ret_pc (Z_to_bv 64 1694468)) with (Z_to_bv 64 1694468) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  assert (INV6 : pb_invN s2 m6 [(g, G, 24)] errv2 ([CB 12%nat (firstn 12 (cells_bytes clo))] ++ [CB 20%nat (zb (genstr ts) ++ Z_to_bv 8 0 :: skipn (S (length (genstr ts))) (skipn 12 (cells_bytes clo)))]) nw).
  { eapply (pb_step_munchN s2 m5 m6); [exact INV5| exact MU6| exact WM6| | exact MI6| exact ST6| | reflexivity| exact NW|].
    - constructor; [left; cbn; lia| constructor].
    - eapply rw_cells_transport; [exact FRL| exact MU6| exact WM6| cbn [disjoint_from]; split; [right; lia| exact I]].
    - eapply rw_cells_transport; [exact HB| exact MU6| exact WM6| cbn [disjoint_from]; rewrite bio_cells_size; unfold BIO_SIZE; split; [left; clear - OB1 CEIL; lia| exact I]]. }
  xport HG MU6 WM6; [| cbn [disjoint_from cells_size csize Nat.add length]; split; [left; clear - GC CEIL; lia| exact I]].
  clear HEAP AS AUX ST ERR SSP MI CS RS NM FRL HB MU WM INV5 MU6 WM6 MI6 ST6 GEN5. clear m5.
  pose proof (pb_openN _ _ _ _ _ _ INV6) as (HEAP & AS & AUX & _ & _ & ST & _ & _ & ERR & SSP & MI & CS & RS & NM & FRL & _ & _ & HB).
  pose proof (munch_refl [(lo, bv_unsigned sp + -96)] m6) as MU. pose proof (wmono_refl ctusegs m6) as WM.
  (* [comment removed for export] *)
  zstep. if_cases KS0; zify_cond KS0; [| exfalso; apply KS0; reflexivity]. try clear KS0.
  zstep. zstep.
  eapply (gentime_free_fwd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc5 fc5 m6 lo);
    [rewrite ESP; exact ST| exact MI| unfold GLOBALS_TOP; lia| rewrite ESP; lia|].
  intros m7 MU7 WM7 MI7 ST7. rewrite ?ESP in *.
  assert (INV7 : pb_invN s2 m7 [(g, G, 24)] errv2 ([CB 12%nat (firstn 12 (cells_bytes clo))] ++ [CB 20%nat (zb (genstr ts) ++ Z_to_bv 8 0 :: skipn (S (length (genstr ts))) (skipn 12 (cells_bytes clo)))]) nw).
  { eapply (pb_step_munchN s2 m6 m7); [exact INV6| exact MU7| exact WM7| | exact MI7| exact ST7| | reflexivity| exact NW|].
    - constructor; [left; cbn; lia| constructor].
    - eapply rw_cells_transport; [exact FRL| exact MU7| exact WM7| cbn [disjoint_from]; split; [right; lia| exact I]].
    - eapply rw_cells_transport; [exact HB| exact MU7| exact WM7| cbn [disjoint_from]; rewrite bio_cells_size; unfold BIO_SIZE; split; [left; clear - OB1 CEIL LOB; lia| exact I]]. }
  xport HG MU7 WM7; [| cbn [disjoint_from cells_size csize Nat.add length]; split; [left; clear - GC CEIL LOB; lia| exact I]].
  clear HEAP AS AUX ST ERR SSP MI CS RS NM FRL HB MU WM INV6 MU7 WM7 MI7 ST7. clear m6.
  pose proof (pb_openN _ _ _ _ _ _ INV7) as (HEAP & AS & AUX & _ & _ & ST & _ & _ & ERR & SSP & MI & CS & RS & NM & FRL & _ & _ & HB).
  ihere.
  lazymatch goal with |- impl ?segs _ (?c ?st0) (epost ?EE) ?ms =>
    lazymatch EE with (fun p => ?QQ (fst p) (snd p)) => change (implM segs c st0 QQ ms) end end.
  pose proof (LH_nodup _ _ _ HEAP) as ND7.
  eapply (ASN1_STRING_free_nodata_walk HF) with (B := B) (lo := lo) (errv := errv2) (L := [(g, G, 24)] ++ OW ++ LB) (pblk := g) (A := G) (len := 0) (ty := V_ASN1_GENERALIZEDTIME);
    [exact HEAP| exact AUX| rewrite ESP; lia| rewrite ESP; exact ST| exact CEIL| unfold GLOBALS_TOP; lia
    | rewrite ESP; unfold ASN1_STRING_FREE_STACK, CRYPTO_FREE_STACK, RFREE_STACK; lia
    | exact ERR| exact MI| reflexivity| exact CS| left; reflexivity| unfold asn1_string_cells, MallocRep.wz; exact HG| reflexivity|].
  intros s8 ms8 PO. unfold vfree_post in PO. rewrite ?ESP in PO.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m8 & -> & MI8 & ST8 & ERR8 & AUX8 & HP8 & FA8 & SO8 & HEAP8 & _).
  cbn [app] in HP8, HEAP8. rewrite (lb_remove_hd g G 24 (OW ++ LB) ND7) in HP8, HEAP8.
  unfold LX_ERRNO, RATP in ERR8. change (3355176 - 164) with 3355012 in ERR8.
  assert (INV8 : pb_invN s8 m8 [] errv2 ([CB 12%nat (firstn 12 (cells_bytes clo))] ++ [CB 20%nat (zb (genstr ts) ++ Z_to_bv 8 0 :: skipn (S (length (genstr ts))) (skipn 12 (cells_bytes clo)))]) nw).
  { eapply (pb_step_nodeN s2 s8 m7 m8 [(g, G, 24)] []); [exact INV7| exact HP8| cbn [app]; exact HEAP8| exact MI8| exact ST8| exact ERR8| exact AUX8| exact SO8| exact FA8]. }
  unfold SCT_PRINT_TAIL, MallocRep.wz in KONT.
  replace (ret_pc (Z_to_bv 64 1694492)) with (Z_to_bv 64 1694492) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  eapply KONT; [exact INV8| exact FRM5| exact HFC5].
Qed.

End SPB.
