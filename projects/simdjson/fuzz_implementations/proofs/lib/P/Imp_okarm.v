(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel PjModel ImpModel Target Prog PjImpl ImpImpl.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjS1Out SjTape SjTapeList SjTapeTile SjPjSer.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Layout Exit Printf_wfile Str_tac Startup_glue Pj_loc_defs Pj_loc_kit Pj_loc_get Pj_os_kit Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit Sj_stage1_kit Sj_stage2_iface F_memset Pj_kit Pj_defs Pj_stmts Imp_defs Imp_iface Imp_oss_defs Imp_str_grow Imp_sb_overflow Imp_xsputn Imp_put Imp_oss_ctor Imp_str Imp_oss_dtor.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
Ltac PROBEH := try (match goal with H : ?T |- _ => lazymatch T with rw_cells _ _ _ _ => idtac H ":" T | munch _ _ _ => idtac H ":" T | stk _ _ _ _ => idtac H ":" T | agree_on _ _ _ => idtac H ":" T | _ => fail end; fail end).
Ltac PROBE := PROBEH; match goal with |- evt _ _ (MS ?r _ ?pc _ _ ?m _) => idtac "PC:" pc "MEM:" m; idtac "REGS:" r | |- ?g => idtac "GOAL:" g end; fail "PROBE".

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma lb_below : forall s LB m a, RHEAP s LB m -> in_block LB a -> 0 < a < alloc_ceiling /\ (a < 0x10000 \/ 0x10b000 <= a).
Proof.
  intros s LB m a H (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ H Hb) as (R1 & R2 & R3 & R4 & R5).
  unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in R4. lia.
Qed.

Lemma DOCREP_agree : forall (P : Z -> Prop) m m' LB0 DOC TAPE SBUF len tws sbs,
  agree_on P m m' -> (forall a, DOC <= a < DOC + 16 -> P a) -> (forall a, in_block LB0 a -> P a) ->
  DOCREP m LB0 DOC TAPE SBUF len tws sbs -> DOCREP m' LB0 DOC TAPE SBUF len tws sbs.
Proof.
  intros P m m' LB0 DOC TAPE SBUF len tws sbs AG HD HB (D1 & D2 & D3 & D4 & D5 & D6 & D7 & (bt & Bt1 & Bt2 & Bt3) & (bq & Bq1 & Bq2 & Bq3)).
  split. { eapply rw_cells_agree; [exact AG| exact D1|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply HD. lia. }
  split. { eapply bytes_at_agree; [exact AG| exact D2|]. intros a Ha. rewrite u64s_length, length_map in Ha. apply HB. exists bt. split; [exact Bt1| cbn in *; lia]. }
  split. { eapply bytes_at_agree; [exact AG| exact D3|]. intros a Ha. rewrite length_map in Ha. apply HB. exists bq. split; [exact Bq1| cbn in *; lia]. }
  split; [exact D4|]. split; [exact D5|]. split; [exact D6|]. split; [exact D7|].
  split; [exists bt; auto| exists bq; auto].
Qed.

Definition okX (q : Z) : list (Z * Z) := [(q + 40, q + 304); (q + 392, q + 440); (q + 848, q + 936)].

Lemma okX_weaken : forall LB q m m', lx_pres LB q (okX q) m m' -> lx_pres LB q (imp_okarm_X q) m m'.
Proof.
  intros LB q m m' H. eapply lx_pres_weaken; [exact H| lia| intros b Hb; exact Hb|].
  intros a Ha. unfold okX, imp_okarm_X in *. cbn [rin_ivs fst snd] in *. tauto.
Qed.

Lemma sj_statics_along : forall LB q m m', alloc_ceiling <= q ->
  lx_pres LB q (okX q) m m' -> sj_statics m true -> sj_statics m' true.
Proof.
  intros LB q m m' HQ PR SJ. eapply sj_statics_agree; [exact (agree_of_lx_pres _ _ _ _ _ PR)| | exact SJ].
  intros a Ha. apply sjs_addr_client; [exact Ha|]. unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha. unfold okX. cbn [rin_ivs fst snd]. lia.
Qed.
Lemma pj_consts_along : forall LB q m m', alloc_ceiling <= q ->
  lx_pres LB q (okX q) m m' -> pj_consts m -> pj_consts m'.
Proof.
  intros LB q m m' HQ PR PC. eapply pj_consts_agree; [exact (agree_of_lx_pres _ _ _ _ _ PR)| | exact PC].
  intros a Ha. apply lxs_addr_client; [unfold lxs_addr; tauto|]. unfold okX. cbn [rin_ivs fst snd]. lia.
Qed.

Lemma in_block_app_r : forall X LB a, in_block LB a -> in_block (X ++ LB) a.
Proof. intros X LB a (b & Hb & Hr). exists b. split; [apply in_app_iff; right; exact Hb| exact Hr]. Qed.
Lemma in_block_app_l : forall LB X a, in_block LB a -> in_block (LB ++ X) a.
Proof. intros LB X a (b & Hb & Hr). exists b. split; [apply in_app_iff; left; exact Hb| exact Hr]. Qed.

Lemma STRREP_agree : forall (P : Z -> Prop) m m' O st,
  agree_on P m m' -> (forall a, O + 72 <= a < O + 96 -> P a) -> (forall a, in_block (osblocks st) a -> P a) ->
  STRREP m O st -> STRREP m' O st.
Proof.
  intros P m m' O st AG HO HB H. unfold STRREP, osblocks in *. destruct (os_blk st) as [b|].
  - destruct H as (H1 & (bs & H2) & H3). split; [| split; [| exact H3]].
    + eapply rw_cells_agree; [exact AG| exact H1|]. intros a Ha. cbn in Ha. apply HO. lia.
    + exists bs. eapply rw_cells_agree; [exact AG| exact H2|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
      pose proof H3 as (_ & _ & Hn & _). rewrite Nat.add_0_r, Z2Nat.id in Ha by exact Hn. apply HB.
      exists (b, os_data st, os_cap st). split; [left; reflexivity| cbn; lia].
  - destruct H as (H1 & (bs & H2) & H3). split; [| split; [| exact H3]].
    + eapply rw_cells_agree; [exact AG| exact H1|]. intros a Ha. cbn in Ha. apply HO. lia.
    + exists bs. eapply rw_cells_agree; [exact AG| exact H2|]. intros a Ha. cbn in Ha. apply HO. lia.
Qed.

Lemma PUTCELLS_agree : forall (P : Z -> Prop) m m' O st,
  agree_on P m m' -> (forall a, O <= a < O + 264 -> P a) -> PUTCELLS m O st -> PUTCELLS m' O st.
Proof.
  intros P m m' O st AG HO (H1 & (hm & H2 & H3) & (j & H4)). split; [| split].
  - eapply rw_cells_agree; [exact AG| exact H1|]. intros a Ha. rewrite sb_cellsI_size in Ha. apply HO. lia.
  - exists hm. split; [| exact H3]. eapply rw_cells_agree; [exact AG| exact H2|]. intros a Ha. cbn in Ha. apply HO. lia.
  - exists j. eapply rw_cells_agree; [exact AG| exact H4|]. intros a Ha. cbn in Ha. apply HO. lia.
Qed.

Lemma SBINVo_agree : forall (P : Z -> Prop) m m' O len st,
  agree_on P m m' -> (forall a, O <= a < O + 264 -> P a) -> (forall a, in_block (osblocks st) a -> P a) ->
  SBINV m O len st -> SBINV m' O len st.
Proof.
  intros P m m' O len st AG HO HB (H1 & H2 & H3). split; [| split; [| exact H3]].
  - eapply PUTCELLS_agree; eassumption.
  - eapply STRREP_agree; [exact AG| intros a Ha; apply HO; lia| exact HB| exact H2].
Qed.

Lemma IOSINV_agree : forall (P : Z -> Prop) m m' O fill,
  agree_on P m m' -> (forall a, O <= a < O + 264 -> P a) -> IOSINV m O fill -> IOSINV m' O fill.
Proof.
  intros P m m' O fill AG HO (H1 & j1 & j2 & H2). split.
  - eapply rw_cells_agree; [exact AG| exact H1|]. intros a Ha. cbn in Ha. apply HO. lia.
  - exists j1, j2. eapply rw_cells_agree; [exact AG| exact H2|]. intros a Ha. rewrite ios_cellsI_size in Ha. apply HO. lia.
Qed.

Lemma OSSINV_agree : forall (P : Z -> Prop) m m' O len st fill,
  agree_on P m m' -> (forall a, O <= a < O + 264 -> P a) -> (forall a, in_block (osblocks st) a -> P a) ->
  OSSINV m O len st fill -> OSSINV m' O len st fill.
Proof.
  intros P m m' O len st fill AG HO HB [H1 H2]. split; [eapply SBINVo_agree; eassumption| eapply IOSINV_agree; eassumption].
Qed.

Lemma SBINVb_agree : forall (P : Z -> Prop) m m' SB len st,
  agree_on P m m' -> (forall a, SB <= a < SB + 88 -> P a) -> (forall a, in_block (sbblocks st) a -> P a) ->
  Pj_defs.SBINV m SB len st -> Pj_defs.SBINV m' SB len st.
Proof.
  intros P m m' SB len st AG HO HB (H1 & H2 & (bs & H3) & (ji & H4) & H5 & H6 & H7).
  split. { eapply rw_cells_agree; [exact AG| exact H1|]. intros a Ha. cbn in Ha. apply HO. lia. }
  split; [exact H2|].
  split. { exists bs. eapply rw_cells_agree; [exact AG| exact H3|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. rewrite Nat.add_0_r, Z2Nat.id in Ha by lia.
           unfold sbblocks in HB. destruct (sb_blk st) as [b|].
           - apply HB. exists (b, sb_buf st, sb_cap st). split; [left; reflexivity| cbn; lia].
           - destruct H7 as (E1 & E2 & _). apply HO. lia. }
  split. { exists ji. eapply rw_cells_agree; [exact AG| exact H4|]. intros a Ha. cbn in Ha. apply HO. lia. }
  split; [exact H5|]. split; [exact H6| exact H7].
Qed.

Definition okarm_setup_post (q : Z) (gp s0 s1 s2 s3 s4 s5 s8 s9 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo len : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x3ef40) (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1
                  (Z_to_bv 64 (q + 848)) (Z_to_bv 64 (q + 336)) (Z_to_bv 64 1) a3 a4 a5 a6 a7 s2 s3 s4 s5
                  (Z_to_bv 64 (q + 336)) (Z_to_bv 64 1) s8 s9 (Z_to_bv 64 (q + 304)) s11 t3 t4 t5 t6)
             F (Z_to_bv 64 PJ_APPEND_ELEM) fc None m' (seg_rom psegs)
    /\ munch [(q - 224, q); (q + 40, q + 304); (q + 392, q + 416); (q + 848, q + 936)] m m'
    /\ wmono psegs m m' /\ mem_inv psegs m' /\ stk psegs m' lo q
    /\ OSSINV m' (q + 40) len (oss0 (q + 40)) 0xFFFFFFFF /\ LOCB m'
    /\ Pj_defs.SBINV m' (q + 848) len (sb0 (q + 848))
    /\ (exists jerr, rw_cells psegs m' (q + 392) [C8 (Z_to_bv 64 (q + 336)); C8 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); CB 4 jerr]).

Lemma okarm_setup : forall x1 gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (q lo len : Z) (j20 jgap jel jsb : list byte),
  stk psegs m lo q -> GLOBALS_TOP <= lo -> lo <= q - 224 -> q + 1040 < 2^62 ->
  LOCB m -> imp_vt_rows m -> mem_inv psegs m ->
  rw_cells psegs m (q + 40) [C8 (Z_to_bv 64 (q + 336)); C8 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); CB 4 j20] ->
  rw_cells psegs m (q + 64) [CB 240 jgap] ->
  rw_cells psegs m (q + 392) [CB 24 jel] ->
  rw_cells psegs m (q + 848) [CB 88 jsb] ->
  0 <= len <= SJ_PADMAX ->
  evt psegs (okarm_setup_post q gp s0 s1 s2 s3 s4 s5 s8 s9 s11 F fc lo len m)
    (MS (mkR x1 (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 (q + 304)) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 IMP_OKARM) fc None m (seg_rom psegs)).
Proof.
  intros until jsb. intros ST GLO LO Q62 LB VT MI SRET GAP JEL SBA LEN.
  unfold IMP_OKARM, SJ_PADMAX, GLOBALS_TOP in *.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  destruct LB as (l1 & l2 & l3 & l4 & l5 & l6 & l7 & l8 & l9 & l10 & l11 & l12 & l13 & l14 & l15 & LBC). hide LBC.
  pose proof (munch_refl [(q - 224, q); (q + 40, q + 304); (q + 392, q + 416); (q + 848, q + 936)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.

  lstep. lstep. replace (Z_to_bv 64 (q + 304 + 88)) with (Z_to_bv 64 (q + 392)) by (f_equal; lia) || idtac.
  lstep. lstep. lstep. try fix_lit_store. lstep. lstep.

  pose proof (rw_cells_join _ _ _ _ _ SRET GAP ltac:(cbn [app cells_size csize Nat.add]; lia)) as OSR. cbn [app] in OSR. clear SRET GAP.
  merge_at OSR 0%nat 5%nat. lazymatch type of OSR with context [CB 264 ?x] => set (jkO := x) in OSR; clearbody jkO end.
  call (oss_ctor_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ q lo (q + 40) len _);
    [exact ST| unfold GLOBALS_TOP; lia| unfold OSS_CTOR_STACK; lia| lia| lia| lia| exact OSR
    | eapply imp_vt_rows_transport; [exact VT| exact MU| exact WM| cbv [disjoint_from fst snd]; repeat split; lia]
    | exists l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15; unhide LBC;
      eapply rw_cells_agree; [exact (agree_on_of_munch _ _ _ MU WM)| exact LBC| intros a Ha; rewrite locb_cells_size in Ha; cbn [outside]; lia]
    | assumption| lia|].
  rename PC into ST1. rename PC0 into OSS1. rename POST into LB1. clear LBC.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  lazymatch goal with H : rw_cells _ m1 (q + 392) _ |- _ => rename H into ELC end.
  pose proof (munch_refl [(q + 848, q + 936)]%Z m1) as MU0. pose proof (wmono_refl psegs m1) as WM0.
  assert (OSSk : keepP (OSSINV m1 (q + 40) len (oss0 (q + 40)) 4294967295)) by exact OSS1. clear OSS1.
  assert (LBk : keepP (LOCB m1)) by exact LB1. clear LB1.

  lstep. lstep. lstep. lstep. lstep. lstep.
  apply (rw_cells_split_CB psegs _ _ [] 88 jsb [] [64;8;8;8]%nat) in SBA; [|reflexivity]. cbn [mk_CB_cells app] in SBA. forget_junk SBA.
  takeZ SBA 1%nat (q + 912) INL. rename SBA into SBW.
  call memset_callZ; [exact INL| assumption| lia| lia| lia| lia|]. rename POST into INL. change (Z.to_nat 64) with 64%nat in INL.
  lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI2 end.

  lstep. lstep. lstep. try fix_lit_store. lstep. lstep. try fix_lit_store. lstep. lstep. lstep. lstep.
  lazymatch goal with H : rw_cells _ _ (q + 912) _ |- _ => rename H into SBUF0 end.
  lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI3 end.
  apply evt_done. unfold okarm_setup_post. do 13 eexists.
  split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact ST1|].
  split. { unhide OSSk. eapply (OSSINV_agree _ m1); [exact (agree_on_of_munch _ _ _ MU0 WM0)| | | exact OSSk].
           - intros a Ha. cbn [outside fst snd]. lia.
           - intros a (b & Hb & _). cbn [osblocks oss0 os_blk] in Hb. destruct Hb. }
  split. { unhide LBk. eapply LOCB_transport; [exact LBk| exact MU0| exact WM0| cbv [disjoint_from fst snd]; repeat split; lia]. }
  split.
  { unfold Pj_defs.SBINV, sb0. cbn [sb_buf sb_size sb_cap sb_blk sb_fuel]. replace (q + 848 + 64) with (q + 912) by lia.
    split; [exact SBUF0|]. split; [lia|]. split; [eexists; exact INL|]. split; [eexists; exact INL|]. split; [apply le_n|].
    split; [| repeat split; reflexivity].
    replace (64 * 2 ^ sb_k _) with 64 by reflexivity. unfold PJ_CAPMAX, PJ_OUTMAX. lia. }
  eexists. exact ELC.
Qed.

Lemma low_bit_roundtrip : forall (x : Z) (l : list byte),
  Z.land (bv_unsigned (Z_to_bv 8 (bv_unsigned (bv_extract 0 64 (le_bytes_to_word (Z_to_bv 8 x :: l)))))) 1 = Z.land x 1.
Proof.
  intros x l. rewrite !Z_to_bv_unsigned. rewrite bv_extract_unsigned. unfold le_bytes_to_word. rewrite Z_to_bv_unsigned.
  cbn [bytes_le_to_Z]. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Z.shiftr_0_r.
  apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
  destruct (Z.eq_dec i 0) as [->|NE].
  - change (Z.testbit 1 0) with true. rewrite !andb_true_r.
    change (bv_modulus 8) with (2^8). change (bv_modulus 64) with (2^64).
    rewrite !Z.mod_pow2_bits_low by lia. rewrite Z.lor_spec, Z.shiftl_spec by lia. rewrite Z.mod_pow2_bits_low by lia.
    rewrite (Z.testbit_neg_r _ (0 - 8)) by lia. rewrite orb_false_r. reflexivity.
  - replace (Z.testbit 1 i) with false; [rewrite !andb_false_r; reflexivity|].
    destruct (Z.eq_dec i 0); [lia|]. rewrite Z.bits_above_log2; [reflexivity| lia| cbn; lia].
Qed.

Definition imp_res (m : mem) (R : Z) (ocp : option block) (L : Z) : Prop :=
  match ocp with
  | None => exists bs, rw_cells psegs m R [C1 (Z_to_bv 8 (2 * L)); CB 23 bs]
  | Some b => rw_cells psegs m R [C8 (Z_to_bv 64 (blk_size b + 1)); C8 (Z_to_bv 64 L); C8 (Z_to_bv 64 (blk_addr b))]
              /\ blk_size b mod 2 = 0 /\ 0 < blk_size b < 2^32 /\ rblock_range (blk_addr b) (blk_size b)
  end.

Lemma imp_out_agree : forall (P : Z -> Prop) m m' q ocp,
  agree_on P m m' -> (forall a, q + 416 <= a < q + 440 -> P a) -> imp_out m q ocp -> imp_out m' q ocp.
Proof.
  intros P m m' q [b|] AG HP H; unfold imp_out in *.
  - destruct H as (L & H1 & H2). exists L. split; [| exact H2]. eapply rw_cells_agree; [exact AG| exact H1|]. intros a Ha. cbn in Ha. apply HP. lia.
  - destruct H as (b0 & j23 & H1 & H2). exists b0, j23. split; [| exact H2]. eapply rw_cells_agree; [exact AG| exact H1|]. intros a Ha. cbn in Ha. apply HP. lia.
Qed.

Definition okarm_move_post (x1 : word) (q : Z) (gp s0 s1 s2 s3 s5 s6 s7 s8 s9 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (ocp : option block) (fill : Z) (j124 j260 : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR x1 (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 OSS_OS_VPTR) s5 s6 s7 s8 s9 (Z_to_bv 64 (q + 304)) s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x3efbc) fc None m' (seg_rom psegs)
    /\ munch [(q + 40, q + 48); (q + 152, q + 160); (q + 416, q + 440)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ rw_cells psegs m' (q + 40) [C8 (Z_to_bv 64 OSS_OS_VPTR)]
    /\ rw_cells psegs m' (q + 152) (ios_cellsI (q + 40) fill j124 j260)
    /\ imp_out m' q ocp
    /\ (exists bs, rw_cells psegs m' (q + 848) [CB 24 bs]).

Lemma okarm_move : forall x1 gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (q : Z) (v0 : word) (ocp : option block) (L fill : Z) (j124 j260 : list byte),
  0x10b000 <= q -> q + 1040 < 2^62 -> mem_inv psegs m ->
  rw_cells psegs m (q + 24) [C8 (Z_to_bv 64 OSS_SB_VPTR); C8 (Z_to_bv 64 OSS_IOS_VPTR)] ->
  rw_cells psegs m (q + 40) [C8 v0] ->
  rw_cells psegs m (q + 152) (ios_cellsI (q + 40) fill j124 j260) ->
  rw_cells psegs m (q + 416) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  imp_res m (q + 848) ocp L -> 0 <= L ->
  rw_cells psegs m OSS_VBOFF [C8 (Z_to_bv 64 0x70)] ->
  evt psegs (okarm_move_post x1 q gp s0 s1 s2 s3 s5 s6 s7 s8 s9 s11 F fc ocp fill j124 j260 m)
    (MS (mkR x1 (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 OSS_OS_VPTR) s5 s6 s7 s8 s9 (Z_to_bv 64 (q + 304)) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3ef70) fc None m (seg_rom psegs)).
Proof.
  intros until j260. intros Q0 Q62 MI V24 OSV IOSC OUT RES L0 VB.
  unfold ios_cellsI in *. unfold OSS_OS_VPTR, OSS_SB_VPTR, OSS_IOS_VPTR, OSS_VBOFF, OSS_CLASSIC in *.
  pose proof (munch_refl [(q + 40, q + 48); (q + 152, q + 160); (q + 416, q + 440)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.

  pose proof (rw_cells_C8_read1_g psegs m _ _ _ OUT) as RD. rewrite unsigned_lit in RD by lia.
  replace (q + 416) with (q + 304 + 112) in RD by lia.
  lstep. lstep. rewrite ?zxb_u. change (Z.land (0 mod 256) 1) with 0. lstep. if_true. clear RD.

  destruct ocp as [b|].
  - destruct RES as (RES & EV & SZ & RB).
    lstep. lstep. lstep. lstep. lstep. lstep.
    lazymatch goal with H : rw_cells _ _ (q + 304 + 112) _ |- _ => rename H into OUT2 end || idtac.

    lstep. lstep. lstep. lstep. lstep. replace (Z_to_bv 64 (q + 40 + 112)) with (Z_to_bv 64 (q + 152)) by (f_equal; lia). lstep.
    apply evt_done. unfold okarm_move_post. do 16 eexists.
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    split; [assumption|]. split; [unfold ios_cellsI, OSS_IOS_VPTR, OSS_CLASSIC; assumption|].
    split.
    + unfold imp_out. exists L. split; [| split; [rewrite land1_mod2; Z.div_mod_to_equations; lia| split; [exact SZ| exact RB]]].
      unfold out_long. lazymatch goal with H : rw_cells _ _ _ [C8 _; C8 _; C8 _] |- rw_cells _ ?mx (q + 416) _ =>
        lazymatch type of H with rw_cells _ mx ?A _ => replace (q + 416) with A by lia; exact H end end.
    + apply rw_cells_forget in RES. destruct RES as [bs RES]. exists bs. exact RES.
  - destruct RES as [bs RES].
    merge_at RES 0%nat 2%nat.
    apply (rw_cells_split_CB psegs _ _ [] 24 _ [] [8;8;8]%nat) in RES; [|reflexivity]. cbn [mk_CB_cells app cells_bytes cbytes firstn skipn] in RES.

    lazymatch type of RES with rw_cells _ _ _ [CB 8 ?l0; CB 8 ?l1; CB 8 ?l2] =>
      remember l0 as k0 eqn:EK0 in RES; set (k1 := l1) in RES; set (k2 := l2) in RES; clearbody k1 k2 end.
    lstep. lstep. lstep. lstep. lstep. lstep.

    lstep. lstep. lstep. lstep. lstep. replace (Z_to_bv 64 (q + 40 + 112)) with (Z_to_bv 64 (q + 152)) by (f_equal; lia). lstep.
    apply evt_done. unfold okarm_move_post. do 16 eexists.
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    split; [assumption|]. split; [unfold ios_cellsI, OSS_IOS_VPTR, OSS_CLASSIC; assumption|].
    split.
    + unfold imp_out. lazymatch goal with H : rw_cells _ _ _ [C8 ?w0; C8 ?w1; C8 ?w2] |- exists b0 j23, rw_cells _ ?mx (q + 416) _ /\ _ =>
        lazymatch type of H with rw_cells _ mx ?A _ =>
        exists (Z_to_bv 8 (bv_unsigned w0)), (List.tl (le8 w0) ++ le8 w1 ++ le8 w2); split;
          [ unfold out_short; replace (q + 416) with A by lia; eapply rw_cells_retype;
            [exact H| cbn [cells_wf cell_wf le8 word_to_le_bytes Z_to_le_bytes List.tl app length]; repeat split; reflexivity
            | cbn [cells_bytes cbytes le8 word_to_le_bytes Z_to_le_bytes List.tl app]; reflexivity| reflexivity]
          | rewrite EK0, low_bit_roundtrip; apply short_byte0 ] end end.
    + lazymatch goal with H : rw_cells _ ?mx (q + 848) _ |- _ => apply rw_cells_forget in H; destruct H as [bs' H]; exists bs'; exact H end.
Qed.

Lemma okarm_fin : forall {A} (k : option bptr -> M PState A) (Q : A -> PState -> machine_state -> Prop)
    (x1 gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m00 m : mem) (s00 s : PState) (LBall : list block) (q lo B : Z) (errv : word) (ocp : option block)
    (v0 v1 : word) (jA j392 j848 j124 j260 : list byte) (fill : Z),
  (forall cpy s' ms', imp_okarm_post q gp s0 s1 s2 s3 (Z_to_bv 64 IMP_OS_VPTR) (Z_to_bv 64 (IMP_VTT + 8)) (Z_to_bv 64 IMP_SBB_VPTR) s9 (Z_to_bv 64 (q + IMP_IMPLS)) s11
                         s00 LBall lo B m00 cpy s' ms' -> implM psegs (k cpy) s' Q ms') ->
  frm0 fc -> mem_inv psegs m -> stk psegs m lo q -> rw_cells psegs m LX_ERRNO [C4 errv] -> rauxv_ok m B ->
  ps_fa s = ps_fa s00 -> ps_so s = ps_so s00 -> RHEAP s (ocp_blocks ocp ++ LBall) m ->
  lx_pres LBall q (okX q) m00 m -> sj_statics m00 true ->
  rw_cells psegs m (q + 40) [C8 v0; C8 v1; C8 (Z_to_bv 64 OSS_CLASSIC); CB 88 jA] ->
  rw_cells psegs m (q + 152) (ios_cellsI (q + 40) fill j124 j260) ->
  imp_out m q ocp ->
  rw_cells psegs m (q + 392) [CB 24 j392] -> rw_cells psegs m (q + 848) [CB 88 j848] ->
  alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q - 48 -> q + 1040 <= B -> B < 2^62 ->
  implM psegs (mbind (pj_free_nulls lops) (fun _ => k (option_map blk_id ocp))) s Q
        (MS (mkR x1 (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3
                 (Z_to_bv 64 IMP_OS_VPTR) (Z_to_bv 64 (IMP_VTT + 8)) s6 s7 (Z_to_bv 64 IMP_SBB_VPTR) s9 (Z_to_bv 64 (q + IMP_IMPLS)) s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x3efe0) fc None m (seg_rom psegs)).
Proof.
  intros until fill. intros KPOST FRM MI ST ERR AUX FA SO HEAP PRES SJS OSC IOSC OUTP J392 J848 CEIL GLO LO QB B62.
  unfold IMP_OS_VPTR, IMP_SBB_VPTR, IMP_IMPLS, OSS_CLASSIC, GLOBALS_TOP in *.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (ELX : LX_ERRNO = 957684) by reflexivity. rewrite ELX in ERR.
  pose proof (munch_refl [(q - 48, q); (q + 48, q + 56); (q + 152, q + 160)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
  apply implM_pj_free_nulls.
  hide OUTP. unfold implM. iprefix.

  lstep. lstep. lstep.
  takeZ OSC 2%nat (q + 56) OSV. takeZ OSC 1%nat (q + 64) LOCC. rename OSC into JA.
  eapply evt_cut; [eapply locale_dtor_spec; [exact LOCC| lia| assumption]|]. intros ms' (u0 & u1 & ->).
  replace (ret_pc (Z_to_bv 64 0x3efec)) with (Z_to_bv 64 0x3efec) by (apply bv_eq; vm_compute; reflexivity).

  lstep. lstep. lstep. lstep.

  lstep. lstep. replace (Z_to_bv 64 (q + 152)) with (Z_to_bv 64 (q + 40 + 112)) by (f_equal; lia).
  replace (q + 152) with (q + 40 + 112) in IOSC by lia.
  call (ios_dtorI_proof _ q _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo (q + 40) fill j124 j260);
    [exact ST| lia| lia| exact IOSC| lia| lia| assumption|].
  rename PC into ST9. rename POST into IOS9.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
  lazymatch goal with H : mem_inv _ m9 |- _ => rename H into MI9 end.
  apply evt_done. to_implM. eapply KPOST. unfold imp_okarm_post, IMP_OKARM_END, IMP_OS_VPTR, IMP_SBB_VPTR, IMP_IMPLS. do 23 eexists.
  split; [cbv delta [mkR]; reflexivity|].
  split; [reflexivity|].
  split; [exact FRM|]. split; [exact MI9|]. split; [exact ST9|]. split; [rewrite ELX; eassumption|].
  split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. unfold RAUXV_CELL. repeat constructor; cbn; lia. }
  split; [exact FA|]. split; [exact SO|].
  split. { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. repeat (constructor; [apply W_ok_stack; cbn; lia|]). constructor. }
  assert (PRES9 : lx_pres LBall q (okX q) m00 m9).
  { eapply lx_pres_trans; [exact PRES|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
    intros a Ha [NX HC]. unfold okX in NX. cbn [rin_ivs fst snd] in NX. cbn [outside].
    destruct HC as [HC|[HC|HC]]; [lia| pose proof (lb_below _ _ _ _ HEAP (in_block_app_r _ _ _ HC)); lia| lia]. }
  split; [apply okX_weaken; exact PRES9|].
  split; [eapply sj_statics_along; [| exact PRES9| exact SJS]; lia|].
  split. { unhide OUTP. eapply imp_out_agree; [exact (agree_on_of_munch _ _ _ MU WM)| | exact OUTP]. intros a Ha. cbn [outside]. lia. }
  lazymatch goal with H : rw_cells _ m9 (q + 40) _ |- _ => rename H into OSV9 end.
  lazymatch goal with H : rw_cells _ m9 (q + 56) _ |- _ => rename H into LOC9 end.
  lazymatch goal with H : rw_cells _ m9 (q + 64) _ |- _ => rename H into JA9 end.
  glueZ OSV9 LOC9. glueZ OSV9 JA9. replace (q + 40 + 112) with (q + 152) in IOS9 by lia. glueZ OSV9 IOS9. rename OSV9 into OSV.
  split. { apply rw_cells_forget in OSV. destruct OSV as [bs OSV]. exists bs. exact OSV. }
  split; [eexists; eassumption|]. eexists; eassumption.
Qed.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.
  Hypothesis SER : ser_stmt TAPE_MAX_DEPTH.

Lemma okarm_tail : forall {A} (k : option bptr -> M PState A) (Q : A -> PState -> machine_state -> Prop)
    (x1 gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m00 m : mem) (s00 s : PState) (LBall : list block) (q lo B len L : Z) (errv hmw : word) (ocp : option block) (st : ossst)
    (j64 j392 j108 j124 j260 : list byte),
  (forall cpy s' ms', imp_okarm_post q gp s0 s1 s2 s3 (Z_to_bv 64 IMP_OS_VPTR) (Z_to_bv 64 (IMP_VTT + 8)) (Z_to_bv 64 IMP_SBB_VPTR) s9 (Z_to_bv 64 (q + IMP_IMPLS)) s11
                         s00 LBall lo B m00 cpy s' ms' -> implM psegs (k cpy) s' Q ms') ->
  frm0 fc -> mem_inv psegs m -> stk psegs m lo q -> rw_cells psegs m LX_ERRNO [C4 errv] -> rauxv_ok m B ->
  ps_fa s = ps_fa s00 -> ps_so s = ps_so s00 -> RHEAP s (ocp_blocks ocp ++ osblocks st ++ LBall) m ->
  lx_pres LBall q (okX q) m00 m -> sj_statics m00 true -> pj_consts m00 ->
  rw_cells psegs m (q + 40) [C8 (Z_to_bv 64 OSS_OS_VPTR)] -> rw_cells psegs m (q + 48) (sb_cellsI st) -> STRREP m (q + 40) st -> OSNUM len st ->
  rw_cells psegs m (q + 136) [C8 hmw] -> rw_cells psegs m (q + 144) [CB 4 mode16; CB 4 j108] -> rw_cells psegs m (q + 152) (ios_cellsI (q + 40) 0x20 j124 j260) ->
  imp_res m (q + 848) ocp L -> 0 <= L -> rw_cells psegs m (q + 872) [CB 64 j64] ->
  rw_cells psegs m (q + 416) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells psegs m (q + 392) [CB 24 j392] ->
  rw_cells psegs m (q + 24) [C8 (Z_to_bv 64 IMP_SB_VPTR); C8 (Z_to_bv 64 IMP_IOS_VPTR)] ->
  0 <= len <= SJ_PADMAX ->
  alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q - RFREE_STACK -> q + 1040 <= B -> B < 2^62 ->
  implM psegs (mbind (del_opt lops (os_blk st)) (fun _ => mbind (pj_free_nulls lops) (fun _ => k (option_map blk_id ocp)))) s Q
        (MS (mkR x1 (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3
                 (Z_to_bv 64 IMP_OS_VPTR) (Z_to_bv 64 (IMP_VTT + 8)) s6 s7 (Z_to_bv 64 IMP_SBB_VPTR) s9 (Z_to_bv 64 (q + IMP_IMPLS)) s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x3ef70) fc None m (seg_rom psegs)).
Proof.
  intros until j260. intros KPOST FRM MI ST ERR AUX FA SO HEAP PRES SJS PJC OSV SBC REP NUM HMC MODE IOSC RES L0 J64 OUT J392 V24 LEN CEIL GLO LO QB B62.
  unfold IMP_OS_VPTR, IMP_SBB_VPTR, IMP_SB_VPTR, IMP_IOS_VPTR, IMP_IMPLS, GLOBALS_TOP, RFREE_STACK, SJ_PADMAX in *.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (ELX : LX_ERRNO = 957684) by reflexivity. rewrite ELX in ERR.
  pose proof (pj_consts_along LBall q m00 m ltac:(lia) PRES PJC) as (_ & VB & _).
  unfold sb_cellsI, OSS_SB_VPTR, OSS_CLASSIC in SBC.
  pose proof (munch_refl [(q + 40, q + 56); (q + 152, q + 160); (q + 416, q + 440)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
  unfold implM. iprefix.
  replace (q + 152) with (q + 40 + 112) in IOSC by lia.
  call (okarm_move _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ q _ ocp L 0x20 j124 j260);
    [lia| lia| assumption| exact V24| exact OSV| replace (q + 152) with (q + 40 + 112) by lia; exact IOSC| exact OUT| exact RES| exact L0
    | unfold OSS_VBOFF; exact VB|].
  rename PC into OSV1. rename PC0 into IOSC1. rename PC1 into OUT1. rename POST into R24. destruct R24 as [j24 R24].
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  lazymatch goal with H : mem_inv _ m1 |- _ => rename H into MI1 end.
  pose proof (munch_refl [(q + 48, q + 56)]%Z m1) as MU1. pose proof (wmono_refl psegs m1) as WM1.
  apply (STRREP_agree _ _ _ _ _ (agree_on_of_munch _ _ _ MU WM)) in REP;
    [| intros a Ha; cbn [outside]; lia
     | intros a Hb; pose proof (lb_below _ _ _ _ HEAP (in_block_app_r _ _ _ (in_block_app_l _ _ _ Hb))); cbn [outside]; lia].

  unfold STRREP in REP. unfold osblocks in HEAP. unfold OSNUM in NUM. destruct (os_blk st) as [b|].
  -
    destruct REP as (R3 & (bsd & DATA) & RB). pose proof NUM as (_ & _ & _ & C16).
    pose proof RB as (RB1 & RB2 & RB3 & RB4 & RB5). unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in RB4 || idtac.
    replace (q + 40 + 72) with (q + 112) in R3 by lia.
    pose proof (rw_cells_C8_read1_g psegs m1 _ _ _ R3) as RD. rewrite unsigned_lit in RD by lia.
    lstep. lstep. rewrite ?zxb_u, ?u8_lit. rewrite long_byte0 by (clear - C16; Z.div_mod_to_equations; lia). lstep. lstep. lstep. if_false. clear RD.

    lstep. lstep. lstep. rewrite ?(unsigned_lit (os_cap st + 1)) by lia. rewrite long_capmask by (clear - C16 RB3 NUM LEN; unfold PJ_CAPMAX, PJ_OUTMAX in NUM; Z.div_mod_to_equations; lia). lstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    ihere. to_implM. apply implM_del_opt_some. eapply implM_bind.
    { assert (HEAPp : RHEAP s ((b, os_data st, os_cap st) :: ocp_blocks ocp ++ LBall) m4).
      { eapply RHEAP_perm; [eapply LH_frame; [exact HEAP| exact MU| exact WM|]|].
        - repeat (constructor; [apply W_ok_stack; cbn; lia|]). constructor.
        - cbn [app]. apply Permutation_sym. apply Permutation_middle. }
      eapply (opdel_sz_proof HF) with (B := B) (lo := lo);
        [exact HEAPp| left; reflexivity| | lia| eassumption| exact CEIL| unfold RFREE_STACK; lia| eassumption| assumption| lia].
      eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. unfold RAUXV_CELL. repeat constructor; cbn; lia. }
    cbv beta. intros [] s5 ms5 PO5. unfold free_postZ in PO5.
    destruct PO5 as (w5 & w6 & w7 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & m5
                     & -> & MI5 & ST5 & ERR5 & AUX5 & PRES45 & FA5 & SO5 & HEAP5).
    assert (ND : List.NoDup (map blk_id ((b, os_data st, os_cap st) :: ocp_blocks ocp ++ LBall))).
    { eapply LH_nodup. eapply RHEAP_perm; [eapply LH_frame; [exact HEAP| exact MU| exact WM|]|].
      - repeat (constructor; [apply W_ok_stack; cbn; lia|]). constructor.
      - cbn [app]. apply Permutation_sym. apply Permutation_middle. }
    rewrite (lb_remove_hd _ _ _ _ ND) in PRES45, HEAP5.
    replace (ret_pc (Z_to_bv 64 0x3efe0)) with (Z_to_bv 64 0x3efe0) by (apply bv_eq; vm_compute; reflexivity).
    pose proof (agree_of_heap_pres _ _ _ _ PRES45) as AG.
    assert (STC : forall a, q <= a -> rclient_addr (ocp_blocks ocp ++ LBall) q a) by (intros a Ha; left; exact Ha).
    apply (rw_cells_agree _ _ _ _ _ AG) in OSV1; [| intros a Ha; cbn in Ha; apply STC; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in IOSC1; [| intros a Ha; rewrite ios_cellsI_size in Ha; apply STC; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in R24; [| intros a Ha; cbn in Ha; apply STC; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in J64; [| intros a Ha; cbn in Ha; apply STC; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in J392; [| intros a Ha; cbn in Ha; apply STC; lia].
    lazymatch goal with H : rw_cells _ m4 (q + 48) _ |- _ => apply (rw_cells_agree _ _ _ _ _ AG) in H; [rename H into SBC1| intros a Ha; cbn in Ha; apply STC; lia] end.
    apply (rw_cells_agree _ _ _ _ _ AG) in R3; [| intros a Ha; cbn in Ha; apply STC; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in HMC; [| intros a Ha; cbn in Ha; apply STC; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in MODE; [| intros a Ha; cbn in Ha; apply STC; lia].
    apply (imp_out_agree _ _ _ _ _ (agree_on_of_munch _ _ _ MU1 WM1)) in OUT1; [| intros a Ha; cbn [outside]; lia].
    apply (imp_out_agree _ _ _ _ _ AG) in OUT1; [| intros a Ha; apply STC; lia].

    takeZ SBC1 1%nat (q + 56) SBV. takeZ SBC1 1%nat (q + 64) LOCC.
    glueZ SBC1 R3. glueZ SBC1 HMC. glueZ SBC1 MODE. merge_at SBC1 0%nat 12%nat. forget_junk SBC1.
    lazymatch type of SBC1 with rw_cells _ _ _ [CB 88 ?x] => set (jA := x) in SBC1; clearbody jA end || idtac.
    glueZ OSV1 SBV. glueZ OSV1 LOCC. glueZ OSV1 SBC1.
    glueZ R24 J64. merge_at R24 0%nat 2%nat. lazymatch type of R24 with rw_cells _ _ _ [CB 88 ?x] => set (j848 := x) in R24; clearbody j848 end || idtac.
    replace (q + 40 + 112) with (q + 152) in IOSC1 by lia.
    eapply okarm_fin with (m00 := m00) (s00 := s00);
      [exact KPOST| exact FRM| exact MI5| exact ST5| exact ERR5| exact AUX5| congruence| congruence| exact HEAP5
      | eapply lx_pres_trans; [| eapply lx_pres_weaken; [apply lx_pres_of_heap_pres; exact PRES45| lia| intros b0 Hb0; apply in_app_iff; right; exact Hb0| intros a Ha; exact Ha]]
      | exact SJS| exact OSV1| exact IOSC1| exact OUT1| exact J392| exact R24| exact CEIL| unfold GLOBALS_TOP; lia| lia| exact QB| exact B62].
    eapply lx_pres_trans; [exact PRES|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
    intros a Ha [NX HC]. unfold okX in NX. cbn [rin_ivs fst snd] in NX. cbn [outside].
    destruct HC as [HC|[HC|HC]]; [lia| | lia].
    pose proof (lb_below _ _ _ _ HEAP ltac:(apply in_block_app_r; apply (in_block_app_r [_]); exact HC)). lia.
  -
    destruct REP as (R44 & (bsd & R23) & Hd).
    replace (q + 40 + 72) with (q + 112) in R44 by lia.
    lstep. lstep. rewrite ?zxb_u, ?u8_lit. replace (Z.land (44 mod 256) 1) with 0 by reflexivity. lstep. lstep. lstep. if_true.
    ihere. to_implM. apply implM_del_opt_none. cbv beta. cbn [app] in HEAP.
    lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    lazymatch goal with H : mem_inv _ m2 |- _ => rename H into MI2 end.
    lazymatch goal with H : rw_cells _ m2 (q + 48) _ |- _ => rename H into SBC1 end.
    takeZ SBC1 1%nat (q + 56) SBV. takeZ SBC1 1%nat (q + 64) LOCC.
    replace (q + 40 + 73) with (q + 113) in R23 by lia.
    glueZ SBC1 R44. glueZ SBC1 R23. glueZ SBC1 HMC. glueZ SBC1 MODE. merge_at SBC1 0%nat 11%nat. forget_junk SBC1.
    lazymatch type of SBC1 with rw_cells _ _ _ [CB 88 ?x] => set (jA := x) in SBC1; clearbody jA end || idtac.
    glueZ OSV1 SBV. glueZ OSV1 LOCC. glueZ OSV1 SBC1.
    glueZ R24 J64. merge_at R24 0%nat 2%nat. lazymatch type of R24 with rw_cells _ _ _ [CB 88 ?x] => set (j848 := x) in R24; clearbody j848 end || idtac.
    replace (q + 40 + 112) with (q + 152) in IOSC1 by lia.
    assert (PRES2 : lx_pres LBall q (okX q) m00 m2).
    { eapply lx_pres_trans; [exact PRES|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
      intros a Ha [NX HC]. unfold okX in NX. cbn [rin_ivs fst snd] in NX. cbn [outside].
      destruct HC as [HC|[HC|HC]]; [lia| | lia].
      pose proof (lb_below _ _ _ _ HEAP ltac:(apply in_block_app_r; exact HC)). lia. }
    eapply okarm_fin with (m00 := m00) (s00 := s00);
      [exact KPOST| exact FRM| exact MI2| assumption| eassumption| | exact FA| exact SO| | exact PRES2
      | exact SJS| exact OSV1| exact IOSC1| | exact J392| exact R24| exact CEIL| unfold GLOBALS_TOP; lia| lia| exact QB| exact B62].
    + eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. unfold RAUXV_CELL. repeat constructor; cbn; lia.
    + eapply LH_frame; [exact HEAP| exact MU| exact WM|]. repeat (constructor; [apply W_ok_stack; cbn; lia|]). constructor.
    + eapply imp_out_agree; [exact (agree_on_of_munch _ _ _ MU1 WM1)| | exact OUT1]. intros a Ha. cbn [outside]. lia.
Qed.

Lemma okarm_str : forall {A} (k : option bptr -> M PState A) (Q : A -> PState -> machine_state -> Prop)
    (x1 gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m00 m : mem) (s00 s : PState) (LBall : list block) (q lo B len : Z) (errv : word) (st : ossst) (j88 j392 : list byte),
  (forall cpy s' ms', imp_okarm_post q gp s0 s1 s2 s3 (Z_to_bv 64 IMP_OS_VPTR) (Z_to_bv 64 (IMP_VTT + 8)) (Z_to_bv 64 IMP_SBB_VPTR) s9 (Z_to_bv 64 (q + IMP_IMPLS)) s11
                         s00 LBall lo B m00 cpy s' ms' -> implM psegs (k cpy) s' Q ms') ->
  frm0 fc -> mem_inv psegs m -> stk psegs m lo q -> rw_cells psegs m LX_ERRNO [C4 errv] -> rauxv_ok m B ->
  ps_fa s = ps_fa s00 -> ps_so s = ps_so s00 -> RHEAP s (osblocks st ++ LBall) m ->
  lx_pres LBall q (okX q) m00 m -> sj_statics m00 true -> pj_consts m00 ->
  OSSINV m (q + 40) len st 0x20 -> os_w st <= PJ_OUTMAX len ->
  rw_cells psegs m (q + 848) [CB 88 j88] ->
  rw_cells psegs m (q + 416) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells psegs m (q + 392) [CB 24 j392] ->
  rw_cells psegs m (q + 24) [C8 (Z_to_bv 64 IMP_SB_VPTR); C8 (Z_to_bv 64 IMP_IOS_VPTR)] ->
  0 <= len <= SJ_PADMAX ->
  alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q - OSS_STR_STACK -> q + 1040 <= B -> B < 2^62 ->
  implM psegs (mbind (imp_copy lops len) (fun cpy => mbind (del_opt lops (os_blk st)) (fun _ => mbind (pj_free_nulls lops) (fun _ => k cpy)))) s Q
        (MS (mkR x1 (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3
                 (Z_to_bv 64 IMP_OS_VPTR) (Z_to_bv 64 (IMP_VTT + 8)) s6 s7 (Z_to_bv 64 IMP_SBB_VPTR) s9 (Z_to_bv 64 (q + IMP_IMPLS)) s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x3ef64) fc None m (seg_rom psegs)).
Proof.
  intros until j392. intros KPOST FRM MI ST ERR AUX FA SO HEAP PRES SJS PJC OSS WMAX J88 OUT J392 V24 LEN CEIL GLO LO QB B62.
  unfold IMP_OS_VPTR, IMP_SBB_VPTR, IMP_SB_VPTR, IMP_IOS_VPTR, IMP_IMPLS, GLOBALS_TOP, OSS_STR_STACK, RMALLOC_STACK, SJ_PADMAX in *.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (ELX : LX_ERRNO = 957684) by reflexivity. rewrite ELX in ERR.
  destruct OSS as [[PUTC [REP NUM]] [OSV [j124 [j260 IOSC]]]]. destruct PUTC as (SBC & (hm & HMC & HMR) & (j108 & MODE)).
  pose proof NUM as (WR & _ & _ & _).
  unfold sb_cellsI in SBC. unfold ios_cellsI in IOSC. unfold OSS_SB_VPTR, OSS_CLASSIC, OSS_IOS_VPTR in SBC, IOSC.
  apply (rw_cells_split_CB psegs _ _ [] 88 j88 [] [24;64]%nat) in J88; [|reflexivity]. cbn [mk_CB_cells app] in J88. forget_junk J88.
  takeZ J88 1%nat (q + 872) R24. rename J88 into J64.
  pose proof (munch_refl [(q - 64, q); (q + 848, q + 872); (q + 136, q + 144)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
  unfold implM. iprefix.

  lstep. lstep. lstep. replace (Z_to_bv 64 (q + 48)) with (Z_to_bv 64 (q + 40 + 8)) by (f_equal; lia).
  destruct (Z_lt_le_dec 22 (os_w st)) as [WL|WS].
  -
    ihere. to_implM. apply (ImpImpl.implM_imp_copy_some psegs raw_malloc raw_free ps_so set_so_ps len (imp_S (os_w st))); [apply imp_S_copy_ok; lia|].
    eapply (str_long_proof HM) with (lo := lo) (B := B) (len := len) (LB := LBall);
      [exact HEAP| exact AUX| lia| lia| exact ST| exact CEIL| unfold GLOBALS_TOP; lia| unfold OSS_STR_STACK, RMALLOC_STACK; lia| eassumption| assumption
      | lia| lia| lia| lia| lia| exact R24| unfold SJ_PADMAX; lia
      | split; [split; [exact SBC| split; [exists hm; split; [exact HMC| exact HMR]| exists j108; exact MODE]]| split; [exact REP| exact NUM]]
      | lia| exact WMAX|].
    intros b s5 ms5 PO5. unfold str_long_post in PO5.
    destruct PO5 as (w5 & w6 & w7 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w28 & w29 & w30 & w31 & m5 & errv5 & NEW
                     & -> & MI5 & ST5 & ERR5 & AUX5 & FA5 & SO5 & HEAP5 & RES5 & (bn & NEWC) & RB5 & (hm5 & HMC5) & PRES45).
    replace (ret_pc (Z_to_bv 64 0x3ef70)) with (Z_to_bv 64 0x3ef70) by (apply bv_eq; vm_compute; reflexivity).
    cbv beta.
    pose proof (agree_of_lx_pres _ _ _ _ _ PRES45) as AG.
    assert (STC : forall a, (q <= a /\ ~ (q + 848 <= a < q + 872) /\ ~ (q + 136 <= a < q + 144)) \/ in_block (osblocks st) a ->
                  lx_client (osblocks st ++ LBall) q [(q + 848, q + 848 + 24); (q + 40 + 96, q + 40 + 104)] a).
    { intros a [Ha|Ha]; [split; [cbn [rin_ivs fst snd]; lia| left; lia]|].
      pose proof (lb_below _ _ _ _ HEAP (in_block_app_l _ _ _ Ha)). split; [cbn [rin_ivs fst snd]; lia| right; left; apply in_block_app_l; exact Ha]. }
    apply (rw_cells_agree _ _ _ _ _ AG) in OSV; [| intros a Ha; cbn in Ha; apply STC; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in SBC; [| intros a Ha; cbn in Ha; apply STC; lia].
    apply (STRREP_agree _ _ _ _ _ AG) in REP; [| intros a Ha; apply STC; lia| intros a Ha; apply STC; right; exact Ha].
    apply (rw_cells_agree _ _ _ _ _ AG) in MODE; [| intros a Ha; cbn in Ha; apply STC; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in IOSC; [| intros a Ha; cbn in Ha; apply STC; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in J64; [| intros a Ha; cbn in Ha; apply STC; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in OUT; [| intros a Ha; cbn in Ha; apply STC; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in J392; [| intros a Ha; cbn in Ha; apply STC; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in V24; [| intros a Ha; cbn in Ha; apply STC; lia].
    replace (q + 40 + 96) with (q + 136) in HMC5 by lia. replace (q + 40 + 8) with (q + 48) in SBC by lia.
    replace (q + 40 + 104) with (q + 144) in MODE by lia. replace (q + 40 + 112) with (q + 152) in IOSC by lia.
    pose proof (imp_S_range (os_w st) ltac:(lia)) as (SR1 & SR2 & SR3).
    eapply (okarm_tail k Q _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m00 m5 s00 s5 LBall q lo B len (os_w st) errv5 (Z_to_bv 64 hm5) (Some (b, NEW, imp_S (os_w st))) st);
      [exact KPOST| exact FRM| exact MI5| exact ST5| exact ERR5| exact AUX5| congruence| congruence| cbn [ocp_blocks app]; exact HEAP5
      | | exact SJS| exact PJC| exact OSV| exact SBC| exact REP| exact NUM| exact HMC5| exact MODE| exact IOSC
      | cbn [imp_res blk_size blk_addr fst snd]; split; [exact RES5| split; [exact SR2| split; [unfold PJ_OUTMAX in WMAX; lia| exact RB5]]]
      | lia| exact J64| exact OUT| exact J392| exact V24| unfold SJ_PADMAX; lia| exact CEIL| unfold GLOBALS_TOP; lia| unfold RFREE_STACK; lia| exact QB| exact B62].
    eapply lx_pres_trans; [exact PRES|]. eapply lx_pres_weaken; [exact PRES45| lia| intros b0 Hb0; apply in_app_iff; right; exact Hb0|].
    intros a Ha. unfold okX. cbn [rin_ivs fst snd] in *. lia.
  -
    call (str_short_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ q lo (q + 40) len (q + 848) st _);
      [exact ST| exact CEIL| unfold GLOBALS_TOP; lia| lia| lia| lia| lia| lia| lia| lia| exact R24
      | split; [split; [exact SBC| split; [exists hm; split; [exact HMC| exact HMR]| exists j108; exact MODE]]| split; [exact REP| exact NUM]]
      | lia| assumption|].
    rename PC into ST2. rename PC0 into RES2. rename POST into HMC2. destruct HMC2 as [hm2 HMC2].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    lazymatch goal with H : mem_inv _ m2 |- _ => rename H into MI2 end.
    replace (q + 40 + 96) with (q + 136) in HMC2 by lia.
    lazymatch goal with H : rw_cells _ m2 (q + 40 + 8) _ |- _ => replace (q + 40 + 8) with (q + 48) in H by lia end.
    lazymatch goal with H : rw_cells _ m2 (q + 40 + 104) _ |- _ => replace (q + 40 + 104) with (q + 144) in H by lia end.
    lazymatch goal with H : rw_cells _ m2 (q + 40 + 112) _ |- _ => replace (q + 40 + 112) with (q + 152) in H by lia end.
    ihere. to_implM. apply implM_imp_copy_none. cbv beta.
    pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
    apply (STRREP_agree _ _ _ _ _ AG) in REP;
      [| intros a Ha; cbn [outside]; lia
       | intros a Hb; pose proof (lb_below _ _ _ _ HEAP (in_block_app_l _ _ _ Hb)); cbn [outside]; lia].
    assert (PRES2 : lx_pres LBall q (okX q) m00 m2).
    { eapply lx_pres_trans; [exact PRES|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
      intros a Ha [NX HC]. unfold okX in NX. cbn [rin_ivs fst snd] in NX. cbn [outside].
      destruct HC as [HC|[HC|HC]]; [lia| | lia].
      pose proof (lb_below _ _ _ _ HEAP (in_block_app_r _ _ _ HC)). lia. }
    eapply (okarm_tail k Q _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m00 m2 s00 s LBall q lo B len (os_w st) errv (Z_to_bv 64 hm2) None st);
      [exact KPOST| exact FRM| exact MI2| exact ST2| eassumption| | exact FA| exact SO| | exact PRES2| exact SJS| exact PJC
      | eassumption| eassumption| exact REP| exact NUM| exact HMC2| eassumption| eassumption
      | cbn [imp_res]; eexists; exact RES2
      | lia| eassumption| eassumption| eassumption| eassumption| unfold SJ_PADMAX; lia| exact CEIL| unfold GLOBALS_TOP; lia| unfold RFREE_STACK; lia| exact QB| exact B62].
    + eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. unfold RAUXV_CELL. repeat constructor; cbn; lia.
    + cbn [ocp_blocks app]. eapply LH_frame; [exact HEAP| exact MU| exact WM|]. repeat (constructor; [apply W_ok_stack; cbn; lia|]). constructor.
Qed.

  Theorem imp_okarm_proof : imp_okarm_stmt.
  Proof.
    pose proof (put_proof (xsputn_proof (overflow_proof (push_back_proof HM HF)))) as PUT.
    unfold imp_okarm_stmt. intros until jsb.
    intros HEAP INT INS AUX QB B62 ST CEIL GLO LO ERR MI FRM AL16 Q0 LXS SJS SSP LEN CAP R24 SRET GAP JEL OUT SBA DOCC OKR KPOST.
    unfold IMP_OKARM, IMP_OKARM_STACK, IMP_FRAME, IMP_DOC, GLOBALS_TOP in *.
    unfold Imp_defs.IMP_SB_VPTR, Imp_defs.IMP_IOS_VPTR in R24.
    assert (Q62 : q < 2^62) by (clear - QB B62; lia).
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in CEIL'.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (lx_statics_pj _ LXS) as PJC. pose proof (sj_statics_locb _ _ SJS) as LB0.
    assert (ELX : LX_ERRNO = 957684) by reflexivity. rewrite ELX in ERR.

    destruct OKR as [KO|(_ & tws & sbs & TB & SBB & WF & FAB & TL & SL)]; [exfalso; rewrite unsigned_lit in KO by lia; lia|].
    takeZ DOCC 2%nat (q + 352) DOC2.
    assert (DR : DOCREP m LBall (q + 336) TAPE SBUF len tws sbs).
    { split; [exact DOC2|]. split; [exact TB|]. split; [exact SBB|]. split; [exact WF|]. split; [exact FAB|].
      unfold SJ_TAPE, SJ_SBUF, sj_cap. rewrite <- CAP. split; [lia|]. split; [lia|].
      split; [exists (ptp, TAPE, 8 * roundup64 (cap + 3)); split; [exact INT| cbn; lia]|].
      exists (psb, SBUF, roundup64 (5 * (cap / 3) + 64)); split; [exact INS| cbn; lia]. }
    pose proof WF as (WN & WSN & _ & _ & EL).
    clear TB SBB DOCC DOC2.

    eapply (PjImpl.implM_pj_chain_part psegs raw_malloc raw_free ps_so set_so_ps).
    unfold implM. iprefix.
    eapply evt_cut.
    { eapply okarm_setup with (len := len); [exact ST| unfold GLOBALS_TOP; lia| lia| lia| exact LB0| | exact MI| exact SRET| exact GAP| exact JEL| exact SBA| unfold SJ_PADMAX; clear - LEN; lia].
      pose proof PJC as (V4 & V3 & V2 & _ & V1 & _).
      unfold imp_vt_rows, OSS_GOT_VT, OSS_VTT, OSS_VBOFF, OSS_SBVT, OSS_XSPUTN, OSS_OVERFLOW, OSS_OS_VPTR, OSS_OS_CVPTR, OSS_IOS_CVPTR, OSS_IOS_VPTR, OSS_SB_VPTR, OSS_SBB_VPTR.
      split; [exact V1| split; [exact V2| split; [exact V3| exact V4]]]. }
    intros ms1 P1. unfold okarm_setup_post in P1.
    destruct P1 as (r5 & r6 & r7 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m1 & -> & MU & WM & MI1 & ST1 & OSS1 & LB1 & INV1 & (jerr & ELC)).
    pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
    assert (HEAP1 : RHEAP s LBall m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. repeat (constructor; [apply W_ok_stack; cbn; lia|]). constructor. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. unfold RAUXV_CELL. repeat constructor; cbn; lia. }
    apply (rw_cells_agree _ _ _ _ _ AG) in ERR; [| intros a Ha; cbn in Ha; cbn [outside]; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in OUT; [| intros a Ha; cbn in Ha; cbn [outside]; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in R24; [| intros a Ha; cbn in Ha; cbn [outside]; lia].
    apply (DOCREP_agree _ _ _ _ _ _ _ _ _ _ AG) in DR; [| intros a Ha; cbn [outside]; lia| intros a Ha; pose proof (lb_below _ _ _ _ HEAP Ha); cbn [outside]; lia].
    assert (PRES01 : lx_pres LBall q (okX q) m m1).
    { eapply lx_pres_of_munch; [exact MU| exact WM|].
      intros a Ha [NX HC]. unfold okX in NX. cbn [rin_ivs fst snd] in NX. cbn [outside].
      destruct HC as [HC|[HC|HC]]; [lia| pose proof (lb_below _ _ _ _ HEAP HC); lia| lia]. }
    clear AG SRET GAP JEL SBA MI ST LB0 MU WM HEAP AUX.
    ihere. to_implM.

    eapply implM_bind.
    { eapply SER with (q := q) (lo := lo) (B := B) (SB := q + 848) (st := sb0 (q + 848)) (DOC := q + 336) (LB0 := LBall) (errv := errv)
                      (j := Z.of_nat (length tws) - 1) (c' := Z.of_nat (length sbs));
        [cbn [sbblocks sb_blk sb0 app]; exact HEAP1| exact AUX1| lia| lia| exact ST1| exact CEIL| unfold GLOBALS_TOP; lia
        | unfold TAPE_MAX_DEPTH; rewrite ser_need_root; unfold PJ_SER_STACK, PJ_GROW_STACK, RMALLOC_STACK; lia
        | rewrite ELX; exact ERR| exact MI1| exact FRM| lia| lia| lia| lia| lia| unfold SJ_PADMAX; clear - LEN; lia| exact INV1| exact DR| exact EL
        | lia| lia| lia| lia| unfold sb_acc1; cbn [sb_size sb0]; lia]. }
    cbv beta. intros c sM2 ms2 PO2. unfold ser_post in PO2.
    destruct PO2 as (v5 & v6 & v7 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v28 & v29 & v30 & v31 & F2 & fc2 & m2 & errv2 & st2
                     & -> & MI2 & ST2 & ERR2 & AUX2 & FRM2 & FA2 & SO2 & -> & HEAP2 & INV2 & ACC2 & PRES12).
    replace (ret_pc (Z_to_bv 64 0x3ef40)) with (Z_to_bv 64 0x3ef40) by (apply bv_eq; vm_compute; reflexivity).
    rewrite ELX in ERR2.
    assert (NB : sb_size st2 <= PJ_OUTMAX len).
    { eapply (sb_acc_out m1 LBall (q + 336) TAPE SBUF len tws sbs st2 (Z.of_nat (length tws) - 1) (Z.of_nat (length sbs)));
        [unfold SJ_PADMAX; clear - LEN; lia| exact DR| lia| lia| exact ACC2]. }
    assert (PRES02 : lx_pres LBall q (okX q) m m2).
    { eapply lx_pres_trans; [exact PRES01|]. eapply lx_pres_weaken; [exact PRES12| lia| intros b0 Hb0; exact Hb0|].
      intros a Ha. unfold okX. cbn [rin_ivs fst snd] in *. lia. }
    pose proof (agree_of_lx_pres _ _ _ _ _ PRES12) as AG.
    assert (STC : forall a, q <= a < q + 848 \/ lxs_addr a \/ (PJ_LOC_LO <= a < PJ_LOC_HI) -> lx_client LBall q [(q + 848, q + 848 + 88)] a).
    { intros a [Ha|[Ha|Ha]]; [split; [cbn [rin_ivs fst snd]; lia| left; lia]| apply lxs_addr_client; [exact Ha| cbn [rin_ivs fst snd]; unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, SJ_GOT_NOTHROW, SJ_IMPL_VT24, SJ_DPI_VPTR in Ha; lia]|].
      split; [cbn [rin_ivs fst snd]; lia| right; right]. unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP in *. lia. }
    apply (OSSINV_agree _ _ _ _ _ _ _ AG) in OSS1; [| intros a Ha; apply STC; lia| intros a (b0 & Hb0 & _); cbn [osblocks oss0 os_blk] in Hb0; destruct Hb0].
    apply (LOCB_agree _ _ _ AG) in LB1; [| intros a Ha; apply STC; right; right; exact Ha].
    apply (rw_cells_agree _ _ _ _ _ AG) in ELC; [| intros a Ha; cbn in Ha; apply STC; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in OUT; [| intros a Ha; cbn in Ha; apply STC; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in R24; [| intros a Ha; cbn in Ha; apply STC; lia].
    pose proof (pj_consts_along LBall q m m2 ltac:(clear - CEIL LO; lia) PRES02 PJC) as PJC2.
    clear AG STC HEAP1 AUX1 MI1 ST1 PRES12 PRES01 ERR INV1.

    unfold sb_ch. cbn [ch_fuel ch_cap ch_blk fst snd].
    eapply (PjImpl.implM_pj_chain_stop psegs raw_malloc raw_free ps_so set_so_ps); [pose proof (SBINV_cap_pos _ _ _ _ INV2); lia|]. cbv beta.

    eapply (PjImpl.implM_pj_chain_part psegs raw_malloc raw_free ps_so set_so_ps).
    unfold Pj_defs.SBINV in INV2. destruct st2 as [buf2 size2 cap2 blk2 fuel2]. cbn [sb_buf sb_size sb_cap sb_blk sb_fuel sbblocks] in *.
    destruct INV2 as (SBW & SZ2 & (bsb & BUF2) & (ji2 & INL) & FU2 & CAPB & BLK2). replace (q + 848 + 64) with (q + 912) in SBW by lia.
    assert (BF : 0 < buf2 /\ buf2 + cap2 < 2^62 /\ (buf2 + cap2 <= lo \/ buf2 = q + 848)).
    { destruct blk2; [destruct BLK2 as (R1 & R2 & R3 & R4 & R5); unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in R4; lia| destruct BLK2 as (-> & -> & _); lia]. }

    apply (rw_cells_split_CB psegs _ _ [] (Z.to_nat cap2) bsb [] [Z.to_nat size2; Z.to_nat (cap2 - size2)]%nat) in BUF2; [| cbn; lia]. cbn [mk_CB_cells app] in BUF2. forget_junk BUF2.
    destruct (rw_cells_split_n psegs _ _ _ 1%nat (buf2 + size2) BUF2 ltac:(cbn [firstn cells_size csize]; lia)) as [SRC _].
    cbn [firstn] in SRC. clear BUF2.
    unfold implM. iprefix.

    lstep. lstep. lstep. lstep.
    ihere. to_implM.
    eapply implM_bind.
    { eapply PUT with (lo := lo) (B := B) (len := len) (st := oss0 (q + 40)) (LB0 := (match blk2 with Some b => [(b, buf2, cap2)] | None => [] end) ++ LBall);
        [cbn [osblocks oss0 os_blk app]; exact HEAP2| exact AUX2| lia| lia| exact ST2| exact CEIL| unfold GLOBALS_TOP; lia
        | unfold OSS_PUT_STACK, OSS_XSPUTN_STACK, OSS_OV_STACK, OSS_PB_STACK, RMALLOC_STACK; lia
        | rewrite ELX; exact ERR2| exact MI2| lia| lia
        | pose proof PJC2 as (V4 & V3 & V2 & _ & V1 & _);
          unfold imp_vt_rows, OSS_GOT_VT, OSS_VTT, OSS_VBOFF, OSS_SBVT, OSS_XSPUTN, OSS_OVERFLOW, OSS_OS_VPTR, OSS_OS_CVPTR, OSS_IOS_CVPTR, OSS_IOS_VPTR, OSS_SB_VPTR, OSS_SBB_VPTR;
          split; [exact V1| split; [exact V2| split; [exact V3| exact V4]]]
        | pose proof PJC2 as (_ & _ & _ & WS & _); exact WS
        | pose proof PJC2 as (_ & _ & _ & _ & _ & GCT & _); exact GCT
        | exact LB1| unfold SJ_PADMAX; clear - LEN; lia| exact OSS1
        | exact SRC| lia| lia| | cbn [os_w oss0]; lia].
      destruct blk2 as [b|].
      - left. exists (b, buf2, cap2). split; [left; reflexivity| cbn; lia].
      - right. destruct BLK2 as (-> & -> & _). lia. }
    cbv beta. intros c3 sM3 ms3 PO3. unfold put_post in PO3.
    destruct PO3 as (u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m3 & errv3 & st3
                     & -> & MI3 & ST3 & ERR3 & AUX3 & FA3 & SO3 & -> & W3 & HEAP3 & OSS3 & LB3 & PRES23).
    replace (ret_pc (Z_to_bv 64 0x3ef50)) with (Z_to_bv 64 0x3ef50) by (apply bv_eq; vm_compute; reflexivity).
    rewrite ELX in ERR3. cbn [os_w oss0] in W3.
    assert (PRES03 : lx_pres LBall q (okX q) m m3).
    { eapply lx_pres_trans; [exact PRES02|]. eapply lx_pres_weaken; [exact PRES23| lia| intros b0 Hb0; apply in_app_iff; right; exact Hb0|].
      intros a Ha. unfold okX. cbn [rin_ivs fst snd] in *. lia. }
    pose proof (agree_of_lx_pres _ _ _ _ _ PRES23) as AG.
    assert (STC : forall a, q + 304 <= a -> lx_client (match blk2 with Some b => [(b, buf2, cap2)] | None => [] end ++ LBall) q [(q + 40, q + 40 + 264)] a).
    { intros a Ha. split; [cbn [rin_ivs fst snd]; lia| left; lia]. }
    apply (rw_cells_agree _ _ _ _ _ AG) in SBW; [| intros a Ha; cbn in Ha; apply STC; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in INL; [| intros a Ha; cbn in Ha; apply STC; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in ELC; [| intros a Ha; cbn in Ha; apply STC; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in OUT; [| intros a Ha; cbn in Ha; apply STC; lia].
    assert (STC2 : forall a, q <= a < q + 40 -> lx_client (match blk2 with Some b => [(b, buf2, cap2)] | None => [] end ++ LBall) q [(q + 40, q + 40 + 264)] a).
    { intros a Ha. split; [cbn [rin_ivs fst snd]; lia| left; lia]. }
    apply (rw_cells_agree _ _ _ _ _ AG) in R24; [| intros a Ha; cbn in Ha; apply STC2; lia].
    pose proof (pj_consts_along LBall q m m3 ltac:(clear - CEIL LO; lia) PRES03 PJC) as PJC3.
    pose proof OSS3 as [[_ [_ NUM3]] _]. pose proof (OSNUM_cap24 _ _ NUM3) as C24.
    clear AG STC STC2 HEAP2 AUX2 MI2 ST2 ERR2 PRES23 PRES02 OSS1 LB1 PJC2 SRC.

    unfold os_ch. cbn [ch_fuel ch_cap ch_blk fst snd].
    eapply (PjImpl.implM_pj_chain_stop psegs raw_malloc raw_free ps_so set_so_ps); [lia|]. cbv beta.

    pose proof (rw_cells_join _ _ _ _ _ INL SBW ltac:(cbn [cells_size csize Nat.add]; lia)) as SB88.
    unfold implM. iprefix. lstep. lstep. lstep.
    apply rw_cells_forget in SB88. destruct SB88 as [bs88 SB88]. cbn [app cells_size csize Nat.add] in SB88. clear INL SBW.
    destruct blk2 as [b|].
    -
      destruct BLK2 as (R1 & R2 & R3 & R4 & R5). unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in R4.
      if_cases KG1. { exfalso. unfold bv_eqb in KG1. rewrite !unsigned_lit in KG1 by lia. apply Z.eqb_eq in KG1. lia. }
      lstep. if_cases KG2. { exfalso. unfold bv_eqb in KG2. rewrite !unsigned_lit in KG2 by lia. apply Z.eqb_eq in KG2. lia. }
      clear KG1 KG2. lstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3' end.
      ihere. to_implM. apply implM_del_opt_some. eapply implM_bind.
      { assert (HEAPp : RHEAP sM3 ((b, buf2, cap2) :: osblocks st3 ++ LBall) m3').
        { eapply RHEAP_perm; [exact HEAP3|]. apply Permutation_sym. apply Permutation_middle. }
        eapply (opdel_arr_proof HF) with (B := B) (lo := lo);
          [exact HEAPp| left; reflexivity| exact AUX3| lia| exact ST3| exact CEIL| unfold RFREE_STACK; lia| rewrite ELX; exact ERR3| exact MI3| lia]. }
      cbv beta. intros [] sM4 ms4 PO4. unfold free_postZ in PO4.
      destruct PO4 as (w5 & w6 & w7 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & m4
                       & -> & MI4 & ST4 & ERR4 & AUX4 & PRES34 & FA4 & SO4 & HEAP4).
      assert (ND : List.NoDup (map blk_id ((b, buf2, cap2) :: osblocks st3 ++ LBall))).
      { eapply LH_nodup. eapply RHEAP_perm; [exact HEAP3|]. apply Permutation_sym. apply Permutation_middle. }
      rewrite (lb_remove_hd _ _ _ _ ND) in PRES34, HEAP4.
      replace (ret_pc (Z_to_bv 64 0x3ef64)) with (Z_to_bv 64 0x3ef64) by (apply bv_eq; vm_compute; reflexivity).
      pose proof (agree_of_heap_pres _ _ _ _ PRES34) as AG.
      assert (STC : forall a, q <= a \/ in_block (osblocks st3) a \/ (PJ_LOC_LO <= a < PJ_LOC_HI) -> rclient_addr (osblocks st3 ++ LBall) q a).
      { intros a [Ha|[Ha|Ha]]; [left; exact Ha| right; right; apply in_block_app_l; exact Ha| right; left].
        unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP in *. lia. }
      apply (OSSINV_agree _ _ _ _ _ _ _ AG) in OSS3; [| intros a Ha; apply STC; lia| intros a Ha; apply STC; right; left; exact Ha].
      apply (rw_cells_agree _ _ _ _ _ AG) in SB88; [| intros a Ha; cbn in Ha; apply STC; lia].
      apply (rw_cells_agree _ _ _ _ _ AG) in ELC; [| intros a Ha; cbn in Ha; apply STC; lia].
      apply (rw_cells_agree _ _ _ _ _ AG) in OUT; [| intros a Ha; cbn in Ha; apply STC; lia].
      apply (rw_cells_agree _ _ _ _ _ AG) in R24; [| intros a Ha; cbn in Ha; apply STC; lia].
      apply rw_cells_forget in ELC. destruct ELC as [j392 ELC]. cbn [cells_size csize Nat.add] in ELC.
      eapply okarm_str with (m00 := m) (s00 := s);
        [exact KPOST| exact FRM2| exact MI4| exact ST4| exact ERR4| exact AUX4| congruence| congruence| exact HEAP4
        | eapply lx_pres_trans; [exact PRES03| eapply lx_pres_weaken; [apply lx_pres_of_heap_pres; exact PRES34| lia| intros b0 Hb0; apply in_app_iff; right; exact Hb0| intros a Ha; exact Ha]]
        | exact SJS| exact PJC| exact OSS3| lia| exact SB88| exact OUT| exact ELC| exact R24
        | unfold SJ_PADMAX; clear - LEN; lia| exact CEIL| unfold GLOBALS_TOP; lia| unfold OSS_STR_STACK, RMALLOC_STACK; lia| exact QB| exact B62].
    -
      destruct BLK2 as (-> & -> & ->).
      if_true. ihere. to_implM. apply implM_del_opt_none. cbv beta.
      cbn [app] in HEAP3.
      apply rw_cells_forget in ELC. destruct ELC as [j392 ELC]. cbn [cells_size csize Nat.add] in ELC.
      eapply okarm_str with (m00 := m) (s00 := s);
        [exact KPOST| exact FRM2| exact MI3| exact ST3| rewrite ELX; exact ERR3| exact AUX3| congruence| congruence| exact HEAP3| exact PRES03
        | exact SJS| exact PJC| exact OSS3| lia| exact SB88| exact OUT| exact ELC| exact R24
        | unfold SJ_PADMAX; clear - LEN; lia| exact CEIL| unfold GLOBALS_TOP; lia| unfold OSS_STR_STACK, RMALLOC_STACK; lia| exact QB| exact B62].
  Qed.

End Proofs.
End WithCeiling0.
