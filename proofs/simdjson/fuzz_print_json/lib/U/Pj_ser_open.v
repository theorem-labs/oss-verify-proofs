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
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel PjModel Target Prog PjImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjAlloc SjTape SjTapeList SjTapeTile SjPjSer SjPjCont.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_h_kit F_memcpy.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Pj_defs Pj_kit Pj_copy Pj_grow Pj_stmts Pj_ser_defs Pj_ser_kit Pj_ser_calls Pj_ser_loop_defs Pj_ser_ends Pj_cont_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require SFModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_store ::= first [ pj_solve_store0 | pj_store_wr ].
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Local Ltac pj_st_eq_leaf ::=
  lazymatch goal with
  | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [reflexivity | f_equal; cbn [length]; lia]
  | |- _ => reflexivity
  end.

Lemma tnext_pred : forall w e, tnext w = e + 1 -> 0 <= e -> 0 <= w -> Z.land (w + -1) 4294967295 = e.
Proof.
  intros w e H He Hw. rewrite land_low32. unfold tnext in *.
  pose proof (Z.mod_pos_bound w 4294967296 ltac:(lia)) as B.
  change (2 ^ 32) with 4294967296 in *.
  rewrite <- Zplus_mod_idemp_l. rewrite H. replace (e + 1 + -1) with e by lia. apply Z.mod_small. lia.
Qed.
Lemma tnext_pred' : forall w e, tnext w = e + 1 -> 0 <= e -> 0 <= w ->
  Z.land (Z.land (w + -1) 18446744073709551615) 4294967295 = e.
Proof.
  intros w e H He Hw. rewrite <- Z.land_assoc. change (Z.land 18446744073709551615 4294967295) with 4294967295. apply tnext_pred; assumption.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma ser_call_cont : forall (k : bool) (d' : nat) (E : senv) (Q : @chst bptr -> PState -> machine_state -> Prop) (e64 e72 e80 spill : word) (isobj : list byte)
       (st : sbst) (s : PState) (m : mem) (i e n c c2 rpc : Z) (F : bvmap 5 word) (fc : bv 32)
       (t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  cont_stmt k d' ->
  senv_ok E -> SERM E e64 e72 e80 spill isobj st s m -> frm0 fc ->
  e_lo E <= e_q E + -256 - cont_need d' ->
  ty (e_T E) i = (if k then t_obj else t_arr) -> tnext (e_T E i) = e + 1 -> ty (e_T E) e = end_ty k ->
  tilesS (itemS (e_T E) (e_S E) (e_sn E) k d') (i + 1) e n c c2 ->
  1 <= i -> e + 1 <= e_n E -> 0 <= c -> c2 <= e_sn E ->
  sb_acc1 st i c ->
  0 <= rpc < 2^64 -> rpc mod 2 = 0 ->
  (forall (st' : sbst) (s' : PState) (m' : mem) (F' : bvmap 5 word) (fc' : bv 32)
          (xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
      SERM E e64 e72 e80 spill isobj st' s' m' -> frm0 fc' -> sb_acc st' (e + 1) c2 ->
      evt usegs (sgoal E Q (sb_ch st') s')
          (SST E rpc (Z_to_bv 64 rpc) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6 F' fc' m')) ->
  evt usegs (sgoal E Q (sb_ch st) s)
      (SST E (if k then PJ_APPEND_OBJ else PJ_APPEND_ARR) (Z_to_bv 64 rpc) t0 t1 t2 (Z_to_bv 64 (e_SB E)) (Z_to_bv 64 (e_DOC E)) (Z_to_bv 64 i) a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros k d' E Q e64 e72 e80 spill isobj st s m i e n c c2 rpc F fc t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         CONT OK HSM FRM STK HTY HNX HTE HT HI HE HC HC2 ACC RP0 RP2 HK.
  pose proof (SBINV_of_SERM _ _ _ _ _ _ _ _ _ HSM) as INV.
  pose proof OK as [_ _ _ _ OKT OKS HLEN [L1 L2] [Q1 Q2] B63 [S1 S2] [D1 D2] SEP _ _ [AL1 AL2]].
  pose proof HSM as [HR HC0].
  pose proof HR as (HEAP & AUX & PRES & TAPEB & SBUFB & DOCC & (errv & ERR) & FA & SO & PURE).
  pose proof HC0 as ((j0 & FRA) & FRI & FRIL & FRT & FRS & SV & SZ & BUFS & INLS & MI & ST).
  assert (DOCR : DOCREP m (e_LB0 E) (e_DOC E) (e_TAPE E) (e_SBUF E) (e_len E) (e_tws E) (e_sbs E)).
  { pose proof OK as [WF SBS TSZ SSZ _ _ _ _ _ _ _ _ _ _ _ _].
    unfold DOCREP. split; [exact DOCC|]. split; [exact TAPEB|]. split; [exact SBUFB|]. split; [exact WF|]. split; [exact SBS|].
    split; [exact TSZ|]. split; [exact SSZ|]. split; [exact OKT| exact OKS]. }
  apply evt_done. unfold sgoal.
  apply implM_pj_part_seq.
  eapply implM_bind.
  { eapply (CONT (Z_to_bv 64 rpc) (e_gp E) t0 t1 t2 (Z_to_bv 64 (e_DOC E)) (Z_to_bv 64 (e_SB E)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m s (e_LB0 E) (e_q E + -256) (e_lo E) (e_B E) errv (e_SB E) (e_len E) st (e_DOC E) (e_TAPE E) (e_SBUF E) (e_tws E) (e_sbs E) i e n c c2);
      [exact HEAP| exact AUX| lia| exact B63| exact ST| exact L1| exact L2| lia
      | exact ERR| exact MI| exact FRM| lia| exact S2| lia| exact D2| exact SEP| exact HLEN| exact INV| exact DOCR| exact AL1| exact AL2
      | exact HTY| exact HNX| exact HTE| exact HT| exact HI| exact HE| exact HC| exact HC2| exact ACC]. }
  cbv beta. intros ch' s' ms' PO. unfold ser_post in PO.
  destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & F' & fc' & m' & errv' & st'
                  & -> & MI' & ST' & ERR' & AUX' & FRM' & FA' & SO' & -> & HEAP' & INV' & ACC' & PRES').
  rewrite (ret_pc_even rpc RP0 RP2).
  assert (HSM' : SERM E e64 e72 e80 spill isobj st' s' m').
  { pose proof (agree_of_lx_pres _ _ _ _ _ PRES') as AG.
    assert (UP : forall a, e_q E + -256 <= a -> ~ (e_SB E <= a < e_SB E + 88) -> lx_client (e_LB0 E) (e_q E + -256) [(e_SB E, e_SB E + 88)] a).
    { intros a Ha Hn. split; [cbn [rin_ivs fst snd]; tauto| left; exact Ha]. }
    assert (BL : forall a, in_block (e_LB0 E) a -> lx_client (e_LB0 E) (e_q E + -256) [(e_SB E, e_SB E + 88)] a).
    { intros a Ha. split; [| right; left; exact Ha].
      assert (BLa : 0 < a < alloc_ceiling).
      { eapply blocks_below; [exact HEAP|]. destruct Ha as (b0 & Hb0 & Hr). exists b0. split; [apply in_or_app; right; exact Hb0| exact Hr]. }
      unfold PJ_GROW_STACK, RMALLOC_STACK in *. cbn [rin_ivs fst snd]. lia. }
    split.
    - unfold SREF. split; [exact HEAP'|]. split; [exact AUX'|].
      split. { eapply lx_pres_trans; [exact PRES|]. eapply lx_pres_weaken; [exact PRES'| lia| intros b0 Hb0; exact Hb0|].
               intros a Ha. exact Ha. }
      split. { eapply bytes_at_agree; [exact AG| exact TAPEB|]. intros a Ha. rewrite u64s_length, length_map in Ha.
               apply BL. eapply in_blocks_in_block; [exact OKT| lia]. }
      split. { eapply bytes_at_agree; [exact AG| exact SBUFB|]. intros a Ha. rewrite length_map in Ha.
               apply BL. eapply in_blocks_in_block; [exact OKS| lia]. }
      split. { eapply rw_cells_agree; [exact AG| exact DOCC|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply UP; lia. }
      split. { exists errv'. exact ERR'. }
      split; [congruence|]. split; [congruence|]. eapply sb_pure_of_SBINV; exact INV'.
    - pose proof INV' as (SV' & SZ' & (bs' & BUF') & (ji' & INL') & _).
      unfold SCUR. split.
      { exists j0. eapply rw_cells_agree; [exact AG| exact FRA|]. intros a Ha. cbn [cells_size csize Nat.add ser_consts length] in Ha. apply UP; lia. }
      split. { eapply u8arr_agree; [exact AG| exact FRI|]. intros a Ha. rewrite FRIL in Ha. apply UP; lia. }
      split; [exact FRIL|].
      split. { eapply stk_agree; [exact AG| exact FRT|]. intros a Ha. apply UP; lia. }
      split. { eapply rw_cells_agree; [exact AG| exact FRS|]. intros a Ha. unfold ser_saved in Ha. cbn [cells_size csize Nat.add] in Ha. apply UP; lia. }
      split; [exact SV'|]. split; [exact SZ'|].
      split. { pose proof (stk_of_rw_cells usegs _ _ _ BUF') as S. cbn [cells_size csize Nat.add] in S.
               pose proof (SBINV_cap_pos _ _ _ _ INV') as CP. rewrite Nat.add_0_r, Z2Nat.id in S by lia. exact S. }
      split. { pose proof (stk_of_rw_cells usegs _ _ _ INL') as S. cbn [cells_size csize Nat.add] in S. exact S. }
      split; [exact MI'|]. exact ST'. }
  unfold implM. apply impl_from_evt.
  change (evt usegs (sgoal E Q (sb_ch st') s')
            (SST E rpc (Z_to_bv 64 rpc) r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r28 r29 r30 r31 F' fc' m')).
  apply HK; [exact HSM'| exact FRM'| exact ACC'].
Qed.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.
  Variable E : senv.
  Variable Q : @chst bptr -> PState -> machine_state -> Prop.
  Variable D : nat.
  Variable f : nat.
  Hypothesis OK : senv_ok E.
  Hypothesis KX : exit_K E Q.
  Hypothesis KH : head_stmt E Q D f.

  Notation REST := (rest_ok (e_T E) (e_S E) (e_sn E)).
  Notation TM := (Z_to_bv 64 PJ_TMASK).
  Notation RB := (Z_to_bv 64 PJ_RBR56).
  Notation ESCW := (Z_to_bv 64 PJ_ESC_TAB).
  Notation LBSW := (Z_to_bv 64 PJ_LIT_BS).
  Notation LQUW := (Z_to_bv 64 PJ_LIT_QU).

  Lemma open_empty : forall (k : bool) (d1 : nat) (ks : list bool) (i c : Z) (isobj : list byte) (st : sbst) (s : PState) (m : mem)
      (F : bvmap 5 word) (fc : bv 32) (spill : word)
      (xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    e_j E - (i + 2) <= Z.of_nat f -> (d1 + length ks = D)%nat -> (length ks <= 15)%nat -> kinds_rel ks isobj ->
    REST d1 ks (i + 2) c (e_j E) (e_c' E) -> 1 <= i -> 0 <= c ->
    SERMC E spill isobj st s m -> frm0 fc -> sb_size st + 1 <= 41 * (i + 1) + 6 * c + 2 -> sb_size st + 1 <= sb_cap st ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (LST E (if k then 0x3e530 else 0x3e3d0) (i + 1) (Z.of_nat (length ks)) TM RB xra xt0 xt1 xt2
             (Z_to_bv 64 (sb_size st)) (Z_to_bv 64 (sb_size st + 1)) xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF OK KX KH.
    intros k d1 ks i c isobj st s m F fc spill xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6
           HF0 HD HL KR HR HI HC HSM FRM ACC ROOM.
    pose proof OK as [WF _ _ _ _ _ _ _ _ _ _ _ _ [J1 J2] [CC1 CC2] _].
    pose proof WF as ((N1 & N2) & SN & _).
    pose proof (rest_ok_le _ _ _ _ _ _ _ _ _ HR) as (LEJ & LEC & _).
    destruct st as [buf size cap blk fuel]. cbn [sb_size sb_cap] in *.
    ser_env OK. ser_open HSM OK.
    assert (AV : forall (st5 : sbst) (s5 : PState) (m5 : mem) (yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
      SERMC E spill isobj st5 s5 m5 -> sb_size st5 = size + 1 ->
      evt usegs (sgoal E Q (sb_ch st5) s5)
          (LST E PJ_AV1 (i + 1) (Z.of_nat (length ks)) TM RB yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 F fc m5)).
    { intros st5 s5 m5 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM5 ESZ.
      replace (i + 1) with (i + 2 - 1) by lia.
      eapply (aval_proof HM HF E Q D f OK KX KH PJ_AV1 d1 ks (i + 2) c isobj st5);
        [right; reflexivity| right; reflexivity| exact HF0| exact HD| exact HL| exact KR| exact HR| lia| lia| exact HSM5| exact FRM| lia]. }
    destruct k.
    -
      step. zstep. step. step. gtrap. zstep. zstep. zstep. unz. change (Z.lxor 1 0) with 1%Z. zstep. if_false. gtrap.
      step. step. pj_store_done. step.
      ser_close HSM2 OK.
      eapply (AV (mkSb buf (size + 1) cap blk fuel)); [exact HSM2| reflexivity].
    -
      step. zstep. step. gtrap. zstep. zstep. zstep. unz. change (Z.lxor 1 0) with 1%Z. zstep. if_false. gtrap.
      step. pj_store_done. step.
      ser_close HSM2 OK.
      eapply (AV (mkSb buf (size + 1) cap blk fuel)); [exact HSM2| reflexivity].
  Qed.

  Lemma open_push : forall (k : bool) (d1 : nat) (ks : list bool) (i i3 c c3 : Z) (isobj : list byte) (st : sbst) (s : PState) (m : mem)
      (F : bvmap 5 word) (fc : bv 32) (spill : word)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    e_j E - (i + 1) <= Z.of_nat f -> (d1 + S (length ks) = D)%nat -> (length ks + 1 <= 15)%nat -> kinds_rel ks isobj ->
    itemS (e_T E) (e_S E) (e_sn E) k d1 (i + 1) i3 c c3 -> REST d1 (k :: ks) i3 c3 (e_j E) (e_c' E) -> 1 <= i -> 0 <= c ->
    SERMC E spill isobj st s m -> frm0 fc -> sb_size st <= 41 * i + 6 * c + 2 ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (LST E (if k then 0x3ee44 else 0x3ee18) (i + 1) (Z.of_nat (length ks)) TM RB xra xt0 xt1 xt2
             xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 F fc m).
  Proof using OK KH.
    intros k d1 ks i i3 c c3 isobj st s m F fc spill xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6
           HF0 HD HL KR HIT HR HI HC HSM FRM ACC.
    destruct st as [buf size cap blk fuel]. cbn [sb_size sb_cap] in *.
    ser_env OK. ser_open HSM OK.
    pose proof (u8arr_store_ok usegs _ (e_q E + -160) isobj (Z.of_nat (length ks) + 1) (wa (e_q E + -160 + (Z.of_nat (length ks) + 1))) FRI ltac:(lia) eq_refl) as SOK1.
    pose proof (kinds_rel_push ks isobj k KR ltac:(lia)) as KR'.
    destruct k; unfold kbyte in KR'.
    -
      step. gtrap. step. zstep. zstep. step.
      change (le1 (Z_to_bv 64 1)) with [Z_to_bv 8 1].
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
        pose proof (u8arr_write usegs mm (e_q E + -160) isobj (Z.of_nat (length ks) + 1) (Z_to_bv 8 1) FRI ltac:(lia)) as FRI' end.
      replace (Z.to_nat (Z.of_nat (length ks) + 1)) with (length ks + 1)%nat in FRI' by lia.
      store_done.
      rewrite <- (upd_length isobj (length ks + 1) (Z_to_bv 8 1)) in FRIL. rename FRI' into FRI.

      step. step.
      ser_close HSM2 OK.
      eapply evt_eq; [| eapply (KH d1 (true :: ks) (i + 1) i3 c c3 false _ (mkSb buf size cap blk fuel))];
        [pj_st_eq| exact HF0| cbn [length]; lia| cbn [length]; lia| exact KR'| exact HIT| exact HR| reflexivity| lia| lia
        | exact HSM2| exact FRM| cbn [sb_size]; lia].
    -
      step. gtrap. step. zstep. zstep. step.
      first [change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] | change (Z_to_le_bytes 1 0) with [Z_to_bv 8 0]].
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
        pose proof (u8arr_write usegs mm (e_q E + -160) isobj (Z.of_nat (length ks) + 1) (Z_to_bv 8 0) FRI ltac:(lia)) as FRI' end.
      replace (Z.to_nat (Z.of_nat (length ks) + 1)) with (length ks + 1)%nat in FRI' by lia.
      store_done.
      rewrite <- (upd_length isobj (length ks + 1) (Z_to_bv 8 0)) in FRIL. rename FRI' into FRI.
      step. step.
      ser_close HSM2 OK.
      eapply evt_eq; [| eapply (KH d1 (false :: ks) (i + 1) i3 c c3 false _ (mkSb buf size cap blk fuel))];
        [pj_st_eq| exact HF0| cbn [length]; lia| cbn [length]; lia| exact KR'| exact HIT| exact HR| reflexivity| lia| lia
        | exact HSM2| exact FRM| cbn [sb_size]; lia].
  Qed.

  Lemma open_mid : forall (k : bool) (d' : nat) (ks : list bool) (i e n c c2 : Z) (isobj : list byte) (st : sbst) (s : PState) (m : mem)
      (F : bvmap 5 word) (fc : bv 32) (spill : word)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    e_j E - (i + 1) <= Z.of_nat f -> (S d' + length ks = D)%nat -> (length ks + 1 <= 15)%nat -> kinds_rel ks isobj ->
    ty (e_T E) e = end_ty k ->
    tilesS (itemS (e_T E) (e_S E) (e_sn E) k d') (i + 1) e n c c2 ->
    REST (S d') ks (e + 1) c2 (e_j E) (e_c' E) -> 1 <= i -> 0 <= c ->
    SERMC E spill isobj st s m -> frm0 fc -> sb_size st <= 41 * (i - 1) + 6 * c + 3 -> sb_size st + 1 <= sb_cap st ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (LST E (if k then 0x3e4bc else 0x3e35c) i (Z.of_nat (length ks)) TM RB xra xt0 xt1 xt2
             xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF OK KX KH.
    intros k d' ks i e n c c2 isobj st s m F fc spill xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6
           HF0 HD HL KR He Ht HR HI HC HSM FRM ACC ROOM.
    pose proof OK as [WF _ _ _ _ _ _ _ _ _ _ _ _ [J1 J2] [CC1 CC2] [AL1 AL2]].
    pose proof WF as ((N1 & N2) & SN & _).
    pose proof (senv_out E OK) as OUTB.
    pose proof (rest_ok_le _ _ _ _ _ _ _ _ _ HR) as (LEJ & LEC & _).
    pose proof (tilesS_le _ (itemS_lt (e_T E) (e_S E) (e_sn E) k d') _ _ _ _ _ Ht) as (LIE & _).
    pose proof (tilesS_cur _ (e_sn E) (itemS_cur (e_T E) (e_S E) (e_sn E) k d') _ _ _ _ _ Ht) as (LCC & _).
    pose proof (rest_ok_open (e_T E) (e_S E) (e_sn E) d' ks k i e n c c2 (e_j E) (e_c' E) Ht He HR) as HR'.
    pose proof (rest_ok_word (e_T E) (e_S E) (e_sn E) SN d' k ks (i + 1) c (e_j E) (e_c' E) HR' ltac:(lia) ltac:(lia)) as WR.
    pose proof (ser_ranges _ _ _ _ _ _ _ _ _ OK HSM) as (TP0 & TP1 & _ & _).
    set (w := e_T E (i + 1)) in *.
    set (t := ttype w) in *.
    assert (TYR : 0 <= t < 256) by (subst t; unfold ttype; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    destruct st as [buf size cap blk fuel]. cbn [sb_size sb_cap] in *.
    ser_env OK.

    assert (NONEMPTY : forall (st5 : sbst) (s5 : PState) (m5 : mem) (yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
      t <> end_ty k -> SERMC E spill isobj st5 s5 m5 -> sb_size st5 = size + 1 ->
      evt usegs (sgoal E Q (sb_ch st5) s5)
          (LST E (if k then 0x3ee44 else 0x3ee18) (i + 1) (Z.of_nat (length ks)) TM RB yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 F fc m5)).
    { intros st5 s5 m5 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 NT HSM5 ESZ.
      assert (NA : SjTape.ty (e_T E) (i + 1) <> t_arr_end /\ SjTape.ty (e_T E) (i + 1) <> t_obj_end).
      { destruct (Z.eq_dec (i + 1) e) as [EE|NE].
        - exfalso. rewrite <- EE in He. unfold SjTape.ty in He. fold w t in He. congruence.
        - destruct (tilesS_next _ (itemS_lt (e_T E) (e_S E) (e_sn E) k d') _ _ _ _ _ Ht NE) as (i3 & c3 & HIT & LE3 & _).
          eapply (itemS_not_end (e_T E) (e_S E) (e_sn E) SN k d' (i + 1) i3 c c3 HIT); lia. }
      destruct (rest_ok_item (e_T E) (e_S E) (e_sn E) SN d' k ks (i + 1) c (e_j E) (e_c' E) HR' (proj1 NA) (proj2 NA))
        as (i3 & c3 & HIT & HR3).
      eapply (open_push k d' ks i i3 c c3 isobj st5); [lia| lia| lia| exact KR| exact HIT| exact HR3| lia| lia| exact HSM5| exact FRM| lia]. }
    assert (EMPTY : forall (st5 : sbst) (s5 : PState) (m5 : mem) (yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
      t = end_ty k -> SERMC E spill isobj st5 s5 m5 -> sb_size st5 = size + 1 ->
      evt usegs (sgoal E Q (sb_ch st5) s5)
          (LST E (if k then 0x3e50c else 0x3e3ac) (i + 1) (Z.of_nat (length ks)) TM RB yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 F fc m5)).
    { intros st5 s5 m5 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 ET HSM5 ESZ.
      assert (HEND : SjTape.ty (e_T E) (i + 1) = t_arr_end \/ SjTape.ty (e_T E) (i + 1) = t_obj_end).
      { unfold SjTape.ty. fold w t. rewrite ET. destruct k; cbn [end_ty]; tauto. }
      pose proof (rest_ok_end (e_T E) (e_S E) (e_sn E) SN d' k ks (i + 1) c (e_j E) (e_c' E) HR' ltac:(lia) ltac:(lia) HEND) as HR2.
      replace (i + 1 + 1) with (i + 2) in HR2 by lia.
      pose proof (rest_ok_le _ _ _ _ _ _ _ _ _ HR2) as (LEJ2 & LEC2 & _).
      destruct st5 as [buf5 size5 cap5 blk5 fuel5]. cbn [sb_size sb_cap] in ESZ. subst size5.
      assert (TAIL : forall (st6 : sbst) (s6 : PState) (m6 : mem) (zra zt0 zt1 zt2 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 : word),
        SERMC E spill isobj st6 s6 m6 -> sb_size st6 = size + 1 -> size + 2 <= sb_cap st6 ->
        evt usegs (sgoal E Q (sb_ch st6) s6)
            (LST E (if k then 0x3e530 else 0x3e3d0) (i + 1) (Z.of_nat (length ks)) TM RB zra zt0 zt1 zt2
                 (Z_to_bv 64 (size + 1)) (Z_to_bv 64 (size + 2)) za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 F fc m6)).
      { intros st6 s6 m6 zra zt0 zt1 zt2 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 HSM6 ESZ6 ROOM6.
        eapply evt_eq; [| eapply (open_empty k (S d') ks i c isobj st6 s6 m6 F fc spill)];
          [pj_st_eq| lia| exact HD| lia| exact KR| exact HR2| lia| lia| exact HSM6| exact FRM| lia| lia]. }
      ser_open HSM5 OK.
      destruct k.
      -
        step. step. zstep. step.
        if_cases K2; zify_cond K2.
        * pjnorm_in K2. ser_close HSM6 OK. eapply (TAIL (mkSb buf5 (size + 1) cap5 blk5 fuel5)); [exact HSM6| reflexivity| cbn [sb_cap]; lia].
        * pjnorm_in K2.

          zstep. pjnorm. step. step.
          ser_close HSM6 OK.
          eapply (ser_grow HM HF) with (st := mkSb buf5 (size + 1) cap5 blk5 fuel5) (z := 2 * cap5) (rpc := 0x3e528); [exact OK| exact HSM6| | lia| reflexivity|].
          { eapply (ser_req_ok2 E _ _ _ _ _ _ _ _ OK HSM6). cbn [sb_cap]. lia. }
          intros s' m' b' NEW wt0 wt1 wt2 wa0 wa1 wa2 wa3 wa4 wa5 wa6 wa7 wt3 wt4 wt5 wt6 HSM7.
          ser_open HSM7 OK.

          step. zstep.
          ser_close HSM8 OK.
          eapply TAIL; [exact HSM8| reflexivity| unfold sb_grown; cbn [sb_cap]; lia].
      - step. step. zstep. step.
        if_cases K2; zify_cond K2.
        * pjnorm_in K2. ser_close HSM6 OK. eapply (TAIL (mkSb buf5 (size + 1) cap5 blk5 fuel5)); [exact HSM6| reflexivity| cbn [sb_cap]; lia].
        * pjnorm_in K2.
          zstep. pjnorm. step. step.
          ser_close HSM6 OK.
          eapply (ser_grow HM HF) with (st := mkSb buf5 (size + 1) cap5 blk5 fuel5) (z := 2 * cap5) (rpc := 0x3e3c8); [exact OK| exact HSM6| | lia| reflexivity|].
          { eapply (ser_req_ok2 E _ _ _ _ _ _ _ _ OK HSM6). cbn [sb_cap]. lia. }
          intros s' m' b' NEW wt0 wt1 wt2 wa0 wa1 wa2 wa3 wa4 wa5 wa6 wa7 wt3 wt4 wt5 wt6 HSM7.
          ser_open HSM7 OK.
          step. zstep.
          ser_close HSM8 OK.
          eapply TAIL; [exact HSM8| reflexivity| unfold sb_grown; cbn [sb_cap]; lia]. }
    destruct k.
    -
      ser_open HSM OK.

      step. step. zstep. zstep. step. gtrap. zstep. zstep. zstep. unz. change (Z.lxor 1 0) with 1%Z. zstep. if_false. gtrap.

      step. step. pj_store_done.
      pose proof (doc_cells_mu E _ _ _ _ OK HREF MU WM) as DOCC.
      pose proof (tape_read_mu E _ _ _ _ (i + 1) OK HREF MU WM ltac:(lia)) as RDT. fold w in RDT.

      zstep. step. step. step.
      eapply tape_ref_call; [exact DOCC| exact AL2| lia| lia| lia| lia| reflexivity|].

      step. zstep. unfold PJ_TMASK. rewrite (land_tmask w) by lia. fold t. step.
      ser_close HSM2 OK.
      if_cases K1; zify_cond K1; unfold PJ_RBR56, PJ_RBK56 in K1; pjnorm_in K1;
      [ eapply (NONEMPTY (mkSb buf (size + 1) cap blk fuel)); [cbn [end_ty]; unfold t_obj_end, t_arr_end; lia| exact HSM2| reflexivity]
      | eapply (EMPTY (mkSb buf (size + 1) cap blk fuel)); [cbn [end_ty]; unfold t_obj_end, t_arr_end; lia| exact HSM2| reflexivity] ].
    -
      ser_open HSM OK.

      step. step. zstep. zstep. step. gtrap. zstep. zstep. zstep. unz. change (Z.lxor 1 0) with 1%Z. zstep. if_false. gtrap.

      step. step. pj_store_done.
      pose proof (doc_cells_mu E _ _ _ _ OK HREF MU WM) as DOCC.
      pose proof (tape_read_mu E _ _ _ _ (i + 1) OK HREF MU WM ltac:(lia)) as RDT. fold w in RDT.

      zstep. step. step. step.
      eapply tape_ref_call; [exact DOCC| exact AL2| lia| lia| lia| lia| reflexivity|].

      step. zstep. unfold PJ_TMASK. rewrite (land_tmask w) by lia. fold t. step.
      ser_close HSM2 OK.
      if_cases K1; zify_cond K1; unfold PJ_RBR56, PJ_RBK56 in K1; pjnorm_in K1;
      [ eapply (NONEMPTY (mkSb buf (size + 1) cap blk fuel)); [cbn [end_ty]; unfold t_obj_end, t_arr_end; lia| exact HSM2| reflexivity]
      | eapply (EMPTY (mkSb buf (size + 1) cap blk fuel)); [cbn [end_ty]; unfold t_obj_end, t_arr_end; lia| exact HSM2| reflexivity] ].
  Qed.

  Hypothesis REC : rec_ok D.
  Hypothesis STK : e_lo E <= e_q E - ser_need D.

  Lemma open_ret : forall (d1 : nat) (ks : list bool) (i e c2 : Z) (isobj : list byte) (st : sbst) (s : PState) (m : mem)
      (F : bvmap 5 word) (fc : bv 32) (spill : word)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 : word),
    ks <> [] -> e_j E - (e + 1) <= Z.of_nat f -> (d1 + length ks = D)%nat -> (length ks <= 15)%nat -> kinds_rel ks isobj ->
    tnext (e_T E i) = e + 1 -> 0 <= e_T E i < 2^64 ->
    REST d1 ks (e + 1) c2 (e_j E) (e_c' E) -> 1 <= i -> i < e -> 0 <= c2 ->
    SERMC E spill isobj st s m -> frm0 fc -> sb_size st <= 41 * e + 6 * c2 + 2 ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (LST E 0x3ee94 i (Z.of_nat (length ks)) TM RB xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF OK KX KH.
    intros d1 ks i e c2 isobj st s m F fc spill xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6
           NE HF0 HD HL KR HNX WR HR HI HIE HC2 HSM FRM ACC.
    pose proof OK as [WF _ _ _ _ _ _ _ _ _ _ _ _ [J1 J2] [CC1 CC2] [AL1 AL2]].
    pose proof WF as ((N1 & N2) & SN & _).
    pose proof (rest_ok_le _ _ _ _ _ _ _ _ _ HR) as (LEJ & LEC & _).
    pose proof (ser_ranges _ _ _ _ _ _ _ _ _ OK HSM) as (TP0 & TP1 & _ & _).
    pose proof HSM as HSM0.
    destruct st as [buf size cap blk fuel]. cbn [sb_size sb_cap] in *.
    ser_env OK. ser_open HSM OK.
    pose proof (doc_cells_mu E _ _ _ _ OK HREF MU WM) as DOCC.
    pose proof (tape_read_mu E _ _ _ _ i OK HREF MU WM ltac:(lia)) as RDT.
    set (w := e_T E i) in *.

    step. step. step.
    eapply tape_ref_call; [exact DOCC| exact AL2| lia| lia| lia| lia| reflexivity|].

    step. zstep. zstep. zstep.
    first [rewrite (tnext_pred w e HNX ltac:(lia) ltac:(lia)) | rewrite (tnext_pred' w e HNX ltac:(lia) ltac:(lia))].
    step. zstep.
    ser_close HSM2 OK.
    eapply evt_eq; [| eapply (ends_loop HM HF E Q D f OK KX KH ks d1 (e + 1) c2 isobj (mkSb buf size cap blk fuel))];
      [pj_st_eq| exact NE| exact HF0| exact HD| exact HL| exact KR| exact HR| lia| lia| exact HSM2| exact FRM| cbn [sb_size]; lia].
  Qed.

  Lemma open_rec : forall (k : bool) (d' : nat) (ks : list bool) (i e n c c2 : Z) (isobj : list byte) (st : sbst) (s : PState) (m : mem)
      (F : bvmap 5 word) (fc : bv 32) (spill : word)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    e_j E - (i + 1) <= Z.of_nat f -> (S d' + length ks = D)%nat -> length ks = 15%nat -> kinds_rel ks isobj ->
    ty (e_T E) i = (if k then t_obj else t_arr) -> tnext (e_T E i) = e + 1 -> ty (e_T E) e = end_ty k ->
    tilesS (itemS (e_T E) (e_S E) (e_sn E) k d') (i + 1) e n c c2 ->
    REST (S d') ks (e + 1) c2 (e_j E) (e_c' E) -> 1 <= i -> 0 <= c ->
    SERMC E spill isobj st s m -> frm0 fc -> sb_size st <= 41 * (i - 1) + 6 * c + 3 ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (LST E (if k then 0x3ee84 else 0x3ee70) i (Z.of_nat (length ks)) TM RB xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
             xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF OK KX KH REC STK.
    intros k d' ks i e n c c2 isobj st s m F fc spill xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6
           HF0 HD HL KR HTY HNX He Ht HR HI HC HSM FRM ACC.
    pose proof OK as [WF _ _ _ _ _ _ _ _ _ _ _ _ [J1 J2] [CC1 CC2] _].
    pose proof WF as ((N1 & N2) & SN & _).
    pose proof (rest_ok_le _ _ _ _ _ _ _ _ _ HR) as (LEJ & LEC & _).
    pose proof (tilesS_le _ (itemS_lt (e_T E) (e_S E) (e_sn E) k d') _ _ _ _ _ Ht) as (LIE & _).
    pose proof (tilesS_cur _ (e_sn E) (itemS_cur (e_T E) (e_S E) (e_sn E) k d') _ _ _ _ _ Ht) as (LCC & _).
    assert (WR : 0 <= e_T E i < 2^64).
    { eapply ttype_range; [exact HTY|]. destruct k; unfold t_obj, t_arr; lia. }
    assert (CONT : cont_stmt k d') by (apply REC; lia).
    assert (STK' : e_lo E <= e_q E + -256 - cont_need d').
    { unfold cont_need. unfold ser_need in *. lia. }
    assert (NE : ks <> []) by (intros ->; cbn in HL; lia).
    assert (KRET : forall (st' : sbst) (s' : PState) (m' : mem) (F' : bvmap 5 word) (fc' : bv 32)
          (yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
      SERMC E spill isobj st' s' m' -> frm0 fc' -> sb_acc st' (e + 1) c2 ->
      evt usegs (sgoal E Q (sb_ch st') s')
          (LST E 0x3ee94 i (Z.of_nat (length ks)) TM RB yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 F' fc' m')).
    { intros st' s' m' F' fc' yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM' FRM' ACC'.
      unfold sb_acc in ACC'.
      eapply (open_ret (S d') ks i e c2 isobj st'); try eassumption; lia. }
    destruct k.
    -
      step. step. step. step.
      eapply evt_eq; [| eapply (ser_call_cont true d' E Q ESCW LBSW LQUW spill isobj st s m i e n c c2 0x3ee94)];
        [pj_st_eq| exact CONT| exact OK| exact HSM| exact FRM| exact STK'| exact HTY| exact HNX| exact He| exact Ht| exact HI| lia| exact HC| lia
        | exact ACC| lia| reflexivity|].
      intros st' s' m' F' fc' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM' FRM' ACC'.
      eapply (KRET st'); eassumption.
    -
      step. step. step. step.
      eapply evt_eq; [| eapply (ser_call_cont false d' E Q ESCW LBSW LQUW spill isobj st s m i e n c c2 0x3ee80)];
        [pj_st_eq| exact CONT| exact OK| exact HSM| exact FRM| exact STK'| exact HTY| exact HNX| exact He| exact Ht| exact HI| lia| exact HC| lia
        | exact ACC| lia| reflexivity|].
      intros st' s' m' F' fc' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM' FRM' ACC'.
        step.
      eapply (KRET st'); eassumption.
  Qed.

  Theorem open_proof : forall k, open_stmt E Q D f k.
  Proof using HM HF OK KX KH REC STK.
    intros k. unfold open_stmt.
    intros d' ks i e n c c2 isobj st s m F fc spill xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6
           HF0 HD HL KR HTY HNX He Ht HR HI HC HSM FRM ACC.
    pose proof OK as [WF _ _ _ _ _ _ _ _ _ _ _ _ [J1 J2] [CC1 CC2] _].
    pose proof WF as ((N1 & N2) & SN & _).
    pose proof (senv_out E OK) as OUTB.
    pose proof (rest_ok_le _ _ _ _ _ _ _ _ _ HR) as (LEJ & LEC & _).
    pose proof (tilesS_le _ (itemS_lt (e_T E) (e_S E) (e_sn E) k d') _ _ _ _ _ Ht) as (LIE & _).
    pose proof (tilesS_cur _ (e_sn E) (itemS_cur (e_T E) (e_S E) (e_sn E) k d') _ _ _ _ _ Ht) as (LCC & _).
    pose proof HSM as HSM0.
    destruct st as [buf size cap blk fuel]. cbn [sb_size sb_cap] in *.
    ser_env OK.
    assert (TAIL : forall (st5 : sbst) (s5 : PState) (m5 : mem) (yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
      (length ks + 1 <= 15)%nat ->
      SERMC E spill isobj st5 s5 m5 -> sb_size st5 = size -> size + 1 <= sb_cap st5 ->
      evt usegs (sgoal E Q (sb_ch st5) s5)
          (LST E (if k then 0x3e4bc else 0x3e35c) i (Z.of_nat (length ks)) TM RB yra yt0 yt1 yt2
               ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 F fc m5)).
    { intros st5 s5 m5 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HL1 HSM5 ESZ ROOM5.
      eapply (open_mid k d' ks i e n c c2 isobj st5 s5 m5 F fc spill);
        [exact HF0| exact HD| exact HL1| exact KR| exact He| exact Ht| exact HR| exact HI| exact HC| exact HSM5| exact FRM| lia| lia]. }
    destruct k.
    -
      step. step.
      if_cases K0; zify_cond K0.
      + pjnorm_in K0.
        eapply (open_rec true d' ks i e n c c2 isobj (mkSb buf size cap blk fuel) s m F fc spill);
          [exact HF0| exact HD| lia| exact KR| exact HTY| exact HNX| exact He| exact Ht| exact HR| exact HI| exact HC| exact HSM0| exact FRM| cbn [sb_size]; lia].
      + pjnorm_in K0.
        ser_open HSM OK.

        step. step. zstep. step.
        if_cases K2; zify_cond K2.
        * pjnorm_in K2. ser_close HSM3 OK. eapply (TAIL (mkSb buf size cap blk fuel)); [lia| exact HSM3| reflexivity| cbn [sb_cap]; lia].
        * pjnorm_in K2.

          zstep. pjnorm. step. step.
          ser_close HSM3 OK.
          eapply (ser_grow HM HF) with (z := 2 * cap) (rpc := 0x3e4bc); [exact OK| exact HSM3| | lia| reflexivity|].
          { eapply (ser_req_ok2 E _ _ _ _ _ _ _ _ OK HSM3). cbn [sb_cap]. lia. }
          intros s' m' b' NEW wt0 wt1 wt2 wa0 wa1 wa2 wa3 wa4 wa5 wa6 wa7 wt3 wt4 wt5 wt6 HSM4.
          eapply TAIL; [lia| exact HSM4| reflexivity| unfold sb_grown; cbn [sb_cap]; lia].
    - step. step.
      if_cases K0; zify_cond K0.
      + pjnorm_in K0.
        eapply (open_rec false d' ks i e n c c2 isobj (mkSb buf size cap blk fuel) s m F fc spill);
          [exact HF0| exact HD| lia| exact KR| exact HTY| exact HNX| exact He| exact Ht| exact HR| exact HI| exact HC| exact HSM0| exact FRM| cbn [sb_size]; lia].
      + pjnorm_in K0.
        ser_open HSM OK.
        step. step. zstep. step.
        if_cases K2; zify_cond K2.
        * pjnorm_in K2. ser_close HSM3 OK. eapply (TAIL (mkSb buf size cap blk fuel)); [lia| exact HSM3| reflexivity| cbn [sb_cap]; lia].
        * pjnorm_in K2.
          zstep. pjnorm. step. step.
          ser_close HSM3 OK.
          eapply (ser_grow HM HF) with (z := 2 * cap) (rpc := 0x3e35c); [exact OK| exact HSM3| | lia| reflexivity|].
          { eapply (ser_req_ok2 E _ _ _ _ _ _ _ _ OK HSM3). cbn [sb_cap]. lia. }
          intros s' m' b' NEW wt0 wt1 wt2 wa0 wa1 wa2 wa3 wa4 wa5 wa6 wa7 wt3 wt4 wt5 wt6 HSM4.
          eapply TAIL; [lia| exact HSM4| reflexivity| unfold sb_grown; cbn [sb_cap]; lia].
  Qed.

End Proofs.
End WithCeiling0.
