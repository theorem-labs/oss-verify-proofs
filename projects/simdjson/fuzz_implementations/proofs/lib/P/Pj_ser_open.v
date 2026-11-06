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
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel PjModel Target Prog PjImpl.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjS1Out SjAlloc SjTape SjTapeList SjTapeTile SjPjSer.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_h_kit F_memcpy F_memmove_t2.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Pj_defs Pj_kit Pj_grow Pj_stmts Pj_ser_defs Pj_ser_kit Pj_ser_calls Pj_ser_loop_defs Pj_ser_ends.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require SFModel.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd.
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

Lemma le8_byte7 : forall w, 0 <= w < 2^64 -> skipn 7 (le8 (Z_to_bv 64 w)) = [Z_to_bv 8 (ttype w)].
Proof.
  intros w H. unfold le8, word_to_le_bytes. rewrite unsigned_lit by lia.
  cbn [Z_to_le_bytes skipn]. rewrite !Z.shiftr_shiftr by lia. cbn [Z.add Pos.add Pos.succ]. rewrite shr56_ttype. reflexivity.
Qed.

Lemma tnext_back : forall w e, tnext w = e + 1 -> 0 <= e ->
  Z.land (Z.land (w + 4294967295) 18446744073709551615) 4294967295 = e.
Proof.
  intros w e H He. unfold tnext in H.
  rewrite <- Z.land_assoc. change (Z.land 18446744073709551615 4294967295) with (Z.ones 32).
  rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound w (2^32) ltac:(lia)) as B.
  rewrite Z.add_mod by lia. rewrite H.
  change (4294967295 mod 2 ^ 32) with 4294967295.
  replace (e + 1 + 4294967295) with (e + 1 * 2^32) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma tape_read7 : forall m TAPE (tws : list Z) (i : Z),
  bytes_at psegs m TAPE (u64s (map (Z_to_bv 64) tws)) -> 0 <= i < Z.of_nat (length tws) -> 0 <= Tf tws i < 2^64 ->
  ov_read_bytes psegs m (wa (TAPE + (8 * i + 7))) 1 = Some [Z_to_bv 8 (ttype (Tf tws i))].
Proof.
  intros m TAPE tws i HB Hi HW.
  rewrite (bytes_at_read psegs m TAPE _ (8 * i + 7) 1 HB); [| lia| rewrite u64s_length, length_map; lia].
  f_equal.
  replace (Z.to_nat (8 * i + 7)) with (7 + 8 * Z.to_nat i)%nat by lia.
  rewrite <- skipn_skipn.
  rewrite <- (le8_byte7 _ HW).
  assert (E8 : firstn 8 (skipn (8 * Z.to_nat i) (u64s (map (Z_to_bv 64) tws))) = le8 (Z_to_bv 64 (Tf tws i))).
  { rewrite u64s_read by (rewrite length_map; lia). f_equal. unfold Tf. apply (map_nth (Z_to_bv 64)). }
  rewrite <- E8.
  set (l := skipn (8 * Z.to_nat i) (u64s (map (Z_to_bv 64) tws))).
  assert (HL : (8 <= length l)%nat) by (unfold l; rewrite skipn_length, u64s_length, length_map; lia).
  clearbody l. clear - HL.
  do 8 (destruct l as [|? l]; [cbn [length] in HL; lia|]). reflexivity.
Qed.

Lemma tape_read7_mu : forall E st s mr m i, senv_ok E -> SREF E st s mr ->
  munch (serW E st) mr m -> wmono psegs mr m -> 0 <= i < e_n E -> 0 <= e_T E i < 2^64 ->
  ov_read_bytes psegs m (wa (e_TAPE E + (8 * i + 7))) 1 = Some [Z_to_bv 8 (ttype (e_T E i))].
Proof.
  intros E st s mr m i OK HR MU WM Hi HW.
  pose proof (SREF_munch E st s mr m (sb_size st) OK HR MU WM) as (_ & _ & _ & TAPEB & _).
  apply tape_read7; assumption.
Qed.

Lemma DOCREP_of_SERM : forall E esc spill isobj st s m, senv_ok E -> SERM E esc spill isobj st s m ->
  DOCREP m (e_LB0 E) (e_DOC E) (e_TAPE E) (e_SBUF E) (e_len E) (e_tws E) (e_sbs E).
Proof.
  intros E esc spill isobj st s m OK [HR _].
  destruct HR as (_ & _ & _ & TAPEB & SBUFB & DOCC & _).
  destruct OK as [WF SBS TSZ SSZ OKT OKS _ _ _ _ _ _ _ _ _].
  unfold DOCREP. split; [exact DOCC|]. split; [exact TAPEB|]. split; [exact SBUFB|]. split; [exact WF|]. split; [exact SBS|].
  split; [exact TSZ|]. split; [exact SSZ|]. split; [exact OKT| exact OKS].
Qed.

Lemma ser_call_cont : forall (k : bool) (d' : nat) (E : senv) (Q : @chst bptr -> PState -> machine_state -> Prop) (esc spill : word) (isobj : list byte)
       (st : sbst) (s : PState) (m : mem) (i e n c c2 rpc : Z) (F : bvmap 5 word) (fc : bv 32)
       (t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  cont_stmt k d' ->
  senv_ok E -> SERM E esc spill isobj st s m -> frm0 fc ->
  e_lo E <= e_q E + -240 - cont_need d' ->
  ty (e_T E) i = (if k then t_obj else t_arr) -> tnext (e_T E i) = e + 1 -> ty (e_T E) e = end_ty k ->
  tilesS (itemS (e_T E) (e_S E) (e_sn E) k d') (i + 1) e n c c2 ->
  1 <= i -> e + 1 <= e_n E -> 0 <= c -> c2 <= e_sn E ->
  sb_acc1 st i c ->
  0 <= rpc < 2^64 -> rpc mod 2 = 0 ->
  (forall (st' : sbst) (s' : PState) (m' : mem) (F' : bvmap 5 word) (fc' : bv 32)
          (xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
      SERM E esc spill isobj st' s' m' -> frm0 fc' -> sb_acc st' (e + 1) c2 ->
      evt psegs (sgoal E Q (sb_ch st') s')
          (SST E rpc (Z_to_bv 64 rpc) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6 F' fc' m')) ->
  evt psegs (sgoal E Q (sb_ch st) s)
      (SST E (if k then PJ_APPEND_OBJ else PJ_APPEND_ARR) (Z_to_bv 64 rpc) t0 t1 t2 (Z_to_bv 64 (e_SB E)) (Z_to_bv 64 (e_DOC E)) (Z_to_bv 64 i) a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros k d' E Q esc spill isobj st s m i e n c c2 rpc F fc t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         CONT OK HSM FRM STK HTY HNX HTE HT HI HE HC HC2 ACC RP0 RP2 HK.
  pose proof (SBINV_of_SERM _ _ _ _ _ _ _ HSM) as INV.
  pose proof (DOCREP_of_SERM _ _ _ _ _ _ _ OK HSM) as DOCR.
  pose proof OK as [_ _ _ _ OKT OKS HLEN [L1 L2] [Q1 Q2] B63 [S1 S2] [D1 D2] SEP _ _].
  pose proof HSM as [HR HC0].
  pose proof HR as (HEAP & AUX & PRES & TAPEB & SBUFB & DOCC & (errv & ERR) & FA & SO & PURE).
  pose proof HC0 as ((j0 & FRA) & FRI & FRIL & FRT & FRS & SV & SZ & BUFS & INLS & MI & ST).
  apply evt_done. unfold sgoal.
  apply implM_pj_part_seq.
  eapply implM_bind.
  { eapply (CONT (Z_to_bv 64 rpc) (e_gp E) t0 t1 t2 (Z_to_bv 64 (e_DOC E)) (Z_to_bv 64 (e_SB E)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m s (e_LB0 E) (e_q E + -240) (e_lo E) (e_B E) errv (e_SB E) (e_len E) st (e_DOC E) (e_TAPE E) (e_SBUF E) (e_tws E) (e_sbs E) i e n c c2);
      [exact HEAP| exact AUX| lia| exact B63| exact ST| exact L1| exact L2| lia
      | exact ERR| exact MI| exact FRM| lia| exact S2| lia| exact D2| exact SEP| exact HLEN| exact INV| exact DOCR
      | exact HTY| exact HNX| exact HTE| exact HT| exact HI| exact HE| exact HC| exact HC2| exact ACC]. }
  cbv beta. intros ch' s' ms' PO. unfold ser_post in PO.
  destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & F' & fc' & m' & errv' & st'
                  & -> & MI' & ST' & ERR' & AUX' & FRM' & FA' & SO' & -> & HEAP' & INV' & ACC' & PRES').
  rewrite (ret_pc_even rpc RP0 RP2).
  assert (HSM' : SERM E esc spill isobj st' s' m').
  { pose proof (agree_of_lx_pres _ _ _ _ _ PRES') as AG.
    assert (UP : forall a, e_q E + -240 <= a -> ~ (e_SB E <= a < e_SB E + 88) -> lx_client (e_LB0 E) (e_q E + -240) [(e_SB E, e_SB E + 88)] a).
    { intros a Ha Hn. split; [cbn [rin_ivs fst snd]; tauto| left; exact Ha]. }
    assert (BL : forall a, in_block (e_LB0 E) a -> lx_client (e_LB0 E) (e_q E + -240) [(e_SB E, e_SB E + 88)] a).
    { intros a Ha. split; [| right; left; exact Ha].
      assert (BLa : 0 < a < alloc_ceiling).
      { eapply blocks_below; [exact HEAP|]. destruct Ha as (b0 & Hb0 & Hr). exists b0. split; [apply in_or_app; right; exact Hb0| exact Hr]. }
      unfold PJ_GROW_STACK, RMALLOC_STACK in *. cbn [rin_ivs fst snd]. lia. }
    split.
    -
      unfold SREF. split; [exact HEAP'|]. split; [exact AUX'|].
      split. { eapply lx_pres_trans; [exact PRES|]. eapply lx_pres_weaken; [exact PRES'| lia| intros b0 Hb0; exact Hb0|].
               intros a Ha. exact Ha. }
      split. { eapply bytes_at_agree; [exact AG| exact TAPEB|]. intros a Ha. rewrite u64s_length, length_map in Ha.
               apply BL. eapply in_blocks_in_block; [exact OKT| lia]. }
      split. { eapply bytes_at_agree; [exact AG| exact SBUFB|]. intros a Ha. rewrite length_map in Ha.
               apply BL. eapply in_blocks_in_block; [exact OKS| lia]. }
      split. { eapply rw_cells_agree; [exact AG| exact DOCC|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply UP; lia. }
      split. { exists errv'. exact ERR'. }
      split; [congruence|]. split; [congruence|]. eapply sb_pure_of_SBINV; exact INV'.
    -
      pose proof INV' as (SV' & SZ' & (bs' & BUF') & (ji' & INL') & _).
      unfold SCUR. split.
      { exists j0. eapply rw_cells_agree; [exact AG| exact FRA|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply UP; lia. }
      split. { eapply u8arr_agree; [exact AG| exact FRI|]. intros a Ha. rewrite FRIL in Ha. apply UP; lia. }
      split; [exact FRIL|].
      split. { eapply stk_agree; [exact AG| exact FRT|]. intros a Ha. apply UP; lia. }
      split. { eapply rw_cells_agree; [exact AG| exact FRS|]. intros a Ha. unfold ser_saved in Ha. cbn [cells_size csize Nat.add] in Ha. apply UP; lia. }
      split; [exact SV'|]. split; [exact SZ'|].
      split. { pose proof (stk_of_rw_cells psegs _ _ _ BUF') as S. cbn [cells_size csize Nat.add] in S.
               pose proof (SBINV_cap_pos _ _ _ _ INV') as CP. rewrite Nat.add_0_r, Z2Nat.id in S by lia. exact S. }
      split. { pose proof (stk_of_rw_cells psegs _ _ _ INL') as S. cbn [cells_size csize Nat.add] in S. exact S. }
      split; [exact MI'|]. exact ST'. }
  unfold implM. apply impl_from_evt.
  change (evt psegs (sgoal E Q (sb_ch st') s')
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
  Notation ESCW := (Z_to_bv 64 PJ_ESC_TAB).

  Lemma open_empty : forall (k : bool) (d1 : nat) (ks : list bool) (i c : Z) (isobj : list byte) (st : sbst) (s : PState) (m : mem)
      (F : bvmap 5 word) (fc : bv 32) (esc spill : word)
      (xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs8 xt3 xt4 xt5 xt6 : word),
    e_j E - (i + 2) <= Z.of_nat f -> (d1 + length ks = D)%nat -> (length ks <= 15)%nat -> kinds_rel ks isobj ->
    REST d1 ks (i + 2) c (e_j E) (e_c' E) -> 1 <= i -> 0 <= c ->
    SERM E esc spill isobj st s m -> frm0 fc -> sb_size st + 1 <= 41 * (i + 1) + 6 * c + 2 -> sb_size st + 1 <= sb_cap st ->
    evt psegs (sgoal E Q (sb_ch st) s)
        (LST E (if k then 0x40420 else 0x40934) (i + 1) (Z.of_nat (length ks)) (Z_to_bv 64 125) xra xt0 xt1 xt2
             (Z_to_bv 64 (sb_size st)) (Z_to_bv 64 (sb_size st + 1)) xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs8 xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF OK KX KH.
    intros k d1 ks i c isobj st s m F fc esc spill xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs8 xt3 xt4 xt5 xt6
           HF0 HD HL KR HR HI HC HSM FRM ACC ROOM.
    pose proof OK as [WF _ _ _ _ _ _ _ _ _ _ _ _ [J1 J2] [CC1 CC2]].
    pose proof WF as ((N1 & N2) & SN & _).
    pose proof (rest_ok_le _ _ _ _ _ _ _ _ _ HR) as (LEJ & LEC & _).
    destruct st as [buf size cap blk fuel]. cbn [sb_size sb_cap] in *.
    ser_env OK. ser_open HSM OK.
    destruct k.
    -
      step. step. zstep. step. pj_store_done. step.
      ser_close HSM2 OK.
      if_cases K9; zify_cond K9.
      + pjnorm_in K9. assert (ks = []) by (destruct ks; [reflexivity| cbn [length] in K9; lia]). subst ks.
        destruct (rest_ok_nil_inv _ _ _ _ _ _ _ _ HR) as [EJ EC].
        eapply (KX (mkSb buf (size + 1) cap blk fuel)); [exact HSM2| exact FRM| cbn [sb_size]; lia].
      + pjnorm_in K9.   step.
        eapply evt_eq; [| eapply (ends_entry HM HF E Q D f OK KX KH ks d1 (i + 2) c isobj (mkSb buf (size + 1) cap blk fuel))];
          [pj_st_eq| intros ->; cbn in K9; lia| exact HF0| exact HD| exact HL| exact KR| exact HR| lia| lia| exact HSM2| exact FRM| cbn [sb_size]; lia].
    - step. step. zstep. step. pj_store_done. step.
      ser_close HSM2 OK.
      if_cases K9; zify_cond K9.
      + pjnorm_in K9. assert (ks = []) by (destruct ks; [reflexivity| cbn [length] in K9; lia]). subst ks.
        destruct (rest_ok_nil_inv _ _ _ _ _ _ _ _ HR) as [EJ EC].
        eapply (KX (mkSb buf (size + 1) cap blk fuel)); [exact HSM2| exact FRM| cbn [sb_size]; lia].
      + pjnorm_in K9.   step.
        eapply evt_eq; [| eapply (ends_entry HM HF E Q D f OK KX KH ks d1 (i + 2) c isobj (mkSb buf (size + 1) cap blk fuel))];
          [pj_st_eq| intros ->; cbn in K9; lia| exact HF0| exact HD| exact HL| exact KR| exact HR| lia| lia| exact HSM2| exact FRM| cbn [sb_size]; lia].
  Qed.

  Lemma open_push : forall (k : bool) (d1 : nat) (ks : list bool) (i i3 c c3 : Z) (isobj : list byte) (st : sbst) (s : PState) (m : mem)
      (F : bvmap 5 word) (fc : bv 32) (esc spill : word)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs8 xt3 xt4 xt5 xt6 : word),
    e_j E - (i + 1) <= Z.of_nat f -> (d1 + S (length ks) = D)%nat -> (length ks + 1 <= 15)%nat -> kinds_rel ks isobj ->
    itemS (e_T E) (e_S E) (e_sn E) k d1 (i + 1) i3 c c3 -> REST d1 (k :: ks) i3 c3 (e_j E) (e_c' E) -> 1 <= i -> 0 <= c ->
    SERM E esc spill isobj st s m -> frm0 fc -> sb_size st <= 41 * i + 6 * c + 2 ->
    evt psegs (sgoal E Q (sb_ch st) s)
        (LST E (if k then 0x40c4c else 0x40c44) (i + 1) (Z.of_nat (length ks)) (Z_to_bv 64 125) xra xt0 xt1 xt2
             xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (Z.of_nat (length ks) + 1)) xs4 xs8 xt3 xt4 xt5 xt6 F fc m).
  Proof using OK KH.
    intros k d1 ks i i3 c c3 isobj st s m F fc esc spill xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs8 xt3 xt4 xt5 xt6
           HF0 HD HL KR HIT HR HI HC HSM FRM ACC.
    destruct st as [buf size cap blk fuel]. cbn [sb_size sb_cap] in *.
    ser_env OK. ser_open HSM OK.
    pose proof (u8arr_store_ok psegs _ (e_q E + -200) isobj (Z.of_nat (length ks) + 1) (wa (e_q E + -200 + (Z.of_nat (length ks) + 1))) FRI ltac:(lia) eq_refl) as SOK1.
    pose proof (kinds_rel_push ks isobj k KR ltac:(lia)) as KR'.
    destruct k; unfold kbyte in KR'.
    -
      step. step. zstep. step.
      change (le1 (Z_to_bv 64 1)) with [Z_to_bv 8 1].
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
        pose proof (u8arr_write psegs mm (e_q E + -200) isobj (Z.of_nat (length ks) + 1) (Z_to_bv 8 1) FRI ltac:(lia)) as FRI' end.
      replace (Z.to_nat (Z.of_nat (length ks) + 1)) with (length ks + 1)%nat in FRI' by lia.
      store_done.
      rewrite <- (upd_length isobj (length ks + 1) (Z_to_bv 8 1)) in FRIL. rename FRI' into FRI.

      step. step.
      ser_close HSM2 OK.
      if_cases K3; zify_cond K3; [| exfalso; pjnorm_in K3; lia].
      eapply evt_eq; [| eapply (KH d1 (true :: ks) (i + 1) i3 c c3 false _ (mkSb buf size cap blk fuel))];
        [pj_st_eq| exact HF0| cbn [length]; lia| cbn [length]; lia| exact KR'| exact HIT| exact HR| reflexivity| lia| lia
        | exact HSM2| exact FRM| cbn [sb_size]; lia].
    -
      step. step. step. zstep. step.
      change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0].
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
        pose proof (u8arr_write psegs mm (e_q E + -200) isobj (Z.of_nat (length ks) + 1) (Z_to_bv 8 0) FRI ltac:(lia)) as FRI' end.
      replace (Z.to_nat (Z.of_nat (length ks) + 1)) with (length ks + 1)%nat in FRI' by lia.
      store_done.
      rewrite <- (upd_length isobj (length ks + 1) (Z_to_bv 8 0)) in FRIL. rename FRI' into FRI.
      step. step.
      ser_close HSM2 OK.
      if_cases K3; zify_cond K3; [| exfalso; pjnorm_in K3; lia].
      eapply evt_eq; [| eapply (KH d1 (false :: ks) (i + 1) i3 c c3 false _ (mkSb buf size cap blk fuel))];
        [pj_st_eq| exact HF0| cbn [length]; lia| cbn [length]; lia| exact KR'| exact HIT| exact HR| reflexivity| lia| lia
        | exact HSM2| exact FRM| cbn [sb_size]; lia].
  Qed.

  Lemma open_mid : forall (k : bool) (d' : nat) (ks : list bool) (i e n c c2 : Z) (isobj : list byte) (st : sbst) (s : PState) (m : mem)
      (F : bvmap 5 word) (fc : bv 32) (esc spill : word)
      (xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xt3 xt4 xt5 xt6 : word),
    e_j E - (i + 1) <= Z.of_nat f -> (S d' + length ks = D)%nat -> (length ks + 1 <= 15)%nat -> kinds_rel ks isobj ->
    ty (e_T E) e = end_ty k ->
    tilesS (itemS (e_T E) (e_S E) (e_sn E) k d') (i + 1) e n c c2 ->
    REST (S d') ks (e + 1) c2 (e_j E) (e_c' E) -> 1 <= i -> 0 <= c ->
    SERM E esc spill isobj st s m -> frm0 fc -> sb_size st <= 41 * (i - 1) + 6 * c + 3 -> sb_size st + 1 <= sb_cap st ->
    evt psegs (sgoal E Q (sb_ch st) s)
        (LST E (if k then 0x403d0 else 0x408e4) i (Z.of_nat (length ks)) (Z_to_bv 64 125) xra xt0 xt1 xt2
             (Z_to_bv 64 (sb_size st)) (Z_to_bv 64 (sb_size st + 1)) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (Z.of_nat (length ks) + 1)) (Z_to_bv 64 (8 * i)) xs8
             xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF OK KX KH.
    intros k d' ks i e n c c2 isobj st s m F fc esc spill xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xt3 xt4 xt5 xt6
           HF0 HD HL KR He Ht HR HI HC HSM FRM ACC ROOM.
    pose proof OK as [WF _ _ _ _ _ _ _ _ _ _ _ _ [J1 J2] [CC1 CC2]].
    pose proof WF as ((N1 & N2) & SN & _).
    pose proof (senv_out E OK) as OUTB.
    pose proof (rest_ok_le _ _ _ _ _ _ _ _ _ HR) as (LEJ & LEC & _).
    pose proof (tilesS_le _ (itemS_lt (e_T E) (e_S E) (e_sn E) k d') _ _ _ _ _ Ht) as (LIE & _).
    pose proof (tilesS_cur _ (e_sn E) (itemS_cur (e_T E) (e_S E) (e_sn E) k d') _ _ _ _ _ Ht) as (LCC & _).
    pose proof (rest_ok_open (e_T E) (e_S E) (e_sn E) d' ks k i e n c c2 (e_j E) (e_c' E) Ht He HR) as HR'.
    pose proof (rest_ok_word (e_T E) (e_S E) (e_sn E) SN d' k ks (i + 1) c (e_j E) (e_c' E) HR' ltac:(lia) ltac:(lia)) as WR.
    pose proof (ser_ranges _ _ _ _ _ _ _ OK HSM) as (TP0 & TP1 & _ & _).
    set (t := ttype (e_T E (i + 1))) in *.
    assert (TYR : 0 <= t < 256) by (unfold t, ttype; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    destruct st as [buf size cap blk fuel]. cbn [sb_size sb_cap] in *.
    ser_env OK. ser_open HSM OK.
    destruct k.
    -

      step. step. zstep. step. step. pj_store_done.
      pose proof (doc_cells_mu E _ _ _ _ OK HREF MU WM) as DOCC.
      pose proof (tape_read7_mu E _ _ _ _ (i + 1) OK HREF MU WM ltac:(lia) WR) as RD7. fold t in RD7.

      step. zstep. zstep. pjnorm. zstep. zstep. pjnorm. step.
      ser_close HSM2 OK.
      if_cases K1; zify_cond K1.
      +   pjnorm_in K1.
        assert (NA : SjTape.ty (e_T E) (i + 1) <> t_arr_end /\ SjTape.ty (e_T E) (i + 1) <> t_obj_end).
        { destruct (Z.eq_dec (i + 1) e) as [EE|NE].
          - exfalso. rewrite <- EE in He. unfold SjTape.ty in He. fold t in He. unfold end_ty, t_obj_end, t_arr_end in He. lia.
          - destruct (tilesS_next _ (itemS_lt (e_T E) (e_S E) (e_sn E) true d') _ _ _ _ _ Ht NE) as (i3 & c3 & HIT & LE3 & _).
            eapply (itemS_not_end (e_T E) (e_S E) (e_sn E) SN true d' (i + 1) i3 c c3 HIT); lia. }
        destruct (rest_ok_item (e_T E) (e_S E) (e_sn E) SN d' true ks (i + 1) c (e_j E) (e_c' E) HR' (proj1 NA) (proj2 NA))
          as (i3 & c3 & HIT & HR3).
        eapply evt_eq; [| eapply (open_push true d' ks i i3 c c3 isobj (mkSb buf (size + 1) cap blk fuel))];
          [pj_st_eq| lia| lia| lia| exact KR| exact HIT| exact HR3| lia| lia| exact HSM2| exact FRM| cbn [sb_size]; lia].
      +   pjnorm_in K1.
        assert (HEND : SjTape.ty (e_T E) (i + 1) = t_arr_end \/ SjTape.ty (e_T E) (i + 1) = t_obj_end)
          by (unfold SjTape.ty; fold t; unfold t_arr_end, t_obj_end; lia).
        pose proof (rest_ok_end (e_T E) (e_S E) (e_sn E) SN d' true ks (i + 1) c (e_j E) (e_c' E) HR' ltac:(lia) ltac:(lia) HEND) as HR2.
        replace (i + 1 + 1) with (i + 2) in HR2 by lia.
        pose proof (rest_ok_le _ _ _ _ _ _ _ _ _ HR2) as (LEJ2 & LEC2 & _).
        assert (TAIL : forall (st5 : sbst) (s5 : PState) (m5 : mem) (yra yt0 yt1 yt2 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
          SERM E esc spill isobj st5 s5 m5 -> sb_size st5 = size + 1 -> size + 2 <= sb_cap st5 ->
          evt psegs (sgoal E Q (sb_ch st5) s5)
              (LST E 0x40420 (i + 1) (Z.of_nat (length ks)) (Z_to_bv 64 125) yra yt0 yt1 yt2
                   (Z_to_bv 64 (size + 1)) (Z_to_bv 64 (size + 2)) ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 (Z.of_nat (length ks) + 1)) (Z_to_bv 64 (8 * i)) xs8 yt3 yt4 yt5 yt6 F fc m5)).
        { intros st5 s5 m5 yra yt0 yt1 yt2 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM5 ESZ ROOM5.
          eapply evt_eq; [| eapply (open_empty true (S d') ks i c isobj st5 s5 m5 F fc esc spill)];
            [pj_st_eq| lia| exact HD| lia| exact KR| exact HR2| lia| lia| exact HSM5| exact FRM| lia| lia]. }
        ser_open HSM2 OK.

        step. step. zstep. step.
        if_cases K2; zify_cond K2.
        * pjnorm_in K2. ser_close HSM3 OK. eapply (TAIL (mkSb buf (size + 1) cap blk fuel)); [exact HSM3| reflexivity| cbn [sb_cap]; lia].
        * pjnorm_in K2.

          zstep. pjnorm. step. step.
          ser_close HSM3 OK.
          eapply (ser_grow HM HF) with (st := mkSb buf (size + 1) cap blk fuel) (z := 2 * cap) (rpc := 0x40418); [exact OK| exact HSM3| | lia| reflexivity|].
          { eapply (ser_req_ok2 E _ _ _ _ _ _ OK HSM3). cbn [sb_cap]. lia. }
          intros s' m' b' NEW yt0 yt1 yt2 za0 za1 za2 za3 za4 za5 za6 za7 yt3 yt4 yt5 yt6 HSM4.
          ser_open HSM4 OK.

          step. zstep.
          ser_close HSM5 OK.
          eapply TAIL; [exact HSM5| reflexivity| unfold sb_grown; cbn [sb_cap]; lia].
    -

      step. step. zstep. step. step. pj_store_done.
      pose proof (doc_cells_mu E _ _ _ _ OK HREF MU WM) as DOCC.
      pose proof (tape_read7_mu E _ _ _ _ (i + 1) OK HREF MU WM ltac:(lia) WR) as RD7. fold t in RD7.

      step. zstep. zstep. pjnorm. zstep. zstep. pjnorm. step.
      ser_close HSM2 OK.
      if_cases K1; zify_cond K1.
      +   pjnorm_in K1.
        assert (NA : SjTape.ty (e_T E) (i + 1) <> t_arr_end /\ SjTape.ty (e_T E) (i + 1) <> t_obj_end).
        { destruct (Z.eq_dec (i + 1) e) as [EE|NE].
          - exfalso. rewrite <- EE in He. unfold SjTape.ty in He. fold t in He. unfold end_ty, t_obj_end, t_arr_end in He. lia.
          - destruct (tilesS_next _ (itemS_lt (e_T E) (e_S E) (e_sn E) false d') _ _ _ _ _ Ht NE) as (i3 & c3 & HIT & LE3 & _).
            eapply (itemS_not_end (e_T E) (e_S E) (e_sn E) SN false d' (i + 1) i3 c c3 HIT); lia. }
        destruct (rest_ok_item (e_T E) (e_S E) (e_sn E) SN d' false ks (i + 1) c (e_j E) (e_c' E) HR' (proj1 NA) (proj2 NA))
          as (i3 & c3 & HIT & HR3).
        eapply evt_eq; [| eapply (open_push false d' ks i i3 c c3 isobj (mkSb buf (size + 1) cap blk fuel))];
          [pj_st_eq| lia| lia| lia| exact KR| exact HIT| exact HR3| lia| lia| exact HSM2| exact FRM| cbn [sb_size]; lia].
      +   pjnorm_in K1.
        assert (HEND : SjTape.ty (e_T E) (i + 1) = t_arr_end \/ SjTape.ty (e_T E) (i + 1) = t_obj_end)
          by (unfold SjTape.ty; fold t; unfold t_arr_end, t_obj_end; lia).
        pose proof (rest_ok_end (e_T E) (e_S E) (e_sn E) SN d' false ks (i + 1) c (e_j E) (e_c' E) HR' ltac:(lia) ltac:(lia) HEND) as HR2.
        replace (i + 1 + 1) with (i + 2) in HR2 by lia.
        pose proof (rest_ok_le _ _ _ _ _ _ _ _ _ HR2) as (LEJ2 & LEC2 & _).
        assert (TAIL : forall (st5 : sbst) (s5 : PState) (m5 : mem) (yra yt0 yt1 yt2 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
          SERM E esc spill isobj st5 s5 m5 -> sb_size st5 = size + 1 -> size + 2 <= sb_cap st5 ->
          evt psegs (sgoal E Q (sb_ch st5) s5)
              (LST E 0x40934 (i + 1) (Z.of_nat (length ks)) (Z_to_bv 64 125) yra yt0 yt1 yt2
                   (Z_to_bv 64 (size + 1)) (Z_to_bv 64 (size + 2)) ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 (Z.of_nat (length ks) + 1)) (Z_to_bv 64 (8 * i)) xs8 yt3 yt4 yt5 yt6 F fc m5)).
        { intros st5 s5 m5 yra yt0 yt1 yt2 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM5 ESZ ROOM5.
          eapply evt_eq; [| eapply (open_empty false (S d') ks i c isobj st5 s5 m5 F fc esc spill)];
            [pj_st_eq| lia| exact HD| lia| exact KR| exact HR2| lia| lia| exact HSM5| exact FRM| lia| lia]. }
        ser_open HSM2 OK.

        step. step. zstep. step.
        if_cases K2; zify_cond K2.
        * pjnorm_in K2. ser_close HSM3 OK. eapply (TAIL (mkSb buf (size + 1) cap blk fuel)); [exact HSM3| reflexivity| cbn [sb_cap]; lia].
        * pjnorm_in K2.

          zstep. pjnorm. step. step.
          ser_close HSM3 OK.
          eapply (ser_grow HM HF) with (st := mkSb buf (size + 1) cap blk fuel) (z := 2 * cap) (rpc := 0x4092c); [exact OK| exact HSM3| | lia| reflexivity|].
          { eapply (ser_req_ok2 E _ _ _ _ _ _ OK HSM3). cbn [sb_cap]. lia. }
          intros s' m' b' NEW yt0 yt1 yt2 za0 za1 za2 za3 za4 za5 za6 za7 yt3 yt4 yt5 yt6 HSM4.
          ser_open HSM4 OK.

          step. zstep.
          ser_close HSM5 OK.
          eapply TAIL; [exact HSM5| reflexivity| unfold sb_grown; cbn [sb_cap]; lia].
  Qed.

  Hypothesis REC : rec_ok D.
  Hypothesis STK : e_lo E <= e_q E - ser_need D.

  Lemma open_ret : forall (d1 : nat) (ks : list bool) (i e c2 : Z) (isobj : list byte) (st : sbst) (s : PState) (m : mem)
      (F : bvmap 5 word) (fc : bv 32) (esc spill : word)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs8 xt3 xt4 xt5 xt6 : word),
    ks <> [] -> e_j E - (e + 1) <= Z.of_nat f -> (d1 + length ks = D)%nat -> (length ks <= 15)%nat -> kinds_rel ks isobj ->
    tnext (e_T E i) = e + 1 -> 0 <= e_T E i < 2^64 ->
    REST d1 ks (e + 1) c2 (e_j E) (e_c' E) -> 1 <= i -> i < e -> 0 <= c2 ->
    SERM E esc spill isobj st s m -> frm0 fc -> sb_size st <= 41 * e + 6 * c2 + 2 ->
    evt psegs (sgoal E Q (sb_ch st) s)
        (LST E 0x40c8c i (Z.of_nat (length ks)) (Z_to_bv 64 125) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 (Z_to_bv 64 (8 * i)) xs8 xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF OK KX KH.
    intros d1 ks i e c2 isobj st s m F fc esc spill xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs8 xt3 xt4 xt5 xt6
           NE HF0 HD HL KR HNX WR HR HI HIE HC2 HSM FRM ACC.
    pose proof OK as [WF _ _ _ _ _ _ _ _ _ _ _ _ [J1 J2] [CC1 CC2]].
    pose proof WF as ((N1 & N2) & SN & _).
    pose proof (rest_ok_le _ _ _ _ _ _ _ _ _ HR) as (LEJ & LEC & _).
    pose proof (ser_ranges _ _ _ _ _ _ _ OK HSM) as (TP0 & TP1 & _ & _).
    pose proof HSM as HSM0.
    destruct st as [buf size cap blk fuel]. cbn [sb_size sb_cap] in *.
    ser_env OK. ser_open HSM OK.
    pose proof (doc_cells_mu E _ _ _ _ OK HREF MU WM) as DOCC.
    pose proof (tape_read_mu E _ _ _ _ i OK HREF MU WM ltac:(lia)) as RDT.
    set (w := e_T E i) in *.

    step. zstep. zstep. step. zstep. zstep. step.
    rewrite (tnext_back w e HNX ltac:(lia)).
    ser_close HSM2 OK.
    eapply evt_eq; [| eapply (ends_entry HM HF E Q D f OK KX KH ks d1 (e + 1) c2 isobj (mkSb buf size cap blk fuel))];
      [pj_st_eq| exact NE| exact HF0| exact HD| exact HL| exact KR| exact HR| lia| lia| exact HSM2| exact FRM| cbn [sb_size]; lia].
  Qed.

  Lemma open_rec : forall (k : bool) (d' : nat) (ks : list bool) (i e n c c2 : Z) (isobj : list byte) (st : sbst) (s : PState) (m : mem)
      (F : bvmap 5 word) (fc : bv 32) (esc spill : word)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs8 xt3 xt4 xt5 xt6 : word),
    e_j E - (i + 1) <= Z.of_nat f -> (S d' + length ks = D)%nat -> length ks = 15%nat -> kinds_rel ks isobj ->
    ty (e_T E) i = (if k then t_obj else t_arr) -> tnext (e_T E i) = e + 1 -> ty (e_T E) e = end_ty k ->
    tilesS (itemS (e_T E) (e_S E) (e_sn E) k d') (i + 1) e n c c2 ->
    REST (S d') ks (e + 1) c2 (e_j E) (e_c' E) -> 1 <= i -> 0 <= c ->
    SERM E esc spill isobj st s m -> frm0 fc -> sb_size st <= 41 * (i - 1) + 6 * c + 3 ->
    evt psegs (sgoal E Q (sb_ch st) s)
        (LST E (if k then 0x40c7c else 0x40c68) i (Z.of_nat (length ks)) (Z_to_bv 64 125) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 (Z_to_bv 64 (8 * i)) xs8
             xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF OK KX KH REC STK.
    intros k d' ks i e n c c2 isobj st s m F fc esc spill xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs8 xt3 xt4 xt5 xt6
           HF0 HD HL KR HTY HNX He Ht HR HI HC HSM FRM ACC.
    pose proof OK as [WF _ _ _ _ _ _ _ _ _ _ _ _ [J1 J2] [CC1 CC2]].
    pose proof WF as ((N1 & N2) & SN & _).
    pose proof (rest_ok_le _ _ _ _ _ _ _ _ _ HR) as (LEJ & LEC & _).
    pose proof (tilesS_le _ (itemS_lt (e_T E) (e_S E) (e_sn E) k d') _ _ _ _ _ Ht) as (LIE & _).
    pose proof (tilesS_cur _ (e_sn E) (itemS_cur (e_T E) (e_S E) (e_sn E) k d') _ _ _ _ _ Ht) as (LCC & _).
    assert (WR : 0 <= e_T E i < 2^64).
    { eapply ttype_range; [exact HTY|]. destruct k; unfold t_obj, t_arr; lia. }
    assert (CONT : cont_stmt k d') by (apply REC; lia).
    assert (STK' : e_lo E <= e_q E + -240 - cont_need d').
    { unfold cont_need. unfold ser_need in *. lia. }
    assert (NE : ks <> []) by (intros ->; cbn in HL; lia).
    assert (KRET : forall (st' : sbst) (s' : PState) (m' : mem) (F' : bvmap 5 word) (fc' : bv 32)
          (yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys3 yt3 yt4 yt5 yt6 : word),
      SERM E esc spill isobj st' s' m' -> frm0 fc' -> sb_acc st' (e + 1) c2 ->
      evt psegs (sgoal E Q (sb_ch st') s')
          (LST E 0x40c8c i (Z.of_nat (length ks)) (Z_to_bv 64 125) yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys3 (Z_to_bv 64 (8 * i)) xs8 yt3 yt4 yt5 yt6 F' fc' m')).
    { intros st' s' m' F' fc' yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys3 yt3 yt4 yt5 yt6 HSM' FRM' ACC'.
      unfold sb_acc in ACC'.
      eapply (open_ret (S d') ks i e c2 isobj st'); try eassumption; lia. }
    destruct k.
    -
      step. step. step. step.
      eapply evt_eq; [| eapply (ser_call_cont true d' E Q esc spill isobj st s m i e n c c2 0x40c8c)];
        [pj_st_eq| exact CONT| exact OK| exact HSM| exact FRM| exact STK'| exact HTY| exact HNX| exact He| exact Ht| exact HI| lia| exact HC| lia
        | exact ACC| lia| reflexivity|].
      intros st' s' m' F' fc' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM' FRM' ACC'.
      eapply (KRET st'); eassumption.
    -
      step. step. step. step.
      eapply evt_eq; [| eapply (ser_call_cont false d' E Q esc spill isobj st s m i e n c c2 0x40c78)];
        [pj_st_eq| exact CONT| exact OK| exact HSM| exact FRM| exact STK'| exact HTY| exact HNX| exact He| exact Ht| exact HI| lia| exact HC| lia
        | exact ACC| lia| reflexivity|].
      intros st' s' m' F' fc' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM' FRM' ACC'.
        step.
      eapply (KRET st'); eassumption.
  Qed.

  Theorem open_proof : forall k, open_stmt E Q D f k.
  Proof using HM HF OK KX KH REC STK.
    intros k. unfold open_stmt.
    intros d' ks i e n c c2 isobj st s m F fc spill xra xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6
           HF0 HD HL KR HTY HNX He Ht HR HI HC HSM FRM ACC.
    pose proof OK as [WF _ _ _ _ _ _ _ _ _ _ _ _ [J1 J2] [CC1 CC2]].
    pose proof WF as ((N1 & N2) & SN & _).
    pose proof (senv_out E OK) as OUTB.
    pose proof (rest_ok_le _ _ _ _ _ _ _ _ _ HR) as (LEJ & LEC & _).
    pose proof (tilesS_le _ (itemS_lt (e_T E) (e_S E) (e_sn E) k d') _ _ _ _ _ Ht) as (LIE & _).
    pose proof (tilesS_cur _ (e_sn E) (itemS_cur (e_T E) (e_S E) (e_sn E) k d') _ _ _ _ _ Ht) as (LCC & _).
    pose proof HSM as HSM0.
    destruct st as [buf size cap blk fuel]. cbn [sb_size sb_cap] in *.
    ser_env OK.
    assert (TAIL : forall (st5 : sbst) (s5 : PState) (m5 : mem) (yra yt0 yt1 yt2 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
      (length ks + 1 <= 15)%nat ->
      SERM E ESCW spill isobj st5 s5 m5 -> sb_size st5 = size -> size + 1 <= sb_cap st5 ->
      evt psegs (sgoal E Q (sb_ch st5) s5)
          (LST E (if k then 0x403d0 else 0x408e4) i (Z.of_nat (length ks)) (Z_to_bv 64 125) yra yt0 yt1 yt2
               (Z_to_bv 64 size) (Z_to_bv 64 (size + 1)) ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 (Z.of_nat (length ks) + 1)) (Z_to_bv 64 (8 * i)) (Z_to_bv 64 PJ_NE_TAB)
               yt3 yt4 yt5 yt6 F fc m5)).
    { intros st5 s5 m5 yra yt0 yt1 yt2 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HL1 HSM5 ESZ ROOM5.
      eapply evt_eq; [| eapply (open_mid k d' ks i e n c c2 isobj st5 s5 m5 F fc ESCW spill)];
        [pj_st_eq| exact HF0| exact HD| exact HL1| exact KR| exact He| exact Ht| exact HR| exact HI| exact HC| exact HSM5| exact FRM| lia| lia]. }
    destruct k.
    -
      zstep. step. step.
      if_cases K0; zify_cond K0.
      + pjnorm_in K0.
        eapply evt_eq; [| eapply (open_rec true d' ks i e n c c2 isobj (mkSb buf size cap blk fuel) s m F fc ESCW spill)];
          [pj_st_eq| exact HF0| exact HD| lia| exact KR| exact HTY| exact HNX| exact He| exact Ht| exact HR| exact HI| exact HC| exact HSM0| exact FRM| cbn [sb_size]; lia].
      + pjnorm_in K0.
        ser_open HSM OK.

        step. step. zstep. step.
        if_cases K2; zify_cond K2.
        * pjnorm_in K2. ser_close HSM3 OK. eapply (TAIL (mkSb buf size cap blk fuel)); [lia| exact HSM3| reflexivity| cbn [sb_cap]; lia].
        * pjnorm_in K2.

          zstep. pjnorm. step. step.
          ser_close HSM3 OK.
          eapply (ser_grow HM HF) with (z := 2 * cap) (rpc := 0x403c8); [exact OK| exact HSM3| | lia| reflexivity|].
          { eapply (ser_req_ok2 E _ _ _ _ _ _ OK HSM3). cbn [sb_cap]. lia. }
          intros s' m' b' NEW yt0 yt1 yt2 za0 za1 za2 za3 za4 za5 za6 za7 yt3 yt4 yt5 yt6 HSM4.
          ser_open HSM4 OK.

          step. zstep.
          ser_close HSM5 OK.
          eapply TAIL; [lia| exact HSM5| reflexivity| unfold sb_grown; cbn [sb_cap]; lia].
    -
      zstep. step. step.
      if_cases K0; zify_cond K0.
      + pjnorm_in K0.
        eapply evt_eq; [| eapply (open_rec false d' ks i e n c c2 isobj (mkSb buf size cap blk fuel) s m F fc ESCW spill)];
          [pj_st_eq| exact HF0| exact HD| lia| exact KR| exact HTY| exact HNX| exact He| exact Ht| exact HR| exact HI| exact HC| exact HSM0| exact FRM| cbn [sb_size]; lia].
      + pjnorm_in K0.
        ser_open HSM OK.

        step. step. zstep. step.
        if_cases K2; zify_cond K2.
        * pjnorm_in K2. ser_close HSM3 OK. eapply (TAIL (mkSb buf size cap blk fuel)); [lia| exact HSM3| reflexivity| cbn [sb_cap]; lia].
        * pjnorm_in K2.

          zstep. pjnorm. step. step.
          ser_close HSM3 OK.
          eapply (ser_grow HM HF) with (z := 2 * cap) (rpc := 0x408dc); [exact OK| exact HSM3| | lia| reflexivity|].
          { eapply (ser_req_ok2 E _ _ _ _ _ _ OK HSM3). cbn [sb_cap]. lia. }
          intros s' m' b' NEW yt0 yt1 yt2 za0 za1 za2 za3 za4 za5 za6 za7 yt3 yt4 yt5 yt6 HSM4.
          ser_open HSM4 OK.

          step. zstep.
          ser_close HSM5 OK.
          eapply TAIL; [lia| exact HSM5| reflexivity| unfold sb_grown; cbn [sb_cap]; lia].
  Qed.

End Proofs.
End WithCeiling0.
