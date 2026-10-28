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
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import F_memchr F_memcmp F_strlen F_memcpy F_memmove_t2 Atp_defs Atp_kitu Atp_arrl Atp_str Atp_strr Atp_objk Atp_obju Atp_objt Atp_objs.
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

Lemma find_byte_zlist_Some : forall c (l : list Z) n ix, Forall (fun x => 0 <= x < 256) l -> 0 <= c < 256 ->
  find_byte c (firstn n (map (Z_to_bv 8) l)) = Some ix ->
  (ix < length l)%nat /\ (ix < n)%nat /\ nth ix l 0 = c /\ (forall j, (j < ix)%nat -> nth j l 0 <> c).
Proof.
  intros c l n ix HF Hc H. destruct (find_byte_Some _ _ _ H) as (Hl & (b & Hb & Hbc) & Hmin).
  rewrite length_firstn, length_map in Hl.
  assert (L1 : (ix < length l)%nat) by lia. assert (L2 : (ix < n)%nat) by lia.
  split; [exact L1|]. split; [exact L2|]. split.
  - rewrite nth_error_firstn in Hb. replace (ix <? n)%nat with true in Hb by (symmetry; apply Nat.ltb_lt; lia).
    rewrite nth_error_map, (nth_error_nth' l 0 L1) in Hb. cbn in Hb. injection Hb as EB. rewrite <- EB in Hbc.
    pose proof (Forall_nth_Z _ l ix HF L1) as R. rewrite a_u8_small in Hbc by exact R. exact Hbc.
  - intros j Hj E. apply (Hmin j (Z_to_bv 8 (nth j l 0)) Hj).
    + rewrite nth_error_firstn. replace (j <? n)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
      rewrite nth_error_map. rewrite (nth_error_nth' l 0) by lia. reflexivity.
    + rewrite a_u8_small; [exact E|]. apply Forall_nth_Z; [exact HF| lia].
Qed.

Lemma find_byte_zlist_None : forall c (l : list Z) n, Forall (fun x => 0 <= x < 256) l -> 0 <= c < 256 ->
  find_byte c (firstn n (map (Z_to_bv 8) l)) = None -> forall j, (j < n)%nat -> (j < length l)%nat -> nth j l 0 <> c.
Proof.
  intros c l n HF Hc H j Hj Hl E. apply (find_byte_None _ _ H j (Z_to_bv 8 (nth j l 0))).
  - rewrite nth_error_firstn. replace (j <? n)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    rewrite nth_error_map. rewrite (nth_error_nth' l 0) by lia. reflexivity.
  - rewrite a_u8_small; [exact E|]. apply Forall_nth_Z; [exact HF| lia].
Qed.

Lemma has_tilde_nth : forall (k : list Z) j, (j < length k)%nat -> nth j k 0 = 126 -> has_tilde k = true.
Proof.
  intros k j Hj E. unfold has_tilde. apply existsb_exists. exists (nth j k 0). split; [apply nth_In; exact Hj| rewrite E; reflexivity].
Qed.

Lemma lor7_eq : forall L, 0 <= L -> Z.lor L 7 = L - L mod 8 + 7.
Proof.
  intros L HL. pose proof (Z.div_mod L 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound L 8 ltac:(lia)) as MB.
  assert (E1 : L = Z.lor (Z.shiftl (L / 8) 3) (L mod 8)).
  { rewrite lor_shiftl_small; [| lia| lia| apply Z.div_pos; lia]. change (2 ^ 3) with 8. lia. }
  rewrite E1 at 1. rewrite <- Z.lor_assoc.
  assert (E2 : Z.lor (L mod 8) 7 = 7).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec.
    destruct (Z.lt_ge_cases i 3) as [Hi3|Hi3].
    - replace (Z.testbit 7 i) with true; [apply Bool.orb_true_r|]. symmetry. change 7 with (Z.ones 3). apply Z.ones_spec_low. lia.
    - replace (Z.testbit 7 i) with false. 2:{ symmetry. change 7 with (Z.ones 3). apply Z.ones_spec_high. lia. }
      rewrite Bool.orb_false_r. destruct (Z.eq_dec (L mod 8) 0) as [->|NZ]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 3); [| lia]. apply Z.log2_lt_pow2; lia. }
  rewrite E2. rewrite lor_shiftl_small; [| lia| lia| apply Z.div_pos; lia]. change (2 ^ 3) with 8. lia.
Qed.
Lemma str_sz_even : forall L, 0 <= L -> str_sz L mod 2 = 0.
Proof.
  intros L HL. unfold str_sz. destruct (Z.eqb_spec L 23); [reflexivity|]. rewrite lor7_eq by lia.
  pose proof (Z.div_mod L 8 ltac:(lia)). pose proof (Z.mod_pos_bound L 8 ltac:(lia)).
  replace (L - L mod 8 + 7 + 1) with ((L / 8 + 1) * 4 * 2) by lia. apply Z_mod_mult.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma fresh_block_sep : forall s p A n LB m a, RHEAP s ((p, A, n) :: LB) m -> A <= a < A + n -> ~ in_block LB a.
Proof.
  intros s p A n LB m a H Ha (b & Hb & Hr).
  pose proof (LH_nodup _ _ _ H) as ND.
  assert (NE : blk_id (p, A, n) <> blk_id b).
  { intros E. cbn [map] in ND. inversion ND as [|x l NI ND' EQ]. subst. apply NI. rewrite E. apply in_map. exact Hb. }
  pose proof (LH_disjoint _ _ _ _ _ H ltac:(left; reflexivity) ltac:(right; exact Hb) NE) as D. cbn [blk_addr blk_size fst snd] in D. lia.
Qed.

Lemma substr_cps_le : forall Q (ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (SV A n pos cnt RA : Z),
  rw_cells usegs m SV [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 n)] -> 0 <= pos <= n -> 0 < A -> A + n < 2^63 -> 0 <= cnt <= n - pos ->
  0 <= SV -> SV + 16 < 2^64 -> ra = Z_to_bv 64 RA -> 0 <= RA < 2^64 -> RA mod 2 = 0 ->
  (forall (xa3 xa4 xa5 : word),
     evt usegs Q (MS (mkR ra sp gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 (A + pos)) (Z_to_bv 64 cnt) (Z_to_bv 64 cnt) xa3 xa4 xa5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 RA) fc None m (seg_rom usegs))) ->
  evt usegs Q (MS (mkR ra sp gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 SV) (Z_to_bv 64 pos) (Z_to_bv 64 cnt) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x3e478) fc None m (seg_rom usegs)).
Proof.
  intros until RA. intros SVC POS A0 AN CNT SV0 SV64 -> RA0 RA2 HK.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.

  step. step. if_lia. step. astep. step. if_lia.

  astep. astep.
  replace (0 <? A) with true by (symmetry; apply Z.ltb_lt; lia).
  first [ replace (pos + A <? 1) with false by (symmetry; apply Z.ltb_ge; lia)
        | replace (A + pos <? 1) with false by (symmetry; apply Z.ltb_ge; lia) ].
  cbn [Z.b2z Z.lxor Pos.lxor]. astep. step. if_false.

  astep. step. if_lia. step. step.
  replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia| exact RA2]).
  eapply evt_eq; [| eapply HK]. atp_st_eq.
Qed.

Section Obj.
  Variable E : aenv.
  Hypothesis OK : aenv_ok E.
  Variable d : nat.
  Hypothesis HELEM : atp_elem_stmt E d.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Definition obj_mid (m0 m1 : mem) (s : PState) (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 : word)
      (out node i e c P L0 L sl : Z) (rest0 k : list Z) (REST : list (list Z)) (j0 j8 j16 j24 j28 js j4 jo : list byte) (errv : word) : Prop :=
    rw_cells usegs m1 (q + -208) [CB 8 j0; CB 8 j8; CB 8 j16; CB 4 j24; CB 4 j28]
    /\ rw_cells usegs m1 (q + -176) [CB 24 js]
    /\ rw_cells usegs m1 (q + -152) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 12); CB 4 j4]
    /\ rw_cells usegs m1 (q + -128) [C8 (Z_to_bv 64 (P + 1)); C8 (Z_to_bv 64 L)]
    /\ rw_cells usegs m1 (q + -112) [C8 (Z_to_bv 64 (P + 1)); C8 (Z_to_bv 64 L0)]
    /\ rw_cells usegs m1 (q + -96) (obj_savedU ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10)
    /\ rw_cells usegs m1 out [CB 24 jo] /\ q <= out /\ out + 24 <= ae_B E /\ q <= ae_DOC E /\ (out + 24 <= ae_DOC E \/ ae_DOC E + 24 <= out)
    /\ AINV E m1 /\ rw_cells usegs m1 node [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 i)] /\ q <= node /\ node + 16 <= ae_B E
    /\ ty (ae_T E) i = t_obj /\ tnext (ae_T E i) = e + 1
    /\ tiles (field (ae_T E) (ae_S E) (ae_sn E) (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d)) (i + 1) e c /\ 0 <= i /\ e + 1 <= ae_n E - 1
    /\ bytes_at usegs m1 (P + 1) (map (Z_to_bv 8) rest0) /\ Forall (fun c => 0 <= c < 256) rest0 /\ zlength rest0 = L0 /\ k = firstn (Z.to_nat L) rest0
    /\ 0 <= L <= L0 /\ L0 < 2^40 /\ 0 <= P /\ ptr_at E P (47 :: rest0)
    /\ ((sl = 18446744073709551615 /\ REST = []) \/
        (0 <= sl < L0 /\ exists r, REST = ptr_segs (47 :: r) /\ ptr_at E (P + 1 + sl) (47 :: r) /\ zlength (47 :: r) = L0 - sl))
    /\ RHEAP s (ae_LB E) m1 /\ rauxv_ok m1 (ae_B E) /\ stk usegs m1 (ae_lo E) (q + -208) /\ ae_lo E <= q - obj_need d /\ q mod 16 = 0
    /\ rw_cells usegs m1 LX_ERRNO [C4 errv] /\ mem_inv usegs m1 /\ lx_pres (ae_LB E) q [(out, out + 24)] m0 m1.

  Lemma sso_slot : forall mX q sz, lstr mX (q + -176) false (q + -175) 23 sz -> exists jj, rw_cells usegs mX (q + -176) [CB 24 jj].
  Proof.
    intros mX q sz (_ & _ & _ & _ & _ & (bsx & BSX & LBX & _) & (HX & _ & _)).
    assert (LBX' : length bsx = 23%nat) by lia.
    pose proof (rw_cells_of_u8arr _ _ _ _ BSX) as BX. rewrite LBX' in BX.
    pose proof (rw_cells_join _ _ _ _ _ HX BX ltac:(cbn [cells_size csize Nat.add]; lia)) as J. cbn [app] in J.
    destruct (rw_cells_forget _ _ _ _ J) as [jj J']. cbn [cells_size csize Nat.add] in J'. exists jj. exact J'.
  Qed.
  Lemma heap_slot : forall mX q A cap sz, lstr mX (q + -176) true A cap sz -> exists jj, rw_cells usegs mX (q + -176) [CB 24 jj].
  Proof.
    intros mX q A cap sz (_ & _ & _ & _ & _ & _ & [HX _]).
    destruct (rw_cells_forget _ _ _ _ HX) as [jj J']. cbn [cells_size csize Nat.add] in J'. exists jj. exact J'.
  Qed.

  Lemma frame112 : forall mX q ja js cr ck pv lv,
    rw_cells usegs mX (q + -208) [CB 32 ja] -> rw_cells usegs mX (q + -176) [CB 24 js] ->
    rw_cells usegs mX (q + -152) cr -> cells_size cr = 24%nat -> rw_cells usegs mX (q + -128) ck -> cells_size ck = 16%nat ->
    rw_cells usegs mX (q + -112) [C8 pv; C8 lv] ->
    exists jj, rw_cells usegs mX (q + -208) [CB 112 jj].
  Proof.
    intros mX q ja js cr ck pv lv A B C CS D DS F0.
    destruct (rw_cells_forget _ _ _ _ C) as [jc C']. rewrite CS in C'.
    destruct (rw_cells_forget _ _ _ _ D) as [jd D']. rewrite DS in D'.
    destruct (rw_cells_forget _ _ _ _ F0) as [jf F']. cbn [cells_size csize Nat.add] in F'.
    pose proof (rw_cells_join _ _ _ _ _ A B ltac:(cbn [cells_size csize Nat.add]; lia)) as J1. cbn [app] in J1.
    pose proof (rw_cells_join _ _ _ _ _ J1 C' ltac:(cbn [cells_size csize Nat.add]; lia)) as J2. cbn [app] in J2.
    pose proof (rw_cells_join _ _ _ _ _ J2 D' ltac:(cbn [cells_size csize Nat.add]; lia)) as J3. cbn [app] in J3.
    pose proof (rw_cells_join _ _ _ _ _ J3 F' ltac:(cbn [cells_size csize Nat.add]; lia)) as J4. cbn [app] in J4.
    destruct (rw_cells_forget _ _ _ _ J4) as [jj J']. cbn [cells_size csize Nat.add] in J'. exists jj. exact J'.
  Qed.

  Lemma obj_noesc : forall (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (out node i e c P L0 L sl : Z) (rest0 k : list Z) (REST : list (list Z)) (m0 m1 : mem) (j0 j8 j16 j24 j28 js j4 jo : list byte) (errv : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
    obj_mid m0 m1 s ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 out node i e c P L0 L sl rest0 k REST j0 j8 j16 j24 j28 js j4 jo errv ->
    implM usegs (atp_walk lops (k :: REST)) s
      (fun _ => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m0))
      (MS (mkR x1 (Z_to_bv 64 (q + -208)) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 out) (Z_to_bv 64 sl) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 node) x19 x20 x21 x22 x23 x24 x25 x26 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x3f180) fc None m1 (seg_rom usegs)).
  Proof.
    intros until x31. intros PRE.
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
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client (ae_LB E) q [(out, out + 24)] a -> outside [(q - 336, q - 112)] a).
    { intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| exact I].
      destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
    assert (PIN : ae_PTR E <= P + 1 /\ P + 1 + L0 <= ae_PTR E + zlength (ae_p1 E)).
    { destruct PAT as (pre & Ep & EP). rewrite EP, Ep. unfold zlength in *. rewrite length_app. cbn [length]. lia. }
    assert (PCEIL : P + 1 + L0 <= alloc_ceiling).
    { destruct BP as [E0p|BPx]; [exfalso; destruct PAT as (pre & Ep & _); rewrite E0p in Ep; destruct pre; discriminate Ep|].
      pose proof (in_blocks_range _ _ _ _ _ HEAP BPx ltac:(unfold zlength; lia)). lia. }
    pose proof AI as (TAPEB & SBUFB & PTRB & DOCC).
    pose proof (bytes_at_firstn _ _ _ (Z.to_nat L) KEYB) as KEYL.
    pose proof (munch_refl [(q - 336, q - 112)]%Z m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    apply (rw_cells_split_CB usegs _ _ [] 24 js [] [8;8;4;4]%nat) in STRS; [|reflexivity]. cbn [mk_CB_cells app] in STRS.
    unfold implM. iprefix.

    step. step. astep. step. step.
    eapply evt_cut.
    { eapply (atkey_spec E OK d) with (lo := ae_lo E) (kb := firstn (Z.to_nat L) (map (Z_to_bv 8) rest0));
      [exact NODE| lia| lia| exact TAPEB| exact SBUFB| exact DOCC| exact TY| exact NXT| exact TILES| exact I0| exact EN
      | exact KEYL| rewrite firstn_length_le by (rewrite length_map; unfold zlength in ZL0; lia); lia| lia| lia| lia| lia
      | exact STRS| lia| lia| exact TR| exact SR| exact ST| lia| lia| exact MI| lia| lia]. }
    cbv beta. intros ms' PO. unfold atkey_post in PO.
    destruct PO as (z0 & z1 & z2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3 & z4 & z5 & z6 & m2 & r0 & it & code & -> & MU2 & WM2 & MI2 & ST2 & AKO & RES).
    replace (ret_pc (Z_to_bv 64 0x3f194)) with (Z_to_bv 64 0x3f194) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    replace (q + -208 - 128) with (q - 336) in MU2 by lia.
    assert (MU12 : munch [(q - 336, q - 112)] m1 m2).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp. cbn [outside]. intros x' Hx. lia. }
    assert (WM12 : wmono usegs m1 m2) by (eapply wmono_trans; [exact WM| exact WM2]).
    pose proof (rw_cells_transport _ _ _ _ _ _ SCR MU2 WM2 ltac:(cbn; lia)) as SCR2.
    pose proof (rw_cells_transport _ _ _ _ _ _ REC MU2 WM2 ltac:(cbn; lia)) as REC2.
    pose proof (rw_cells_transport _ _ _ _ _ _ FRK MU2 WM2 ltac:(cbn; lia)) as FRK2.
    pose proof (rw_cells_transport _ _ _ _ _ _ FRSV MU2 WM2 ltac:(cbn; lia)) as FRSV2.
    pose proof (rw_cells_transport _ _ _ _ _ _ FRB MU2 WM2 ltac:(cbn; lia)) as FRB2.
    pose proof (rw_cells_transport _ _ _ _ _ _ OUTR MU2 WM2 ltac:(cbn; lia)) as OUTR2.
    pose proof (rw_cells_transport _ _ _ _ _ _ NODE MU2 WM2 ltac:(cbn; lia)) as NODE2.
    pose proof (rw_cells_transport _ _ _ _ _ _ ERR MU2 WM2 ltac:(cbn; lia)) as ERR2.
    clear SCR REC FRK FRSV FRB OUTR NODE ERR MI ST MU2 WM2 MU WM.
    assert (CR : 0 <= code < 64) by (destruct RES as [(C0 & _)|(C20 & _)]; lia).

    step. step. astep. astep. hstep. hstep. step. if_lia. hstep. step. name_mem m3.
    lazymatch goal with H : rw_cells usegs m3 (q + -152) _ |- _ => rename H into REC3 end.
    lazymatch goal with H : rw_cells usegs m3 (q + -176) _ |- _ => rename H into AKO3 end.
    lazymatch goal with H : rw_cells usegs m3 (q + -208) _ |- _ => rename H into SCR3 end.
    lazymatch goal with H : rw_cells usegs m3 (q + -128) _ |- _ => rename H into FRK3 end.
    lazymatch goal with H : rw_cells usegs m3 (q + -112) _ |- _ => rename H into FRSV3 end.
    lazymatch goal with H : rw_cells usegs m3 (q + -96) _ |- _ => rename H into FRB3 end.
    lazymatch goal with H : rw_cells usegs m3 out _ |- _ => rename H into OUTR3 end.
    lazymatch goal with H : rw_cells usegs m3 node _ |- _ => rename H into NODE3 end.
    lazymatch goal with H : rw_cells usegs m3 980196 _ |- _ => rename H into ERR3 end.
    lazymatch goal with H : mem_inv usegs m3 |- _ => rename H into MI3 end.
    lazymatch goal with H : stk usegs m3 _ _ |- _ => rename H into ST3 end.
    rename MU12 into MU13. rename WM12 into WM13.
    assert (HEAP3 : RHEAP s (ae_LB E) m3).
    { eapply LH_frame; [exact HEAP| exact MU13| exact WM13|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX3 : rauxv_ok m3 (ae_B E)).
    { eapply rauxv_ok_frame; [exact AUX| exact MU13| exact WM13|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (PRES3 : lx_pres (ae_LB E) q [(out, out + 24)] m0 m3).
    { eapply lx_pres_trans; [exact PRES|]. eapply lx_pres_of_munch; [exact MU13| exact WM13| exact CLI]. }
    assert (AI3 : AINV E m3).
    { eapply AINV_agree; [exact AI| eapply agree_on_of_munch; [exact MU13| exact WM13]| | | exact OK].
      - intros a Ha. pose proof (BLB a Ha). cbn [outside]. lia.
      - intros a Ha. cbn [outside]. lia. }
    destruct (rw_cells_forget _ _ _ _ AKO3) as [js3 FRS3]. cbn [cells_size csize Nat.add] in FRS3.
    destruct (rw_cells_forget _ _ _ _ FRK3) as [jk3 FRK3']. cbn [cells_size csize Nat.add] in FRK3'.
    apply (rw_cells_merge usegs _ _ [] [_; _; _; _; _] []) in SCR3. cbn [cells_size csize cells_bytes cbytes Nat.add app] in SCR3.
    assert (HCODE : code = 20 \/ (code = 0 /\ exists vj j', r0 = Z_to_bv 64 (ae_DOC E) /\ Z_to_bv 64 it = Z_to_bv 64 vj /\
                      elem (ae_T E) (ae_S E) (ae_sn E) ck_any d vj j' /\ 0 <= vj /\ j' <= e)).
    { destruct RES as [(C0 & R0 & IT0 & (j' & EL & JE))|(C20 & R0 & IT0)]; [right| left; exact C20].
      split; [exact C0|]. exists it, j'. split; [exact R0|]. split; [reflexivity|]. split; [exact EL|]. split; [exact IT0| exact JE]. }
    apply evt_done. to_implM_at (fun _ : unit => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m0)).
    apply implM_atp_walk_plain.
    eapply (obj_tail E OK d HELEM ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s s out P L0 sl e code r0 (Z_to_bv 64 it) REST m0 m3);
      [exact SCR3| exact FRS3| exact REC3| exact FRK3'| exact FRSV3| unfold obj_savedU; exact FRB3| exact OUTR3| exact QO| exact OB| exact QD| exact AI3| exact HCODE
      | exact EN| exact P0| lia| lia| exact RC| exact HEAP3| exact AUX3| exact ST3| exact LOF| exact Q16| exists errv; rewrite ELX; exact ERR3| exact MI3
      | reflexivity| reflexivity| exact PRES3].
  Qed.

  Lemma obj_esc_sso : forall (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (out node i e c P L0 L e0 sl : Z) (rest0 k : list Z) (REST : list (list Z)) (m0 m1 : mem) (j0 j8 j16 j24 j28 js j4 jo : list byte) (errv : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
    obj_mid m0 m1 s ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 out node i e c P L0 L sl rest0 k REST j0 j8 j16 j24 j28 js j4 jo errv ->
    0 <= e0 < L -> has_tilde k = true -> L <= 22 ->
    implM usegs (atp_walk lops (k :: REST)) s
      (fun _ => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m0))
      (MS (mkR x1 (Z_to_bv 64 (q + -208)) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 out) (Z_to_bv 64 sl) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 node) (Z_to_bv 64 e0) (Z_to_bv 64 (P + 1)) (Z_to_bv 64 L) x22 x23 x24 x25 x26 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x3f138) fc None m1 (seg_rom usegs)).
  Proof.
    intros until x31. intros PRE E0 HT L22.
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
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client (ae_LB E) q [(out, out + 24)] a -> outside [(q - 336, q - 112); (q + -175, q + -175 + 23)] a).
    { intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| split; [| exact I]];
        (destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]). }
    assert (PIN : ae_PTR E <= P + 1 /\ P + 1 + L0 <= ae_PTR E + zlength (ae_p1 E)).
    { destruct PAT as (pre & Ep & EP). rewrite EP, Ep. unfold zlength in *. rewrite length_app. cbn [length]. lia. }
    assert (PCEIL : P + 1 + L0 <= alloc_ceiling).
    { destruct BP as [E0p|BPx]; [exfalso; destruct PAT as (pre & Ep & _); rewrite E0p in Ep; destruct pre; discriminate Ep|].
      pose proof (in_blocks_range _ _ _ _ _ HEAP BPx ltac:(unfold zlength; lia)). lia. }
    pose proof (munch_refl [(q - 336, q - 112); (q + -175, q + -175 + 23)]%Z m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    hide AI. hide KEYB.
    unfold implM. iprefix.

    apply (rw_cells_split_CB usegs _ _ [] 24 js [] [1; 23]%nat) in STRS; [|reflexivity]. cbn [mk_CB_cells app] in STRS.
    astep. step. rewrite le1_smallZ by lia. mem_after_store. astep. step. if_lia. name_mem m2.
    apply (proj1 (rw_cells_app _ _ [_] _)) in STRS. destruct STRS as [HDRC DATA]. cbn [cells_size csize Nat.add] in DATA.
    replace (q + -176 + Z.of_nat 1) with (q + -175) in DATA by lia.
    set (KK := fun ms' : machine_state => impl usegs (at_node usegs) (atp_walk lops (k :: REST) s)
                (epost (fun p => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m0) (snd p))) ms') in *.
    assert (AI2 : AINV E m2).
    { unhide AI. eapply AINV_agree; [exact AI| eapply agree_on_of_munch; [exact MU| exact WM]| | | exact OK].
      - intros a Ha. pose proof (BLB a Ha). cbn [outside]. lia.
      - intros a Ha. cbn [outside]. lia. }
    assert (KEYB2 : bytes_at usegs m2 (P + 1) (map (Z_to_bv 8) rest0)).
    { unhide KEYB. eapply bytes_at_agree; [eapply agree_on_of_munch; [exact MU| exact WM]| exact KEYB|]. intros a Ha. rewrite length_map in Ha. unfold zlength in ZL0. cbn [outside]. lia. }
    assert (HDR2 : shdr m2 (q + -176) false (q + -175) 23 L).
    { unfold shdr. split; [| split; [lia| reflexivity]]. lazymatch type of HDRC with rw_cells _ _ _ [C1 (Z_to_bv 8 ?x)] => replace x with (2 * L) in HDRC by lia end. exact HDRC. }
    destruct (rw_cells_forget _ _ _ _ FRK) as [jk FRK']. cbn [cells_size csize Nat.add] in FRK'.
    eapply evt_eq; [| eapply (obj_str_phase E OK d KK m2 F fc q false (q + -175) 23 L e0 P L0 sl rest0 i e c node out);
      [ exact HDR2| exact DATA| lia| lia| lia| lia| lia| intros X; discriminate X| intros _; reflexivity| right; split; reflexivity
      | intros a Ha Hb; pose proof (BLB a Hb); lia| exact BLB| exact PIN| exact KEYB2| exact KEYF| exact ZL0| lia| exact L040| exact P0| lia| exact PCEIL| exact E0
      | exact SCR| exact REC| exact FRK'| exact AI2| exact NODE| exact QN| exact NB| exact QD| exact TY| exact NXT| exact TILES| exact I0| exact EN| exact TR| exact SR
      | exact ST| lia| exact CEIL'| unfold GLOBALS_TOP; lia| exact QO| exact OB| exact B63| exact MI| | ] ]; [atp_st_eq| |].
    -
      intros m' sz ja' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y28 y29 y30 y31 LS' _ SCR' REC' FRK2 MI' ST' MU' WM'.
      unfold objs_W in MU'.
      pose proof (rw_cells_transport _ _ _ _ _ _ FRB MU' WM' ltac:(cbn; lia)) as FRB'.
      pose proof (rw_cells_transport _ _ _ _ _ _ FRSV MU' WM' ltac:(cbn; lia)) as FRSV'.
      pose proof (rw_cells_transport _ _ _ _ _ _ OUTR MU' WM' ltac:(cbn; lia)) as OUTR'.
      pose proof (rw_cells_transport _ _ _ _ _ _ ERR MU' WM' ltac:(cbn; lia)) as ERR'.
      pose proof LS' as (SZ0' & SZC' & _ & _ & _ & _ & (HDR' & EA' & ECAP')).
      pose proof (munch_refl [(out, out + 24)]%Z m') as MUo. pose proof (wmono_refl usegs m') as WMo.
      apply (rw_cells_split_CB usegs _ _ [] 24 _ [] [8;8;4;4]%nat) in OUTR'; [|reflexivity]. cbn [mk_CB_cells app] in OUTR'.
      hide MU'. step. if_lia. astep. astep. astep. rewrite short_byte0. hstep. hstep. hstep. step. if_true. name_mem m3. unhide MU'.
      lazymatch goal with H : rw_cells usegs m3 out _ |- _ => rename H into OUT3 end.
      subst KK. stop_now.
      assert (LS3 : lstr m3 (q + -176) false (q + -175) 23 sz).
      { eapply lstr_frame; [exact LS'| exact MUo| exact WMo| cbn; lia| cbn; lia]. }
      destruct (sso_slot m3 q sz LS3) as [jj SL].
      destruct (frame112 m3 q _ _ _ _ _ _ SCR' SL REC' eq_refl FRK2 eq_refl FRSV') as [ja3 FRA].
      assert (CLIb : forall a, 0 <= a < 2^64 -> lx_client (ae_LB E) q [(out, out + 24)] a -> outside [(q - 336, q - 112); (q + -175, q + -175 + 23); (out, out + 24)] a).
      { intros a Ha HC. pose proof (CLI a Ha HC) as X. destruct HC as [HX _]. cbn [rin_ivs fst snd] in HX. cbn [outside] in X |- *. tauto. }
      assert (MU13 : munch [(q - 336, q - 112); (q + -175, q + -175 + 23); (out, out + 24)] m1 m3).
      { eapply munch_trans; [eapply munch_weaken; [| exact MU]|]. 2: eapply munch_trans; [eapply munch_weaken; [| exact MU']| eapply munch_weaken; [| exact MUo]].
        all: unfold sub_fp; cbn [outside]; intros x' Hx; lia. }
      assert (WM13 : wmono usegs m1 m3) by (eapply wmono_trans; [exact WM| exact WM']).
      eapply (obj_epi E); [exact FRA| unfold obj_savedU; exact FRB'| exact MI'| exact ST'| lia| exists errv; rewrite ELX; exact ERR'| | reflexivity| reflexivity| | |].
      + eapply rauxv_ok_frame; [exact AUX| exact MU13| exact WM13|].
        constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor].
      + eapply LH_frame; [exact HEAP| exact MU13| exact WM13|].
        constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor].
      + eapply lx_pres_trans; [exact PRES|]. eapply lx_pres_of_munch; [exact MU13| exact WM13| exact CLIb].
      + exists (Z_to_bv 64 0), 0, 22. eexists. split; [exact OUT3|]. split; [lia|]. intros C0. exfalso. lia.
    -
      intros m' sz err ja' w0 w1 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y25 y26 y28 y29 y30 y31 LS' SCR' REC' FRK2 HERR MI' ST' MU' WM'.
      split; [intros _| intros X; discriminate X].
      unfold objs_W in MU'.
      pose proof (rw_cells_transport _ _ _ _ _ _ FRB MU' WM' ltac:(cbn; lia)) as FRB'.
      pose proof (rw_cells_transport _ _ _ _ _ _ FRSV MU' WM' ltac:(cbn; lia)) as FRSV'.
      pose proof (rw_cells_transport _ _ _ _ _ _ OUTR MU' WM' ltac:(cbn; lia)) as OUTR'.
      pose proof (rw_cells_transport _ _ _ _ _ _ ERR MU' WM' ltac:(cbn; lia)) as ERR'.
      pose proof (rw_cells_transport _ _ _ _ _ _ NODE MU' WM' ltac:(cbn; lia)) as NODE'.
      assert (MU1' : munch [(q - 336, q - 112); (q + -175, q + -175 + 23)] m1 m').
      { eapply munch_trans; [exact MU|]. exact MU'. }
      assert (WM1' : wmono usegs m1 m') by (eapply wmono_trans; [exact WM| exact WM']).
      assert (HEAP' : RHEAP s (ae_LB E) m').
      { eapply LH_frame; [exact HEAP| exact MU1'| exact WM1'|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
      assert (AUX' : rauxv_ok m' (ae_B E)).
      { eapply rauxv_ok_frame; [exact AUX| exact MU1'| exact WM1'|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      assert (PRES' : lx_pres (ae_LB E) q [(out, out + 24)] m0 m').
      { eapply lx_pres_trans; [exact PRES|]. eapply lx_pres_of_munch; [exact MU1'| exact WM1'| exact CLI]. }
      assert (AI' : AINV E m').
      { unhide AI. eapply AINV_agree; [exact AI| eapply agree_on_of_munch; [exact MU1'| exact WM1']| | | exact OK].
        - intros a Ha. pose proof (BLB a Ha). cbn [outside]. lia.
        - intros a Ha. cbn [outside]. lia. }
      destruct (sso_slot m' q sz LS') as [jj SL].
      subst KK. apply evt_done. to_implM_at (fun _ : unit => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m0)).
      apply implM_atp_walk_plain.
      eapply (obj_tail E OK d HELEM ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s s out P L0 sl e err w0 w1 REST m0 m');
        [exact SCR'| exact SL| exact REC'| exact FRK2| exact FRSV'| unfold obj_savedU; exact FRB'| exact OUTR'| exact QO| exact OB| exact QD| exact AI'| exact HERR
        | exact EN| exact P0| lia| lia| exact RC| exact HEAP'| exact AUX'| exact ST'| exact LOF| exact Q16| exists errv; rewrite ELX; exact ERR'| exact MI'
        | reflexivity| reflexivity| exact PRES'].
  Qed.

End Obj.
End WithCeiling0.
