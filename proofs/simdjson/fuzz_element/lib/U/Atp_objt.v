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
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import F_memchr F_memcmp F_strlen F_memcpy F_memmove_t2 Atp_defs Atp_kitu Atp_arrl.
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

Definition obj_savedU (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 : word) : list cell :=
  [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma land_shiftl_ones8 : forall y, Z.land (Z.shiftl y 8) (Z.ones 8) = 0.
Proof.
  intros y. apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.bits_0.
  destruct (Z_lt_dec k 8).
  - rewrite Z.shiftl_spec_low by lia. reflexivity.
  - rewrite Z.ones_spec_high by lia. apply Bool.andb_false_r.
Qed.

Lemma Z_to_le_bytes_to_Z : forall (bs : list byte), Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. cbn in Hb.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
    rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l, land_shiftl_ones8, Z.lor_0_r.
    rewrite Z.land_ones by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_lor, Z.shiftr_shiftl_l by lia. cbn [Z.sub]. rewrite Z.shiftl_0_r.
    rewrite (Z.shiftr_div_pow2 (bv_unsigned b) 8) by lia. rewrite Z.div_small by lia. rewrite Z.lor_0_l. exact IH.
Qed.

Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs H. unfold le8, word_to_le_bytes, le_bytes_to_word. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z_to_le_bytes_mod by (cbn; lia). rewrite <- H. apply Z_to_le_bytes_to_Z.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma rec_merge8 : forall m A (a b v : word) (j : list byte),
  rw_cells usegs m A [C8 a; C8 b; C4 v; CB 4 j] -> rw_cells usegs m A [C8 a; C8 b; C8 (le_bytes_to_word (le4 v ++ j))] /\ length j = 4%nat.
Proof.
  intros m A a b v j H. pose proof H as [[W _] _]. cbn [cells_wf cell_wf] in W. destruct W as (_ & _ & _ & L & _).
  split; [| exact L].
  eapply rw_cells_recast; [exact H| cbn; tauto| | reflexivity].
  cbn [cells_bytes cbytes]. rewrite le8_of_bytes by (rewrite length_app, length_le4, L; reflexivity). rewrite <- app_assoc. reflexivity.
Qed.

Lemma rec_split8 : forall m A (a b v : word) (j : list byte),
  rw_cells usegs m A [C8 a; C8 b; C8 (le_bytes_to_word (le4 v ++ j))] -> length j = 4%nat -> rw_cells usegs m A [C8 a; C8 b; C4 v; CB 4 j].
Proof.
  intros m A a b v j H L.
  eapply rw_cells_recast; [exact H| cbn; tauto| | reflexivity].
  cbn [cells_bytes cbytes]. rewrite le8_of_bytes by (rewrite length_app, length_le4, L; reflexivity). rewrite <- app_assoc. reflexivity.
Qed.

Lemma rw_cells_join : forall m A B cs1 cs2,
  rw_cells usegs m A cs1 -> rw_cells usegs m B cs2 -> B = A + Z.of_nat (cells_size cs1) -> rw_cells usegs m A (cs1 ++ cs2).
Proof. intros m A B cs1 cs2 H1 H2 ->. apply (proj2 (rw_cells_app _ _ _ _)). split; assumption. Qed.

Section Obj.
  Variable E : aenv.
  Hypothesis OK : aenv_ok E.
  Variable d : nat.
  Hypothesis HELEM : atp_elem_stmt E d.

  Lemma obj_epi : forall (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s s' : PState) (out : Z) (m0 m2 : mem) (ja : list byte)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
    rw_cells usegs m2 (q + -208) [CB 112 ja] -> rw_cells usegs m2 (q + -96) (obj_savedU ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10) ->
    mem_inv usegs m2 -> stk usegs m2 (ae_lo E) (q + -208) -> ae_lo E <= q - 208 -> (exists errv' : word, rw_cells usegs m2 LX_ERRNO [C4 errv']) ->
    rauxv_ok m2 (ae_B E) -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
    RHEAP s' (ae_LB E) m2 -> lx_pres (ae_LB E) q [(out, out + 24)] m0 m2 -> out_rec E m2 out ->
    evt usegs (hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m0) s')
      (MS (mkR x1 (Z_to_bv 64 (q + -208)) gp (Z_to_bv 64 RATP) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x3f398) fc None m2 (seg_rom usegs)).
  Proof.
    intros until x31. intros FRA FRB MI ST LO ERR AUX FA SO HEAP PRES OUT.
    unfold obj_savedU in FRB.
    pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    do 12 step. step.
    release_frame FRA ST (q + -96). release_frame FRB ST q.
    step.
    apply evt_done. unfold hpost. do 15 eexists. exists m2. split; [reflexivity|].
    split; [exact MI|]. split; [exact ST|]. split; [exact ERR|]. split; [exact AUX|]. split; [exact FA|]. split; [exact SO|].
    unfold lvl_R. split; [exact HEAP|]. split; [exact PRES| exact OUT].
  Qed.

  Lemma obj_out : forall (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s s' : PState) (out : Z) (m0 m2 : mem) (ja jb jn jo : list byte) (r0 : word) (j code : Z)
      (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
    rw_cells usegs m2 (q + -208) [CB 56 ja] -> rw_cells usegs m2 (q + -152) [C8 r0; C8 (Z_to_bv 64 j); C4 (Z_to_bv 64 code); CB 4 jn] ->
    0 <= code < 64 -> (code = 0 -> r0 = Z_to_bv 64 (ae_DOC E) /\ 0 <= j /\ exists dd jj, elem (ae_T E) (ae_S E) (ae_sn E) ck_any dd j jj) ->
    rw_cells usegs m2 (q + -128) [CB 32 jb] ->
    rw_cells usegs m2 (q + -96) (obj_savedU ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10) ->
    rw_cells usegs m2 out [CB 24 jo] -> q <= out -> out + 24 <= ae_B E ->
    mem_inv usegs m2 -> stk usegs m2 (ae_lo E) (q + -208) -> ae_lo E <= q - 208 -> (exists errv' : word, rw_cells usegs m2 LX_ERRNO [C4 errv']) ->
    rauxv_ok m2 (ae_B E) -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
    RHEAP s' (ae_LB E) m2 -> lx_pres (ae_LB E) q [(out, out + 24)] m0 m2 ->
    evt usegs (hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m0) s')
      (MS (mkR x1 (Z_to_bv 64 (q + -208)) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 out) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x3f380) fc None m2 (seg_rom usegs)).
  Proof.
    intros until x31. intros FRA REC CR CIMP FRK FRB OUT QO OB MI ST LO ERR AUX FA SO HEAP PRES. unfold obj_savedU in FRB.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L BT BS BP P0 [CEIL GLO] B63 [DL DB] [AL8D AL8T]].
    unfold GLOBALS_TOP in *.
    assert (LO0 : 0 <= ae_lo E) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    destruct ERR as [errv ERR]. assert (ELX : LX_ERRNO = 980196) by reflexivity. rewrite ELX in ERR.
    pose proof (munch_refl [(out, out + 24)]%Z m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    assert (BLB : forall a, in_block (ae_LB E) a -> a < alloc_ceiling) by (intros a Ha; exact (proj2 (blocks_below _ _ _ _ HEAP Ha))).
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client (ae_LB E) q [(out, out + 24)] a -> outside [(out, out + 24)] a).
    { intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [clear - HX; lia| exact I]. }
    apply (rw_cells_split_CB usegs _ _ [] 24 jo [] [8;8;8]%nat) in OUT; [|reflexivity]. cbn [mk_CB_cells app] in OUT.
    destruct (rec_merge8 _ _ _ _ _ _ REC) as [REC8 LJN]. clear REC.

    step. step. step. hstep. hstep. hstep. name_mem m3.
    lazymatch goal with H : rw_cells usegs m3 out _ |- _ => rename H into OUT3 end.
    pose proof (rec_split8 _ _ _ _ _ _ OUT3 LJN) as OUTX.
    destruct (rw_cells_forget _ _ _ _ REC8) as [jr REC']. cbn [cells_size csize Nat.add] in REC'.
    pose proof (rw_cells_join _ _ _ _ _ FRA REC' ltac:(cbn [cells_size csize Nat.add]; lia)) as J1. cbn [app] in J1.
    pose proof (rw_cells_join _ _ _ _ _ J1 FRK ltac:(cbn [cells_size csize Nat.add]; lia)) as J2. cbn [app] in J2.
    destruct (rw_cells_forget _ _ _ _ J2) as [ja' FRA'']. cbn [cells_size csize Nat.add] in FRA''.
    eapply obj_epi; [exact FRA''| unfold obj_savedU; exact FRB| exact MI| exact ST| exact LO| exists errv; rewrite ELX; exact ERR| | exact FA| exact SO| | |].
    - eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor].
    - eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor].
    - eapply lx_pres_trans; [exact PRES|]. eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI].
    - exists r0, j, code, jn. split; [exact OUTX|]. split; [exact CR| exact CIMP].
  Qed.

  Lemma obj_tail : forall (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s s' : PState) (out P L0 sl e code : Z) (w0 w1 : word) (REST : list (list Z)) (m0 m2 : mem) (ja js j4 jk jo : list byte)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
    rw_cells usegs m2 (q + -208) [CB 32 ja] -> rw_cells usegs m2 (q + -176) [CB 24 js] ->
    rw_cells usegs m2 (q + -152) [C8 w0; C8 w1; C4 (Z_to_bv 64 code); CB 4 j4] ->
    rw_cells usegs m2 (q + -128) [CB 16 jk] -> rw_cells usegs m2 (q + -112) [C8 (Z_to_bv 64 (P + 1)); C8 (Z_to_bv 64 L0)] ->
    rw_cells usegs m2 (q + -96) (obj_savedU ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10) ->
    rw_cells usegs m2 out [CB 24 jo] -> q <= out -> out + 24 <= ae_B E -> q <= ae_DOC E ->
    AINV E m2 ->
    (code = 20 \/ (code = 0 /\ exists vj j', w0 = Z_to_bv 64 (ae_DOC E) /\ w1 = Z_to_bv 64 vj /\
                   elem (ae_T E) (ae_S E) (ae_sn E) ck_any d vj j' /\ 0 <= vj /\ j' <= e)) ->
    e + 1 <= ae_n E - 1 -> 0 <= P -> P + 1 + L0 < 2^63 -> 0 <= L0 ->
    ((sl = 18446744073709551615 /\ REST = []) \/
     (0 <= sl < L0 /\ exists r, REST = ptr_segs (47 :: r) /\ ptr_at E (P + 1 + sl) (47 :: r) /\ zlength (47 :: r) = L0 - sl)) ->
    RHEAP s' (ae_LB E) m2 -> rauxv_ok m2 (ae_B E) -> stk usegs m2 (ae_lo E) (q + -208) -> ae_lo E <= q - obj_need d -> q mod 16 = 0 ->
    (exists errv' : word, rw_cells usegs m2 LX_ERRNO [C4 errv']) -> mem_inv usegs m2 ->
    ps_fa s' = ps_fa s -> ps_so s' = ps_so s -> lx_pres (ae_LB E) q [(out, out + 24)] m0 m2 ->
    implM usegs (atp_walk lops REST) s'
      (fun _ => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m0))
      (MS (mkR x1 (Z_to_bv 64 (q + -208)) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 out) (Z_to_bv 64 sl) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 code) x19 x20 x21 x22 x23 x24 x25 x26 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x3f330) fc None m2 (seg_rom usegs)).
  Proof.
    intros until x31. intros FRA FRS REC FRK FRSV FRB OUT QO OB QD AI HCODE EN P0 PL L00 RC HEAP AUX ST LO Q16 ERR MI FA SO PRES.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L BT BS BP PP0 [CEIL GLO] B63 [DL DB] [AL8D AL8T]].
    unfold obj_need, elem_need, ATP_LEAFX, RMALLOC_STACK, GLOBALS_TOP in *. unfold obj_savedU in FRB.
    assert (LO0 : 0 <= ae_lo E) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    destruct ERR as [errv ERR]. assert (ELX : LX_ERRNO = 980196) by reflexivity. rewrite ELX in ERR.
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    assert (BLB : forall a, in_block (ae_LB E) a -> a < alloc_ceiling) by (intros a Ha; exact (proj2 (blocks_below _ _ _ _ HEAP Ha))).
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client (ae_LB E) q [(out, out + 24)] a -> outside [(q - 208, q)] a).
    { intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| exact I].
      destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
    pose proof (munch_refl [(q - 208, q)]%Z m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    unfold implM. iprefix.

    assert (XOUT : forall (y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 : word), 0 <= code < 64 ->
      (code = 0 -> w0 = Z_to_bv 64 (ae_DOC E) /\ exists vj, w1 = Z_to_bv 64 vj /\ 0 <= vj /\ exists dd jj, elem (ae_T E) (ae_S E) (ae_sn E) ck_any dd vj jj) ->
      evt usegs (fun ms' => impl usegs (at_node usegs) (atp_walk lops REST s')
                  (epost (fun p => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m0) (snd p))) ms')
        (MS (mkR y1 (Z_to_bv 64 (q + -208)) gp (Z_to_bv 64 RATP) y5 y6 y7 (Z_to_bv 64 out) y9 y10 y11 y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 code) x19 x20 x21 x22 x23 x24 x25 x26 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x3f380) fc None m2 (seg_rom usegs))).
    { intros y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 CR CIMP. stop_now.
      pose proof (rw_cells_join _ _ _ _ _ FRA FRS ltac:(cbn [cells_size csize Nat.add]; lia)) as J1. cbn [app] in J1.
      destruct (rw_cells_forget _ _ _ _ J1) as [ja' FRA']. cbn [cells_size csize Nat.add] in FRA'.
      pose proof (rw_cells_join _ _ _ _ _ FRK FRSV ltac:(cbn [cells_size csize Nat.add]; lia)) as J2. cbn [app] in J2.
      destruct (rw_cells_forget _ _ _ _ J2) as [jb FRK']. cbn [cells_size csize Nat.add] in FRK'.
      destruct (Z.eq_dec code 0) as [C0|C0].
      - destruct (CIMP C0) as (-> & vj & -> & VJ0 & ELV).
        eapply (obj_out ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s s' out m0 m2 ja' jb j4 jo (Z_to_bv 64 (ae_DOC E)) vj code);
          [exact FRA'| exact REC| exact CR| intros _; split; [reflexivity| split; [exact VJ0| exact ELV]]| exact FRK'| unfold obj_savedU; exact FRB| exact OUT| exact QO| exact OB
          | exact MI| exact ST| lia| exists errv; rewrite ELX; exact ERR| exact AUX| exact FA| exact SO| exact HEAP| exact PRES].
      - pose proof (bv_unsigned_in_range 64 w1) as W1R.
        assert (EW1 : w1 = Z_to_bv 64 (bv_unsigned w1)) by (symmetry; apply Z_to_bv_bv_unsigned).
        rewrite EW1 in REC.
        eapply (obj_out ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s s' out m0 m2 ja' jb j4 jo w0 (bv_unsigned w1) code);
          [exact FRA'| exact REC| exact CR| intros C0'; exfalso; exact (C0 C0')| exact FRK'| unfold obj_savedU; exact FRB| exact OUT| exact QO| exact OB
          | exact MI| exact ST| lia| exists errv; rewrite ELX; exact ERR| exact AUX| exact FA| exact SO| exact HEAP| exact PRES]. }

    step. if_cases KC; zify_cond KC.
    { destruct HCODE as [C20|(C0 & _)]; [| exfalso; lia].
      apply XOUT; [lia| intros C0; exfalso; lia]. }
    destruct HCODE as [C20|(C0 & vj & j' & -> & -> & EL & VJ0 & JE)]; [exfalso; lia|]. subst code.
    pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ2.

    astep. step. if_cases KS; zify_cond KS; rewrite ?land64_mod in KS.
    { apply XOUT; [lia| intros _; split; [reflexivity| exists vj; split; [reflexivity| split; [exact VJ0| exists d, j'; exact EL]]]]. }
    destruct RC as [[SLN _]|(SLR & r & -> & PAT2 & ZR)]; [exfalso; clear - KS SLN; lia|].
    pose proof (zlength_nonneg r) as ZRN. rewrite zlength_cons in ZR.

    astep. astep. step. step.
    eapply substr_cps with (SV := q + -112) (A := P + 1) (n := L0) (pos := sl) (RA := 0x3f34c);
      [exact FRSV| lia| lia| lia| | lia| lia| reflexivity| lia| reflexivity|].
    { match goal with |- _ < bv_unsigned ?w => let v := eval vm_compute in (bv_unsigned w) in change (bv_unsigned w) with v end. lia. }
    intros ya3 ya4 ya5.

    step. step. astep. astep. step.
    apply (proj1 (rw_cells_app _ _ [_; _] _)) in REC. destruct REC as [NODE2 RT]. cbn [cells_size csize Nat.add] in RT.
    replace (q + -152 + Z.of_nat 16) with (q + -136) in RT by lia.
    replace (Z_to_bv 64 (L0 - sl)) with (Z_to_bv 64 (zlength (47 :: r))) by (f_equal; rewrite zlength_cons; lia).
    apply evt_done. to_implM_at (fun _ : unit => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m0)).
    pose proof HELEM as HE. unfold atp_elem_stmt in HE.
    eapply implM_post_evt.
    { eapply (HE (47 :: r) vj j') with (jo := js);
        [exact AI| exact PAT2| exact EL| exact VJ0| lia| exact NODE2| lia| lia| lia| exact FRS| lia| lia| lia
        | exact HEAP| exact AUX| lia| exact ST| unfold elem_need, ATP_LEAFX, RMALLOC_STACK; lia| clear - Q16; lia| rewrite ELX; exact ERR| exact MI]. }
    cbv beta. intros [] s'' ms' PO. unfold hpost in PO.
    destruct PO as (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m3 & -> & MI3 & ST3 & [errv3 ERR3] & AUX3 & FA3 & SO3 & RR).
    unfold lvl_R in RR. destruct RR as (HEAP3 & PRES3 & OUTC).
    replace (ret_pc (Z_to_bv 64 0x3f360)) with (Z_to_bv 64 0x3f360) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (agree_of_lx_pres _ _ _ _ _ PRES3) as AG3.
    apply (rw_cells_agree _ _ _ _ _ AG3) in FRA; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG3) in NODE2; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG3) in RT; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG3) in FRK; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG3) in FRSV; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG3) in FRB; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG3) in OUT; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
    rewrite ELX in ERR3.
    pose proof (munch_refl [(q - 208, q)]%Z m3) as MU3. pose proof (wmono_refl usegs m3) as WM3.
    destruct OUTC as (r0' & j'' & code' & jn' & OUTC & CR' & OIMP).
    pose proof (bv_unsigned_in_range 64 r0') as R0R.

    step. step. astep. astep. hstep. hstep. step. if_lia. hstep. name_mem m4.
    lazymatch goal with H : rw_cells usegs m4 (q + -152) _ |- _ => rename H into NODE4 end.
    lazymatch goal with H : rw_cells usegs m4 (q + -136) _ |- _ => rename H into RT4 end.
    lazymatch goal with H : rw_cells usegs m4 (q + -176) _ |- _ => rename H into OUTC4 end.
    lazymatch goal with H : mem_inv usegs m4 |- _ => rename H into MI4 end.
    lazymatch goal with H : stk usegs m4 _ _ |- _ => rename H into ST4 end.
    lazymatch goal with H : munch _ m3 m4 |- _ => rename H into MU4 end.
    lazymatch goal with H : wmono usegs m3 m4 |- _ => rename H into WM4 end.
    pose proof (rw_cells_join _ _ _ _ _ NODE4 RT4 ltac:(cbn [cells_size csize Nat.add]; lia)) as REC4. cbn [app] in REC4.
    assert (HEAP4 : RHEAP s'' (ae_LB E) m4).
    { eapply LH_frame; [exact HEAP3| exact MU4| exact WM4|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX4 : rauxv_ok m4 (ae_B E)).
    { eapply rauxv_ok_frame; [exact AUX3| exact MU4| exact WM4|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (PRES4 : lx_pres (ae_LB E) q [(out, out + 24)] m0 m4).
    { eapply lx_pres_trans; [exact PRES|]. eapply lx_pres_trans; [| eapply lx_pres_of_munch; [exact MU4| exact WM4| exact CLI]].
      eapply lx_pres_sub; [exact PRES3| lia| intros b Hb; exact Hb|].
      intros a Ha Hna. cbn [rin_ivs fst snd] in Ha. split; [lia|]. split; [intros Hb; pose proof (BLB a Hb); lia| lia]. }
    destruct (rw_cells_forget _ _ _ _ OUTC4) as [js' FRS4]. cbn [cells_size csize Nat.add] in FRS4.
    pose proof (rw_cells_join _ _ _ _ _ FRA FRS4 ltac:(cbn [cells_size csize Nat.add]; lia)) as J1. cbn [app] in J1.
    destruct (rw_cells_forget _ _ _ _ J1) as [ja' FRA']. cbn [cells_size csize Nat.add] in FRA'.
    pose proof (rw_cells_join _ _ _ _ _ FRK FRSV ltac:(cbn [cells_size csize Nat.add]; lia)) as J2. cbn [app] in J2.
    destruct (rw_cells_forget _ _ _ _ J2) as [jb FRK']. cbn [cells_size csize Nat.add] in FRK'.
    eapply (obj_out ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s s'' out m0 m4 ja' jb j4 jo r0' j'' code');
      [exact FRA'| exact REC4| exact CR'| exact OIMP| exact FRK'| unfold obj_savedU; exact FRB| exact OUT| exact QO| exact OB
      | exact MI4| exact ST4| lia| exists errv3; rewrite ELX; exact ERR3| exact AUX4| | | exact HEAP4| exact PRES4].
    - rewrite FA3. exact FA.
    - rewrite SO3. exact SO.
  Qed.
End Obj.
End WithCeiling0.
