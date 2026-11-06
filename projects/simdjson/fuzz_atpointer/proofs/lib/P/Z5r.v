(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Image Z11w Z119 ITree Nodes Decode Arr FP MonadX Z10q.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Malloc Require Import Zei Zf6.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.MallocP Require Import Zhy Zhz Zi1.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun Zpb Z3o Target Prog AtpImpl.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import SjTape Zpk.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Layout Exit Zfr Zq5 Sj_kit Sj_new Zq6 Zpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Z9l Z9m Zb0 Z9n Zso Z9o Z44 Z74 Z75 Z66 Z6g Z6f Z6d.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Rnd.
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

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma fresh_block_sep : forall s p A n LB m a, RHEAP s ((p, A, n) :: LB) m -> A <= a < A + n -> ~ in_block LB a.
Proof.
  intros s p A n LB m a H Ha (b & Hb & Hr).
  pose proof (LH_nodup _ _ _ H) as ND.
  assert (NE : blk_id (p, A, n) <> blk_id b).
  { intros E. cbn [map] in ND. inversion ND as [|x l NI ND' EQ]. subst. apply NI. rewrite E. apply in_map. exact Hb. }
  pose proof (LH_disjoint _ _ _ _ _ H ltac:(left; reflexivity) ltac:(right; exact Hb) NE) as D. cbn [blk_addr blk_size fst snd] in D. lia.
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

Section Obj.
  Variable E : aenv.
  Hypothesis OK : aenv_ok E.
  Variable d : nat.
  Hypothesis HELEM : atp_elem_stmt E d.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Definition esc_pre (m0 m1 : mem) (s : PState) (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (out node i e c P L0 L e0 sl : Z) (rest0 k : list Z) (REST : list (list Z)) (j0 j8 j16 j24 j32 j40 j48 j64 js j4 jo : list byte) (errv : word) : Prop :=
    rw_cells psegs m1 (q + -224) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; C8 (Z_to_bv 64 sl); CB 8 j64]
    /\ rw_cells psegs m1 (q + -152) [CB 24 js]
    /\ rw_cells psegs m1 (q + -128) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 12); CB 4 j4]
    /\ rw_cells psegs m1 (q + -104) (obj_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
    /\ rw_cells psegs m1 out [CB 24 jo] /\ q <= out /\ out + 24 <= ae_B E /\ q <= ae_DOC E /\ (out + 24 <= ae_DOC E \/ ae_DOC E + 24 <= out)
    /\ AINV E m1 /\ rw_cells psegs m1 node [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 i)] /\ q <= node /\ node + 16 <= ae_B E
    /\ ty (ae_T E) i = t_obj /\ tnext (ae_T E i) = e + 1
    /\ tiles (field (ae_T E) (ae_S E) (ae_sn E) (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d)) (i + 1) e c /\ 0 <= i /\ e + 1 <= ae_n E - 1
    /\ bytes_at psegs m1 (P + 1) (map (Z_to_bv 8) rest0) /\ Forall (fun c => 0 <= c < 256) rest0 /\ zlength rest0 = L0 /\ k = firstn (Z.to_nat L) rest0
    /\ 1 <= L <= L0 /\ L0 < 2^40 /\ 0 <= e0 < L /\ 0 <= P /\ ptr_at E P (47 :: rest0) /\ has_tilde k = true
    /\ ((sl = 18446744073709551615 /\ REST = []) \/
        (0 <= sl < L0 /\ exists r, REST = ptr_segs (47 :: r) /\ ptr_at E (P + 1 + sl) (47 :: r) /\ zlength (47 :: r) = L0 - sl))
    /\ RHEAP s (ae_LB E) m1 /\ rauxv_ok m1 (ae_B E) /\ stk psegs m1 (ae_lo E) (q + -224) /\ ae_lo E <= q - obj_need d /\ q mod 16 = 0
    /\ rw_cells psegs m1 LX_ERRNO [C4 errv] /\ mem_inv psegs m1 /\ lx_pres (ae_LB E) q [(out, out + 24)] m0 m1.

  Lemma obj_esc_sso : forall (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (out node i e c P L0 L e0 sl : Z) (rest0 k : list Z) (REST : list (list Z)) (m0 m1 : mem) (j0 j8 j16 j24 j32 j40 j48 j64 js j4 jo : list byte) (errv : word)
      (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x19 x23 x24 x25 x28 x29 x30 x31 : word),
    esc_pre m0 m1 s ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 out node i e c P L0 L e0 sl rest0 k REST j0 j8 j16 j24 j32 j40 j48 j64 js j4 jo errv -> L <= 22 ->
    implM psegs (atp_walk lops (k :: REST)) s
      (fun _ => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m0))
      (MS (mkR x1 (Z_to_bv 64 (q + -224)) gp (Z_to_bv 64 RATP) x5 x6 x7 x8 (Z_to_bv 64 (P + 1)) (Z_to_bv 64 23) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 sl) x19 (Z_to_bv 64 node) (Z_to_bv 64 L) (Z_to_bv 64 e0) x23 x24 x25 (Z_to_bv 64 out) (Z_to_bv 64 L0) x28 x29 x30 x31)
          F (Z_to_bv 64 0x2817c) fc None m1 (seg_rom psegs)).
  Proof.
    intros until x31. intros PRE L22.
    destruct PRE as (SCR & STRS & REC & FRB & OUTR & QO & OB & QD & OD & AI & NODE & QN & NB & TY & NXT & TILES & I0 & EN & KEYB & KEYF & ZL0 & EK
                     & LL0 & L040 & E0 & P0 & PAT & HT & RC & HEAP & AUX & ST & LO & Q16 & ERR & MI & PRES).
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L BT BS BP PP0 [CEIL GLO] B63 [DL DB]].
    unfold obj_need, elem_need, ATP_LEAFX, RMALLOC_STACK, GLOBALS_TOP in *. unfold obj_saved in FRB.
    assert (LO0 : 0 <= ae_lo E) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    assert (ELX : LX_ERRNO = 563116) by reflexivity. rewrite ELX in ERR.
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    pose proof (aenv_ranges E s m1 OK HEAP) as (TR & SR & PR).
    assert (BLB : forall a, in_block (ae_LB E) a -> a < alloc_ceiling) by (intros a Ha; exact (proj2 (blocks_below _ _ _ _ HEAP Ha))).
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client (ae_LB E) q [(out, out + 24)] a -> outside [(q - 304, q - 104); (q + -151, q + -151 + 23)] a).
    { intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| split; [| exact I]];
        (destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]). }
    assert (PIN : ae_PTR E <= P + 1 /\ P + 1 + L0 <= ae_PTR E + zlength (ae_p1 E)).
    { destruct PAT as (pre & Ep & EP). rewrite EP, Ep. unfold zlength in *. rewrite length_app. cbn [length]. lia. }
    assert (PCEIL : P + 1 + L0 <= alloc_ceiling).
    { destruct BP as [E0p|BPx]; [rewrite E0p in PIN; unfold zlength in PIN; cbn in PIN; lia|]. pose proof (in_blocks_range _ _ _ _ _ HEAP BPx ltac:(unfold zlength; lia)). lia. }
    pose proof (munch_refl [(q - 304, q - 104); (q + -151, q + -151 + 23)]%Z m1) as MU. pose proof (wmono_refl psegs m1) as WM.
    hide AI. hide KEYB.
    unfold implM. iprefix.

    apply (rw_cells_split_CB psegs _ _ [] 24 js [] [1; 23]%nat) in STRS; [|reflexivity]. cbn [mk_CB_cells app] in STRS.
    astep. step. rewrite le1_smallZ by lia. mem_after_store. astep. step. name_mem m2.
    apply (proj1 (rw_cells_app _ _ [_] _)) in STRS. destruct STRS as [HDRC DATA]. cbn [cells_size csize Nat.add] in DATA.
    replace (q + -152 + Z.of_nat 1) with (q + -151) in DATA by lia.
    set (KK := fun ms' : machine_state => impl psegs (at_node psegs) (atp_walk lops (k :: REST) s)
                (epost (fun p => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m0) (snd p))) ms') in *.
    assert (AI2 : AINV E m2).
    { unhide AI. eapply AINV_agree; [exact AI| eapply agree_on_of_munch; [exact MU| exact WM]| | | exact OK].
      - intros a Ha. pose proof (BLB a Ha). cbn [outside]. lia.
      - intros a Ha. cbn [outside]. lia. }
    assert (KEYB2 : bytes_at psegs m2 (P + 1) (map (Z_to_bv 8) rest0)).
    { unhide KEYB. eapply bytes_at_agree; [eapply agree_on_of_munch; [exact MU| exact WM]| exact KEYB|]. intros a Ha. rewrite length_map in Ha. unfold zlength in ZL0. cbn [outside]. lia. }
    assert (HDR2 : shdr m2 (q + -152) false (q + -151) 23 L).
    { unfold shdr. split; [| split; [lia| reflexivity]]. lazymatch type of HDRC with rw_cells _ _ _ [C1 (Z_to_bv 8 ?x)] => replace x with (2 * L) in HDRC by lia end. exact HDRC. }
    eapply evt_eq; [| eapply (obj_str_phase E OK d KK m2 F fc q false (q + -151) 23 L e0 P L0 sl rest0 i e c node out);
      [ exact HDR2| exact DATA| lia| lia| lia| lia| lia| intros X; discriminate X| intros _; reflexivity| right; split; reflexivity
      | intros a Ha Hb; pose proof (BLB a Hb); lia| exact BLB| exact PIN| exact KEYB2| exact KEYF| exact ZL0| lia| exact L040| exact P0| lia| exact PCEIL| exact E0
      | exact SCR| exact REC| exact AI2| exact NODE| exact QN| exact NB| exact QD| exact TY| exact NXT| exact TILES| exact I0| exact EN| exact TR| exact SR
      | exact ST| lia| exact CEIL'| unfold GLOBALS_TOP; lia| exact QO| exact OB| exact B63| exact MI| | ] ]; [atp_st_eq| |].

    all: assert (SLOT : forall mX sz, lstr mX (q + -152) false (q + -151) 23 sz -> exists jj, rw_cells psegs mX (q + -152) [CB 24 jj]).
    1,3: intros mX sz (_ & _ & _ & _ & _ & (bsx & BSX & LBX & _) & (HX & _ & _));
         assert (LBX' : length bsx = 23%nat) by lia;
         pose proof (rw_cells_of_u8arr _ _ _ _ BSX) as BX; rewrite LBX' in BX;
         pose proof (rw_cells_join _ _ _ _ _ HX BX ltac:(cbn [cells_size csize Nat.add]; lia)) as J; cbn [app] in J;
         destruct (rw_cells_forget _ _ _ _ J) as [jj J']; cbn [cells_size csize Nat.add] in J'; exists jj; exact J'.
    -
      intros m' sz ja' jb' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y22 y28 y29 y30 y31 LS' _ SCR' REC' MI' ST' MU' WM'.
      unfold objs_W in MU'.
      pose proof (rw_cells_transport _ _ _ _ _ _ FRB MU' WM' ltac:(cbn; lia)) as FRB'.
      pose proof (rw_cells_transport _ _ _ _ _ _ OUTR MU' WM' ltac:(cbn; lia)) as OUTR'.
      pose proof (rw_cells_transport _ _ _ _ _ _ ERR MU' WM' ltac:(cbn; lia)) as ERR'.
      pose proof LS' as (SZ0' & SZC' & _ & _ & _ & _ & (HDR' & EA' & ECAP')).
      pose proof (munch_refl [(out, out + 24)]%Z m') as MUo. pose proof (wmono_refl psegs m') as WMo.
      apply (rw_cells_split_CB psegs _ _ [] 24 _ [] [8;8;8]%nat) in OUTR'; [|reflexivity]. cbn [mk_CB_cells app] in OUTR'.
      hide MU'. astep. astep. astep. rewrite short_byte0. hstep. hstep. hstep. step. if_true. name_mem m3. unhide MU'.
      subst KK. stop_now.
      assert (LS3 : lstr m3 (q + -152) false (q + -151) 23 sz).
      { eapply lstr_frame; [exact LS'| exact MUo| exact WMo| cbn; lia| cbn; lia]. }
      destruct (SLOT m3 sz LS3) as [jj SL].
      pose proof (rw_cells_join _ _ _ _ _ SCR' SL ltac:(cbn [cells_size csize Nat.add]; lia)) as J1. cbn [app] in J1.
      pose proof (rw_cells_join _ _ _ _ _ J1 REC' ltac:(cbn [cells_size csize Nat.add]; lia)) as J2. cbn [app] in J2.
      destruct (rw_cells_forget _ _ _ _ J2) as [ja3 FRA]. cbn [cells_size csize Nat.add] in FRA.
      assert (CLIb : forall a, 0 <= a < 2^64 -> lx_client (ae_LB E) q [(out, out + 24)] a -> outside [(q - 304, q - 104); (q + -151, q + -151 + 23); (out, out + 24)] a).
      { intros a Ha HC. pose proof (CLI a Ha HC) as X. destruct HC as [HX _]. cbn [rin_ivs fst snd] in HX. cbn [outside] in X |- *. tauto. }
      assert (MU13 : munch [(q - 304, q - 104); (q + -151, q + -151 + 23); (out, out + 24)] m1 m3).
      { eapply munch_trans; [eapply munch_weaken; [| exact MU]|]. 2: eapply munch_trans; [eapply munch_weaken; [| exact MU']| eapply munch_weaken; [| exact MUo]].
        all: unfold sub_fp; cbn [outside]; intros x' Hx; lia. }
      assert (WM13 : wmono psegs m1 m3) by (eapply wmono_trans; [exact WM| exact WM']).
      eapply (obj_epi E); [exact FRA| unfold obj_saved; exact FRB'| exact MI'| exact ST'| lia| exists errv; rewrite ELX; exact ERR'| | reflexivity| reflexivity| | |].
      + eapply rauxv_ok_frame; [exact AUX| exact MU13| exact WM13|].
        constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor].
      + eapply LH_frame; [exact HEAP| exact MU13| exact WM13|].
        constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor].
      + eapply lx_pres_trans; [exact PRES|]. eapply lx_pres_of_munch; [exact MU13| exact WM13| exact CLIb].
      + destruct (rw_cells_forget _ _ _ _ OUTR') as [j' O']. cbn [cells_size csize Nat.add] in O'. exists j'. exact O'.
    -
      intros m' sz err ja' jb' w0 w1 y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y25 y28 y29 y30 y31 LS' SCR' REC' HERR MI' ST' MU' WM'.
      split; [intros _| intros X; discriminate X].
      unfold objs_W in MU'.
      pose proof (rw_cells_transport _ _ _ _ _ _ FRB MU' WM' ltac:(cbn; lia)) as FRB'.
      pose proof (rw_cells_transport _ _ _ _ _ _ OUTR MU' WM' ltac:(cbn; lia)) as OUTR'.
      pose proof (rw_cells_transport _ _ _ _ _ _ ERR MU' WM' ltac:(cbn; lia)) as ERR'.
      pose proof (rw_cells_transport _ _ _ _ _ _ NODE MU' WM' ltac:(cbn; lia)) as NODE'.
      assert (MU1' : munch [(q - 304, q - 104); (q + -151, q + -151 + 23)] m1 m').
      { eapply munch_trans; [exact MU|]. exact MU'. }
      assert (WM1' : wmono psegs m1 m') by (eapply wmono_trans; [exact WM| exact WM']).
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
      destruct (SLOT m' sz LS') as [jj SL].
      pose proof (munch_refl ([] : list (Z * Z)) m') as MU0. pose proof (wmono_refl psegs m') as WM0.
      step. step. step. if_cases KE8; zify_cond KE8.
      +
        subst KK. stop_now.
        pose proof (rw_cells_join _ _ _ _ _ SCR' SL ltac:(cbn [cells_size csize Nat.add]; lia)) as J1. cbn [app] in J1.
        destruct (rw_cells_forget _ _ _ _ J1) as [ja3 FRA]. cbn [cells_size csize Nat.add] in FRA.
        apply (proj1 (rw_cells_app _ _ [_; _] _)) in REC'. destruct REC' as [RA RB]. cbn [cells_size csize Nat.add] in RB.
        apply rec_tail_merge in RB.
        pose proof (rw_cells_join _ _ _ _ _ RA RB ltac:(cbn [cells_size csize Nat.add]; lia)) as REC3. cbn [app] in REC3.
        pose proof (rec_recast _ _ _ _ _ REC3 eq_refl) as RECX. cbn [cbytes] in RECX.
        eapply (obj_out E OK); [exact FRA| exact RECX| unfold obj_saved; exact FRB'| exact OUTR'| exact QO| exact OB| exact MI'| exact ST'| lia| exists errv; rewrite ELX; exact ERR'
                       | exact AUX'| reflexivity| reflexivity| exact HEAP'| exact PRES'].
      +
        destruct HERR as [HE20|(HE0 & vj & j' & -> & -> & EL & VJ0 & JE)]; [exfalso; lia|].
        subst KK. apply evt_done. to_implM_at (fun _ : unit => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m0)).
        apply implM_atp_walk_plain.
        apply (rw_cells_merge psegs _ _ [] [_; _; _] []) in SCR'. cbn [cells_size csize cells_bytes cbytes Nat.add app] in SCR'.
        apply (proj1 (rw_cells_app _ _ [_; _] _)) in REC'. destruct REC' as [NODE2 RT]. cbn [cells_size csize Nat.add] in RT.
        replace (q + -128 + Z.of_nat 16) with (q + -112) in RT by lia.
        pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ2. replace (Z_to_bv 64 err) with (Z_to_bv 64 0) in * by (f_equal; lia).
        eapply (obj_found E OK d HELEM ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s s out P L0 sl vj j' REST m0 m');
          [exact SCR'| exact SL| exact NODE2| exact RT| unfold obj_saved; exact FRB'| exact OUTR'| exact QO| exact OB| exact QD| exact AI'| exact EL| exact VJ0| lia| exact RC| lia
          | exact HEAP'| exact AUX'| exact ST'| unfold obj_need, elem_need, ATP_LEAFX, RMALLOC_STACK; lia| exact Q16| exists errv; rewrite ELX; exact ERR'| exact MI'
          | reflexivity| reflexivity| exact PRES'].
  Qed.
  Lemma obj_esc_heap : forall (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (out node i e c P L0 L e0 sl : Z) (rest0 k : list Z) (REST : list (list Z)) (m0 m1 : mem) (j0 j8 j16 j24 j32 j40 j48 j64 js j4 jo : list byte) (errv : word)
      (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x19 x23 x24 x25 x28 x29 x30 x31 : word),
    esc_pre m0 m1 s ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 out node i e c P L0 L e0 sl rest0 k REST j0 j8 j16 j24 j32 j40 j48 j64 js j4 jo errv -> 23 <= L ->
    implM psegs (atp_walk lops (k :: REST)) s
      (fun _ => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m0))
      (MS (mkR x1 (Z_to_bv 64 (q + -224)) gp (Z_to_bv 64 RATP) x5 x6 x7 x8 (Z_to_bv 64 (P + 1)) (Z_to_bv 64 23) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 sl) x19 (Z_to_bv 64 node) (Z_to_bv 64 L) (Z_to_bv 64 e0) x23 x24 x25 (Z_to_bv 64 out) (Z_to_bv 64 L0) x28 x29 x30 x31)
          F (Z_to_bv 64 0x281f8) fc None m1 (seg_rom psegs)).
  Proof.
    intros until x31. intros PRE L23.
    destruct PRE as (SCR & STRS & REC & FRB & OUTR & QO & OB & QD & OD & AI & NODE & QN & NB & TY & NXT & TILES & I0 & EN & KEYB & KEYF & ZL0 & EK
                     & LL0 & L040 & E0 & P0 & PAT & HT & RC & HEAP & AUX & ST & LO & Q16 & ERR & MI & PRES).
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L BT BS BP PP0 [CEIL GLO] B63 [DL DB]].
    unfold obj_need, elem_need, ATP_LEAFX, RMALLOC_STACK, GLOBALS_TOP in *. unfold obj_saved in FRB.
    assert (LO0 : 0 <= ae_lo E) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    assert (ELX : LX_ERRNO = 563116) by reflexivity. rewrite ELX in ERR.
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    pose proof (aenv_ranges E s m1 OK HEAP) as (TR & SR & PR).
    assert (BLB : forall a, in_block (ae_LB E) a -> a < alloc_ceiling) by (intros a Ha; exact (proj2 (blocks_below _ _ _ _ HEAP Ha))).
    assert (PIN : ae_PTR E <= P + 1 /\ P + 1 + L0 <= ae_PTR E + zlength (ae_p1 E)).
    { destruct PAT as (pre & Ep & EP). rewrite EP, Ep. unfold zlength in *. rewrite length_app. cbn [length]. lia. }
    assert (L026 : L0 < 2^26) by lia.
    destruct BP as [E0p|BPx]; [exfalso; rewrite E0p in PIN; unfold zlength in PIN; cbn in PIN; lia|].
    pose proof (in_blocks_range _ _ _ _ _ HEAP BPx ltac:(unfold zlength; lia)) as PRANGE.
    assert (PCEIL : P + 1 + L0 <= alloc_ceiling) by lia.
    assert (ZLK : zlength k = L) by (rewrite EK; unfold zlength in *; rewrite firstn_length_le by lia; lia).
    pose proof (str_sz_bound L ltac:(lia)) as SZB. pose proof (str_sz_even L ltac:(lia)) as SZE.
    hide AI. hide KEYB.
    pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl psegs m1) as WM.
    unfold implM. iprefix.

    pose proof (lor7_eq L ltac:(lia)) as L7. pose proof (Z.mod_pos_bound L 8 ltac:(lia)) as M8.
    assert (AT64 :
      evt psegs (fun ms' => impl psegs (at_node psegs) (atp_walk lops (k :: REST) s)
                  (epost (fun p => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m0) (snd p))) ms')
        (MS (mkR x1 (Z_to_bv 64 (q + -224)) gp (Z_to_bv 64 RATP) x5 x6 x7 x8 (Z_to_bv 64 (P + 1)) (Z_to_bv 64 23) x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 sl) (Z_to_bv 64 (str_sz L)) (Z_to_bv 64 node) (Z_to_bv 64 L) (Z_to_bv 64 e0) x23 x24 x25 (Z_to_bv 64 out) (Z_to_bv 64 L0) x28 x29 x30 x31)
            F (Z_to_bv 64 0x28360) fc None m1 (seg_rom psegs))).
    2:{ astep. rewrite L7. step. if_cases KS; zify_cond KS.
        - astep. replace (L - L mod 8 + 8) with (str_sz L) by (unfold str_sz; destruct (Z.eqb_spec L 23) as [E23|N23]; [exfalso; subst; cbn in KS; lia| rewrite L7; lia]).
          eapply evt_eq; [| apply AT64]; [atp_st_eq].
        - astep. step. replace (Z_to_bv 64 26) with (Z_to_bv 64 (str_sz L)) by (unfold str_sz; destruct (Z.eqb_spec L 23) as [E23|N23]; [reflexivity| exfalso; lia]).
          eapply evt_eq; [| apply AT64]; [atp_st_eq]. }
    step. step.
    assert (HEAP1 : RHEAP s (ae_LB E) m1) by exact HEAP.
    apply evt_done. to_implM_at (fun _ : unit => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m0)).
    apply implM_atp_walk_string; [exact HT| rewrite ZLK; unfold SSO_MAX; lia|]. rewrite ZLK.
    eapply implM_bind.
    { eapply (opnew_body HM) with (B := ae_B E) (lo := ae_lo E);
        [exact HEAP| exact AUX| lia| exact ST| exact CEIL'| unfold RMALLOC_STACK; lia| rewrite ELX; exact ERR| exact MI| lia| lia]. }
    cbv beta. intros pb s1' ms1 PO. unfold opnew_postZ in PO.
    destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3 & errv3 & A & junk & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA3 & SO3 & BR & HEAP3 & BLK).
    replace (ret_pc (Z_to_bv 64 0x28368)) with (Z_to_bv 64 0x28368) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (agree_of_heap_pres _ _ _ _ HP) as AG3.
    apply (rw_cells_agree _ _ _ _ _ AG3) in SCR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG3) in STRS; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG3) in REC; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG3) in FRB; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG3) in OUTR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG3) in NODE; [| intros a Ha; left; cbn in Ha; lia].
    assert (AI3 : AINV E m3).
    { unhide AI. eapply AINV_agree; [exact AI| exact AG3| | | exact OK].
      - intros a Ha. right. right. exact Ha.
      - intros a Ha. left. lia. }
    assert (KEYB3 : bytes_at psegs m3 (P + 1) (map (Z_to_bv 8) rest0)).
    { unhide KEYB. eapply bytes_at_agree; [exact AG3| exact KEYB|]. intros a Ha. rewrite length_map in Ha. unfold zlength in ZL0.
      right. right. eapply in_blocks_in_block; [exact BPx| lia]. }
    hide KEYB3.
    assert (PRES3 : lx_pres (ae_LB E) q [(out, out + 24)] m0 m3).
    { eapply lx_pres_trans; [exact PRES|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP| lia| auto]. }
    clear AG3 HP MU WM HEAP1. rewrite ELX in ERR3.
    pose proof BR as (BA0 & BA16 & _ & BAC & BAS). unfold OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec.Malloc.MCEIL in BAC.
    assert (NBLK : forall a, A <= a < A + str_sz L -> ~ in_block (ae_LB E) a) by (intros a Ha; eapply fresh_block_sep; [exact HEAP3| exact Ha]).

    pose proof (munch_refl [(q - 304, q - 104); (A, A + str_sz L)]%Z m3) as MU. pose proof (wmono_refl psegs m3) as WM.
    unfold implM. iprefix.
    apply (rw_cells_split_CB psegs _ _ [] 24 js [] [8;8;8]%nat) in STRS; [|reflexivity]. cbn [mk_CB_cells app] in STRS.
    step. astep. hstep. hstep. hstep. name_mem m4.
    set (KK := fun ms' : machine_state => impl psegs (at_node psegs) (mbind (del lops pb) (fun _ : unit => atp_walk lops REST) s1')
                (epost (fun p => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m0) (snd p))) ms') in *.
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client (ae_LB E) q [(out, out + 24)] a -> outside [(q - 304, q - 104); (A, A + str_sz L)] a).
    { intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| split; [| exact I]].
      - destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia].
      - destruct HC as [HC|[HC|HC]]; [lia| intros R; exact (NBLK a R HC)| lia]. }
    assert (AI4 : AINV E m4).
    { eapply AINV_agree; [exact AI3| eapply agree_on_of_munch; [exact MU| exact WM]| | | exact OK].
      - intros a Ha. pose proof (BLB a Ha). cbn [outside]. split; [lia|]. split; [| exact I]. intros R. exact (NBLK a R Ha).
      - intros a Ha. cbn [outside]. lia. }
    assert (KEYB4 : bytes_at psegs m4 (P + 1) (map (Z_to_bv 8) rest0)).
    { unhide KEYB3. eapply bytes_at_agree; [eapply agree_on_of_munch; [exact MU| exact WM]| exact KEYB3|]. intros a Ha. rewrite length_map in Ha. unfold zlength in ZL0.
      cbn [outside]. split; [lia|]. split; [| exact I]. intros R. apply (NBLK a R). eapply in_blocks_in_block; [exact BPx| lia]. }
    assert (HDR4 : shdr m4 (q + -152) true A (str_sz L) L).
    { unfold shdr. split; [| exact SZE].
      lazymatch goal with |- rw_cells _ _ _ _ => idtac end.
      lazymatch type of STRS with rw_cells _ _ _ [C8 (Z_to_bv 64 ?x); _; _] => replace x with (str_sz L + 1) in STRS by lia end. exact STRS. }
    eapply evt_eq; [| eapply (obj_str_phase E OK d KK m4 F fc q true A (str_sz L) L e0 P L0 sl rest0 i e c node out);
      [ exact HDR4| exact BLK| lia| lia| lia| lia| lia| intros _; split; lia| intros X; discriminate X| left; lia
      | exact NBLK| exact BLB| exact PIN| exact KEYB4| exact KEYF| exact ZL0| lia| exact L040| exact P0| lia| exact PCEIL| exact E0
      | exact SCR| exact REC| exact AI4| exact NODE| exact QN| exact NB| exact QD| exact TY| exact NXT| exact TILES| exact I0| exact EN| exact TR| exact SR
      | exact ST3| lia| exact CEIL'| unfold GLOBALS_TOP; lia| exact QO| exact OB| exact B63| exact MI3| | ] ]; [atp_st_eq| |].

    all: assert (CLI3 : forall a, 0 <= a < 2^64 -> lx_client (ae_LB E) q [(out, out + 24)] a -> outside [(q - 304, q - 104); (A, A + str_sz L); (out, out + 24)] a)
      by (intros a Ha HC; pose proof (CLI a Ha HC) as X; destruct HC as [HX _]; cbn [rin_ivs fst snd] in HX; cbn [outside] in X |- *; tauto).
    all: assert (WOK3 : Forall (rclient_write_ok ((pb, A, str_sz L) :: ae_LB E)) [(q - 304, q - 104); (A, A + str_sz L); (out, out + 24)])
      by (constructor; [apply W_ok_stack; cbn; lia|]; constructor; [eapply W_ok_block; [left; reflexivity| cbn; lia| cbn; lia]|];
          constructor; [apply W_ok_stack; cbn; lia| constructor]).
    -
      intros m' sz ja' jb' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y22 y28 y29 y30 y31 LS' HA0 SCR' REC' MI' ST' MU' WM'.
      rewrite (HA0 eq_refl). unfold objs_W in MU'.
      pose proof (rw_cells_transport _ _ _ _ _ _ FRB MU' WM' ltac:(cbn; lia)) as FRB'.
      pose proof (rw_cells_transport _ _ _ _ _ _ OUTR MU' WM' ltac:(cbn; lia)) as OUTR'.
      pose proof (rw_cells_transport _ _ _ _ _ _ ERR3 MU' WM' ltac:(cbn; lia)) as ERR'.
      pose proof LS' as (SZ0' & SZC' & CAP' & A0' & AC' & _ & [HDR' EV']).
      pose proof (munch_refl [(out, out + 24)]%Z m') as MUo. pose proof (wmono_refl psegs m') as WMo. hide MU'.
      pose proof (rw_cells_C8_read1 _ _ _ _ HDR') as RD0.
      apply (rw_cells_split_CB psegs _ _ [] 24 _ [] [8;8;8]%nat) in OUTR'; [|reflexivity]. cbn [mk_CB_cells app] in OUTR'.
      astep. rewrite zx8_lit by lia. astep. astep. rewrite long_byte0 by lia. hstep. hstep. hstep. step. if_false. step. astep. rewrite long_capmask by lia. step.
      name_mem m5. unhide MU'.
      assert (MU35 : munch [(q - 304, q - 104); (A, A + str_sz L); (out, out + 24)] m3 m5).
      { eapply munch_trans; [eapply munch_weaken; [| exact MU]|]. 2: eapply munch_trans; [eapply munch_weaken; [| exact MU']| eapply munch_weaken; [| exact MUo]].
        all: unfold sub_fp; cbn [outside]; intros x' Hx; lia. }
      assert (WM35 : wmono psegs m3 m5) by (eapply wmono_trans; [exact WM| exact WM']).
      assert (HEAP5 : RHEAP s1' ((pb, A, str_sz L) :: ae_LB E) m5) by (eapply LH_frame; [exact HEAP3| exact MU35| exact WM35| exact WOK3]).
      assert (AUX5 : rauxv_ok m5 (ae_B E)).
      { eapply rauxv_ok_frame; [exact AUX3| exact MU35| exact WM35|].
        constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      pose proof (LH_nodup _ _ _ HEAP5) as ND.
      subst KK. apply evt_done. to_implM_at (fun _ : unit => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m0)).
      eapply implM_bind.
      { eapply (opdel_sz_proof HF) with (B := ae_B E) (lo := ae_lo E) (A := A) (n := str_sz L);
          [exact HEAP5| left; reflexivity| exact AUX5| lia| exact ST'| exact CEIL'| unfold RFREE_STACK; lia| rewrite ELX; exact ERR'| exact MI'| lia]. }
      cbv beta. intros [] s2' ms2 PO. unfold free_postZ in PO.
      destruct PO as (u5 & u6 & u7 & u10 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m6 & -> & MI6 & ST6 & ERR6 & AUX6 & HP6 & FA6 & SO6 & HEAP6).
      rewrite (lb_remove_hd _ _ _ _ ND) in HP6, HEAP6.
      replace (ret_pc (Z_to_bv 64 0x28460)) with (Z_to_bv 64 0x28460) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (agree_of_heap_pres _ _ _ _ HP6) as AG6.
      apply (rw_cells_agree _ _ _ _ _ AG6) in SCR'; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG6) in REC'; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG6) in FRB'; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG6) in OUTR'; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG6) in HDR'; [| intros a Ha; left; cbn in Ha; lia].
      pose proof (munch_refl ([] : list (Z * Z)) m6) as MU6. pose proof (wmono_refl psegs m6) as WM6.
      unfold implM. iprefix. step. stop_now.
      pose proof (rw_cells_join _ _ _ _ _ SCR' HDR' ltac:(cbn [cells_size csize Nat.add]; lia)) as J1. cbn [app] in J1.
      pose proof (rw_cells_join _ _ _ _ _ J1 REC' ltac:(cbn [cells_size csize Nat.add]; lia)) as J2. cbn [app] in J2.
      destruct (rw_cells_forget _ _ _ _ J2) as [ja3 FRA]. cbn [cells_size csize Nat.add] in FRA.
      eapply (obj_epi E); [exact FRA| unfold obj_saved; exact FRB'| exact MI6| exact ST6| lia| exists errv3; rewrite ELX; exact ERR6| exact AUX6
                       | rewrite FA6; exact FA3| rewrite SO6; exact SO3| exact HEAP6| |].
      + eapply lx_pres_trans; [exact PRES3|]. eapply lx_pres_trans; [eapply lx_pres_of_munch; [exact MU35| exact WM35| exact CLI3]|].
        apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP6| lia| auto].
      + destruct (rw_cells_forget _ _ _ _ OUTR') as [j' O']. cbn [cells_size csize Nat.add] in O'. exists j'. exact O'.
    -
      intros m' sz err ja' jb' w0 w1 y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y25 y28 y29 y30 y31 LS' SCR' REC' HERR MI' ST' MU' WM'.
      split; [intros X; discriminate X| intros _].
      unfold objs_W in MU'.
      pose proof (rw_cells_transport _ _ _ _ _ _ FRB MU' WM' ltac:(cbn; lia)) as FRB'.
      pose proof (rw_cells_transport _ _ _ _ _ _ OUTR MU' WM' ltac:(cbn; lia)) as OUTR'.
      pose proof (rw_cells_transport _ _ _ _ _ _ ERR3 MU' WM' ltac:(cbn; lia)) as ERR'.
      pose proof (rw_cells_transport _ _ _ _ _ _ NODE MU' WM' ltac:(cbn; lia)) as NODE'.
      pose proof LS' as (SZ0' & SZC' & CAP' & A0' & AC' & _ & [HDR' EV']).
      assert (MU3' : munch [(q - 304, q - 104); (A, A + str_sz L); (out, out + 24)] m3 m').
      { eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MU']]; unfold sub_fp; cbn [outside]; intros x' Hx; lia. }
      assert (WM3' : wmono psegs m3 m') by (eapply wmono_trans; [exact WM| exact WM']).
      assert (HEAP' : RHEAP s1' ((pb, A, str_sz L) :: ae_LB E) m') by (eapply LH_frame; [exact HEAP3| exact MU3'| exact WM3'| exact WOK3]).
      assert (AUX' : rauxv_ok m' (ae_B E)).
      { eapply rauxv_ok_frame; [exact AUX3| exact MU3'| exact WM3'|].
        constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      assert (AI' : AINV E m').
      { eapply AINV_agree; [exact AI3| eapply agree_on_of_munch; [exact MU3'| exact WM3']| | | exact OK].
        - intros a Ha. pose proof (BLB a Ha). cbn [outside]. split; [lia|]. split; [intros R; exact (NBLK a R Ha)|]. split; [lia| exact I].
        - intros a Ha. cbn [outside]. lia. }
      pose proof (LH_nodup _ _ _ HEAP') as ND.
      subst KK. apply evt_done. to_implM_at (fun _ : unit => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m0)).
      eapply implM_bind.
      { eapply (opdel_sz_proof HF) with (B := ae_B E) (lo := ae_lo E) (A := A) (n := str_sz L);
          [exact HEAP'| left; reflexivity| exact AUX'| lia| exact ST'| exact CEIL'| unfold RFREE_STACK; lia| rewrite ELX; exact ERR'| exact MI'| lia]. }
      cbv beta. intros [] s2' ms2 PO. unfold free_postZ in PO.
      destruct PO as (u5 & u6 & u7 & u10 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m6 & -> & MI6 & ST6 & ERR6 & AUX6 & HP6 & FA6 & SO6 & HEAP6).
      rewrite (lb_remove_hd _ _ _ _ ND) in HP6, HEAP6.
      replace (ret_pc (Z_to_bv 64 0x28638)) with (Z_to_bv 64 0x28638) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (agree_of_heap_pres _ _ _ _ HP6) as AG6.
      apply (rw_cells_agree _ _ _ _ _ AG6) in SCR'; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG6) in REC'; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG6) in FRB'; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG6) in OUTR'; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG6) in HDR'; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG6) in NODE'; [| intros a Ha; left; cbn in Ha; lia].
      assert (AI6 : AINV E m6).
      { eapply AINV_agree; [exact AI'| exact AG6| | | exact OK]; [intros a Ha; right; right; exact Ha| intros a Ha; left; lia]. }
      assert (PRES6 : lx_pres (ae_LB E) q [(out, out + 24)] m0 m6).
      { eapply lx_pres_trans; [exact PRES3|]. eapply lx_pres_trans; [eapply lx_pres_of_munch; [exact MU3'| exact WM3'| exact CLI3]|].
        apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP6| lia| auto]. }
      rewrite ELX in ERR6.

      destruct (rw_cells_forget _ _ _ _ HDR') as [jj SL]. cbn [cells_size csize Nat.add] in SL.
      pose proof (munch_refl ([] : list (Z * Z)) m6) as MU6. pose proof (wmono_refl psegs m6) as WM6.
      unfold implM. iprefix.

      step. step. step. if_cases KE8; zify_cond KE8.
      + stop_now.
        pose proof (rw_cells_join _ _ _ _ _ SCR' SL ltac:(cbn [cells_size csize Nat.add]; lia)) as J1. cbn [app] in J1.
        destruct (rw_cells_forget _ _ _ _ J1) as [ja3 FRA]. cbn [cells_size csize Nat.add] in FRA.
        apply (proj1 (rw_cells_app _ _ [_; _] _)) in REC'. destruct REC' as [RA RB]. cbn [cells_size csize Nat.add] in RB.
        apply rec_tail_merge in RB.
        pose proof (rw_cells_join _ _ _ _ _ RA RB ltac:(cbn [cells_size csize Nat.add]; lia)) as REC3. cbn [app] in REC3.
        pose proof (rec_recast _ _ _ _ _ REC3 eq_refl) as RECX. cbn [cbytes] in RECX.
        eapply (obj_out E OK); [exact FRA| exact RECX| unfold obj_saved; exact FRB'| exact OUTR'| exact QO| exact OB| exact MI6| exact ST6| lia| exists errv3; rewrite ELX; exact ERR6
                       | exact AUX6| rewrite FA6; exact FA3| rewrite SO6; exact SO3| exact HEAP6| exact PRES6].
      + destruct HERR as [HE20|(HE0 & vj & j' & -> & -> & EL & VJ0 & JE)]; [exfalso; lia|].
        apply evt_done. to_implM_at (fun _ : unit => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m0)).
        apply (rw_cells_merge psegs _ _ [] [_; _; _] []) in SCR'. cbn [cells_size csize cells_bytes cbytes Nat.add app] in SCR'.
        apply (proj1 (rw_cells_app _ _ [_; _] _)) in REC'. destruct REC' as [NODE2 RT]. cbn [cells_size csize Nat.add] in RT.
        replace (q + -128 + Z.of_nat 16) with (q + -112) in RT by lia.
        pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ2. replace (Z_to_bv 64 err) with (Z_to_bv 64 0) in * by (f_equal; lia).
        eapply (obj_found E OK d HELEM ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s s2' out P L0 sl vj j' REST m0 m6);
          [exact SCR'| exact SL| exact NODE2| exact RT| unfold obj_saved; exact FRB'| exact OUTR'| exact QO| exact OB| exact QD| exact AI6| exact EL| exact VJ0| lia| exact RC| lia
          | exact HEAP6| exact AUX6| exact ST6| unfold obj_need, elem_need, ATP_LEAFX, RMALLOC_STACK; lia| exact Q16| exists errv3; rewrite ELX; exact ERR6| exact MI6
          | rewrite FA6; exact FA3| rewrite SO6; exact SO3| exact PRES6].
  Qed.

End Obj.
End WithCeiling0.
