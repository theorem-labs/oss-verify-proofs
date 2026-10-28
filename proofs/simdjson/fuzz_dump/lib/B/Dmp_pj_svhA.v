(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Mem Frame Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit
     El_os_defsA Pj_defsA Pj_ser_trefA Atp_defsA Atp_kitA Atp_objwA Dmp_pj_getdA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition DMP_PJ_SVH_A : Z := 0xafee0.

Definition gstr_W (q R : Z) : list ivl := [(q + -96, q); (R, R + 24)].

Lemma land56_tval : forall w, 0 <= w -> Z.land w 72057594037927935 = w mod 2^56.
Proof. intros w Hw. change 72057594037927935 with (Z.ones 56). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma tword_str_mod : forall o, 0 <= o < 2^56 -> (tword t_str o) mod 2^56 = o.
Proof. intros o Ho. unfold tword, t_str. replace (34 * 2^56 + o) with (o + 34 * 2^56) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia. Qed.

Lemma le8_nth7 : forall v, (0 <= v < 2^64)%Z -> nth 7 (le8 (Z_to_bv 64 v)) (Z_to_bv 8 0) = Z_to_bv 8 (ttype v).
Proof.
  intros v Hv. unfold le8, word_to_le_bytes. rewrite a_u64_small by lia.
  cbn [Z_to_le_bytes nth]. rewrite !Z.shiftr_shiftr by lia. cbn [Z.add Pos.add Pos.succ]. rewrite a_shr56. reflexivity.
Qed.
Lemma u64s_read7 : forall (ws : list word) (i : nat), (i < length ws)%nat ->
  firstn 1 (skipn (8 * i + 7) (u64s ws)) = [nth 7 (le8 (nth i ws (Z_to_bv 64 0))) (Z_to_bv 8 0)].
Proof.
  induction ws as [|w ws IH]; intros i Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i].
  - cbn [Nat.mul Nat.add u64s nth]. rewrite skipn_app, length_le8. replace (7 - 8)%nat with 0%nat by lia. cbn [skipn].
    pose proof (length_le8 w) as L. remember (le8 w) as l eqn:El. clear El.
    destruct l as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|b8 r]]]]]]]]]; cbn [length] in L; try lia. reflexivity.
  - replace (8 * S i + 7)%nat with (8 + (8 * i + 7))%nat by lia. cbn [u64s nth]. rewrite skipn_app, length_le8.
    replace (8 + (8 * i + 7) - 8)%nat with (8 * i + 7)%nat by lia. rewrite skipn_all2 by (rewrite length_le8; lia). cbn [app].
    apply IH. lia.
Qed.
Lemma tape_read_type : forall m TAPE (tws : list Z) (i : Z),
  bytes_at bsegs m TAPE (u64s (map (Z_to_bv 64) tws)) -> 0 <= i < Z.of_nat (length tws) -> 0 <= Tf tws i < 2^64 ->
  ov_read_bytes bsegs m (wa (TAPE + 8 * i + 7)) 1 = Some [Z_to_bv 8 (ttype (Tf tws i))].
Proof.
  intros m TAPE tws i HB Hi HT.
  replace (TAPE + 8 * i + 7) with (TAPE + (8 * i + 7)) by lia.
  rewrite (bytes_at_read bsegs m TAPE _ (8 * i + 7) 1 HB); [| lia| rewrite u64s_length, length_map; lia].
  f_equal. replace (Z.to_nat (8 * i + 7)) with (8 * Z.to_nat i + 7)%nat by lia.
  rewrite u64s_read7 by (rewrite length_map; lia).
  rewrite <- le8_nth7 by exact HT. do 3 f_equal.
  unfold Tf. rewrite (map_nth (Z_to_bv 64)). reflexivity.
Qed.

Lemma svh_len : forall c0 c1 c2 c3, 0 <= c0 < 256 -> 0 <= c1 < 256 -> 0 <= c2 < 256 -> 0 <= c3 < 256 ->
  Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 c3)) 24)))
                                        (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 c2)) 16))))))
        (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 c1)) 8)))
                                        (bv_unsigned (Z_to_bv 64 c0)))))
  = c0 + 2^8 * c1 + 2^16 * c2 + 2^24 * c3.
Proof.
  intros c0 c1 c2 c3 H0 H1 H2 H3.
  assert (U : forall x, 0 <= x < 2^64 -> bv_unsigned (Z_to_bv 64 x) = x) by (intros x Hx; apply a_u64_small; exact Hx).
  rewrite (U c0), (U c1), (U c2), (U c3) by lia.
  assert (S3 : Z.shiftl c3 24 = c3 * 2^24) by (apply Z.shiftl_mul_pow2; lia).
  assert (S2 : Z.shiftl c2 16 = c2 * 2^16) by (apply Z.shiftl_mul_pow2; lia).
  assert (S1 : Z.shiftl c1 8 = c1 * 2^8) by (apply Z.shiftl_mul_pow2; lia).
  rewrite (U (Z.shiftl c3 24)), (U (Z.shiftl c2 16)), (U (Z.shiftl c1 8)) by lia.
  assert (L1 : Z.lor (Z.shiftl c3 24) (Z.shiftl c2 16) = c3 * 2^24 + Z.shiftl c2 16)
    by (apply lor_shiftl_smallA; lia).
  assert (L0 : Z.lor (Z.shiftl c1 8) c0 = c1 * 2^8 + c0) by (apply lor_shiftl_smallA; lia).
  rewrite (U (Z.lor (Z.shiftl c3 24) (Z.shiftl c2 16))) by (rewrite L1; lia).
  rewrite (U (Z.lor (Z.shiftl c1 8) c0)) by (rewrite L0; lia).
  apply le32_of_lbu4A; lia.
Qed.

Local Ltac chkS H x := shz_pose H x; zstep; shz_norm.

Local Ltac after_tix ma mb MUab WMab MW MUa WMa q EL R FR ELC RC G1 G2 :=
  let XP := fresh "XP" in
  assert (XP : forall A cs, q + -80 <= A -> rw_cells bsegs ma A cs -> rw_cells bsegs mb A cs)
    by (intros A cs HA H; apply (rw_cells_agree bsegs ma mb _ _ H); [| exact WMab]; apply (agree_of_munch _ _ _ _ MUab); intros x Hx; cbn [outside]; lia);
  let FR' := fresh "FR" in let ELC' := fresh "ELC" in let RC' := fresh "RC" in
  pose proof (XP (q + -80) _ ltac:(lia) FR) as FR';
  lazymatch type of ELC with rw_cells _ _ _ ?cs => assert (ELC' : rw_cells bsegs mb EL cs)
    by (apply (rw_cells_agree bsegs ma mb _ _ ELC); [| exact WMab]; apply (agree_of_munch _ _ _ _ MUab); intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [outside]; lia) end;
  pose proof (XP R _ ltac:(lia) RC) as RC';
  clear FR ELC RC XP; rename FR' into FR; rename ELC' into ELC; rename RC' into RC;
  let G1' := fresh "G" in let G2' := fresh "G" in
  pose proof (ro_cells_transport bsegs _ ma mb _ _ G1 MUab) as G1'; cbn [cells_size csize Nat.add disjoint_from] in G1'; specialize (G1' ltac:(lia));
  pose proof (ro_cells_transport bsegs _ ma mb _ _ G2 MUab) as G2'; cbn [cells_size csize Nat.add disjoint_from] in G2'; specialize (G2' ltac:(lia));
  clear G1 G2; rename G1' into G1; rename G2' into G2;
  let MU := fresh "MU" in let WM := fresh "WM" in
  destruct (MW ma mb MUa WMa MUab WMab) as [MU WM]; clear MUa WMa MUab WMab; unfold gstr_W in MU.

Lemma svh_walk : forall (E : aenvA) (sp R EL i o l : Z)
    (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (g : list byte),
  aenvA_ok E -> AINV_A E m -> client_consts m -> mem_inv bsegs m ->
  stk bsegs m (ae_lo E) sp -> ae_lo E + 96 <= sp -> sp mod 16 = 0 ->
  shz m (ae_TAPE E) (8 * ae_n E) -> shz m (ae_SBUF E) (ae_NS E) ->
  0 <= i -> ae_T E i = tword t_str o -> str_at (ae_S E) (ae_sn E) o l ->
  rw_cells bsegs m EL [C8 (wz (ae_DOC E)); C8 (wz i)] -> EL mod 8 = 0 -> shz m EL 16 ->
  (EL + 16 <= sp - 96 \/ sp <= EL) -> 0 < EL -> EL + 16 <= USTACK_TOP ->
  rw_cells bsegs m R [CB 24 g] -> R mod 8 = 0 -> shz m R 24 -> sp <= R -> R + 24 <= USTACK_TOP ->
  (EL + 16 <= R \/ R + 24 <= EL) ->
  evt bsegs (fun ms => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (e4 : list byte) (m' : mem),
      ms = MS (mkR ra (wz sp) gp (wz TPV_A) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
              F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ rw_cells bsegs m' R [C8 (wz (ae_SBUF E + o + 4)); C8 (wz l); C4 (wz 0); CB 4 e4]
      /\ munch [(sp - 96, sp); (R, R + 24)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' (ae_lo E) sp /\ AINV_A E m')
    (MS (mkR ra (wz sp) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz R) (wz EL) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz DMP_PJ_SVH_A) fc None m (seg_rom bsegs)).
Proof.
  intros E q R EL j o l ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m g.
  intros OK AI CC MI ST LO Q16 SZT0 SZS0 J0 TJ SA ELC E8 SZE0 QE EP EH RC R8 SZR0 QR RH ER.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L [T16 [NT8 [TN [TS TL]]]] [S16 [NS8 [SNS [SS SL]]]] PTRR P0' [D8 [DF [DL [DS DT]]]] LOW [HL HT]].
    clear P1 P1L PTRR P0'.

    hide T16. hide NT8. hide S16. hide NS8. hide D8. hide E8. hide R8.
    assert (FS : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    unfold DMP_PJ_SVH_A, TPV_A, TPV in *. unfold SEGTOP_A, USTACK_TOP in *.
    destruct SA as (O0 & L0 & OL & L32 & ZT).
    assert (RA0 : 0 <= bv_unsigned ra < 2^64) by (pose proof (bv_unsigned_in_range 64 ra) as X; unfold bv_modulus in X; cbn in X; lia).
    assert (OR : 0 <= o < 2^56) by lia.
    assert (JN : j < ae_n E).
    { destruct (Z.lt_ge_cases j (ae_n E)) as [Lt|Ge]; [exact Lt| exfalso].
      unfold Tf in TJ. cbv beta in TJ. rewrite nth_overflow in TJ by lia. unfold tword, t_str in TJ. lia. }
    assert (TIR : 0 <= ae_T E j < 2^64) by (rewrite TJ; apply tword_range; [unfold t_str; lia| exact OR]).
    assert (TTR : 0 <= ttype (ae_T E j) < 256) by (unfold ttype; lia).
    assert (AIM : forall m', munch (gstr_W q R) m m' -> wmono bsegs m m' -> AINV_A E m').
    { intros m' MU' _. apply (AINV_A_munch E _ m m' OK AI MU'). unfold gstr_W.
      apply Forall_cons; [cbn [fst]; lia|]. apply Forall_cons; [cbn [fst]; lia| apply Forall_nil]. }
    assert (CCW : forall m', munch (gstr_W q R) m m' -> wmono bsegs m m' -> client_consts m').
    { intros m' MU' _. apply (client_consts_munch _ m m' CC MU'). intros x Hx. unfold gstr_W. cbn [outside]. split; [lia| split; [lia| exact I]]. }
    assert (SHZE : forall m', munch (gstr_W q R) m m' -> wmono bsegs m m' -> shz m' EL 16).
    { intros m' MU' _. apply (shz_munch _ m m' EL 16 SZE0 MU'); [| lia| lia].
      intros x Hx. unfold gstr_W. cbn [outside]. split; [Z.div_mod_to_equations; lia| split; [Z.div_mod_to_equations; lia| exact I]]. }
    assert (SHZR : forall m', munch (gstr_W q R) m m' -> wmono bsegs m m' -> shz m' R 24).
    { intros m' MU' _. apply (shz_munch _ m m' R 24 SZR0 MU'); [| lia| lia].
      intros x Hx. unfold gstr_W. cbn [outside]. split; [Z.div_mod_to_equations; lia| split; [Z.div_mod_to_equations; lia| exact I]]. }
    assert (SHZT : forall m', munch (gstr_W q R) m m' -> wmono bsegs m m' -> shz m' (ae_TAPE E) (8 * ae_n E)).
    { intros m' MU' _. apply (shz_munch _ m m' (ae_TAPE E) (8 * ae_n E) SZT0 MU'); [| lia| lia].
      intros x Hx. unfold gstr_W. cbn [outside]. split; [Z.div_mod_to_equations; lia| split; [Z.div_mod_to_equations; lia| exact I]]. }
    assert (SHZS : forall m', munch (gstr_W q R) m m' -> wmono bsegs m m' -> shz m' (ae_SBUF E) (ae_NS E)).
    { intros m' MU' _. apply (shz_munch _ m m' (ae_SBUF E) (ae_NS E) SZS0 MU'); [| lia| lia].
      intros x Hx. unfold gstr_W. cbn [outside]. split; [Z.div_mod_to_equations; lia| split; [Z.div_mod_to_equations; lia| exact I]]. }
    assert (SHZD : forall m', munch (gstr_W q R) m m' -> wmono bsegs m m' -> shz m' (ae_DOC E) 16).
    { intros m' MU' WM'. exact (shz_doc E m' OK (AIM m' MU' WM')). }
    assert (SHB : shb_cells m) by (destruct CC as (G1 & G2 & _); exact (conj G1 G2)).
    clear SZE0 SZR0 SZT0 SZS0.
    pose proof (munch_refl (gstr_W q R) m) as MU. pose proof (wmono_refl bsegs m) as WM. unfold gstr_W in MU.
    assert (EU : bv_unsigned (wz (q + -80)) = q + -80) by (apply unsigned_lit; lia).
    assert (Q16' : (q + -80) mod 16 = 0) by (replace (q + -80) with (q + (-5) * 16) by lia; rewrite Z.mod_add by lia; exact Q16).
    hide Q16. hide Q16'.
    destruct SHB as [G1 G2].
    hide AI.

    step. carve_frame 80%nat ST.
    apply (rw_cells_split_CB bsegs _ _ [] 80 junk [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    set (j0 := firstn 8 junk) in FR. clearbody j0.
    repeat match type of FR with context [CB 8 (firstn ?a ?b)] => let jk := fresh "jk" in set (jk := firstn a b) in FR; clearbody jk end.
    do 9 step.
    step. step. step.

    assert (MW : forall m1 m2, munch (gstr_W q R) m m1 -> wmono bsegs m m1 -> munch [(q + -80 + -16, q + -80)] m1 m2 -> wmono bsegs m1 m2 ->
                 munch (gstr_W q R) m m2 /\ wmono bsegs m m2).
    { intros m1 m2 MU1 WM1 MU2 WM2. split; [| exact (wmono_trans _ _ _ _ WM1 WM2)].
      apply (munch_trans _ m m1 m2 MU1). eapply munch_weaken; [| exact MU2]. intros x Hx. unfold gstr_W in Hx. cbn [outside] in *. lia. }

    step. chk0 SHZE EL. step. if_false.

    step. step. step. if_dead1 by DF DS. astep. step. unhide D8; if_dead1 by D8 DF DS; hide D8.

    astep. chk0 SHZE (EL + 8). step. if_false.

    step. step.
    name_mem m1.
    lazymatch goal with MU1 : munch _ m m1, WM1 : wmono _ m m1 |- _ => rename MU1 into MUa; rename WM1 into WMa end.
    eapply (tix_cpsB E); [exact OK| exact (AIM m1 MUa WMa)| exact (CCW m1 MUa WMa)| lia| exact ST| lia| unfold USTACK_TOP, SEGTOP_A; lia| assumption| lia| reflexivity|].
    intros m2 xa1 xa3 xa4 MU2 WM2 MI2 ST2.
    after_tix m1 m2 MU2 WM2 MW MUa WMa q EL R FR ELC RC G1 G2.

    chk0 SHZT (ae_TAPE E + 8 * j). step. if_false.
    pose proof (tape_read_type m2 (ae_TAPE E) (ae_tws E) j (proj1 (AIM m2 MU WM)) ltac:(lia) TIR) as RDB.
    astep. step.
    step. if_cases KT; zify_cond KT.
    -
      exfalso. assert (TYS : ttype (ae_T E j) = t_str) by (rewrite TJ; apply ttype_tword; exact OR).
      unfold t_str in TYS. clear - KT TYS TTR. lia.
    -

      chkS SHZE EL. step. if_false.
      step. step. if_dead1 by DF DS. astep. step. unhide D8; if_dead1 by D8 DF DS; hide D8.
      chkS SHZE (EL + 8). step. if_false.
      step. step.
      lazymatch goal with MU1 : munch _ m m2, WM1 : wmono _ m m2 |- _ => rename MU1 into MUa; rename WM1 into WMa end.
      eapply (tix_cpsB E); [exact OK| exact (AIM m2 MUa WMa)| exact (CCW m2 MUa WMa)| lia| exact ST2| lia| unfold USTACK_TOP, SEGTOP_A; lia| assumption| lia| reflexivity|].
      intros m3 xb1 xb3 xb4 MU3 WM3 MI3 ST3.
      after_tix m2 m3 MU3 WM3 MW MUa WMa q EL R FR ELC RC G1 G2. clear MI2 ST2 RDB.
      lazymatch goal with MU1 : munch _ m m3, WM1 : wmono _ m m3 |- _ => rename MU1 into MU; rename WM1 into WM end.
      pose proof (AIM m3 MU WM) as (TAPEB & _ & _ & DOCC & _).
      pose proof (tape_read _ (ae_TAPE E) (ae_tws E) j TAPEB ltac:(lia)) as RDT. clear TAPEB.

      chkS SHZE EL. step. if_false.
      step. step. step. if_dead1 by DF DS. astep. step. unhide D8; if_dead1 by D8 DF DS; hide D8.
      chk0 SHZT (ae_TAPE E + 8 * j). step. if_false.
      astep. chk0 SHZD (ae_DOC E + 8). step. if_false.
      step. step. if_dead1 by SS.

      step. step. astep. astep.
      replace (Z.land (ae_T E j) 72057594037927935) with o by (symmetry; rewrite land56_tval by lia; rewrite TJ; apply tword_str_mod; exact OR).
      astep. astep. step. if_dead1 by SS O0. step. if_dead1 by SS O0 SL SNS OL L0 HL HT.

      chkS SHZE (EL + 8). step. if_false.
      step. step. clear RDT DOCC.
      lazymatch goal with MU1 : munch _ m m3, WM1 : wmono _ m m3 |- _ => rename MU1 into MUa; rename WM1 into WMa end.
      eapply (tix_cpsB E); [exact OK| exact (AIM m3 MUa WMa)| exact (CCW m3 MUa WMa)| lia| exact ST3| lia| unfold USTACK_TOP, SEGTOP_A; lia| assumption| lia| reflexivity|].
      intros m4 xc1 xc3 xc4 MU4 WM4 MI4 ST4.
      after_tix m3 m4 MU4 WM4 MW MUa WMa q EL R FR ELC RC G1 G2. clear MI3 ST3.
      lazymatch goal with MU1 : munch _ m m4, WM1 : wmono _ m m4 |- _ => rename MU1 into MU; rename WM1 into WM end.
      pose proof (AIM m4 MU WM) as (TAPEB & SBUFB & _ & DOCC & _).
      pose proof (tape_read _ (ae_TAPE E) (ae_tws E) j TAPEB ltac:(lia)) as RDT. clear TAPEB.

      chkS SHZE EL. step. if_false.
      step. step. if_dead1 by DF DS. astep. step. unhide D8; if_dead1 by D8 DF DS; hide D8.
      chk0 SHZT (ae_TAPE E + 8 * j). step. if_false.
      astep. chk0 SHZD (ae_DOC E + 8). step. if_false.
      step. step. clear RDT DOCC.

      astep. replace (Z.land (ae_T E j) 72057594037927935) with o by (symmetry; rewrite land56_tval by lia; rewrite TJ; apply tword_str_mod; exact OR).
      astep. step. if_dead1 by SS O0 SL SNS OL L0 HL HT.
      astep. astep.
      replace (0 <? ae_SBUF E) with true by (symmetry; apply Z.ltb_lt; lia).
      replace (ae_SBUF E + o <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
      astep. step. if_false. step. if_dead1 by SS. step. if_dead1 by QR LO LOW.

      chk0 SHZS (ae_SBUF E + o). step. if_false.
      astep. chk0 SHZS (ae_SBUF E + o + 3). step. if_false.
      chk0 SHZR R. step. if_false.

      assert (SNL : ae_sn E = Z.of_nat (length (ae_sbs E))) by reflexivity.
      pose proof (sbuf_read1 m4 (ae_SBUF E) (ae_sbs E) o SBUFB ltac:(lia)) as RS0.
      pose proof (sbuf_read1 m4 (ae_SBUF E) (ae_sbs E) (o + 1) SBUFB ltac:(lia)) as RS1. replace (ae_SBUF E + (o + 1)) with (ae_SBUF E + o + 1) in RS1 by lia.
      pose proof (sbuf_read1 m4 (ae_SBUF E) (ae_sbs E) (o + 2) SBUFB ltac:(lia)) as RS2. replace (ae_SBUF E + (o + 2)) with (ae_SBUF E + o + 2) in RS2 by lia.
      pose proof (sbuf_read1 m4 (ae_SBUF E) (ae_sbs E) (o + 3) SBUFB ltac:(lia)) as RS3. replace (ae_SBUF E + (o + 3)) with (ae_SBUF E + o + 3) in RS3 by lia.
      clear SBUFB.
      assert (CR : forall k, 0 <= k < ae_sn E -> 0 <= Tf (ae_sbs E) k < 256).
      { intros k Hk. unfold Tf. apply (Forall_nth_Z _ (ae_sbs E) (Z.to_nat k) SBS). lia. }
      pose proof (CR o ltac:(lia)) as C0R. pose proof (CR (o + 1) ltac:(lia)) as C1R. pose proof (CR (o + 2) ltac:(lia)) as C2R. pose proof (CR (o + 3) ltac:(lia)) as C3R.
      clear CR.

      unfold le32 in L32. cbv beta in L32.
      set (c0 := Tf (ae_sbs E) o) in *. set (c1 := Tf (ae_sbs E) (o + 1)) in *. set (c2 := Tf (ae_sbs E) (o + 2)) in *. set (c3 := Tf (ae_sbs E) (o + 3)) in *.
      clearbody c0 c1 c2 c3.

      repeat match goal with H : ov_read_bytes _ _ _ 1 = Some [Z_to_bv 8 0] |- _ => clear H end.
      hide RS1. hide RS2. hide RS3.
      step. unhide RS1. step. unhide RS2. step. unhide RS3. step.

      apply (rw_cells_split_CB bsegs _ _ [] 24 g [] [8; 8; 4; 4]%nat) in RC; [| reflexivity]. cbn [mk_CB_cells app] in RC.
      step.

      astep. chk0 SHZR (R + 8). step. if_false.
      step. step. step. step. step. step.
      step. step.

      repeat match goal with |- evt _ _ (MS ?r _ _ _ _ _ _) =>
        match r with context [Some (Z_to_bv 64 (Z.lor ?x ?y))] => let w := fresh "lw" in set (w := Z.lor x y) end end.
      repeat match goal with |- evt _ _ (MS ?r _ _ _ _ _ _) =>
        match r with context [Some (Z_to_bv 64 (Z.shiftl ?x ?y))] => let w := fresh "lw" in set (w := Z.shiftl x y) end end.
      zstep. chk0 SHZR (R + 16). step. if_false.
      step.
      do 9 step. step.
      clear ST. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with H : stk bsegs mx _ _ |- _ => release_frame FR H q end end. step.
      apply evt_done.
      lazymatch goal with H : rw_cells bsegs _ R _ |- _ => rename H into RCF end.
      repeat match goal with x := _ : Z |- _ => subst x end.
      rewrite (svh_len c0 c1 c2 c3 C0R C1R C2R C3R), L32 in RCF.
      replace (ae_SBUF E + (o + 4)) with (ae_SBUF E + o + 4) in RCF by lia.
      replace (q - 96) with (q + -96) by lia.
      do 16 eexists. lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end.
      split; [atp_st_eq_goal|]. split; [exact RCF|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|].
      split; [lazymatch goal with H : stk bsegs _ _ q |- _ => exact H end|].
      exact (AIM _ MU WM).
Qed.
