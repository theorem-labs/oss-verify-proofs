(* talk, PLAIN build: the chunk loop fragment F_chunk (lib/Prog/talk_defs.v), 0x157d0 .. 0x157fc,
   0x15800 .. 0x15808 (into the message loop F_msg, lib/Prog/talk_msg.v) and 0x15844 .. 0x15848.
   Induction on the fuel of chunk_loop. Each turn stores the cursor c+1 at M+8 (`sw a1, 8(s4)`),
   loads chunk_len[c] (ld at G+0x40000+8c), and after a chunk that answers nothing loads n_chunks
   (lw at G+0x40200), or end_errno (lw at G+0x40208) once the chunks are used up. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem talk_defs talk_kit talk_msg.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
(* the faster stepping, as lib/Prog/memcpy.v lines 19-40 *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Step.zstep ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.StepFast.sf_zstep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Destzna.dk_ands PO.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.WeqGuard.word_eq_guarded.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Stor0fe.sb_mem_after_store.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Dieta54.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require AndN.
Local Ltac lia ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Dieta54.dlia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* --------------------------------------------------------------------------
   1. the model block after the store of the cursor
   -------------------------------------------------------------------------- *)

(* two stores of the cursor: the second one wins *)
Lemma fc_set_set : forall mb x y, (12 <= length mb)%nat ->
  md_set_next (md_set_next mb x) y = md_set_next mb y.
Proof.
  intros mb x y H.
  assert (LA : length (firstn 8 mb) = 8%nat) by (rewrite length_firstn; lia).
  assert (E1 : md_set_next mb x = firstn 8 mb ++ le4 (Z_to_bv 64 x) ++ skipn 12 mb)
    by (unfold md_set_next, upd_bytes; rewrite length_le4; reflexivity).
  assert (E2 : md_set_next mb y = firstn 8 mb ++ le4 (Z_to_bv 64 y) ++ skipn 12 mb)
    by (unfold md_set_next, upd_bytes; rewrite length_le4; reflexivity).
  rewrite E1, E2. unfold md_set_next.
  pose proof (upd_bytes_mid (firstn 8 mb) (le4 (Z_to_bv 64 x)) (skipn 12 mb) (le4 (Z_to_bv 64 y))
                ltac:(rewrite !length_le4; reflexivity)) as U.
  rewrite LA in U. exact U.
Qed.

(* `sw a1, 8(s4)`: the model block takes the cursor, the fake kernel (apart) keeps its bytes *)
Lemma fc_store : forall m M mb kbs j m',
  m' = write_to_mem m (Z_to_bv 64 (M + 8)) (le4 (Z_to_bv 64 j)) ->
  model_at m M mb -> nlk_at m kbs -> apart_gnl M MD_SIZE -> mem_inv rsegs m ->
  mem_inv rsegs m' /\ model_at m' M (md_set_next mb j) /\ nlk_at m' kbs /\
  munch [(M + 8, M + 12)] m m' /\ wmono rsegs m m'.
Proof.
  intros m M mb kbs j m' -> [[HB HW] HL] [[KB KW] KL] AP MI.
  change (Z_to_bv 64 (M + 8)) with (wa (M + 8)).
  pose proof (bytes_at_bound rsegs m M mb HB) as BD. pose proof (bytes_at_bound rsegs m A_G_NL kbs KB) as BK.
  unfold MD_SIZE in HL. unfold apart_gnl, MD_SIZE, NK_SIZE in AP. unfold NK_SIZE in KL.
  split; [|split; [|split; [|split]]].
  - apply mem_inv_store; [exact MI|]. rewrite length_le4. apply (wr_at_store_ok rsegs m M _ 8 4 HW); lia.
  - unfold model_at, u8arr. split; [split|].
    + exact (bytes_at_write_inside rsegs m M mb 8 (le4 (Z_to_bv 64 j)) HB ltac:(lia) ltac:(rewrite length_le4; lia)).
    + unfold md_set_next. rewrite upd_bytes_length by (rewrite length_le4; lia). apply wr_at_write. exact HW.
    + unfold md_set_next, MD_SIZE. rewrite upd_bytes_length by (rewrite length_le4; lia). exact HL.
  - unfold nlk_at, u8arr. split; [split|].
    + apply bytes_at_write_other; [exact KB | lia | rewrite length_le4; lia | rewrite length_le4; lia].
    + apply wr_at_write. exact KW.
    + unfold NK_SIZE. exact KL.
  - apply munch_write; [apply munch_refl | lia | rewrite length_le4; lia |].
    rewrite length_le4. cbn [inside]. left. lia.
  - apply wmono_write, wmono_refl.
Qed.

(* --------------------------------------------------------------------------
   2. words and reads of the fake kernel
   -------------------------------------------------------------------------- *)

Lemma fc_swrap32 : forall z, - 2 ^ 31 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof. intros z Hz. apply bv_swrap_small. change (bv_half_modulus 32) with (2 ^ 31). lia. Qed.

Lemma fc_rd_u32 : forall m kbs off, nlk_at m kbs -> 0 <= off -> off + 4 <= NK_SIZE ->
  ov_read_bytes rsegs m (Z_to_bv 64 (A_G_NL + off)) 4 = Some (le4 (Z_to_bv 64 (fld_u32 kbs off))).
Proof.
  intros m kbs off [[KB _] KL] H1 H2.
  unfold NK_SIZE in *.
  rewrite (tk_read m A_G_NL kbs off 4 KB H1) by lia. f_equal.
  change (Z.of_nat 4) with 4. unfold fld_u32, link_spec.rdn. apply tk_le4.
  rewrite tk_slice_length by lia. reflexivity.
Qed.

Lemma fc_rd_u64 : forall m kbs off, nlk_at m kbs -> 0 <= off -> off + 8 <= NK_SIZE ->
  ov_read_bytes rsegs m (Z_to_bv 64 (A_G_NL + off)) 8 = Some (le8 (Z_to_bv 64 (fld_u64 kbs off))).
Proof.
  intros m kbs off [[KB _] KL] H1 H2.
  unfold NK_SIZE in *.
  rewrite (tk_read m A_G_NL kbs off 8 KB H1) by lia. f_equal.
  change (Z.of_nat 8) with 8. unfold fld_u64, link_spec.rdn. apply tk_le8.
  rewrite tk_slice_length by lia. reflexivity.
Qed.

(* --------------------------------------------------------------------------
   3. chunk_loop, one turn at a time
   -------------------------------------------------------------------------- *)

Lemma fc_ret_some : forall v rc, msg_ret v rc -> v <> NlNone.
Proof. unfold msg_ret. intros v rc [[-> _] | [[code [-> _]] | [-> _]]]; discriminate. Qed.

Lemma fc_loop_hit : forall f kbs c, 0 <= c < nk_n_chunks kbs -> chunk_walk (nk_chunk kbs c) <> NlNone ->
  chunk_loop (S f) (nk_chunks kbs) (Z.to_nat c) = (chunk_walk (nk_chunk kbs c), S (Z.to_nat c)).
Proof.
  intros f kbs c Hc Hw. cbn [chunk_loop]. rewrite (tk_nth_chunks kbs c Hc). cbv beta iota.
  destruct (chunk_walk (nk_chunk kbs c)) eqn:E; [congruence | reflexivity | reflexivity | reflexivity].
Qed.

Lemma fc_loop_miss : forall f kbs c, 0 <= c < nk_n_chunks kbs -> chunk_walk (nk_chunk kbs c) = NlNone ->
  chunk_loop (S f) (nk_chunks kbs) (Z.to_nat c) = chunk_loop f (nk_chunks kbs) (Z.to_nat (c + 1)).
Proof.
  intros f kbs c Hc Hw. cbn [chunk_loop]. rewrite (tk_nth_chunks kbs c Hc). cbv beta iota. rewrite Hw. cbv beta iota.
  f_equal. lia.
Qed.

Lemma fc_loop_end : forall f kbs c, 0 <= nk_n_chunks kbs <= c ->
  chunk_loop f (nk_chunks kbs) (Z.to_nat c) = (NlNone, Z.to_nat c).
Proof.
  intros [|f] kbs c Hc; [reflexivity|]. cbn [chunk_loop]. rewrite (tk_nth_chunks_none kbs c Hc). reflexivity.
Qed.

(* --------------------------------------------------------------------------
   4. the walk
   -------------------------------------------------------------------------- *)

Ltac fc_leaf := first [ reflexivity | (f_equal; lia) | (apply Z_to_bv_eqm; Z.div_mod_to_equations; lia) ].
Ltac fc_eq :=
  lazymatch goal with |- MS _ _ _ _ _ _ _ = MS _ _ _ _ _ _ _ => idtac end;
  unfold mkR;
  repeat (first [ reflexivity
                | lazymatch goal with
                  | |- Z_to_bv 64 _ = Z_to_bv 64 _ => fail
                  | |- _ => progress f_equal
                  end ]);
  fc_leaf.

Lemma F_chunk_ok : F_chunk_spec.
Proof.
  unfold F_chunk_spec.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m M kbs mb fu.
  revert t0 t1 t2 a1 a7 s5 s6 s7 m mb.
  induction fu as [|f IH]; intros t0 t1 t2 a1 a7 s5 s6 s7 m mb c
    Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 Ha6 Hs4 Hs5 NK WF MD AG MI HC HF K1 K2.
  { cbn in HF. lia. }
  subst a0 a1 a2 a3 a4 a5 a6 s4 s5.
  unfold tG, A_G_NL in *.
  pose proof WF as WF'. destruct WF' as (WN & _ & _ & _ & _ & _ & _ & _ & WE & _).
  unfold NL_CHUNKS in WN.
  pose proof NK as NK0. destruct NK0 as [[KB KW] KL].
  pose proof MD as MD0. destruct MD0 as [[MB MW] ML].
  assert (L12 : (12 <= length mb)%nat) by (unfold MD_SIZE in ML; lia).
  pose proof (wr_at_store_ok rsegs m M _ 8 4 MW ltac:(lia) ltac:(unfold MD_SIZE in ML; lia)) as SO.
  step.                                         (* mv t1, a1 *)
  step.                                         (* addiw a1, a1, 1 *)
  rewrite (unsigned_lit c) by lia. rewrite (fc_swrap32 (c + 1)) by lia.
  step.                                         (* slli a7, t1, 3 *)
  rewrite (unsigned_lit c) by lia. rewrite Z.shiftl_mul_pow2 by lia. replace (c * 2 ^ 3) with (8 * c) by lia.
  step.                                         (* add t0, a3, a0 *)
  step.                                         (* sw a1, 8(s4) *)
  destruct (fc_store m M mb kbs (c + 1) _ eq_refl MD NK AG MI) as (MI1 & MD1 & NK1 & MU1 & WM1).
  remember (write_to_mem m (Z_to_bv 64 (M + 8)) (le4 (Z_to_bv 64 (c + 1)))) as m1 eqn:Em1.
  clear Em1 SO.
  (* the rest of the turn, from 0x157f0: n_chunks, the next chunk or end_errno *)
  assert (TAIL : forall t0 t1 t2 a7 s6 s7, chunk_walk (nk_chunk kbs c) = NlNone ->
    evt rsegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 262144) (Z_to_bv 64 (c + 1)) (Z_to_bv 64 465792)
               (Z_to_bv 64 203648) (Z_to_bv 64 16) (Z_to_bv 64 4096) (Z_to_bv 64 2) a7 s2 s3 (Z_to_bv 64 M)
               (Z_to_bv 64 (203648 + 4096 * c + 4)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x157f0) fc None m1 (seg_rom rsegs))).
  { intros t0' t1' t2' a7' s6' s7' HW.
    pose proof (fc_rd_u32 m1 kbs NK_N_CHUNKS NK1 ltac:(unfold NK_N_CHUNKS; lia) ltac:(unfold NK_N_CHUNKS, NK_SIZE; lia)) as RN.
    change (fld_u32 kbs NK_N_CHUNKS) with (nk_n_chunks kbs) in RN. unfold A_G_NL, NK_N_CHUNKS in RN.
    step.                                       (* lw a7, 0x200(a2) *)
    rewrite (tk_sx32_small (nk_n_chunks kbs)) by lia. clear RN.
    step.                                       (* add s5, s5, a5 *)
    step.                                       (* blt a1, a7 *)
    rewrite (tk_lts (c + 1) (nk_n_chunks kbs)) by lia.
    if_cases K; zify_bool K.
    - (* the next chunk *)
      eapply evt_eq;
        [ | eapply (IH _ _ _ _ _ _ _ _ m1 (md_set_next mb (c + 1)) (c + 1) eq_refl eq_refl eq_refl eq_refl eq_refl
                     eq_refl eq_refl eq_refl eq_refl NK1 WF MD1 AG MI1 ltac:(lia) ltac:(lia)) ];
        [ fc_eq | | ].
      + intros rc v j m' CL V MU' WM' MI' MD' t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' s5'' s6'' s7''.
        rewrite fc_set_set in MD' by exact L12.
        eapply K1; [ | exact V | exact (munch_trans _ _ _ _ MU1 MU') | exact (wmono_trans _ _ _ _ WM1 WM')
                   | exact MI' | exact MD' ].
        rewrite (fc_loop_miss f kbs c HC HW). exact CL.
      + intros c' f' off' ml m' CL Hc' H36 Ho Hom Hf MU' WM' MI' MD' t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6''.
        rewrite fc_set_set in MD' by exact L12.
        eapply K2; [ | lia | exact H36 | exact Ho | exact Hom | exact Hf | exact (munch_trans _ _ _ _ MU1 MU')
                   | exact (wmono_trans _ _ _ _ WM1 WM') | exact MI' | exact MD' ].
        rewrite (fc_loop_miss f kbs c HC HW). exact CL.
    - (* no chunk left: -end_errno *)
      pose proof (fc_rd_u32 m1 kbs NK_END_ERRNO NK1 ltac:(unfold NK_END_ERRNO; lia) ltac:(unfold NK_END_ERRNO, NK_SIZE; lia)) as RE.
      change (fld_u32 kbs NK_END_ERRNO) with (nk_end_errno kbs) in RE. unfold A_G_NL, NK_END_ERRNO in RE.
      step.                                     (* j 0x15844 *)
      step.                                     (* lw a0, 0x208(a2) *)
      rewrite (tk_sx32_small (nk_end_errno kbs)) by lia. clear RE.
      step.                                     (* negw a0, a0 *)
      rewrite (unsigned_lit (nk_end_errno kbs)) by lia. rewrite (fc_swrap32 (0 - nk_end_errno kbs)) by lia.
      eapply evt_eq; [ | eapply (K1 (- nk_end_errno kbs) NlNone (S (Z.to_nat c)) m1) ]; [ fc_eq | | | | | | ].
      + rewrite (fc_loop_miss f kbs c HC HW). replace (S (Z.to_nat c)) with (Z.to_nat (c + 1)) by lia.
        apply fc_loop_end. lia.
      + left. split; reflexivity.
      + exact MU1.
      + exact WM1.
      + exact MI1.
      + replace (Z.of_nat (S (Z.to_nat c))) with (c + 1) by lia. exact MD1. }
  pose proof (tk_chunk_len kbs c WF KL HC) as [ELEN LLEN].
  pose proof (fc_rd_u64 m1 kbs (NK_CHUNK_LEN + 8 * c) NK1 ltac:(unfold NK_CHUNK_LEN; lia)
                ltac:(unfold NK_CHUNK_LEN, NK_SIZE; lia)) as RL.
  remember (fld_u64 kbs (NK_CHUNK_LEN + 8 * c)) as len eqn:Elen.
  unfold A_G_NL, NK_CHUNK_LEN in RL. unfold NL_CHUNK_MAX in LLEN.
  step.                                         (* add a7, t0, a7 *)
  step.                                         (* ld t0, 0(a7) *)
  clear RL.
  step.                                         (* bge t0, a4 *)
  rewrite (tk_lts len 16) by lia.
  if_cases K; zify_bool K.
  - (* 0x15800: the messages of chunk c *)
    step.                                       (* mv a7, zero *)
    step.                                       (* slli t1, t1, 0xc *)
    rewrite (unsigned_lit c) by lia. rewrite Z.shiftl_mul_pow2 by lia. replace (c * 2 ^ 12) with (4096 * c) by lia.
    step.                                       (* add s6, a3, t1 *)
    pose proof F_msg_ok as FM. unfold F_msg_spec in FM.
    eapply evt_eq;
      [ | eapply FM with (B := 203648 + 4096 * c) (ck := nk_chunk kbs c) (fu := S (length (nk_chunk kbs c)))
                         (off := 0) (left := Z.of_nat (length (nk_chunk kbs c))) ];
      [ fc_eq | fc_leaf | fc_leaf | fc_leaf | fc_leaf | fc_leaf | | | | | | | | | | | ].
    + exact (tk_chunk_at m1 kbs c NK1 WF HC).
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + (* nothing in this chunk: 0x157f0 *)
      intros HN t0' t1' t2' a7' s7'.
      eapply evt_eq; [ | eapply (TAIL _ _ _ _ _ _ HN) ]. fc_eq.
    + (* an error or a short RTM_NEWLINK: 0x1584c *)
      intros rc V t0' t1' t2' a1' a2' a3' a7' s7'.
      eapply evt_eq; [ | eapply (K1 rc (chunk_walk (nk_chunk kbs c)) (S (Z.to_nat c)) m1) ]; [ fc_eq | | | | | | ].
      * exact (fc_loop_hit f kbs c HC (fc_ret_some _ _ V)).
      * right. exact V.
      * exact MU1.
      * exact WM1.
      * exact MI1.
      * replace (Z.of_nat (S (Z.to_nat c))) with (c + 1) by lia. exact MD1.
    + (* the first RTM_NEWLINK with room for attributes: 0x158a0 *)
      intros f' off' ml HL H36 Ho Hom Hf t0' t1' t2' a0'.
      eapply evt_eq; [ | eapply (K2 c f' off' ml m1) ]; [ fc_eq | | | | | | | | | | ].
      * rewrite (fc_loop_hit f kbs c HC) by (unfold chunk_walk; rewrite HL; discriminate).
        unfold chunk_walk. rewrite HL. reflexivity.
      * lia.
      * exact H36.
      * exact Ho.
      * exact Hom.
      * exact Hf.
      * exact MU1.
      * exact WM1.
      * exact MI1.
      * exact MD1.
  - (* a chunk too short for a message: 0x157f0 *)
    eapply evt_eq; [ | eapply TAIL ]; [ fc_eq | ].
    unfold chunk_walk. apply fm_scan_short. lia.
Qed.

Print Assumptions F_chunk_ok.
