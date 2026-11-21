(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_tr_stored Z_tr_fb1 Z_tr_fb2 Z_tr_fb3 Z_tr_fb7.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees SendModel BitsModel BitsModel2 FillWinModel TrSmallModel TreeModel FlushBlockModel RefFlushBlk12 RefFlushBlk13.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Lemma tfb_emit_ns : forall (L : dlay) (X Rfin : deflate_state) (c : cstrm) (buf : option Z) (last len bufp mb SL OL d lo : Z) (m0 : mem)
    (ra0 s0o s1o s2o s3o s4o s5o s6o sp : word)
    (ra gp tp t0 t1 t2 a2 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L X -> dzs m L c -> ds_strm X = c -> mem_inv psegs m ->
  munch (tfW L lo sp) m0 m -> wmono psegs m0 m ->
  rw_cells psegs m (bv_unsigned sp + -64) (tf_frame ra0 s0o s1o s2o s3o s4o s5o s6o) ->
  stk psegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - Z_TRFB_STACK -> dlay_below L lo (bv_unsigned sp) ->
  BINV 65536 X -> 0 <= last <= 1 -> 0 <= mb <= 18 -> 0 <= SL < 2^64 -> 0 <= OL < 2^64 ->
  d = (if SL =? OL then 0 else 1) ->
  match d with 0 => RefFlushBlk13.stat_ok 65536 last X | 1 => RefFlushBlk12.dyn_ok 65536 last X mb | _ => RefFlushBlk13.sto_ok 65536 X buf len last end ->
  RefFlushBlk13.post_ok 65536 last (tfb_emit d X mb buf len last) ->
  Rfin = tfb_fin last (tfb_emit d X mb buf len last) ->
  evt psegs (tfb_post_gen ra0 sp gp tp s0o s1o s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 F fc L Rfin lo m0)
      (MS (tfR L sp last len bufp ra gp tp t0 t1 t2 (wz mb) (wz SL) a2 (wz OL) a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b7bc) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ST DZ ESTRM MI MU WM FR STK LO BEL BI Rl Rmb RSL ROL Ed SAFE POK ER.
  pose proof BI as (RBV & RBB & RPD).
  pose proof ST as ST'. destruct ST' as [_ _ _ GD _ _ _ _ _ _ _ _ _ _ _ LAY]. lay_open LAY.
  destruct GD as (hD0 & hD1 & hD2 & hD3 & hD4 & GD). unfold dsD_cells in GD.
  unfold tfR. zs2. clear GD. zstep. br_cases K.
  -
    rewrite (proj2 (Z.eqb_neq _ _) K) in Ed. subst d.
    eapply (tfb_arm_dyn L X Rfin c buf last len bufp mb lo m0); try eassumption.
  -
    rewrite (proj2 (Z.eqb_eq _ _) K) in Ed. subst d. rewrite tfb_emit_0 in POK, ER.
    eapply (tfb_arm_static L X Rfin c last len bufp lo m0); try eassumption.
Qed.

Lemma tfb_emit_all : forall (L : dlay) (X Rfin : deflate_state) (c : cstrm) (buf : option Z) (last len mb SL OL d lo : Z) (m0 : mem)
    (ra0 s0o s1o s2o s3o s4o s5o s6o sp : word)
    (ra gp tp t0 t1 t2 a2 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L X -> dzs m L c -> ds_strm X = c -> mem_inv psegs m ->
  munch (tfW L lo sp) m0 m -> wmono psegs m0 m ->
  rw_cells psegs m (bv_unsigned sp + -64) (tf_frame ra0 s0o s1o s2o s3o s4o s5o s6o) ->
  stk psegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - Z_TRFB_STACK -> dlay_below L lo (bv_unsigned sp) ->
  BINV 65536 X -> fb_buf_ok buf len -> 0 <= len < 2^64 -> 0 <= last <= 1 -> 0 <= mb <= 18 -> 0 <= SL < 2^64 -> 0 <= OL < 2^64 ->
  d = (if (wrap64 (len + 4) <=? OL) && is_some buf then 2 else if SL =? OL then 0 else 1) ->
  match d with 0 => RefFlushBlk13.stat_ok 65536 last X | 1 => RefFlushBlk12.dyn_ok 65536 last X mb | _ => RefFlushBlk13.sto_ok 65536 X buf len last end ->
  RefFlushBlk13.post_ok 65536 last (tfb_emit d X mb buf len last) ->
  Rfin = tfb_fin last (tfb_emit d X mb buf len last) ->
  evt psegs (tfb_post_gen ra0 sp gp tp s0o s1o s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 F fc L Rfin lo m0)
      (MS (tfR L sp last len (buf_ptr L buf) ra gp tp t0 t1 t2 (wz mb) (wz SL) a2 (wz OL) a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b78c) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ST DZ ESTRM MI MU WM FR STK LO BEL BI BOK Rlen Rl Rmb RSL ROL Ed SAFE POK ER.
  pose proof BI as (RBV & RBB & RPD).
  assert (LAY : dlay_ok L) by (destruct ST; assumption). lay_open LAY.
  unfold tfR. destruct buf as [off|]; cbn [buf_ptr is_some] in *.
  -
    pose proof BOK as [Roff Roff2].
    zstep. br_false. zs2. zstep. br_cases K.
    +
      rewrite wrap64_id in Ed by lia. rewrite (proj2 (Z.leb_gt _ _)) in Ed by lia. cbn [andb] in Ed.
      eapply (tfb_emit_ns L X Rfin c (Some off) last len (dl_Aw L + off) mb SL OL d lo m0); try eassumption.
    + rewrite wrap64_id in Ed by lia. rewrite (proj2 (Z.leb_le _ _)) in Ed by lia. cbn [andb] in Ed. subst d. rewrite tfb_emit_2 in POK, ER.
      eapply (tfb_arm_stored L X Rfin c (Some off) last len lo m0); try eassumption.
  -
    rewrite Bool.andb_false_r in Ed.
    zstep. br_true.
    eapply (tfb_emit_ns L X Rfin c None last len 0 mb SL OL d lo m0); try eassumption.
Qed.

Definition tfb_SL (X6 : deflate_state) : Z := Z.shiftr (wrap64 (ds_static_len X6 + 3 + 7)) 3.
Definition tfb_OL (X6 : deflate_state) : Z :=
  let opt_lenb := Z.shiftr (wrap64 (ds_opt_len X6 + 3 + 7)) 3 in
  if (tfb_SL X6 <=? opt_lenb) || (ds_strategy X6 =? Z_FIXED) then tfb_SL X6 else opt_lenb.

Definition tfb_optlen_post (L : dlay) (X5 : deflate_state) (sp : word) (last len bufp mb : Z)
    (ra gp tp t0 t1 t2 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a2 a4 m',
    ms' = MS (tfR L sp last len bufp ra gp tp t0 t1 t2 (wz mb) (wz (tfb_SL (tfb_X6 X5 mb))) a2 (wz (tfb_OL (tfb_X6 X5 mb))) a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz 0x1b78c) fc None m' (seg_rom psegs)
    /\ munch [(dl_As L + 5912, dl_As L + 5920)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ dsD m' L (tfb_X6 X5 mb).

Lemma tfb_optlen : forall (L : dlay) (X5 : deflate_state) (sp : word) (last len bufp mb : Z)
    (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  dsA m L X5 -> dsD m L X5 -> mem_inv psegs m -> dlay_ok L ->
  0 <= ds_opt_len X5 < 2^63 -> 0 <= ds_static_len X5 < 2^63 -> 0 <= ds_strategy X5 <= 4 -> 0 <= mb <= 18 ->
  evt psegs (tfb_optlen_post L X5 sp last len bufp mb ra gp tp t0 t1 t2 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (tfR L sp last len bufp ra gp tp t0 t1 t2 (wz mb) a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b74c) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros GA GD MI LAY Rol Rsl Rst Rmb.
  pose proof (munch_refl [(dl_As L + 5912, dl_As L + 5920)] m) as MU. pose proof (wmono_refl psegs m) as WM.
  lay_open LAY.
  destruct GA as (hA1 & hA2 & hA3 & hA4 & hA5 & GA). unfold dsA_cells in GA.
  destruct GD as (hD0 & hD1 & hD2 & hD3 & hD4 & GD). unfold dsD_cells in GD.
  assert (SHR : forall x, 0 <= x < 2^63 + 200 -> 0 <= Z.shiftr x 3 < 2^63).
  { intros x Hx. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  assert (E6o : ds_opt_len (tfb_X6 X5 mb) = mb * 2 + mb + ds_opt_len X5 + 17).
  { unfold tfb_X6. rewrite RefFlushBlk13.ds_opt_len_set_opt_len, wrap64_id by lia. lia. }
  assert (ESL : tfb_SL (tfb_X6 X5 mb) = Z.shiftr (ds_static_len X5 + 10) 3).
  { unfold tfb_SL. change (ds_static_len (tfb_X6 X5 mb)) with (ds_static_len X5). rewrite wrap64_id by lia. f_equal. lia. }
  assert (EOLb : Z.shiftr (wrap64 (ds_opt_len (tfb_X6 X5 mb) + 3 + 7)) 3 = Z.shiftr (mb * 2 + mb + ds_opt_len X5 + 27) 3).
  { rewrite E6o, wrap64_id by lia. f_equal. lia. }
  pose proof (SHR (ds_static_len X5 + 10) ltac:(lia)) as RSLb. pose proof (SHR (mb * 2 + mb + ds_opt_len X5 + 27) ltac:(lia)) as ROLb.
  unfold tfR. zs2. zs2. zs2. shl_norm. do 7 zs2.
  set (SLb := Z.shiftr (ds_static_len X5 + 10) 3) in *. set (OLb := Z.shiftr (mb * 2 + mb + ds_opt_len X5 + 27) 3) in *.
  zs2. zstep. br_cases K.
  -
    zs2.
    apply evt_done. unfold tfb_optlen_post, tfR. rewrite ESL. unfold tfb_OL. rewrite EOLb, ESL. fold SLb OLb.
    rewrite (proj2 (Z.leb_le SLb OLb)) by lia. cbn [orb]. do 3 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    exists hD0, hD1, hD2, hD3, hD4. unfold dsD_cells. rewrite E6o. close_cells GD.
  - zs2. zs2. zstep. br_cases K2.
    +
      apply evt_done. unfold tfb_optlen_post, tfR. rewrite ESL. unfold tfb_OL. rewrite EOLb, ESL. fold SLb OLb.
      rewrite (proj2 (Z.leb_gt SLb OLb)) by lia. change (ds_strategy (tfb_X6 X5 mb)) with (ds_strategy X5). unfold Z_FIXED.
      rewrite (proj2 (Z.eqb_neq _ _) K2). cbn [orb]. do 3 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      exists hD0, hD1, hD2, hD3, hD4. unfold dsD_cells. rewrite E6o. close_cells GD.
    + zs2.
      apply evt_done. unfold tfb_optlen_post, tfR. rewrite ESL. unfold tfb_OL. rewrite EOLb, ESL. fold SLb OLb.
      change (ds_strategy (tfb_X6 X5 mb)) with (ds_strategy X5). unfold Z_FIXED.
      rewrite (proj2 (Z.eqb_eq _ _) K2), Bool.orb_true_r. do 3 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      exists hD0, hD1, hD2, hD3, hD4. unfold dsD_cells. rewrite E6o. close_cells GD.
Qed.
