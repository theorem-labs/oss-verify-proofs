(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prelim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Stdio.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ITree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Decode.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SFModel.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MonadX.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Monad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_syscalls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_pad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_stdout_write.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Scan_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_fwritex.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Shgetc_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require PImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_model.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_fprintf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
From Stdlib Require Zify.
Module SO_fwritex_stdout.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma combine_app1 {A B} : forall (l1 : list A) (l2 : list B) a b,
  length l1 = length l2 -> combine (l1 ++ [a]) (l2 ++ [b]) = combine l1 l2 ++ [(a, b)].
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] a b L; cbn in *; try discriminate; [reflexivity|].
  rewrite IH by lia. reflexivity.
Qed.

Lemma after_last_nl_snoc : forall s c,
  after_last_nl (s ++ [c]) = if c =? 10 then zlength s + 1 else after_last_nl s.
Proof.
  intros s c. unfold after_last_nl. rewrite length_app. cbn [length]. rewrite Nat.add_1_r, seq_S, map_app. cbn [map].
  rewrite combine_app1 by (rewrite length_map, length_seq; reflexivity).
  rewrite fold_left_app. cbn [fold_left fst snd]. unfold zlength. rewrite Nat.add_0_l. destruct (c =? 10); reflexivity.
Qed.

Lemma after_last_nl_nil : after_last_nl [] = 0.
Proof. reflexivity. Qed.

Lemma after_last_nl_app_nonl : forall s t, ~ In 10 t -> after_last_nl (s ++ t) = after_last_nl s.
Proof.
  intros s t. induction t as [|c t IH] using rev_ind; intros NI.
  - rewrite app_nil_r. reflexivity.
  - rewrite app_assoc, after_last_nl_snoc. rewrite in_app_iff in NI. cbn in NI.
    destruct (Z.eqb_spec c 10); [exfalso; apply NI; right; left; lia|]. apply IH. intros H; apply NI; left; exact H.
Qed.

Lemma after_last_nl_found : forall s t, ~ In 10 t -> after_last_nl (s ++ 10 :: t) = zlength s + 1.
Proof.
  intros s t NI. change (s ++ 10 :: t) with (s ++ [10] ++ t). rewrite app_assoc, after_last_nl_app_nonl by exact NI.
  rewrite after_last_nl_snoc. rewrite Z.eqb_refl. reflexivity.
Qed.

Lemma after_last_nl_range : forall s, 0 <= after_last_nl s <= zlength s.
Proof.
  induction s as [|c s IH] using rev_ind. { rewrite after_last_nl_nil. unfold zlength. cbn. lia. }
  rewrite after_last_nl_snoc. unfold zlength in *. rewrite length_app. cbn [length]. destruct (c =? 10); lia.
Qed.

(* [comment removed for export] *)
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MonadX.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_syscalls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_printf_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_stdout_write.SO_stdio_write OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_fwritex_gen OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_stdout_write.


Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.SO_piface.   (* [comment removed for export] *)

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Local Ltac step ::= step2_fast. Local Ltac stepz ::= stepz_fast.   (* [comment removed for export] *)
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
Local Ltac tslia ::= first [ exact I | gonly_lia | gonly_refute; fail 1 | tlia | split; [ tlia | exact I ] ].
(* [comment removed for export] *)

Import ITree.Exc.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma zb_app : forall a b, zb (a ++ b) = zb a ++ zb b.
Proof. intros. unfold zb. apply map_app. Qed.
Lemma zb_length : forall a, length (zb a) = length a.
Proof. intros. unfold zb. apply length_map. Qed.
Lemma zb_to_bytes : forall l, zb l = to_bytes l.
Proof. reflexivity. Qed.
Lemma zb_firstn : forall n l, zb (firstn n l) = firstn n (zb l).
Proof. intros. unfold zb. rewrite firstn_map. reflexivity. Qed.
Lemma zb_skipn : forall n l, zb (skipn n l) = skipn n (zb l).
Proof. intros. unfold zb. rewrite skipn_map. reflexivity. Qed.

Lemma split_at_znth : forall (cs : list Z) i, 0 <= i < zlength cs ->
  cs = firstn (Z.to_nat i) cs ++ znth cs i :: skipn (Z.to_nat (i + 1)) cs.
Proof.
  intros cs i Hi. unfold zlength in Hi.
  rewrite <- (firstn_skipn (Z.to_nat i) cs) at 1. f_equal.
  replace (Z.to_nat (i + 1)) with (1 + Z.to_nat i)%nat by lia. rewrite <- skipn_skipn.
  unfold znth. destruct (Z.ltb_spec i 0); [lia|].
  rewrite <- (Nat.add_0_r (Z.to_nat i)) at 2. rewrite <- (nth_skipn _ cs 0 0%Z).
  destruct (skipn (Z.to_nat i) cs) as [|c rest] eqn:E.
  - exfalso. apply (f_equal (@length Z)) in E. rewrite length_skipn in E. cbn in E. lia.
  - reflexivity.
Qed.

(* [comment removed for export] *)
Section Scan.
  Variables (ra sp gp tp t0 t1 t2 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (wpos S l : Z) (bs : list Z).
  Variable POST : machine_state -> Prop.
  Hypothesis SRC : bytes_at psegs m S (zb bs).
  Hypothesis LEN : zlength bs = l.
  Hypothesis BYT : Forall (fun c => 0 <= c < 256) bs.
  Hypothesis L1 : 1 <= l.
  Hypothesis LHI : l < 2^62.

  Definition scan_st (k : Z) (a3 : word) : machine_state :=
    MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 RSTDOUT) (Z_to_bv 64 l) (Z_to_bv 64 wpos)
            (Z_to_bv 64 (-1 - k)) (Z_to_bv 64 10) a3 a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 k) (Z_to_bv 64 (S + l))
            s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x175e8) fc None m (seg_rom psegs).
  (* [comment removed for export] *)
  Hypothesis NF : forall a3,
    after_last_nl bs = 0 ->
    evt psegs POST (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 RSTDOUT) (Z_to_bv 64 l) (Z_to_bv 64 wpos)
            (Z_to_bv 64 (-1 - l)) (Z_to_bv 64 10) a3 a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 l) (Z_to_bv 64 (S + l))
            s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x17600) fc None m (seg_rom psegs)).
  (* [comment removed for export] *)
  Hypothesis FD : forall k a3,
    0 <= k < l -> after_last_nl bs = l - k ->
    evt psegs POST (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 RSTDOUT) (Z_to_bv 64 l) (Z_to_bv 64 wpos)
            (Z_to_bv 64 (-1 - k)) (Z_to_bv 64 10) a3 a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 k) (Z_to_bv 64 (S + l))
            s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x17624) fc None m (seg_rom psegs)).

  Lemma scan_loop : forall (n : nat) k a3,
    Z.of_nat n = l - k -> 0 <= k < l ->
    ~ In 10 (skipn (Z.to_nat (l - k)) bs) ->
    evt psegs POST (scan_st k a3).
  Proof.
    induction n as [|n IH]; intros k a3 Hn Hk NI; [lia|].
    unfold scan_st.
    pose proof (bytes_at_bound _ _ _ _ SRC) as BS. rewrite zb_length in BS. unfold zlength in LEN.
    assert (RD : ov_read_bytes psegs m (wa (S + (l - 1 - k))) 1 = Some [Z_to_bv 8 (znth bs (l - 1 - k))]).
    { rewrite (bytes_at_read psegs m S (zb bs) (l - 1 - k) 1 SRC) by (rewrite ?zb_length; lia).
      f_equal. unfold zb. rewrite skipn_map, firstn_map. unfold znth.
      destruct (Z.ltb_spec (l - 1 - k) 0); [lia|].
      destruct (skipn (Z.to_nat (l - 1 - k)) bs) as [|c rest] eqn:E.
      - exfalso. apply (f_equal (@length Z)) in E. rewrite length_skipn in E. cbn in E. lia.
      - cbn [firstn map]. f_equal. f_equal. rewrite <- (Nat.add_0_r (Z.to_nat (l - 1 - k))), <- (nth_skipn _ bs 0 0%Z), E. reflexivity. }
    pose proof (proj1 (List.Forall_forall _ _) BYT) as BYT'.
    assert (CR : 0 <= znth bs (l - 1 - k) < 256).
    { unfold znth. destruct (Z.ltb_spec (l - 1 - k) 0); [lia|]. apply BYT'. apply nth_In. lia. }
    pose proof (split_at_znth bs (l - 1 - k) ltac:(unfold zlength; lia)) as SPL.
    replace (l - 1 - k + 1) with (l - k) in SPL by lia.
    step.
    replace (Z_to_bv 64 (S + l + (-1 - k)) : word) with (wa (S + (l - 1 - k))) by (unfold wa; f_equal; lia).
    step.
    unfold zxb. rewrite (Shgetc_lemmas.unsigned_lit8 _ CR).
    step. if_cases Hnl; zify_cond Hnl.
    - (* [comment removed for export] *) apply FD; [lia|].
      rewrite Hnl in SPL. rewrite SPL at 1. rewrite after_last_nl_found by exact NI.
      unfold zlength. rewrite length_firstn. lia.
    - step. step. step.
      if_cases Hend; zify_cond Hend.
      + (* [comment removed for export] *)
        replace (Z_to_bv 64 (-1 - k + -1) : word) with (Z_to_bv 64 (-1 - (k + 1)) : word) by (f_equal; lia).
        apply (IH (k + 1)).
        { clear - Hn. lia. }
        { clear - Hk Hend. lia. }
        { replace (Z.to_nat (l - (k + 1))) with (Z.to_nat (l - 1 - k)) by (clear - Hk; lia).
          rewrite SPL at 1. rewrite skipn_app. rewrite skipn_firstn_comm, Nat.sub_diag, firstn_O, length_firstn.
          replace (Z.to_nat (l - 1 - k) - Nat.min (Z.to_nat (l - 1 - k)) (length bs))%nat with 0%nat by (clear - Hk LEN; lia).
          cbn [skipn app]. intros [H|H]; [clear - H Hnl; lia| exact (NI H)]. }
      + (* [comment removed for export] *)
        replace (Z_to_bv 64 (-1 - k + -1) : word) with (Z_to_bv 64 (-1 - l) : word) by (f_equal; clear - Hend; lia).
        replace (Z_to_bv 64 (k + 1) : word) with (Z_to_bv 64 l : word) by (f_equal; exact Hend).
        apply NF.
        rewrite <- (app_nil_l bs). rewrite after_last_nl_app_nonl; [reflexivity|].
        rewrite SPL at 1. replace (Z.to_nat (l - 1 - k)) with 0%nat by (clear - Hend Hk; lia). cbn [firstn app].
        intros [H|H]; [clear - H Hnl; lia | exact (NI H)].
  Qed.
End Scan.

Lemma zbv_sub_wrap : forall e k, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 e) - k) = Z_to_bv 64 (e - k).
Proof.
  intros e k. apply ZBridge.Z_to_bv_eqm. rewrite unsigned_lit_wrap. rewrite Zminus_mod_idemp_l. reflexivity.
Qed.

Lemma CB_prefix_bytes_at : forall m A n (bb : list byte) (p : list byte),
  rw_cells psegs m A [CB n bb] -> firstn (length p) bb = p -> bytes_at psegs m A p.
Proof.
  intros m A n bb p H E.
  pose proof (rw_cells_bytes_at _ _ _ _ H) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  rewrite <- E. rewrite <- (firstn_skipn (length p) bb) in B.
  exact (proj1 (proj1 (bytes_at_app _ _ _ _ _) B)).
Qed.

Theorem fwritex_stdout_proof : fwritex_stdout_stmt.
Proof.
  unfold fwritex_stdout_stmt, out_stmt. intros St get_so set_so GS SS. intros until canary.
  intros SINK SRC BYT BSL -> -> ST LO GLO SPHI TOP SSP MI SEPF SEPB SEPS1 SEPS2 SEPS3.
  (nelim SINK 10%nat; intros ACT flags mode tail bufbytes FC FL104 BUF BUFP BUFL).
  unfold OUT_DEPTH, GLOBALS_TOP, STDOUT_BUFSIZ in *.
  change psegs with psegs in *.
  pose proof SSP as SSP0.
  destruct SSP as [GOT GUARD]. change psegs with psegs in GOT, GUARD. unfold got_ssp, ssp_guard in GOT, GUARD.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BS. rewrite zb_length in BS.
  assert (LSB : length (zb bs) = length bs) by apply zb_length.
  pose proof (bv_unsigned_in_range 64 a0) as RA0. unfold bv_modulus in RA0.
  remember (get_so st) as so eqn:ESO.
  set (buf := so_buf so) in *.
  assert (LZ : 0 <= zlength buf) by (unfold zlength; lia).
  assert (LS : 0 <= zlength bs) by (unfold zlength; lia).
  pose proof (rw_cells_bound _ _ _ _ BUF) as BB. cbn [cells_size csize Nat.add] in BB.
  assert (LBB : length bufbytes = 1024%nat) by (destruct BUF as [[WF _] _]; cbn in WF; exact (proj1 WF)).
  assert (LTB : length (to_bytes buf) = length buf) by (unfold to_bytes; apply length_map).
  set (S := bv_unsigned a0) in *.
  assert (EA0 : a0 = Z_to_bv 64 S) by (subst S; symmetry; apply Z_to_bv_bv_unsigned).
  assert (FL64 : Z.land (bv_unsigned flags) 64 = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.eq_dec i 6) as [->|NE].
    - pose proof (f_equal (fun z => Z.testbit z 6) FL104) as T. cbn beta in T. rewrite Z.land_spec, Z.bits_0 in T.
      change (Z.testbit 64 6) with true in T |- *. change (Z.testbit 104 6) with true in T. exact T.
    - change 64 with (2^6). rewrite Z.pow2_bits_eqb by lia.
      destruct (Z.eqb_spec 6 i); [lia|]. apply Bool.andb_false_r. }
  assert (BUFB : bytes_at psegs m RSTDOUT_BUF (to_bytes buf)).
  { eapply CB_prefix_bytes_at; [exact BUF|]. rewrite LTB. exact BUFP. }
  unfold zlength in *. unfold file_cells in FC.
  unfold stdout_fwritex, stdout_towrite.
  apply (implM_updso psegs get_so set_so). rewrite <- ESO, ACT.
  apply (implM_rdso psegs get_so). rewrite GS.
  set (st1 := set_so so st).
  assert (ESO1 : get_so st1 = so) by (unfold st1; apply GS).
  change (so_buf so) with buf. unfold STDOUT_BUFSIZ. cbv beta. unfold zlength.
  destruct (1024 - Z.of_nat (length buf) <? Z.of_nat (length bs)) eqn:CMP.
  - (* [comment removed for export] *)
    pose proof (proj1 (Z.ltb_lt _ _) CMP) as CMP'.
    eapply implM_evt.
    { eapply fwx_nofit with (lo := lo); [exact FC | exact EA0 | reflexivity | reflexivity | lia | lia | lia | lia
        | destruct (so_first so); lia | destruct (so_first so); reflexivity | exact ST | lia | lia | exact MI | lia]. }
    cbv beta. intros ms1 PO.
    (nelim PO 17%nat; intros t0' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m1 -> MU1 WM1 MI1 ST1).
    transport_after_call psegs m m1 MU1 WM1.
    replace (Z_to_bv 64 (if so_first so then 97288 else 96880) : word) with (Z_to_bv 64 (wfn_of (get_so st1)) : word)
      by (rewrite ESO1; reflexivity).
    eapply implM_mono.
    { eapply (stdout_writefn_spec get_so set_so GS SS) with (lo := lo) (S := S) (flags := flags) (mode := mode) (tail := tail) (canary := canary);
        [ rewrite ESO1; exact ACT
        | unfold stdout_cells, wfn_of, lbf_of, file_cells; rewrite ESO1; exact FC
        | exact FL64
        | rewrite ESO1; exact BUFB
        | rewrite ESO1; unfold zlength; exact BUFL
        | rewrite <- zb_to_bytes; exact SRC
        | reflexivity | reflexivity | reflexivity
        | exact ST1 | unfold STDOUT_WRITE_DEPTH; lia | lia
        | split; [exact GOT | exact GUARD] | exact MI1
        | unfold zlength; lia | lia | unfold zlength; lia
        | right; unfold zlength; split; lia
        | let E := fresh in intros E; rewrite E in *; unfold zlength in *; cbn [length Z.of_nat] in *; lia ]. }
    cbv beta. intros [] st' ms' PO.
    (nelim PO 23%nat; intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m2 -> MU2 WM2 MI2 ST2 FC2 SSP2 ->).
    unfold STDOUT_WRITE_DEPTH in MU2.
    rewrite ESO1 in FC2 |- *.
    pose proof (rw_cells_transport psegs _ m1 m2 _ _ BUF MU2 WM2 ltac:(cbn; lia)) as BUF2.
    pose proof (bytes_at_transport psegs _ m1 m2 _ _ SRC MU2 ltac:(cbn; rewrite LSB; lia)) as SRC2.
    unfold out_post, SR. nexists 16%nat. split; [reflexivity|].
    split. { apply (munch_trans _ m m1 m2).
             - eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; lia.
             - eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
    split; [eapply wmono_trans; [exact WM1 | exact WM2] |]. split; [exact MI2|]. split; [exact ST2|].
    split.
    { (* [comment removed for export] *)
      unfold SINK_stdout. rewrite GS. split; [reflexivity|].
      exists flags, mode, tail, bufbytes.
      split; [unfold stdout_cells, wfn_of, lbf_of in FC2; cbn [so_after so_buf so_first so_lbf_nl] in FC2; exact FC2|].
      split; [exact FL104|]. split; [exact BUF2|]. split; [reflexivity|]. unfold zlength; cbn; lia. }
    split; [exact SSP2 | exact SRC2].
  - pose proof (proj1 (Z.ltb_ge _ _) CMP) as CMP'.
    (* [comment removed for export] *)
    pose proof BUF as BUF0.
    apply (rw_cells_split_CB psegs _ _ [] 1024 bufbytes [] [length buf; 1024 - length buf]%nat) in BUF; [| cbn; lia].
    cbn [mk_CB_cells app] in BUF. rewrite BUFP in BUF.
    apply (proj1 (F_fwritex.rw_cells_app psegs _ _ [_] _)) in BUF. destruct BUF as [BUFa BUFb].
    cbn [cells_size csize Nat.add] in BUFb. rewrite Nat.add_0_r in BUFb. rewrite firstn_all2 in BUFb by (rewrite length_skipn; lia).
    destruct (so_lbf_nl so) eqn:LBF.
    2: { (* [comment removed for export] *)
      apply implM_upd. cbv beta. rewrite ESO1. unfold st1. rewrite SS.
      eapply evt_mono.
      { eapply (fwx_fit_plain ra sp gp tp t0 t1 t2 s0 s1 a0) with (lo := lo) (cap := (1024 - length buf)%nat) (src := zb bs) (S := S)
          (Fp := RSTDOUT) (wend := RSTDOUT_BUF + 1024) (wpos := RSTDOUT_BUF + Z.of_nat (length buf)) (junk := skipn (length buf) bufbytes);
          [ exact FC | exact BUFb | lia | exact SRC | rewrite LSB; reflexivity | exact EA0 | reflexivity | reflexivity | try lia .. ];
          [exact ST | exact MI]. }
      cbv beta. intros ms' PO.
      (nelim PO 23%nat; intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 -> MU2 WM2 MI2 ST2 FC2 DST2 SRC2).
      unfold out_post, SR. nexists 16%nat.
      split. { reflexivity. }
      split. { eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
      split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|].
      assert (GOT2 : rw_cells psegs m2 140520 [C8 (Z_to_bv 64 342776)]).
      { eapply (rw_cells_transport psegs _ m m2); [exact GOT | exact MU2 | exact WM2 | cbn; lia]. }
      assert (GUARD2 : rw_cells psegs m2 342776 [C8 canary]).
      { eapply (rw_cells_transport psegs _ m m2); [exact GUARD | exact MU2 | exact WM2 | cbn; lia]. }
      assert (BUFa2 : rw_cells psegs m2 RSTDOUT_BUF [CB (length buf) (to_bytes buf)]).
      { eapply (rw_cells_transport psegs _ m m2); [exact BUFa | exact MU2 | exact WM2 | cbn; lia]. }
      split.
      { (* [comment removed for export] *)
        unfold SINK_stdout. rewrite GS. cbn [so_active so_buf so_lbf_nl so_first]. split; [exact ACT|].
        exists flags, mode, tail, (to_bytes buf ++ zb bs ++ skipn (length (zb bs)) (skipn (length buf) bufbytes)).
        split. { unfold zlength, file_cells. change (so_buf so) with buf. rewrite length_app, Nat2Z.inj_add, Z.add_assoc, LBF. exact FC2. }
        split; [exact FL104|].
        split.
        { assert (J : rw_cells psegs m2 RSTDOUT_BUF ([] ++ [CB (length buf) (to_bytes buf); CB (length (zb bs)) (zb bs); CB (1024 - length buf - length (zb bs))%nat (skipn (length (zb bs)) (skipn (length buf) bufbytes))] ++ [])).
          { cbn [app]. apply (proj2 (F_fwritex.rw_cells_app psegs _ _ [_] _)); split; [exact BUFa2|].
            cbn [cells_size csize]. rewrite Nat.add_0_r. exact DST2. }
          apply rw_cells_merge in J. cbn [cells_size cells_bytes csize cbytes app Nat.add] in J. rewrite app_nil_r in J.
          rewrite LSB in J |- *.
          replace (length buf + (length bs + (1024 - length buf - length bs + 0)))%nat with 1024%nat in J by lia. exact J. }
        split.
        { change (so_buf so) with buf. rewrite length_app, app_assoc, firstn_app, length_app, LTB, LSB, Nat.sub_diag, firstn_O, app_nil_r.
          rewrite firstn_all2 by (rewrite length_app, LTB, LSB; lia). unfold to_bytes, zb. rewrite map_app. reflexivity. }
        change (so_buf so) with buf. unfold zlength. rewrite length_app. lia. }
      split; [split; [exact GOT2 | exact GUARD2] | exact SRC2]. }


    pose proof (after_last_nl_range bs) as IR. unfold zlength in IR.
    pose proof BUFa as BUFam. change (rw_cells psegs m RSTDOUT_BUF [CB (length buf) (to_bytes buf)]) with (boxed (rw_cells psegs m RSTDOUT_BUF [CB (length buf) (to_bytes buf)])) in BUFam.
    destruct (0 <? after_last_nl bs) eqn:CI.
    2: { (* [comment removed for export] *)
      pose proof (proj1 (Z.ltb_ge _ _) CI) as CI'.
      apply implM_retb. apply implM_upd. cbv beta. rewrite ESO1. unfold st1. rewrite SS.
      replace (after_last_nl bs) with 0 by (clear - CI' IR; lia). change (skipn (Z.to_nat 0) bs) with bs.
      pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT + 40, RSTDOUT + 48); (RSTDOUT_BUF + Z.of_nat (length buf), RSTDOUT_BUF + Z.of_nat (length buf) + Z.of_nat (length bs))] m) as MU.
      pose proof (wmono_refl psegs m) as WM.
      rewrite EA0.
      carve_frame 64%nat ST.
      do 13 step.
      if_cases Hw; zify_cond Hw. 1:{ exfalso. clear - Hw. lia. }
      do 3 step.
      if_cases Hr; zify_cond Hr. 2:{ exfalso. rewrite land_W64, Z.mod_small in Hr by lia. clear - Hr CMP'. lia. }
      do 3 step.
      if_cases Hl; zify_cond Hl.
      1:{ exfalso. clear - Hl. replace (bv_unsigned (sx32 (Z_to_bv 64 10))) with 10 in Hl by reflexivity. lia. }
      step. if_cases Hz; zify_cond Hz.
      1:{ (* [comment removed for export] *)
        eapply evt_mono.
        { eapply fwx_tail with (lo := lo) (cap := (1024 - length buf)%nat) (src := zb bs) (i := 0) (m0 := m);
            [ exact FR | exact FC | exact BUFb | clear - LSB CMP'; lia | exact SRC | rewrite LSB; reflexivity | exact ST
            | clear - LO GLO; lia | exact SPHI | exact MU | exact WM | exact MI
            | try (cbn in RA0; clear - RA0 Hz LSB CMP' BUFL LZ LS SEPF SEPB SEPS1 SEPS2 SEPS3 BS GLO LO SPHI; lia) .. ]. }
        cbv beta. intros ms' PO.
        (nelim PO 23%nat; intros t0' t1' t2' a1' a2' a3'' a4' a5' a6' a7' t3' t4' t5' t6' m2 -> MU2 WM2 MI2 ST2 FC2 DST2 SRC2).
        unfold out_post, SR. nexists 16%nat.
        split. { reflexivity. }
        split. { eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
        split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|].
        destruct SSP0 as [GOTm GUARDm]. change psegs with psegs in GOTm, GUARDm. unfold got_ssp, ssp_guard in GOTm, GUARDm.
        assert (GOT2 : rw_cells psegs m2 140520 [C8 (Z_to_bv 64 342776)]).
        { eapply (rw_cells_transport psegs _ m m2); [exact GOTm | exact MU2 | exact WM2 | cbn; lia]. }
        assert (GUARD2 : rw_cells psegs m2 342776 [C8 canary]).
        { eapply (rw_cells_transport psegs _ m m2); [exact GUARDm | exact MU2 | exact WM2 | cbn; lia]. }
        assert (BUFa2 : rw_cells psegs m2 RSTDOUT_BUF [CB (length buf) (to_bytes buf)]).
        { unfold boxed in BUFam. eapply (rw_cells_transport psegs _ m m2); [exact BUFam | exact MU2 | exact WM2 | cbn; lia]. }
        split.
        { (* [comment removed for export] *)
          unfold SINK_stdout. rewrite GS. cbn [so_active so_buf so_lbf_nl so_first]. split; [exact ACT|].
          exists flags, mode, tail, (to_bytes buf ++ zb bs ++ skipn (length (zb bs)) (skipn (length buf) bufbytes)).
          split. { unfold zlength, file_cells. change (so_buf so) with buf. rewrite length_app, Nat2Z.inj_add, Z.add_assoc, LBF. exact FC2. }
          split; [exact FL104|].
          split.
          { assert (J : rw_cells psegs m2 RSTDOUT_BUF ([] ++ [CB (length buf) (to_bytes buf); CB (length (zb bs)) (zb bs); CB (1024 - length buf - length (zb bs))%nat (skipn (length (zb bs)) (skipn (length buf) bufbytes))] ++ [])).
            { cbn [app]. apply (proj2 (F_fwritex.rw_cells_app psegs _ _ [_] _)); split; [exact BUFa2|].
              cbn [cells_size csize]. rewrite Nat.add_0_r. exact DST2. }
            apply rw_cells_merge in J. cbn [cells_size cells_bytes csize cbytes app Nat.add] in J. rewrite app_nil_r in J.
            rewrite LSB in J |- *.
            replace (length buf + (length bs + (1024 - length buf - length bs + 0)))%nat with 1024%nat in J by lia. exact J. }
          split.
          { change (so_buf so) with buf. rewrite length_app, app_assoc, firstn_app, length_app, LTB, LSB, Nat.sub_diag, firstn_O, app_nil_r.
            rewrite firstn_all2 by (rewrite length_app, LTB, LSB; lia). unfold to_bytes, zb. rewrite map_app. reflexivity. }
          change (so_buf so) with buf. unfold zlength. rewrite length_app. clear - CMP' LZ Hz. lia. }
        split; [split; [exact GOT2 | exact GUARD2] | exact SRC2]. }
      (* [comment removed for export] *)
      do 4 step.
      replace (Z_to_bv 64 (-1) : word) with (Z_to_bv 64 (-1 - 0) : word) by reflexivity.
      eapply (scan_loop _ sp) with (bs := bs) (n := length bs);
        [ exact SRC | reflexivity | exact BYT | clear - Hz LS; lia | clear - BSL; lia | | | clear - Hz; lia | clear - Hz LS; lia | ].
      3:{ rewrite Z.sub_0_r, Nat2Z.id, skipn_all. intros H; exact H. }
      2:{ intros k a3x Hk Hanl. exfalso. clear - Hk Hanl CI'. lia. }
      cbv beta. intros a3x _.
      step. step.
      eapply evt_mono.
      { eapply fwx_tail with (lo := lo) (cap := (1024 - length buf)%nat) (src := zb bs) (i := 0) (m0 := m);
          [ exact FR | exact FC | exact BUFb | clear - LSB CMP'; lia | exact SRC | rewrite LSB; reflexivity | exact ST
          | clear - LO GLO; lia | exact SPHI | exact MU | exact WM | exact MI
          | try (cbn in RA0; clear - RA0 Hz LSB CMP' BUFL LZ LS SEPF SEPB SEPS1 SEPS2 SEPS3 BS GLO LO SPHI; lia) .. ]. }
      cbv beta. intros ms' PO.
      (nelim PO 23%nat; intros t0' t1' t2' a1' a2' a3'' a4' a5' a6' a7' t3' t4' t5' t6' m2 -> MU2 WM2 MI2 ST2 FC2 DST2 SRC2).
      unfold out_post, SR. nexists 16%nat.
      split. { reflexivity. }
      split. { eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
      split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|].
      destruct SSP0 as [GOTm GUARDm]. change psegs with psegs in GOTm, GUARDm. unfold got_ssp, ssp_guard in GOTm, GUARDm.
      assert (GOT2 : rw_cells psegs m2 140520 [C8 (Z_to_bv 64 342776)]).
      { eapply (rw_cells_transport psegs _ m m2); [exact GOTm | exact MU2 | exact WM2 | cbn; lia]. }
      assert (GUARD2 : rw_cells psegs m2 342776 [C8 canary]).
      { eapply (rw_cells_transport psegs _ m m2); [exact GUARDm | exact MU2 | exact WM2 | cbn; lia]. }
      assert (BUFa2 : rw_cells psegs m2 RSTDOUT_BUF [CB (length buf) (to_bytes buf)]).
      { unfold boxed in BUFam. eapply (rw_cells_transport psegs _ m m2); [exact BUFam | exact MU2 | exact WM2 | cbn; lia]. }
      split.
      { (* [comment removed for export] *)
        unfold SINK_stdout. rewrite GS. cbn [so_active so_buf so_lbf_nl so_first]. split; [exact ACT|].
        exists flags, mode, tail, (to_bytes buf ++ zb bs ++ skipn (length (zb bs)) (skipn (length buf) bufbytes)).
        split. { unfold zlength, file_cells. change (so_buf so) with buf. rewrite length_app, Nat2Z.inj_add, Z.add_assoc, LBF. exact FC2. }
        split; [exact FL104|].
        split.
        { assert (J : rw_cells psegs m2 RSTDOUT_BUF ([] ++ [CB (length buf) (to_bytes buf); CB (length (zb bs)) (zb bs); CB (1024 - length buf - length (zb bs))%nat (skipn (length (zb bs)) (skipn (length buf) bufbytes))] ++ [])).
          { cbn [app]. apply (proj2 (F_fwritex.rw_cells_app psegs _ _ [_] _)); split; [exact BUFa2|].
            cbn [cells_size csize]. rewrite Nat.add_0_r. exact DST2. }
          apply rw_cells_merge in J. cbn [cells_size cells_bytes csize cbytes app Nat.add] in J. rewrite app_nil_r in J.
          rewrite LSB in J |- *.
          replace (length buf + (length bs + (1024 - length buf - length bs + 0)))%nat with 1024%nat in J by lia. exact J. }
        split.
        { change (so_buf so) with buf. rewrite length_app, app_assoc, firstn_app, length_app, LTB, LSB, Nat.sub_diag, firstn_O, app_nil_r.
          rewrite firstn_all2 by (rewrite length_app, LTB, LSB; lia). unfold to_bytes, zb. rewrite map_app. reflexivity. }
        change (so_buf so) with buf. unfold zlength. rewrite length_app. clear - CMP' LZ. lia. }
      split; [split; [exact GOT2 | exact GUARD2] | exact SRC2]. }
    (* [comment removed for export] *)
    pose proof (proj1 (Z.ltb_lt _ _) CI) as CI'.
    set (i := after_last_nl bs) in *.
    eapply (implM_evt psegs) with (P := fun ms1 => exists (k : Z) (a3x : word) (j8 : list byte) (m1 : mem),
        0 <= k < Z.of_nat (length bs) /\ i = Z.of_nat (length bs) - k /\
        ms1 = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 RSTDOUT) (Z_to_bv 64 (Z.of_nat (length bs))) (Z_to_bv 64 (RSTDOUT_BUF + Z.of_nat (length buf)))
                (Z_to_bv 64 (-1 - k)) (Z_to_bv 64 10) a3x a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 k) (Z_to_bv 64 (S + Z.of_nat (length bs)))
                s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x17624) fc None m1 (seg_rom psegs) /\
        rw_cells psegs m1 (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
        munch [(bv_unsigned sp + -64, bv_unsigned sp)] m m1 /\ wmono psegs m m1 /\ mem_inv psegs m1 /\
        stk psegs m1 lo (bv_unsigned sp + -64)).
    { pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp)] m) as MU.
      pose proof (wmono_refl psegs m) as WM.
      rewrite EA0.
      carve_frame 64%nat ST.
      do 13 step.
      if_cases Hw; zify_cond Hw. 1:{ exfalso. clear - Hw. lia. }
      do 3 step.
      if_cases Hr; zify_cond Hr. 2:{ exfalso. rewrite land_W64, Z.mod_small in Hr by lia. clear - Hr CMP'. lia. }
      do 3 step.
      if_cases Hl; zify_cond Hl.
      1:{ exfalso. clear - Hl. replace (bv_unsigned (sx32 (Z_to_bv 64 10))) with 10 in Hl by reflexivity. lia. }
      step. if_cases Hz; zify_cond Hz.
      1:{ exfalso. clear - Hz CI' IR. lia. }
      do 4 step.
      replace (Z_to_bv 64 (-1) : word) with (Z_to_bv 64 (-1 - 0) : word) by reflexivity.
      eapply (scan_loop _ sp) with (bs := bs) (n := length bs);
        [ exact SRC | reflexivity | exact BYT | clear - Hz LS; lia | clear - BSL; lia | | | clear - Hz; lia | clear - Hz LS; lia | ].
      3:{ rewrite Z.sub_0_r, Nat2Z.id, skipn_all. intros H; exact H. }
      1:{ intros a3x Hanl. exfalso. clear - Hanl CI'. subst i. lia. }
      cbv beta. intros k a3x Hk Hanl.
      apply evt_done. exists k, a3x. eexists. exists m0.
      split; [exact Hk|]. split; [subst i; exact Hanl|]. split; [reflexivity|].
      split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. exact ST. }
    intros ms1 nelH_; (nelim nelH_ 12%nat; intros k a3x j8 m1 Hk Hik -> FR1 MU1 WM1 MI1 ST1).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; clear - RSP LO GLO; lia).
    transport_after_call psegs m m1 MU1 WM1.
    eapply (implM_evt psegs). 2:{ intros ms' H; exact H. } cbv beta.
    do 5 step. step.
    rewrite ?zbv_sub_wrap. rewrite ?(unsigned_lit k) by (clear - Hk BSL; lia).
    try rewrite (Z.add_opp_r (Z.of_nat (length bs)) k).
    assert (LFI : zlength (firstn (Z.to_nat i) bs) = Z.of_nat (length bs) - k).
    { unfold zlength. rewrite length_firstn. clear - Hk Hik IR. lia. }
    rewrite <- LFI.
    rewrite (ret_pc_even _) by (destruct (so_first so); cbn; lia).
    replace (Z_to_bv 64 (if so_first so then 97288 else 96880) : word) with (Z_to_bv 64 (wfn_of (get_so st1)) : word)
      by (rewrite ESO1; reflexivity).
    assert (SRCa : bytes_at psegs m1 S (to_bytes (firstn (Z.to_nat i) bs))).
    { rewrite <- (firstn_skipn (Z.to_nat i) bs), zb_app in SRC. exact (proj1 (proj1 (bytes_at_app _ _ _ _ _) SRC)). }
    apply evt_done.
    eapply implM_bind.
    { eapply (stdout_writefn_spec get_so set_so GS SS) with (lo := lo) (S := S) (flags := flags) (mode := mode) (tail := tail) (canary := canary);
        [ rewrite ESO1; exact ACT
        | unfold stdout_cells, wfn_of, lbf_of, file_cells; rewrite ESO1, LBF; exact FC
        | exact FL64
        | rewrite ESO1; exact BUFB
        | rewrite ESO1; unfold zlength; exact BUFL
        | exact SRCa
        | reflexivity | reflexivity | reflexivity
        | rewrite ESP; exact ST1 | rewrite ESP; unfold STDOUT_WRITE_DEPTH; clear - LO; lia | exact GLO
        | split; [exact GOT | exact GUARD] | exact MI1
        | clear - LFI BSL Hk; lia | cbn in RA0; clear - RA0; lia | clear - LFI BS Hk; lia
        | right; rewrite ESP; clear - LFI Hk SEPS1 SEPS2; split; lia
        | intros E; rewrite E in *; unfold zlength in *; cbn [length Z.of_nat] in *; lia ]. }
    cbv beta. intros [] st2 ms2 PO2.
    (nelim PO2 23%nat; intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 -> MU2 WM2 MI2 ST2 FC2 SSP2 ->).
    unfold STDOUT_WRITE_DEPTH in MU2.
    rewrite ESP in MU2, ST2. rewrite ESO1 in FC2 |- *.
    apply implM_upd. cbv beta. rewrite GS. unfold st1. rewrite !SS. cbn [so_active so_buf so_lbf_nl so_first so_after].
    assert (FR2 : rw_cells psegs m2 (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (rw_cells_transport psegs _ m1 m2); [exact FR1 | exact MU2 | exact WM2 | cbn; clear - LO GLO RSP; lia]. }
    assert (BUF2 : rw_cells psegs m2 RSTDOUT_BUF [CB 1024 bufbytes]).
    { eapply (rw_cells_transport psegs _ m1 m2); [exact BUF0 | exact MU2 | exact WM2 | cbn; clear - GLO LO; lia]. }
    assert (SRC2 : bytes_at psegs m2 S (zb bs)).
    { eapply (bytes_at_transport psegs _ m1 m2); [exact SRC | exact MU2 | cbn; rewrite LSB; clear - SEPS1 SEPS2 GLO LO; lia]. }
    clear FR1 BUF0 SRC SRCa BUFa BUFb BUFB FC GOT GUARD.
    unfold stdout_cells, file_cells, wfn_of, lbf_of in FC2. cbn [so_active so_buf so_lbf_nl so_first so_after zlength length Z.of_nat] in FC2.
    rewrite Z.add_0_r, LBF in FC2.
    rewrite (ret_pc_even 95804) by (cbn; lia).
    step. if_cases Hn; zify_cond Hn. 1:{ exfalso. clear - Hn. lia. }
    step. step. step.
    rewrite ?zbv_sub_wrap. rewrite ?(unsigned_lit k) by (clear - Hk BSL; lia).
    try rewrite (Z.add_opp_r (S + Z.of_nat (length bs)) k).
    set (S2 := (S + Z.of_nat (length bs) - k) mod 2^64).
    replace (Z_to_bv 64 (S + Z.of_nat (length bs) - k) : word) with (Z_to_bv 64 S2 : word) by (subst S2; apply ZBridge.Z_to_bv_mod64).
    assert (HS2 : 0 <= S2 < 2^64) by (subst S2; apply Z.mod_pos_bound; reflexivity).
    assert (HS2c : S2 = S + Z.of_nat (length bs) - k \/ (S2 = 0 /\ k = 0 /\ S + Z.of_nat (length bs) = 2^64)).
    { subst S2. cbn in RA0. destruct (Z.eq_dec (S + Z.of_nat (length bs) - k) (2^64)) as [E|E].
      - right. rewrite E. rewrite Z_mod_same_full. clear - E Hk BS RA0. lia.
      - left. rewrite Z.mod_small; [clear; lia|]. clear - BS Hk E RA0. lia. }
    assert (SRCk : bytes_at psegs m2 S2 (zb (skipn (Z.to_nat i) bs))).
    { destruct (Z.eq_dec k 0) as [K0|K0].
      - replace (skipn (Z.to_nat i) bs) with (@nil Z) by (symmetry; apply skipn_all2; clear - Hik K0 IR; lia).
        apply bytes_at_nil. clear - HS2; lia.
      - destruct HS2c as [E|[_ [E _]]]; [| exfalso; exact (K0 E)]. rewrite E.
        pose proof SRC2 as X. rewrite <- (firstn_skipn (Z.to_nat i) bs), zb_app in X.
        apply (proj1 (bytes_at_app _ _ _ _ _)) in X. destruct X as [_ X]. rewrite zb_length, length_firstn in X.
        replace (S + Z.of_nat (length bs) - k) with (S + Z.of_nat (Nat.min (Z.to_nat i) (length bs))) by (clear - Hik Hk IR; lia). exact X. }
    eapply evt_mono.
    { eapply fwx_tail with (lo := lo) (cap := 1024%nat) (src := zb (skipn (Z.to_nat i) bs)) (m0 := m2) (S := S2);
        [ exact FR2 | exact FC2 | exact BUF2
        | rewrite zb_length, length_skipn; clear - CMP' LZ; lia
        | exact SRCk
        | rewrite zb_length, length_skipn; clear - Hik Hk IR; lia
        | exact ST2
        | clear - LO GLO; lia | exact SPHI | apply munch_refl | apply wmono_refl | exact MI2
        | try (cbn in RA0; clear - RA0 HS2 HS2c LFI Hik Hk IR LSB CMP' BUFL LZ LS SEPF SEPB SEPS1 SEPS2 SEPS3 BS GLO LO SPHI; lia) .. ]. }
    cbv beta. intros ms' PO.
    (nelim PO 23%nat; intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m3 -> MU3 WM3 MI3 ST3 FC3 DST3 SRC3).
    unfold out_post, SR. nexists 16%nat.
    split. { reflexivity. }
    split. { apply (munch_trans _ m m1 m3).
             - eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; lia.
             - apply (munch_trans _ m1 m2 m3).
               + eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia.
               + eapply munch_weaken; [| exact MU3]. unfold sub_fp; cbn [outside]; intros; lia. }
    split. { eapply wmono_trans; [exact WM1 | eapply wmono_trans; [exact WM2 | exact WM3]]. }
    split; [exact MI3|]. split; [exact ST3|].
    assert (SRC3f : bytes_at psegs m3 S (zb bs)).
    { eapply (bytes_at_transport psegs _ m2 m3); [exact SRC2 | exact MU3 | cbn; rewrite LSB; clear - SEPS1 SEPS2 SEPS3 GLO LO Hk CMP'; lia]. }
    destruct SSP2 as [GOT2 GUARD2]. change psegs with psegs in GOT2, GUARD2. unfold got_ssp, ssp_guard in GOT2, GUARD2.
    assert (GOT3 : rw_cells psegs m3 140520 [C8 (Z_to_bv 64 342776)]).
    { eapply (rw_cells_transport psegs _ m2 m3); [exact GOT2 | exact MU3 | exact WM3 | cbn; clear - GLO LO Hk; lia]. }
    assert (GUARD3 : rw_cells psegs m3 342776 [C8 canary]).
    { eapply (rw_cells_transport psegs _ m2 m3); [exact GUARD2 | exact MU3 | exact WM3 | cbn; clear - GLO LO Hk; lia]. }
    split.
    { unfold SINK_stdout. rewrite GS. cbn [so_active so_buf so_lbf_nl so_first app]. split; [reflexivity|].
      exists flags, mode, tail, (zb (skipn (Z.to_nat i) bs) ++ skipn (length (zb (skipn (Z.to_nat i) bs))) bufbytes).
      split. { unfold zlength, file_cells. rewrite length_skipn, LBF.
               replace (343904 + Z.of_nat (length bs - Z.to_nat i)) with (343904 + k) by (clear - Hik Hk IR; lia). exact FC3. }
      split; [exact FL104|].
      split.
      { assert (J : rw_cells psegs m3 RSTDOUT_BUF ([] ++ [CB (length (zb (skipn (Z.to_nat i) bs))) (zb (skipn (Z.to_nat i) bs)); CB (1024 - length (zb (skipn (Z.to_nat i) bs)))%nat (skipn (length (zb (skipn (Z.to_nat i) bs))) bufbytes)] ++ [])) by exact DST3.
        apply rw_cells_merge in J. cbn [cells_size cells_bytes csize cbytes app Nat.add] in J. rewrite app_nil_r in J.
        replace (length (zb (skipn (Z.to_nat i) bs)) + (1024 - length (zb (skipn (Z.to_nat i) bs)) + 0))%nat with 1024%nat in J
          by (rewrite zb_length, length_skipn; clear - Hik Hk IR CMP' LZ; lia).
        exact J. }
      split. { rewrite <- (zb_length (skipn (Z.to_nat i) bs)), firstn_app, Nat.sub_diag, firstn_O, app_nil_r, firstn_all. reflexivity. }
      unfold zlength. rewrite length_skipn. clear - CMP' LZ Hik IR Hk; lia. }
    split; [split; [exact GOT3 | exact GUARD3] | exact SRC3f].
Qed.
End SO_fwritex_stdout.

(* [comment removed for export] *)
Module SO_stdio_exit.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MonadX.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_syscalls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_stdout_write.SO_stdio_write OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_stdout_write SO_fwritex_stdout.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.SO_piface.   (* [comment removed for export] *)

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
Local Ltac tslia ::= first [ exact I | gonly_lia | gonly_refute; fail 1 | tlia | split; [ tlia | exact I ] ].
(* [comment removed for export] *)

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma bv_eqb_refl : forall {n} (x : bv n), bv_eqb x x = true.
Proof. intros n x. unfold bv_eqb. apply Z.eqb_refl. Qed.

Ltac if_refl :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if bv_eqb ?x ?x then _ else _) _ _ _ _) => rewrite (bv_eqb_refl x); cbv iota
  end.

Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
  end.

(* [comment removed for export] *)
Lemma impl_post_evt' : forall {R} (t : itree node R) (Q Q' : R -> machine_state -> Prop) ms,
  impl psegs (at_node psegs) t Q ms -> (forall r ms', Q r ms' -> evt psegs (Q' r) ms') ->
  impl psegs (at_node psegs) t Q' ms.
Proof.
  induction t as [r|n k IH]; intros Q Q' ms H HQ; cbn in *.
  - eapply evt_cut; [exact H|]. intros ms' H'. apply HQ. exact H'.
  - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; eauto.
Qed.
Lemma implM_post_evt' : forall {St A} (c : M St A) s Q Q' ms,
  implM psegs c s Q ms -> (forall a s' ms', Q a s' ms' -> evt psegs (Q' a s') ms') ->
  implM psegs c s Q' ms.
Proof.
  intros St A c s Q Q' ms H HQ. unfold implM in *. eapply impl_post_evt'; [exact H|].
  intros [|[a s']] ms' H'; cbn in *; [apply evt_done; exact I| apply HQ; exact H'].
Qed.

Section StdioExit.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis get_set : forall s so, get_so (set_so so s) = so.
  Hypothesis set_set : forall s so so', set_so so' (set_so so s) = set_so so' s.
  Hypothesis set_get : forall s, set_so (get_so s) s = s.

  Theorem stdio_exit_proof : stdio_exit_spec_stmt get_so set_so.
  Proof.
    unfold stdio_exit_spec_stmt. intros until tm1. intros ST LIBC OFL SIN SOUT SERR SOF SEF GOT GUARD MI -> LO GLO.
    destruct SOF as (flags & mode & tail & bufbytes & FC & FL72 & BUF & BUFP & BUFL & INACT).
    destruct SEF as (eflags & emode & ee & ewend & etail & EFC).
    change psegs with psegs in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    remember (get_so s) as so eqn:ESO.
    pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp); (RSTDOUT, 0x23718); (RSTDOUT_BUF, 0x54360)]%Z m) as MU.
    pose proof (wmono_refl psegs m) as WM.
    assert (FL64 : Z.land (bv_unsigned flags) 64 = 0).
    { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
      destruct (Z.eq_dec i 6) as [->|NE].
      - pose proof (f_equal (fun z => Z.testbit z 6) FL72) as T. cbn beta in T. rewrite Z.land_spec, Z.bits_0 in T.
        change (Z.testbit 64 6) with true in T |- *. change (Z.testbit 72 6) with true in T. exact T.
      - change 64 with (2^6). rewrite Z.pow2_bits_eqb by lia.
        destruct (Z.eqb_spec 6 i); [lia|]. apply Bool.andb_false_r. }
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; clear - RSP LO GLO; lia).
    assert (LTB : length (to_bytes (so_buf so)) = length (so_buf so)) by (unfold to_bytes; apply length_map).
    unfold file_cells in FC, EFC.
    unfold implM, stdout_exit_flush. apply (implM_rdso psegs get_so). rewrite <- ESO.
    eapply (implM_evt psegs). 2:{ intros ms' H; exact H. } cbv beta.
    carve_frame 16%nat ST.
    do 4 step.
    (* [comment removed for export] *)
    carve_frame 16%nat ST.
    step. step. fix_lit_store. do 5 step.
    do 3 step. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true.
    step.
    do 5 step.
    release_frame FR0 ST (bv_unsigned sp + -16).
    (* [comment removed for export] *)
    step. step. if_false.
    step. step. step. if_true.
    (* [comment removed for export] *)
    step. step. step. if_false.
    step. step. if_lit.
    step. step.
    destruct (0 <? zlength (so_buf so)) eqn:CF.
    - (* [comment removed for export] *)
      pose proof (proj1 (Z.ltb_lt _ _) CF) as CF'.
      assert (ACT : so_active so = true).
      { destruct (so_active so) eqn:E; [reflexivity|]. exfalso. rewrite (INACT eq_refl) in CF'. unfold zlength in CF'. cbn in CF'. clear - CF'. lia. }
      rewrite ACT in FC |- *.
      step. if_cases Hq; zify_cond Hq. 1:{ exfalso. unfold zlength in *. clear - Hq CF'. lia. }
      do 4 step. step.
      rewrite (ret_pc_even _) by (destruct (so_first so); cbn; lia).
      replace (Z_to_bv 64 (if so_first so then 97288 else 96880) : word) with (Z_to_bv 64 (wfn_of (get_so s)) : word)
        by (rewrite <- ESO; reflexivity).
      apply evt_done.
      eapply implM_post_evt'.
      { eapply (stdout_writefn_spec get_so set_so get_set set_set) with (lo := lo) (S := 0) (s := []) (flags := flags) (mode := mode) (tail := tail) (canary := guard);
          [ rewrite <- ESO; exact ACT
          | unfold stdout_cells, wfn_of, lbf_of, file_cells; rewrite <- ESO; exact FC
          | exact FL64
          | rewrite <- ESO; eapply CB_prefix_bytes_at; [exact BUF| rewrite LTB; exact BUFP]
          | rewrite <- ESO; exact BUFL
          | apply bytes_at_nil; clear; lia
          | reflexivity | reflexivity | reflexivity
          | rewrite ESP; exact ST | rewrite ESP; unfold STDOUT_WRITE_DEPTH; clear - LO; lia | exact GLO
          | split; [exact GOT | exact GUARD] | exact MI
          | unfold zlength; cbn; clear; lia | clear; lia | unfold zlength; cbn; clear; lia
          | left; reflexivity
          | intros _; unfold TASK_SIZE; clear; lia ]. }
      cbv beta. intros [] st2 ms2 PO2.
      destruct PO2 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->).
      rewrite ESP in MU2, ST2. unfold STDOUT_WRITE_DEPTH in MU2. rewrite <- ESO in FC2 |- *.
      rewrite (ret_pc_even 96328) by (cbn; lia).
      transport_after_call psegs m1 m2 MU2 WM2.
      unfold stdout_cells, file_cells in FC2.
      (* [comment removed for export] *)
      step. step. step. if_lit.
      (* [comment removed for export] *)
      step. step. step. if_lit.
      step. step. if_lit.
      step. step. step. if_refl.
      step. step. step. if_lit.
      (* [comment removed for export] *)
      step. step. step. step.
      release_frame FR ST2 (bv_unsigned sp).
      apply evt_done. unfold stdio_exit_post.
      do 15 eexists. exists (so_after so). eexists.
      split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [exact ST2|].
      split; [reflexivity|].
      split.
      { unfold stdout_file. exists flags, mode, tail, bufbytes.
        unfold stdout_cells, wfn_of, lbf_of in FC2 |- *. cbn [so_active so_buf so_first so_lbf_nl so_after] in FC2 |- *.
        split; [exact FC2|]. split; [exact FL72|]. split; [exact BUF|]. split; [reflexivity|].
        split; [unfold zlength; cbn; clear; lia|]. intros X; discriminate X. }
      split; [reflexivity|].
      split; [exists eflags, emode, ee, ewend, etail; exact EFC|].
      destruct SSP2 as [GOT2 GUARD2]. change psegs with psegs in GOT2, GUARD2. split; [exact GOT2 | exact GUARD2].
    - (* [comment removed for export] *)
      pose proof (proj1 (Z.ltb_ge _ _) CF) as CF'.
      assert (E0 : so_buf so = []).
      { destruct (so_buf so); [reflexivity|]. exfalso. unfold zlength in CF'. cbn [length] in CF'. clear - CF'. lia. }
      rewrite E0 in *. unfold zlength. cbn [length Z.of_nat]. rewrite Z.add_0_r.
      unfold zlength in FC. cbn [length Z.of_nat] in FC. rewrite Z.add_0_r in FC.
      step. if_refl.
      step. step. step. if_lit.
      (* [comment removed for export] *)
      step. step. step. if_lit.
      step. step. if_lit.
      step. step. step. if_refl.
      step. step. step. if_lit.
      step. step. step. step.
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. apply evt_done. unfold stdio_exit_post.
      do 15 eexists. exists so. eexists.
      split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
      split; [rewrite ESO, set_get; reflexivity|].
      split.
      { unfold stdout_file. exists flags, mode, tail, bufbytes. rewrite E0. unfold zlength. cbn [length Z.of_nat]. rewrite Z.add_0_r.
        split; [exact FC|]. split; [exact FL72|]. split; [exact BUF|]. split; [reflexivity|].
        split; [clear; lia|]. intros _; reflexivity. }
      split; [exact E0|].
      split; [exists eflags, emode, ee, ewend, etail; exact EFC|].
      split; [exact GOT | exact GUARD].
  Qed.
End StdioExit.

(* [comment removed for export] *)
End SO_stdio_exit.

(* [comment removed for export] *)
From Stdlib Require NArith.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require RelSpec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Exec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require RegsEquiv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NodesSound.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require RzNodesImpl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Driver.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_rz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeSpec.
Module SO_exit.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RelSpec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RegsEquiv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NodesSound OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RzNodesImpl.RzNodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RzNodesImpl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Driver.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.Startup_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_printf_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.Stdio_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.SO_piface.   (* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_rz SO_stdio_exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.SO_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
      (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).
Local Notation rzt := (SO_rz.rzt psegs).
Local Notation z64 := (Z_to_bv 64 0).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section StdoutModel.
  Let get_so : stdout_st -> stdout_st := fun s => s.
  Let set_so : stdout_st -> stdout_st -> stdout_st := fun so _ => so.

  (* [comment removed for export] *)

  Lemma rzt_rd_so : forall st mo (R : stdout_st * stdout_st -> Prop), R (st, st) -> rzt (rd_so get_so st) mo [] R.
  Proof.
    intros st mo R HR. unfold rd_so. eapply (rzt_mbind_nil_l psegs _ _ _ _ _ (fun r => r = (st, st))); [apply rzt_mget; reflexivity|].
    intros a s' E. injection E as -> ->. apply rzt_mret. exact HR.
  Qed.

  Lemma rzt_upd_so : forall f st mo (R : unit * stdout_st -> Prop), R (tt, f st) -> rzt (upd_so get_so set_so f st) mo [] R.
  Proof. intros f st mo R HR. unfold upd_so. apply rzt_mupd. exact HR. Qed.

  Lemma rzt_stdout_stdio_write : forall s st mo,
    chan_ok mo 1 -> zlength (so_buf st) + zlength s <= 67108864 ->
    rzt (stdout_stdio_write get_so set_so s st) mo (map (WriteEv (Z_to_bv 64 1)) (to_bytes (so_buf st ++ s)))
        (fun r => snd r = mkStdout true [] (so_lbf_nl st) (so_first st)).
  Proof.
    intros s st mo CH B. unfold stdout_stdio_write.
    eapply (rzt_mbind_nil_l psegs _ _ _ _ _ (fun r => r = (st, st))); [apply rzt_rd_so; reflexivity|]. intros so s' E. injection E as -> ->.
    eapply rzt_mbind_nil_r; [apply (rzt_stdio_writev psegs st mo 1 (so_buf st) s CH); exact B|].
    intros [] s' E. cbn [snd] in E. subst s'. apply rzt_upd_so. reflexivity.
  Qed.

  Lemma rzt_stdout_writefn : forall s st mo,
    chan_ok mo 1 -> zlength (so_buf st) + zlength s <= 67108864 ->
    rzt (stdout_writefn get_so set_so s st) mo (map (WriteEv (Z_to_bv 64 1)) (to_bytes (so_buf st ++ s)))
        (fun r => snd r = mkStdout true [] (if so_first st then false else so_lbf_nl st) false).
  Proof.
    intros s st mo CH B. unfold stdout_writefn.
    eapply (rzt_mbind_nil_l psegs _ _ _ _ _ (fun r => r = (st, st))); [apply rzt_rd_so; reflexivity|]. intros so s' E. injection E as -> ->.
    destruct st as [act buf lbf first]. cbn [so_first so_buf so_lbf_nl] in *. destruct first.
    - eapply (rzt_mbind_nil_l psegs _ _ _ _ _ (fun r => snd r = mkStdout act buf false false)).
      + eapply (rzt_mbind_nil_l psegs _ _ _ _ _ (fun r => r = (tt, mkStdout act buf lbf false))); [apply rzt_upd_so; reflexivity|].
        intros [] s1 E. injection E as ->.
        eapply (rzt_mbind_nil_l psegs _ _ _ _ _ (fun r => (exists err, fst r = SErr err) /\ snd r = mkStdout act buf lbf false));
          [eapply (rzt_ioctl psegs); [exact CH| discriminate|]; intros err; split; [exists err; reflexivity| reflexivity] |].
        intros r s1 [[err E1] E2]. cbn [fst snd] in E1, E2. subst r s1. apply rzt_upd_so. reflexivity.
      + intros [] s1 E. cbn [snd] in E. subst s1.
        eapply rzt_mono; [apply rzt_stdout_stdio_write; [exact CH| cbn [so_buf]; exact B]|]. intros [[] s2] E2. exact E2.
    - eapply (rzt_mbind_nil_l psegs _ _ _ _ _ (fun r => r = (tt, mkStdout act buf lbf false))); [apply rzt_mret; reflexivity|].
      intros [] s1 E. injection E as ->.
      eapply rzt_mono; [apply rzt_stdout_stdio_write; [exact CH| cbn [so_buf]; exact B]|]. intros [[] s2] E2. exact E2.
  Qed.

  Lemma rzt_stdout_exit_flush : forall st mo,
    chan_ok mo 1 -> zlength (so_buf st) <= 67108864 ->
    rzt (stdout_exit_flush get_so set_so st) mo (map (WriteEv (Z_to_bv 64 1)) (to_bytes (so_buf st))) (fun _ => True).
  Proof.
    intros st mo CH B. unfold stdout_exit_flush.
    eapply (rzt_mbind_nil_l psegs _ _ _ _ _ (fun r => r = (st, st))); [apply rzt_rd_so; reflexivity|]. intros so s' E. injection E as -> ->.
    destruct (Z.ltb_spec 0 (zlength (so_buf st))) as [P|N].
    - rewrite <- (app_nil_r (so_buf st)) at 1. eapply rzt_mono; [apply rzt_stdout_writefn; [exact CH| unfold zlength in *; cbn [length]; lia]|]. intros; exact I.
    - replace (so_buf st) with (@nil Z) by (symmetry; apply length_zero_iff_nil; unfold zlength in N; lia). cbn [to_bytes map]. apply rzt_mret. exact I.
  Qed.
End StdoutModel.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section ExitImpl.
  Let get_so : stdout_st -> stdout_st := fun s => s.
  Let set_so : stdout_st -> stdout_st -> stdout_st := fun so _ => so.
  Local Open Scope bv_scope.

  Lemma exit_spec_so : forall (s : stdout_st) (Q : Empty_set -> stdout_st -> machine_state -> Prop)
      ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (code t : Z) (td0 td1 td2 td3 guard : word)
      (cdt thr sec : byte) (tm1 : word) (ph : bool),
    stk psegs m lo (bv_unsigned sp) ->
    rw_cells psegs m RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)] ->
    rw_cells psegs m 0x53af0 [C4 z64] ->
    rw_cells psegs m 0x224f0 [C8 (Z_to_bv 64 0x223f8); C8 (Z_to_bv 64 0x223f0)] ->
    rw_cells psegs m 0x223f0 [C8 (Z_to_bv 64 0x120bc)] ->
    rw_cells psegs m 0x23778 [C1 (Z_to_bv 8 0)] ->
    rw_cells psegs m 0x22498 [C8 (Z_to_bv 64 0x14e98); C8 z64] ->
    rw_cells psegs m 0x23500 [C8 (Z_to_bv 64 0x23500)] ->
    rw_cells psegs m 0x33784 [C1 (Z_to_bv 8 0)] ->
    ATEX ph m ->
    rw_cells psegs m 0x53b18 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
    rw_cells psegs m 0x53f48 [C8 z64] -> rw_cells psegs m 0x53f38 [C8 z64] ->
    rw_cells psegs m 0x23718 [C8 (Z_to_bv 64 RSTDOUT)] -> rw_cells psegs m 0x23628 [C8 (Z_to_bv 64 RSTDERR)] ->
    stdout_file m (get_so s) -> stderr_file m ->
    rw_cells psegs m 0x224e8 [C8 (Z_to_bv 64 0x53af8)] -> rw_cells psegs m 0x53af8 [C8 guard] ->
    mem_inv psegs m ->
    tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
    (0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 176)%Z -> (0x55000 <= lo)%Z ->
    implM psegs (Driver.exit_model (io_S get_so set_so) code) s Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x14fb4) fc None m (seg_rom psegs)).
  Proof.
    intros until ph. intros ST TDa EXL GF FA FIN GCX DSO INCB ATX LCH OFL SIN SOU SEU SOF SEF GG GU MI -> -> Ht LO LOLO.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    destruct SOF as (flg & mode & tail & bufb & SOF1 & SOF2 & SOF3 & SOF4 & SOF5 & SOF6).
    destruct SEF as (flg' & mode' & ee & wend' & tail' & SEF1).
    unfold file_cells in SOF1, SEF1.
    unfold Driver.exit_model.
    eapply (implM_bind psegs _ _ s
              (fun _ _ ms' => exists sp' gp' tp' x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m',
                 ms' = MS (mkR (Z_to_bv 64 0x15020) sp' gp' tp' x5 x6 x7 (Z_to_bv 64 code) x9 x10 x11 x12 x13 x14 x15 x16 x17
                               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                          F (Z_to_bv 64 0x15020) fc None m' (seg_rom psegs))).
    - change (io_exit (io_S get_so set_so)) with (stdout_exit_flush get_so set_so).
      unfold implM. iprefix.
      call rexit_prefix_spec; [exact ST | exact TDa | exact EXL | exact GF | exact FA | exact FIN | exact GCX | exact DSO | exact LCH | exact INCB | exact ATX | exact MI
                              | reflexivity | reflexivity | lia | lia | lia | ].
      name_sp sp (-16)%Z.
      pose proof (stdio_exit_proof get_so set_so (fun _ _ => eq_refl) (fun _ _ _ => eq_refl) (fun _ => eq_refl)) as SE.
      unfold stdio_exit_spec_stmt, implM in SE.
      apply evt_done. eapply impl_epost_mono; [eapply SE|].
      all: lazymatch goal with
           | |- forall _, _ =>
               intros [[] s'] ms' PO; cbn [fst snd] in PO; unfold stdio_exit_post in PO;
               destruct_exs PO; destruct PO as (E & PO); subst ms'; cbn [fst snd];
               replace (ret_pc (Z_to_bv 64 0x15020)) with (Z_to_bv 64 0x15020) by (symmetry; apply ret_pc_even; [lia|reflexivity]);
               repeat eexists; cbv delta [mkR]; reflexivity
           | |- stdout_file _ _ => exists flg, mode, tail, bufb; exact (conj SOF1 (conj SOF2 (conj SOF3 (conj SOF4 (conj SOF5 SOF6)))))
           | |- stderr_file _ => exists flg', mode', ee, wend', tail'; exact SEF1
           | |- _ => unname_sp; first [ hyp_by_addr | reflexivity | lia ]
           end.
    - clear SOF1 SOF2 SOF3 SOF4 SOF5 SOF6 SEF1.
      intros [] s' ms' PO. destruct_exs PO. subst ms'.
      apply implM_sys. do 4 lstep. step_ecall.
      split; [ at_node_red; split; [right; reflexivity | reflexivity] | intros rsp a H; cbn in H; discriminate H].
  Time Qed.
End ExitImpl.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rz_at_exit : forall ms mo code,
  at_node psegs (NExit code) ms -> MOK mo -> 0 <= code < 256 ->
  realizes psegs (mkCfg ms mo) (t_exit (Z_to_bv 64 code) (m_fs mo)).
Proof.
  intros ms mo code Hat [Hh _] Hc. cbn [at_node] in Hat. destruct Hat as [Hsvc H10].
  rewrite <- (bv_and_255_small code Hc), <- H10. change (areg ms 10) with (ms_gpr ms 0).
  destruct Hsvc as [Hs|Hs]; (eapply ShapeAlg.rz_exit; [exact Hh | exact Hs | ]); [apply is_exit_no_93 | apply is_exit_no_94].
Qed.

Theorem so_exit_proof : so_exit_stmt.
Proof.
  unfold so_exit_stmt. intros until ph.
  intros HM CH ST TDa EXL GF FA FIN GCX DSO INCB ATX LCH OFL SIN SOU SEU SOF BND SEF GG GU MI Htp Ha0 Hc Ht LO GLO.
  unfold EXIT_DEPTH, GLOBALS_TOP in *.
  pose proof (exit_spec_so so (fun _ _ _ => False) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m lo code t td0 td1 td2 td3 guard cdt thr sec tm1 ph
                ST TDa EXL GF FA FIN GCX DSO INCB ATX LCH OFL SIN SOU SEU SOF SEF GG GU MI Htp Ha0 Ht LO GLO) as H.
  unfold Driver.exit_model, implM, mbind in H. cbn [io_exit io_S] in H. apply impl_bind_inv in H.
  pose proof (rzt_stdout_exit_flush so mo CH ltac:(lia)) as RZ.
  unfold W. unfold t_exit.
  refine (RZ (fun a ms' => ITree.impl psegs (at_node psegs) (msys (NExit code) dec_exit (snd a)) (epost (fun (_ : Empty_set * stdout_st) (_ : machine_state) => False)) ms') _ _ HM _ (t_emit_has_nil _ _) _).
  - eapply impl_mono; [exact H|]. intros [|a] ms'; cbn [epost]; [intros _; exact I| intros X; exact X].
  - intros a ms' Hi _. unfold msys in Hi. fold (t_exit (Z_to_bv 64 code) (m_fs mo)).
    eapply (rz_impl_enode psegs); [exact HM | exact Hi |]. intros ms1 Hat _. apply rz_at_exit; [exact Hat | exact HM | exact Hc].
Qed.
End SO_exit.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import RelSpec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NodesSound.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require RzNodesImpl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RzNodesImpl.RzNodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import RzNodesImpl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim Monad SoftFloat FmtFp Stdio Driver.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit.F_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_memcpy F_fwritex F_pad F_fmt_fp_lib F_fmt_fp F_pop_arg Exit Printf_model Printf_mlib F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_vsnprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_vsnprintf.F_printf_core.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_vsnprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_vsnprintf.F_printf_snsink.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_vsnprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_vsnprintf.F_vfprintf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_vsnprintf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import Printf_pieces.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import PImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SO_model.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_fprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.SO_piface.   (* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SO_rz.
Import SO_fwritex_stdout.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_fprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.SO_vfprintf_stdout.
Import SO_exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_fprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.SO_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg ShapeSpec.      (* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import StoreCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac arith_goal := lazymatch goal with
  | |- (_ <= _)%Z => idtac | |- (_ < _)%Z => idtac | |- (_ >= _)%Z => idtac | |- (_ > _)%Z => idtac
  | |- @eq Z _ _ => idtac | |- @eq nat _ _ => idtac | |- (_ <= _)%nat => idtac | |- (_ < _)%nat => idtac
  | |- ~ _ => idtac | |- _ /\ _ => idtac | |- _ \/ _ => idtac | |- False => idtac | |- True => idtac
  end.   (* [comment removed for export] *)
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac lia ::= lia3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.LiaClosure.
Local Ltac lia ::= lia4.
Local Ltac tlia ::= tlia4.
Local Ltac flia ::= first [ assumption | slim; lia ].   (* [comment removed for export] *)

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
Ltac ienter := lazymatch goal with |- Monad.implM _ _ _ _ _ => unfold Monad.implM; apply impl_from_evt | |- ITree.impl _ _ _ _ _ => apply impl_from_evt | _ => idtac end.
Ltac ileave := lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end;
               lazymatch goal with |- ITree.impl _ _ (?c ?s) (epost (fun p => ?Q (fst p) (snd p))) ?ms => change (Monad.implM psegs c s Q ms) | _ => idtac end.

Notation mem := (word -> option byte).
Local Notation rzt := (SO_rz.rzt psegs).

(* [comment removed for export] *)
Definition FMT_emitd : list Z := [37; 100; 10; 0].      (* [comment removed for export] *)
Definition A_FMT_emitd : Z := 0x102d9.
Definition EMITD_PIECES : list (list Z) := [[]; []; [48]; []; [10]].

Lemma printf_pieces_emitd : printf_pieces FMT_emitd [PA_i 0] = Some (EMITD_PIECES, 2).
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Shell.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis GS : forall x so, get_so (set_so so x) = so.
  Hypothesis SS : forall x so so', set_so so' (set_so so x) = set_so so' x.

  Lemma emitd_gen :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word),
      stdout_file m (get_so st) ->
      bv_unsigned a1 mod 2^32 = 0 ->
      stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - EMITD_DEPTH) -> (GLOBALS_TOP <= lo) ->
      (bv_unsigned sp < 2^63) ->
      ssp_cells m canary -> mem_inv psegs m -> frm0 fc ->
      Monad.implM psegs (stdout_towrite get_so set_so ;;; outsk (stdout_fwritex get_so set_so) EMITD_PIECES (mret tt)) st
            (emit_printf_post get_so ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x125a4) fc None m (seg_rom psegs)).
  Proof using GS SS.
    intros until canary. intros SF HA1 ST LO GLO QHI SSP MI FRM.
    unfold EMITD_DEPTH, GLOBALS_TOP in *.
    pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. idtac. fold psegs in SSP1, SSP2.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU1.
    ienter.
    carve_frame 80%nat ST.
    do 15 zs.
    (* [comment removed for export] *)
    do 7 zs.
    apply (proj1 (rw_cells_app psegs _ _ [_;_;_] _)) in FR. destruct FR as [FR VAC]. cbn [cells_size csize Nat.add app] in VAC.
    replace (bv_unsigned sp + -80 + Z.of_nat 24)%Z with (bv_unsigned sp + -56)%Z in VAC by lia.
    pose proof (rw_cells_bytes_at' _ _ _ _ VAC) as VAA. cbn [cells_bytes cbytes] in VAA.
    change (le8 a1 ++ le8 a2 ++ le8 a3 ++ le8 a4 ++ le8 a5 ++ le8 a6 ++ le8 a7 ++ []) with (u64s [a1; a2; a3; a4; a5; a6; a7]) in VAA.
    ileave.
    pose proof (vfprintf_stdout_proof get_so set_so GS SS fwritex_stdout_proof) as VF. unfold vfprintf_stdout_stmt in VF. cbv zeta in VF.
    eapply implM_post_evt.
    { eapply VF with (A := A_FMT_emitd) (VA := bv_unsigned sp + -56) (fmt := FMT_emitd) (slots := [a1; a2; a3; a4; a5; a6; a7]) (args := [PA_i 0])
                     (r := 2) (lo := lo) (canary := canary);
        clear VF; rewrite ?unsigned_lit by lia; unfold VF_FRAME, VF_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength; cbn [length].
      all: try reflexivity. all: try (arith_goal; lia).
      - eapply stdout_file_stk; [exact SF | exact MU1 | exact WM | lia].
      - apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_emitd; lia | vm_compute; discriminate].
      - unfold FMT_emitd. forall_range.
      - exact VAA.
      - cbn [args_ok arg_ok]. split; [|exact I]. split; [lia|]. rewrite HA1. reflexivity.
      - exact ST.
      - split; [exact SSP1 | exact SSP2].
      - exact MI.
      - exact FRM.
      - unfold A_FMT_emitd, FMT_emitd. cbn [length]. lia.
      - unfold A_FMT_emitd, FMT_emitd. cbn [length]. lia. }
    cbv beta. intros [] st' ms' P. clear MU1.
    unfold vfprintf_stdout_post in P. rewrite !unsigned_lit in P by lia.
    destruct P as (y5 & y6 & y7 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SF3 & SSP3).
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call psegs mm m3 MUc WMc; clear MUc WMc; try clear MI end.
    fix_ret.
    zs. zs. zs.
    lazymatch goal with FR : rw_cells _ ?mm (bv_unsigned sp + -80)%Z ?hd, VAC : rw_cells _ ?mm (bv_unsigned sp + -56)%Z ?rest |- _ =>
      assert (FALL : rw_cells psegs mm (bv_unsigned sp + -80) (hd ++ rest));
      [ apply (proj2 (rw_cells_app psegs _ _ _ _)); split; [exact FR|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact VAC | lia]
      | clear FR VAC ] end.
    cbn [app] in FALL.
    release_frame FALL ST3 (bv_unsigned sp).
    apply evt_done. unfold emit_printf_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|].
    split; [exact ST3|]. split; [exact SF3|]. exact SSP3.
  Qed.
End Shell.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section StdoutModel.
  Let get_so : stdout_st -> stdout_st := fun s => s.
  Let set_so : stdout_st -> stdout_st -> stdout_st := fun so _ => so.
  Local Notation OUT := (stdout_fwritex get_so set_so).

  Lemma zlength_app' : forall {A} (a b : list A), zlength (a ++ b) = zlength a + zlength b.
  Proof. intros. unfold zlength. rewrite length_app. lia. Qed.

  Lemma rzt_stdout_towrite : forall st mo (R : unit * stdout_st -> Prop),
    R (tt, if so_active st then st else mkStdout true [] (so_lbf_nl st) (so_first st)) ->
    rzt (stdout_towrite get_so set_so st) mo [] R.
  Proof. intros st mo R HR. unfold stdout_towrite. apply rzt_upd_so. exact HR. Qed.

  (* [comment removed for export] *)
  Lemma rzt_fwritex_keep : forall s buf lbf first mo,
    zlength buf + zlength s <= STDOUT_BUFSIZ -> (lbf = false \/ after_last_nl s = 0) ->
    rzt (OUT s (mkStdout true buf lbf first)) mo [] (fun r => snd r = mkStdout true (buf ++ s) lbf first).
  Proof.
    intros s buf lbf first mo B NL. unfold stdout_fwritex.
    eapply (rzt_mbind_nil_l psegs _ _ _ _ _ (fun r => r = (tt, mkStdout true buf lbf first))); [apply rzt_stdout_towrite; reflexivity|].
    intros [] s1 E. injection E as ->.
    eapply (rzt_mbind_nil_l psegs _ _ _ _ _ (fun r => r = (mkStdout true buf lbf first, mkStdout true buf lbf first))); [apply rzt_rd_so; reflexivity|].
    intros so s1 E. injection E as -> ->. cbn [so_buf so_lbf_nl so_active so_first].
    destruct (Z.ltb_spec (STDOUT_BUFSIZ - zlength buf) (zlength s)) as [X|X]; [lia|].
    destruct lbf.
    - destruct NL as [NL|NL]; [discriminate|]. rewrite NL. cbn [Z.ltb Z.to_nat skipn].
      eapply (rzt_mbind_nil_l psegs _ _ _ _ _ (fun r => r = (tt, mkStdout true buf true first))); [apply rzt_mret; reflexivity|].
      intros [] s1 E. injection E as ->. apply rzt_upd_so. reflexivity.
    - apply rzt_upd_so. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma rzt_fwritex_flushline : forall s buf first mo,
    chan_ok mo 1 -> zlength buf + zlength s <= STDOUT_BUFSIZ -> after_last_nl s = zlength s -> 0 < zlength s ->
    rzt (OUT s (mkStdout true buf true first)) mo (map (WriteEv (Z_to_bv 64 1)) (to_bytes (buf ++ s)))
        (fun r => snd r = mkStdout true [] (if first then false else true) false).
  Proof.
    intros s buf first mo CH B NL POS. unfold stdout_fwritex.
    eapply (rzt_mbind_nil_l psegs _ _ _ _ _ (fun r => r = (tt, mkStdout true buf true first))); [apply rzt_stdout_towrite; reflexivity|].
    intros [] s1 E. injection E as ->.
    eapply (rzt_mbind_nil_l psegs _ _ _ _ _ (fun r => r = (mkStdout true buf true first, mkStdout true buf true first))); [apply rzt_rd_so; reflexivity|].
    intros so s1 E. injection E as -> ->. cbn [so_buf so_lbf_nl so_active so_first].
    destruct (Z.ltb_spec (STDOUT_BUFSIZ - zlength buf) (zlength s)) as [X|X]; [lia|].
    rewrite NL. rewrite (proj2 (Z.ltb_lt 0 (zlength s))) by exact POS.
    rewrite firstn_all2 by (unfold zlength; lia). rewrite skipn_all2 by (unfold zlength; lia).
    eapply rzt_mbind_nil_r.
    - eapply rzt_mono; [apply rzt_stdout_writefn; [exact CH| cbn [so_buf]; unfold STDOUT_BUFSIZ in B; lia]|]. intros r Hr; exact Hr.
    - intros [] s1 E. cbn [snd so_first] in E. subst s1. apply rzt_upd_so. cbn [snd so_active so_buf so_lbf_nl so_first]. reflexivity.
  Qed.

  Local Notation EMRUN := (stdout_towrite get_so set_so ;;; outsk OUT EMITD_PIECES (mret tt)).

  Ltac em_keep B :=
    eapply (rzt_mbind_nil_l psegs _ _ _ _ _ (fun r => snd r = B)); [ | intros [] ? E; cbn [snd] in E; subst ].

  (* [comment removed for export] *)
  Lemma rzt_emit_first : forall mo, chan_ok mo 1 ->
    rzt (EMRUN stdout_init) mo (W 1 emit_line) (fun r => snd r = emit_after_first).
  Proof.
    intros mo CH. unfold stdout_init, emit_after_first, W, emit_line. cbn [outsk].
    em_keep (mkStdout true [] true true); [apply rzt_stdout_towrite; reflexivity|].
    em_keep (mkStdout true ([] ++ []) true true); [apply rzt_fwritex_keep; [apply Z.leb_le; reflexivity| right; reflexivity]|]. cbn [app].
    em_keep (mkStdout true ([] ++ []) true true); [apply rzt_fwritex_keep; [apply Z.leb_le; reflexivity| right; reflexivity]|]. cbn [app].
    em_keep (mkStdout true ([] ++ [48]) true true); [apply rzt_fwritex_keep; [apply Z.leb_le; reflexivity| right; reflexivity]|]. cbn [app].
    em_keep (mkStdout true ([48] ++ []) true true); [apply rzt_fwritex_keep; [apply Z.leb_le; reflexivity| right; reflexivity]|]. cbn [app].
    eapply rzt_mbind_nil_r.
    - change [Z_to_bv 8 48; Z_to_bv 8 10] with (to_bytes ([48] ++ [10])).
      apply (rzt_fwritex_flushline [10] [48] true mo CH); [apply Z.leb_le; reflexivity| reflexivity| reflexivity].
    - intros [] s1 E. cbn [snd] in E. subst s1. apply rzt_mret. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma rzt_emit_again : forall mo buf, chan_ok mo 1 -> zlength buf + 2 <= STDOUT_BUFSIZ ->
    rzt (EMRUN (mkStdout true buf false false)) mo (W 1 []) (fun r => snd r = mkStdout true (buf ++ [48; 10]) false false).
  Proof.
    intros mo buf CH B. unfold W. cbn [outsk map].
    em_keep (mkStdout true buf false false); [apply rzt_stdout_towrite; reflexivity|].
    em_keep (mkStdout true (buf ++ []) false false); [apply rzt_fwritex_keep; [unfold zlength in *; cbn [length]; lia| left; reflexivity]|]. rewrite app_nil_r.
    em_keep (mkStdout true (buf ++ []) false false); [apply rzt_fwritex_keep; [unfold zlength in *; cbn [length]; lia| left; reflexivity]|]. rewrite app_nil_r.
    em_keep (mkStdout true (buf ++ [48]) false false); [apply rzt_fwritex_keep; [unfold zlength in *; cbn [length]; lia| left; reflexivity]|].
    em_keep (mkStdout true ((buf ++ [48]) ++ []) false false); [apply rzt_fwritex_keep; [rewrite zlength_app'; unfold zlength in *; cbn [length]; lia| left; reflexivity]|]. rewrite app_nil_r.
    em_keep (mkStdout true ((buf ++ [48]) ++ [10]) false false); [apply rzt_fwritex_keep; [rewrite zlength_app'; unfold zlength in *; cbn [length]; lia| left; reflexivity]|].
    apply rzt_mret. cbn [snd]. rewrite <- app_assoc. reflexivity.
  Qed.
End StdoutModel.

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem so_emit_first_proof : so_emit_first_stmt.
Proof.
  unfold so_emit_first_stmt. intros until K. intros HM CH SF HA1 ST LO GLO QHI SSP MI FRM HK HC.
  pose proof (emitd_gen (fun s : stdout_st => s) (fun so _ => so) (fun _ _ => eq_refl) (fun _ _ _ => eq_refl)
                ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m stdout_init lo canary SF HA1 ST LO GLO QHI SSP MI FRM) as H.
  unfold Monad.implM in H.
  pose proof (rzt_emit_first mo CH) as RZ.
  apply (RZ _ _ K HM H HK). intros [[] st'] ms' PO E. cbn [snd] in E. subst st'. cbn [fst snd] in PO. unfold emit_printf_post in PO.
  destruct PO as (x5 & x6 & x7 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & Ft & fc' & m' & -> & MU & WM & MI' & FRM' & FOK & ST' & SF' & SSP').
  eapply HC; eassumption.
Qed.

Theorem so_emit_again_proof : so_emit_again_stmt.
Proof.
  unfold so_emit_again_stmt. intros until K. intros HM CH SF B HF HA1 ST LO GLO QHI SSP MI FRM HK HC.
  pose proof (emitd_gen (fun s : stdout_st => s) (fun so _ => so) (fun _ _ => eq_refl) (fun _ _ _ => eq_refl)
                ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m (mkStdout true buf false false) lo canary SF HA1 ST LO GLO QHI SSP MI FRM) as H.
  unfold Monad.implM in H.
  pose proof (rzt_emit_again mo buf CH B) as RZ.
  apply (RZ _ _ K HM H HK). intros [[] st'] ms' PO E. cbn [snd] in E. subst st'. cbn [fst snd] in PO. unfold emit_printf_post in PO.
  destruct PO as (x5 & x6 & x7 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & Ft & fc' & m' & -> & MU & WM & MI' & FRM' & FOK & ST' & SF' & SSP').
  eapply HC; eassumption.
Qed.
