(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_infl_top_pure.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Zg_inflate_glue.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_ikit Z_updwin_pure Zg_updwin_pure Z_infl_defs Zg_infl_defs Zg_zlib_iface Z_inflate_glue.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState InflateArms Inflate HarnessSmall RefZApi RefInflateRel RefInflateSafeD RefInflateSafeTY RefInflateSafeTY2
  RefInflateEqS RefInflate_runA InflateCall InflateFrameIn ZApiInst ZTaintI RefUpdWin1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateEqB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma W0_PATG : forall X s zc,
  PATIq s -> bk_ok s -> ix_input X = arr_of_list (zc_input zc) -> zlength (zc_input zc) < 2^31 ->
  zc_avail_out zc = Z.of_nat (length (ix_rest0 X)) -> Z.of_nat (length (ix_rest0 X)) < 2^31 ->
  (is_window_blk s <> None <-> ix_hasw X = true) ->
  PATG X (W0 s zc).
Proof.
  intros X s zc (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & _) P9 EIN LIN EAO LR0 HW.
  assert (EM : is_mode (s_entry s) = (if is_mode s =? TYPE then TYPEDO else is_mode s)) by (destruct (s_entry_facts s) as (_&_&_&_&_&_&_&_&_&_&E&_); exact E).
  assert (EQ : forall A (f : inflate_state -> A), (forall x v, f (iset_mode x v) = f x) -> f (s_entry s) = f s).
  { intros A f Hf. unfold s_entry. destruct (is_mode s =? TYPE); [apply Hf| reflexivity]. }
  unfold PATG, W0, OBYT, ISR. cbn [w_s w_c w_r ir_put ir_out ir_left ic_input ic_outbuf icall_of_zcall].
  rewrite (EQ _ is_wrap), (EQ _ is_wbits), (EQ _ is_head), (EQ _ is_flags), (EQ _ is_window_blk), (EQ _ is_last), (EQ _ is_havedict), (EQ _ is_window) by reflexivity.
  rewrite EM.
  split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
  split. { destruct P4 as [F0|(F1 & HM)]; [left; exact F0| right]. split; [exact F1|]. split; [|split; reflexivity].
           destruct HM as [E|E]; rewrite E; [left| right]; reflexivity. }
  split. { destruct (Z.eqb_spec (is_mode s) TYPE) as [E|E]; [unfold TYPEDO, FLAGS, HCRC; lia| exact P5]. }
  split; [exact (proj1 HW)|]. split; [symmetry; exact EIN|]. split; [rewrite EIN, arr_len_of_list; exact LIN|].
  split; [unfold arr_make; rewrite arr_len_init; exact EAO|]. split; [exact LR0|].
  split; [split; assumption|].
  split.
  { split; [intros i Hi; lia|]. split; [exact P8|]. split; [lia|]. split; [unfold NOPUTb; apply andb_false_r| exact (proj2 HW)]. }
  unfold bk_ok in *. rewrite (EQ _ is_back) by reflexivity. rewrite EM.
  destruct (is_mode s =? TYPE); [| exact P9]. pose proof (bkmax_le (is_mode s)) as BM. unfold bkmax. cbn. lia.
Qed.

(* [comment removed for export] *)
Definition zi_stepG := OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P.Zg_inflate_glue.zi_stepG.
Definition sA_facts := OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P.Zg_inflate_glue.sA_facts.
Definition updw_core_wbytes := OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P.Zg_inflate_glue.updw_core_wbytes.
Definition updw_core_facts := OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P.Zg_inflate_glue.updw_core_facts.

(* [comment removed for export] *)
Lemma updw_core_back : forall s src e copy, is_back (updw_core s src e copy) = is_back s.
Proof. intros s src e copy. rewrite (updw_core_shape s src e copy). cbv zeta. unfold uw_set. destruct s; reflexivity. Qed.

Lemma PATIq_of_PATG : forall X s c r s_f, PATG X (mkW s c r) ->
  is_wrap s_f = is_wrap s -> is_wbits s_f = is_wbits s -> is_head s_f = is_head s -> is_flags s_f = is_flags s ->
  (is_mode s_f = is_mode s \/ (is_mode s_f = MEM /\ is_flags s = 0)) -> is_last s_f = is_last s -> is_havedict s_f = is_havedict s ->
  is_back s_f = is_back s ->
  (forall i, 0 <= i < arr_len (is_window s_f) -> 0 <= arr_get (is_window s_f) i < 256) -> PATIq s_f.
Proof.
  intros X s c r s_f (P1 & P2 & P3 & P4 & P5 & _ & _ & _ & _ & _ & [P11 P12] & _ & PBK) E1 E2 E3 E4 E5 E6 E7 EB HWB. cbn [w_s w_r] in *.
  unfold PATIq. rewrite E1, E2, E3, E4, E6, E7. split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
  split. { destruct P4 as [F0|(F1 & HM & _)]; [left; exact F0|]. destruct E5 as [E5|(_ & E5)]; [right; rewrite E5; split; assumption| left; exact E5]. }
  split. { destruct E5 as [E5|(E5 & _)]; rewrite E5; [exact P5| unfold MEM, FLAGS, HCRC; lia]. }
  split; [exact P11|]. split; [exact P12|]. split; [exact HWB|].
  (* [comment removed for export] *)
  unfold bk_ok in *. rewrite EB. destruct E5 as [E5|(E5 & _)]; rewrite E5; [exact PBK|].
  pose proof (bkmax_le (is_mode s)) as BM. unfold bkmax. cbn. lia.
Qed.
