(* WHY fr_CAP (lib/A/ReplyLScap.v): RiRestate's LS_exit_cap is false over the top's instance WITHOUT fr_CAP.
   proves no function (kind: counterexample).
   LS_exit_cap (a working branch 5a9b16eac9e, W_LLVMFuzzerTestOneInput_exit_x.v:196-198 /
   _exit.v:7785-7787) concludes gse_cap (lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) <= CAPOUT_MAX, which is
   at least lm_cap m (ReplyLS3o.v ou_rf_cap).  At LSx := fr_LS3cp B /\ fr_OUT OM /\ fr_ENT B and RINV := fr_RINV it is
   false: cex_* is a Theorem Labs lane's first-head witness (ReplyLS3.v sat3, ReplyLSI.v lsi_sat) at t = 0 with the entry's
   g_capout = 2 ^ 32 > CAPOUT_MAX: g_out is a live 2 ^ 32-byte block of the entry state (a secondary chunk), the entry's
   memory holds g_out / g_capout, so the entry's harness blocks fr_hblks are that block, and the model's lm_cap is
   2 ^ 32.  fr_LS3's bound holds (blocks_bytes of the entry 1 + 2 ^ 32, plus CALL_ROOM 2 ^ 33, <= LIVE_MAX 2 ^ 34),
   fr_OUT holds (XB counts the entry's g_out block), fr_ENT holds, and so does fr_RINV.  With fr_CAP (0 <= lm_cap m <=
   CAPOUT_MAX) LAST in the instance the rule holds (ReplyLScap.v LS_exit_cap_I). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract W_sites W_frame W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_drain.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_write.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_event.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
  W_LLVMFuzzerTestOneInput_head W_LLVMFuzzerTestOneInput_small W_LLVMFuzzerTestOneInput_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyRINV.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLSArms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  drain_b_c gestures_end_b_c gesture_end_c relay_remove_b_c RelayCap SlotReads SlotInv SlotDrain3Aux SlotPass2Aux
  relay_remove_b_aux send_line_b_c RelayRunT RelayRunF ListTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ACfn_cf CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
  ReplyLS3 ReplyLSDrainPre ReplyLSDrain3 ReplyLSRemove3 ReplyLSEvent3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS3Arms ReplyLSCntL ReplyLS3c ReplyLS3cArms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyTrPeak ReplyTrPeakC.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_exit.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS3o.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS3p ReplyLS3oRf ReplyLS3oGn ReplyLS3e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
  ReplyLS3cTopxGoneF ReplyLS3cTopxGoneH ReplyLS3cTopx ReplyLS3cTopxPost ReplyLS3cTopxPro
  ReplyLS3cTopxGone8.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyLS3eCap.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS3w ReplyCnt.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section cex.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

(* the entry's g_out block: a secondary chunk of 2 ^ 32 bytes (its address is the layout's secondary base, concrete) *)
Definition cex_kout : YG00.chunk := YG00.mkChunk (YG00.PSec 0 (2 ^ 40)) (2 ^ 32) YG00.CAllocated.
Definition cex_out : Z := sptr_addr B ls3_ly (YG00.ck_user cex_kout).
Definition cex_cap : Z := 2 ^ 32.
(* the entry state: the input block and g_out's block; the state after the first head adds the table and the buffer *)
Definition cex_S0 : astate := YG00.set_chunks [ls3_k0; cex_kout] YG00.init_state.
Definition cex_S : astate := YG00.set_chunks [ls3_k0; ls3_k1; ls3_k2; cex_kout] YG00.init_state.
(* the entry's memory: g_out and g_capout (fr_globals, W_rep.v:46) hold cex_out and 2 ^ 32, little-endian *)
Definition cex_mem : word -> option byte := fun w =>
  let a := bv_unsigned w in
  if (rg_out fr_RG <=? a) && (a <? rg_out fr_RG + 8) then
    Some (Z_to_bv 8 (le_byte cex_out 8 (Z.to_nat (a - rg_out fr_RG))))
  else if (rg_capout fr_RG <=? a) && (a <? rg_capout fr_RG + 8) then
    Some (Z_to_bv 8 (le_byte cex_cap 8 (Z.to_nat (a - rg_capout fr_RG))))
  else None.
Definition cex_cx : lfcx (rc := rc) :=
  LFCX ls3_ly cex_S0 ls3_W bvmap_empty cex_mem ls3_md (ls3_p B) 1 [Z_to_bv 8 7] 0.
(* the first head's model with g_out = (cex_out, 2 ^ 32) *)
Definition cex_m : lmod := ls_pro_m (ls3_q B) (ls3_G B) [] (CTL 3 0 0 0 0) [] cex_cap cex_out.


Lemma cex_LSI3 : forall OM, OUT_MAX4 <= OM ->
  fr_LS3cp B cex_cx 0 cex_m ls3_ly cex_S /\ fr_OUT OM cex_cx 0 cex_m ls3_ly cex_S /\ fr_ENT B cex_cx cex_m ls3_ly cex_S.
Proof.
  intros OM HOM.
  assert (EA : ablocks B ls3_ly cex_S = input_blks cex_cx ++ model_blks cex_m ++ []) by reflexivity.
  assert (E0 : ablocks B ls3_ly cex_S0 = input_blks cex_cx ++ [(cex_out, cex_cap)] ++ []) by reflexivity.
  assert (Hbb : blocks_bytes cex_S = 1 + ATABLE + APARTIAL + 2 ^ 32) by (vm_compute; reflexivity).
  assert (Hb0 : blocks_bytes cex_S0 = 1 + 2 ^ 32) by (vm_compute; reflexivity).
  assert (Hin : bsum (input_blks cex_cx) = 1) by reflexivity.
  assert (Hrest : bsum (@nil (Z * Z)) = 0) by reflexivity.
  assert (HS : c_S cex_cx = cex_S0) by reflexivity.
  assert (Hn : c_n cex_cx = 1) by reflexivity.
  assert (HC : ACfn_cf.CALL_ROOM = 8589934592) by reflexivity.
  assert (HL : LIVE_MAX = 17179869184) by reflexivity.
  assert (En : npend cex_m = 0) by reflexivity.
  assert (Ek : kk cex_cx cex_m = 0) by reflexivity.
  assert (Eo : nopen (lm_hs cex_m) = 1) by reflexivity.
  assert (Ep : PHI3 cex_m = ATABLE + APARTIAL + 2 ^ 32 + E_ENT + K0) by (vm_compute; reflexivity).
  refine (conj (conj (conj _ _) _) (conj _ _)).
  - exists [], (2 ^ 32). rewrite EA, HS, Hb0, Hn, Hin, Hrest, HC, HL, En, Ek, Eo, Ep.
    split; [apply Permutation_refl|].
    unfold W_OPEN, MB_K, MB_C, ATABLE, APARTIAL, E_ENT, K0.
    refine (conj _ (conj _ (conj _ (conj eq_refl (conj _ _))))); lia.
  - unfold fr_CNT. rewrite EA, !cnt_sec_app, cnt_sec_nil.
    split; [unfold SEC0; lia | split; [| rewrite En; lia]].
    intros c. rewrite !cnt_cls_app, cnt_cls_nil. unfold CLS0. lia.
  - intros c. assert (E1 : pt_kc c cex_m = 0) by reflexivity. assert (E2 : pt_mass cex_m = 0) by reflexivity.
    rewrite E1, E2. lia.
  - assert (EM : bsum (model_blks cex_m) = ATABLE + APARTIAL + 2 ^ 32) by (vm_compute; reflexivity).
    assert (EC : lm_cap cex_m = 2 ^ 32) by reflexivity.
    assert (EMass : MASS cex_m = 0) by reflexivity.
    unfold fr_OUT, XB. rewrite HS, Hb0, Hbb, EM, EC, EMass. unfold OUT_MAX4 in HOM. unfold ATABLE, APARTIAL.
    repeat split; lia.
  - intros rest Hr. rewrite EA in Hr.
    pose proof (ent_rest_eq _ _ _ _ _ (Permutation_refl (input_blks cex_cx ++ model_blks cex_m ++ [])) Hr) as Hrr.
    change (ablocks B (c_ly cex_cx) (c_S cex_cx)) with (ablocks B ls3_ly cex_S0). rewrite E0.
    (* the entry's harness blocks: g_out's block, read from cex_mem (the table pointer reads 0 from the image) *)
    match goal with |- Permutation _ (_ ++ ?F ++ _) => replace F with [(cex_out, cex_cap)] by (vm_compute; reflexivity) end.
    apply Permutation_app_head, Permutation_app_head. exact Hrr.
Qed.

Lemma cex_RINV : fr_RINV cex_cx 0 cex_m.
Proof.
  unfold fr_RINV. refine (conj _ (conj _ (conj _ _))).
  - unfold fr_count. vm_compute. split; [discriminate | split; discriminate].
  - unfold fr_relay.
    refine (conj _ _); [reflexivity|].
    refine (conj _ _).
    { cbn. constructor; [intros Hin; inversion Hin | constructor]. }
    refine (conj _ _).
    { cbn. constructor; [cbn; lia | constructor]. }
    refine (conj _ _).
    { cbn. constructor; [|constructor]. unfold fr_entry_ok. cbn.
      refine (conj (or_introl eq_refl) (conj eq_refl (conj eq_refl (conj _ (or_introl eq_refl))))). constructor. }
    exists [(oa_new_src 100 (ls3_q B) [], 0%nat)].
    refine (conj _ _).
    { constructor; [|constructor]. unfold fr_pair_ok. cbn [fst snd].
      repeat match goal with |- _ /\ _ => split end.
      all: try (cbn; lia).
      all: try reflexivity.
      all: try (intros _; split; [reflexivity | intros _; reflexivity]).
      all: try (cbn; constructor).
      all: try (unfold same_set; cbn; split; intros x Hx; destruct Hx).
      all: try (unfold SlotInv.ecap_ok; cbn; lia).
      all: try (unfold SlotInv.ecap_ok; cbn; tauto). }
    refine (conj _ _).
    { cbn. constructor; [intros Hin; inversion Hin | constructor]. }
    refine (conj _ _).
    { intros i Hi Ho. destruct i as [|[|[|[|i]]]]; vm_compute in Ho |- *; first [reflexivity | discriminate | lia]. }
    vm_compute. split; discriminate.
  - vm_compute. reflexivity.
  - unfold fr_gone. split; intros H; vm_compute in H |- *; [repeat split; reflexivity | discriminate].
Qed.

(* THE COUNTEREXAMPLE: LS_exit_cap at LSx := fr_LS3cp B /\ fr_OUT OM /\ fr_ENT B (no fr_CAP), RINV := fr_RINV *)
Theorem LS_exit_cap_false_at_LSI : forall OM, OUT_MAX4 <= OM ->
  ~ (forall cx t m ly S,
       (fr_LS3cp B cx t m ly S /\ fr_OUT OM cx t m ly S /\ fr_ENT B cx m ly S) ->
       fr_RINV cx t m -> 0 <= t <= OPS_MAX ->
       gse_cap (W_LLVMFuzzerTestOneInput_exit.lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) <= CAPOUT_MAX).
Proof.
  intros OM HOM H.
  pose proof (H cex_cx 0 cex_m ls3_ly cex_S (cex_LSI3 OM HOM) cex_RINV ltac:(unfold OPS_MAX; lia)) as Hc.
  assert (EC : lm_cap cex_m = 2 ^ 32) by reflexivity.
  destruct (ou_rf_cap (lm_es cex_m) (lm_c cex_m) [] (lm_mx cex_m) 0 (lm_cap cex_m) ltac:(rewrite EC; lia)) as (R1 & _).
  assert (Hcap : 2 ^ 32 <= lm_cap cex_m) by (rewrite EC; lia).
  unfold CAPOUT_MAX, OPS_MAX in Hc. lia.
Qed.
End cex.

Print Assumptions LS_exit_cap_false_at_LSI.
