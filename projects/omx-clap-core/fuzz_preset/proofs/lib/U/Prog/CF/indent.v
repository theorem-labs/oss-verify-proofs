(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v; 64 of its 422 lines of code are new or changed and 670 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/TxGlue.v, with its module paths and module names changed; 649 of its 741 lines of code are new or changed and 330 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/U/Prog/CF/WriterRet.v, with its module paths and module names changed; 391 of its 430 lines of code are new or changed and 702 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require PropExec Step.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import MState Mem Exec Frame Cells Regs6ss RegisterBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterApp WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import put_c put_kb WriterRet WriterCall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import indent_blocks.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import indent_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

Lemma need_of : forall st P bs Rest,
  Z.of_nat (length (w_text st)) + Z.of_nat (length (concat (P ++ bs :: Rest))) + 1 <= WMAX ->
  Z.of_nat (length (w_text (putN st P))) + Z.of_nat (length bs) + 1 <= WMAX.
Proof.
  intros st P bs Rest H. pose proof (putN_text P st) as T.
  rewrite concat_app in H. cbn [concat] in H. rewrite !length_app in H. lia.
Qed.

Lemma room_of : forall F st b P bs Rest bk, wr_rooms F b st (P ++ bs :: Rest) -> bk = wfold F b st P ->
  w_failed (putN st P) = 0 ->
  w_cap (putN st P) < Z.of_nat (length (w_text (putN st P))) + Z.of_nat (length bs) + 1 ->
  rf_room F bk (newcap (w_cap (putN st P)) (Z.of_nat (length (w_text (putN st P))) + Z.of_nat (length bs) + 1) + 16).
Proof.
  intros F st b P bs Rest bk H E. apply wr_rooms_app in H. destruct H as [_ H]. subst bk. exact (proj1 H).
Qed.

Definition cs_file (regs : bvmap 5 word) (sp s0 s1 s2 : word) : bvmap 5 word :=
  mkR (reg_get regs 1) sp (reg_get regs 3) (reg_get regs 4) (reg_get regs 5) (reg_get regs 6) (reg_get regs 7) s0 s1
      (reg_get regs 10) (reg_get regs 11) (reg_get regs 12) (reg_get regs 13) (reg_get regs 14) (reg_get regs 15)
      (reg_get regs 16) (reg_get regs 17) s2 (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22)
      (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) (reg_get regs 28)
      (reg_get regs 29) (reg_get regs 30) (reg_get regs 31).

Definition ind_agree (regs regs1 : bvmap 5 word) (sp s0 s1 s2 : word) : Prop :=
  forall q, callee_saved q -> getr regs1 (Z_to_bv 5 q) = getr (cs_file regs sp s0 s1 s2) (Z_to_bv 5 q).

Lemma agree_get : forall regs1 R (r : reg),
  (forall q, callee_saved q -> getr regs1 (Z_to_bv 5 q) = getr R (Z_to_bv 5 q)) -> callee_saved (bv_unsigned r) ->
  reg_get regs1 r = reg_get R r.
Proof.
  intros regs1 R r H Hr.
  assert (Hz : bv_eqb r 0 = false).
  { unfold bv_eqb. apply Z.eqb_neq. intros E. rewrite E in Hr. unfold callee_saved in Hr.
    match type of Hr with context [bv_unsigned ?k] => let v := eval vm_compute in (bv_unsigned k) in
      change (bv_unsigned k) with v in Hr end; lia. }
  assert (Er : Z_to_bv 5 (bv_unsigned r) = r)
    by (apply bv_eq; rewrite Z_to_bv_unsigned; apply bv_wrap_small; apply bv_unsigned_in_range).
  rewrite <- !getr_reg by exact Hz. pose proof (H (bv_unsigned r) Hr) as E. rewrite Er in E. exact E.
Qed.

Lemma agree_mkR : forall regs regs1 sp s0 s1 s2, ind_agree regs regs1 sp s0 s1 s2 ->
  mkR_of regs1 =
  mkR (reg_get regs1 1) sp (reg_get regs 3) (reg_get regs 4) (reg_get regs1 5) (reg_get regs1 6) (reg_get regs1 7)
      s0 s1 (reg_get regs1 10) (reg_get regs1 11) (reg_get regs1 12) (reg_get regs1 13) (reg_get regs1 14)
      (reg_get regs1 15) (reg_get regs1 16) (reg_get regs1 17) s2 (reg_get regs 19) (reg_get regs 20)
      (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26)
      (reg_get regs 27) (reg_get regs1 28) (reg_get regs1 29) (reg_get regs1 30) (reg_get regs1 31).
Proof.
  intros regs regs1 sp s0 s1 s2 H. unfold mkR_of. f_equal;
    (etransitivity;
     [ apply (agree_get regs1 (cs_file regs sp s0 s1 s2) _ H); unfold callee_saved;
       match goal with |- context [bv_unsigned ?k] => let v := eval vm_compute in (bv_unsigned k) in
         change (bv_unsigned k) with v end; lia
     | reflexivity ]).
Qed.

Lemma agree_post : forall regs R F pc fc rv m ro x regs1 sp s0 s1 s2,
  ms_eqv (MS R F pc fc rv m ro) x -> regs_preserved (ms_regs x) regs1 ->
  (forall q, callee_saved q -> getr R (Z_to_bv 5 q) = getr (cs_file regs sp s0 s1 s2) (Z_to_bv 5 q)) ->
  ind_agree regs regs1 sp s0 s1 s2.
Proof.
  intros regs R F pc fc rv m ro x regs1 sp s0 s1 s2 HE RP H q Hq.
  rewrite (RP q Hq), (eqv_getr _ _ _ _ _ _ _ _ _ HE). exact (H q Hq).
Qed.

Lemma sp2 : forall regs, bv_unsigned (reg_get regs 2) = spZ regs.
Proof. intros regs. unfold spZ. rewrite getr_reg by reflexivity. reflexivity. Qed.

Section I.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable RF : ResForm.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.

Lemma sp_word : forall regs, alloc_ceiling + IND_K <= spZ regs -> spZ regs < 2 ^ 63 ->
  bv_unsigned (Z_to_bv 64 (bv_unsigned (reg_get regs 2) - IND_FRAME)) = spZ regs - 32.
Proof.
  intros regs H1 H2. pose proof ceil_big as CB. unfold IMG_TOP in CB.
  rewrite sp2. unfold IND_FRAME. apply unsigned_lit.
  unfold IND_K, PUT_K, REALLOC_STACK, ALLOC_STACK in H1. lia.
Qed.

Definition ind_env (regs : bvmap 5 word) (L : layout) (A : astate) (mem : word -> option byte) (md : Model)
    (o : Z) (st : wst) : Prop :=
  aa_MR API L A mem md /\ st_init_done A = true /\ 0 <= w_cap st /\
  alloc_ceiling + IND_K <= spZ regs /\ spZ regs < 2 ^ 63 /\ spZ regs mod 16 = 0 /\
  (forall a, spZ regs - IND_K <= a < spZ regs -> writable_at (ms_segs B) mem a) /\
  (forall a, errno_at B a -> writable_at (ms_segs B) mem a) /\
  spZ regs <= o /\ off_errno B o 32 /\ off_errno B (spZ regs - IND_K) IND_K /\
  getr regs 4 = Z_to_bv 64 (ms_tp B).

Lemma chain_stk : forall regs L A mem md o st buf Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk,
  ind_env regs L A mem md o st ->
  wr_rel B API RF (spZ regs - IND_K) (spZ regs) L A mem md o buf st Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk ->
  stk rsegs memk (spZ regs - IND_K) (spZ regs - 32).
Proof using SEGS.
  intros regs L A mem md o st buf Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk ENV RC.
  destruct ENV as (HM & INIT & CAP0 & CEIL & S63 & S16 & WS & WE & SO & EO & ES & TP).
  destruct (wr_writable B API RF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spZ regs - IND_K) (spZ regs) RC
    ltac:(lia) ltac:(lia) WS WE) as [W1 _].
  pose proof ceil_big as CB.
  apply stk_hi; [unfold IND_K, PUT_K, REALLOC_STACK, ALLOC_STACK in *; lia | lia |].
  intros a Ha. rewrite <- SEGS. apply W1. lia.
Qed.

Lemma ind_fin : forall regs L A mem md o buf st Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk regs1 pc lo,
  YK0s.ret_ok (getr regs 1) ->
  wr_rel B API RF (spZ regs - IND_K) (spZ regs) L A mem md o buf st Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk ->
  Exec.evt rsegs
    (ind_ret (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 8) (reg_get regs 9)
       (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23)
       (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) (@fp_regs fx) (@fp_csr fx) lo memk)
    (MS (mkR_of regs1) (@fp_regs fx) pc (@fp_csr fx) None memk (PropExec.seg_rom rsegs)) ->
  SR (ms_segs B) (mkCfg (mkst regs1 pc memk (seg_rom (ms_segs B))) mdk)
    (wr_ret B API RF IND_K L A regs mem md o buf st Lam peak b P).
Proof using SEGS.
  intros regs L A mem md o buf st Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk regs1 pc lo RA RC EV.
  pose proof RC as (HMk & _).
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMk) as (Hh & Hl & _).
  rewrite SEGS. eapply kA_lift; [exact Hh | exact Hl | exact EV |].
  intros x y HQ HEQ HRM.
  destruct HQ as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & Ey & _). subst y.
  assert (PC : ret_pc (reg_get regs 1) = getr regs 1)
    by (rewrite <- getr_reg by reflexivity; apply ret_pc_ok; exact RA).
  destruct (post_shape B SEGS regs _ memk x mdk HEQ PC) as [CF _].
  rewrite CF. apply SR_ret. unfold wr_ret.
  exists Lk, Ak, (ms_regs x), memk, mdk, bufk, Lamk, peakk, bk.
  split; [reflexivity|]. split; [| exact RC].
  eapply regs_kept; [exact HEQ |]. callee_cases.
Qed.

Section P.
Hypothesis PUTC : put_contract B API RF.

Lemma put_step : forall regs L A mem md o buf st Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk regsk s bs Rest cs Q,
  ind_env regs L A mem md o st ->
  wr_rel B API RF (spZ regs - IND_K) (spZ regs) L A mem md o buf st Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk ->
  wr_rooms RF b st (P ++ bs :: Rest) ->
  Z.of_nat (length (w_text st)) + Z.of_nat (length (concat (P ++ bs :: Rest))) + 1 <= WMAX ->
  spZ regsk = spZ regs - 32 -> getr regsk 4 = getr regs 4 -> YK0s.ret_ok (getr regsk 1) ->
  getr regsk 10 = Z_to_bv 64 o -> getr regsk 11 = Z_to_bv 64 s ->
  getr regsk 12 = Z_to_bv 64 (Z.of_nat (length bs)) ->
  img_ok s bs = true ->
  existsb (fun sg => (bv_unsigned (fst sg) <=? s) && (s <? bv_unsigned (fst sg) + bv_unsigned (snd sg)))
    (segments_reserved rsegs) = true ->
  0 <= s -> s + Z.of_nat (length bs) <= IMG_TOP -> bytes_ok bs ->
  Step.rw_cells rsegs memk (spZ regs - 32) cs -> cells_size cs = 32%nat ->
  (forall regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1, regs_preserved regsk regs1 ->
     wr_rel B API RF (spZ regs - IND_K) (spZ regs) L A mem md o buf st Lam peak b (P ++ [bs])
       L1 A1 mem1 md1 buf1 Lam1 peak1 b1 ->
     Step.rw_cells rsegs mem1 (spZ regs - 32) cs ->
     SR (ms_segs B) (mkCfg (mkst regs1 (getr regsk 1) mem1 (seg_rom (ms_segs B))) md1) Q) ->
  SR (ms_segs B) (mkCfg (mkst regsk (Z_to_bv 64 CF.put_c.PUT) memk (seg_rom (ms_segs B))) mdk) Q.
Proof using SEGS AX CTX PUTC.
  intros regs L A mem md o buf st Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk regsk s bs Rest cs Q
    ENV RC ROOMS NEED SPk TPk RAk Q10 Q11 Q12 IMG SEG S0 SI BO FR CS K.
  pose proof ENV as (HM & INIT & CAP0 & CEIL & S63 & S16 & WS & WE & SO & EO & ES & TP).
  pose proof RC as (HMk & HWk & HBk & [ROk GKk] & PJk & LGk & RSk & EBk & _ & _ & _ & INk & _).
  destruct (wr_writable B API RF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spZ regs - IND_K) (spZ regs) RC
    ltac:(lia) ltac:(lia) WS WE) as [WSk WEk].
  pose proof ceil_big as CB. unfold IMG_TOP in CB, SI.
  pose proof (Nat2Z.is_nonneg (length bs)) as LB.
  assert (ROr : ro_agree rsegs memk) by (rewrite <- SEGS; exact ROk).
  apply (put_call B API RF SEGS AX PUTC IND_K (spZ regs) Lk Ak regsk memk mdk o s (Z.of_nat (length bs)) bs bufk
    (putN st P) Lamk peakk bk Q).
  - rewrite SPk. unfold IND_K. lia.
  - lia.
  - exact CEIL.
  - exact S63.
  - rewrite SPk. Z.div_mod_to_equations. lia.
  - exact WSk.
  - exact WEk.
  - rewrite TPk. exact TP.
  - exact RAk.
  - exact HMk.
  - exact HWk.
  - exact HBk.
  - exact (INk INIT).
  - exact ROk.
  - exact Q10.
  - exact Q11.
  - exact Q12.
  - exact PJk.
  - exact LGk.
  - exact RSk.
  - exact SO.
  - exact EO.
  - exact ES.
  - exact (img_zbytes B SEGS memk s bs ROr IMG).
  - reflexivity.
  - exact BO.
  - lia.
  - lia.
  - exact (img_where B SEGS regsk Lamk s _ bufk bs SEG IMG eq_refl).
  - left. unfold IND_K, PUT_K, REALLOC_STACK, ALLOC_STACK in CEIL. lia.
  - exact (need_of st P bs Rest NEED).
  - exact (room_of RF st b P bs Rest bk ROOMS EBk).
  - intros regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1 RP R1.
    assert (FR1 : Step.rw_cells rsegs mem1 (spZ regs - 32) cs).
    { eapply (wr_cells B API RF SEGS); [exact HMk | exact R1 | exact FR | | | |].
      - unfold IND_K, PUT_K, REALLOC_STACK, ALLOC_STACK in CEIL. lia.
      - lia.
      - rewrite CS. change (Z.of_nat 32) with 32. left. lia.
      - rewrite CS. change (Z.of_nat 32) with 32.
        eapply off_errno_sub; [exact ES | unfold IND_K, PUT_K, REALLOC_STACK, ALLOC_STACK; lia
          | unfold IND_K, PUT_K, REALLOC_STACK, ALLOC_STACK; lia]. }
    assert (R1' : wr_rel B API RF (spZ regs - IND_K) (spZ regs) Lk Ak memk mdk o bufk (putN st P) Lamk peakk bk [bs]
                    L1 A1 mem1 md1 buf1 Lam1 peak1 b1).
    { apply (wr_rel_widen B API RF (spZ regsk - PUT_K) (spZ regsk)); [exact HMk | | | | | exact R1].
      - rewrite SPk. unfold IND_K. lia.
      - lia.
      - lia.
      - lia. }
    apply (K regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1 RP); [| exact FR1].
    exact (wr_rel_app B API RF SEGS AX CTX _ _ L A mem md o buf st Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk [bs]
      L1 A1 mem1 md1 buf1 Lam1 peak1 b1 HM CAP0 RC R1').
Qed.

Lemma bytes_ok_sp : bytes_ok [32; 32].
Proof. unfold bytes_ok. repeat constructor; lia. Qed.

Lemma bytes_ok_nl : bytes_ok [10].
Proof. unfold bytes_ok. repeat constructor; lia. Qed.

Lemma ind_loop : forall n regs L A mem md o buf st Lam peak b W P Lk Ak memk mdk bufk Lamk peakk bk regs1,
  ind_env regs L A mem md o st -> YK0s.ret_ok (getr regs 1) ->
  wr_rooms RF b st W -> Z.of_nat (length (w_text st)) + Z.of_nat (length (concat W)) + 1 <= WMAX ->
  W = P ++ repeat [32; 32] n -> Z.of_nat n + 1 < 2 ^ 31 ->
  wr_rel B API RF (spZ regs - IND_K) (spZ regs) L A mem md o buf st Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk ->
  ind_agree regs regs1 (Z_to_bv 64 (bv_unsigned (reg_get regs 2) - IND_FRAME)) (Z_to_bv 64 (Z.of_nat n + 1))
    (Z_to_bv 64 o) (Z_to_bv 64 STR_SP2) ->
  Step.rw_cells rsegs memk (spZ regs - 32)
    [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)] ->
  SR (ms_segs B) (mkCfg (mkst regs1 (Z_to_bv 64 IND_SP_RET) memk (seg_rom (ms_segs B))) mdk)
    (wr_ret B API RF IND_K L A regs mem md o buf st Lam peak b W).
Proof using SEGS AX CTX PUTC.
  induction n as [|n IH]; intros regs L A mem md o buf st Lam peak b W P Lk Ak memk mdk bufk Lamk peakk bk regs1
    ENV RA ROOMS NEED HW HN RC AG FR.
  - cbn [repeat] in HW. rewrite app_nil_r in HW. subst W.
    pose proof (chain_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ENV RC) as STK.
    pose proof ENV as (_ & _ & _ & CEIL & S63 & _).
    change (Z.of_nat 0 + 1) with 1 in AG.
    eapply ind_fin; [exact RA | exact RC |].
    rewrite (agree_mkR _ _ _ _ _ _ AG).
    eapply ind_loop_done with (lo := spZ regs - IND_K).
    + rewrite sp2. unfold IND_FRAME. exact STK.
    + rewrite sp2. unfold IND_FRAME, IND_K, PUT_K, REALLOC_STACK, ALLOC_STACK. lia.
    + rewrite sp2. unfold IND_FRAME. exact FR.
  - pose proof RC as (HMk & _).
    destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMk) as (Hh & Hl & _).
    pose proof ENV as (_ & _ & _ & CEIL & S63 & _).
    rewrite SEGS. eapply kA_lift; [exact Hh | exact Hl | |].
    { rewrite (agree_mkR _ _ _ _ _ _ AG). eapply ind_loop_put. lia. }
    intros x y HQ HEQ HRM.
    replace (Z.of_nat (S n) + 1 - 1) with (Z.of_nat n + 1) in HQ by lia.
    subst y.
    rewrite (eqv_shape _ _ _ _ HEQ). rewrite <- SEGS.
    apply (put_step regs L A mem md o buf st Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk (ms_regs x)
      STR_SP2 [32; 32] (repeat [32; 32] n)
      [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
    + exact ENV.
    + exact RC.
    + rewrite HW in ROOMS. exact ROOMS.
    + rewrite HW in NEED. exact NEED.
    + unfold spZ at 1. rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ). exact (sp_word regs CEIL S63).
    + rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ). reflexivity.
    + rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ).
      exact (ret_ok_lit IND_SP_RET ltac:(unfold IND_SP_RET; lia) eq_refl).
    + rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ). reflexivity.
    + rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ). reflexivity.
    + rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ). reflexivity.
    + vm_compute. reflexivity.
    + vm_compute. reflexivity.
    + unfold STR_SP2. lia.
    + unfold STR_SP2, IMG_TOP. change (Z.of_nat (length [32; 32])) with 2. lia.
    + exact bytes_ok_sp.
    + exact FR.
    + reflexivity.
    + intros regs2 L2 A2 mem2 md2 buf2 Lam2 peak2 b2 RP R2 FR2.
      replace (getr (ms_regs x) 1) with (Z_to_bv 64 IND_SP_RET)
        by (rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ); reflexivity).
      apply (IH regs L A mem md o buf st Lam peak b W (P ++ [[32; 32]]) L2 A2 mem2 md2 buf2 Lam2 peak2 b2 regs2
        ENV RA ROOMS NEED).
      * rewrite HW, <- app_assoc. reflexivity.
      * lia.
      * exact R2.
      * eapply agree_post; [exact HEQ | exact RP | callee_cases].
      * exact FR2.
Qed.

End P.

Theorem indent_holds : put_contract B API RF -> indent_contract B API RF.
Proof using SEGS AX CTX.
  intros PUTC. unfold indent_contract.
  intros L A regs mem md b o pretty depth buf st Lam peak SG PRE INIT MI R10 R11 R12 Hp Hd PJ LG SPO EO ES NEED RS
    ROOMS.
  pose proof PRE as (HM & HWF & HB & Hra & Hal & Hceil & Hsp & HWs & Htp & HWe & Haux).
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  pose proof ceil_big as CB. unfold IMG_TOP in CB.
  pose proof (sp2 regs) as SP2.
  assert (Q10 : reg_get regs 10 = Z_to_bv 64 o) by (rewrite <- getr_reg by reflexivity; exact R10).
  assert (Q11 : reg_get regs 11 = Z_to_bv 64 pretty) by (rewrite <- getr_reg by reflexivity; exact R11).
  assert (Q12 : reg_get regs 12 = Z_to_bv 64 depth) by (rewrite <- getr_reg by reflexivity; exact R12).
  assert (PC : ret_pc (reg_get regs 1) = getr regs 1)
    by (rewrite <- getr_reg by reflexivity; apply ret_pc_ok; exact Hra).
  assert (CAP0 : 0 <= w_cap st) by (destruct PJ as (_ & _ & _ & _ & _ & _ & Rc & _); lia).
  assert (ENV : ind_env regs L A mem md o st).
  { unfold ind_env. split; [exact HM|]. split; [exact INIT|]. split; [exact CAP0|]. split; [exact Hceil|].
    split; [exact Hsp|]. split; [exact Hal|]. split; [exact HWs|]. split; [exact HWe|]. split; [exact SPO|].
    split; [exact EO|]. split; [exact ES | exact Htp]. }
  destruct (Z.eq_dec pretty 0) as [P0|P0].
  - subst pretty. rewrite SEGS. eapply kA_lift; [exact Hh | exact Hl | |].
    { unfold mkR_of. rewrite Q11. change (Z_to_bv 64 INDENT_PC) with (Z_to_bv 64 INDENT).
      apply ind_nopretty. apply unsigned_lit. lia. }
    intros x y HQ HEQ HRM. cbv beta in HQ. subst y.
    destruct (post_shape B SEGS regs _ mem x md HEQ PC) as [CF _].
    rewrite CF. apply SR_ret. unfold wr_ret.
    exists L, A, (ms_regs x), mem, md, buf, Lam, peak, b.
    split; [reflexivity|]. split.
    + eapply regs_kept; [exact HEQ |]. callee_cases.
    + exact (wr_rel_nil B API RF _ _ L A mem md o buf st Lam peak b HM HWF HB MI PJ LG RS).
  - replace (negb (pretty =? 0)) with true in * by (destruct (Z.eqb_spec pretty 0); [lia | reflexivity]).
    rewrite SEGS. eapply kA_lift; [exact Hh | exact Hl | |].
    { unfold mkR_of. rewrite Q10, Q11, Q12. change (Z_to_bv 64 INDENT_PC) with (Z_to_bv 64 INDENT).
      eapply ind_to_put_nl with (lo := spZ regs - IND_K).
      - rewrite unsigned_lit by lia. exact P0.
      - rewrite SP2. apply stk_hi; [unfold IMG_TOP, IND_K, PUT_K, REALLOC_STACK, ALLOC_STACK in *; lia | lia |].
        intros a Ha. rewrite <- SEGS. apply HWs. exact Ha.
      - rewrite SP2. unfold IND_FRAME, IND_K, PUT_K, REALLOC_STACK, ALLOC_STACK. lia. }
    intros x y HQ HEQ HRM.
    destruct HQ as (m0 & Ey & MU & WM & ST0 & FR0). subst y.
    assert (XM : ms_mem x = m0) by (destruct HEQ as (_ & _ & _ & _ & _ & _ & HMx & _); cbn in HMx; congruence).
    rewrite XM in HRM. rewrite SP2 in FR0. unfold IND_FRAME in FR0.
    assert (R0 : wr_rel B API RF (spZ regs - IND_K) (spZ regs) L A mem md o buf st Lam peak b [] L A m0 md buf Lam peak b).
    { eapply (wr_rel_munch B API RF SEGS);
        [exact (wr_rel_nil B API RF _ _ L A mem md o buf st Lam peak b HM HWF HB MI PJ LG RS) | exact MU | exact WM
        | exact HRM | |].
      - intros z Hz Hn. cbn [outside] in Hn. rewrite SP2 in Hn. unfold IND_FRAME in Hn.
        assert (Hw : spZ regs - 32 <= z < spZ regs).
        { destruct (Z_le_gt_dec (spZ regs - 32) z) as [H1|H1];
            [destruct (Z_lt_ge_dec z (spZ regs)) as [H2|H2]|];
            [lia | exfalso; apply Hn; split; [lia | exact I] | exfalso; apply Hn; split; [lia | exact I]]. }
        unfold IND_K, PUT_K, REALLOC_STACK, ALLOC_STACK. lia.
      - unfold IND_K, PUT_K, REALLOC_STACK, ALLOC_STACK in *. lia. }
    rewrite (eqv_shape _ _ _ _ HEQ). rewrite <- SEGS.
    apply (put_step PUTC regs L A mem md o buf st Lam peak b [] L A m0 md buf Lam peak b (ms_regs x)
      STR_NL [10] (repeat [32; 32] (Z.to_nat depth))
      [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
    + exact ENV.
    + exact R0.
    + exact ROOMS.
    + exact NEED.
    + unfold spZ at 1. rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ). exact (sp_word regs Hceil Hsp).
    + rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ). reflexivity.
    + rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ).
      exact (ret_ok_lit IND_NL_RET ltac:(unfold IND_NL_RET; lia) eq_refl).
    + rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ). reflexivity.
    + rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ). reflexivity.
    + rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ). reflexivity.
    + vm_compute. reflexivity.
    + vm_compute. reflexivity.
    + unfold STR_NL. lia.
    + unfold STR_NL, IMG_TOP. change (Z.of_nat (length [10])) with 1. lia.
    + exact bytes_ok_nl.
    + exact FR0.
    + reflexivity.
    + intros regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1 RP R1 FR1.
      replace (getr (ms_regs x) 1) with (Z_to_bv 64 IND_NL_RET)
        by (rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ); reflexivity).
      assert (AG1 : ind_agree regs regs1 (Z_to_bv 64 (bv_unsigned (reg_get regs 2) - IND_FRAME)) (Z_to_bv 64 depth)
                      (Z_to_bv 64 o) (reg_get regs 18))
        by (eapply agree_post; [exact HEQ | exact RP | callee_cases]).
      pose proof (chain_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ENV R1) as STK1.
      destruct (Z_le_gt_dec depth 0) as [D0|D0].
      * assert (EW : wind true depth = [] ++ [[10]])
          by (unfold wind; replace (Z.to_nat depth) with 0%nat by lia; reflexivity).
        rewrite EW.
        eapply ind_fin; [exact Hra | exact R1 |].
        rewrite (agree_mkR _ _ _ _ _ _ AG1).
        eapply ind_after_nl_done with (lo := spZ regs - IND_K).
        -- lia.
        -- rewrite SP2. unfold IND_FRAME. exact STK1.
        -- rewrite SP2. unfold IND_FRAME, IND_K, PUT_K, REALLOC_STACK, ALLOC_STACK. lia.
        -- rewrite SP2. unfold IND_FRAME. exact FR1.
      * pose proof R1 as (HM1 & _).
        destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM1) as (Hh1 & Hl1 & _).
        assert (EW : wind true depth = ([] ++ [[10]]) ++ [32; 32] :: repeat [32; 32] (Z.to_nat depth - 1)).
        { unfold wind. replace (Z.to_nat depth) with (S (Z.to_nat depth - 1)) at 1 by lia. reflexivity. }
        rewrite SEGS. eapply kA_lift; [exact Hh1 | exact Hl1 | |].
        { rewrite (agree_mkR _ _ _ _ _ _ AG1). eapply ind_after_nl_put. lia. }
        intros x2 y2 HQ2 HEQ2 HRM2. cbv beta in HQ2. subst y2.
        rewrite (eqv_shape _ _ _ _ HEQ2). rewrite <- SEGS.
        apply (put_step PUTC regs L A mem md o buf st Lam peak b ([] ++ [[10]]) L1 A1 mem1 md1 buf1 Lam1 peak1 b1
          (ms_regs x2) STR_SP2 [32; 32] (repeat [32; 32] (Z.to_nat depth - 1))
          [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
        -- exact ENV.
        -- exact R1.
        -- rewrite <- EW. exact ROOMS.
        -- rewrite <- EW. exact NEED.
        -- unfold spZ at 1. rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ2). exact (sp_word regs Hceil Hsp).
        -- rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ2). reflexivity.
        -- rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ2).
           exact (ret_ok_lit IND_SP_RET ltac:(unfold IND_SP_RET; lia) eq_refl).
        -- rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ2). reflexivity.
        -- rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ2). reflexivity.
        -- rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ2). reflexivity.
        -- vm_compute. reflexivity.
        -- vm_compute. reflexivity.
        -- unfold STR_SP2. lia.
        -- unfold STR_SP2, IMG_TOP. change (Z.of_nat (length [32; 32])) with 2. lia.
        -- exact bytes_ok_sp.
        -- exact FR1.
        -- reflexivity.
        -- intros regs2 L2 A2 mem2 md2 buf2 Lam2 peak2 b2 RP2 R2 FR2.
           replace (getr (ms_regs x2) 1) with (Z_to_bv 64 IND_SP_RET)
             by (rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ2); reflexivity).
           apply (ind_loop PUTC (Z.to_nat depth - 1) regs L A mem md o buf st Lam peak b (wind true depth)
             (([] ++ [[10]]) ++ [[32; 32]]) L2 A2 mem2 md2 buf2 Lam2 peak2 b2 regs2 ENV Hra ROOMS NEED).
           ++ rewrite EW. reflexivity.
           ++ lia.
           ++ exact R2.
           ++ replace (Z.of_nat (Z.to_nat depth - 1) + 1) with depth by lia.
              eapply agree_post; [exact HEQ2 | exact RP2 | callee_cases].
           ++ exact FR2.
Qed.

End I.
