(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v; 64 of its 422 lines of code are new or changed and 670 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/TxGlue.v, with its module paths and module names changed; 647 of its 739 lines of code are new or changed and 330 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/U/Prog/WriterRet.v, with its module paths and module names changed; 1111 of its 1216 lines of code are new or changed and 634 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require PropExec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import MState Mem Exec Frame Cells Step FP Image.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import Regs6ss RegisterBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger put_c put_kb.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterApp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import WriterRet WriterCall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import printf_facts_c snprintf_c strlen_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import put_string_blocks put_string_c.
Import ListNotations.
Local Open Scope Z_scope.

Ltac pz_cs := cbn [cells_size csize ps_lits ps_saved Nat.add app length disjoint_from].
Ltac pz_csh H := cbn [cells_size csize ps_lits ps_saved Nat.add app length disjoint_from] in H.

Lemma pz_wx : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pz_getr : forall R k, 0 < k < 32 -> getr R (Z_to_bv 5 k) = reg_get R (Z_to_bv 5 k).
Proof.
  intros R k Hk. apply getr_reg. unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia.
  match goal with |- _ <> ?z => let v := eval vm_compute in z in change z with v end. lia.
Qed.

Lemma pz_mkR_of_eq : forall R, mkR_of R =
  mkR (reg_get R (Z_to_bv 5 1)) (reg_get R (Z_to_bv 5 2)) (reg_get R (Z_to_bv 5 3)) (reg_get R (Z_to_bv 5 4))
      (reg_get R (Z_to_bv 5 5)) (reg_get R (Z_to_bv 5 6)) (reg_get R (Z_to_bv 5 7)) (reg_get R (Z_to_bv 5 8))
      (reg_get R (Z_to_bv 5 9)) (reg_get R (Z_to_bv 5 10)) (reg_get R (Z_to_bv 5 11)) (reg_get R (Z_to_bv 5 12))
      (reg_get R (Z_to_bv 5 13)) (reg_get R (Z_to_bv 5 14)) (reg_get R (Z_to_bv 5 15)) (reg_get R (Z_to_bv 5 16))
      (reg_get R (Z_to_bv 5 17)) (reg_get R (Z_to_bv 5 18)) (reg_get R (Z_to_bv 5 19)) (reg_get R (Z_to_bv 5 20))
      (reg_get R (Z_to_bv 5 21)) (reg_get R (Z_to_bv 5 22)) (reg_get R (Z_to_bv 5 23)) (reg_get R (Z_to_bv 5 24))
      (reg_get R (Z_to_bv 5 25)) (reg_get R (Z_to_bv 5 26)) (reg_get R (Z_to_bv 5 27)) (reg_get R (Z_to_bv 5 28))
      (reg_get R (Z_to_bv 5 29)) (reg_get R (Z_to_bv 5 30)) (reg_get R (Z_to_bv 5 31)).
Proof. intros R. reflexivity. Qed.

Lemma pz_spZ_mkR : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31,
  spZ (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
         x29 x30 x31) = bv_unsigned x2.
Proof. intros. reflexivity. Qed.

Definition pz_xrel (x y0 : machine_state) : Prop :=
  xregs_eqv (ms_regs y0) (ms_regs x) /\ ms_fregs y0 = ms_fregs x /\ ms_pc_val y0 = ms_pc_val x /\
  ms_svc_pending y0 = ms_svc_pending x /\ ms_resv y0 = ms_resv x /\ ms_fcsr y0 = ms_fcsr x /\
  ms_rom y0 = ms_rom x /\ mem_rel_cj rsegs (ms_mem x) (ms_mem y0).

Lemma pz_xrel_eqv : forall x R F pc fc rv m0 ro, pz_xrel x (MS R F pc fc rv m0 ro) ->
  ms_eqv (MS R F pc fc rv (ms_mem x) ro) x /\ mem_rel_cj rsegs (ms_mem x) m0.
Proof.
  intros x R F pc fc rv m0 ro (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8). cbn in *.
  split; [|exact H8]. unfold ms_eqv. cbn. repeat split; first [assumption | reflexivity].
Qed.

Lemma pz_lift : forall (fx1 : FPState) regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] -> ro_agree rsegs mem ->
  evt rsegs Q (MS (mkR_of regs) (@fp_regs fx1) pc (@fp_csr fx1) None (normalize_cj rsegs mem) (PropExec.seg_rom rsegs)) ->
  (forall x y0, Q y0 -> pz_xrel x y0 -> cj_same rsegs mem (ms_mem x) -> rm mem (ms_mem x) -> SR rsegs (mkCfg x md) P) ->
  SR rsegs (mkCfg (@YK11.mkst fx1 regs pc mem (YK11.seg_rom rsegs)) md) P.
Proof.
  intros fx1 regs pc mem md Q P Hh Hl RO HE K.
  apply (@kA_lift fx1 regs pc mem md (fun s => exists s0, Q s0 /\ ms_rel_cj rsegs s s0 /\ cj_same rsegs mem (ms_mem s)) P Hh Hl).
  - exact (evt_normalize_cj rsegs Q _ _ pc _ None mem _ pz_wx RO HE).
  - intros x y (y0 & HQ & HR & HO) HEQ RM. apply (K x y0 HQ); [| | exact RM].
    + destruct HR as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
      destruct HEQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
      split; [rewrite <- R1; exact Q1|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
      split; [congruence|]. split; [congruence|]. split; [congruence|]. rewrite <- Q7. exact R8.
    + destruct HEQ as (_ & _ & _ & _ & _ & _ & Q7 & _). rewrite <- Q7. exact HO.
Qed.

Lemma pz_kA_after : forall (fx1 : FPState) regs2 mem2 md2 (Q : machine_state -> Prop) (P : config -> Prop)
    (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29
     v30 v31 : word),
  regs_preserved (mkR v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26
                    v27 v28 v29 v30 v31) regs2 ->
  m_halted md2 = None -> m_vm_lazy md2 = [] -> ro_agree rsegs mem2 ->
  evt rsegs Q (MS (mkR (reg_get regs2 (Z_to_bv 5 1)) v2 v3 v4 (reg_get regs2 (Z_to_bv 5 5)) (reg_get regs2 (Z_to_bv 5 6))
        (reg_get regs2 (Z_to_bv 5 7)) v8 v9 (reg_get regs2 (Z_to_bv 5 10)) (reg_get regs2 (Z_to_bv 5 11))
        (reg_get regs2 (Z_to_bv 5 12)) (reg_get regs2 (Z_to_bv 5 13)) (reg_get regs2 (Z_to_bv 5 14))
        (reg_get regs2 (Z_to_bv 5 15)) (reg_get regs2 (Z_to_bv 5 16)) (reg_get regs2 (Z_to_bv 5 17))
        v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 (reg_get regs2 (Z_to_bv 5 28)) (reg_get regs2 (Z_to_bv 5 29))
        (reg_get regs2 (Z_to_bv 5 30)) (reg_get regs2 (Z_to_bv 5 31)))
     (@fp_regs fx1) v1 (@fp_csr fx1) None (normalize_cj rsegs mem2) (PropExec.seg_rom rsegs)) ->
  (forall x y0, Q y0 -> pz_xrel x y0 -> cj_same rsegs mem2 (ms_mem x) -> rm mem2 (ms_mem x) -> SR rsegs (mkCfg x md2) P) ->
  SR rsegs (mkCfg (@YK11.mkst fx1 regs2 (getr (mkR v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18
      v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31) (Z_to_bv 5 1)) mem2 (YK11.seg_rom rsegs)) md2) P.
Proof.
  intros fx1 regs2 mem2 md2 Q P v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24
    v25 v26 v27 v28 v29 v30 v31 RP Hh Hl RO HE K.
  change (getr (mkR v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27
      v28 v29 v30 v31) (Z_to_bv 5 1)) with v1.
  apply (pz_lift fx1 regs2 v1 mem2 md2 Q P Hh Hl RO); [|exact K].
  assert (E : forall k, callee_saved k -> reg_get regs2 (Z_to_bv 5 k) =
    getr (mkR v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28
      v29 v30 v31) (Z_to_bv 5 k)).
  { intros k Hk. rewrite <- (RP k Hk). symmetry. apply pz_getr. unfold callee_saved in Hk. lia. }
  rewrite pz_mkR_of_eq.
  rewrite (E 2), (E 3), (E 4), (E 8), (E 9), (E 18), (E 19), (E 20), (E 21), (E 22), (E 23), (E 24), (E 25), (E 26),
    (E 27) by (unfold callee_saved; lia).
  exact HE.
Qed.

Lemma pz_back : forall W m m0' x, ro_agree rsegs m -> mem_rel_cj rsegs (ms_mem x) m0' -> cj_same rsegs m (ms_mem x) ->
  munch W (normalize_cj rsegs m) m0' -> wmono rsegs (normalize_cj rsegs m) m0' ->
  munch W m (ms_mem x) /\ wmono rsegs m (ms_mem x) /\ ro_agree rsegs (ms_mem x).
Proof.
  intros W m m0' x RO HR HO MU WM. pose proof (mem_rel_cj_normalize rsegs m RO) as HN.
  split; [exact (munch_rel_cj rsegs W m _ (ms_mem x) m0' HN HR HO MU)|].
  split; [exact (wmono_rel_cj rsegs m _ (ms_mem x) m0' HN HR HO WM)|].
  exact (ro_agree_same_cj rsegs m _ RO HO).
Qed.

Lemma pz_keep : forall a, IMG_TOP <= a < TASK_SIZE -> cj_drop rsegs (wa a) = false.
Proof.
  intros a Ha. assert (T : TASK_SIZE = 2 ^ 47) by reflexivity. unfold IMG_TOP in Ha.
  apply cj_drop_false_intro.
  - apply ro_false_hi. unfold IMG_TOP. lia.
  - right. rewrite wa_unsigned by lia. lia.
Qed.

Lemma pz_stk_norm : forall m lo hi, stk rsegs m lo hi -> IMG_TOP <= lo -> hi <= TASK_SIZE ->
  stk rsegs (normalize_cj rsegs m) lo hi.
Proof.
  intros m lo hi (H1 & H2 & H) Hlo Hhi. split; [exact H1|]. split; [exact H2|]. intros a Ha.
  assert (N : normalize_cj rsegs m (wa a) = m (wa a))
    by (unfold normalize_cj; rewrite (pz_keep a) by lia; reflexivity).
  destruct (H a Ha) as [W [b E]]. split.
  - unfold wview in *. rewrite N. exact W.
  - exists b. unfold mrd in *. rewrite N. exact E.
Qed.

Lemma pz_rw_norm : forall m A cs, ro_agree rsegs m -> rw_cells rsegs m A cs ->
  IMG_TOP <= A -> A + Z.of_nat (cells_size cs) <= TASK_SIZE ->
  rw_cells rsegs (normalize_cj rsegs m) A cs.
Proof.
  intros m A cs RO [[Hwf Hb] Hw] Hlo Hhi. split; [split; [exact Hwf|]|].
  - apply bytes_at_normalize_cj_low; [exact RO | | exact Hb]. rewrite cells_bytes_length by exact Hwf. exact Hhi.
  - apply (wr_at_norm_cj rsegs m (normalize_cj rsegs m) A _ (mem_rel_cj_normalize rsegs m RO) Hw).
    intros i Hi. apply pz_keep. lia.
Qed.

Lemma pz_rw_rel : forall m m0 A cs, mem_rel_cj rsegs m m0 -> rw_cells rsegs m0 A cs -> rw_cells rsegs m A cs.
Proof.
  intros m m0 A cs HR [[Hwf Hb] Hw]. split; [split; [exact Hwf|]|].
  - exact (bytes_at_rel_cj rsegs m m0 A _ HR Hb).
  - exact (wr_at_rel_cj rsegs m m0 A _ HR Hw).
Qed.

Lemma pz_rw_app : forall m A c1 c2, rw_cells rsegs m A (c1 ++ c2) ->
  rw_cells rsegs m A c1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size c1)) c2.
Proof.
  intros m A c1 c2 [[Hwf Hb] (W1 & W2 & Hw)]. apply cells_wf_app in Hwf as [Wf1 Wf2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb as [B1 B2].
  rewrite cells_bytes_length in B2 by exact Wf1. rewrite cells_size_app, Nat2Z.inj_add in W2, Hw.
  pose proof (Nat2Z.is_nonneg (cells_size c1)). pose proof (Nat2Z.is_nonneg (cells_size c2)).
  split.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size c1) + i) with (A + (Z.of_nat (cells_size c1) + i)) by lia. apply Hw. lia.
Qed.

Lemma pz_rw_join : forall m A c1 c2, rw_cells rsegs m A c1 -> rw_cells rsegs m (A + Z.of_nat (cells_size c1)) c2 ->
  rw_cells rsegs m A (c1 ++ c2).
Proof.
  intros m A c1 c2 [[Wf1 B1] (V1 & V2 & H1)] [[Wf2 B2] (U1 & U2 & H2)].
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite cells_bytes_length by exact Wf1. exact B2.
  - rewrite cells_size_app, Nat2Z.inj_add. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_ge_dec i (Z.of_nat (cells_size c1))) as [L|L]; [apply H1; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size c1) + (i - Z.of_nat (cells_size c1))) by lia. apply H2. lia.
Qed.

Lemma pz_rw_addr : forall m A A' cs, A = A' -> rw_cells rsegs m A cs -> rw_cells rsegs m A' cs.
Proof. intros m A A' cs -> H. exact H. Qed.

Lemma pz_bytes_addr : forall m A A' bs, A = A' -> bytes_at rsegs m A bs -> bytes_at rsegs m A' bs.
Proof. intros m A A' bs -> H. exact H. Qed.

Lemma pz_cell_bytes : forall m A n bs, rw_cells rsegs m A [CB n bs] -> bytes_at rsegs m A bs /\ length bs = n /\
  wr_at rsegs m A (Z.of_nat n).
Proof.
  intros m A n bs [[(Hl & _) H] W]. cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H.
  cbn [cells_size csize] in W. rewrite Nat.add_0_r in W. split; [exact H|]. split; [exact Hl | exact W].
Qed.

Lemma pz_cell_mk : forall m A n bs, length bs = n -> bytes_at rsegs m A bs -> wr_at rsegs m A (Z.of_nat n) ->
  rw_cells rsegs m A [CB n bs].
Proof.
  intros m A n bs Hl Hb Hw. split; [split|].
  - cbn. split; [exact Hl | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hw.
Qed.

Lemma pz_frame_parts : forall m A e SV, rw_cells rsegs m A (ps_lits ++ CB 8 e :: SV) ->
  rw_cells rsegs m A ps_lits /\ rw_cells rsegs m (A + 32) [CB 8 e] /\ rw_cells rsegs m (A + 40) SV.
Proof.
  intros m A e SV FR. destruct (pz_rw_app _ _ _ _ FR) as [FL FR2].
  change (CB 8 e :: SV) with ([CB 8 e] ++ SV) in FR2.
  destruct (pz_rw_app _ _ _ _ FR2) as [FS FV].
  split; [exact FL|]. split.
  - eapply pz_rw_addr; [|exact FS]. reflexivity.
  - eapply pz_rw_addr; [|exact FV]. cbn. lia.
Qed.

Lemma pz_frame_mk : forall m A e SV, rw_cells rsegs m A ps_lits -> rw_cells rsegs m (A + 32) [CB 8 e] ->
  rw_cells rsegs m (A + 40) SV -> rw_cells rsegs m A (ps_lits ++ CB 8 e :: SV).
Proof.
  intros m A e SV FL FS FV. apply pz_rw_join; [exact FL|].
  change (CB 8 e :: SV) with ([CB 8 e] ++ SV). apply pz_rw_join.
  - eapply pz_rw_addr; [|exact FS]. reflexivity.
  - eapply pz_rw_addr; [|exact FV]. cbn. lia.
Qed.

Lemma pz_sub1 : forall a b lo hi, lo <= a -> b <= hi -> sub_fp [(a, b)] [(lo, hi)].
Proof. intros a b lo hi H1 H2 x Hx. cbn [outside] in *. destruct Hx as [Hx _]. split; [lia | exact I]. Qed.

Lemma pz_sub0 : forall W, sub_fp [] W.
Proof. intros W x _. exact I. Qed.

Lemma pz_sub2 : forall a1 b1 a2 b2 lo hi, lo <= a1 -> b1 <= hi -> lo <= a2 -> b2 <= hi ->
  sub_fp [(a1, b1); (a2, b2)] [(lo, hi)].
Proof.
  intros a1 b1 a2 b2 lo hi H1 H2 H3 H4 x Hx. cbn [outside] in *. destruct Hx as [Hx _].
  split; [lia|]. split; [lia | exact I].
Qed.

Lemma pz_sr_run : forall run acc, Forall (fun x => special x = false) run -> spieces_run acc run = [acc ++ run].
Proof.
  induction run as [|c run IH]; intros acc H; cbn [spieces_run]; [rewrite app_nil_r; reflexivity|].
  inversion H as [|? ? Hc Hr]; subst. rewrite Hc. rewrite IH by exact Hr. rewrite <- app_assoc. reflexivity.
Qed.

Lemma pz_sr_split : forall run c rest acc, Forall (fun x => special x = false) run -> special c = true ->
  spieces_run acc (run ++ c :: rest) = (acc ++ run) :: esc c :: spieces_run [] rest.
Proof.
  induction run as [|x run IH]; intros c rest acc H Hc; cbn [app spieces_run].
  - rewrite Hc, app_nil_r. reflexivity.
  - inversion H as [|? ? Hx Hr]; subst. rewrite Hx. rewrite IH by assumption. rewrite <- app_assoc. reflexivity.
Qed.

Lemma pz_skipn_cons : forall (l : list Z) k, (k < length l)%nat -> skipn k l = nth k l 0 :: skipn (S k) l.
Proof. induction l as [|x l IH]; intros [|k] H; cbn in *; try lia; [reflexivity|]. apply IH. lia. Qed.

Lemma pz_nth_skipn : forall (l : list Z) r i, nth i (skipn r l) 0 = nth (r + i) l 0.
Proof.
  intros l r. revert l. induction r as [|r IH]; intros [|x l] i; cbn; try reflexivity.
  - destruct i; reflexivity.
  - apply IH.
Qed.

Lemma pz_nth_firstn : forall (l : list Z) n i, (i < n)%nat -> nth i (firstn n l) 0 = nth i l 0.
Proof.
  intros l n. revert l. induction n as [|n IH]; intros [|x l] i H; try lia; cbn; [destruct i; reflexivity|].
  destruct i as [|i]; [reflexivity|]. apply IH. lia.
Qed.

Lemma pz_in_sub : forall (l : list Z) r n x, In x (firstn n (skipn r l)) -> In x l.
Proof.
  intros l r n x H. rewrite <- (firstn_skipn r l). apply in_or_app. right.
  rewrite <- (firstn_skipn n (skipn r l)). apply in_or_app. left. exact H.
Qed.

Lemma pz_in_skip : forall (l : list Z) r x, In x (skipn r l) -> In x l.
Proof. intros l r x H. rewrite <- (firstn_skipn r l). apply in_or_app. right. exact H. Qed.

Lemma pz_split_at : forall (bs : list Z) r j, 0 <= r <= j -> j < Z.of_nat (length bs) ->
  skipn (Z.to_nat r) bs =
  firstn (Z.to_nat (j - r)) (skipn (Z.to_nat r) bs) ++ nth (Z.to_nat j) bs 0 :: skipn (Z.to_nat (j + 1)) bs.
Proof.
  intros bs r j H1 H2. rewrite <- (firstn_skipn (Z.to_nat (j - r)) (skipn (Z.to_nat r) bs)) at 1. f_equal.
  rewrite skipn_skipn. replace (Z.to_nat (j - r) + Z.to_nat r)%nat with (Z.to_nat j) by lia.
  rewrite (pz_skipn_cons bs (Z.to_nat j)) by lia.
  replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia. reflexivity.
Qed.

Lemma pz_nospec_sub : forall bs r j, 0 <= r <= j ->
  (forall k, r <= k < j -> special (nth (Z.to_nat k) bs 0) = false) ->
  Forall (fun x => special x = false) (firstn (Z.to_nat (j - r)) (skipn (Z.to_nat r) bs)).
Proof.
  intros bs r j Hr NS. apply Forall_forall. intros x Hx. apply (In_nth _ _ 0) in Hx as (i & Hi & <-).
  rewrite length_firstn, length_skipn in Hi. rewrite pz_nth_firstn by lia. rewrite pz_nth_skipn.
  specialize (NS (r + Z.of_nat i)). replace (Z.to_nat (r + Z.of_nat i)) with (Z.to_nat r + i)%nat in NS by lia.
  apply NS. lia.
Qed.

Lemma pz_nospec_skip : forall bs r, 0 <= r ->
  (forall k, r <= k < Z.of_nat (length bs) -> special (nth (Z.to_nat k) bs 0) = false) ->
  Forall (fun x => special x = false) (skipn (Z.to_nat r) bs).
Proof.
  intros bs r Hr NS. apply Forall_forall. intros x Hx. apply (In_nth _ _ 0) in Hx as (i & Hi & <-).
  rewrite length_skipn in Hi. rewrite pz_nth_skipn.
  specialize (NS (r + Z.of_nat i)). replace (Z.to_nat (r + Z.of_nat i)) with (Z.to_nat r + i)%nat in NS by lia.
  apply NS. lia.
Qed.

Lemma pz_esc_len : forall c, (2 <= length (esc c) <= 6)%nat.
Proof.
  intros c. unfold esc.
  destruct (c =? 34); [cbn; lia|]. destruct (c =? 92); [cbn; lia|]. destruct (c =? 10); [cbn; lia|].
  destruct (c =? 9); [cbn; lia|]. destruct (c =? 13); cbn; lia.
Qed.

Lemma pz_sr_len : forall l acc, (length acc + length l <= length (concat (spieces_run acc l)))%nat.
Proof.
  induction l as [|c l IH]; intros acc; cbn [spieces_run].
  - cbn [concat]. rewrite app_nil_r. cbn [length]. lia.
  - destruct (special c).
    + cbn [concat]. rewrite !length_app. pose proof (IH []) as H. cbn [length] in H |- *.
      pose proof (pz_esc_len c). lia.
    + specialize (IH (acc ++ [c])). rewrite length_app in IH. cbn [length] in IH |- *. lia.
Qed.

Lemma pz_wstr_len : forall bs, Z.of_nat (length bs) + 2 <= Z.of_nat (length (wstr bs)).
Proof.
  intros bs. unfold wstr, spieces. cbn [concat]. rewrite concat_app, !length_app.
  pose proof (pz_sr_len bs []). cbn [length concat app] in *. lia.
Qed.

Lemma pz_hexd : forall d, 0 <= d < 16 -> 48 <= hexd d <= 102.
Proof. intros d Hd. unfold hexd. destruct (Z.ltb_spec d 10); lia. Qed.

Lemma pz_esc_ok : forall c, 0 <= c < 256 -> Forall (fun b => 0 < b < 256) (esc c).
Proof.
  intros c Hc. pose proof (pz_hexd (c / 16) ltac:(Z.div_mod_to_equations; lia)) as H1.
  pose proof (pz_hexd (c mod 16) ltac:(Z.div_mod_to_equations; lia)) as H2.
  unfold esc. destruct (c =? 34); [|destruct (c =? 92); [|destruct (c =? 10); [|destruct (c =? 9);
    [|destruct (c =? 13)]]]]; repeat (apply Forall_cons; [cbv beta; lia|]); apply Forall_nil.
Qed.

Lemma pz_ok_bytes : forall l, Forall (fun b => 0 < b < 256) l -> bytes_ok l.
Proof. intros l H. unfold bytes_ok. eapply Forall_impl; [|exact H]. cbv beta. intros a Ha. lia. Qed.

Lemma pz_hex4 : forall c, 0 <= c < 32 -> pf_hex4 c = [48; 48; hexd (c / 16); hexd (c mod 16)].
Proof.
  intros c Hc.
  assert (E : forall k : nat, (k < 32)%nat ->
    pf_hex4 (Z.of_nat k) = [48; 48; hexd (Z.of_nat k / 16); hexd (Z.of_nat k mod 16)]).
  { intros k Hk. do 32 (destruct k as [|k]; [reflexivity|]). lia. }
  replace c with (Z.of_nat (Z.to_nat c)) by lia. apply E. lia.
Qed.

Definition pz_fmtb (c : Z) : list Z := if (c =? 34) || (c =? 92) then [92; 37; 99] else [92; 117; 37; 48; 52; 120].
Definition pz_ps (c : Z) : list pf_piece := if (c =? 34) || (c =? 92) then [PLit 92; Pc] else [PLit 92; PLit 117; Px04].

Lemma pz_fmt_parse : forall c, pf_parse (pz_fmtb c) = Some (pz_ps c).
Proof. intros c. unfold pz_fmtb, pz_ps. destruct ((c =? 34) || (c =? 92)); reflexivity. Qed.

Lemma pz_fmt_len : forall c, Z.of_nat (length (pz_fmtb c)) <= 6.
Proof. intros c. unfold pz_fmtb. destruct ((c =? 34) || (c =? 92)); cbn; lia. Qed.

Lemma pz_fmt_text : forall c, special c = true -> 0 < c < 256 -> c <> 9 -> c <> 10 -> c <> 13 ->
  pf_text (pz_ps c) [AInt c] = Some (esc c).
Proof.
  intros c SP Hc C9 C10 C13. destruct (ps_special_inv c SP) as [-> | [-> | Hlt]]; [reflexivity | reflexivity |].
  unfold pz_ps. rewrite (proj2 (Z.eqb_neq c 34)) by lia. rewrite (proj2 (Z.eqb_neq c 92)) by lia.
  cbn [orb pf_text option_map]. rewrite pz_hex4 by lia. cbn [app]. unfold esc.
  rewrite (proj2 (Z.eqb_neq c 34)) by lia. rewrite (proj2 (Z.eqb_neq c 92)) by lia.
  rewrite (proj2 (Z.eqb_neq c 10)) by lia. rewrite (proj2 (Z.eqb_neq c 9)) by lia.
  rewrite (proj2 (Z.eqb_neq c 13)) by lia. reflexivity.
Qed.

Lemma pz_fmt_img : forall c m, mem_inv rsegs m -> bytes_at rsegs m (ps_fmt c) (pf_bytes (pz_fmtb c ++ [0])).
Proof.
  intros c m MI. unfold ps_fmt, pz_fmtb. destruct ((c =? 34) || (c =? 92));
    (apply ro_bytes_at; [exact MI | unfold PS_FMT_C, PS_FMT_U; lia | cbn; unfold PS_FMT_C, PS_FMT_U; lia
      | apply ro_bytes_b_sound; vm_compute; reflexivity]).
Qed.

Lemma pz_fmt_range : forall c, RO_LO <= ps_fmt c /\ ps_fmt c + 7 <= RO_END.
Proof. intros c. unfold ps_fmt, RO_LO, RO_END. destruct ((c =? 34) || (c =? 92)); unfold PS_FMT_C, PS_FMT_U; lia. Qed.

Lemma pz_img_free : forall D n, IMG_TOP <= D -> pf_img_free D n.
Proof.
  intros D n HD i Hi sg Hs Hin. pose proof reserved_top as T. rewrite forallb_forall in T.
  specialize (T sg Hs). cbv beta in T. apply Z.leb_le in T. lia.
Qed.

Lemma pz_rp_lit : forall z, 0 <= z < 2 ^ 64 -> z mod 2 = 0 -> ret_pc (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz He. apply ret_pc_even; assumption. Qed.

Lemma pz_bytes_pre : forall m A (str : list Z) slack, bytes_at rsegs m A (map (Z_to_bv 8) str ++ Z_to_bv 8 0 :: slack) ->
  bytes_at rsegs m A (map (Z_to_bv 8) (str ++ [0])).
Proof.
  intros m A str slack H. rewrite map_app. cbn [map].
  assert (E : map (Z_to_bv 8) str ++ Z_to_bv 8 0 :: slack = (map (Z_to_bv 8) str ++ [Z_to_bv 8 0]) ++ slack)
    by (rewrite <- app_assoc; reflexivity).
  rewrite E in H. exact (proj1 (proj1 (bytes_at_app rsegs _ _ _ _) H)).
Qed.

Section Esc.
Hypothesis SNP : snprintf_contract.
Hypothesis STL : strlen_contract.

Lemma pz_tail : forall (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o s r j c : Z)
    (str : list Z) (slack : list byte) (x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  PS_FRAME <= bv_unsigned sp -> bv_unsigned sp mod 8 = 0 ->
  bytes_at rsegs m (bv_unsigned sp - PS_FRAME + 32) (map (Z_to_bv 8) str ++ Z_to_bv 8 0 :: slack) ->
  Forall (fun b => 0 < b < 256) str -> Z.of_nat (length str) + 1 + Z.of_nat (length slack) = 8 ->
  mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (m' : word -> option byte) (y5 y6 y7 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
      ms' = ps_loop PS_PUT sp gp tp F fc m' o s r j (Z_to_bv 64 0x176ec) y5 y6 y7 x9 (Z_to_bv 64 o)
              (Z_to_bv 64 (bv_unsigned sp - PS_FRAME + 32)) (Z_to_bv 64 (Z.of_nat (length str))) y13 y14 y15 y16 y17
              (Z_to_bv 64 c) y28 y29 y30 y31 /\
      munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      bytes_at rsegs m' (bv_unsigned sp - PS_FRAME + 32) (map (Z_to_bv 8) str ++ Z_to_bv 8 0 :: slack))
    (ps_loop PS_STRLEN sp gp tp F fc m o s r j (Z_to_bv 64 0x176dc) x5 x6 x7 x9
       (Z_to_bv 64 (bv_unsigned sp - PS_FRAME + 32)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 c) x28 x29 x30 x31).
Proof using STL.
  intros sp gp tp F fc m o s r j c str slack x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 SP SP8 BY NZs LEN MI.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
  assert (PF : PS_FRAME = 144) by reflexivity.
  unfold ps_loop.
  eapply evt_cut.
  { eapply STL with (str := map (Z_to_bv 8) str) (slack := slack).
    - rewrite unsigned_lit by lia. exact BY.
    - intros Hin. apply in_map_iff in Hin as (b & Eb & Hb). rewrite Forall_forall in NZs. specialize (NZs b Hb).
      apply (f_equal bv_unsigned) in Eb. rewrite !Z_to_bv_unsigned in Eb. unfold bv_wrap, bv_modulus in Eb.
      change (2 ^ Z.of_N 8) with 256 in Eb. rewrite Z.mod_small in Eb by lia. rewrite Zmod_0_l in Eb. lia.
    - rewrite unsigned_lit by lia. rewrite length_map. Z.div_mod_to_equations. lia.
    - exact MI. }
  intros ms1 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI'
    & BY').
  rewrite (pz_rp_lit 0x176dc) by (first [lia | reflexivity]).
  eapply evt_cut; [eapply ps_after_strlen; exact SP|].
  intros ms2 ->. apply evt_done.
  exists m', t0', t1', t2', a3', a4', a5', a6', a7', t3', t4', t5', t6'.
  split; [rewrite length_map; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
  rewrite unsigned_lit in BY' by lia. exact BY'.
Qed.

Lemma pz_slack : forall m m' W A e (t : list byte),
  bytes_at rsegs m A e -> length e = 8%nat -> (length t <= 8)%nat -> munch W m m' ->
  disjoint_from W (A + Z.of_nat (length t)) (8 - Z.of_nat (length t)) ->
  bytes_at rsegs m' (A + Z.of_nat (length t)) (skipn (length t) e).
Proof.
  intros m m' W A e t BE Le Lt MU D.
  rewrite <- (firstn_skipn (length t) e) in BE. apply bytes_at_app in BE as [_ B2].
  rewrite length_firstn, Nat.min_l in B2 by lia.
  eapply bytes_at_transport; [exact B2 | exact MU |]. rewrite length_skipn, Le.
  replace (Z.of_nat (8 - length t)) with (8 - Z.of_nat (length t)) by lia. exact D.
Qed.

Lemma pz_esc_seg : forall (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o s r j c : Z)
    (e : list byte) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 canary : word)
    (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  special c = true -> 0 < c < 256 ->
  IMG_TOP + PS_FRAME + SNPRINTF_K <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < 2 ^ 63 ->
  rw_cells rsegs m (bv_unsigned sp - PS_FRAME) (ps_lits ++ CB 8 e :: ps_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  stk rsegs m (bv_unsigned sp - PS_FRAME - SNPRINTF_K) (bv_unsigned sp - PS_FRAME) ->
  mem_inv rsegs m -> MemNorm.task_mem rsegs m -> frm0 fc ->
  bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 canary) ->
  evt rsegs (fun ms' => exists (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte) (e' : list byte)
                 (y5 y6 y7 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
      ms' = ps_loop PS_PUT sp gp tp F' fc' m' o s r j (Z_to_bv 64 0x176ec) y5 y6 y7 x9 (Z_to_bv 64 o)
              (Z_to_bv 64 (bv_unsigned sp - PS_FRAME + 32)) (Z_to_bv 64 (Z.of_nat (length (esc c)))) y13 y14 y15 y16
              y17 (Z_to_bv 64 c) y28 y29 y30 y31 /\
      (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k) /\ frm0 fc' /\
      munch [(bv_unsigned sp - PS_FRAME - SNPRINTF_K, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
      mem_inv rsegs m' /\
      rw_cells rsegs m' (bv_unsigned sp - PS_FRAME) (ps_lits ++ CB 8 e' :: ps_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) /\
      bytes_at rsegs m' (bv_unsigned sp - PS_FRAME + 32) (map (Z_to_bv 8) (esc c ++ [0])))
    (ps_loop 0x17664 sp gp tp F fc m o s r j x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 c) x28 x29 x30 x31).
Proof using SNP STL.
  intros sp gp tp F fc m o s r j c e ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 canary
    x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 SPc Hc SPB SP16 SP63 FR ST MI TM FRM GG1 GG2.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
  assert (PF : PS_FRAME = 144) by reflexivity. assert (PK : SNPRINTF_K = 5936) by reflexivity.
  assert (PE : IMG_END = 0x55e20) by reflexivity. assert (IT : IMG_TOP = 0x60000) by reflexivity.
  assert (SP8 : bv_unsigned sp mod 8 = 0) by (Z.div_mod_to_equations; lia).
  destruct (pz_frame_parts _ _ _ _ FR) as (FL & FS & FV).
  destruct (pz_cell_bytes _ _ _ _ FS) as (BE & Le & WE).
  pose proof (pz_esc_len c) as LE. pose proof (pz_esc_ok c ltac:(lia)) as EOK.
  assert (D : (c = 9 \/ c = 10 \/ c = 13) \/ (c <> 9 /\ c <> 10 /\ c <> 13)) by lia.
  destruct D as [D | (C9 & C10 & C13)].
  - eapply evt_cut.
    { eapply (ps_after_run_store sp gp tp F fc m (bv_unsigned sp - PS_FRAME - SNPRINTF_K) o s r j c e
        ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31);
        [exact D | lia | exact FR | exact ST | exact MI]. }
    intros ms1 (m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    assert (L2 : length (esc c) = 2%nat) by (destruct D as [-> | [-> | ->]]; reflexivity).
    destruct (pz_frame_parts _ _ _ _ FR1) as (_ & FS1 & _).
    destruct (pz_cell_bytes _ _ _ _ FS1) as (BE1 & _ & _).
    assert (BY1 : bytes_at rsegs m1 (bv_unsigned sp - PS_FRAME + 32) (map (Z_to_bv 8) (esc c) ++ Z_to_bv 8 0 :: skipn 3 e)).
    { rewrite map_app, <- app_assoc in BE1. exact BE1. }
    eapply evt_cut.
    { eapply (pz_tail sp gp tp F fc m1 o s r j c (esc c) (skipn 3 e)); [lia | exact SP8 | exact BY1 | exact EOK | |
        exact MI1].
      rewrite length_skipn, Le, L2. reflexivity. }
    intros ms2 (m2 & y5 & y6 & y7 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & -> & MU2 & WM2 & MI2 & BY2).
    apply evt_done.
    exists F, fc, m2, (map (Z_to_bv 8) (esc c ++ [0]) ++ skipn 3 e), y5, y6, y7, y13, y14, y15, y16, y17, y28, y29, y30, y31.
    split; [reflexivity|]. split; [intros k _; reflexivity|]. split; [exact FRM|].
    split.
    { apply (munch_trans _ m m1 m2).
      - eapply munch_weaken; [|exact MU1]. apply pz_sub1; lia.
      - eapply munch_weaken; [|exact MU2]. apply pz_sub0. }
    split; [exact (wmono_trans rsegs m m1 m2 WM1 WM2)|]. split; [exact MI2|].
    split; [exact (rw_cells_transport rsegs [] m1 m2 _ _ FR1 MU2 WM2 I)|].
    exact (pz_bytes_pre _ _ _ _ BY2).
  - pose proof (pz_fmt_text c SPc Hc C9 C10 C13) as HT.
    pose proof (pz_fmt_range c) as FRg.
    eapply evt_cut.
    { eapply (ps_after_run_fmt sp gp tp F fc m o s r j c e ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
        x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31);
        [exact SPc | lia | exact C9 | exact C10 | exact C13 | lia | exact FR]. }
    intros ms1 ->. unfold ps_loop at 1.
    eapply evt_cut.
    { eapply SNP with (lo := bv_unsigned sp - PS_FRAME - SNPRINTF_K) (canary := canary) (fmt := pz_fmtb c)
        (ps := pz_ps c) (args := [AInt c]) (T := esc c) (junk := e).
      - rewrite unsigned_lit by (unfold RO_LO, RO_END in FRg; lia). exact (pz_fmt_img c m MI).
      - rewrite unsigned_lit by (unfold RO_LO, RO_END in FRg; lia). lia.
      - rewrite unsigned_lit by (unfold RO_LO, RO_END in FRg; lia). pose proof (pz_fmt_len c). lia.
      - exact (pz_fmt_parse c).
      - cbn [pf_args_ok pf_arg_ok]. split; [|exact I]. split; [lia|]. rewrite unsigned_lit by lia. reflexivity.
      - exact HT.
      - rewrite !unsigned_lit by lia. exact FS.
      - rewrite unsigned_lit by lia. lia.
      - lia.
      - rewrite unsigned_lit by lia. lia.
      - rewrite !unsigned_lit by lia. right. lia.
      - rewrite !unsigned_lit by lia. apply pz_img_free. lia.
      - rewrite unsigned_lit by lia. exact ST.
      - rewrite unsigned_lit by lia. lia.
      - lia.
      - rewrite unsigned_lit by lia. lia.
      - exact FRM.
      - exact MI.
      - exact TM.
      - exact GG1.
      - exact GG2. }
    intros ms2 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc' & m2 & ->
      & MU2 & WM2 & MI2 & TM2 & FRM2 & FK2 & ST2 & BY2).
    change (bv_unsigned (Z_to_bv 64 8)) with 8 in BY2, MU2.
    repeat match type of MU2 with context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) in MU2 by lia end.
    repeat match type of BY2 with context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) in BY2 by lia end.
    rewrite firstn_all2 in BY2, MU2 by lia.
    rewrite (pz_rp_lit 0x176d4) by (first [lia | reflexivity]).
    eapply evt_cut; [eapply ps_after_snprintf; lia|].
    intros ms3 ->.
    assert (LT : (length (map (Z_to_bv 8) (esc c ++ [0%Z])) <= 8)%nat)
      by (rewrite length_map, length_app; cbn [length]; lia).
    pose proof (pz_slack m m2 _ _ e _ BE Le LT MU2) as SL.
    assert (SL' : bytes_at rsegs m2 (bv_unsigned sp - PS_FRAME + 32 + Z.of_nat (length (map (Z_to_bv 8) (esc c ++ [0]))))
                    (skipn (length (map (Z_to_bv 8) (esc c ++ [0]))) e)).
    { apply SL. rewrite length_map, length_app. cbn [length disjoint_from]. repeat split; try exact I; lia. }
    assert (BY3 : bytes_at rsegs m2 (bv_unsigned sp - PS_FRAME + 32)
                    (map (Z_to_bv 8) (esc c) ++ Z_to_bv 8 0 :: skipn (length (map (Z_to_bv 8) (esc c ++ [0]))) e)).
    { assert (E : map (Z_to_bv 8) (esc c) ++ Z_to_bv 8 0 :: skipn (length (map (Z_to_bv 8) (esc c ++ [0]))) e =
                  map (Z_to_bv 8) (esc c ++ [0]) ++ skipn (length (map (Z_to_bv 8) (esc c ++ [0]))) e)
        by (rewrite map_app, <- app_assoc; reflexivity).
      rewrite E. apply bytes_at_app. split; [exact BY2 | exact SL']. }
    eapply evt_cut.
    { eapply (pz_tail sp gp tp Ft fc' m2 o s r j c (esc c)); [lia | exact SP8 | exact BY3 | exact EOK | | exact MI2].
      rewrite length_skipn, Le, length_map, length_app. cbn [length]. lia. }
    intros ms4 (m3 & y5 & y6 & y7 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & -> & MU3 & WM3 & MI3 & BY4).
    apply evt_done.
    exists Ft, fc', m3, (map (Z_to_bv 8) (esc c ++ [0]) ++ skipn (length (map (Z_to_bv 8) (esc c ++ [0]))) e),
      y5, y6, y7, y13, y14, y15, y16, y17, y28, y29, y30, y31.
    split; [reflexivity|]. split; [exact FK2|]. split; [exact FRM2|].
    split.
    { apply (munch_trans _ m m2 m3).
      - eapply munch_weaken; [|exact MU2]. apply pz_sub2; rewrite ?length_map, ?length_app; cbn [length];
          pose proof (pz_esc_len c); lia.
      - eapply munch_weaken; [|exact MU3]. apply pz_sub0. }
    split; [exact (wmono_trans rsegs m m2 m3 WM2 WM3)|]. split; [exact MI3|].
    split.
    { apply (rw_cells_transport rsegs [] m2 m3 _ _); [| exact MU3 | exact WM3 | exact I].
      apply pz_frame_mk.
      - eapply rw_cells_transport; [exact FL | exact MU2 | exact WM2 |]. pz_cs. repeat split; try exact I; lia.
      - apply pz_cell_mk.
        + rewrite length_app, length_skipn, Le. pose proof (pz_esc_len c). rewrite length_map, length_app. cbn [length].
          lia.
        + apply bytes_at_app. split; [exact BY2 | exact SL'].
        + exact (wr_at_transport rsegs m m2 _ _ WE WM2).
      - eapply rw_cells_transport; [exact FV | exact MU2 | exact WM2 |]. pz_cs. repeat split; try exact I; lia. }
    exact (pz_bytes_pre _ _ _ _ BY4).
Qed.

End Esc.

Lemma pz_not_out1 : forall lo hi z, ~ outside [(lo, hi)] z -> lo <= z < hi.
Proof.
  intros lo hi z H. destruct (Z_le_gt_dec lo z) as [H1|H1]; [destruct (Z_lt_ge_dec z hi) as [H2|H2]|].
  - lia.
  - exfalso. apply H. cbn [outside]. split; [lia | exact I].
  - exfalso. apply H. cbn [outside]. split; [lia | exact I].
Qed.

Lemma pz_xrel_mem : forall x y, pz_xrel x y -> mem_rel_cj rsegs (ms_mem x) (ms_mem y).
Proof. intros x y (_ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.

Lemma pz_next_mem : forall sp gp tp F fc m o' s' r bs' y, ps_next sp gp tp F fc m o' s' r bs' y -> ms_mem y = m.
Proof.
  intros sp gp tp F fc m o' s' r bs' y
    [(j & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & _ & _ & _ & ->) |
     (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & _ & ->)]; reflexivity.
Qed.

Lemma pz_reserved_low : forallb (fun sg => 0 <? bv_unsigned (fst sg)) (segments_reserved rsegs) = true.
Proof. vm_compute. reflexivity. Qed.

Section PS.
Context {rc : RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable RF : ResForm.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis GOTG : ms_got_guard B = GOT_GUARD.
Hypothesis GDG : ms_guard B = GUARD.
Hypothesis PUTC : forall fx' : FPState, @put_contract fx' rc B API RF.
Hypothesis SNP : snprintf_contract.
Hypothesis STL : strlen_contract.

Lemma pz_guard : forall L A m md, aa_MR API L A m md -> guard_cells m.
Proof.
  intros L A m md HM. destruct (ax_statics AX L A m md HM) as (W1 & (g & Hg & W2) & _).
  rewrite SEGS, GOTG, GDG in W1. rewrite SEGS, GDG in W2.
  split.
  - apply word_mem_iff; [unfold GOT_GUARD; lia | unfold GOT_GUARD; lia | exact W1].
  - exists (Z_to_bv 64 g). apply word_mem_iff; [unfold GUARD; lia | unfold GUARD; lia | exact W2].
Qed.

Lemma pz_q1_z : forall m, ro_agree rsegs m -> zbytes_at B m PS_Q1 [34].
Proof. intros m RO. apply (img_zbytes B SEGS); [exact RO | vm_compute; reflexivity]. Qed.

Lemma pz_q1_w : forall R Lam1 buf1, s_where B R Lam1 PS_Q1 1 buf1.
Proof.
  intros R Lam1 buf1. apply (img_where B SEGS _ _ _ _ _ [34]); [vm_compute; reflexivity | vm_compute; reflexivity |
    reflexivity].
Qed.

Lemma pz_lblock : forall L A m Lam peak cnt fail x k, ledger B L A m Lam peak cnt fail -> In (x, k) Lam ->
  0 <= k /\ In (x - 16, k + 16) (blocks L A).
Proof.
  intros L A m Lam peak cnt fail x k HL Hin. destruct HL as (_ & _ & _ & _ & _ & HF).
  rewrite Forall_forall in HF. destruct (HF _ Hin) as (Hk & Hb & _). split; assumption.
Qed.

Lemma pz_sw_keep : forall lo hi L1 A1 m1 md1 o1 buf1 st1 Lam1 peak1 b1 Q L2 A2 m2 md2 buf2 Lam2 peak2 b2 s1 n,
  wr_rel B API RF lo hi L1 A1 m1 md1 o1 buf1 st1 Lam1 peak1 b1 Q L2 A2 m2 md2 buf2 Lam2 peak2 b2 ->
  ledger B L1 A1 m1 Lam1 peak1 (w_cnt st1) (w_fail st1) ->
  str_where B Lam1 s1 n buf1 -> str_where B Lam2 s1 n buf2.
Proof.
  intros lo hi L1 A1 m1 md1 o1 buf1 st1 Lam1 peak1 b1 Q L2 A2 m2 md2 buf2 Lam2 peak2 b2 s1 n R LG SW.
  destruct R as (_ & _ & _ & _ & _ & _ & _ & _ & LM & _ & _ & _ & _ & _ & _ & FM & _).
  destruct SW as [IMG | (x & y & Hin & Hne & H1 & H2)]; [left; exact IMG | right].
  destruct (pz_lblock _ _ _ _ _ _ _ _ _ LG Hin) as [Hy Hb].
  pose proof (FM (x - 16) (y + 16) Hb ltac:(lia) ltac:(intros E; injection E as E _; lia)) as Hne2.
  exists x, y. split; [|split; [lia | lia]].
  destruct LM as [(_ & _ & -> & _) | (_ & l1 & l2 & Hl & -> & _)]; [exact Hin|].
  right. destruct Hl as [(_ & -> & ->) | (_ & ->)]; [exact Hin|].
  apply (in_mid _ _ _ _ Hin). intros E. injection E as E1 _. lia.
Qed.

Variable fx0 : FPState.
Variables (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (b0 : rf_R RF).
Variables (o s buf0 len0 cap0 failed0 : Z) (text0 bs : list Z) (Lam0 : list (Z * Z)) (peak0 cnt0 fail0 : Z).
Variable calls0 : list Z.
Hypothesis PRE0 : call_pre_k B (aa_MR API) PS_K L0 A0 regs0 mem0 md0.
Hypothesis SPT0 : spZ regs0 <= TASK_SIZE.
Hypothesis RO0 : ro_agree (ms_segs B) mem0.
Hypothesis INIT0 : st_init_done A0 = true.
Hypothesis FRM0 : frm0 (@fp_csr fx0).
Hypothesis R10 : getr regs0 10 = Z_to_bv 64 o.
Hypothesis R11 : getr regs0 11 = Z_to_bv 64 s.
Hypothesis PJ0 : pj_out_ok B mem0 Lam0 o buf0 len0 cap0 failed0 text0.
Hypothesis LG0 : ledger B L0 A0 mem0 Lam0 peak0 cnt0 fail0.
Hypothesis SPO : spZ regs0 <= o.
Hypothesis EO : off_errno B o 32.
Hypothesis ES : off_errno B (spZ regs0 - PS_K) PS_K.
Hypothesis SB0 : zbytes_at B mem0 s (bs ++ [0]).
Hypothesis BO : bytes_ok bs.
Hypothesis NZ : no_zero bs.
Hypothesis SW0 : str_where B Lam0 s (Z.of_nat (length bs) + 1) buf0.
Hypothesis NEED : len0 + Z.of_nat (length (wstr bs)) + 1 <= WMAX.
Hypothesis RES0 : rf_ok RF A0 b0.
Hypothesis ROOMS : wr_rooms RF b0 (mkW failed0 text0 cap0 cnt0 fail0 calls0) (spieces bs).

Local Abbreviation st0 := (mkW failed0 text0 cap0 cnt0 fail0 calls0).
Local Abbreviation SPW := (reg_get regs0 (Z_to_bv 5 2)).
Local Abbreviation GPW := (reg_get regs0 (Z_to_bv 5 3)).
Local Abbreviation TPW := (reg_get regs0 (Z_to_bv 5 4)).
Local Abbreviation FB := (bv_unsigned (reg_get regs0 (Z_to_bv 5 2)) - PS_FRAME).
Local Abbreviation SAVED := (ps_saved (reg_get regs0 (Z_to_bv 5 1)) (reg_get regs0 (Z_to_bv 5 8))
  (reg_get regs0 (Z_to_bv 5 9)) (reg_get regs0 (Z_to_bv 5 18)) (reg_get regs0 (Z_to_bv 5 19))
  (reg_get regs0 (Z_to_bv 5 20)) (reg_get regs0 (Z_to_bv 5 21)) (reg_get regs0 (Z_to_bv 5 22))
  (reg_get regs0 (Z_to_bv 5 23)) (reg_get regs0 (Z_to_bv 5 24)) (reg_get regs0 (Z_to_bv 5 25))
  (reg_get regs0 (Z_to_bv 5 26)) (reg_get regs0 (Z_to_bv 5 27))).
Local Abbreviation Post := (@put_string_ret fx0 rc B API RF L0 A0 regs0 mem0 md0 o buf0
  (mkW failed0 text0 cap0 cnt0 fail0 calls0) Lam0 peak0 b0 bs).

Lemma pz_spw : bv_unsigned SPW = spZ regs0.
Proof. unfold spZ. f_equal; symmetry; exact (pz_getr regs0 2 ltac:(lia)). Qed.

Lemma pz_sp : alloc_ceiling + PS_K <= spZ regs0 /\ spZ regs0 < 2 ^ 63 /\ spZ regs0 mod 16 = 0.
Proof.
  pose proof PRE0 as (_ & _ & _ & _ & H16 & HC & H63 & _). split; [exact HC|]. split; [exact H63 | exact H16].
Qed.

Lemma pz_spc16 : (spZ regs0 - PS_FRAME) mod 16 = 0.
Proof.
  pose proof pz_sp as (_ & _ & H). replace (spZ regs0 - PS_FRAME) with (spZ regs0 + (-9) * 16)
    by (unfold PS_FRAME; lia).
  rewrite Z_mod_plus_full. exact H.
Qed.

Lemma pz_slow : 0 <= s /\ s + Z.of_nat (length bs) + 1 <= alloc_ceiling.
Proof.
  pose proof (pz_wstr_len bs) as WL. pose proof ceil_big as CBg. unfold IMG_TOP in CBg.
  pose proof PJ0 as (_ & _ & _ & _ & _ & Rl & _). unfold WMAX in NEED.
  pose proof PRE0 as (HM0 & _).
  destruct SW0 as [(HI & HR) | (x & y & Hin & _ & H1 & H2)].
  - pose proof (in_img_low B SEGS s HI) as Hs. unfold IMG_TOP in Hs.
    pose proof (ro_addr_low (s + Z.of_nat (length bs)) (HR (Z.of_nat (length bs)) ltac:(lia)) ltac:(lia) ltac:(lia))
      as H. unfold IMG_TOP in H. lia.
  - pose proof (ledger_block_range B API _ _ _ _ _ _ _ _ _ _ HM0 LG0 Hin). lia.
Qed.

Lemma pz_spos : 0 < s.
Proof.
  pose proof PRE0 as (HM0 & _).
  destruct SW0 as [((_ & sg & Hs & Ha) & _) | (x & y & Hin & _ & H1 & _)].
  - rewrite SEGS in Hs. pose proof pz_reserved_low as T. rewrite forallb_forall in T.
    specialize (T sg Hs). apply Z.ltb_lt in T. lia.
  - pose proof (ledger_block_range B API _ _ _ _ _ _ _ _ _ _ HM0 LG0 Hin). lia.
Qed.

Lemma pz_s_norm : forall m, ro_agree rsegs m -> bytes_at rsegs m s (map (Z_to_bv 8) (bs ++ [0])) ->
  bytes_at rsegs (normalize_cj rsegs m) s (map (Z_to_bv 8) (bs ++ [0])).
Proof.
  intros m RO H. pose proof pz_slow as (S0 & S1). pose proof ceil_big as CBg.
  apply bytes_at_normalize_cj_low; [exact RO | | exact H].
  rewrite length_map, length_app. cbn [length]. unfold TASK_SIZE. lia.
Qed.

Definition pz_acc (fx1 : FPState) (L1 : layout) (A1 : astate) (m1 : word -> option byte) (md1 : Model)
    (buf1 : Z) (Lam1 : list (Z * Z)) (peak1 : Z) (b1 : rf_R RF) (P : list (list Z)) : Prop :=
  wr_rel B API RF (spZ regs0 - PS_K) (spZ regs0) L0 A0 mem0 md0 o buf0 st0 Lam0 peak0 b0 P L1 A1 m1 md1 buf1 Lam1
    peak1 b1 /\
  (forall k : reg, bv_unsigned k <> 10 -> reg_get (@fp_regs fx1) k = reg_get (@fp_regs fx0) k) /\
  frm0 (@fp_csr fx1) /\
  zbytes_at B m1 s (bs ++ [0]) /\ str_where B Lam1 s (Z.of_nat (length bs) + 1) buf1.

Lemma pz_acc_facts : forall fx1 L1 A1 m1 md1 buf1 Lam1 peak1 b1 P, pz_acc fx1 L1 A1 m1 md1 buf1 Lam1 peak1 b1 P ->
  aa_MR API L1 A1 m1 md1 /\ ro_agree rsegs m1 /\ m_halted md1 = None /\ m_vm_lazy md1 = [] /\
  (forall a, spZ regs0 - PS_K <= a < spZ regs0 -> writable_at rsegs m1 a) /\
  bytes_at rsegs m1 s (map (Z_to_bv 8) (bs ++ [0])).
Proof.
  intros fx1 L1 A1 m1 md1 buf1 Lam1 peak1 b1 P (WR & _ & _ & ZB & _).
  pose proof WR as (HM1 & _ & _ & (RO1 & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WR1).
  pose proof PRE0 as (_ & _ & _ & _ & _ & _ & _ & HWs0 & _).
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM1) as (Hh & Hl & _).
  pose proof pz_slow as (S0 & S1). pose proof ceil_big as CBg. unfold IMG_TOP in CBg.
  split; [exact HM1|]. split; [rewrite <- SEGS; exact RO1|]. split; [exact Hh|]. split; [exact Hl|].
  split.
  - intros a Ha. rewrite <- SEGS. apply WR1; [left; exact Ha|]. apply HWs0. exact Ha.
  - unfold zbytes_at in ZB. rewrite SEGS in ZB.
    apply zbytes_core; [lia | rewrite length_app; cbn [length]; lia | exact ZB].
Qed.

Lemma pz_acc_munch : forall fx1 fx2 L1 A1 m1 md1 buf1 Lam1 peak1 b1 P W m2,
  pz_acc fx1 L1 A1 m1 md1 buf1 Lam1 peak1 b1 P ->
  munch W m1 m2 -> wmono rsegs m1 m2 -> rm m1 m2 ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> spZ regs0 - PS_K <= x < spZ regs0) ->
  (forall k : reg, bv_unsigned k <> 10 -> reg_get (@fp_regs fx2) k = reg_get (@fp_regs fx1) k) ->
  frm0 (@fp_csr fx2) ->
  pz_acc fx2 L1 A1 m2 md1 buf1 Lam1 peak1 b1 P.
Proof.
  intros fx1 fx2 L1 A1 m1 md1 buf1 Lam1 peak1 b1 P W m2 (WR & FK & _ & ZB & SW) MU WM RM HW FK2 FR2.
  pose proof pz_sp as (SPa & SPb & SPc). pose proof pz_slow as (S0 & S1). pose proof ceil_big as CBg.
  unfold IMG_TOP in CBg. assert (PK : PS_K = 8496) by reflexivity.
  split; [|split; [|split; [|split]]].
  - eapply (wr_rel_munch B API RF SEGS); [exact WR | exact MU | exact WM | exact RM | |].
    + intros x Hx Hn. pose proof (HW x Hx Hn). split; lia.
    + lia.
  - intros k Hk. rewrite FK2 by exact Hk. apply FK. exact Hk.
  - exact FR2.
  - intros i Hi. rewrite <- (ZB i Hi). rewrite length_app in Hi. cbn [length] in Hi.
    assert (Out : outside W (s + i)).
    { destruct (outside_dec W (s + i)) as [Ho|Hn]; [exact Ho|]. exfalso.
      pose proof (HW (s + i) ltac:(lia) Hn). lia. }
    exact (proj1 (raw_mbyte (ms_segs B) m1 m2 (s + i) (munch_raw W m1 m2 (s + i) MU ltac:(lia) Out))).
  - exact SW.
Qed.

Lemma pz_s_keep : forall L1 A1 m1 Lam1 peak1 cnt1 fail1 buf1 m2,
  ledger B L1 A1 m1 Lam1 peak1 cnt1 fail1 -> ro_agree rsegs m1 -> ro_agree rsegs m2 ->
  keeps B L1 A1 m1 m2 (buf1 - 16) -> str_where B Lam1 s (Z.of_nat (length bs) + 1) buf1 ->
  zbytes_at B m1 s (bs ++ [0]) -> zbytes_at B m2 s (bs ++ [0]).
Proof.
  intros L1 A1 m1 Lam1 peak1 cnt1 fail1 buf1 m2 LG RO1 RO2 KP SW ZB i Hi. rewrite <- (ZB i Hi).
  rewrite length_app in Hi. cbn [length] in Hi.
  destruct SW as [(_ & HR) | (x & y & Hin & Hne & H1 & H2)].
  - rewrite SEGS. rewrite !mbyte_mrd, (RO2 _ (HR i ltac:(lia))), (RO1 _ (HR i ltac:(lia))). reflexivity.
  - destruct (pz_lblock _ _ _ _ _ _ _ _ _ LG Hin) as [Hy Hb].
    replace (s + i) with (x - 16 + (s + i - (x - 16))) by lia.
    apply (KP (x - 16) (y + 16) (s + i - (x - 16)) Hb); lia.
Qed.

Lemma pz_zsub : forall m r n, zbytes_at B m s (bs ++ [0]) -> 0 <= r -> 0 <= n -> r + n <= Z.of_nat (length bs) ->
  zbytes_at B m (s + r) (firstn (Z.to_nat n) (skipn (Z.to_nat r) bs)).
Proof.
  intros m r n ZB Hr Hn Hrn i Hi. rewrite length_firstn, length_skipn in Hi.
  replace (s + r + i) with (s + (r + i)) by lia.
  rewrite (ZB (r + i)) by (rewrite length_app; cbn [length]; lia).
  rewrite pz_nth_firstn by lia. rewrite pz_nth_skipn. rewrite app_nth1 by lia.
  replace (Z.to_nat r + Z.to_nat i)%nat with (Z.to_nat (r + i)) by lia. reflexivity.
Qed.

Lemma pz_zskip : forall m r, zbytes_at B m s (bs ++ [0]) -> 0 <= r <= Z.of_nat (length bs) ->
  zbytes_at B m (s + r) (skipn (Z.to_nat r) bs).
Proof.
  intros m r ZB Hr i Hi. rewrite length_skipn in Hi.
  replace (s + r + i) with (s + (r + i)) by lia.
  rewrite (ZB (r + i)) by (rewrite length_app; cbn [length]; lia).
  rewrite pz_nth_skipn, app_nth1 by lia.
  replace (Z.to_nat r + Z.to_nat i)%nat with (Z.to_nat (r + i)) by lia. reflexivity.
Qed.

Lemma pz_bok_sub : forall r n, bytes_ok (firstn n (skipn r bs)).
Proof.
  intros r n. apply Forall_forall. intros x Hx. exact (proj1 (Forall_forall _ _) BO x (pz_in_sub _ _ _ _ Hx)).
Qed.

Lemma pz_bok_skip : forall r, bytes_ok (skipn r bs).
Proof. intros r. apply Forall_forall. intros x Hx. exact (proj1 (Forall_forall _ _) BO x (pz_in_skip _ _ _ Hx)). Qed.

Lemma pz_swhere : forall R Lam1 buf1 r n, str_where B Lam1 s (Z.of_nat (length bs) + 1) buf1 ->
  0 <= r <= Z.of_nat (length bs) -> 0 <= n -> r + n <= Z.of_nat (length bs) ->
  s_where B R Lam1 (s + r) n buf1.
Proof.
  intros R Lam1 buf1 r n SW Hr Hn Hrn. pose proof pz_slow as (S0 & S1). pose proof ceil_big as CBg.
  unfold IMG_TOP in CBg.
  destruct SW as [(HI & HR) | (x & y & Hin & Hne & H1 & H2)].
  - right. left. split.
    + apply (ro_in_img B SEGS (s + r)); [lia | exact (HR r ltac:(lia))].
    + intros i Hi. replace (s + r + i) with (s + (r + i)) by lia. apply HR. lia.
  - right. right. exists x, y. split; [exact Hin|]. split; [exact Hne|]. lia.
Qed.

Lemma pz_put_step : forall (fx1 : FPState) x (R : bvmap 5 word) m0 md1 L1 A1 buf1 Lam1 peak1 b1 P q Rest src spc,
  pz_xrel x (MS R (@fp_regs fx1) (Z_to_bv 64 PS_PUT) (@fp_csr fx1) None m0 (PropExec.seg_rom rsegs)) ->
  getr R 10 = Z_to_bv 64 o -> getr R 11 = Z_to_bv 64 src -> getr R 12 = Z_to_bv 64 (Z.of_nat (length q)) ->
  getr R 4 = getr regs0 4 -> YK0s.ret_ok (getr R 1) -> spZ R = spc ->
  spc mod 16 = 0 -> spZ regs0 - PS_K + PUT_K <= spc <= spZ regs0 ->
  pz_acc fx1 L1 A1 (ms_mem x) md1 buf1 Lam1 peak1 b1 P ->
  P ++ q :: Rest = spieces bs ->
  zbytes_at B (ms_mem x) src q -> bytes_ok q -> 0 <= src < 2 ^ 64 -> src + Z.of_nat (length q) <= 2 ^ 64 ->
  s_where B R Lam1 src (Z.of_nat (length q)) buf1 -> (src + Z.of_nat (length q) <= o \/ o + 32 <= src) ->
  (forall L2 A2 regs2 mem2 md2 buf2 Lam2 peak2 b2,
     regs_preserved R regs2 ->
     wr_rel B API RF (spc - PUT_K) spc L1 A1 (ms_mem x) md1 o buf1 (putN st0 P) Lam1 peak1 b1 [q]
       L2 A2 mem2 md2 buf2 Lam2 peak2 b2 ->
     pz_acc fx1 L2 A2 mem2 md2 buf2 Lam2 peak2 b2 (P ++ [q]) ->
     SR rsegs (mkCfg (@YK11.mkst fx1 regs2 (getr R 1) mem2 (YK11.seg_rom rsegs)) md2) Post) ->
  SR rsegs (mkCfg x md1) Post.
Proof.
  intros fx1 x R m0 md1 L1 A1 buf1 Lam1 peak1 b1 P q Rest src spc XR G10 G11 G12 G4 GRA GSP SP16 SPR ACC SPL ZB QB
    SRC SRCN SWQ SOQ K.
  destruct (pz_xrel_eqv _ _ _ _ _ _ _ _ XR) as [EQV _].
  pose proof pz_sp as (SPa & SPb & SPc).
  pose proof PRE0 as (HM0 & HWF0 & HB0 & Hra0 & Hal0 & Hceil0 & Hsp0 & HWs0 & Htp0 & HWe0 & Haux0).
  pose proof PJ0 as (_ & _ & _ & _ & _ & _ & Rc0 & _).
  destruct (pz_acc_facts _ _ _ _ _ _ _ _ _ _ ACC) as (HM1 & RO1 & _ & _ & WT1 & _).
  pose proof ACC as (WR & FK & FRM & ZBs & SWs).
  pose proof WR as (_ & HWF1 & HB1 & _ & PJ1 & LG1 & RS1 & EB1 & _ & _ & _ & IN1 & _ & _ & _ & _ & _ & WR1).
  assert (PK : PS_K = 144 + PUT_K) by reflexivity. assert (PU : PUT_K = 8352) by reflexivity.
  pose proof ceil_big as CBg. unfold IMG_TOP in CBg.
  assert (G : forall k, getr (ms_regs x) k = getr R k) by (intros k; exact (eqv_getr _ _ _ _ _ _ _ x k EQV)).
  assert (S1 : spZ (ms_regs x) = spc) by (unfold spZ; rewrite G; exact GSP).
  assert (NQ : Z.of_nat (length (w_text (putN st0 P))) + Z.of_nat (length q) + 1 <= WMAX).
  { pose proof (putN_text P st0) as T1. cbn [w_text] in T1.
    assert (T2 : Z.of_nat (length (concat P)) + Z.of_nat (length q) <= Z.of_nat (length (wstr bs))).
    { unfold wstr. rewrite <- SPL. rewrite concat_app. cbn [concat]. rewrite !length_app. lia. }
    pose proof PJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LT0 & _). lia. }
  rewrite (eqv_shape _ _ _ _ EQV).
  rewrite <- SEGS.
  apply (@put_call fx1 rc B API RF SEGS AX (PUTC fx1) PS_K (spZ regs0) L1 A1 (ms_regs x) (ms_mem x) md1 o src
    (Z.of_nat (length q)) q buf1 (putN st0 P) Lam1 peak1 b1 Post).
  - rewrite S1. lia.
  - rewrite S1. lia.
  - exact Hceil0.
  - exact Hsp0.
  - rewrite S1. exact SP16.
  - intros a Ha. rewrite SEGS. apply WT1. exact Ha.
  - intros a Ha. apply WR1; [right; exact Ha|]. apply HWe0. exact Ha.
  - rewrite G, G4. exact Htp0.
  - rewrite G. exact GRA.
  - exact HM1.
  - exact HWF1.
  - exact HB1.
  - exact (IN1 INIT0).
  - rewrite SEGS. exact RO1.
  - rewrite G. exact G10.
  - rewrite G. exact G11.
  - rewrite G. exact G12.
  - exact PJ1.
  - exact LG1.
  - exact RS1.
  - exact SPO.
  - exact EO.
  - exact ES.
  - exact ZB.
  - reflexivity.
  - exact QB.
  - exact SRC.
  - exact SRCN.
  - unfold s_where in SWQ |- *. rewrite S1. rewrite GSP in SWQ. exact SWQ.
  - exact SOQ.
  - exact NQ.
  - pose proof ROOMS as RM. rewrite <- SPL in RM. apply (proj1 (wr_rooms_app RF P (q :: Rest) b0 st0)) in RM.
    destruct RM as [_ RM]. cbn [wr_rooms] in RM. destruct RM as [RM _]. rewrite EB1. exact RM.
  - intros regs1 L2 A2 mem2 md2 buf2 Lam2 peak2 b2 RP WRN. rewrite S1 in WRN. rewrite G, SEGS.
    pose proof WRN as (HM2 & _ & _ & (RO2 & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & KP2 & _ & _ & _).
    apply (K L2 A2 regs1 mem2 md2 buf2 Lam2 peak2 b2).
    + intros r Hr. rewrite (RP r Hr). apply G.
    + exact WRN.
    + split; [|split; [exact FK|split; [exact FRM|split]]].
      * eapply (wr_rel_app B API RF SEGS AX CTX); [exact HM0 | cbn [w_cap]; lia | exact WR |].
        eapply (wr_rel_widen B API RF); [exact HM1 | | | | | exact WRN]; lia.
      * eapply pz_s_keep; [exact LG1 | exact RO1 | rewrite <- SEGS; exact RO2 | exact KP2 | exact SWs | exact ZBs].
      * eapply pz_sw_keep; [exact WRN | exact LG1 | exact SWs].
Qed.

Lemma pz_fin : forall r (fx1 : FPState) x m0 L1 A1 md1 buf1 Lam1 peak1 b1 P junk
    (x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
  0 <= r <= Z.of_nat (length bs) ->
  (forall k, r <= k < Z.of_nat (length bs) -> special (nth (Z.to_nat k) bs 0) = false) ->
  P ++ spieces_run [] (skipn (Z.to_nat r) bs) ++ [[34]] = spieces bs ->
  x12 = Z_to_bv 64 (Z.of_nat (length bs) - r) ->
  pz_xrel x (MS (mkR (Z_to_bv 64 0x17724) (Z_to_bv 64 FB) GPW TPW x5 x6 x7
                  (Z_to_bv 64 o) x9 (Z_to_bv 64 o) (Z_to_bv 64 (s + r)) x12 x13 x14 x15 x16 x17
                  x18 x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 (s + r)) x28 x29 x30 x31)
             (@fp_regs fx1) (Z_to_bv 64 PS_PUT) (@fp_csr fx1) None m0 (PropExec.seg_rom rsegs)) ->
  pz_acc fx1 L1 A1 (ms_mem x) md1 buf1 Lam1 peak1 b1 P ->
  rw_cells rsegs (ms_mem x) FB (CB 40 junk :: SAVED) ->
  SR rsegs (mkCfg x md1) Post.
Proof.
  intros r fx1 x m0 L1 A1 md1 buf1 Lam1 peak1 b1 P junk x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
    x24 x25 x26 x28 x29 x30 x31 Hr NS SPL E12 XR ACC FR.
  pose proof pz_spw as SPE. pose proof pz_sp as (SPa & SPb & SPc). pose proof pz_slow as (S0 & S1).
  pose proof pz_spc16 as SP16. pose proof ceil_big as CBg. unfold IMG_TOP in CBg.
  pose proof PRE0 as (HM0 & HWF0 & HB0 & Hra0 & _).
  assert (PF : PS_FRAME = 144) by reflexivity. assert (PK : PS_K = 144 + PUT_K) by reflexivity.
  assert (PU : PUT_K = 8352) by reflexivity.
  pose proof ACC as (_ & _ & FRM1 & ZBs & SWs).
  destruct (pz_acc_facts _ _ _ _ _ _ _ _ _ _ ACC) as (HM1 & _).
  assert (NSF : Forall (fun z => special z = false) (skipn (Z.to_nat r) bs)) by (apply pz_nospec_skip; [lia | exact NS]).
  rewrite (pz_sr_run _ [] NSF) in SPL. cbn [app] in SPL.
  assert (LQ : Z.of_nat (length (skipn (Z.to_nat r) bs)) = Z.of_nat (length bs) - r) by (rewrite length_skipn; lia).
  eapply (pz_put_step fx1 x _ m0 md1 L1 A1 buf1 Lam1 peak1 b1 P (skipn (Z.to_nat r) bs) [[34]] (s + r)
    (spZ regs0 - PS_FRAME) XR).
  - reflexivity.
  - reflexivity.
  - rewrite LQ. exact E12.
  - exact (eq_sym (pz_getr regs0 4 ltac:(lia))).
  - change (YK0s.ret_ok (Z_to_bv 64 0x17724)). apply ret_ok_lit; [lia | reflexivity].
  - rewrite pz_spZ_mkR, unsigned_lit by lia. lia.
  - exact SP16.
  - lia.
  - exact ACC.
  - exact SPL.
  - apply pz_zskip; [exact ZBs | lia].
  - apply pz_bok_skip.
  - lia.
  - lia.
  - rewrite LQ. apply pz_swhere; [exact SWs | lia | lia | lia].
  - left. lia.
  - intros L2 A2 regs2 mem2 md2 buf2 Lam2 peak2 b2 RP WRN ACC2.
    destruct (pz_acc_facts _ _ _ _ _ _ _ _ _ _ ACC2) as (HM2 & RO2 & Hh2 & Hl2 & WT2 & _).
    assert (FR2 : rw_cells rsegs mem2 FB (CB 40 junk :: SAVED)).
    { eapply (wr_cells B API RF SEGS); [exact HM1 | exact WRN | exact FR | lia | lia | left; pz_cs; lia |].
      eapply (off_errno_sub B); [exact ES | lia | pz_cs; lia]. }
    eapply pz_kA_after; [exact RP | exact Hh2 | exact Hl2 | exact RO2 | |].
    { eapply (ps_after_final SPW GPW TPW _ _ (normalize_cj rsegs mem2) (spZ regs0 - PS_K) o junk).
      - apply pz_rw_norm; [exact RO2 | exact FR2 | unfold IMG_TOP; lia | pz_cs; lia].
      - apply pz_stk_norm; [apply stk_hi; [unfold IMG_TOP; lia | lia | intros a Ha; apply WT2; lia] | unfold IMG_TOP; lia
          | lia].
      - lia. }
    intros x1 y1 (-> & _) XR1 HO1 RM1.
    destruct (pz_xrel_eqv _ _ _ _ _ _ _ _ XR1) as [_ HR1].
    destruct (pz_back [] mem2 (normalize_cj rsegs mem2) x1 RO2 HR1 HO1 (munch_refl [] _) (wmono_refl rsegs _))
      as (MU1 & WM1 & RO1').
    assert (ACC3 : pz_acc fx1 L2 A2 (ms_mem x1) md2 buf2 Lam2 peak2 b2 (P ++ [skipn (Z.to_nat r) bs])).
    { eapply pz_acc_munch; [exact ACC2 | exact MU1 | exact WM1 | exact RM1 | | intros k _; reflexivity | exact FRM1].
      intros z _ Hn. exfalso. apply Hn. exact I. }
    eapply (pz_put_step fx1 x1 _ (normalize_cj rsegs mem2) md2 L2 A2 buf2 Lam2 peak2 b2 (P ++ [skipn (Z.to_nat r) bs])
      [34] [] PS_Q1 (spZ regs0) XR1).
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + exact (eq_sym (pz_getr regs0 4 ltac:(lia))).
    + change (YK0s.ret_ok (reg_get regs0 (Z_to_bv 5 1))). rewrite <- (pz_getr regs0 1) by lia. exact Hra0.
    + rewrite pz_spZ_mkR. exact SPE.
    + exact SPc.
    + lia.
    + exact ACC3.
    + rewrite <- app_assoc. exact SPL.
    + exact (pz_q1_z _ RO1').
    + constructor; [cbv beta; lia | constructor].
    + unfold PS_Q1. lia.
    + unfold PS_Q1. cbn [length]. lia.
    + apply pz_q1_w.
    + left. unfold PS_Q1. cbn [length]. lia.
    + intros L3 A3 regs3 mem3 md3 buf3 Lam3 peak3 b3 RP3 _ ACC4.
      destruct ACC4 as (WR4 & FK4 & FRM4 & _ & _).
      pose proof WR4 as (HM4 & _).
      apply SR_ret. unfold put_string_ret. exists fx1. split; [exact FK4|]. split; [exact FRM4|].
      split; [exact (pz_guard L3 A3 mem3 md3 HM4)|].
      unfold wr_ret. exists L3, A3, regs3, mem3, md3, buf3, Lam3, peak3, b3.
      split; [rewrite SEGS; f_equal; f_equal; exact (eq_sym (pz_getr regs0 1 ltac:(lia)))|].
      split.
      { intros k Hk. rewrite (RP3 k Hk). rewrite (pz_getr regs0 k) by (unfold callee_saved in Hk; lia).
        unfold callee_saved in Hk.
        destruct Hk as [->|[->|[->|[->|[->|Hk]]]]]; [reflexivity .. |].
        assert (Hk' : k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27)
          by lia.
        repeat (destruct Hk' as [->|Hk']; [reflexivity|]). subst k. reflexivity. }
      rewrite <- app_assoc in WR4. rewrite <- SPL. exact WR4.
Qed.

Lemma pz_loop : forall (n : nat) r (fx1 : FPState) x y0 m0 L1 A1 md1 buf1 Lam1 peak1 b1 P e,
  Z.to_nat (Z.of_nat (length bs) - r) = n -> 0 <= r <= Z.of_nat (length bs) ->
  P ++ spieces_run [] (skipn (Z.to_nat r) bs) ++ [[34]] = spieces bs ->
  ps_next SPW GPW TPW (@fp_regs fx1) (@fp_csr fx1) m0 o s r bs y0 -> pz_xrel x y0 ->
  pz_acc fx1 L1 A1 (ms_mem x) md1 buf1 Lam1 peak1 b1 P ->
  rw_cells rsegs (ms_mem x) FB (ps_lits ++ CB 8 e :: SAVED) ->
  SR rsegs (mkCfg x md1) Post.
Proof.
  induction n as [n IH] using lt_wf_ind.
  intros r fx1 x y0 m0 L1 A1 md1 buf1 Lam1 peak1 b1 P e En Hr SPL HN XR ACC FR.
  pose proof pz_spw as SPE. pose proof pz_sp as (SPa & SPb & SPc). pose proof pz_slow as (S0 & S1).
  pose proof pz_spc16 as SP16. pose proof ceil_big as CBg. unfold IMG_TOP in CBg.
  assert (PF : PS_FRAME = 144) by reflexivity. assert (PK : PS_K = 144 + PUT_K) by reflexivity.
  assert (PU : PUT_K = 8352) by reflexivity. assert (SK : SNPRINTF_K = 5936) by reflexivity.
  destruct HN as [(j & x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & Hj & SPj & NSj & ->) |
                  (x5 & x6 & x7 & x9 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 & x21 & x22 & x23 & x24 & x25 &
                   x26 & x28 & x29 & x30 & x31 & NS & ->)].
  2: { destruct (ps_frame_forget _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as [junk FR'].
       exact (pz_fin r fx1 x m0 L1 A1 md1 buf1 Lam1 peak1 b1 P junk x5 x6 x7 x9 _ x13 x14 x15 x16 x17 x18 x19 x20
         x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 Hr NS SPL eq_refl XR ACC FR'). }
  pose proof (ps_byte bs j BO NZ ltac:(lia)) as Hc.
  pose proof (pz_nospec_sub bs r j ltac:(lia) NSj) as NSR.
  assert (SPLIT : spieces_run [] (skipn (Z.to_nat r) bs) =
    firstn (Z.to_nat (j - r)) (skipn (Z.to_nat r) bs) :: esc (nth (Z.to_nat j) bs 0) ::
    spieces_run [] (skipn (Z.to_nat (j + 1)) bs)).
  { rewrite (pz_split_at bs r j ltac:(lia) ltac:(lia)) at 1. rewrite (pz_sr_split _ _ _ [] NSR SPj). reflexivity. }
  rewrite SPLIT in SPL.
  assert (LR : Z.of_nat (length (firstn (Z.to_nat (j - r)) (skipn (Z.to_nat r) bs))) = j - r)
    by (rewrite length_firstn, length_skipn; lia).
  pose proof ACC as (_ & _ & FRM1 & ZBs & SWs).
  destruct (pz_acc_facts _ _ _ _ _ _ _ _ _ _ ACC) as (HM1 & _).
  unfold ps_loop in XR.
  eapply (pz_put_step fx1 x _ m0 md1 L1 A1 buf1 Lam1 peak1 b1 P (firstn (Z.to_nat (j - r)) (skipn (Z.to_nat r) bs))
    (esc (nth (Z.to_nat j) bs 0) :: spieces_run [] (skipn (Z.to_nat (j + 1)) bs) ++ [[34]]) (s + r)
    (spZ regs0 - PS_FRAME) XR).
  - reflexivity.
  - reflexivity.
  - rewrite LR. reflexivity.
  - exact (eq_sym (pz_getr regs0 4 ltac:(lia))).
  - change (YK0s.ret_ok (Z_to_bv 64 0x17664)). apply ret_ok_lit; [lia | reflexivity].
  - rewrite pz_spZ_mkR, unsigned_lit by lia. lia.
  - exact SP16.
  - lia.
  - exact ACC.
  - exact SPL.
  - apply pz_zsub; [exact ZBs | lia | lia | lia].
  - apply pz_bok_sub.
  - lia.
  - rewrite LR. lia.
  - rewrite LR. apply pz_swhere; [exact SWs | lia | lia | lia].
  - left. rewrite LR. lia.
  - intros L2 A2 regs2 mem2 md2 buf2 Lam2 peak2 b2 RP WRN ACC2.
    destruct (pz_acc_facts _ _ _ _ _ _ _ _ _ _ ACC2) as (HM2 & RO2 & Hh2 & Hl2 & WT2 & _).
    assert (FR2 : rw_cells rsegs mem2 FB (ps_lits ++ CB 8 e :: SAVED)).
    { eapply (wr_cells B API RF SEGS); [exact HM1 | exact WRN | exact FR | lia | lia | left; pz_cs; lia |].
      eapply (off_errno_sub B); [exact ES | lia | pz_cs; lia]. }
    destruct (pz_guard L2 A2 mem2 md2 HM2) as [GG1 (canary & GG2)].
    eapply pz_kA_after; [exact RP | exact Hh2 | exact Hl2 | exact RO2 | |].
    { eapply (pz_esc_seg SNP STL SPW GPW TPW _ _ (normalize_cj rsegs mem2) o s r j (nth (Z.to_nat j) bs 0) e
        _ _ _ _ _ _ _ _ _ _ _ _ _ canary).
      - exact SPj.
      - lia.
      - unfold IMG_TOP. lia.
      - rewrite SPE. exact SPc.
      - lia.
      - apply pz_rw_norm; [exact RO2 | exact FR2 | unfold IMG_TOP; lia | pz_cs; lia].
      - apply pz_stk_norm; [apply stk_hi; [unfold IMG_TOP; lia | lia | intros a Ha; apply WT2; lia] | unfold IMG_TOP; lia
          | lia].
      - exact (mem_inv_cj_inv rsegs _ (mem_inv_cj_normalize rsegs mem2)).
      - exact (mem_inv_cj_task rsegs _ (mem_inv_cj_normalize rsegs mem2)).
      - exact FRM1.
      - apply bytes_at_normalize_cj_low; [exact RO2 | rewrite length_le8; unfold GOT_GUARD, TASK_SIZE; lia | exact GG1].
      - apply bytes_at_normalize_cj_low; [exact RO2 | rewrite length_le8; unfold GUARD, TASK_SIZE; lia | exact GG2]. }
    intros x1 y1 HQ XR1 HO1 RM1.
    destruct HQ as (F' & fc' & m0' & e' & y5 & y6 & y7 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & -> & FK'
      & FRM' & MU' & WM' & MI' & FR' & BYS).
    unfold ps_loop in XR1.
    destruct (pz_xrel_eqv _ _ _ _ _ _ _ _ XR1) as [_ HR1].
    destruct (pz_back _ mem2 m0' x1 RO2 HR1 HO1 MU' WM') as (MU1 & WM1 & RO1').
    assert (ACC3 : pz_acc (YK11.mkFP F' fc') L2 A2 (ms_mem x1) md2 buf2 Lam2 peak2 b2
                     (P ++ [firstn (Z.to_nat (j - r)) (skipn (Z.to_nat r) bs)])).
    { eapply pz_acc_munch; [exact ACC2 | exact MU1 | exact WM1 | exact RM1 | | exact FK' | exact FRM'].
      intros z Hz Hn. apply pz_not_out1 in Hn. rewrite SPE in Hn. lia. }
    assert (FR3 : rw_cells rsegs (ms_mem x1) FB (ps_lits ++ CB 8 e' :: SAVED)) by exact (pz_rw_rel _ _ _ _ HR1 FR').
    assert (BY3 : bytes_at rsegs (ms_mem x1) (FB + 32) (map (Z_to_bv 8) (esc (nth (Z.to_nat j) bs 0) ++ [0])))
      by exact (bytes_at_rel_cj rsegs _ _ _ _ HR1 BYS).
    pose proof (pz_esc_len (nth (Z.to_nat j) bs 0)) as LE.
    pose proof (pz_esc_ok (nth (Z.to_nat j) bs 0) ltac:(lia)) as EOK.
    eapply (pz_put_step (YK11.mkFP F' fc') x1 _ m0' md2 L2 A2 buf2 Lam2 peak2 b2
      (P ++ [firstn (Z.to_nat (j - r)) (skipn (Z.to_nat r) bs)]) (esc (nth (Z.to_nat j) bs 0))
      (spieces_run [] (skipn (Z.to_nat (j + 1)) bs) ++ [[34]]) (FB + 32) (spZ regs0 - PS_FRAME) XR1).
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + exact (eq_sym (pz_getr regs0 4 ltac:(lia))).
    + change (YK0s.ret_ok (Z_to_bv 64 0x176ec)). apply ret_ok_lit; [lia | reflexivity].
    + rewrite pz_spZ_mkR, unsigned_lit by lia. lia.
    + exact SP16.
    + lia.
    + exact ACC3.
    + rewrite <- app_assoc. exact SPL.
    + unfold zbytes_at. rewrite SEGS.
      apply (proj2 (zbytes_core (ms_mem x1) (FB + 32) (esc (nth (Z.to_nat j) bs 0)) ltac:(lia) ltac:(lia))).
      rewrite map_app in BY3. exact (proj1 (proj1 (bytes_at_app rsegs _ _ _ _) BY3)).
    + exact (pz_ok_bytes _ EOK).
    + lia.
    + lia.
    + left. split; [rewrite pz_spZ_mkR, unsigned_lit by lia; lia|]. unfold off_errno in *. lia.
    + left. lia.
    + intros L3 A3 regs3 mem3 md3 buf3 Lam3 peak3 b3 RP3 WRN3 ACC4.
      destruct (pz_acc_facts _ _ _ _ _ _ _ _ _ _ ACC4) as (HM4 & RO4 & Hh4 & Hl4 & WT4 & SB4).
      destruct (pz_acc_facts _ _ _ _ _ _ _ _ _ _ ACC3) as (HM3 & _).
      assert (FR4 : rw_cells rsegs mem3 FB (ps_lits ++ CB 8 e' :: SAVED)).
      { eapply (wr_cells B API RF SEGS); [exact HM3 | exact WRN3 | exact FR3 | lia | lia | left; pz_cs; lia |].
        eapply (off_errno_sub B); [exact ES | lia | pz_cs; lia]. }
      eapply pz_kA_after; [exact RP3 | exact Hh4 | exact Hl4 | exact RO4 | |].
      { eapply ps_after_esc; [exact (pz_s_norm mem3 RO4 SB4) | exact BO | exact NZ | lia]. }
      intros x2 y2 HN2 XR2 HO2 RM2.
      assert (HR2 : mem_rel_cj rsegs (ms_mem x2) (normalize_cj rsegs mem3))
        by (rewrite <- (pz_next_mem _ _ _ _ _ _ _ _ _ _ _ HN2); exact (pz_xrel_mem _ _ XR2)).
      destruct (pz_back [] mem3 (normalize_cj rsegs mem3) x2 RO4 HR2 HO2 (munch_refl [] _) (wmono_refl rsegs _))
        as (MU2 & WM2 & _).
      assert (ACC5 : pz_acc (YK11.mkFP F' fc') L3 A3 (ms_mem x2) md3 buf3 Lam3 peak3 b3
        ((P ++ [firstn (Z.to_nat (j - r)) (skipn (Z.to_nat r) bs)]) ++ [esc (nth (Z.to_nat j) bs 0)])).
      { eapply (pz_acc_munch (YK11.mkFP F' fc') (YK11.mkFP F' fc'));
          [exact ACC4 | exact MU2 | exact WM2 | exact RM2 | | intros k _; reflexivity | exact FRM'].
        intros z _ Hn. exfalso. apply Hn. exact I. }
      eapply (IH (Z.to_nat (Z.of_nat (length bs) - (j + 1))) ltac:(lia) (j + 1) (YK11.mkFP F' fc') x2 y2
        (normalize_cj rsegs mem3) L3 A3 md3 buf3 Lam3 peak3 b3
        ((P ++ [firstn (Z.to_nat (j - r)) (skipn (Z.to_nat r) bs)]) ++ [esc (nth (Z.to_nat j) bs 0)]) e' eq_refl
        ltac:(lia)).
      * rewrite <- !app_assoc. exact SPL.
      * exact HN2.
      * exact XR2.
      * exact ACC5.
      * exact (rw_cells_transport rsegs [] mem3 (ms_mem x2) _ _ FR4 MU2 WM2 I).
Qed.

Lemma pz_main : SR (ms_segs B) (mkCfg (@YK11.mkst fx0 regs0 (Z_to_bv 64 PUT_STRING) mem0 (YK11.seg_rom (ms_segs B)))
  md0) Post.
Proof.
  pose proof pz_spw as SPE. pose proof pz_sp as (SPa & SPb & SPc). pose proof pz_slow as (S0 & S1).
  pose proof pz_spc16 as SP16. pose proof ceil_big as CBg. unfold IMG_TOP in CBg.
  assert (PF : PS_FRAME = 144) by reflexivity. assert (PK : PS_K = 144 + PUT_K) by reflexivity.
  assert (PU : PUT_K = 8352) by reflexivity.
  pose proof PRE0 as (HM0 & HWF0 & HB0 & Hra0 & Hal0 & Hceil0 & Hsp0 & HWs0 & Htp0 & HWe0 & Haux0).
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM0) as (Hh0 & Hl0 & _).
  assert (ROr : ro_agree rsegs mem0) by (rewrite <- SEGS; exact RO0).
  assert (E10 : reg_get regs0 (Z_to_bv 5 10) = Z_to_bv 64 o) by (rewrite <- (pz_getr regs0 10) by lia; exact R10).
  assert (E11 : reg_get regs0 (Z_to_bv 5 11) = Z_to_bv 64 s) by (rewrite <- (pz_getr regs0 11) by lia; exact R11).
  assert (ACC0 : pz_acc fx0 L0 A0 mem0 md0 buf0 Lam0 peak0 b0 []).
  { pose proof PJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LT0 & _).
    split; [|split; [|split; [|split]]].
    - apply (wr_rel_nil B API RF); [exact HM0 | exact HWF0 | exact HB0 | exact RO0 | | exact LG0 | exact RES0].
      cbn [w_text w_cap w_failed]. rewrite LT0. exact PJ0.
    - intros k _. reflexivity.
    - exact FRM0.
    - exact SB0.
    - exact SW0. }
  rewrite SEGS.
  eapply (pz_lift fx0 regs0 _ mem0 md0 _ Post Hh0 Hl0 ROr).
  { rewrite pz_mkR_of_eq, E10, E11.
    eapply (ps_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (normalize_cj rsegs mem0)
      (spZ regs0 - PS_K) o s).
    - apply pz_stk_norm; [apply stk_hi; [unfold IMG_TOP; lia | lia |] | unfold IMG_TOP; lia | lia].
      intros a Ha. rewrite <- SEGS. apply HWs0. lia.
    - lia.
    - exact (mem_inv_cj_inv rsegs _ (mem_inv_cj_normalize rsegs mem0)). }
  intros x y0 (junk & m1 & -> & MU & WM & MI1 & ST1 & FR1) XR HO RM.
  destruct (pz_xrel_eqv _ _ _ _ _ _ _ _ XR) as [_ HR].
  destruct (pz_back _ mem0 m1 x ROr HR HO MU WM) as (MUx & WMx & ROx).
  assert (ACC1 : pz_acc fx0 L0 A0 (ms_mem x) md0 buf0 Lam0 peak0 b0 []).
  { eapply pz_acc_munch; [exact ACC0 | exact MUx | exact WMx | exact RM | | intros k _; reflexivity | exact FRM0].
    intros z Hz Hn. apply pz_not_out1 in Hn. rewrite SPE in Hn. lia. }
  assert (FRx : rw_cells rsegs (ms_mem x) FB (CB 40 junk :: SAVED)) by exact (pz_rw_rel _ _ _ _ HR FR1).
  eapply (pz_put_step fx0 x _ m1 md0 L0 A0 buf0 Lam0 peak0 b0 [] [34] (spieces_run [] bs ++ [[34]]) PS_Q1
    (spZ regs0 - PS_FRAME) XR).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact (eq_sym (pz_getr regs0 4 ltac:(lia))).
  - change (YK0s.ret_ok (Z_to_bv 64 0x175e4)). apply ret_ok_lit; [lia | reflexivity].
  - rewrite pz_spZ_mkR, unsigned_lit by lia. lia.
  - exact SP16.
  - lia.
  - exact ACC1.
  - reflexivity.
  - exact (pz_q1_z _ ROx).
  - constructor; [cbv beta; lia | constructor].
  - unfold PS_Q1. lia.
  - unfold PS_Q1. cbn [length]. lia.
  - apply pz_q1_w.
  - left. unfold PS_Q1. cbn [length]. lia.
  - intros L2 A2 regs2 mem2 md2 buf2 Lam2 peak2 b2 RP WRN ACC2.
    destruct (pz_acc_facts _ _ _ _ _ _ _ _ _ _ ACC2) as (HM2 & RO2 & Hh2 & Hl2 & WT2 & SB2).
    destruct (pz_acc_facts _ _ _ _ _ _ _ _ _ _ ACC1) as (HM1 & _).
    assert (FR2 : rw_cells rsegs mem2 FB (CB 40 junk :: SAVED)).
    { eapply (wr_cells B API RF SEGS); [exact HM1 | exact WRN | exact FRx | lia | lia | left; pz_cs; lia |].
      eapply (off_errno_sub B); [exact ES | lia | pz_cs; lia]. }
    pose proof ACC2 as (_ & _ & FRM2 & _ & _).
    destruct (list_eq_dec Z.eq_dec bs []) as [E0 | NE0].
    + eapply pz_kA_after; [exact RP | exact Hh2 | exact Hl2 | exact RO2 | |].
      { eapply ps_after_open_empty; [exact pz_spos |]. pose proof (pz_s_norm mem2 RO2 SB2) as SBn. rewrite E0 in SBn.
        exact SBn. }
      intros x1 y1 HN XR1 HO1 RM1.
      assert (HR1 : mem_rel_cj rsegs (ms_mem x1) (normalize_cj rsegs mem2))
        by (rewrite <- (pz_next_mem _ _ _ _ _ _ _ _ _ _ _ HN); exact (pz_xrel_mem _ _ XR1)).
      destruct (pz_back [] mem2 (normalize_cj rsegs mem2) x1 RO2 HR1 HO1 (munch_refl [] _) (wmono_refl rsegs _))
        as (MU1 & WM1 & _).
      assert (ACC3 : pz_acc fx0 L2 A2 (ms_mem x1) md2 buf2 Lam2 peak2 b2 [[34]]).
      { eapply pz_acc_munch; [exact ACC2 | exact MU1 | exact WM1 | exact RM1 | | intros k _; reflexivity | exact FRM2].
        intros z _ Hn. exfalso. apply Hn. exact I. }
      destruct HN as [(j & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Hj & _) |
                      (x5 & x6 & x7 & x9 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 & x21 & x22 & x23 & x24 & x25 &
                       x26 & x28 & x29 & x30 & x31 & _ & ->)].
      { cbn [length Z.of_nat] in Hj. lia. }
      eapply (pz_fin 0 fx0 x1 (normalize_cj rsegs mem2) L2 A2 md2 buf2 Lam2 peak2 b2 [[34]] junk x5 x6 x7 x9
        (Z_to_bv 64 (Z.of_nat (@length Z []) - 0)) x13 x14 x15
        x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31).
      * lia.
      * intros k Hk. rewrite E0 in Hk. cbn [length Z.of_nat] in Hk. lia.
      * rewrite E0. reflexivity.
      * rewrite E0. reflexivity.
      * exact XR1.
      * exact ACC3.
      * exact (rw_cells_transport rsegs [] mem2 (ms_mem x1) _ _ FR2 MU1 WM1 I).
    + eapply pz_kA_after; [exact RP | exact Hh2 | exact Hl2 | exact RO2 | |].
      { eapply (ps_after_open _ _ _ _ _ (normalize_cj rsegs mem2) (spZ regs0 - PS_K) o s bs junk).
        - exact pz_spos.
        - exact (pz_s_norm mem2 RO2 SB2).
        - exact BO.
        - exact NZ.
        - exact NE0.
        - apply pz_rw_norm; [exact RO2 | exact FR2 | unfold IMG_TOP; lia | pz_cs; lia].
        - apply pz_stk_norm; [apply stk_hi; [unfold IMG_TOP; lia | lia | intros a Ha; apply WT2; lia] | unfold IMG_TOP; lia
            | lia].
        - exact (mem_inv_cj_inv rsegs _ (mem_inv_cj_normalize rsegs mem2)).
        - left. lia. }
      intros x1 y1 (e & m1' & MU1 & WM1 & MI1' & ST1' & FR1' & SB1' & HN1) XR1 HO1 RM1.
      assert (HR1 : mem_rel_cj rsegs (ms_mem x1) m1')
        by (rewrite <- (pz_next_mem _ _ _ _ _ _ _ _ _ _ _ HN1); exact (pz_xrel_mem _ _ XR1)).
      destruct (pz_back _ mem2 m1' x1 RO2 HR1 HO1 MU1 WM1) as (MUx1 & WMx1 & _).
      assert (ACC3 : pz_acc fx0 L2 A2 (ms_mem x1) md2 buf2 Lam2 peak2 b2 [[34]]).
      { eapply pz_acc_munch; [exact ACC2 | exact MUx1 | exact WMx1 | exact RM1 | | intros k _; reflexivity | exact FRM2].
        intros z Hz Hn. apply pz_not_out1 in Hn. rewrite SPE in Hn. lia. }
      eapply (pz_loop _ 0 fx0 x1 y1 m1' L2 A2 md2 buf2 Lam2 peak2 b2 [[34]] e eq_refl).
      * lia.
      * reflexivity.
      * exact HN1.
      * exact XR1.
      * exact ACC3.
      * exact (pz_rw_rel _ _ _ _ HR1 FR1').
Qed.

End PS.

Section Q.
Context {fx : FPState} {rc : RunCeil}.

Theorem put_string_holds : forall (B : malloc_syms) (API : AllocAPI B) (RF : ResForm),
  AllocExtra B (aa_MR API) -> ctx_owned B API ->
  (forall fx' : FPState, @put_contract fx' rc B API RF) -> snprintf_contract -> strlen_contract ->
  put_string_contract B API RF.
Proof.
  intros B API RF AX CTX PUTC SNP STL. unfold put_string_contract.
  intros L A regs mem md b o s buf len cap failed text bs Lam peak cnt fail calls SEGS GOTG GDG PRE RO INIT FRM R10 R11 PJ
    LG SPO EO ES SB BO NZ SW NEED RES ROOMS.
  destruct PRE as [PRE SPT].
  eapply (pz_main B API RF); eassumption.
Qed.

End Q.
