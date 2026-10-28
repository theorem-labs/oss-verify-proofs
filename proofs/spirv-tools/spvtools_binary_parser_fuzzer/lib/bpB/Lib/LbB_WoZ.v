(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_PrsStmt LbB_SR LbB_Conv LbB_WoGen LbB_WoDefs LbB_WoKit.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition zap (a b c d : Z) : Prop := b <= c \/ d <= a.

Lemma zap_sub : forall a b c d x y A A', zap a b c d -> a <= x -> y <= b -> c <= A -> A' <= d -> y <= A \/ A' <= x.
Proof. unfold zap. intros. lia. Qed.
Lemma zap_subr : forall a b c d x y A A', zap a b c d -> c <= x -> y <= d -> a <= A -> A' <= b -> y <= A \/ A' <= x.
Proof. unfold zap. intros. lia. Qed.

Ltac zbase t :=
  lazymatch t with
  | ?x + _ => zbase x
  | ?x - _ => zbase x
  | _ => t
  end.

Ltac zdj1 :=
  lazymatch goal with
  | |- ?p <= ?q \/ ?r <= ?s =>
      let bs := zbase s in let bq := zbase q in
      first [ match goal with K : zap ?a _ ?c _ |- _ =>
                let ba := zbase a in let bc := zbase c in
                first [ constr_eq ba bs; constr_eq bc bq; apply (zap_sub _ _ _ _ _ _ _ _ K); lia
                      | constr_eq ba bq; constr_eq bc bs; apply (zap_subr _ _ _ _ _ _ _ _ K); lia ] end
            | lia ]
  | |- _ => lia
  end.

Ltac zdj :=
  repeat lazymatch goal with
  | |- _ /\ _ => split
  | |- True => exact I
  | |- Forall _ (_ :: _) => apply Forall_cons; [cbn beta iota delta [fst snd] |]
  | |- Forall _ [] => apply Forall_nil
  end;
  lazymatch goal with
  | |- _ \/ _ => zdj1
  | |- _ => lia
  end.

Lemma munch_drop0 : forall a W m m', munch ((a, a + 0) :: W) m m' -> munch W m m'.
Proof. intros a W m m' MU x Hx. apply MU. cbn [outside]. split; [lia | exact Hx]. Qed.

Lemma munch_in2 : forall W m m' lo1 hi1 lo2 hi2, munch W m m' ->
  Forall (fun iv : Z * Z => (lo1 <= fst iv /\ snd iv <= hi1) \/ (lo2 <= fst iv /\ snd iv <= hi2)) W ->
  munch [(lo1, hi1); (lo2, hi2)] m m'.
Proof.
  intros W m m' lo1 hi1 lo2 hi2 MU FW x Hx. apply MU. cbn [outside] in Hx. destruct Hx as (Hx1 & Hx2 & _).
  clear MU. induction FW as [|[a b] W K FW IH]; cbn [outside]; [exact I|]. cbn [fst snd] in K.
  split; [intros Hab; destruct K as [K|K]; [apply Hx1 | apply Hx2]; lia | exact IH].
Qed.

Section Z.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HB : asan_rt_hyps H.

  Lemma wframe_z : forall LF ff fp, fresh_frame H LF 6 ff fp ->
       0x6e8000 + 0x9000 <= ff /\ ff + 4096 <= aceil /\ ff mod 64 = 0
    /\ as_FSB H + 0x1000 <= fp /\ fp < as_FSB H + 0x9000 /\ as_FSB H + 0x9000 <= ff /\ ff + 4096 <= as_FSB H + AFS_SIZE
    /\ 0x6e8000 <= as_FSB H /\ as_FSB H + AFS_SIZE <= aceil /\ aapp (as_FSB H) AFS_SIZE
    /\ sh ff + 512 = sh (ff + 4096) /\ sh (as_FSB H) <= sh ff /\ sh (ff + 4096) <= sh (as_FSB H + AFS_SIZE)
    /\ 0x7fff8000 <= sh ff /\ sh ff + 512 <= 0x10007fff8000
    /\ zap (sh ff) (sh ff + 512) (as_FSB H) (as_FSB H + AFS_SIZE)
    /\ zap ff (ff + 4096) 0x7fff7000 0x10007fff8000
    /\ zap (sh ff) (sh ff + 512) ff (ff + 4096).
  Proof.
    intros LF ff fp FF.
    pose proof (wframe_facts H _ _ _ FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    assert (FAPP : ff + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= ff)
      by (unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in F10; destruct F10 as [[X Y]|[X Y]]; [left | right]; lia).
    assert (FSH : sh ff + 512 <= ff \/ ff + 4096 <= sh ff).
    { destruct FAPP as [X|X].
      - right. lia.
      - left. unfold sh in *. rewrite ASHADOW_BASE_val in *. clear - X. Z.div_mod_to_equations. lia. }
    unfold zap. repeat split; assumption.
  Qed.

  Lemma wblk_geo : forall (e : went H) ff fp XSc sk LBk m p b n, wpre H e -> winv H e ff fp XSc sk LBk m -> In (p, b, n) LBk ->
       0 < b /\ b mod 16 = 0 /\ 0 <= n /\ b + n <= aceil /\ b + n + 512 < 2 ^ 64
    /\ sh b + nsh n <= sh aceil /\ sh aceil < aceil /\ aceil <= w_lo e /\ w_lo e + 32768 <= wS1 e
    /\ zap b (b + n) ff (ff + 4096) /\ zap (sh b) (sh b + nsh n) ff (ff + 4096)
    /\ zap (sh b) (sh b + nsh n) (sh ff) (sh ff + 512) /\ zap (sh b) (sh b + nsh n) b (b + n)
    /\ zap b (b + n) (sh ff) (sh ff + 512).
  Proof.
    intros e ff fp XSc sk LBk m p b n HP HI IN.
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _).
    pose proof (wframe_facts H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof (ah_blocks H HB _ _ _ _ (winv_rh H _ _ _ _ _ _ _ HI) IN) as (B0 & B16 & Bn & BI & BC & BF & BAPP).
    cbn in B0, B16, Bn, BI, BC, BF, BAPP. pose proof aceil_facts as ACF.
    assert (SHP : sh b + nsh n <= sh aceil) by (unfold sh, nsh; Z.div_mod_to_equations; nia).
    assert (SHC : sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE b n F10 ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as D1.
    assert (D2 : sh b + nsh n <= sh ff \/ sh ff + 512 <= sh b).
    { destruct BF as [BF|BF].
      - left. assert (sh b + nsh n <= sh (as_FSB H)) by (unfold sh, nsh; Z.div_mod_to_equations; nia). lia.
      - right. assert (sh (as_FSB H + AFS_SIZE) <= sh b) by (apply sh_mono; lia). unfold AFS_SIZE in *. lia. }
    pose proof (aapp_disjoint_sh b n b n BAPP ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as D3.
    pose proof (aapp_disjoint_sh b n ff 4096 BAPP ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as D4.
    change (nsh 4096) with 512 in D4.
    unfold zap. repeat split; try lia.
  Qed.

  Lemma wblk2_geo : forall s LBk m p b n q c k, as_RHEAP H s LBk m -> In (p, b, n) LBk -> In (q, c, k) LBk -> p <> q ->
       zap b (b + n) c (c + k) /\ zap (sh b) (sh b + nsh n) c (c + k) /\ zap b (b + n) (sh c) (sh c + nsh k)
    /\ zap (sh b) (sh b + nsh n) (sh c) (sh c + nsh k).
  Proof.
    intros s LBk m p b n q c k RH INb INc NE.
    pose proof (ah_blocks H HB _ _ _ _ RH INb) as (B0 & B16 & Bn & BI & BC & BF & BAPP).
    pose proof (ah_blocks H HB _ _ _ _ RH INc) as (C0 & C16 & Cn & CI & CC & CF & CAPP).
    cbn in B0, B16, Bn, BI, BC, BF, BAPP, C0, C16, Cn, CI, CC, CF, CAPP. pose proof aceil_facts as ACF.
    pose proof (ah_disj H HB _ _ _ (p, b, n) (q, c, k) RH INb INc NE) as D. cbn in D.
    pose proof (aapp_disjoint_sh c k b n CAPP ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as D1.
    pose proof (aapp_disjoint_sh b n c k BAPP ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as D2.
    assert (D3 : sh b + nsh n <= sh c \/ sh c + nsh k <= sh b).
    { clear - D B16 C16 Bn Cn B0 C0. destruct D as [D|D]; [left | right]; unfold sh, nsh; Z.div_mod_to_equations; nia. }
    unfold zap. split; [lia|]. split; [lia|]. split; [lia|]. lia.
  Qed.
End Z.
