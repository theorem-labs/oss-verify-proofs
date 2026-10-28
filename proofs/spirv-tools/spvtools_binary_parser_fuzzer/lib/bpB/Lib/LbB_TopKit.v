(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BecLazy.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import DvB_FuzzStmt LbB_PrsStmt LbB_DStat LbB_SR LbB_TopDefs.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require LbB_Kit LbB_Conv.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtB_Td LbB_TdKit.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Lemma wr_at_wmono : forall m m' a n, wr_at asegs m a n -> wmono asegs m m' -> wr_at asegs m' a n.
Proof. intros m m' a n (W1 & W2 & W) WM. split; [lia|]. split; [lia|]. intros i Hi. apply WM. apply W. exact Hi. Qed.

Lemma disjoint_from_app : forall W1 W2 A n, disjoint_from W1 A n /\ disjoint_from W2 A n -> disjoint_from (W1 ++ W2) A n.
Proof.
  induction W1 as [|[x y] W1 IH]; intros W2 A n [D1 D2]; cbn in *; [exact D2|].
  destruct D1 as [D11 D12]. split; [exact D11 | apply IH; split; assumption].
Qed.

Lemma mdef_of_wr_at : forall m a n, wr_at asegs m a n -> 0x6e8000 <= a -> CRep.mdef m a n.
Proof.
  intros m a n (W0 & W1 & W) Ha i Hi. specialize (W i Hi). unfold wview in W.
  unfold wa in W. rewrite HLib.u64_of_Z in W by lia.
  destruct (m (Z_to_bv 64 (a + i))) eqn:E; [discriminate|].
  rewrite BecLazy.asegs_find_segment_none_high in W by lia. congruence.
Qed.

Lemma sh_ge_base : forall a, 0 <= a -> 0x7fff8000 <= sh a.
Proof. intros a Ha. unfold sh. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. lia. Qed.

Lemma zero24_cells : forall m a, rw_cells asegs m a [CB 24 (poison_bytes 24 0)] -> rw_cells asegs m a [C8 (wz 0); C8 (wz 0); C8 (wz 0)].
Proof.
  intros m a [[WF B] W]. split; [split|].
  - cbn. tauto.
  - replace (cells_bytes [C8 (wz 0); C8 (wz 0); C8 (wz 0)]) with (cells_bytes [CB 24 (poison_bytes 24 0)]) by (vm_compute; reflexivity).
    exact B.
  - exact W.
Qed.

Lemma stk_wmono : forall m m' lo hi, stk asegs m lo hi -> wmono asegs m m' -> 0x6e8000 <= lo -> stk asegs m' lo hi.
Proof.
  intros m m' lo hi (S0 & S1 & S) WM Hlo. split; [lia|]. split; [lia|]. intros a Ha.
  destruct (S a Ha) as [W _]. pose proof (WM _ W) as W'. split; [exact W'|].
  unfold wview in W'. unfold wa in W' |- *. rewrite HLib.u64_of_Z in W' by lia.
  destruct (m' (Z_to_bv 64 a)) as [b|] eqn:E.
  - exists b. unfold mrd. rewrite E. reflexivity.
  - rewrite BecLazy.asegs_find_segment_none_high in W' by lia. congruence.
Qed.

Lemma wr_at_rw_cells : forall m a n, wr_at asegs m a n -> 0x6e8000 <= a -> 0 <= n ->
  exists bs, rw_cells asegs m a [CB (Z.to_nat n) bs].
Proof.
  intros m a n W Ha Hn. pose proof (mdef_of_wr_at m a n W Ha) as MD.
  assert (EX : forall k, (k <= Z.to_nat n)%nat -> exists bs, length bs = k /\ bytes_at asegs m a bs).
  { induction k as [|k IH]; intros Hk.
    - exists []. split; [reflexivity|]. split; [lia|]. split; [cbn; destruct W as (_ & W1 & _); lia|]. intros i Hi. cbn in Hi. lia.
    - destruct (IH ltac:(lia)) as (bs & Lb & Bb).
      specialize (MD (Z.of_nat k) ltac:(lia)). destruct (m (Z_to_bv 64 (a + Z.of_nat k))) as [b|] eqn:E; [|congruence].
      exists (bs ++ [b]). rewrite length_app, Lb. cbn [length]. split; [lia|]. apply bytes_at_app. split; [exact Bb|].
      destruct W as (W0 & W1 & _). split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. destruct i as [|i]; [|lia].
      cbn. unfold mrd, wa. rewrite Lb, Z.add_0_r, E. reflexivity. }
  destruct (EX (Z.to_nat n) ltac:(lia)) as (bs & Lb & Bb). exists bs.
  split; [split; [cbn; split; [exact Lb | exact I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact Bb]|].
  cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact W.
Qed.

Lemma shk_last_of_addressable : forall m A n x, addressable m A n -> n mod 8 <> 0 ->
  A + 8 * (n / 8) <= x < A + n -> LbB_Kit.shk m x (n mod 8).
Proof.
  intros m A n x (Hn & SH) E Hx. pose proof SH as (HA & HA8 & _).
  assert (R : A <= x < A + 8 * Z.of_nat (length (shadow_of n))) by (rewrite shadow_of_length by lia; unfold nsh; Z.div_mod_to_equations; nia).
  destruct (LbB_Conv.shk_of_SHAD m A _ x SH R) as (b & Hb & K).
  replace (Z.to_nat ((x - A) / 8)) with (Z.to_nat (n / 8)) in Hb by (f_equal; Z.div_mod_to_equations; nia).
  rewrite (shadow_of_nth_last n ltac:(lia) E) in Hb. injection Hb as <-.
  unfold b8 in K. rewrite Z_to_bv_unsigned, bv_wrap_small in K by (change (bv_modulus 8) with 256; Z.div_mod_to_equations; lia). exact K.
Qed.

Lemma u8arr_sub : forall m A bs i k, u8arr asegs m A bs -> 0 <= i -> 0 <= k -> i + k <= Z.of_nat (length bs) ->
  u8arr asegs m (A + i) (firstn (Z.to_nat k) (skipn (Z.to_nat i) bs)).
Proof.
  intros m A bs i k [B W] Hi Hk Hik.
  assert (L : length (firstn (Z.to_nat k) (skipn (Z.to_nat i) bs)) = Z.to_nat k)
    by (rewrite firstn_length_le; [reflexivity| rewrite length_skipn; lia]).
  split.
  - rewrite <- (firstn_skipn (Z.to_nat i) bs) in B. apply bytes_at_app in B as [_ B2].
    rewrite firstn_length_le in B2 by lia. rewrite Z2Nat.id in B2 by lia.
    rewrite <- (firstn_skipn (Z.to_nat k) (skipn (Z.to_nat i) bs)) in B2. apply bytes_at_app in B2 as [B3 _]. exact B3.
  - destruct W as (W1 & W2 & W). rewrite L. split; [lia|]. split; [lia|]. intros j Hj.
    replace (A + i + j) with (A + (i + j)) by lia. apply W. lia.
Qed.

Lemma skipn_repeat' : forall (A : Type) (x : A) n k, skipn k (repeat x n) = repeat x (n - k).
Proof. intros A x n. induction n as [|n IH]; intros [|k]; cbn; try reflexivity. apply IH. Qed.
Lemma firstn_repeat' : forall (A : Type) (x : A) n k, firstn k (repeat x n) = repeat x (Nat.min k n).
Proof. intros A x n. induction n as [|n IH]; intros [|k]; cbn; try reflexivity. f_equal. apply IH. Qed.

Lemma u8arr_repeat_sub : forall m A (b : byte) n i k, u8arr asegs m A (repeat b n) -> 0 <= i -> 0 <= k -> i + k <= Z.of_nat n ->
  u8arr asegs m (A + i) (repeat b (Z.to_nat k)).
Proof.
  intros m A b n i k U Hi Hk Hik. pose proof (u8arr_sub m A _ i k U Hi Hk ltac:(rewrite repeat_length; lia)) as X.
  rewrite skipn_repeat', firstn_repeat' in X. replace (Init.Nat.min (Z.to_nat k) (n - Z.to_nat i)) with (Z.to_nat k) in X by lia. exact X.
Qed.

Lemma rw_cells_CB_sub : forall m A n bs i k, rw_cells asegs m A [CB n bs] -> 0 <= i -> 0 <= k -> i + k <= Z.of_nat n ->
  exists bs', rw_cells asegs m (A + i) [CB (Z.to_nat k) bs'].
Proof.
  intros m A n bs i k C Hi Hk Hik.
  assert (LN : length bs = n) by (destruct C as [[[X _] _] _]; exact X).
  pose proof (u8arr_of_rw_cells asegs m A n bs C) as U.
  pose proof (u8arr_sub m A bs i k U Hi Hk ltac:(lia)) as U2.
  exists (firstn (Z.to_nat k) (skipn (Z.to_nat i) bs)).
  pose proof (rw_cells_of_u8arr asegs m _ _ U2) as C2.
  rewrite firstn_length_le in C2 by (rewrite length_skipn; lia). exact C2.
Qed.

Section Kit.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma sh_aceil_lt : sh aceil < 0x10007fff8000.
  Proof. pose proof aceil_facts. unfold sh. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. lia. Qed.

  Lemma hframe_facts : forall LF ff fp, fresh_frame H LF 6 ff fp ->
       0x6e8000 + 0x9000 <= ff /\ ff + 4096 <= aceil /\ ff mod 64 = 0
    /\ as_FSB H + 0x1000 <= fp /\ fp < as_FSB H + 0x9000 /\ as_FSB H + 0x9000 <= ff /\ ff + 4096 <= as_FSB H + AFS_SIZE
    /\ 0x6e8000 <= as_FSB H /\ as_FSB H + AFS_SIZE <= aceil /\ aapp (as_FSB H) AFS_SIZE
    /\ sh ff + 512 = sh (ff + 4096) /\ sh (as_FSB H) <= sh ff /\ sh (ff + 4096) <= sh (as_FSB H + AFS_SIZE)
    /\ 0x7fff8000 <= sh ff /\ sh ff + 512 <= 0x10007fff8000
    /\ (sh ff + 512 <= as_FSB H \/ as_FSB H + AFS_SIZE <= sh ff).
  Proof.
    intros LF ff fp FF. pose proof (fresh_frame_facts H LF 6 ff fp FF) as (K & R1 & R2 & M64 & M8 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
    change (fsz 6) with 4096 in *. unfold AIMG_TOP, AFS_HDR, AFS_FLAGS in *.
    pose proof aceil_facts as ACF.
    assert (S1 : sh ff + 512 = sh (ff + 4096)) by (unfold sh; Z.div_mod_to_equations; lia).
    assert (S2 : sh (as_FSB H) <= sh ff) by (apply sh_mono; lia).
    assert (S3 : sh (ff + 4096) <= sh (as_FSB H + AFS_SIZE)) by (apply sh_mono; lia).
    assert (S4 : 0x7fff8000 <= sh ff /\ sh ff + 512 <= 0x10007fff8000)
      by (unfold sh; rewrite ASHADOW_BASE_val; unfold AFS_SIZE in *; Z.div_mod_to_equations; lia).
    pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE ff 4096 P9 ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as S5.
    change (nsh 4096) with 512 in S5.
    repeat split; try assumption; try lia.
  Qed.

  Lemma hpre_geo : forall e, hpre H e ->
    aceil <= e_lo e /\ e_lo e <= eSP e - 65536 /\ eSP e <= e_shi e /\ e_shi e <= AAPP_HI /\ eSP e mod 16 = 0
    /\ e_tp e = Z_to_bv 64 ATP.
  Proof.
    intros e HP.
    destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SP16 & _ & CE & LO & _ & _ & TP & _ & _ & _ & _ & _ & _ & S0 & SHI & _).
    pose proof (stack0_bounds _ _ _ S0). unfold AFUZZ_STACK in LO. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [exact SP16 | exact TP].
  Qed.
  Lemma hpre_RH0 : forall e, hpre H e -> as_RHEAP H (e_s e) (e_LB e) (e_m e).
  Proof. intros e HP. destruct HP as (_ & _ & _ & _ & _ & _ & _ & X & _). exact X. Qed.
  Lemma errno_ATP : forall (e : hent H), e_tp e = Z_to_bv 64 ATP -> errno_addr (e_tp e) = ATP - 164.
  Proof. intros e TP. rewrite TP, HLib.u64_of_Z by (unfold ATP; lia). lia. Qed.

  Definition hwin (e : hent H) (ff : Z) (iv : Z * Z) : Prop :=
    (e_lo e <= fst iv /\ snd iv <= eSP e - 104) \/ (ff <= fst iv /\ snd iv <= ff + 4088) \/ (sh ff <= fst iv /\ snd iv <= sh ff + 512).

  Lemma hwin_ok : forall e ff fp XSc iv, fresh_frame H (e_LF e) 6 ff fp ->
    aceil <= e_lo e -> e_lo e <= eSP e - 104 -> eSP e <= AAPP_HI -> hwin e ff iv ->
       afs_write_ok H ((6, ff, fp) :: e_LF e) iv /\ (forall LBk, aclient_write_ok H LBk iv) /\ aconst_ok iv /\ stack0_ok iv
    /\ ((aceil <= fst iv /\ snd iv <= eSP e) \/ (forall a, fst iv <= a < snd iv -> rin_ivs (XH H ff fp ++ XSc) a))
    /\ (snd iv <= eSP e - 104 \/ eSP e <= fst iv)
    /\ (snd iv <= ff + 4088 \/ ff + 4096 <= fst iv)
    /\ (snd iv <= ATP - 164 \/ ATP - 160 <= fst iv).
  Proof.
    intros e ff fp XSc iv FF CE LO SPH HW.
    pose proof (hframe_facts _ _ _ FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof aceil_facts as ACF.
    destruct iv as [a b]. unfold hwin in HW. cbn [fst snd] in *.
    set (SP := eSP e) in *. set (lo := e_lo e) in *. clearbody SP lo.
    unfold afs_write_ok, aclient_write_ok; cbn [fst snd].
    destruct HW as [(W1 & W2)|[(W1 & W2)|(W1 & W2)]].
    -
      split; [left; split; [right; lia | right; unfold ATLS_PRIV_HI, ATP; lia]|].
      split; [intros LBk; left; cbn; lia|].
      split; [apply aconst_ok_high; [replace (sh AIMG_TOP) with 0x800d5000 by reflexivity; lia | right; left; lia]|].
      split; [apply stack0_ok_app; unfold AHI_LO; lia|].
      split; [left; lia|]. split; [left; lia|]. split; [right; lia|]. right; unfold ATP; lia.
    -
      split; [right; exists (6, ff, fp); split; [left; reflexivity | cbn; change (fsz 6) with 4096; lia]|].
      split; [intros LBk; right; right; right; right; left; cbn; lia|].
      split; [eapply (LbB_SR.aconst_ok_app (as_FSB H) AFS_SIZE); [exact F10 | cbn; lia | cbn; lia]|].
      split; [eapply (stack0_ok_aapp (as_FSB H) AFS_SIZE); [exact F10 | lia | lia]|].
      split; [right; intros x Hx; apply rin_ivs_app; left; cbn; right; right; left; change (fsz 6) with 4096; lia|].
      split; [left; lia|]. split; [left; lia|]. right; unfold ATP; lia.
    -
      split; [left; split; [destruct F16; [left | right]; lia | right; unfold ATLS_PRIV_HI, ATP; lia]|].
      split; [intros LBk; right; right; right; right; right; left; cbn; lia|].
      split; [apply aconst_ok_high; [assert (sh AIMG_TOP <= sh ff) by (apply sh_mono; unfold AIMG_TOP; lia); lia | right; left; lia]|].
      split; [right; cbn; assert (sh (ff + 4096) <= sh aceil) by (apply sh_mono; lia); lia|].
      split; [right; intros x Hx; apply rin_ivs_app; left; cbn; right; right; right; left; change (fshn 6) with 512; lia|].
      split; [left; lia|]. split; [destruct F16; [left | right]; lia|]. right; unfold ATP; lia.
  Qed.

  Lemma hwin_all : forall e ff fp XSc W, fresh_frame H (e_LF e) 6 ff fp ->
    aceil <= e_lo e -> e_lo e <= eSP e - 104 -> eSP e <= AAPP_HI -> Forall (hwin e ff) W ->
       Forall (afs_write_ok H ((6, ff, fp) :: e_LF e)) W /\ (forall LBk, Forall (aclient_write_ok H LBk) W) /\ Forall aconst_ok W
    /\ Forall stack0_ok W
    /\ Forall (fun iv : Z * Z => (aceil <= fst iv /\ snd iv <= eSP e) \/ (forall a, fst iv <= a < snd iv -> rin_ivs (XH H ff fp ++ XSc) a)) W
    /\ disjoint_from W (eSP e - 104) 104 /\ disjoint_from W (ff + 4088) 8 /\ disjoint_from W (ATP - 164) 4.
  Proof.
    intros e ff fp XSc W FF CE LO SPH FW. induction W as [|iv W IH].
    - split; [apply Forall_nil|]. split; [intros; apply Forall_nil|]. do 3 (split; [apply Forall_nil|]). cbn. tauto.
    - apply Forall_cons_iff in FW as [F0 FW]. destruct (IH FW) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
      destruct (hwin_ok e ff fp XSc iv FF CE LO SPH F0) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
      split; [apply Forall_cons; assumption|]. split; [intros LBk; apply Forall_cons; [apply B2 | apply A2]|].
      split; [apply Forall_cons; assumption|]. split; [apply Forall_cons; assumption|]. split; [apply Forall_cons; assumption|].
      destruct iv as [x y]. cbn [fst snd] in *. cbn [disjoint_from].
      split; [split; [lia | exact A6]|]. split; [split; [lia | exact A7]|]. split; [lia | exact A8].
  Qed.

  Lemma hinv_munch : forall e ff fp XSc sk LBk m1 m2 W,
    hpre H e -> hinv H e ff fp XSc sk LBk m1 ->
    munch W m1 m2 -> wmono asegs m1 m2 -> mem_inv asegs m2 -> stk asegs m2 (e_lo e) (eSP e) ->
    Forall (hwin e ff) W -> hinv H e ff fp XSc sk LBk m2.
  Proof.
    intros e ff fp XSc sk LBk m1 m2 W HP HI MU WM MI2 ST2 FW.
    destruct HI as (RF & FF & RH & AC & MI & S0 & RA & (errv & ER) & ST & SV & SF & WF & XP & FS & LVI).
    pose proof (hpre_geo e HP) as (CE & LO' & SH1 & SH2 & _ & TP).
    assert (LO : e_lo e <= eSP e - 104) by lia. assert (SPH : eSP e <= AAPP_HI) by lia. clear LO' SH1 SH2.
    unfold hinv. rewrite (errno_ATP e TP) in ER |- *.
    destruct (hwin_all e ff fp XSc W FF CE LO SPH FW) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    pose proof (hpre_RH0 e HP) as RH0.
    split; [eapply (ah_RFS_frame H HH); [exact RF | exact MU | exact WM | exact A1]|].
    split; [exact FF|].
    split; [eapply (ah_RHEAP_frame H HH); [exact RH | exact MU | exact WM | exact (A2 LBk)]|].
    split; [eapply ACONST_frame; [exact AC | exact MU | exact WM | exact A3]|].
    split; [exact MI2|].
    split; [eapply stack0_transport; [exact S0 | exact MU | exact WM | exact A4]|].
    split; [eapply (ah_rauxv_frame H HH); [exact RA | exact MU | exact WM | exact (A2 LBk)]|].
    split; [exists errv; eapply rw_cells_transport; [exact ER | exact MU | exact WM | exact A8]|].
    split; [exact ST2|].
    split; [eapply rw_cells_transport; [exact SV | exact MU | exact WM | exact A6]|].
    split; [eapply rw_cells_transport; [exact SF | exact MU | exact WM | exact A7]|].
    split; [exact (wr_at_wmono _ _ _ _ WF WM)|].
    split; [| split; [exact FS|]].
    - eapply xpres_trans; [exact XP|]. eapply (xpres_of_munch H (e_s e) (e_LB e) (eSP e) _ W (e_m e)); [exact HH | exact RH0 | exact MU | exact WM |].
        eapply Forall_impl; [| exact A5]. intros iv [K|K]; [left; exact K | right; intros a Ha; right; exact (K a Ha)].
    -
      eapply LbB_TdKit.LINV_P5_munch_hi; [exact LVI | exact MU |]. eapply Forall_impl; [| exact FW]. intros iv HW.
      pose proof (hframe_facts _ _ _ FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
      pose proof aceil_facts as ACF. unfold hwin in HW. unfold AIMG_TOP. destruct HW as [(W1 & _)|[(W1 & _)|(W1 & _)]]; lia.
  Qed.

  Lemma eS1_facts : forall (e : hent H), hpre H e ->
    eS1 e mod 32 = 0 /\ eS1 e + 224 <= eSP e <= eS1 e + 240 /\ 2 ^ 45 <= eS1 e /\ eSP e <= 2 ^ 47
    /\ e_lo e <= eS1 e - 65536 + 240 /\ aceil <= e_lo e.
  Proof.
    intros e HP. pose proof (hpre_geo e HP) as (CE & LO & SH1 & SH2 & SP16 & _).
    pose proof aceil_facts as ACF. unfold eS1. unfold AAPP_HI in SH2.
    set (SP := eSP e) in *. clearbody SP.
    assert (R : SP mod 32 = 0 \/ SP mod 32 = 16) by (clear - SP16; Z.div_mod_to_equations; lia).
    assert (R2 : (SP - 224 - SP mod 32) mod 32 = 0) by (clear - R; Z.div_mod_to_equations; lia).
    split; [exact R2|]. destruct R as [R|R]; rewrite R; lia.
  Qed.

  Lemma fs_scratch_mono : forall f LF iv, fs_scratch H (f :: LF) iv -> fs_scratch H LF iv.
  Proof.
    intros f LF iv [X|(k & ff & fp & (FA & FB & FD) & E)]; [left; exact X|]. right. exists k, ff, fp. split; [| exact E].
    split; [exact FA|]. split; [exact FB|]. intros g IN. apply FD. right. exact IN.
  Qed.

  Lemma rin_ivs_none : forall X a, Forall (fun iv : Z * Z => a < fst iv \/ snd iv <= a) X -> ~ rin_ivs X a.
  Proof.
    induction X as [|iv X IH]; intros a F; cbn; [tauto|]. inversion F as [|? ? F1 F2]; subst.
    intros [K|K]; [lia| exact (IH a F2 K)].
  Qed.

  Lemma fsw_ok : forall (e : hent H) ff fp m iv,
    as_RFS H ((6, ff, fp) :: e_LF e) m -> fresh_frame H (e_LF e) 6 ff fp -> aceil <= e_lo e ->
    fs_scratch H ((6, ff, fp) :: e_LF e) iv ->
       (forall LBk, aclient_write_ok H LBk iv) /\ aconst_ok iv /\ stack0_ok iv
    /\ (snd iv <= ff + 4088 \/ ff + 4096 <= fst iv) /\ (snd iv <= ff \/ ff + 4096 <= fst iv)
    /\ (snd iv <= sh ff \/ sh ff + 512 <= fst iv)
    /\ snd iv <= e_lo e /\ (snd iv <= ATP - 164 \/ ATP - 160 <= fst iv).
  Proof.
    intros e ff fp m iv RF FF CE FS.
    pose proof (hframe_facts _ _ _ FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof aceil_facts as ACF.
    assert (OB : fsobj H ((6, ff, fp) :: e_LF e) ff 4096) by (eapply (fsobj_inframe H); [left; reflexivity | cbn; lia | cbn; change (fsz 6) with 4096; lia]).
    pose proof (fsobj_scratch H HH _ ff 4096 m iv RF OB ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)
                  (aapp_sub _ _ ff 4096 F10 ltac:(lia) ltac:(lia)) FS) as D1.
    pose proof (fsobj_scratch_sh H HH _ ff 4096 m iv RF OB ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia) FS) as D2.
    change (nsh 4096) with 512 in D2.

    assert (WH : (as_FSB H <= fst iv /\ snd iv <= as_FSB H + AFS_SIZE) \/ (sh (as_FSB H) <= fst iv /\ snd iv <= sh (as_FSB H + AFS_SIZE))).
    { destruct FS as [->|(k & ff' & fp' & FF' & E)]; [left; cbn; unfold AFS_FLAGS, AFS_SIZE; lia|].
      pose proof (fresh_frame_facts H _ _ _ _ FF') as (K & R1 & R2 & M64 & M8 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
      pose proof (fsz_pos k ltac:(lia)).
      unfold AFS_HDR, AFS_FLAGS in *. destruct E as [E|[E|E]]; rewrite E; cbn [fst snd]; [left; lia | left; unfold AFS_SIZE in *; lia | right].
      assert (sh (as_FSB H) <= sh ff') by (apply sh_mono; lia).
      assert (sh ff' + fshn k = sh (ff' + fsz k)) by (unfold sh, fshn, fsz; Z.div_mod_to_equations; nia).
      assert (sh (ff' + fsz k) <= sh (as_FSB H + AFS_SIZE)) by (apply sh_mono; lia). lia. }
    assert (SHF : sh (as_FSB H + AFS_SIZE) <= sh aceil) by (apply sh_mono; lia).
    assert (SHA : 0x7fff8000 <= sh (as_FSB H)) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHC : sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    split; [intros LBk; unfold aclient_write_ok; destruct WH as [W|W]; [right; right; right; right; left | right; right; right; right; right; left]; exact W|].
    split.
    { destruct iv as [x y]. cbn [fst snd] in *. destruct WH as [W|W].
      - eapply (LbB_SR.aconst_ok_app (as_FSB H) AFS_SIZE); [exact F10 | lia | lia].
      - apply aconst_ok_high; [| right; left; unfold AFS_SIZE in *; lia].
        replace (sh AIMG_TOP) with 0x800d5000 by reflexivity. assert (sh 0x6e8000 <= sh (as_FSB H)) by (apply sh_mono; lia).
        replace (sh 0x6e8000) with 0x800d5000 in * by reflexivity. lia. }
    split.
    { destruct iv as [x y]. cbn [fst snd] in *. destruct WH as [W|W]; [eapply (stack0_ok_aapp (as_FSB H) AFS_SIZE); [exact F10 | lia | lia] | right; cbn; lia]. }
    split; [destruct D1; [right | left]; lia|]. split; [destruct D1; [right | left]; lia|].
    split; [destruct D2; [right | left]; lia|].
    split; [destruct WH; unfold AFS_SIZE in *; lia|]. right. unfold ATP. destruct WH; unfold AFS_SIZE in *; lia.
  Qed.

  Definition cwin (e : hent H) (ff : Z) (XSn : list (Z * Z)) (iv : Z * Z) : Prop :=
    (e_lo e <= fst iv /\ snd iv <= eS1 e) \/ (ff <= fst iv /\ snd iv <= ff + 4088) \/ (sh ff <= fst iv /\ snd iv <= sh ff + 512)
    \/ In iv XSn.

  Lemma hinv_callee : forall e ff fp XSc XSn sk LBk sk' LBk' m1 m2 W,
    hpre H e -> hinv H e ff fp XSc sk LBk m1 ->
    munch W m1 m2 -> wmono asegs m1 m2 -> mem_inv asegs m2 -> stk asegs m2 (e_lo e) (eS1 e) ->
    as_RFS H ((6, ff, fp) :: e_LF e) m2 -> ACONST m2 -> as_RHEAP H sk' LBk' m2 ->
    Forall (fs_scratch H ((6, ff, fp) :: e_LF e)) XSn -> Forall (cwin e ff XSn) W ->
    hinv H e ff fp (XSc ++ XSn) sk' LBk' m2.
  Proof.
    intros e ff fp XSc XSn sk LBk sk' LBk' m1 m2 W HP HI MU WM MI2 ST2 RF2 AC2 RH2 FSn FW.
    destruct HI as (RF & FF & RH & AC & MI & S0 & RA & (errv & ER) & ST & SV & SF & WF & XP & FS & LVI).
    pose proof (hpre_geo e HP) as (CE & LO' & SH1 & SH2 & _ & TP).
    pose proof (eS1_facts e HP) as (_ & S1SP & _ & _ & LOS1 & _).
    pose proof (hpre_RH0 e HP) as RH0.
    assert (LO : e_lo e <= eSP e - 104) by lia. assert (SPH : eSP e <= AAPP_HI) by lia. clear LO' SH1 SH2.

    assert (WOK : Forall (fun iv => (forall LBk0, aclient_write_ok H LBk0 iv) /\ aconst_ok iv /\ stack0_ok iv
                           /\ ((aceil <= fst iv /\ snd iv <= eSP e) \/ (forall a, fst iv <= a < snd iv -> rin_ivs (XH H ff fp ++ XSc ++ XSn) a))
                           /\ (snd iv <= eSP e - 104 \/ eSP e <= fst iv) /\ (snd iv <= ff + 4088 \/ ff + 4096 <= fst iv)
                           /\ (snd iv <= ATP - 164 \/ ATP - 160 <= fst iv) /\ (snd iv <= eS1 e \/ eSP e <= fst iv)) W).
    { eapply Forall_impl; [| exact FW]. intros iv CW. unfold cwin in CW.
      destruct CW as [CW|[CW|[CW|CW]]].
      - destruct (hwin_ok e ff fp (XSc ++ XSn) iv FF CE LO SPH ltac:(left; lia)) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
        repeat split; try assumption. left; lia.
      - destruct (hwin_ok e ff fp (XSc ++ XSn) iv FF CE LO SPH ltac:(right; left; exact CW)) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
        pose proof (hframe_facts _ _ _ FF) as (F1 & F2 & _). pose proof aceil_facts.
        repeat split; try assumption. left; lia.
      - destruct (hwin_ok e ff fp (XSc ++ XSn) iv FF CE LO SPH ltac:(right; right; exact CW)) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
        pose proof (hframe_facts _ _ _ FF) as (_ & F2 & _ & _ & _ & _ & _ & _ & _ & _ & F11 & _ & _ & _ & F15 & _).
        pose proof aceil_facts. assert (sh (ff + 4096) <= sh aceil) by (apply sh_mono; lia).
        assert (sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
        repeat split; try assumption. left; lia.
      - pose proof (proj1 (Forall_forall _ _) FSn iv CW) as FSi.
        destruct (fsw_ok e ff fp m2 iv RF2 FF CE FSi) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
        repeat split; try assumption; try (left; lia).
        right. intros a Ha. apply rin_ivs_app. right. apply rin_ivs_app. right.
        clear - CW Ha. induction XSn as [|iv' XSn IH]; [destruct CW|]. destruct CW as [->|CW]; [left; exact Ha| right; exact (IH CW)]. }
    assert (A1 : forall LBk0, Forall (aclient_write_ok H LBk0) W) by (intros LBk0; eapply Forall_impl; [| exact WOK]; intros iv X; apply X).
    assert (A3 : Forall aconst_ok W) by (eapply Forall_impl; [| exact WOK]; intros iv X; apply X).
    assert (A4 : Forall stack0_ok W) by (eapply Forall_impl; [| exact WOK]; intros iv X; apply X).
    assert (A5 : Forall (fun iv : Z * Z => (aceil <= fst iv /\ snd iv <= eSP e) \/ (forall a, fst iv <= a < snd iv -> rin_ivs (XH H ff fp ++ XSc ++ XSn) a)) W)
      by (eapply Forall_impl; [| exact WOK]; intros iv X; apply X).
    assert (DJ : forall A n, (forall iv, In iv W -> snd iv <= A \/ A + n <= fst iv) -> disjoint_from W A n).
    { intros A n K. clear - K. induction W as [|[x y] W IH]; cbn; [exact I|].
      split; [destruct (K (x, y) (or_introl eq_refl)); cbn in *; lia | apply IH; intros iv Hiv; apply K; right; exact Hiv]. }
    assert (DSV : disjoint_from W (eSP e - 104) 104)
      by (apply DJ; intros iv Hiv; pose proof (proj1 (Forall_forall _ _) WOK iv Hiv) as X; destruct X as (_ & _ & _ & _ & X & _); lia).
    assert (DSF : disjoint_from W (ff + 4088) 8)
      by (apply DJ; intros iv Hiv; pose proof (proj1 (Forall_forall _ _) WOK iv Hiv) as X; destruct X as (_ & _ & _ & _ & _ & X & _); lia).
    assert (DER : disjoint_from W (ATP - 164) 4)
      by (apply DJ; intros iv Hiv; pose proof (proj1 (Forall_forall _ _) WOK iv Hiv) as X; destruct X as (_ & _ & _ & _ & _ & _ & X & _); lia).
    assert (DST : disjoint_from W (eS1 e) (eSP e - eS1 e))
      by (apply DJ; intros iv Hiv; pose proof (proj1 (Forall_forall _ _) WOK iv Hiv) as X; destruct X as (_ & _ & _ & _ & _ & _ & _ & X); lia).
    unfold hinv. rewrite (errno_ATP e TP) in ER |- *.
    split; [exact RF2|]. split; [exact FF|]. split; [exact RH2|]. split; [exact AC2|]. split; [exact MI2|].
    split; [eapply stack0_transport; [exact S0 | exact MU | exact WM | exact A4]|].
    split; [eapply (ah_rauxv_frame H HH); [exact RA | exact MU | exact WM | exact (A1 LBk)]|].
    split; [exists errv; eapply rw_cells_transport; [exact ER | exact MU | exact WM | exact DER]|].
    split.
    { destruct (stk_split asegs m1 (e_lo e) (eS1 e) (eSP e) ST ltac:(lia)) as [_ STu].
      assert (STu2 : stk asegs m2 (eS1 e) (eSP e)) by (eapply stk_transport_disjoint; [exact STu | exact MU | exact WM | exact DST]).
      exact (stk_merge asegs m2 (e_lo e) (eS1 e) (eSP e) ST2 STu2 ltac:(lia)). }
    split; [eapply rw_cells_transport; [exact SV | exact MU | exact WM | exact DSV]|].
    split; [eapply rw_cells_transport; [exact SF | exact MU | exact WM | exact DSF]|].
    split; [exact (wr_at_wmono _ _ _ _ WF WM)|].
    split; [| split].
    - eapply xpres_trans.
      + eapply xpres_weaken; [exact XP | lia | intros b Hb; exact Hb |]. intros a Ha. cbn [rin_ivs] in Ha. destruct Ha as [Ha|Ha]; [left; exact Ha | right].
        apply rin_ivs_app in Ha as [Ha|Ha].
        * apply rin_ivs_app. left. exact Ha.
        * apply rin_ivs_app. right. apply rin_ivs_app. left. exact Ha.
      + eapply (xpres_of_munch H (e_s e) (e_LB e) (eSP e) _ W (e_m e)); [exact HH | exact RH0 | exact MU | exact WM |].
        eapply Forall_impl; [| exact A5]. intros iv [K|K]; [left; exact K | right; intros a Ha; right; exact (K a Ha)].
    - apply Forall_app. split; [exact FS|]. eapply Forall_impl; [| exact FSn]. intros iv X. exact (fs_scratch_mono _ _ _ X).
    -
      eapply LbB_TdKit.LINV_P5_munch_hi; [exact LVI | exact MU |]. eapply Forall_impl; [| exact FW]. intros iv HW.
      pose proof (hframe_facts _ _ _ FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
      pose proof aceil_facts as ACF. unfold cwin in HW. destruct HW as [(W1 & _)|[(W1 & _)|[(W1 & _)|HW]]]; [unfold AIMG_TOP; lia | unfold AIMG_TOP; lia | unfold AIMG_TOP; lia |].
      exact (LbB_TdKit.fs_scratch_above H HH _ m2 iv RF2 (proj1 (Forall_forall _ _) FSn iv HW)).
  Qed.

  Lemma hkeep : forall e ff fp XSc sk LBk m' a,
    hpre H e -> hinv H e ff fp XSc sk LBk m' -> 0 <= a < 2 ^ 64 ->
    ((exists p A n, In (p, A, n) (e_LB e) /\ ((A <= a < A + n) \/ (sh A <= a < sh A + nsh n))) \/ (aimg_client a /\ ~ (RtB_Td.ATDLOC <= a < RtB_Td.ATDLOC + 8)) \/ eSP e <= a) ->
    m' (wa a) = e_m e (wa a) /\ (wview asegs (e_m e) (wa a) <> None -> wview asegs m' (wa a) <> None).
  Proof.
    intros e ff fp XSc sk LBk m' a HP HI Ha K.
    destruct HI as (_ & FF & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & XP & FS & _).
    pose proof (hpre_RH0 e HP) as RH0.
    pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RF0 & _).
    pose proof (hpre_geo e HP) as (CE & LO & SH1 & SH2 & _ & _).
    pose proof aceil_facts as ACF.
    assert (FSA : Forall (fs_scratch H (e_LF e)) (XH H ff fp ++ XSc))
      by (apply Forall_app; split; [exact (fs_scratch_of_fresh H (e_LF e) 6 ff fp FF) | exact FS]).
    apply XP; [exact Ha|]. split.
    - unfold aclient_addr. destruct K as [(p & A & n & IN & [K|K])|[K|K]].
      + right; right; left. exists (p, A, n). split; [exact IN| cbn; lia].
      + right; right; right; left. exists (p, A, n). split; [exact IN| cbn; lia].
      + right; left. exact (proj1 K).
      + left. exact K.
    - apply rin_ivs_none. apply Forall_cons.
      { cbn [fst snd]. destruct K as [(p & A & n & IN & [K|K])|[[K1 K2]|K]].
        - pose proof (ah_blocks H HH _ _ _ _ RH0 IN) as (B0 & B16 & Bn & BI & BC & BF & BAPP). cbn in *. right. unfold RtB_Td.ATDLOC, AIMG_TOP in *. lia.
        - right. unfold sh in K. rewrite ASHADOW_BASE_val in K. pose proof (ah_blocks H HH _ _ _ _ RH0 IN) as (B0 & B16 & Bn & BI & BC & BF & BAPP). cbn in *.
          unfold RtB_Td.ATDLOC. Z.div_mod_to_equations. lia.
        - lia.
        - right. unfold RtB_Td.ATDLOC. lia. }
      eapply Forall_impl; [| exact FSA]. intros iv FSi.
      destruct K as [(p & A & n & IN & [K|K])|[[K KTD]|K]].
      + pose proof (ah_blocks H HH _ _ _ _ RH0 IN) as (B0 & B16 & Bn & BI & BC & BF & BAPP). cbn in *.
        pose proof (fsobj_scratch H HH (e_LF e) A n (e_m e) iv RF0 (fsobj_block H HH _ _ _ _ p A n RH0 IN) ltac:(lia) Bn
                      ltac:(unfold AAPP_HI; lia) BAPP FSi). lia.
      + pose proof (ah_blocks H HH _ _ _ _ RH0 IN) as (B0 & B16 & Bn & BI & BC & BF & BAPP). cbn in *.
        pose proof (fsobj_scratch_sh H HH (e_LF e) A n (e_m e) iv RF0 (fsobj_block H HH _ _ _ _ p A n RH0 IN) ltac:(lia) Bn
                      ltac:(unfold AAPP_HI; lia) FSi). lia.
      + destruct FSi as [->|(k & ff' & fp' & FF' & E)].
        * pose proof (proj1 (ah_RFS_range H HH _ _ RF0)) as (Q1 & _). unfold aimg_client, AIMG_TOP in *. cbn. lia.
        * pose proof (fresh_frame_facts H _ _ _ _ FF') as (K0 & R1 & R2 & _ & _ & P1 & _).
          assert (sh AIMG_TOP <= sh ff') by (apply sh_mono; unfold AIMG_TOP, AFS_HDR in *; lia).
          replace (sh AIMG_TOP) with 0x800d5000 in * by reflexivity.
          unfold aimg_client, AIMG_TOP, AFS_HDR, AFS_FLAGS in *. destruct E as [->|[->| ->]]; cbn; lia.
      + destruct FSi as [->|(k & ff' & fp' & FF' & E)].
        * pose proof (proj1 (ah_RFS_range H HH _ _ RF0)) as (_ & Q2 & _). unfold AFS_FLAGS, AFS_SIZE in *. cbn. lia.
        * pose proof (fresh_frame_facts H _ _ _ _ FF') as (K0 & R1 & R2 & _ & _ & P1 & P2 & _).
          pose proof (fsz_pos k ltac:(lia)).
          assert (sh (ff' + fsz k) <= sh aceil) by (apply sh_mono; lia).
          assert (sh ff' + fshn k = sh (ff' + fsz k)) by (unfold sh, fshn, fsz; Z.div_mod_to_equations; nia).
          assert (sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
          destruct E as [->|[->| ->]]; cbn; lia.
  Qed.
  Lemma sh_in_range : forall A n x, 0 <= A -> A mod 8 = 0 -> A <= x < A + n -> sh A <= sh x < sh A + nsh n.
  Proof. intros A n x H0 H8 Hx. unfold sh, nsh. Z.div_mod_to_equations. nia. Qed.

  Lemma haccessible : forall e ff fp XSc sk LBk m' p A n, hpre H e -> hinv H e ff fp XSc sk LBk m' ->
    In (p, A, n) (e_LB e) -> accessible (e_m e) A n -> accessible m' A n.
  Proof.
    intros e ff fp XSc sk LBk m' p A n HP HI IN (A0 & A1 & AX).
    pose proof (ah_blocks H HH _ _ _ _ (hpre_RH0 e HP) IN) as (B0 & B16 & Bn & BI & BC & BF & BAPP). cbn in *.
    assert (B8 : A mod 8 = 0) by (clear - B16; Z.div_mod_to_equations; lia).
    split; [lia|]. split; [lia|]. intros x Hx. destruct (AX x Hx) as (v & V1 & V2 & V3). exists v. split; [exact V1|]. split; [|exact V3].
    pose proof (sh_in_range A n x ltac:(lia) B8 Hx) as SR.
    assert (SB : 0 <= sh x < 2 ^ 64) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; unfold AAPP_HI in *; lia).
    unfold mrd in *. rewrite (proj1 (hkeep e ff fp XSc sk LBk m' (sh x) HP HI SB ltac:(left; exists p, A, n; split; [exact IN| right; exact SR]))).
    exact V2.
  Qed.

  Lemma hbytes : forall e ff fp XSc sk LBk m' p A n a bs, hpre H e -> hinv H e ff fp XSc sk LBk m' ->
    In (p, A, n) (e_LB e) -> A <= a -> a + Z.of_nat (length bs) <= A + n -> bytes_at asegs (e_m e) a bs -> bytes_at asegs m' a bs.
  Proof.
    intros e ff fp XSc sk LBk m' p A n a bs HP HI IN H1 H2 (B0 & B1 & B).
    split; [lia|]. split; [lia|]. intros i Hi.
    unfold mrd. rewrite (proj1 (hkeep e ff fp XSc sk LBk m' (a + Z.of_nat i) HP HI ltac:(lia) ltac:(left; exists p, A, n; split; [exact IN| left; lia]))).
    exact (B i Hi).
  Qed.

  Lemma hpre_linv : forall e, hpre H e -> LINV_P5 (e_m e).
  Proof. intros e HP. pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LV & _). exact LV. Qed.

  Lemma hlinv : forall e ff fp XSc sk LBk m', hpre H e -> hinv H e ff fp XSc sk LBk m' -> LINV_P5 m'.
  Proof using HH.
    intros e ff fp XSc sk LBk m' HP HI.
    apply HI.
  Qed.

  Lemma hchain : forall e ff fp XSc sk LBk m', hpre H e -> hinv H e ff fp XSc sk LBk m' ->
    as_chain H m' (bv_unsigned (e_s0 e)) (e_CH e).
  Proof.
    intros e ff fp XSc sk LBk m' HP HI.
    pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                      & CHN & _ & CHU & _).
    eapply (ah_chain_ext H HH); [exact CHN|]. intros f r a IN Ha.
    pose proof (ah_chain_range H HH _ _ _ f r CHN IN) as (R1 & R2 & R3). pose proof (CHU f r IN). pose proof aceil_facts.
    assert (X1 : 0 <= a < 2 ^ 64) by lia. assert (X2 : eSP e <= a) by lia.
    exact (proj1 (hkeep e ff fp XSc sk LBk m' a HP HI X1 (or_intror (or_intror X2)))).
  Qed.

  Section Proj.
    Variables (e : hent H) (ff fp : Z) (XSc : list (Z * Z)) (sk : as_St H) (LBk : list block) (m : mem).
    Hypothesis HI : hinv H e ff fp XSc sk LBk m.
    Lemma hinv_rf : as_RFS H ((6, ff, fp) :: e_LF e) m.             Proof. apply HI. Qed.
    Lemma hinv_ff : fresh_frame H (e_LF e) 6 ff fp.                  Proof. apply HI. Qed.
    Lemma hinv_rh : as_RHEAP H sk LBk m.                             Proof. apply HI. Qed.
    Lemma hinv_ac : ACONST m.                                        Proof. apply HI. Qed.
    Lemma hinv_mi : mem_inv asegs m.                                 Proof. apply HI. Qed.
    Lemma hinv_s0 : stack0 m (e_lo e) (e_shi e).                     Proof. apply HI. Qed.
    Lemma hinv_stk : stk asegs m (e_lo e) (eSP e).                   Proof. apply HI. Qed.
    Lemma hinv_sf : rw_cells asegs m (ff + 4088) [C8 (Z_to_bv 64 fp)]. Proof. apply HI. Qed.
    Lemma hinv_wf : wr_at asegs m ff 8.                              Proof. apply HI. Qed.
    Lemma hinv_sv : rw_cells asegs m (eSP e - 104) (esaved e).         Proof. apply HI. Qed.
    Lemma hinv_ra : as_rauxv_ok H m (e_B e).                         Proof. apply HI. Qed.
    Lemma hinv_er : exists errv, rw_cells asegs m (errno_addr (e_tp e)) [C4 errv]. Proof. apply HI. Qed.

  End Proj.
  Lemma hpre_D : forall e, hpre H e -> 0 <= e_D e < 2 ^ 64.
  Proof.
    intros e HP. pose proof HP as (_ & BY & LEN & NR & _ & _ & DZ & _).
    destruct BY as (B1 & B2 & _). destruct (Z.eq_dec (e_N e) 0) as [E0|E0].
    - rewrite (DZ E0). unfold AFUZZ_EMPTY. lia.
    - lia.
  Qed.

  Lemma lb_remove_keep : forall p LB b, List.NoDup (map blk_id LB) -> In b LB -> blk_id b <> p -> In b (as_lb_remove H p LB).
  Proof.
    intros p LB b ND IN NE. pose proof (ah_lb_remove H HH) as (L1 & L2 & L3).
    induction LB as [|b' LB IH]; [destruct IN|]. cbn [map] in ND. apply NoDup_cons_iff in ND as [ND1 ND2].
    destruct (Z.eq_dec (blk_id b') p) as [E|E].
    - destruct b' as [[p' A'] n']. cbn in E. subst p'. rewrite L1 by exact ND1.
      destruct IN as [<-|IN]; [cbn in NE; congruence | exact IN].
    - rewrite L2 by exact E. destruct IN as [<-|IN]; [left; reflexivity | right; exact (IH ND2 IN)].
  Qed.

  Lemma lb_remove_perm : forall p A n LB, List.NoDup (map blk_id LB) -> In (p, A, n) LB ->
    Permutation LB ((p, A, n) :: as_lb_remove H p LB).
  Proof.
    intros p A n LB ND IN. pose proof (ah_lb_remove H HH) as (L1 & L2 & L3).
    induction LB as [|b LB IH]; [destruct IN|]. cbn [map] in ND. apply NoDup_cons_iff in ND as [ND1 ND2].
    destruct (Z.eq_dec (blk_id b) p) as [E|E].
    - destruct b as [[p' A'] n']. cbn in E. subst p'. rewrite L1 by exact ND1.
      destruct IN as [EQ|IN]; [rewrite EQ; reflexivity|].
      exfalso. apply ND1. apply in_map_iff. exists (p, A, n). split; [reflexivity | exact IN].
    - rewrite L2 by exact E. destruct IN as [EQ|IN]; [subst b; cbn in E; congruence|].
      specialize (IH ND2 IN). eapply perm_trans; [apply perm_skip; exact IH|]. apply perm_swap.
  Qed.

  Lemma hinv_sr_gen : forall e ff fp XSc XSn Xc sk LBk LBx sk' LBk' m1 m2,
    hpre H e -> hinv H e ff fp XSc sk LBk m1 ->
    (forall b, In b (e_LB e) -> In b LBx) ->
    xpres H LBx (eS1 e) Xc m1 m2 ->
    Forall (fs_scratch H ((6, ff, fp) :: e_LF e)) XSn ->
    Forall (fun iv : Z * Z => In iv XSn \/ (ff + 8 <= fst iv /\ snd iv <= ff + 4088) \/ (sh ff <= fst iv /\ snd iv <= sh ff + 512)
                              \/ iv = (RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8)) Xc ->
    as_RFS H ((6, ff, fp) :: e_LF e) m2 -> as_RHEAP H sk' LBk' m2 -> ACONST m2 -> mem_inv asegs m2 ->
    stk asegs m2 (e_lo e) (eS1 e) -> (exists errv', rw_cells asegs m2 (errno_addr (e_tp e)) [C4 errv']) -> as_rauxv_ok H m2 (e_B e) ->
    LINV_P5 m2 ->
    hinv H e ff fp (XSc ++ XSn) sk' LBk' m2.
  Proof.
    intros e ff fp XSc XSn Xc sk LBk LBx sk' LBk' m1 m2 HP HI INC XP FSn FXc RF2 RH2 AC2 MI2 ST2 ER2 RA2 LV2.
    destruct HI as (RF & FF & RH & AC & MI & S0 & RA & _ & ST & SV & SF & WF & XP0 & FS & LVI).
    pose proof (hpre_geo e HP) as (CE & LO' & SH1 & SH2 & _ & TP).
    pose proof (eS1_facts e HP) as (_ & S1SP & _ & _ & LOS1 & _).
    pose proof (hframe_facts _ _ _ FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof aceil_facts as ACF.
    assert (SHC : sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHF : sh (ff + 4096) <= sh aceil) by (apply sh_mono; lia).

    assert (XW : Forall (fun iv : Z * Z => (snd iv <= e_lo e /\ stack0_ok iv)
                           /\ (snd iv <= ff + 8 \/ ff + 4096 <= fst iv \/ snd iv <= ff + 4088 /\ ff + 8 <= fst iv)
                           /\ (snd iv <= ff \/ ff + 4096 <= fst iv \/ (ff + 8 <= fst iv /\ snd iv <= ff + 4088))
                           /\ (forall a, fst iv <= a < snd iv -> rin_ivs ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8) :: XH H ff fp ++ XSc ++ XSn) a)) Xc).
    { eapply Forall_impl; [| exact FXc]. intros iv K. destruct K as [K|[K|[K|K]]].
      - pose proof (proj1 (Forall_forall _ _) FSn iv K) as FSi.
        destruct (fsw_ok e ff fp m2 iv RF2 FF CE FSi) as (_ & _ & B3 & B4 & B5 & B6 & B7 & _).
        split; [split; [exact B7 | exact B3]|]. split; [destruct B5; [left; lia | right; left; lia]|]. split; [destruct B5; [left | right; left]; lia|].
        intros a Ha. right. apply rin_ivs_app. right. apply rin_ivs_app. right.
        clear - K Ha. induction XSn as [|iv' XSn IH]; [destruct K|]. destruct K as [->|K]; [left; exact Ha| right; exact (IH K)].
      - split; [split; [lia | destruct iv as [x y]; cbn [fst snd] in *; eapply (stack0_ok_aapp (as_FSB H) AFS_SIZE); [exact F10 | lia | lia]]|].
        split; [right; right; lia|]. split; [right; right; lia|].
        intros a Ha. right. apply rin_ivs_app. left. cbn. right; right; left. change (fsz 6) with 4096. lia.
      - split; [split; [lia | right; lia]|]. split; [destruct F16; [left | right; left]; lia|]. split; [destruct F16; [left | right; left]; lia|].
        intros a Ha. right. apply rin_ivs_app. left. cbn. right; right; right; left. change (fshn 6) with 512. lia.
      -
        subst iv. cbn [fst snd]. split; [split; [unfold RtB_Td.ATDLOC; lia | exact RtB_Td.stack0_ok_td]|].
        split; [left; unfold RtB_Td.ATDLOC; lia|]. split; [left; unfold RtB_Td.ATDLOC; lia|].
        intros a Ha. left. cbn [fst snd]. exact Ha. }
    assert (XCL : forall A n, (forall iv, In iv Xc -> A + n <= fst iv \/ snd iv <= A) -> aclient_range H LBx (eS1 e) A n ->
                    xclient_range H LBx (eS1 e) Xc A n).
    { intros A n K CL. split; [exact CL|]. apply Forall_forall. intros iv Hiv. exact (K iv Hiv). }
    assert (LBI : forall b, In b (e_LB e) -> In b LBx) by exact INC.
    unfold hinv.
    split; [exact RF2|]. split; [exact FF|]. split; [exact RH2|]. split; [exact AC2|]. split; [exact MI2|].
    split.
    { eapply (stack0_xpres H); [exact XP | exact S0 |]. eapply Forall_impl; [| exact XW]. intros iv ((_ & K1) & _). exact K1. }
    split; [exact RA2|]. split; [exact ER2|].
    split.
    { destruct (stk_split asegs m1 (e_lo e) (eS1 e) (eSP e) ST ltac:(lia)) as [_ STu].
      assert (STu2 : stk asegs m2 (eS1 e) (eSP e)).
      { eapply xpres_stk; [exact XP | exact STu | lia |]. eapply Forall_impl; [| exact XW]. intros iv ((K1 & _) & _). right. lia. }
      exact (stk_merge asegs m2 (e_lo e) (eS1 e) (eSP e) ST2 STu2 ltac:(lia)). }
    split.
    { eapply xpres_rw_cells; [exact XP | exact SV |]. apply XCL; [| left; lia].
      intros iv Hiv. pose proof (proj1 (Forall_forall _ _) XW iv Hiv) as ((K1 & _) & _). right; lia. }
    split.
    { eapply xpres_rw_cells; [exact XP | exact SF |]. apply XCL.
      - intros iv Hiv. pose proof (proj1 (Forall_forall _ _) XW iv Hiv) as (_ & K2 & _). cbn [cells_size csize]. lia.
      - right; right; right; right; left. cbn [cells_size csize]. lia. }
    split.
    { eapply xpres_wr_at; [exact XP | exact WF |]. apply XCL.
      - intros iv Hiv. pose proof (proj1 (Forall_forall _ _) XW iv Hiv) as (_ & _ & K3 & _). lia.
      - right; right; right; right; left. lia. }
    split.
    { eapply xpres_trans; [eapply xpres_weaken; [exact XP0 | lia | intros b Hb; exact Hb |] |].
      - intros a Ha. cbn [rin_ivs] in Ha. destruct Ha as [Ha|Ha]; [left; exact Ha | right].
        apply rin_ivs_app in Ha as [Ha|Ha]; [apply rin_ivs_app; left; exact Ha|].
        apply rin_ivs_app; right; apply rin_ivs_app; left; exact Ha.
      - eapply xpres_weaken; [exact XP | lia | exact LBI |]. intros a Ha.
        clear - XW Ha. induction Xc as [|iv Xc IH]; [destruct Ha|]. inversion XW as [|? ? X1 X2]; subst.
        destruct Ha as [Ha|Ha]; [exact ((proj2 (proj2 (proj2 X1))) a Ha) | exact (IH X2 Ha)]. }
    split; [| exact LV2].
    apply Forall_app. split; [exact FS|]. eapply Forall_impl; [| exact FSn]. intros iv X. exact (fs_scratch_mono _ _ _ X).
  Qed.

  Lemma hinv_sr : forall e ff fp XSc XSn Xc sk LBk LBx sk' LBk' m1 m2,
    hpre H e -> hinv H e ff fp XSc sk LBk m1 ->
    (forall b, In b (e_LB e) -> In b LBx) ->
    xpres H LBx (eS1 e) Xc m1 m2 ->
    Forall (fs_scratch H ((6, ff, fp) :: e_LF e)) XSn ->
    Forall (fun iv : Z * Z => In iv XSn \/ (ff + 8 <= fst iv /\ snd iv <= ff + 4088) \/ (sh ff <= fst iv /\ snd iv <= sh ff + 512)) Xc ->
    as_RFS H ((6, ff, fp) :: e_LF e) m2 -> as_RHEAP H sk' LBk' m2 -> ACONST m2 -> mem_inv asegs m2 ->
    stk asegs m2 (e_lo e) (eS1 e) -> (exists errv', rw_cells asegs m2 (errno_addr (e_tp e)) [C4 errv']) -> as_rauxv_ok H m2 (e_B e) ->
    hinv H e ff fp (XSc ++ XSn) sk' LBk' m2.
  Proof.
    intros e ff fp XSc XSn Xc sk LBk LBx sk' LBk' m1 m2 HP HI INC XP FSn FXc RF2 RH2 AC2 MI2 ST2 ER2 RA2.
    eapply (hinv_sr_gen e ff fp XSc XSn Xc sk LBk LBx sk' LBk' m1 m2); try eassumption.
    - eapply Forall_impl; [| exact FXc]. intros iv [K|[K|K]]; [left | right; left | right; right; left]; exact K.
    - pose proof HI as (_ & FF & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LVI).
      pose proof (hframe_facts _ _ _ FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
      eapply (LbB_TdKit.LINV_P5_xpres_hi H); [exact LVI | exact XP |].
      eapply Forall_impl; [| exact FXc]. intros iv [K|[K|K]].
      + exact (LbB_TdKit.fs_scratch_above H HH _ m2 iv RF2 (proj1 (Forall_forall _ _) FSn iv K)).
      + unfold AIMG_TOP. lia.
      + unfold AIMG_TOP. lia.
  Qed.

  Lemma hchain_call : forall e ff fp XSc sk LBk m', hpre H e -> hinv H e ff fp XSc sk LBk m' ->
    as_chain H m' (eSP e) ((eSP e, bv_unsigned (e_ra e)) :: e_CH e)
    /\ (forall f r, In (f, r) ((eSP e, bv_unsigned (e_ra e)) :: e_CH e) -> eS1 e + 16 <= f).
  Proof.
    intros e ff fp XSc sk LBk m' HP HI.
    pose proof (hchain e ff fp XSc sk LBk m' HP HI) as CH0.
    pose proof (hinv_sv e ff fp XSc sk LBk m' HI) as SV.
    pose proof (hpre_geo e HP) as (CE & LO & SH1 & SH2 & SP16 & _).
    pose proof (eS1_facts e HP) as (_ & S1SP & _ & _ & _ & _).
    pose proof aceil_facts as ACF.
    pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                      & _ & _ & CHU & _).
    change (esaved e) with ([C8 (e_s11 e); C8 (e_s10 e); C8 (e_s9 e); C8 (e_s8 e); C8 (e_s7 e); C8 (e_s6 e); C8 (e_s5 e); C8 (e_s4 e);
                             C8 (e_s3 e); C8 (e_s2 e); C8 (e_s1 e)] ++ [C8 (e_s0 e); C8 (e_ra e)]) in SV.
    apply rw_cells_app in SV as [_ SV2]. cbn [cells_size csize] in SV2.
    replace (eSP e - 104 + Z.of_nat (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + 0))))))))))))
      with (eSP e - 16) in SV2 by lia.
    pose proof (bv_unsigned_in_range 64 (e_s0 e)) as R0. pose proof (bv_unsigned_in_range 64 (e_ra e)) as R1.
    change (bv_modulus 64) with (2 ^ 64) in R0, R1.
    split.
    - eapply (ah_chain_cons H HH); [exact CH0 | lia | lia | exact SP16 | unfold AAPP_HI in *; lia | unfold AAPP_HI in *; lia |].
      rewrite !Z_to_bv_bv_unsigned. exact SV2.
    - intros f r [EQ|IN]; [injection EQ as <- <-; lia|]. pose proof (CHU f r IN). lia.
  Qed.

  Lemma htrace : forall e pc0 p, hpre H e -> In (pc0, p) TOP_PF -> trace_ok (as_TR H) pc0 (p ++ bv_unsigned (e_ra e) :: map snd (e_CH e)).
  Proof.
    intros e pc0 p HP IN.
    pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                      & _ & PF & _).
    exact (pf_ok_site (as_TR H) TOP_PF (bv_unsigned (e_ra e)) (e_CH e) pc0 p PF IN).
  Qed.

  Lemma hinv_blockw : forall e ff fp XSc sk LBk m1 m2 W pv P k,
    hpre H e -> hinv H e ff fp XSc sk LBk m1 -> In (pv, P, k) LBk ->
    (forall b, In b (e_LB e) -> In b LBk /\ blk_id b <> pv) ->
    munch W m1 m2 -> wmono asegs m1 m2 -> mem_inv asegs m2 ->
    Forall (fun iv : Z * Z => P <= fst iv /\ snd iv <= P + k) W ->
    hinv H e ff fp XSc sk LBk m2.
  Proof.
    intros e ff fp XSc sk LBk m1 m2 W pv P k HP HI INv LBI MU WM MI2 FW.
    destruct HI as (RF & FF & RH & AC & MI & S0 & RA & (errv & ER) & ST & SV & SF & WF & XP & FS & LVI).
    pose proof (hpre_geo e HP) as (CE & LO & SH1 & SH2 & _ & TP).
    pose proof (hframe_facts _ _ _ FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof (ah_blocks H HH _ _ _ _ RH INv) as (B0 & B16 & Bn & BI & BC & BF & BAPP). cbn in B0, B16, Bn, BI, BC, BF, BAPP.
    pose proof aceil_facts as ACF.
    assert (WW : Forall (fun iv => aclient_write_ok H LBk iv /\ afs_write_ok H ((6, ff, fp) :: e_LF e) iv /\ aconst_ok iv /\ stack0_ok iv) W).
    { eapply Forall_impl; [| exact FW]. intros [x y] (X1 & X2). cbn [fst snd] in *.
      split; [right; right; left; exists (pv, P, k); split; [exact INv | cbn; lia]|].
      split; [left; cbn [fst snd]; split; [destruct BF; [left | right]; unfold AFS_SIZE in *; lia | right; unfold ATLS_PRIV_HI, ATP, AIMG_TOP in *; lia]|].
      split; [eapply (aconst_ok_app P k); [exact BAPP | exact X1 | exact X2]|].
      eapply (stack0_ok_aapp P k); [exact BAPP | exact X1 | exact X2]. }
    assert (DJ : forall A n, (A + n <= P \/ P + k <= A) -> disjoint_from W A n).
    { intros A n K. clear - FW K. induction W as [|[x y] W IH]; cbn; [exact I|]. inversion FW as [|? ? X1 X2]; subst. cbn in X1.
      split; [lia | exact (IH X2)]. }
    unfold hinv. rewrite (errno_ATP e TP) in ER |- *.
    split; [eapply (ah_RFS_frame H HH); [exact RF | exact MU | exact WM | eapply Forall_impl; [| exact WW]; intros iv X; apply X]|].
    split; [exact FF|].
    split; [eapply (ah_RHEAP_frame H HH); [exact RH | exact MU | exact WM | eapply Forall_impl; [| exact WW]; intros iv X; apply X]|].
    split; [eapply ACONST_frame; [exact AC | exact MU | exact WM | eapply Forall_impl; [| exact WW]; intros iv X; apply X]|].
    split; [exact MI2|].
    split; [eapply stack0_transport; [exact S0 | exact MU | exact WM | eapply Forall_impl; [| exact WW]; intros iv X; apply X]|].
    split; [eapply (ah_rauxv_frame H HH); [exact RA | exact MU | exact WM | eapply Forall_impl; [| exact WW]; intros iv X; apply X]|].
    split; [exists errv; eapply rw_cells_transport; [exact ER | exact MU | exact WM | cbn [cells_size csize]; apply DJ; unfold ATP, AIMG_TOP in *; lia]|].
    split; [eapply stk_transport_disjoint; [exact ST | exact MU | exact WM | apply DJ; lia]|].
    split; [eapply rw_cells_transport; [exact SV | exact MU | exact WM | apply DJ; cbn; lia]|].
    split; [eapply rw_cells_transport; [exact SF | exact MU | exact WM | apply DJ; cbn; destruct BF; unfold AFS_SIZE in *; lia]|].
    split; [exact (wr_at_wmono _ _ _ _ WF WM)|].
    split; [| split; [exact FS|]].
    2: {
      eapply LbB_TdKit.LINV_P5_munch_hi; [exact LVI | exact MU |]. eapply Forall_impl; [| exact FW]. intros iv (X1 & _). lia. }
    eapply xpres_trans; [exact XP|]. intros a Ha [Hc _]. split; [| intros X; apply WM; exact X].
    apply MU. unfold wa. rewrite HLib.u64_of_Z by lia. eapply disjoint_outside; [apply (DJ a 1) | lia].
    unfold aclient_addr in Hc.
    destruct Hc as [Hc|[Hc|[(b & INb & Hb)|[(b & INb & Hb)|[Hc|[Hc|Hc]]]]]].
    - lia.
    - unfold aimg_client in Hc. unfold AIMG_TOP in BI. lia.
    - destruct (LBI b INb) as (INb' & NE).
      destruct (ah_disj H HH _ _ _ b (pv, P, k) RH INb' INv NE) as [D|D]; cbn in D; lia.
    - destruct (LBI b INb) as (INb' & _).
      pose proof (ah_blocks H HH _ _ _ _ RH INb') as (C0 & C16 & Cn & CI & CC & CF & CAPP).
      pose proof (aapp_disjoint_sh P k (blk_addr b) (blk_size b) BAPP ltac:(lia) ltac:(unfold AAPP_HI; lia) Cn) as D. lia.
    - destruct BF; unfold AFS_SIZE in *; lia.
    - pose proof (aapp_disjoint_sh P k (as_FSB H) AFS_SIZE BAPP ltac:(lia) ltac:(unfold AAPP_HI, AFS_SIZE in *; lia) ltac:(unfold AFS_SIZE; lia)) as D.
      assert (sh (as_FSB H + AFS_SIZE) <= sh (as_FSB H) + nsh AFS_SIZE) by (unfold sh, nsh; Z.div_mod_to_equations; lia). lia.
    - unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in BAPP, Hc.
      assert (sh 0x7fff7000 <= sh aceil) by (apply sh_mono; lia). replace (sh 0x7fff7000) with 0x8fff6e00 in * by reflexivity. lia.
  Qed.
  Lemma haddressable : forall e ff fp XSc sk LBk m' p A n, hpre H e -> hinv H e ff fp XSc sk LBk m' ->
    In (p, A, n) (e_LB e) -> addressable (e_m e) A n -> addressable m' A n.
  Proof.
    intros e ff fp XSc sk LBk m' p A n HP HI IN (Hn & HA & HA8 & (B0 & B1 & B) & (W0 & W1 & W)).
    rewrite shadow_of_length in B1, W1, W by lia.
    pose proof (ah_blocks H HH _ _ _ _ (hpre_RH0 e HP) IN) as (C0 & C16 & Cn & CI & CC & CF & CAPP). cbn in C0, C16, Cn, CI, CC, CF, CAPP.
    pose proof aceil_facts as ACF.
    assert (X1 : A + n <= AAPP_HI) by (unfold AAPP_HI; lia).
    assert (SB : sh A + nsh n <= 0x10007fff8000) by (pose proof (sh_nsh_high A n ltac:(lia) ltac:(lia) X1); unfold AHI_LO in *; lia).
    assert (KP : forall a, sh A <= a < sh A + nsh n -> m' (wa a) = e_m e (wa a) /\ (wview asegs (e_m e) (wa a) <> None -> wview asegs m' (wa a) <> None)).
    { intros a Ha. apply (hkeep e ff fp XSc sk LBk m' a HP HI); [unfold sh in *; rewrite ASHADOW_BASE_val in *; lia|].
      left. exists p, A, n. split; [exact IN | right; exact Ha]. }
    split; [exact Hn|]. split; [exact HA|]. split; [exact HA8|]. split.
    - split; [exact B0|]. split; [rewrite shadow_of_length by lia; exact B1|]. intros i Hi. unfold mrd.
      assert (Hi' : Z.of_nat i < nsh n) by (rewrite <- shadow_of_length by lia; lia).
      rewrite (proj1 (KP (sh A + Z.of_nat i) ltac:(lia))). exact (B i Hi).
    - split; [exact W0|]. split; [rewrite shadow_of_length by lia; exact W1|]. intros i Hi. rewrite shadow_of_length in Hi by lia.
      apply (proj2 (KP (sh A + i) ltac:(lia))). apply W. exact Hi.
  Qed.
End Kit.
