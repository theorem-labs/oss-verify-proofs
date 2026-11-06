(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac ZBridge RzCPS. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnDivWords BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib BgWords BgArith BgMont BgExp.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout R_unwind_chain RT_iface RT_iface2 RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import MState Mem Cells Step Arr Bytes Frame.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA W_cryptoA W_smallA AsStruct2.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import AFrameKit AFrameCall AFrameTac AFrameEnv BnAKitAF BnCallAF W_callsAF AFrameComp ExpKitAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma num_bits_pure_range : forall b : bignum bptr, limbs (bn_buf b) -> 0 <= num_bits_pure b <= 64 * Z.of_nat (bn_top b).
Proof.
  intros b HL. unfold num_bits_pure. destruct (Nat.eqb_spec (bn_top b) 0) as [E|NE]; [lia|].
  pose proof (limbs_nth (bn_buf b) (bn_top b - 1) HL) as LN. unfold limb, BW in LN.
  pose proof (num_bits_word_le (nth (bn_top b - 1) (bn_buf b) 0) 64 ltac:(lia) LN). lia.
Qed.

Lemma last_nth : forall {A} (l : list A) (d : A), last l d = nth (length l - 1) l d.
Proof.
  intros A l d. induction l as [|x l IH]; [reflexivity|]. destruct l as [|y l']; [reflexivity|].
  change (last (x :: y :: l') d) with (last (y :: l') d). rewrite IH.
  cbn [length]. destruct (length l'); reflexivity.
Qed.

Lemma exp_table_loop_S : forall (mulop : bnref -> bnref -> bnref -> BM (M:=btree bptr) (ptr:=bptr) unit) c vals d (s : bstate bptr),
  exp_table_loop (tree_ops bptr) mulop (S c) vals d s =
  tbind (BN_CTX_get (tree_ops bptr) s)
        (fun p => tbind (mulop (fst p) (last vals 0%nat) d (snd p)) (fun p0 => exp_table_loop (tree_ops bptr) mulop c (vals ++ [fst p]) d (snd p0))).
Proof. reflexivity. Qed.
Lemma exp_table_loop_O : forall (mulop : bnref -> bnref -> bnref -> BM (M:=btree bptr) (ptr:=bptr) unit) vals d (s : bstate bptr),
  exp_table_loop (tree_ops bptr) mulop 0 vals d s = TRet (vals, s).
Proof. reflexivity. Qed.

Section LoopEqs.
  Context (mulop : bnref -> bnref -> bnref -> BM (M:=btree bptr) (ptr:=bptr) unit).
  Lemma exp_sqr_loop_S : forall c r (s : bstate bptr),
    exp_sqr_loop (tree_ops bptr) mulop (S c) r s = tbind (mulop r r r s) (fun p => exp_sqr_loop (tree_ops bptr) mulop c r (snd p)).
  Proof. reflexivity. Qed.
  Lemma exp_sqr_loop_O : forall r (s : bstate bptr), exp_sqr_loop (tree_ops bptr) mulop 0 r s = TRet (tt, s).
  Proof. reflexivity. Qed.
  Lemma tbind_bret : forall {A B} (a : A) (s : bstate bptr) (k : A * bstate bptr -> btree bptr B),
    tbind (bret (tree_ops bptr) a s) k = k (a, s).
  Proof. reflexivity. Qed.
  Lemma ewl_clear : forall f rp rr vals window wstart start (s : bstate bptr),
    is_bit_set_pure (getbn rp s) wstart = false ->
    exp_window_loop (tree_ops bptr) mulop (S f) rp rr vals window wstart start s =
    tbind ((if start then bret (tree_ops bptr) tt else mulop rr rr rr) s)
          (fun p => (if wstart =? 0 then bret (tree_ops bptr) tt else exp_window_loop (tree_ops bptr) mulop f rp rr vals window (wstart - 1) start) (snd p)).
  Proof. intros. cbn [exp_window_loop bbind bget bret bind ret tree_ops tbind]. rewrite H. cbn [negb]. destruct start; reflexivity. Qed.
  Lemma ewl_set : forall f rp rr vals window wstart start (s : bstate bptr) wv we,
    is_bit_set_pure (getbn rp s) wstart = true ->
    window_scan (is_bit_set_pure (getbn rp s)) wstart (Z.to_nat (window - 1)) 1 1 0 = (wv, we) ->
    exp_window_loop (tree_ops bptr) mulop (S f) rp rr vals window wstart start s =
    tbind ((if start then bret (tree_ops bptr) tt else exp_sqr_loop (tree_ops bptr) mulop (Z.to_nat (we + 1)) rr) s)
          (fun p2 => tbind (mulop rr rr (nth (Z.to_nat (Z.shiftr wv 1)) vals 0%nat) (snd p2))
             (fun p => (if wstart - (we + 1) <? 0 then bret (tree_ops bptr) tt else exp_window_loop (tree_ops bptr) mulop f rp rr vals window (wstart - (we + 1)) false) (snd p))).
  Proof. intros. cbn [exp_window_loop bbind bget bret bind ret tree_ops tbind]. rewrite H. cbn [negb]. rewrite H0. destruct start; reflexivity. Qed.
End LoopEqs.

Lemma lor_shiftl_1 : forall wv k, 0 <= wv -> 1 <= k -> Z.lor (Z.shiftl wv k) 1 = wv * 2 ^ k + 1.
Proof.
  intros wv k Hw Hk. rewrite Z.shiftl_mul_pow2 by lia.
  assert (L0 : Z.land (wv * 2 ^ k) 1 = 0).
  { change 1 with (Z.ones 1). rewrite Z.land_ones by lia. change (2 ^ 1) with 2.
    replace (2 ^ k) with (2 * 2 ^ (k - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    replace (wv * (2 * 2 ^ (k - 1))) with ((wv * 2 ^ (k - 1)) * 2) by lia. apply Z.mod_mul. lia. }
  rewrite <- Z.lxor_lor by exact L0. symmetry. apply Z.add_nocarry_lxor. exact L0.
Qed.

Lemma swrap32_plus_2_64 : forall x, bv_swrap 32 (x + 18446744073709551616) = bv_swrap 32 x.
Proof.
  intros x. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 `div` 2) with 2147483648.
  replace (x + 18446744073709551616 + 2147483648) with (x + 2147483648 + 4294967296 * 4294967296) by lia.
  rewrite Z.add_mod, Z.mod_mul, Z.add_0_r, Z.mod_mod by lia. reflexivity.
Qed.

Lemma window_scan_bnd : forall (bit : Z -> bool) wstart c i wv we,
  1 <= i -> 0 <= we < i -> we <= wstart -> 1 <= wv < 2 ^ (we + 1) ->
  let '(wv', we') := window_scan bit wstart c i wv we in
  0 <= we' < i + Z.of_nat c /\ we' <= wstart /\ 1 <= wv' < 2 ^ (we' + 1).
Proof.
  intros bit wstart c. induction c as [|c IH]; intros i wv we Hi Hwe Hws Hwv; cbn [window_scan].
  - lia.
  - destruct (Z.ltb_spec (wstart - i) 0) as [Hl|Hge]; [lia|].
    destruct (bit (wstart - i)).
    + assert (HB : 1 <= Z.lor (Z.shiftl wv (i - we)) 1 < 2 ^ (i + 1)).
      { rewrite lor_shiftl_1 by lia.
        assert (2 ^ (we + 1) * 2 ^ (i - we) = 2 ^ (i + 1)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
        assert (2 <= 2 ^ (i - we)) by (replace (2 ^ (i - we)) with (2 * 2 ^ (i - we - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia);
                                       assert (0 < 2 ^ (i - we - 1)) by (apply Z.pow_pos_nonneg; lia); lia).
        assert (0 <= wv * 2 ^ (i - we)) by (apply Z.mul_nonneg_nonneg; lia).
        split; [lia|]. assert (wv * 2 ^ (i - we) <= (2 ^ (we + 1) - 1) * 2 ^ (i - we)) by (apply Z.mul_le_mono_nonneg_r; lia).
        assert ((2 ^ (we + 1) - 1) * 2 ^ (i - we) = 2 ^ (we + 1) * 2 ^ (i - we) - 2 ^ (i - we)) by lia. lia. }
      specialize (IH (i + 1) (Z.lor (Z.shiftl wv (i - we)) 1) i ltac:(lia) ltac:(lia) ltac:(lia) HB).
      destruct (window_scan bit wstart c (i + 1) (Z.lor (Z.shiftl wv (i - we)) 1) i) as [wv' we']. lia.
    + specialize (IH (i + 1) wv we ltac:(lia) ltac:(lia) ltac:(lia) Hwv). destruct (window_scan bit wstart c (i + 1) wv we) as [wv' we']. lia.
Qed.

Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (le_val_range _ (bytes_ok_map bs)) as HR. rewrite length_map, HL in HR. change (256 ^ Z.of_nat 8) with (2 ^ 64) in HR.
  rewrite <- bytes_le_to_Z_le_val in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.

Lemma u64s_exists : forall k (bs : list byte), length bs = (8 * k)%nat -> exists ws : list word, length ws = k /\ u64s ws = bs.
Proof.
  induction k as [|k IH]; intros bs H.
  - exists []. destruct bs; [split; reflexivity| cbn in H; lia].
  - destruct (IH (skipn 8 bs) ltac:(rewrite length_skipn; lia)) as (ws & Hl & E).
    exists (le_bytes_to_word (firstn 8 bs) :: ws). split; [cbn; lia|]. cbn [u64s].
    rewrite le8_of_bytes by (rewrite length_firstn; lia). rewrite E. apply firstn_skipn.
Qed.

Lemma rw_cells_CB_u64arr : forall m A ws n, n = (8 * length ws)%nat ->
  rw_cells bgbsegs m A [CB n (u64s ws)] <-> u64arr bgbsegs m A ws.
Proof.
  intros m A ws n Hn. unfold rw_cells, cells_at, u64arr. cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize].
  rewrite app_nil_r, u64s_length, Nat.add_0_r. subst n. rewrite Nat2Z.inj_mul. cbn [Z.of_nat Pos.of_succ_nat]. change (Z.pos 8) with 8. tauto.
Qed.

Lemma val_obj_init : forall m A (a0 : word) junk,
  rw_cells bgbsegs m A [C8 a0; CB 248 junk] -> exists ws, length ws = 32%nat /\ nth_error ws 0 = Some a0 /\ u64arr bgbsegs m A ws.
Proof.
  intros m A a0 junk H.
  assert (HLj : length junk = 248%nat) by (destruct H as [[Hwf _] _]; cbn [cells_wf cell_wf] in Hwf; tauto).
  destruct (u64s_exists 31 junk ltac:(rewrite HLj; reflexivity)) as (ws & Hl & E).
  exists (a0 :: ws). split; [cbn; lia|]. split; [reflexivity|].
  apply (rw_cells_CB_u64arr m A (a0 :: ws) 256); [cbn [length]; rewrite Hl; reflexivity|].
  change [C8 a0; CB 248 junk] with ([] ++ ([C8 a0] ++ [CB 248 junk]) ++ []) in H.
  change [CB 256 (u64s (a0 :: ws))] with ([] ++ [CB 256 (u64s (a0 :: ws))] ++ []).
  eapply bk_rw_cells_recast; [exact H| | |].
  - destruct H as [[Hwf _] _]. rewrite !cells_wf_app in *. cbn [cells_wf cell_wf] in *. rewrite u64s_length. cbn [length]. rewrite Hl. tauto.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes u64s]. rewrite E, !app_nil_r. reflexivity.
  - rewrite !cells_size_app. reflexivity.
Qed.

Lemma cb8_word : forall (j : list byte), length j = 8%nat -> exists w : word, le8 w = j.
Proof. intros j H. exists (le_bytes_to_word j). apply le8_of_bytes. exact H. Qed.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Lemma blk_not_static_gen : forall Σ OW LB m b x, AHEAP Σ OW LB m -> In b (OW ++ LB) -> blk_addr b <= x < blk_addr b + blk_size b -> client_static x -> False.
Proof.
  intros Σ OW LB m b x HEAP Hb Hx [(l & h & Hin & Hr) _].
  pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (B0 & _ & _ & _ & BI).
  unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
Qed.

Lemma cenv_objA : forall (b : block) (LB : list block) PL EA lo SPv FB (s0w raw : word) rasO TOTAL Σ0 (ls0 : bstate bptr) OW0 m0 pre used Σ (ls : bstate bptr) m m' OW W,
  cenvA (b :: LB) PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m OW ->
  lib_state ls m OW PL EA ->
  munch W m m' -> wmono bgbsegs m m' ->
  Forall (fun iv : Z * Z => blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b) W ->
  (forall x, blk_addr b <= x < blk_addr b + blk_size b -> ~ rin_ivs (pl_frames PL) x) ->
  stk bgbsegs m' lo FB -> mem_inv bgbsegs m' ->
  cenvA (b :: LB) PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m' pre used Σ ls m' OW
  /\ lib_state ls m' OW PL EA
  /\ ax_pres LB SPv (XW PL) m0 m'.
Proof.
  intros b LB PL EA lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m m' OW W
         (OK & HEAP & ST & MI & AXP & CR & CNT & RS & FR & FSZ & UW) LS MU WM HW NF ST' MI'.
  pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & CNT0 & CRED0 & FROK & FAL & NOFR).
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN in *.
  assert (INB : In b (OW ++ b :: LB)) by (apply in_or_app; right; left; reflexivity).
  pose proof (AH_range_gen _ _ _ _ b HEAP INB) as (B0 & _ & Bn & BC & BI).
  assert (AGO : agree_on (fun a => ~ (blk_addr b <= a < blk_addr b + blk_size b)) m m').
  { eapply agree_on_mono; [apply (agree_on_of_munch _ _ _ MU WM)|]. intros a Ha. cbv beta in Ha. clear - HW Ha.
    induction HW as [|[x y] W' [H1 H2] HW' IH]; [exact I|]. cbn [outside fst snd] in *. split; [lia | exact IH]. }
  assert (HEAP' : AHEAP Σ OW (b :: LB) m').
  { eapply (AH_frame Σ OW (b :: LB) m m' W HEAP MU WM). eapply Forall_impl; [|exact HW].
    intros iv [H1 H2]. right; right. exists b. split; [exact INB | split; [exact H1 | exact H2]]. }
  assert (AGS : agree_on (fun a => FB <= a < USTACK_TOP) m m').
  { eapply agree_on_mono; [exact AGO|]. intros a Ha. cbv beta in *. unfold BnHeapA.ACEIL in *. lia. }
  assert (LS' : lib_state ls m' OW PL EA).
  { eapply (lib_state_frame_lb Σ (b :: LB) SPv USTACK_TOP false [] ls m m' OW PL EA W HEAP LS MU WM FROK).
    eapply Forall_impl; [|exact HW]. intros iv [H1 H2]. right. exists b. split; [left; reflexivity|]. split; [exact H1|]. split; [exact H2|].
    intros x Hx. apply NF. lia. }
  split; [|split; [exact LS'|]].
  - unfold cenvA. split; [exact OK|]. split; [exact HEAP'|]. split; [exact ST'|]. split; [exact MI'|].
    split; [apply ax_pres_refl|]. split; [exact CR|]. split; [exact CNT|]. split; [exact RS|].
    split. { eapply rw_cells_agree; [exact AGS | exact FR |]. intros a Ha. rewrite cells_size_app in Ha. cbn [cells_size csize Nat.add] in Ha. unfold USTACK_TOP in *. lia. }
    split; [exact FSZ|].
    unfold uw_opt in *. destruct rasO as [ras|]; [|exact I].
    apply (uw_chain_agree m m' ras SPv (bv_unsigned s0w) UW). eapply agree_on_mono; [exact AGS|]. intros a Ha. cbv beta in *. lia.
  - eapply ax_pres_trans; [exact (ax_pres_outer [b] LB SPv (XW PL) m0 m AXP)|].
    unfold ax_pres. eapply agree_on_mono; [exact AGO|]. intros a [_ Ha] Hx.
    destruct Ha as [Ha|[Ha|(b0 & Hb0 & Hr)]].
    + unfold USTACK_TOP, BnHeapA.ACEIL in *. lia.
    + exact (blk_not_static_gen Σ OW (b :: LB) m b a HEAP INB Hx Ha).
    + assert (NE : blk_id b0 <> blk_id b).
      { intros E. pose proof (AH_nodup _ _ _ _ HEAP) as NDA. rewrite map_app in NDA. apply NoDup_app_remove_l in NDA. cbn [map] in NDA.
        inversion NDA as [|? ? NI _]. apply NI. rewrite <- E. apply in_map. exact Hb0. }
      pose proof (AH_disjoint_gen _ _ _ _ b0 b HEAP ltac:(apply in_or_app; right; right; exact Hb0) INB NE) as DJ. lia.
Qed.

Lemma cenv_localA : forall (LB : list block) PL EA lo SPv FB (s0w raw : word) rasO TOTAL Σ0 (ls0 : bstate bptr) OW0 m0 pre pre' used Σ (ls : bstate bptr) m m' OW a b,
  cenvA LB PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m OW -> lib_state ls m OW PL EA ->
  munch [(a, b)]%Z m m' -> wmono bgbsegs m m' -> FB <= a -> b <= SPv ->
  stk bgbsegs m' lo FB -> mem_inv bgbsegs m' ->
  rw_cells bgbsegs m' FB (pre' ++ [C8 s0w; C8 raw]) -> Z.of_nat (cells_size pre') = SPv - FB - 16 ->
  cenvA LB PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre' used Σ ls m' OW /\ lib_state ls m' OW PL EA.
Proof.
  intros LB PL EA lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre pre' used Σ ls m m' OW a b ENV LS MU WM HA HB ST' MI' FR' FSZ'.
  pose proof ENV as (OK & HEAP & ST & MI & AXP & CR & CNT & RS & FR & FSZ & UW).
  pose proof OK as (CEIL & LOFB & FBSP & SPT & _ & _ & _ & _ & FROK & _).
  assert (WOK : Forall (w_ok OW LB ls PL EA SPv []) [(a, b)]) by (constructor; [apply w_stack; cbn [fst snd]; clear - CEIL LOFB HA HB; lia| constructor]).
  assert (HWL : Forall (w_lib ls OW PL lo SPv) [(a, b)]) by (constructor; [left; cbn [fst snd]; clear - LOFB HA HB; lia| constructor]).
  split.
  - eapply cenv_silentA; [exact ENV | exact LS | exact MU | exact WM | exact HWL | exact ST' | exact MI' | exact FR' | exact FSZ'].
  - exact (lib_state_frame Σ LB SPv USTACK_TOP [] ls m m' OW PL EA _ HEAP LS MU WM FROK WOK).
Qed.

Lemma cenv_recastA : forall (LB : list block) PL lo SPv FB (s0w raw : word) rasO TOTAL Σ0 (ls0 : bstate bptr) OW0 m0 pre pre' used Σ (ls : bstate bptr) m OW,
  cenvA LB PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m OW ->
  cells_wf pre' -> cells_bytes pre' = cells_bytes pre -> cells_size pre' = cells_size pre ->
  cenvA LB PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre' used Σ ls m OW.
Proof.
  intros LB PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre pre' used Σ ls m OW (OK & HEAP & ST & MI & AXP & CR & CNT & RS & FR & FSZ & UW) W B S.
  unfold cenvA. repeat (split; [assumption|]). split; [| split; [rewrite S; exact FSZ | exact UW]].
  eapply bk_rw_cells_recast; [exact FR | | |].
  - destruct FR as [[Hwf _] _]. rewrite cells_wf_app in *. split; [exact W | exact (proj2 Hwf)].
  - rewrite !cells_bytes_app, B. reflexivity.
  - rewrite !cells_size_app, S. reflexivity.
Qed.

Lemma cenv_pre_wf : forall (LB : list block) PL lo SPv FB (s0w raw : word) rasO TOTAL Σ0 (ls0 : bstate bptr) OW0 m0 pre used Σ (ls : bstate bptr) m OW,
  cenvA LB PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m OW -> cells_wf pre.
Proof.
  intros LB PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m OW (_ & _ & _ & _ & _ & _ & _ & _ & FR & _).
  destruct FR as [[Hwf _] _]. rewrite cells_wf_app in Hwf. exact (proj1 Hwf).
Qed.

Lemma obj_keepA : forall (b : block) (LB : list block) PL lo SPv FB (s0w raw : word) rasO TOTAL Σ0 (ls0 : bstate bptr) OW0 m0 pre used Σ (ls : bstate bptr) m OW A cs,
  cenvA (b :: LB) PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m OW ->
  rw_cells bgbsegs m0 A cs -> blk_addr b <= A -> A + Z.of_nat (cells_size cs) <= blk_addr b + blk_size b ->
  (forall x, blk_addr b <= x < blk_addr b + blk_size b -> ~ rin_ivs (pl_frames PL) x) ->
  rw_cells bgbsegs m A cs.
Proof.
  intros b LB PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m OW A cs (OK & HEAP & ST & MI & AXP & _) H H1 H2 NF.
  assert (INB : In b (OW ++ b :: LB)) by (apply in_or_app; right; left; reflexivity).
  pose proof (AH_range_gen _ _ _ _ b HEAP INB) as (B0 & _ & Bn & BC & BI).
  eapply rw_cells_agree; [exact AXP | exact H |]. intros a Ha. split.
  - unfold XW. intros HX. apply rin_ivs_In in HX. destruct HX as (iv & Hiv & Hr). apply in_app_or in Hiv as [Hiv|Hiv].
    + revert Hiv Hr. unfold LIBW_bgr, LIBW_A, CONST_ONE, BN_STRUCT_SZ. cbn [In]. intros [E|E]; [subst iv; cbn [fst snd]; lia|].
      revert E. cbn [In]. clear - Ha H1 H2 BI. intros E. repeat (destruct E as [E|E]; [subst iv; cbn [fst snd]; intros; lia|]). destruct E.
    + apply (NF a ltac:(lia)). apply rin_ivs_In. exists iv. split; [exact Hiv | exact Hr].
  - right; right. exists b. split; [left; reflexivity | lia].
Qed.

Lemma implA_tbind_assoc : forall {A B C} (t : btree bptr A) (f : A -> btree bptr B) (g : B -> btree bptr C) Σ
    (Q : C -> rts RT -> machine_state -> Prop) ms,
  implA (tbind t (fun a => tbind (f a) g)) Σ Q ms -> implA (tbind (tbind t f) g) Σ Q ms.
Proof.
  intros A B C t f g Σ Q ms H. unfold implA in *. intros X Φ S. apply (H X Φ).
  apply safe_bind. eapply safe_mono; [exact (safe_bind_inv _ _ _ _ (safe_bind_inv _ _ _ _ S))|].
  intros a X' Ha. cbv beta in Ha. apply safe_bind. exact Ha.
Qed.

Lemma obj_arrA : forall (b : block) (LB : list block) PL lo SPv FB (s0w raw : word) rasO TOTAL Σ0 (ls0 : bstate bptr) OW0 m0 pre used Σ (ls : bstate bptr) m OW ws,
  cenvA (b :: LB) PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m OW ->
  u64arr bgbsegs m0 (blk_addr b) ws -> 8 * Z.of_nat (length ws) = blk_size b ->
  (forall x, blk_addr b <= x < blk_addr b + blk_size b -> ~ rin_ivs (pl_frames PL) x) ->
  u64arr bgbsegs m (blk_addr b) ws.
Proof.
  intros b LB PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m OW ws EV U L NF.
  apply (rw_cells_CB_u64arr m (blk_addr b) ws (8 * length ws)); [reflexivity|].
  eapply (obj_keepA b LB PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m OW); [exact EV | | lia | | exact NF].
  - apply (rw_cells_CB_u64arr m0 (blk_addr b) ws (8 * length ws)); [reflexivity | exact U].
  - cbn [cells_size csize Nat.add]. lia.
Qed.

Lemma obj_acc : forall Σ OW LB m b, AHEAP Σ OW LB m -> In b LB -> acc bgbsegs m (blk_addr b) (blk_size b).
Proof. intros Σ OW LB m b HEAP Hb. exact (proj2 (AH_acc _ _ _ _ b HEAP ltac:(apply in_or_app; right; exact Hb))). Qed.

Section Calls.
  Variables (LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs) (lo SPv FB : Z) (s0w raw : word) (rasO : option (list Z)) (TOTAL : Z).
  Variables (Σ0 : rts RT) (ls0 : bstate bptr) (OW0 : list block) (m0 : mem).
  Local Notation CENV := (cenvA LB PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0).
  Hypothesis LOFB16 : lo <= FB - 16.

  Lemma zero_callA : forall (POST : machine_state -> Prop) pre used Σ (ls : bstate bptr) (m : mem) (OW : list block) (r : bnref) (ar : Z)
      (ra gp t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    CENV pre used Σ ls m OW -> lib_state ls m OW PL EA -> ref_at ls OW PL r ar -> wref PL r ->
    (forall m' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14,
        let ls' := setbn r (bn_zero_pure (getbn r ls)) ls in
        CENV pre used Σ ls' m' OW -> lib_state ls' m' OW PL EA ->
        evt bgbsegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) y0 y1 y2 x8 x9 y3 y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                           F (ret_pc ra) fc None m' (seg_rom bgbsegs))) ->
    evt bgbsegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) t0 t1 t2 x8 x9 (Z_to_bv 64 ar) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 BN_ZERO_EX) fc None m (seg_rom bgbsegs)).
  Proof using LOFB16.
    intros until fc. intros ENV LS HA WR K.
    pose proof (proj1 WR : not_one r) as NRO.
    destruct (open_for_call LB PL EA lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 LOFB16 _ _ _ _ _ _ _ _ ENV LS HA NRO) as (D0 & _ & _ & ESP & ST & MI & SEP & SHBC & ACC & AL & SLO & OFR & A0).
    pose proof ENV as (OK & HEAP & _ & _ & AXP & CR & CNT & RS & FR & FSZ & UW). pose proof OK as (CEIL & LOFB & FBSP & SPT & _ & _ & _ & _ & FROK & _ & NOFR).
    pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
    destruct (lib_state_open [] ls m OW PL EA r ar LS ND HA ltac:(intros []) NRO) as ((D & BN & ARR) & (OK1 & OK2 & OK3 & OK4) & LSH).
    set (b := getbn r ls) in *.
    destruct (bn_arr_facts_w ls OW PL EA SPv USTACK_TOP Σ LB m r D HEAP PARTS FROK HV WR ARR) as (U & _ & DD0 & DC & DI & SEPd). fold b in U, DC, DI, SEPd.
    pose proof (SEPd r ar HA) as SEPr. clear SEPd.
    unfold BG_DMAX in OK3.
    eapply evt_cut.
    { eapply BN_zero_ex_specA with (lo := lo) (A := ar) (D := D) (b := b);
        [exact BN | rewrite ESP; exact ST | rewrite ESP; exact LOFB16 | exact MI | rewrite ESP; left; exact SEP
        | exact SHBC | exact ACC | exact AL | exact SLO | exact OFR | reflexivity | exact A0]. }
    intros ms' PO. unfold bn_small_postA in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & E & MUc & WMc & MIc & STc & RES).
    subst ms'. rewrite ESP in *.
    assert (U' : u64arr bgbsegs m' D (wlimbs (bn_buf b))).
    { eapply u64arr_transport; [exact U | exact MUc | exact WMc |]. cbn [disjoint_from]. rewrite wlimbs_len. fold (bn_dmax b).
      split; [left; unfold BnHeapA.ACEIL in *; clear - DC CEIL LOFB16; lia|]. split; [clear - SEPr; lia| exact I]. }
    eapply (rw_cells_transport bgbsegs _ m m') in FR; [| exact MUc | exact WMc | cbn [disjoint_from]; split; [right; clear; lia|]; split; [right; clear - SEP; lia| exact I]].
    assert (WOK : Forall (w_ok OW LB ls PL EA SPv [r]) [(FB - 16, FB); (ar, ar + 24)]).
    { constructor; [apply w_stack; cbn [fst snd]; clear - CEIL LOFB FBSP LOFB16; lia|].
      constructor; [eapply (w_struct OW LB ls PL EA SPv false [r] _ r ar); [left; reflexivity| exact HA| exact NRO| cbn; clear; lia| cbn; clear; lia]| constructor]. }
    assert (HWL : Forall (w_lib ls OW PL lo SPv) [(FB - 16, FB); (ar, ar + 24)]).
    { constructor; [left; cbn [fst snd]; clear - LOFB FBSP LOFB16; lia|].
      constructor; [w_lib_ref HA NRO| constructor]. }
    assert (LS' : lib_state (setbn r (bn_zero_pure b) ls) m' OW PL EA).
    { unfold lib_state. eapply (lib_state_close [] ls m' OW PL EA r ar); [| exact ND | exact HA | exact NRO | | |].
      - exact (lib_state_frame Σ LB SPv USTACK_TOP [r] ls m m' OW PL EA _ HEAP LSH MUc WMc FROK WOK).
      - exists D. split; [exact RES|].
        assert (ARR' : bn_arr m' OW (pl_of PL r) D b) by (eapply bn_arr_of_u64arr; [exact ARR| exact U']).
        unfold bn_arr in ARR' |- *. unfold bn_zero_pure, bn_dmax in *. cbn [bn_d bn_buf]. exact ARR'.
      - unfold bg_ok, bn_zero_pure, bn_dmax, BG_DMAX in *. cbn [bn_buf bn_top bn_flags].
        split; [exact OK1|]. split; [clear; lia|]. split; [exact OK3| exact OK4].
      - apply ids_ok_setbn_same; [exact (proj1 (proj2 (proj2 PARTS))) | exact HV | reflexivity]. }
    eapply K; [| exact LS'].
    apply cenv_setbnA; [| exact HV | reflexivity].
    eapply cenv_silentA; [exact ENV | exact LS | exact MUc | exact WMc | exact HWL | exact STc | exact MIc | exact FR | exact FSZ].
  Qed.
End Calls.

End WithRT.
