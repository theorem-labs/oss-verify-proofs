(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun SjModel AtpModel Target Prog AtpImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_num_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import F_memchr F_memcmp F_strlen F_memcpy F_memmove_t2 Atp_defs Atp_str Atp_strr.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Definition LIT_T : Z := 0x137b1.
Definition LIT_S : Z := 0x10c43.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma lit_tilde_bytes : forall m, mem_inv usegs m ->
  bytes_at usegs m LIT_T (Z_to_bv 8 126 :: Z_to_bv 8 0 :: [Z_to_bv 8 73; Z_to_bv 8 78; Z_to_bv 8 83; Z_to_bv 8 85; Z_to_bv 8 70]).
Proof.
  intros m MI.
  assert (R : ro_cells usegs m LIT_T [CB 7 [Z_to_bv 8 126; Z_to_bv 8 0; Z_to_bv 8 73; Z_to_bv 8 78; Z_to_bv 8 83; Z_to_bv 8 85; Z_to_bv 8 70]]).
  { apply (ro_cells_image usegs m); [exact MI| vm_compute; reflexivity| unfold LIT_T; lia| unfold LIT_T; cbn; lia]. }
  destruct R as [_ B]. cbn [cells_bytes cbytes app] in B. exact B.
Qed.
Lemma lit_slash_bytes : forall m, mem_inv usegs m ->
  bytes_at usegs m LIT_S (Z_to_bv 8 47 :: Z_to_bv 8 0 :: [Z_to_bv 8 32; Z_to_bv 8 58; Z_to_bv 8 32]).
Proof.
  intros m MI.
  assert (R : ro_cells usegs m LIT_S [CB 5 [Z_to_bv 8 47; Z_to_bv 8 0; Z_to_bv 8 32; Z_to_bv 8 58; Z_to_bv 8 32]]).
  { apply (ro_cells_image usegs m); [exact MI| vm_compute; reflexivity| unfold LIT_S; lia| unfold LIT_S; cbn; lia]. }
  destruct R as [_ B]. cbn [cells_bytes cbytes app] in B. exact B.
Qed.

Definition unesc_W (spv A cap : Z) : list (Z * Z) := [(spv - 80, spv); (spv + 32, spv + 56); (A, A + cap)].

Lemma obj_unesc_loop : forall (K : machine_state -> Prop) (m0 : mem) (F : bvmap 5 word) (fc : bv 32) (spv lo : Z) (lg : bool) (A cap : Z)
    (x3 x8 x9 x18 x27 : word),
  alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= spv - 80 -> spv + 56 < 2^63 -> 0 < A -> A + cap < 2^63 ->
  (lg = true -> A + cap <= lo /\ (A + cap <= 0x10000 \/ 0x111000 <= A)) -> (lg = false -> A = spv + 33) ->

  (forall (m : mem) (sz : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x28 x29 x30 x31 : word),
     lstr m (spv + 32) lg A cap sz -> (lg = true -> x10 = Z_to_bv 64 A) ->
     mem_inv usegs m -> stk usegs m lo spv -> munch (unesc_W spv A cap) m0 m -> wmono usegs m0 m ->
     evt usegs K (MS (mkR x1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                        x18 x19 (Z_to_bv 64 (spv + 33)) x21 (Z_to_bv 64 49) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 LIT_T) (Z_to_bv 64 LIT_S) (Z_to_bv 64 48) x27 x28 x29 x30 x31)
                   F (Z_to_bv 64 0x3f2b0) fc None m (seg_rom usegs))) ->

  (forall (m : mem) (sz : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31 : word),
     lstr m (spv + 32) lg A cap sz ->
     mem_inv usegs m -> stk usegs m lo spv -> munch (unesc_W spv A cap) m0 m -> wmono usegs m0 m ->
     evt usegs K (MS (mkR x1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                        x18 (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 (spv + 33)) x21 (Z_to_bv 64 49) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 LIT_T) (Z_to_bv 64 LIT_S) (Z_to_bv 64 48) x27 x28 x29 x30 x31)
                   F (Z_to_bv 64 0x3f298) fc None m (seg_rom usegs))) ->
  forall (n : nat) (m : mem) (sz esc : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31 : word),
    lstr m (spv + 32) lg A cap sz -> 0 <= esc < sz -> sz - esc <= Z.of_nat n ->
    mem_inv usegs m -> stk usegs m lo spv -> munch (unesc_W spv A cap) m0 m -> wmono usegs m0 m ->
    evt usegs K (MS (mkR x1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                       x18 (Z_to_bv 64 esc) (Z_to_bv 64 (spv + 33)) x21 (Z_to_bv 64 49) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 LIT_T) (Z_to_bv 64 LIT_S) (Z_to_bv 64 48) x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x3f22c) fc None m (seg_rom usegs)).
Proof.
  intros K m0 F fc spv lo lg A cap x3 x8 x9 x18 x27 CEIL GLO LO S63 A0 AC HLG HSH XBAD XDONE.
  pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
  unfold GLOBALS_TOP in GLO.
  induction n as [|n IH]; intros m sz esc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31 LS ESC FUEL MI ST MU WM; [lia|].
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof LS as (SZ0 & SZC & CAP & _ & _ & (bs & BS & LBS & NUL) & REP).

  set (cb := nth (Z.to_nat (esc + 1)) bs (Z_to_bv 8 1)). set (c := bv_unsigned cb).
  assert (CR : 0 <= c < 256) by (subst c; pose proof (bv_unsigned_in_range 8 cb) as X; unfold bv_modulus in X; cbn in X; lia).
  assert (CNUL : esc + 1 = sz -> c = 0).
  { intros E. subst c cb. replace (Z.to_nat (esc + 1)) with (Z.to_nat sz) by lia. rewrite NUL. reflexivity. }
  assert (RDC : ov_read_bytes usegs m (wa (A + (esc + 1))) 1 = Some [cb]).
  { apply (u8arr_read usegs m A bs (esc + 1) cb _ BS); [apply nth_error_nth'; lia| lia| reflexivity]. }
  assert (EZ : zxb cb = Z_to_bv 64 c) by reflexivity.

  assert (LOADS : forall (K' : machine_state -> Prop),
    (forall (xa0 xa2 : word), (lg = true -> xa0 = Z_to_bv 64 A) ->
       evt usegs K' (MS (mkR x1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) x5 x6 x7 x8 x9 xa0 (Z_to_bv 64 c) xa2 x13 x14 x15 x16 x17
                           x18 (Z_to_bv 64 esc) (Z_to_bv 64 (spv + 33)) (Z_to_bv 64 (esc + 1)) (Z_to_bv 64 49) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 LIT_T) (Z_to_bv 64 LIT_S) (Z_to_bv 64 48) x27 x28 x29 x30 x31)
                      F (Z_to_bv 64 0x3f25c) fc None m (seg_rom usegs))) ->
    evt usegs K' (MS (mkR x1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                        x18 (Z_to_bv 64 esc) (Z_to_bv 64 (spv + 33)) x21 (Z_to_bv 64 49) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 LIT_T) (Z_to_bv 64 LIT_S) (Z_to_bv 64 48) x27 x28 x29 x30 x31)
                   F (Z_to_bv 64 0x3f22c) fc None m (seg_rom usegs))).
  { intros K' HK'. pose proof (munch_refl ([] : list (Z * Z)) m) as MU0. pose proof (wmono_refl usegs m) as WM0.
    destruct lg.
    -
      destruct REP as [HDR EV]. destruct (HLG eq_refl) as [ALO ABLK].
      pose proof (rw_cells_C8_read1 _ _ _ _ HDR) as RD0.
      astep. rewrite zx8_lit by lia. step. astep. rewrite long_byte0 by lia. step. step. if_false. step.
      step. if_lia. astep. astep. step. if_lia. step. if_lia. step. rewrite EZ.
      eapply evt_eq; [| eapply HK'; reflexivity]. atp_st_eq.
    -
      destruct REP as (HDR & EA & ECAP).
      pose proof (bytes_at_read usegs m A bs 15 8 (proj1 BS) ltac:(lia) ltac:(lia)) as RD8.
      remember (firstn 8 (skipn (Z.to_nat 15) bs)) as l8 eqn:El8 in RD8.
      replace (A + 15) with (spv + 48) in RD8 by lia.
      astep. step. astep. rewrite short_byte0. step. step. if_true.
      step. if_lia. astep. astep. step. if_lia. step. if_lia. step. rewrite EZ.
      eapply evt_eq; [| eapply HK'; intros X; discriminate X]. atp_st_eq. }
  apply LOADS. clear LOADS. intros xa0 xa2 HA0.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU0. pose proof (wmono_refl usegs m) as WM0.

  assert (CALLS : forall (lit c3 : Z) (slack : list byte) (ya1 ya2 : word),
    bytes_at usegs m lit (Z_to_bv 8 c3 :: Z_to_bv 8 0 :: slack) -> (- (lit + 2)) mod 8 <= Z.of_nat (length slack) -> Z.of_nat (length slack) <= 8 ->
    0 < c3 < 256 -> (lit = LIT_T \/ lit = LIT_S) -> esc + 2 <= sz ->
    evt usegs K (MS (mkR x1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) x5 x6 x7 x8 x9 xa0 ya1 ya2 (Z_to_bv 64 lit) x14 x15 x16 x17
                       x18 (Z_to_bv 64 esc) (Z_to_bv 64 (spv + 33)) (Z_to_bv 64 (esc + 1)) (Z_to_bv 64 49) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 LIT_T) (Z_to_bv 64 LIT_S) (Z_to_bv 64 48) x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x3f270) fc None m (seg_rom usegs))).
  { intros lit c3 slack ya1 ya2 LIT CPAD SL8 C3 HL E2.
    assert (LITR : 0x10c43 <= lit <= 0x137b1) by (unfold LIT_T, LIT_S in HL; lia).

    astep. astep. step. step.
    eapply evt_cut.
    { eapply str_replace_spec with (F := F) (fc := fc) (m := m) (q := spv) (lo := lo) (S := spv + 32) (lg := lg) (A := A) (cap := cap) (sz := sz) (pos := esc) (lit := lit) (c := c3) (slack := slack);
        [exact LS| lia| exact E2| exact LIT| exact CPAD| exact SL8| exact C3| lia| lia| | lia| lia| intros Hl; exact (proj1 (HLG Hl))| exact ST| lia| exact MI].
      destruct lg; [destruct (HLG eq_refl) as [_ AB]; lia| rewrite (HSH eq_refl); lia]. }
    cbv beta. intros ms' PO. unfold replace_post in PO.
    destruct PO as (z0 & z1 & z2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3 & z4 & z5 & z6 & m2 & -> & MU2 & WM2 & MI2 & ST2 & LS2).
    replace (ret_pc (Z_to_bv 64 0x3f280)) with (Z_to_bv 64 0x3f280) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (MU02 : munch (unesc_W spv A cap) m0 m2).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp, unesc_W. cbn [outside]. intros x Hx. lia. }
    assert (WM02 : wmono usegs m0 m2) by (eapply wmono_trans; [exact WM| exact WM2]).
    clear MU0 WM0. pose proof (munch_refl ([] : list (Z * Z)) m2) as MU0. pose proof (wmono_refl usegs m2) as WM0.

    astep. astep. step. step.
    eapply evt_cut.
    { eapply str_find_spec with (F := F) (fc := fc) (m := m2) (q := spv) (lo := lo) (S := spv + 32) (lg := lg) (A := A) (cap := cap) (sz := sz - 1) (pos := esc + 1);
        [exact LS2| lia| lia| lia| intros Hl; exact (proj1 (HLG Hl))| exact ST2| lia| exact MI2]. }
    cbv beta. intros ms' PO. unfold find_post in PO.
    destruct PO as (w0 & w1 & w2 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & m3 & r & -> & MU3 & WM3 & MI3 & ST3 & LS3 & HR).
    replace (ret_pc (Z_to_bv 64 0x3f290)) with (Z_to_bv 64 0x3f290) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (MU03 : munch (unesc_W spv A cap) m0 m3).
    { eapply munch_trans; [exact MU02|]. eapply munch_weaken; [| exact MU3]. unfold sub_fp, unesc_W. cbn [outside]. intros x Hx. lia. }
    assert (WM03 : wmono usegs m0 m3) by (eapply wmono_trans; [exact WM02| exact WM3]).
    clear MU0 WM0. pose proof (munch_refl ([] : list (Z * Z)) m3) as MU0. pose proof (wmono_refl usegs m3) as WM0.

    step. step. if_cases KR; zify_cond KR; rewrite ?land64_mod in KR.
    -   destruct HR as [->|HR]; [exfalso; clear - KR; lia|].
      eapply evt_eq; [| eapply (IH m3 (sz - 1) r)]; [atp_st_eq| exact LS3| lia| lia| exact MI3| exact ST3| exact MU03| exact WM03].
    -   destruct HR as [->|HR]; [| exfalso; clear - KR HR ESC SZC CAP; lia].
      eapply evt_eq; [| eapply (XDONE m3 (sz - 1))]; [atp_st_eq| exact LS3| exact MI3| exact ST3| exact MU03| exact WM03]. }

  step. if_cases K1; zify_cond K1.
  -
    step. eapply evt_eq; [| eapply (CALLS LIT_S 47 [Z_to_bv 8 32; Z_to_bv 8 58; Z_to_bv 8 32])];
      [atp_st_eq| apply lit_slash_bytes; exact MI| unfold LIT_S; cbn; lia| cbn; lia| lia| right; reflexivity| ].
    destruct (Z.eq_dec (esc + 1) sz) as [E|NE]; [exfalso; rewrite (CNUL E) in K1; lia| lia].
  - step. step. if_cases K0; zify_cond K0.
    +
      eapply evt_eq; [| eapply (XBAD m sz)]; [atp_st_eq| exact LS| exact HA0| exact MI| exact ST| exact MU| exact WM].
    + step. eapply evt_eq; [| eapply (CALLS LIT_T 126 [Z_to_bv 8 73; Z_to_bv 8 78; Z_to_bv 8 83; Z_to_bv 8 85; Z_to_bv 8 70])];
        [atp_st_eq| apply lit_tilde_bytes; exact MI| unfold LIT_T; cbn; lia| cbn; lia| lia| left; reflexivity| ].
      destruct (Z.eq_dec (esc + 1) sz) as [E|NE]; [exfalso; rewrite (CNUL E) in K0; lia| lia].
Qed.

End WithCeiling0.
