(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Instr Mem State Step Plan ValProofs MemProofs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require GTwinSub.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require HeapCtr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import GlueA Actr CallA.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan ValP MemP CtrLib CtrFX ActrA.
Open Scope Z_scope.
Unset Lia Cache.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require KnownT.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require KnownA.
Unset Nia Cache. Unset Nra Cache.

Section CallV.
Variable segs : list Segment.
Variable OPS : optable.

Definition shz (a : Z) : Z := a / 8 + 0x7fff8000.

Definition view_parent (fs : list fact) (R : IMap.t region) (n sh : int) : Prop :=
  (exists kb o1, find_ub_g fs n = Some (kb, o1) /\ twin_of fs kb = Some sh)
  \/ (exists rsh, IMap.find sh R = Some rsh /\ hi_names rsh n = true).
Definition view_sem (E : env) (st : sstate) (wl : list (int * sv * w64)) (ks k : int) (r : region) : Prop :=
  let lo := bv_unsigned (ev E k) + loZ r in
  let hi := bv_unsigned (ev E k) + hiZ E r in
  ((exists hs, zero_view r = Some hs) /\
   exists blo bhi, (forall a, lo <= a < hi -> exists a', blo <= a' < bhi /\ a = shz a') /\ bhi <= 2 ^ 47 /\
      ((exists wlo, stack_wlo st = Some wlo /\ blo = bv_unsigned (den E (VP STACK_ID wlo)))
       \/ (exists rs, IMap.find ks (s_regs st) = Some rs /\ blo = bv_unsigned (ev E ks) + loZ rs)
       \/ bv_unsigned (den E (getr st X2)) <= blo))
  \/ (exists hs n sh len, zero_view r = Some hs /\ block_of_twin (s_facts st) k = Some n /\ view_parent (s_facts st) (s_regs st) n sh
        /\ CtrA.win_lookup wl sh = Some (len, K_TWIN)
        /\ bv_unsigned (ev E sh) <= lo /\ hi <= bv_unsigned (ev E sh) + bv_unsigned (den E len))
  \/ (view_I (s_facts st) k r = true /\ exists v, In v IMGSH /\ fst v <= lo /\ hi <= snd v)

  \/ (exists sh kb n len, CtrA.win_lookup wl sh = Some (len, K_TWIN) /\ block_of_twin (s_facts st) sh = Some kb
        /\ CtrA.win_lookup wl kb = Some (n, CtrLib.K_BLOCK) /\ size_tail_ok (s_facts st) n = true
        /\ tail_named (tail_rhs sh n) k (s_facts st) = true /\ rg_w r = false
        /\ bv_unsigned (ev E sh) <= lo /\ hi <= bv_unsigned (ev E sh) + bv_unsigned (den E len)).

Lemma zero_view_hi : forall E r hs, zero_view r = Some hs -> hiZ E r = hs.
Proof.
  intros E r hs H. unfold zero_view in H. unfold hiZ. destruct (rg_hi r) as [w| | | | | | | | | |]; try discriminate.
  destruct (rg_bg r); try discriminate. destruct (rg_cells r); try discriminate.
  destruct (negb (rg_w r) && negb (wt w)); [| discriminate]. injection H as <-. cbn [den]. apply wbv_unsigned.
Qed.
Lemma lit_hi_sound : forall E r h, lit_hi r = Some h -> hiZ E r = h.
Proof.
  intros E r h H. unfold lit_hi in H. unfold hiZ. destruct (rg_hi r) as [w| | | | | | | | | |]; try discriminate.
  destruct (wt w); [discriminate|]. injection H as <-. cbn [den]. apply wbv_unsigned.
Qed.
Lemma ro_lit_hi_sound : forall E r h, ro_lit_hi r = Some h -> hiZ E r = h.
Proof.
  intros E r h H. unfold ro_lit_hi in H. unfold hiZ. destruct (rg_hi r) as [w| | | | | | | | | |]; try discriminate.
  destruct (negb (rg_w r) && negb (wt w)); [| discriminate]. injection H as <-. cbn [den]. apply wbv_unsigned.
Qed.

Lemma twin_of_sound : forall E fs k sh, facts_hold E fs -> twin_of fs k = Some sh ->
  bv_unsigned (ev E sh) = (bv_unsigned (ev E k) / 8 + 0x7fff8000) mod 2 ^ 64.
Proof.
  intros E fs k sh HF. unfold twin_of. induction fs as [|f fs IH]; intros H; [discriminate|].
  inversion HF as [|f' l Hf HF']; subst.
  assert (STEP : (fix go (l : list fact) : option int :=
                    match l with
                    | FEq (VP sh0 o) (VAlu ALU_ADD (VAlu ALU_SRL (VP k' o') (VL c3)) (VL sb)) :: l' =>
                        if PrimInt63.eqb k k' && weqb o wzero && weqb o' wzero && weqb c3 (wlit 3%uint63) && weqb sb SBw then Some sh0 else go l'
                    | _ :: l' => go l'
                    | [] => None
                    end) fs = Some sh -> bv_unsigned (ev E sh) = (bv_unsigned (ev E k) / 8 + 0x7fff8000) mod 2 ^ 64) by exact (IH HF').
  destruct f as [| | | |x y| | |]; try (apply STEP; exact H).
  destruct x as [|sh0 z| | | | | | | | |]; try (apply STEP; exact H).
  destruct y as [| |op y1 y2| | | | | | | |]; try (apply STEP; exact H). destruct op; try (apply STEP; exact H).
  destruct y1 as [| |op1 u1 u2| | | | | | | |]; try (apply STEP; exact H). destruct op1; try (apply STEP; exact H).
  destruct u1 as [|k' z'| | | | | | | | |]; try (apply STEP; exact H). destruct u2 as [c| | | | | | | | | |]; try (apply STEP; exact H).
  destruct y2 as [s'| | | | | | | | | |]; try (apply STEP; exact H).
  destruct (PrimInt63.eqb k k' && weqb z wzero && weqb z' wzero && weqb c (wlit 3%uint63) && weqb s' SBw) eqn:C; [|apply STEP; exact H].
  injection H as ->. apply andb_prop in C as [C S']. apply andb_prop in C as [C C3]. apply andb_prop in C as [C Z']. apply andb_prop in C as [K' Z0].
  apply Uint63.eqb_correct in K'. subst k'.
  apply (block_of_twin_sound E [FEq (VP sh z) (VAlu ALU_ADD (VAlu ALU_SRL (VP k z') (VL c)) (VL s'))] sh k).
  - constructor; [exact Hf| constructor].
  - unfold block_of_twin. rewrite Uint63.eqb_refl, Z0, Z', C3, S'. reflexivity.
Qed.

Lemma find_pin_sound : forall E fs s a, facts_hold E fs -> find_pin fs s = Some a -> bv_unsigned (ev E s) = w2Z a.
Proof.
  intros E fs s a HF. unfold find_pin. induction fs as [|f fs IH]; intros H; [discriminate|].
  inversion HF as [|f' l Hf HF']; subst.
  assert (STEP : (fix go (l : list fact) : option w64 :=
                    match l with
                    | FEq (VP s' z) (VL a0) :: l' => if PrimInt63.eqb s s' && weqb z wzero then Some a0 else go l'
                    | _ :: l' => go l'
                    | [] => None
                    end) fs = Some a -> bv_unsigned (ev E s) = w2Z a) by exact (IH HF').
  destruct f as [| | | |x y| | |]; try (apply STEP; exact H).
  destruct x as [|s' z| | | | | | | | |]; try (apply STEP; exact H).
  destruct y as [a0| | | | | | | | | |]; try (apply STEP; exact H).
  destruct (PrimInt63.eqb s s' && weqb z wzero) eqn:C; [|apply STEP; exact H].
  injection H as ->. apply andb_prop in C as [S' Z0]. apply Uint63.eqb_correct in S'. apply weqb_eq in Z0. subst s' z.
  cbn [fact_holds] in Hf. rewrite HeapCtr.den_VPz in Hf. rewrite Hf. cbn [den]. apply wbv_unsigned.
Qed.

Lemma stack_wlo_inv : forall st wlo, stack_wlo st = Some wlo -> nowrap_kb (s_facts st) STACK_ID wlo = true.
Proof.
  intros st wlo H. unfold stack_wlo in H. destruct (find_op HEAP_ID (s_ops st)) as [hargs|]; [|discriminate].
  destruct (heap_nwin hargs) as [n|]; [|discriminate]. destruct hargs as [|h1 [|h2 [|h3 rest]]]; try discriminate.
  destruct (stack_window_key n rest) as [w|]; [|discriminate]. destruct (nowrap_kb (s_facts st) STACK_ID w) eqn:NW; [|discriminate].
  injection H as <-. exact NW.
Qed.

Lemma view_anchor : forall E fs s n, facts_hold E fs -> block_of_twin fs s = Some n ->
  bv_unsigned (ev E s) = bv_unsigned (ev E n) / 8 + 0x7fff8000.
Proof.
  intros E fs s n HF BT. rewrite (block_of_twin_sound E fs s n HF BT).
  pose proof (bv_unsigned_in_range 64 (ev E n)) as R. unfold bv_modulus in R. apply Z.mod_small. Z.div_mod_to_equations. lia.
Qed.

Lemma ub_cand_holds : forall E fs n f k o, facts_hold E fs -> fact_holds E f -> ub_cand fs n f = Some (k, o) ->
  wt o = false /\ bv_unsigned (ev E n) <= bv_unsigned (ev E k) + w2Z o.
Proof.
  intros E fs n f k o HF Hf H. unfold ub_cand in H. destruct f as [| | |x y|x y| | |]; try discriminate H.
  destruct x as [|n' oU| | | | | | | | |]; try discriminate H. destruct y as [|k' cU| | | | | | | | |]; try discriminate H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:C; [|discriminate H] end. injection H as <- <-.
  apply andb_prop in C as [C NWK]. apply andb_prop in C as [C NWN]. apply andb_prop in C as [C LE]. apply andb_prop in C as [C TC]. apply andb_prop in C as [EN TU].
  apply Uint63.eqb_correct in EN. subst n'. apply negb_true_iff in TU. apply negb_true_iff in TC. apply Uint63.leb_spec in LE.
  destruct (nowrap_kb_sound E _ HF n oU NWN) as [_ DN]. destruct (nowrap_kb_sound E _ HF k' cU NWK) as [_ DK].
  cbn [fact_holds] in Hf. rewrite DN, DK in Hf.
  assert (ZU : w2Zs oU = w2Z oU) by (rewrite w2Zs_eq; rewrite TU; lia).
  assert (ZC : w2Zs cU = w2Z cU) by (rewrite w2Zs_eq; rewrite TC; lia).
  assert (WU : w2Z oU = to_Z (wl oU)) by (unfold w2Z; rewrite TU; lia).
  assert (WC : w2Z cU = to_Z (wl cU)) by (unfold w2Z; rewrite TC; lia).
  pose proof (w2Z_range oU) as RU. pose proof (w2Z_range cU) as RC. unfold two64 in RU, RC.
  assert (SUBV : w2Z (wsub cU oU) = w2Z cU - w2Z oU) by (rewrite wsub_ok; unfold two64; apply Z.mod_small; lia).
  split.
  - rewrite w2Z_wt. apply Z.leb_gt. rewrite SUBV. pose proof (to_Z_bounded (wl cU)) as B. rewrite wB_two63 in B. unfold two63 in *. lia.
  - rewrite SUBV. lia.
Qed.
Lemma find_ub_go_holds : forall E fsA n fs acc k o, facts_hold E fsA -> Forall (fact_holds E) fs ->
  (forall k0 o0, acc = Some (k0, o0) -> wt o0 = false /\ bv_unsigned (ev E n) <= bv_unsigned (ev E k0) + w2Z o0) ->
  find_ub_go fsA n fs acc = Some (k, o) -> wt o = false /\ bv_unsigned (ev E n) <= bv_unsigned (ev E k) + w2Z o.
Proof.
  intros E fsA n fs. induction fs as [|f fs IH]; intros acc k o HA HF ACC H; cbn [find_ub_go] in H; [exact (ACC k o H)|].
  inversion HF as [|f' l Hf HF']; subst. refine (IH _ k o HA HF' _ H).
  intros k0 o0 E0. destruct (ub_cand fsA n f) as [[k1 o1]|] eqn:UC; [| exact (ACC k0 o0 E0)].
  pose proof (ub_cand_holds E fsA n f k1 o1 HA Hf UC) as G.
  destruct acc as [[k2 o2]|]; [| injection E0 as <- <-; exact G].
  destruct (PrimInt63.eqb k1 k2 && wltu o1 o2); [injection E0 as <- <-; exact G| exact (ACC k0 o0 E0)].
Qed.
Lemma find_ub_g_holds : forall E fs n k o, facts_hold E fs -> find_ub_g fs n = Some (k, o) -> wt o = false ->
  bv_unsigned (ev E n) <= bv_unsigned (ev E k) + w2Z o.
Proof.
  intros E fs n k o HF H WT. unfold find_ub_g in H. destruct (GTwinSub.GTwinSub.find_ub fs n) as [[k' o']|] eqn:UB.
  - injection H as <- <-. pose proof (GTwinSub.GTwinSub.find_ub_holds E fs n k' o' HF UB) as U. rewrite HeapCtr.den_VPz in U.
    cbn [den] in U. rewrite bv_add_unsigned, wbv_unsigned in U. unfold bv_wrap, bv_modulus in U.
    pose proof (bv_unsigned_in_range 64 (ev E k')) as RK. unfold bv_modulus in RK. pose proof (w2Z_range o') as RO. unfold two64 in RO.
    clear - U RK RO. Z.div_mod_to_equations. lia.
  - exact (proj2 (find_ub_go_holds E fs n fs None k o HF HF ltac:(intros ? ? X; discriminate X) H)).
Qed.

Lemma twin_arm_ev_sound : forall E fs ks kb (r : region) o2 o1 lw, facts_hold E fs ->
  PrimInt63.leb 3%uint63 (find_align fs kb) = true -> KnownT.KnownT.known_ltu_t fs (VL wzero) (rg_hi r) = true ->
  GTwinSub.GTwinSub.find_lb fs ks kb = Some o2 -> find_ub_g fs ks = Some (kb, o1) -> wt o2 = false -> wt o1 = false ->
  nowrap_kb fs kb o2 = true -> to_Z (wl o1) + 8 <= 8 * to_Z (wl lw) ->
  bv_unsigned (ev E kb) mod 8 = 0 /\ 0 < hiZ E r
  /\ bv_unsigned (ev E kb) <= bv_unsigned (ev E ks) /\ bv_unsigned (ev E ks) + 8 <= bv_unsigned (ev E kb) + 8 * to_Z (wl lw).
Proof.
  intros E fs ks kb r o2 o1 lw HF AL POS LB UB WT2 WT1 NW LE8.
  split; [exact (GTwinSub.GTwinSub.mod8_of_align E _ kb HF AL)|].
  split. { pose proof (KnownA.KnownA.known_ltu_sound E _ _ _ HF POS) as X. unfold hiZ. cbn [den] in X. rewrite wbv_unsigned, w2Z_wzero in X. exact X. }
  pose proof (GTwinSub.GTwinSub.find_lb_holds E _ ks kb o2 HF LB) as L. rewrite HeapCtr.den_VPz in L.
  destruct (nowrap_kb_sound E _ HF kb o2 NW) as [_ D2]. rewrite D2 in L.
  assert (Z2 : w2Zs o2 = w2Z o2) by (rewrite w2Zs_eq; rewrite WT2; lia). rewrite Z2 in L. pose proof (w2Z_range o2) as RO2.
  pose proof (find_ub_g_holds E fs ks kb o1 HF UB WT1) as U.
  assert (W1 : w2Z o1 = to_Z (wl o1)) by (unfold w2Z; rewrite WT1; lia).
  split; lia.
Qed.

Lemma twin_ev_cases : forall E fs R wl0 cv sh len kx, facts_hold E fs -> twin_arm_evx fs R wl0 cv sh len kx = true ->
  exists kb, block_of_twin fs sh = Some kb /\ bv_unsigned (den E len) <= 8064 /\ PrimInt63.leb 3%uint63 (find_align fs kb) = true
    /\ (In kb cv
        \/ exists ks lens kd r, In (ks, lens, kd) wl0 /\ ks <> kx /\ kd <> CtrLib.K_BLOCK /\ weqb kd K_TWIN = false
             /\ IMap.find ks R = Some r /\ rg_w r = true /\ rg_lo r = 0%uint63
             /\ 0 < hiZ E r /\ bv_unsigned (ev E kb) <= bv_unsigned (ev E ks)
             /\ bv_unsigned (ev E ks) + 8 <= bv_unsigned (ev E kb) + 8 * bv_unsigned (den E len)).
Proof.
  intros E fs R wl0 cv sh len kx HF H. unfold twin_arm_evx in H. apply orb_prop in H as [H|H].
  -
    destruct (CallA.twin_arm_ev_inv _ _ _ _ _ _ _ H) as (lw & kb & -> & BT & WTL & LW & AL & EVD). exists kb.
    assert (DL : bv_unsigned (den E (VL lw)) = to_Z (wl lw)) by (cbn [den]; rewrite wbv_unsigned; unfold w2Z; rewrite WTL; reflexivity).
    split; [exact BT|]. split; [rewrite DL; exact LW|]. split; [exact AL|].
    destruct EVD as [CV|(ks & lens & kd & r & o2 & o1 & Hin & NX & NKB & NKT & Fr & RW & L0 & POS & LB & UB & WT2 & WT1 & NW & LE8)]; [left; exact CV| right].
    destruct (twin_arm_ev_sound E _ ks kb r o2 o1 lw HF AL POS LB UB WT2 WT1 NW LE8) as (_ & HPOS & XLO & XHI).
    exists ks, lens, kd, r. rewrite DL. repeat (split; [assumption|]). exact XHI.
  -
    unfold twin_arm_evs in H. destruct (tie_of fs len) as [xs|] eqn:TIE; [|discriminate H]. destruct (block_of_twin fs sh) as [kb|] eqn:BT; [|discriminate H].
    apply andb_prop in H as [H EX]. apply andb_prop in H as [H AL]. apply andb_prop in H as [H NWK]. apply andb_prop in H as [H XS]. apply andb_prop in H as [L8 D8].
    pose proof (KnownA.KnownA.known_leu_sound E _ _ _ HF L8) as LEN. replace (bv_unsigned (den E (VL (wlit 8064%uint63)))) with 8064 in LEN by (vm_compute; reflexivity).
    exists kb. split; [reflexivity|]. split; [exact LEN|]. split; [exact AL|].
    apply orb_prop in EX as [CV|EX].
    { left. apply existsb_exists in CV as (x & Hx & Q). apply Uint63.eqb_correct in Q. subst x. exact Hx. }
    right. apply existsb_exists in EX as ([[ks lens] kd] & Hin & EV). unfold own_ev1s in EV.
    apply andb_prop in EV as [EV M]. apply andb_prop in EV as [EV NT]. apply andb_prop in EV as [NX NB].
    apply negb_true_iff in NX. apply Uint63.eqb_false_spec in NX. apply negb_true_iff in NT.
    assert (NKB : kd <> CtrLib.K_BLOCK). { intros ->. apply negb_true_iff in NB. rewrite weqb_refl in NB. discriminate NB. }
    destruct (IMap.find ks R) as [r|] eqn:FR; [|discriminate M].
    apply andb_prop in M as [M F]. apply andb_prop in M as [M POS]. apply andb_prop in M as [RW L0]. apply Uint63.eqb_correct in L0.
    destruct (GTwinSub.GTwinSub.find_lb fs ks kb) as [o2|] eqn:LB; [|discriminate F]. destruct (find_ub_sym fs ks) as [[[oU kb'] xs']|] eqn:UB; [|discriminate F].
    apply andb_prop in F as [F NWU]. apply andb_prop in F as [F NW2]. apply andb_prop in F as [F O8]. apply andb_prop in F as [F WT2]. apply andb_prop in F as [EKB EXS].
    apply Uint63.eqb_correct in EKB. subst kb'. apply ValP.sv_eqb_eq in EXS. subst xs'. apply negb_true_iff in WT2. apply Uint63.leb_spec in O8. change (to_Z 8%uint63) with 8 in O8.
    destruct (CallA.find_ub_sym_holds E fs ks oU kb xs HF UB) as [WTU U]. rewrite CallA.den_add_vp0 in U.
    destruct (nowrap_kb_sound E _ HF ks oU NWU) as [_ DU]. rewrite DU in U.
    destruct (nowrap_kb_sound E _ HF kb o2 NW2) as [_ D2].
    destruct (nowrap_kb_sound E _ HF kb _ NWK) as [RK8 _]. replace (w2Zs SYMCAPw) with 65536 in RK8 by (vm_compute; reflexivity).
    pose proof (GTwinSub.GTwinSub.find_lb_holds E _ ks kb o2 HF LB) as L. rewrite HeapCtr.den_VPz in L. rewrite D2 in L.
    assert (ZU : w2Zs oU = to_Z (wl oU)) by (rewrite w2Zs_eq; unfold w2Z; rewrite WTU; lia).
    assert (Z2 : w2Zs o2 = w2Z o2) by (rewrite w2Zs_eq; rewrite WT2; lia). rewrite ZU in U. rewrite Z2 in L. pose proof (w2Z_range o2) as RO2.
    pose proof (KnownA.KnownA.known_leu_sound E _ _ _ HF XS) as X8. replace (bv_unsigned (den E (VL SYMCAPw))) with 65536 in X8 by (vm_compute; reflexivity).
    pose proof (bv_unsigned_in_range 64 (den E xs)) as RX. unfold bv_modulus in RX. change (2 ^ Z.of_N 64) with (2 ^ 64) in RX.
    pose proof (bv_unsigned_in_range 64 (ev E kb)) as RKK. unfold bv_modulus in RKK. change (2 ^ Z.of_N 64) with (2 ^ 64) in RKK.
    unfold two64 in *. rewrite Z.mod_small in U by lia.
    pose proof (CallA.tie_of_holds E fs len xs HF TIE) as TL. pose proof (CallA.div8x_holds E fs xs HF D8) as X0.
    exists ks, lens, kd, r. repeat (split; [assumption|]).
    split. { pose proof (KnownA.KnownA.known_ltu_sound E _ _ _ HF POS) as X. unfold hiZ. cbn [den] in X. rewrite wbv_unsigned, w2Z_wzero in X. exact X. }
    split; [lia|]. rewrite TL. clear - U O8 X0. Z.div_mod_to_equations. lia.
Qed.

Lemma tail_named_In : forall rhs s fs, In (FEq (VP s wzero) rhs) fs -> tail_named rhs s fs = true.
Proof.
  intros rhs s fs. induction fs as [|f fs IH]; intros H; [destruct H|]. destruct H as [->|H].
  - cbn [tail_named]. rewrite (proj2 (Uint63.eqb_spec s s) eq_refl), weqb_refl, sv_eqb_refl. reflexivity.
  - specialize (IH H). cbn [tail_named]. destruct f as [| | | |a b| | |]; try exact IH.
    destruct a as [|s' z| | | | | | | | |]; try exact IH. destruct (PrimInt63.eqb s' s && weqb z wzero && sv_eqb b rhs); [reflexivity| exact IH].
Qed.
Lemma tail_fact_go_inv : forall fs0 wl s l, tail_fact_go fs0 wl s l = true ->
  exists rhs, In (FEq (VP s wzero) rhs) l /\ existsb (tail_win_ok fs0 wl rhs) wl = true.
Proof.
  intros fs0 wl s l. induction l as [|f l IH]; intros H; [discriminate H|]. cbn [tail_fact_go] in H.
  assert (REC : tail_fact_go fs0 wl s l = true -> exists rhs, In (FEq (VP s wzero) rhs) (f :: l) /\ existsb (tail_win_ok fs0 wl rhs) wl = true).
  { intros X. destruct (IH X) as (rhs & I1 & I2). exists rhs. split; [right; exact I1| exact I2]. }
  destruct f as [| | | |a b| | |]; try (apply REC; exact H).
  destruct a as [|s' z| | | | | | | | |]; try (apply REC; exact H).
  destruct (PrimInt63.eqb s' s && weqb z wzero) eqn:Q; [| apply REC; exact H].
  destruct (existsb (tail_win_ok fs0 wl b) wl) eqn:X; [| apply REC; exact H].
  apply andb_prop in Q as [Q1 Q2]. apply Uint63.eqb_correct in Q1. apply weqb_eq in Q2. subst s' z.
  exists b. split; [left; reflexivity| exact X].
Qed.
Lemma view_tail_sound : forall E st ms mo wl k r,
  st_ok segs OPS E st ms mo -> view_tail (s_facts st) wl k r = true ->
  exists sh kb n len, CtrA.win_lookup wl sh = Some (len, K_TWIN) /\ block_of_twin (s_facts st) sh = Some kb
        /\ CtrA.win_lookup wl kb = Some (n, CtrLib.K_BLOCK) /\ size_tail_ok (s_facts st) n = true
        /\ tail_named (tail_rhs sh n) k (s_facts st) = true /\ rg_w r = false
        /\ bv_unsigned (ev E sh) <= bv_unsigned (ev E k) + loZ r
        /\ bv_unsigned (ev E k) + hiZ E r <= bv_unsigned (ev E sh) + bv_unsigned (den E len).
Proof.
  intros E st ms mo wl k r HS H. pose proof (so_facts _ _ _ _ _ _ HS) as HF. unfold view_tail in H.
  destruct (negb (rg_w r) && PrimInt63.eqb (rg_lo r) 0%uint63 && sv_eqb (rg_hi r) (VL wone)) eqn:Q; [|discriminate H].
  apply andb_prop in Q as [Q HI]. apply andb_prop in Q as [WR LO]. apply negb_true_iff in WR. apply Uint63.eqb_correct in LO. apply sv_eqb_eq in HI.
  destruct (tail_fact_go_inv _ _ _ _ H) as (rhs & INF & EX). apply existsb_exists in EX as (e & _ & TW). unfold tail_win_ok in TW. cbv zeta in TW.
  set (sh := fst (fst e)) in *.
  destruct (CtrA.win_lookup wl sh) as [[len kd]|] eqn:WLs; [|discriminate TW]. destruct (block_of_twin (s_facts st) sh) as [kb|] eqn:BT; [|discriminate TW].
  destruct (CtrA.win_lookup wl kb) as [[n kdb]|] eqn:WLk; [|discriminate TW].
  destruct (weqb kd K_TWIN && weqb kdb CtrLib.K_BLOCK) eqn:KK; [|discriminate TW]. apply andb_prop in KK as [K1 K2]. apply weqb_eq in K1, K2. subst kd kdb.
  destruct (sv_eqb rhs (tail_rhs sh n)) eqn:RH; [|discriminate TW]. apply sv_eqb_eq in RH. subst rhs.
  apply andb_prop in TW as [TW NMAX]. apply andb_prop in TW as [LEN ST]. apply sv_eqb_eq in LEN. subst len.
  destruct (CallA.size_tail_sound E _ n HF ST) as [N1 _].
  pose proof (KnownA.KnownA.known_leu_sound E _ _ _ HF NMAX) as NLE. replace (bv_unsigned (den E (VL AREQMAXw))) with 4293918720 in NLE by (vm_compute; reflexivity).
  set (N := bv_unsigned (den E n)) in *.
  pose proof (CallA.block_of_twin_sound E _ sh kb HF BT) as LK. pose proof (bv_unsigned_in_range 64 (ev E kb)) as RK. change (bv_modulus 64) with (2 ^ 64) in RK.
  rewrite Z.mod_small in LK by (clear - RK; Z.div_mod_to_equations; lia).
  pose proof (bv_unsigned_in_range 64 (den E n)) as RN. fold N in RN.
  fold N in N1. assert (B : bv_unsigned (ev E sh) + (N - 1) / 8 < 2 ^ 64) by (rewrite LK; clear - RK NLE RN N1; Z.div_mod_to_equations; lia).
  pose proof (proj1 (Forall_forall _ _) HF _ INF) as FH. cbn [fact_holds] in FH. rewrite HeapCtr.den_VPz in FH. apply (f_equal bv_unsigned) in FH.
  rewrite (CallA.tail_rhs_den E sh n N1 B) in FH. fold N in FH.
  exists sh, kb, n, (twin_len n). split; [exact WLs|]. split; [exact BT|]. split; [exact WLk|]. split; [exact ST|].
  split; [apply tail_named_In; exact INF|]. split; [exact WR|].
  rewrite (CallA.twin_len_den E n ltac:(fold N; lia)). fold N.
  assert (LZ : loZ r = 0) by (unfold loZ; rewrite LO; reflexivity).
  assert (HZ : hiZ E r = 1) by (unfold hiZ; rewrite HI; cbn [den]; rewrite wbv_unsigned; reflexivity).
  rewrite LZ, HZ, FH. clear - N1 RN. split; [Z.div_mod_to_equations; lia| Z.div_mod_to_equations; lia].
Qed.

Theorem view_just_sound : forall E st ms mo wl ks offs rss k r,
  st_ok segs OPS E st ms mo -> sp_region st = Some (ks, offs, rss) ->
  IMap.find k (s_regs st) = Some r -> k <> 0%uint63 ->
  view_just (s_facts st) (s_regs st) (getr st X2) (sp_below_anchor_t (s_facts st) (getr st X2)) wl ks (stack_wlo st) k r = true ->
  view_sem E st wl ks k r.
Proof.
  intros E st ms mo wl ks offs rss k r HS SR Hk K0 J. pose proof (so_facts _ _ _ _ _ _ HS) as HF.
  assert (KZ : PrimInt63.eqb k 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact K0).
  pose proof (so_reg _ _ _ _ _ _ HS k r Hk) as RO. destruct (ro_range _ _ _ _ _ _ RO KZ) as [RLO RHI].
  unfold view_sem. cbv zeta. unfold view_just in J. apply orb_prop in J as [J|TL].
  2:{   right. right. right. exact (view_tail_sound E st ms mo wl k r HS TL). }
  apply orb_prop in J as [J|J].
  - destruct (zero_view r) as [hs|] eqn:ZV; [|discriminate]. destruct (block_of_twin (s_facts st) k) as [n|] eqn:BT; [|discriminate].
    cbv zeta in J. apply andb_prop in J as [J ARMS]. apply andb_prop in J as [J NS]. apply andb_prop in J as [AL NZ].
    rewrite (zero_view_hi E r hs ZV) in *. unfold loZ in *.
    pose proof (view_anchor E _ k n HF BT) as SA. set (S := bv_unsigned (ev E k)) in *. set (N := bv_unsigned (ev E n)) in *.
    assert (N0 : n <> 0%uint63) by (apply Uint63.eqb_false_spec; destruct (PrimInt63.eqb n 0%uint63); [discriminate| reflexivity]).
    assert (SHZ : forall j, shz (N + 8 * j) = S + j).
    { intros j. unfold shz. rewrite SA. replace (N + 8 * j) with (N + j * 8) by lia. rewrite Z.div_add by lia. lia. }
    apply orb_prop in ARMS as [ARMS|T2]; [apply orb_prop in ARMS as [ARMS|TR]; [apply orb_prop in ARMS as [T1|TH]|]|].
    +
      left. unfold view_T1 in T1. apply andb_prop in T1 as [NS1 T1]. apply Uint63.eqb_correct in NS1. subst n.
      destruct (stack_wlo st) as [wlo|] eqn:SW; [|discriminate]. destruct (IMap.find STACK_ID (s_regs st)) as [r1|] eqn:F1; [|discriminate].
      destruct (lit_hi r1) as [h1|] eqn:LH; [|discriminate]. apply andb_prop in T1 as [T1 BT1]. apply andb_prop in T1 as [C1 C2].
      apply Z.leb_le in C1. apply Z.leb_le in C2.
      destruct (nowrap_kb_sound E _ HF STACK_ID wlo (stack_wlo_inv st wlo SW)) as [NWR DW].
      pose proof (below_top_sound segs OPS E st ms mo STACK_ID r1 HS F1 N0 BT1) as TOP. rewrite (lit_hi_sound E r1 h1 LH) in TOP. fold N in TOP, NWR, DW.
      split; [exists hs; reflexivity|]. exists (N + w2Zs wlo), (N + h1). split; [| split; [exact TOP| left; exists wlo; split; [reflexivity| symmetry; exact DW]]].
      intros a Ha. exists (N + 8 * (a - S)). split; [lia|]. rewrite SHZ. lia.
    +
      right. left. unfold view_TH in TH. destruct (find_ub_g (s_facts st) n) as [[kb o1]|] eqn:UB; [|discriminate].
      destruct (GTwinSub.GTwinSub.find_lb (s_facts st) n kb) as [o2|] eqn:LB; [|discriminate].
      destruct (twin_of (s_facts st) kb) as [sh|] eqn:TW; [|discriminate].
      destruct (CtrA.win_lookup wl sh) as [[len kd]|] eqn:WL; [|discriminate].
      apply andb_prop in TH as [TH CLT]. apply andb_prop in TH as [TH CLEN]. apply andb_prop in TH as [TH CLH]. apply andb_prop in TH as [TH CLO].
      apply andb_prop in TH as [TH NW2]. apply andb_prop in TH as [TH NW1]. apply andb_prop in TH as [TH WT2]. apply andb_prop in TH as [TH WT1].
      apply andb_prop in TH as [KD ALK]. apply weqb_eq in KD. subst kd.
      pose proof (GTwinSub.GTwinSub.mod8_of_align E _ kb HF ALK) as K8.
      destruct (nowrap_kb_sound E _ HF kb o1 NW1) as [R1 D1]. destruct (nowrap_kb_sound E _ HF kb o2 NW2) as [R2 D2].
      pose proof (find_ub_g_holds E _ n kb o1 HF UB ltac:(apply negb_true_iff; exact WT1)) as U. pose proof (GTwinSub.GTwinSub.find_lb_holds E _ n kb o2 HF LB) as L.
      rewrite HeapCtr.den_VPz in L. rewrite D2 in L. fold N in U, L.
      assert (O1 : w2Zs o1 = w2Z o1) by (rewrite w2Zs_eq; destruct (wt o1); [discriminate| lia]).
      assert (O2 : w2Zs o2 = w2Z o2) by (rewrite w2Zs_eq; destruct (wt o2); [discriminate| lia]).
      rewrite O1 in *. rewrite O2 in *.
      pose proof (twin_of_sound E _ kb sh HF TW) as SH. pose proof (bv_unsigned_in_range 64 (ev E kb)) as RK. unfold bv_modulus in RK. set (K := bv_unsigned (ev E kb)) in *.
      pose proof (w2Z_range o1) as RO1. pose proof (w2Z_range o2) as RO2.
      rewrite Z.mod_small in SH by (clear - RK; Z.div_mod_to_equations; lia).
      apply Z.leb_le in CLO. apply Z.leb_le in CLH. apply Z.ltb_lt in CLT.
      pose proof (KnownA.KnownA.known_leu_q_sound E _ _ _ HF CLEN) as LEN. cbn [den] in LEN. rewrite wbv_unsigned, wlit_ok in LEN.
      assert (HS0 : 0 <= hs) by (rewrite <- (zero_view_hi E r hs ZV); unfold hiZ; pose proof (bv_unsigned_in_range 64 (den E (rg_hi r))) as X; lia).
      rewrite Uint63.of_Z_spec in LEN. rewrite Z.mod_small in LEN by (rewrite wB_two63, two63_eq; clear - CLT HS0 RO1; Z.div_mod_to_equations; lia).
      exists hs, n, sh, len. split; [reflexivity|]. split; [reflexivity|]. split; [left; exists kb, o1; split; [exact UB| exact TW]|]. split; [exact WL|]. rewrite SH, SA. clear - K8 U L CLO CLH LEN RO1 RO2 R1. Z.div_mod_to_equations. lia.
    +
      right. left. unfold view_TR in TR. apply existsb_exists in TR as (e0 & _ & TR). set (sh := fst (fst e0)) in *. unfold view_TR1 in TR.
      destruct (CtrA.win_lookup wl sh) as [[len kd]|] eqn:WL; [|discriminate]. destruct (IMap.find sh (s_regs st)) as [rsh|] eqn:Fsh; [|discriminate].
      destruct (block_of_twin (s_facts st) sh) as [kB|] eqn:BTs; [|discriminate].
      destruct (rg_hi rsh) as [| |op x c3v| | | | | | | |] eqn:EHI; try discriminate. destruct op; try discriminate.
      destruct x as [| |op2 a b| | | | | | | |]; try discriminate. destruct op2; try discriminate.
      destruct a as [|n' oA| | | | | | | | |]; try discriminate. destruct b as [|k' z| | | | | | | | |]; try discriminate.
      destruct c3v as [c3| | | | | | | | | |]; try discriminate.
      apply andb_prop in TR as [TR VHI]. apply andb_prop in TR as [TR LBO]. apply andb_prop in TR as [TR NWA]. apply andb_prop in TR as [TR ALK].
      apply andb_prop in TR as [TR C8]. apply andb_prop in TR as [TR CLH]. apply andb_prop in TR as [TR CLO]. apply andb_prop in TR as [TR LO0].
      apply andb_prop in TR as [TR WTA]. apply andb_prop in TR as [TR KB]. apply andb_prop in TR as [KD HN].
      apply weqb_eq in KD. subst kd. apply Uint63.eqb_correct in KB. subst k'. apply Uint63.eqb_correct in LO0. apply negb_true_iff in WTA.
      apply Z.leb_le in C8. apply Z.leb_le in CLH. apply Z.leb_le in CLO.
      pose proof HN as HN0. unfold hi_names in HN0. rewrite EHI in HN0. apply andb_prop in HN0 as [HN0 C3]. apply andb_prop in HN0 as [NN Z0].
      apply Uint63.eqb_correct in NN. apply weqb_eq in Z0. apply weqb_eq in C3. subst n' z c3.
      destruct (find_lb_to (s_facts st) n kB) as [o2|] eqn:LB; [|discriminate LBO]. apply andb_prop in LBO as [WT2 NW2]. apply negb_true_iff in WT2.
      pose proof (GTwinSub.GTwinSub.mod8_of_align E _ kB HF ALK) as K8.
      pose proof (GTwinSub.GTwinSub.mod8_of_align E _ n HF AL) as N8. fold N in N8.
      destruct (nowrap_kb_sound E _ HF n oA NWA) as [RA DA]. destruct (nowrap_kb_sound E _ HF kB o2 NW2) as [R2 D2].
      pose proof (CallA.find_lb_to_holds E _ n kB o2 HF LB) as L. rewrite D2 in L. fold N in L, RA, DA.
      assert (OA : w2Zs oA = w2Z oA) by (rewrite w2Zs_eq; rewrite WTA; lia).
      assert (O2 : w2Zs o2 = w2Z o2) by (rewrite w2Zs_eq; rewrite WT2; lia).
      rewrite OA in *. rewrite O2 in *.
      pose proof (view_anchor E _ sh kB HF BTs) as SH. set (K := bv_unsigned (ev E kB)) in *.
      pose proof (w2Z_range oA) as ROA. pose proof (w2Z_range o2) as RO2.
      pose proof (CallA.vec_hi_in_sound E _ _ len HF VHI) as VH. rewrite <- EHI in VH.

      assert (HV : bv_unsigned (den E (rg_hi rsh)) = (N + w2Z oA - K) / 8).
      { rewrite EHI. cbn [den]. unfold alu64, alu. rewrite bv_shiftr_unsigned, bv_and_unsigned, bv_sub_unsigned.
        replace (bv_unsigned (wbv (wlit 3%uint63))) with 3 by (vm_compute; reflexivity).
        replace (bv_unsigned (Z_to_bv 64 63)) with 63 by (vm_compute; reflexivity).
        change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
        change (bv_add (ev E n) (wbv oA)) with (den E (VP n oA)). rewrite DA.
        change (bv_add (ev E kB) (wbv wzero)) with (den E (VP kB wzero)). rewrite (HeapCtr.den_VPz E kB). fold K.
        unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
        pose proof (bv_unsigned_in_range 64 (ev E kB)) as RKK. unfold bv_modulus in RKK. change (2 ^ Z.of_N 64) with (2 ^ 64) in RKK. fold K in RKK.
        unfold two64 in *. rewrite Z.mod_small by lia. reflexivity. }
      rewrite HV in VH.
      exists hs, n, sh, len. split; [reflexivity|]. split; [reflexivity|]. split; [right; exists rsh; split; [exact Fsh| exact HN]|]. split; [exact WL|].
      rewrite SH, SA. clear - K8 N8 L C8 CLO CLH VH RO2 ROA. Z.div_mod_to_equations. lia.
    +
      left. unfold view_T2 in T2. destruct (IMap.find n (s_regs st)) as [rn|] eqn:Fn; [|discriminate].
      destruct (lit_hi rn) as [hn|] eqn:LH; [|discriminate]. apply andb_prop in T2 as [T2 SJ]. apply andb_prop in T2 as [T2 C2]. apply andb_prop in T2 as [_ C1].
      apply Z.leb_le in C1. apply Z.leb_le in C2.
      destruct (stack_side_just_sound segs OPS E st ms mo ks n rn HS Fn N0 SJ) as [SIDE TOP]. rewrite (lit_hi_sound E rn hn LH) in TOP. fold N in TOP, SIDE.
      split; [exists hs; reflexivity|]. exists (N + loZ rn), (N + hn). split; [| split; [exact TOP|]].
      * intros a Ha. exists (N + 8 * (a - S)). unfold loZ. split; [lia|]. rewrite SHZ. lia.
      * destruct SIDE as [->|SIDE]; [right; left; exists rn; split; [exact Fn| reflexivity]| right; right; exact SIDE].
  -
    right. right. left. split; [exact J|]. unfold view_I in J. destruct (ro_lit_hi r) as [hs|] eqn:RL; [|discriminate]. destruct (find_pin (s_facts st) k) as [a|] eqn:FP; [|discriminate].
    apply andb_prop in J as [_ IM]. unfold in_imgsh in IM. apply andb_prop in IM as [IM _]. apply existsb_exists in IM as (v & Hv & C).
    apply andb_prop in C as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2.
    rewrite (ro_lit_hi_sound E r hs RL). rewrite (find_pin_sound E _ k a HF FP). unfold loZ. exists v. split; [exact Hv| split; assumption].
Qed.

Lemma wlo_floor : forall E st hargs n md A nw rest LB ceil wlo,
  find_op HEAP_ID (s_ops st) = Some hargs -> hargs = VL md :: A :: VL nw :: rest -> wt nw = false -> n = Z.to_nat (to_Z (wl nw)) ->
  (3 * n <= length rest)%nat -> HeapOp.windows_wf (wins_of E n rest) LB ceil -> stack_wlo st = Some wlo ->
  ceil <= bv_unsigned (den E (VP STACK_ID wlo)).
Proof.
  intros E st hargs n md A nw rest LB ceil wlo Hf Eh Tnw Nn Ln WF H. unfold stack_wlo in H. rewrite Hf in H.
  assert (HN : heap_nwin hargs = Some n).
  { rewrite Eh. unfold heap_nwin. rewrite Tnw. rewrite <- Nn. destruct (Nat.leb_spec (3 * n) (length rest)); [reflexivity| lia]. }
  rewrite HN in H. rewrite Eh in H. destruct (stack_window_key n rest) as [w|] eqn:SK; [|discriminate].
  destruct (nowrap_kb (s_facts st) STACK_ID w); [|discriminate]. injection H as <-.
  destruct (stack_window_key_In E n rest w SK) as (len & INW).
  pose proof (proj1 (Forall_forall _ _) WF _ INW) as (_ & _ & _ & [[_ C]|[[K _]|[K _]]]); cbn [HeapOp.w_kind HeapOp.w_lo] in *; [exact C| |];
    unfold HeapOp.K_STACK, HeapOp.K_BLOCK, HeapOp.K_SUB in K; lia.
Qed.

End CallV.

Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.
Import GlueA.TwinB Actr.TwinB CallA.TwinB.

Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan ValP MemP CtrLib CtrFX ActrA.
Open Scope Z_scope.
Unset Lia Cache.

Unset Nia Cache. Unset Nra Cache.

Section CallV.
Variable segs : list Segment.
Variable OPS : optable.

Definition shz (a : Z) : Z := a / 8 + 0x7fff8000.

Definition view_parent (fs : list fact) (R : IMap.t region) (n sh : int) : Prop :=
  (exists kb o1, find_ub_g fs n = Some (kb, o1) /\ twin_of fs kb = Some sh)
  \/ (exists rsh, IMap.find sh R = Some rsh /\ hi_names rsh n = true).
Definition view_sem (E : env) (st : sstate) (wl : list (int * sv * w64)) (ks k : int) (r : region) : Prop :=
  let lo := bv_unsigned (ev E k) + loZ r in
  let hi := bv_unsigned (ev E k) + hiZ E r in
  ((exists hs, zero_view r = Some hs) /\
   exists blo bhi, (forall a, lo <= a < hi -> exists a', blo <= a' < bhi /\ a = shz a') /\ bhi <= 2 ^ 47 /\
      ((exists wlo, stack_wlo st = Some wlo /\ blo = bv_unsigned (den E (VP STACK_ID wlo)))
       \/ (exists rs, IMap.find ks (s_regs st) = Some rs /\ blo = bv_unsigned (ev E ks) + loZ rs)
       \/ bv_unsigned (den E (getr st X2)) <= blo))
  \/ (exists hs n sh len, zero_view r = Some hs /\ block_of_twin (s_facts st) k = Some n /\ view_parent (s_facts st) (s_regs st) n sh
        /\ CtrA.win_lookup wl sh = Some (len, K_TWIN)
        /\ bv_unsigned (ev E sh) <= lo /\ hi <= bv_unsigned (ev E sh) + bv_unsigned (den E len))
  \/ (view_I (s_facts st) k r = true /\ exists v, In v IMGSH /\ fst v <= lo /\ hi <= snd v)

  \/ (exists sh kb n len, CtrA.win_lookup wl sh = Some (len, K_TWIN) /\ block_of_twin (s_facts st) sh = Some kb
        /\ CtrA.win_lookup wl kb = Some (n, CtrLib.K_BLOCK) /\ size_tail_ok (s_facts st) n = true
        /\ tail_named (tail_rhs sh n) k (s_facts st) = true /\ rg_w r = false
        /\ bv_unsigned (ev E sh) <= lo /\ hi <= bv_unsigned (ev E sh) + bv_unsigned (den E len)).

Lemma zero_view_hi : forall E r hs, zero_view r = Some hs -> hiZ E r = hs.
Proof.
  intros E r hs H. unfold zero_view in H. unfold hiZ. destruct (rg_hi r) as [w| | | | | | | | | |]; try discriminate.
  destruct (rg_bg r); try discriminate. destruct (rg_cells r); try discriminate.
  destruct (negb (rg_w r) && negb (wt w)); [| discriminate]. injection H as <-. cbn [den]. apply wbv_unsigned.
Qed.
Lemma lit_hi_sound : forall E r h, lit_hi r = Some h -> hiZ E r = h.
Proof.
  intros E r h H. unfold lit_hi in H. unfold hiZ. destruct (rg_hi r) as [w| | | | | | | | | |]; try discriminate.
  destruct (wt w); [discriminate|]. injection H as <-. cbn [den]. apply wbv_unsigned.
Qed.
Lemma ro_lit_hi_sound : forall E r h, ro_lit_hi r = Some h -> hiZ E r = h.
Proof.
  intros E r h H. unfold ro_lit_hi in H. unfold hiZ. destruct (rg_hi r) as [w| | | | | | | | | |]; try discriminate.
  destruct (negb (rg_w r) && negb (wt w)); [| discriminate]. injection H as <-. cbn [den]. apply wbv_unsigned.
Qed.

Lemma twin_of_sound : forall E fs k sh, facts_hold E fs -> twin_of fs k = Some sh ->
  bv_unsigned (ev E sh) = (bv_unsigned (ev E k) / 8 + 0x7fff8000) mod 2 ^ 64.
Proof.
  intros E fs k sh HF. unfold twin_of. induction fs as [|f fs IH]; intros H; [discriminate|].
  inversion HF as [|f' l Hf HF']; subst.
  assert (STEP : (fix go (l : list fact) : option int :=
                    match l with
                    | FEq (VP sh0 o) (VAlu ALU_ADD (VAlu ALU_SRL (VP k' o') (VL c3)) (VL sb)) :: l' =>
                        if PrimInt63.eqb k k' && weqb o wzero && weqb o' wzero && weqb c3 (wlit 3%uint63) && weqb sb SBw then Some sh0 else go l'
                    | _ :: l' => go l'
                    | [] => None
                    end) fs = Some sh -> bv_unsigned (ev E sh) = (bv_unsigned (ev E k) / 8 + 0x7fff8000) mod 2 ^ 64) by exact (IH HF').
  destruct f as [| | | |x y| | |]; try (apply STEP; exact H).
  destruct x as [|sh0 z| | | | | | | | |]; try (apply STEP; exact H).
  destruct y as [| |op y1 y2| | | | | | | |]; try (apply STEP; exact H). destruct op; try (apply STEP; exact H).
  destruct y1 as [| |op1 u1 u2| | | | | | | |]; try (apply STEP; exact H). destruct op1; try (apply STEP; exact H).
  destruct u1 as [|k' z'| | | | | | | | |]; try (apply STEP; exact H). destruct u2 as [c| | | | | | | | | |]; try (apply STEP; exact H).
  destruct y2 as [s'| | | | | | | | | |]; try (apply STEP; exact H).
  destruct (PrimInt63.eqb k k' && weqb z wzero && weqb z' wzero && weqb c (wlit 3%uint63) && weqb s' SBw) eqn:C; [|apply STEP; exact H].
  injection H as ->. apply andb_prop in C as [C S']. apply andb_prop in C as [C C3]. apply andb_prop in C as [C Z']. apply andb_prop in C as [K' Z0].
  apply Uint63.eqb_correct in K'. subst k'.
  apply (block_of_twin_sound E [FEq (VP sh z) (VAlu ALU_ADD (VAlu ALU_SRL (VP k z') (VL c)) (VL s'))] sh k).
  - constructor; [exact Hf| constructor].
  - unfold block_of_twin. rewrite Uint63.eqb_refl, Z0, Z', C3, S'. reflexivity.
Qed.

Lemma find_pin_sound : forall E fs s a, facts_hold E fs -> find_pin fs s = Some a -> bv_unsigned (ev E s) = w2Z a.
Proof.
  intros E fs s a HF. unfold find_pin. induction fs as [|f fs IH]; intros H; [discriminate|].
  inversion HF as [|f' l Hf HF']; subst.
  assert (STEP : (fix go (l : list fact) : option w64 :=
                    match l with
                    | FEq (VP s' z) (VL a0) :: l' => if PrimInt63.eqb s s' && weqb z wzero then Some a0 else go l'
                    | _ :: l' => go l'
                    | [] => None
                    end) fs = Some a -> bv_unsigned (ev E s) = w2Z a) by exact (IH HF').
  destruct f as [| | | |x y| | |]; try (apply STEP; exact H).
  destruct x as [|s' z| | | | | | | | |]; try (apply STEP; exact H).
  destruct y as [a0| | | | | | | | | |]; try (apply STEP; exact H).
  destruct (PrimInt63.eqb s s' && weqb z wzero) eqn:C; [|apply STEP; exact H].
  injection H as ->. apply andb_prop in C as [S' Z0]. apply Uint63.eqb_correct in S'. apply weqb_eq in Z0. subst s' z.
  cbn [fact_holds] in Hf. rewrite HeapCtr.TwinB.den_VPz in Hf. rewrite Hf. cbn [den]. apply wbv_unsigned.
Qed.

Lemma stack_wlo_inv : forall st wlo, stack_wlo st = Some wlo -> nowrap_kb (s_facts st) STACK_ID wlo = true.
Proof.
  intros st wlo H. unfold stack_wlo in H. destruct (find_op HEAP_ID (s_ops st)) as [hargs|]; [|discriminate].
  destruct (heap_nwin hargs) as [n|]; [|discriminate]. destruct hargs as [|h1 [|h2 [|h3 rest]]]; try discriminate.
  destruct (stack_window_key n rest) as [w|]; [|discriminate]. destruct (nowrap_kb (s_facts st) STACK_ID w) eqn:NW; [|discriminate].
  injection H as <-. exact NW.
Qed.

Lemma view_anchor : forall E fs s n, facts_hold E fs -> block_of_twin fs s = Some n ->
  bv_unsigned (ev E s) = bv_unsigned (ev E n) / 8 + 0x7fff8000.
Proof.
  intros E fs s n HF BT. rewrite (block_of_twin_sound E fs s n HF BT).
  pose proof (bv_unsigned_in_range 64 (ev E n)) as R. unfold bv_modulus in R. apply Z.mod_small. Z.div_mod_to_equations. lia.
Qed.

Lemma ub_cand_holds : forall E fs n f k o, facts_hold E fs -> fact_holds E f -> ub_cand fs n f = Some (k, o) ->
  wt o = false /\ bv_unsigned (ev E n) <= bv_unsigned (ev E k) + w2Z o.
Proof.
  intros E fs n f k o HF Hf H. unfold ub_cand in H. destruct f as [| | |x y|x y| | |]; try discriminate H.
  destruct x as [|n' oU| | | | | | | | |]; try discriminate H. destruct y as [|k' cU| | | | | | | | |]; try discriminate H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:C; [|discriminate H] end. injection H as <- <-.
  apply andb_prop in C as [C NWK]. apply andb_prop in C as [C NWN]. apply andb_prop in C as [C LE]. apply andb_prop in C as [C TC]. apply andb_prop in C as [EN TU].
  apply Uint63.eqb_correct in EN. subst n'. apply negb_true_iff in TU. apply negb_true_iff in TC. apply Uint63.leb_spec in LE.
  destruct (nowrap_kb_sound E _ HF n oU NWN) as [_ DN]. destruct (nowrap_kb_sound E _ HF k' cU NWK) as [_ DK].
  cbn [fact_holds] in Hf. rewrite DN, DK in Hf.
  assert (ZU : w2Zs oU = w2Z oU) by (rewrite w2Zs_eq; rewrite TU; lia).
  assert (ZC : w2Zs cU = w2Z cU) by (rewrite w2Zs_eq; rewrite TC; lia).
  assert (WU : w2Z oU = to_Z (wl oU)) by (unfold w2Z; rewrite TU; lia).
  assert (WC : w2Z cU = to_Z (wl cU)) by (unfold w2Z; rewrite TC; lia).
  pose proof (w2Z_range oU) as RU. pose proof (w2Z_range cU) as RC. unfold two64 in RU, RC.
  assert (SUBV : w2Z (wsub cU oU) = w2Z cU - w2Z oU) by (rewrite wsub_ok; unfold two64; apply Z.mod_small; lia).
  split.
  - rewrite w2Z_wt. apply Z.leb_gt. rewrite SUBV. pose proof (to_Z_bounded (wl cU)) as B. rewrite wB_two63 in B. unfold two63 in *. lia.
  - rewrite SUBV. lia.
Qed.
Lemma find_ub_go_holds : forall E fsA n fs acc k o, facts_hold E fsA -> Forall (fact_holds E) fs ->
  (forall k0 o0, acc = Some (k0, o0) -> wt o0 = false /\ bv_unsigned (ev E n) <= bv_unsigned (ev E k0) + w2Z o0) ->
  find_ub_go fsA n fs acc = Some (k, o) -> wt o = false /\ bv_unsigned (ev E n) <= bv_unsigned (ev E k) + w2Z o.
Proof.
  intros E fsA n fs. induction fs as [|f fs IH]; intros acc k o HA HF ACC H; cbn [find_ub_go] in H; [exact (ACC k o H)|].
  inversion HF as [|f' l Hf HF']; subst. refine (IH _ k o HA HF' _ H).
  intros k0 o0 E0. destruct (ub_cand fsA n f) as [[k1 o1]|] eqn:UC; [| exact (ACC k0 o0 E0)].
  pose proof (ub_cand_holds E fsA n f k1 o1 HA Hf UC) as G.
  destruct acc as [[k2 o2]|]; [| injection E0 as <- <-; exact G].
  destruct (PrimInt63.eqb k1 k2 && wltu o1 o2); [injection E0 as <- <-; exact G| exact (ACC k0 o0 E0)].
Qed.
Lemma find_ub_g_holds : forall E fs n k o, facts_hold E fs -> find_ub_g fs n = Some (k, o) -> wt o = false ->
  bv_unsigned (ev E n) <= bv_unsigned (ev E k) + w2Z o.
Proof.
  intros E fs n k o HF H WT. unfold find_ub_g in H. destruct (GTwinSub.GTwinSub.find_ub fs n) as [[k' o']|] eqn:UB.
  - injection H as <- <-. pose proof (GTwinSub.GTwinSub.find_ub_holds E fs n k' o' HF UB) as U. rewrite HeapCtr.TwinB.den_VPz in U.
    cbn [den] in U. rewrite bv_add_unsigned, wbv_unsigned in U. unfold bv_wrap, bv_modulus in U.
    pose proof (bv_unsigned_in_range 64 (ev E k')) as RK. unfold bv_modulus in RK. pose proof (w2Z_range o') as RO. unfold two64 in RO.
    clear - U RK RO. Z.div_mod_to_equations. lia.
  - exact (proj2 (find_ub_go_holds E fs n fs None k o HF HF ltac:(intros ? ? X; discriminate X) H)).
Qed.

Lemma twin_arm_ev_sound : forall E fs ks kb (r : region) o2 o1 lw, facts_hold E fs ->
  PrimInt63.leb 3%uint63 (find_align fs kb) = true -> KnownT.KnownT.known_ltu_t fs (VL wzero) (rg_hi r) = true ->
  GTwinSub.GTwinSub.find_lb fs ks kb = Some o2 -> find_ub_g fs ks = Some (kb, o1) -> wt o2 = false -> wt o1 = false ->
  nowrap_kb fs kb o2 = true -> to_Z (wl o1) + 8 <= 8 * to_Z (wl lw) ->
  bv_unsigned (ev E kb) mod 8 = 0 /\ 0 < hiZ E r
  /\ bv_unsigned (ev E kb) <= bv_unsigned (ev E ks) /\ bv_unsigned (ev E ks) + 8 <= bv_unsigned (ev E kb) + 8 * to_Z (wl lw).
Proof.
  intros E fs ks kb r o2 o1 lw HF AL POS LB UB WT2 WT1 NW LE8.
  split; [exact (GTwinSub.GTwinSub.mod8_of_align E _ kb HF AL)|].
  split. { pose proof (KnownA.TwinB.KnownA.known_ltu_sound E _ _ _ HF POS) as X. unfold hiZ. cbn [den] in X. rewrite wbv_unsigned, w2Z_wzero in X. exact X. }
  pose proof (GTwinSub.GTwinSub.find_lb_holds E _ ks kb o2 HF LB) as L. rewrite HeapCtr.TwinB.den_VPz in L.
  destruct (nowrap_kb_sound E _ HF kb o2 NW) as [_ D2]. rewrite D2 in L.
  assert (Z2 : w2Zs o2 = w2Z o2) by (rewrite w2Zs_eq; rewrite WT2; lia). rewrite Z2 in L. pose proof (w2Z_range o2) as RO2.
  pose proof (find_ub_g_holds E fs ks kb o1 HF UB WT1) as U.
  assert (W1 : w2Z o1 = to_Z (wl o1)) by (unfold w2Z; rewrite WT1; lia).
  split; lia.
Qed.

Lemma twin_ev_cases : forall E fs R wl0 cv sh len kx, facts_hold E fs -> twin_arm_evx fs R wl0 cv sh len kx = true ->
  exists kb, block_of_twin fs sh = Some kb /\ bv_unsigned (den E len) <= 8064 /\ PrimInt63.leb 3%uint63 (find_align fs kb) = true
    /\ (In kb cv
        \/ exists ks lens kd r, In (ks, lens, kd) wl0 /\ ks <> kx /\ kd <> CtrLib.K_BLOCK /\ weqb kd K_TWIN = false
             /\ IMap.find ks R = Some r /\ rg_w r = true /\ rg_lo r = 0%uint63
             /\ 0 < hiZ E r /\ bv_unsigned (ev E kb) <= bv_unsigned (ev E ks)
             /\ bv_unsigned (ev E ks) + 8 <= bv_unsigned (ev E kb) + 8 * bv_unsigned (den E len)).
Proof.
  intros E fs R wl0 cv sh len kx HF H. unfold twin_arm_evx in H. apply orb_prop in H as [H|H].
  -
    destruct (CallA.TwinB.twin_arm_ev_inv _ _ _ _ _ _ _ H) as (lw & kb & -> & BT & WTL & LW & AL & EVD). exists kb.
    assert (DL : bv_unsigned (den E (VL lw)) = to_Z (wl lw)) by (cbn [den]; rewrite wbv_unsigned; unfold w2Z; rewrite WTL; reflexivity).
    split; [exact BT|]. split; [rewrite DL; exact LW|]. split; [exact AL|].
    destruct EVD as [CV|(ks & lens & kd & r & o2 & o1 & Hin & NX & NKB & NKT & Fr & RW & L0 & POS & LB & UB & WT2 & WT1 & NW & LE8)]; [left; exact CV| right].
    destruct (twin_arm_ev_sound E _ ks kb r o2 o1 lw HF AL POS LB UB WT2 WT1 NW LE8) as (_ & HPOS & XLO & XHI).
    exists ks, lens, kd, r. rewrite DL. repeat (split; [assumption|]). exact XHI.
  -
    unfold twin_arm_evs in H. destruct (tie_of fs len) as [xs|] eqn:TIE; [|discriminate H]. destruct (block_of_twin fs sh) as [kb|] eqn:BT; [|discriminate H].
    apply andb_prop in H as [H EX]. apply andb_prop in H as [H AL]. apply andb_prop in H as [H NWK]. apply andb_prop in H as [H XS]. apply andb_prop in H as [L8 D8].
    pose proof (KnownA.TwinB.KnownA.known_leu_sound E _ _ _ HF L8) as LEN. replace (bv_unsigned (den E (VL (wlit 8064%uint63)))) with 8064 in LEN by (vm_compute; reflexivity).
    exists kb. split; [reflexivity|]. split; [exact LEN|]. split; [exact AL|].
    apply orb_prop in EX as [CV|EX].
    { left. apply existsb_exists in CV as (x & Hx & Q). apply Uint63.eqb_correct in Q. subst x. exact Hx. }
    right. apply existsb_exists in EX as ([[ks lens] kd] & Hin & EV). unfold own_ev1s in EV.
    apply andb_prop in EV as [EV M]. apply andb_prop in EV as [EV NT]. apply andb_prop in EV as [NX NB].
    apply negb_true_iff in NX. apply Uint63.eqb_false_spec in NX. apply negb_true_iff in NT.
    assert (NKB : kd <> CtrLib.K_BLOCK). { intros ->. apply negb_true_iff in NB. rewrite weqb_refl in NB. discriminate NB. }
    destruct (IMap.find ks R) as [r|] eqn:FR; [|discriminate M].
    apply andb_prop in M as [M F]. apply andb_prop in M as [M POS]. apply andb_prop in M as [RW L0]. apply Uint63.eqb_correct in L0.
    destruct (GTwinSub.GTwinSub.find_lb fs ks kb) as [o2|] eqn:LB; [|discriminate F]. destruct (find_ub_sym fs ks) as [[[oU kb'] xs']|] eqn:UB; [|discriminate F].
    apply andb_prop in F as [F NWU]. apply andb_prop in F as [F NW2]. apply andb_prop in F as [F O8]. apply andb_prop in F as [F WT2]. apply andb_prop in F as [EKB EXS].
    apply Uint63.eqb_correct in EKB. subst kb'. apply ValP.sv_eqb_eq in EXS. subst xs'. apply negb_true_iff in WT2. apply Uint63.leb_spec in O8. change (to_Z 8%uint63) with 8 in O8.
    destruct (CallA.TwinB.find_ub_sym_holds E fs ks oU kb xs HF UB) as [WTU U]. rewrite CallA.TwinB.den_add_vp0 in U.
    destruct (nowrap_kb_sound E _ HF ks oU NWU) as [_ DU]. rewrite DU in U.
    destruct (nowrap_kb_sound E _ HF kb o2 NW2) as [_ D2].
    destruct (nowrap_kb_sound E _ HF kb _ NWK) as [RK8 _]. replace (w2Zs SYMCAPw) with 65536 in RK8 by (vm_compute; reflexivity).
    pose proof (GTwinSub.GTwinSub.find_lb_holds E _ ks kb o2 HF LB) as L. rewrite HeapCtr.TwinB.den_VPz in L. rewrite D2 in L.
    assert (ZU : w2Zs oU = to_Z (wl oU)) by (rewrite w2Zs_eq; unfold w2Z; rewrite WTU; lia).
    assert (Z2 : w2Zs o2 = w2Z o2) by (rewrite w2Zs_eq; rewrite WT2; lia). rewrite ZU in U. rewrite Z2 in L. pose proof (w2Z_range o2) as RO2.
    pose proof (KnownA.TwinB.KnownA.known_leu_sound E _ _ _ HF XS) as X8. replace (bv_unsigned (den E (VL SYMCAPw))) with 65536 in X8 by (vm_compute; reflexivity).
    pose proof (bv_unsigned_in_range 64 (den E xs)) as RX. unfold bv_modulus in RX. change (2 ^ Z.of_N 64) with (2 ^ 64) in RX.
    pose proof (bv_unsigned_in_range 64 (ev E kb)) as RKK. unfold bv_modulus in RKK. change (2 ^ Z.of_N 64) with (2 ^ 64) in RKK.
    unfold two64 in *. rewrite Z.mod_small in U by lia.
    pose proof (CallA.TwinB.tie_of_holds E fs len xs HF TIE) as TL. pose proof (CallA.TwinB.div8x_holds E fs xs HF D8) as X0.
    exists ks, lens, kd, r. repeat (split; [assumption|]).
    split. { pose proof (KnownA.TwinB.KnownA.known_ltu_sound E _ _ _ HF POS) as X. unfold hiZ. cbn [den] in X. rewrite wbv_unsigned, w2Z_wzero in X. exact X. }
    split; [lia|]. rewrite TL. clear - U O8 X0. Z.div_mod_to_equations. lia.
Qed.

Lemma tail_named_In : forall rhs s fs, In (FEq (VP s wzero) rhs) fs -> tail_named rhs s fs = true.
Proof.
  intros rhs s fs. induction fs as [|f fs IH]; intros H; [destruct H|]. destruct H as [->|H].
  - cbn [tail_named]. rewrite (proj2 (Uint63.eqb_spec s s) eq_refl), weqb_refl, sv_eqb_refl. reflexivity.
  - specialize (IH H). cbn [tail_named]. destruct f as [| | | |a b| | |]; try exact IH.
    destruct a as [|s' z| | | | | | | | |]; try exact IH. destruct (PrimInt63.eqb s' s && weqb z wzero && sv_eqb b rhs); [reflexivity| exact IH].
Qed.
Lemma tail_fact_go_inv : forall fs0 wl s l, tail_fact_go fs0 wl s l = true ->
  exists rhs, In (FEq (VP s wzero) rhs) l /\ existsb (tail_win_ok fs0 wl rhs) wl = true.
Proof.
  intros fs0 wl s l. induction l as [|f l IH]; intros H; [discriminate H|]. cbn [tail_fact_go] in H.
  assert (REC : tail_fact_go fs0 wl s l = true -> exists rhs, In (FEq (VP s wzero) rhs) (f :: l) /\ existsb (tail_win_ok fs0 wl rhs) wl = true).
  { intros X. destruct (IH X) as (rhs & I1 & I2). exists rhs. split; [right; exact I1| exact I2]. }
  destruct f as [| | | |a b| | |]; try (apply REC; exact H).
  destruct a as [|s' z| | | | | | | | |]; try (apply REC; exact H).
  destruct (PrimInt63.eqb s' s && weqb z wzero) eqn:Q; [| apply REC; exact H].
  destruct (existsb (tail_win_ok fs0 wl b) wl) eqn:X; [| apply REC; exact H].
  apply andb_prop in Q as [Q1 Q2]. apply Uint63.eqb_correct in Q1. apply weqb_eq in Q2. subst s' z.
  exists b. split; [left; reflexivity| exact X].
Qed.
Lemma view_tail_sound : forall E st ms mo wl k r,
  st_ok segs OPS E st ms mo -> view_tail (s_facts st) wl k r = true ->
  exists sh kb n len, CtrA.win_lookup wl sh = Some (len, K_TWIN) /\ block_of_twin (s_facts st) sh = Some kb
        /\ CtrA.win_lookup wl kb = Some (n, CtrLib.K_BLOCK) /\ size_tail_ok (s_facts st) n = true
        /\ tail_named (tail_rhs sh n) k (s_facts st) = true /\ rg_w r = false
        /\ bv_unsigned (ev E sh) <= bv_unsigned (ev E k) + loZ r
        /\ bv_unsigned (ev E k) + hiZ E r <= bv_unsigned (ev E sh) + bv_unsigned (den E len).
Proof.
  intros E st ms mo wl k r HS H. pose proof (so_facts _ _ _ _ _ _ HS) as HF. unfold view_tail in H.
  destruct (negb (rg_w r) && PrimInt63.eqb (rg_lo r) 0%uint63 && sv_eqb (rg_hi r) (VL wone)) eqn:Q; [|discriminate H].
  apply andb_prop in Q as [Q HI]. apply andb_prop in Q as [WR LO]. apply negb_true_iff in WR. apply Uint63.eqb_correct in LO. apply sv_eqb_eq in HI.
  destruct (tail_fact_go_inv _ _ _ _ H) as (rhs & INF & EX). apply existsb_exists in EX as (e & _ & TW). unfold tail_win_ok in TW. cbv zeta in TW.
  set (sh := fst (fst e)) in *.
  destruct (CtrA.win_lookup wl sh) as [[len kd]|] eqn:WLs; [|discriminate TW]. destruct (block_of_twin (s_facts st) sh) as [kb|] eqn:BT; [|discriminate TW].
  destruct (CtrA.win_lookup wl kb) as [[n kdb]|] eqn:WLk; [|discriminate TW].
  destruct (weqb kd K_TWIN && weqb kdb CtrLib.K_BLOCK) eqn:KK; [|discriminate TW]. apply andb_prop in KK as [K1 K2]. apply weqb_eq in K1, K2. subst kd kdb.
  destruct (sv_eqb rhs (tail_rhs sh n)) eqn:RH; [|discriminate TW]. apply sv_eqb_eq in RH. subst rhs.
  apply andb_prop in TW as [TW NMAX]. apply andb_prop in TW as [LEN ST]. apply sv_eqb_eq in LEN. subst len.
  destruct (CallA.TwinB.size_tail_sound E _ n HF ST) as [N1 _].
  pose proof (KnownA.TwinB.KnownA.known_leu_sound E _ _ _ HF NMAX) as NLE. replace (bv_unsigned (den E (VL AREQMAXw))) with 4293918720 in NLE by (vm_compute; reflexivity).
  set (N := bv_unsigned (den E n)) in *.
  pose proof (CallA.TwinB.block_of_twin_sound E _ sh kb HF BT) as LK. pose proof (bv_unsigned_in_range 64 (ev E kb)) as RK. change (bv_modulus 64) with (2 ^ 64) in RK.
  rewrite Z.mod_small in LK by (clear - RK; Z.div_mod_to_equations; lia).
  pose proof (bv_unsigned_in_range 64 (den E n)) as RN. fold N in RN.
  fold N in N1. assert (B : bv_unsigned (ev E sh) + (N - 1) / 8 < 2 ^ 64) by (rewrite LK; clear - RK NLE RN N1; Z.div_mod_to_equations; lia).
  pose proof (proj1 (Forall_forall _ _) HF _ INF) as FH. cbn [fact_holds] in FH. rewrite HeapCtr.TwinB.den_VPz in FH. apply (f_equal bv_unsigned) in FH.
  rewrite (CallA.TwinB.tail_rhs_den E sh n N1 B) in FH. fold N in FH.
  exists sh, kb, n, (twin_len n). split; [exact WLs|]. split; [exact BT|]. split; [exact WLk|]. split; [exact ST|].
  split; [apply tail_named_In; exact INF|]. split; [exact WR|].
  rewrite (CallA.TwinB.twin_len_den E n ltac:(fold N; lia)). fold N.
  assert (LZ : loZ r = 0) by (unfold loZ; rewrite LO; reflexivity).
  assert (HZ : hiZ E r = 1) by (unfold hiZ; rewrite HI; cbn [den]; rewrite wbv_unsigned; reflexivity).
  rewrite LZ, HZ, FH. clear - N1 RN. split; [Z.div_mod_to_equations; lia| Z.div_mod_to_equations; lia].
Qed.

Theorem view_just_sound : forall E st ms mo wl ks offs rss k r,
  st_ok segs OPS E st ms mo -> sp_region st = Some (ks, offs, rss) ->
  IMap.find k (s_regs st) = Some r -> k <> 0%uint63 ->
  view_just (s_facts st) (s_regs st) (getr st X2) (sp_below_anchor_t (s_facts st) (getr st X2)) wl ks (stack_wlo st) k r = true ->
  view_sem E st wl ks k r.
Proof.
  intros E st ms mo wl ks offs rss k r HS SR Hk K0 J. pose proof (so_facts _ _ _ _ _ _ HS) as HF.
  assert (KZ : PrimInt63.eqb k 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact K0).
  pose proof (so_reg _ _ _ _ _ _ HS k r Hk) as RO. destruct (ro_range _ _ _ _ _ _ RO KZ) as [RLO RHI].
  unfold view_sem. cbv zeta. unfold view_just in J. apply orb_prop in J as [J|TL].
  2:{   right. right. right. exact (view_tail_sound E st ms mo wl k r HS TL). }
  apply orb_prop in J as [J|J].
  - destruct (zero_view r) as [hs|] eqn:ZV; [|discriminate]. destruct (block_of_twin (s_facts st) k) as [n|] eqn:BT; [|discriminate].
    cbv zeta in J. apply andb_prop in J as [J ARMS]. apply andb_prop in J as [J NS]. apply andb_prop in J as [AL NZ].
    rewrite (zero_view_hi E r hs ZV) in *. unfold loZ in *.
    pose proof (view_anchor E _ k n HF BT) as SA. set (S := bv_unsigned (ev E k)) in *. set (N := bv_unsigned (ev E n)) in *.
    assert (N0 : n <> 0%uint63) by (apply Uint63.eqb_false_spec; destruct (PrimInt63.eqb n 0%uint63); [discriminate| reflexivity]).
    assert (SHZ : forall j, shz (N + 8 * j) = S + j).
    { intros j. unfold shz. rewrite SA. replace (N + 8 * j) with (N + j * 8) by lia. rewrite Z.div_add by lia. lia. }
    apply orb_prop in ARMS as [ARMS|T2]; [apply orb_prop in ARMS as [ARMS|TR]; [apply orb_prop in ARMS as [T1|TH]|]|].
    +
      left. unfold view_T1 in T1. apply andb_prop in T1 as [NS1 T1]. apply Uint63.eqb_correct in NS1. subst n.
      destruct (stack_wlo st) as [wlo|] eqn:SW; [|discriminate]. destruct (IMap.find STACK_ID (s_regs st)) as [r1|] eqn:F1; [|discriminate].
      destruct (lit_hi r1) as [h1|] eqn:LH; [|discriminate]. apply andb_prop in T1 as [T1 BT1]. apply andb_prop in T1 as [C1 C2].
      apply Z.leb_le in C1. apply Z.leb_le in C2.
      destruct (nowrap_kb_sound E _ HF STACK_ID wlo (stack_wlo_inv st wlo SW)) as [NWR DW].
      pose proof (below_top_sound segs OPS E st ms mo STACK_ID r1 HS F1 N0 BT1) as TOP. rewrite (lit_hi_sound E r1 h1 LH) in TOP. fold N in TOP, NWR, DW.
      split; [exists hs; reflexivity|]. exists (N + w2Zs wlo), (N + h1). split; [| split; [exact TOP| left; exists wlo; split; [reflexivity| symmetry; exact DW]]].
      intros a Ha. exists (N + 8 * (a - S)). split; [lia|]. rewrite SHZ. lia.
    +
      right. left. unfold view_TH in TH. destruct (find_ub_g (s_facts st) n) as [[kb o1]|] eqn:UB; [|discriminate].
      destruct (GTwinSub.GTwinSub.find_lb (s_facts st) n kb) as [o2|] eqn:LB; [|discriminate].
      destruct (twin_of (s_facts st) kb) as [sh|] eqn:TW; [|discriminate].
      destruct (CtrA.win_lookup wl sh) as [[len kd]|] eqn:WL; [|discriminate].
      apply andb_prop in TH as [TH CLT]. apply andb_prop in TH as [TH CLEN]. apply andb_prop in TH as [TH CLH]. apply andb_prop in TH as [TH CLO].
      apply andb_prop in TH as [TH NW2]. apply andb_prop in TH as [TH NW1]. apply andb_prop in TH as [TH WT2]. apply andb_prop in TH as [TH WT1].
      apply andb_prop in TH as [KD ALK]. apply weqb_eq in KD. subst kd.
      pose proof (GTwinSub.GTwinSub.mod8_of_align E _ kb HF ALK) as K8.
      destruct (nowrap_kb_sound E _ HF kb o1 NW1) as [R1 D1]. destruct (nowrap_kb_sound E _ HF kb o2 NW2) as [R2 D2].
      pose proof (find_ub_g_holds E _ n kb o1 HF UB ltac:(apply negb_true_iff; exact WT1)) as U. pose proof (GTwinSub.GTwinSub.find_lb_holds E _ n kb o2 HF LB) as L.
      rewrite HeapCtr.TwinB.den_VPz in L. rewrite D2 in L. fold N in U, L.
      assert (O1 : w2Zs o1 = w2Z o1) by (rewrite w2Zs_eq; destruct (wt o1); [discriminate| lia]).
      assert (O2 : w2Zs o2 = w2Z o2) by (rewrite w2Zs_eq; destruct (wt o2); [discriminate| lia]).
      rewrite O1 in *. rewrite O2 in *.
      pose proof (twin_of_sound E _ kb sh HF TW) as SH. pose proof (bv_unsigned_in_range 64 (ev E kb)) as RK. unfold bv_modulus in RK. set (K := bv_unsigned (ev E kb)) in *.
      pose proof (w2Z_range o1) as RO1. pose proof (w2Z_range o2) as RO2.
      rewrite Z.mod_small in SH by (clear - RK; Z.div_mod_to_equations; lia).
      apply Z.leb_le in CLO. apply Z.leb_le in CLH. apply Z.ltb_lt in CLT.
      pose proof (KnownA.TwinB.KnownA.known_leu_q_sound E _ _ _ HF CLEN) as LEN. cbn [den] in LEN. rewrite wbv_unsigned, wlit_ok in LEN.
      assert (HS0 : 0 <= hs) by (rewrite <- (zero_view_hi E r hs ZV); unfold hiZ; pose proof (bv_unsigned_in_range 64 (den E (rg_hi r))) as X; lia).
      rewrite Uint63.of_Z_spec in LEN. rewrite Z.mod_small in LEN by (rewrite wB_two63, two63_eq; clear - CLT HS0 RO1; Z.div_mod_to_equations; lia).
      exists hs, n, sh, len. split; [reflexivity|]. split; [reflexivity|]. split; [left; exists kb, o1; split; [exact UB| exact TW]|]. split; [exact WL|]. rewrite SH, SA. clear - K8 U L CLO CLH LEN RO1 RO2 R1. Z.div_mod_to_equations. lia.
    +
      right. left. unfold view_TR in TR. apply existsb_exists in TR as (e0 & _ & TR). set (sh := fst (fst e0)) in *. unfold view_TR1 in TR.
      destruct (CtrA.win_lookup wl sh) as [[len kd]|] eqn:WL; [|discriminate]. destruct (IMap.find sh (s_regs st)) as [rsh|] eqn:Fsh; [|discriminate].
      destruct (block_of_twin (s_facts st) sh) as [kB|] eqn:BTs; [|discriminate].
      destruct (rg_hi rsh) as [| |op x c3v| | | | | | | |] eqn:EHI; try discriminate. destruct op; try discriminate.
      destruct x as [| |op2 a b| | | | | | | |]; try discriminate. destruct op2; try discriminate.
      destruct a as [|n' oA| | | | | | | | |]; try discriminate. destruct b as [|k' z| | | | | | | | |]; try discriminate.
      destruct c3v as [c3| | | | | | | | | |]; try discriminate.
      apply andb_prop in TR as [TR VHI]. apply andb_prop in TR as [TR LBO]. apply andb_prop in TR as [TR NWA]. apply andb_prop in TR as [TR ALK].
      apply andb_prop in TR as [TR C8]. apply andb_prop in TR as [TR CLH]. apply andb_prop in TR as [TR CLO]. apply andb_prop in TR as [TR LO0].
      apply andb_prop in TR as [TR WTA]. apply andb_prop in TR as [TR KB]. apply andb_prop in TR as [KD HN].
      apply weqb_eq in KD. subst kd. apply Uint63.eqb_correct in KB. subst k'. apply Uint63.eqb_correct in LO0. apply negb_true_iff in WTA.
      apply Z.leb_le in C8. apply Z.leb_le in CLH. apply Z.leb_le in CLO.
      pose proof HN as HN0. unfold hi_names in HN0. rewrite EHI in HN0. apply andb_prop in HN0 as [HN0 C3]. apply andb_prop in HN0 as [NN Z0].
      apply Uint63.eqb_correct in NN. apply weqb_eq in Z0. apply weqb_eq in C3. subst n' z c3.
      destruct (find_lb_to (s_facts st) n kB) as [o2|] eqn:LB; [|discriminate LBO]. apply andb_prop in LBO as [WT2 NW2]. apply negb_true_iff in WT2.
      pose proof (GTwinSub.GTwinSub.mod8_of_align E _ kB HF ALK) as K8.
      pose proof (GTwinSub.GTwinSub.mod8_of_align E _ n HF AL) as N8. fold N in N8.
      destruct (nowrap_kb_sound E _ HF n oA NWA) as [RA DA]. destruct (nowrap_kb_sound E _ HF kB o2 NW2) as [R2 D2].
      pose proof (CallA.TwinB.find_lb_to_holds E _ n kB o2 HF LB) as L. rewrite D2 in L. fold N in L, RA, DA.
      assert (OA : w2Zs oA = w2Z oA) by (rewrite w2Zs_eq; rewrite WTA; lia).
      assert (O2 : w2Zs o2 = w2Z o2) by (rewrite w2Zs_eq; rewrite WT2; lia).
      rewrite OA in *. rewrite O2 in *.
      pose proof (view_anchor E _ sh kB HF BTs) as SH. set (K := bv_unsigned (ev E kB)) in *.
      pose proof (w2Z_range oA) as ROA. pose proof (w2Z_range o2) as RO2.
      pose proof (CallA.TwinB.vec_hi_in_sound E _ _ len HF VHI) as VH. rewrite <- EHI in VH.

      assert (HV : bv_unsigned (den E (rg_hi rsh)) = (N + w2Z oA - K) / 8).
      { rewrite EHI. cbn [den]. unfold alu64, alu. rewrite bv_shiftr_unsigned, bv_and_unsigned, bv_sub_unsigned.
        replace (bv_unsigned (wbv (wlit 3%uint63))) with 3 by (vm_compute; reflexivity).
        replace (bv_unsigned (Z_to_bv 64 63)) with 63 by (vm_compute; reflexivity).
        change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
        change (bv_add (ev E n) (wbv oA)) with (den E (VP n oA)). rewrite DA.
        change (bv_add (ev E kB) (wbv wzero)) with (den E (VP kB wzero)). rewrite (HeapCtr.TwinB.den_VPz E kB). fold K.
        unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
        pose proof (bv_unsigned_in_range 64 (ev E kB)) as RKK. unfold bv_modulus in RKK. change (2 ^ Z.of_N 64) with (2 ^ 64) in RKK. fold K in RKK.
        unfold two64 in *. rewrite Z.mod_small by lia. reflexivity. }
      rewrite HV in VH.
      exists hs, n, sh, len. split; [reflexivity|]. split; [reflexivity|]. split; [right; exists rsh; split; [exact Fsh| exact HN]|]. split; [exact WL|].
      rewrite SH, SA. clear - K8 N8 L C8 CLO CLH VH RO2 ROA. Z.div_mod_to_equations. lia.
    +
      left. unfold view_T2 in T2. destruct (IMap.find n (s_regs st)) as [rn|] eqn:Fn; [|discriminate].
      destruct (lit_hi rn) as [hn|] eqn:LH; [|discriminate]. apply andb_prop in T2 as [T2 SJ]. apply andb_prop in T2 as [T2 C2]. apply andb_prop in T2 as [_ C1].
      apply Z.leb_le in C1. apply Z.leb_le in C2.
      destruct (stack_side_just_sound segs OPS E st ms mo ks n rn HS Fn N0 SJ) as [SIDE TOP]. rewrite (lit_hi_sound E rn hn LH) in TOP. fold N in TOP, SIDE.
      split; [exists hs; reflexivity|]. exists (N + loZ rn), (N + hn). split; [| split; [exact TOP|]].
      * intros a Ha. exists (N + 8 * (a - S)). unfold loZ. split; [lia|]. rewrite SHZ. lia.
      * destruct SIDE as [->|SIDE]; [right; left; exists rn; split; [exact Fn| reflexivity]| right; right; exact SIDE].
  -
    right. right. left. split; [exact J|]. unfold view_I in J. destruct (ro_lit_hi r) as [hs|] eqn:RL; [|discriminate]. destruct (find_pin (s_facts st) k) as [a|] eqn:FP; [|discriminate].
    apply andb_prop in J as [_ IM]. unfold in_imgsh in IM. apply andb_prop in IM as [IM _]. apply existsb_exists in IM as (v & Hv & C).
    apply andb_prop in C as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2.
    rewrite (ro_lit_hi_sound E r hs RL). rewrite (find_pin_sound E _ k a HF FP). unfold loZ. exists v. split; [exact Hv| split; assumption].
Qed.

Lemma wlo_floor : forall E st hargs n md A nw rest LB ceil wlo,
  find_op HEAP_ID (s_ops st) = Some hargs -> hargs = VL md :: A :: VL nw :: rest -> wt nw = false -> n = Z.to_nat (to_Z (wl nw)) ->
  (3 * n <= length rest)%nat -> HeapOp.windows_wf (wins_of E n rest) LB ceil -> stack_wlo st = Some wlo ->
  ceil <= bv_unsigned (den E (VP STACK_ID wlo)).
Proof.
  intros E st hargs n md A nw rest LB ceil wlo Hf Eh Tnw Nn Ln WF H. unfold stack_wlo in H. rewrite Hf in H.
  assert (HN : heap_nwin hargs = Some n).
  { rewrite Eh. unfold heap_nwin. rewrite Tnw. rewrite <- Nn. destruct (Nat.leb_spec (3 * n) (length rest)); [reflexivity| lia]. }
  rewrite HN in H. rewrite Eh in H. destruct (stack_window_key n rest) as [w|] eqn:SK; [|discriminate].
  destruct (nowrap_kb (s_facts st) STACK_ID w); [|discriminate]. injection H as <-.
  destruct (stack_window_key_In E n rest w SK) as (len & INW).
  pose proof (proj1 (Forall_forall _ _) WF _ INW) as (_ & _ & _ & [[_ C]|[[K _]|[K _]]]); cbn [HeapOp.w_kind HeapOp.w_lo] in *; [exact C| |];
    unfold HeapOp.K_STACK, HeapOp.K_BLOCK, HeapOp.K_SUB in K; lia.
Qed.

End CallV.
End TwinB.
