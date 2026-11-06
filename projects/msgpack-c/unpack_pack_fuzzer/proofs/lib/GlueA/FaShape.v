(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan W64Proofs ValProofs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require HeapCtr HeapCtrB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import ActrB FaC.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib HeapOp CtrFX.
Open Scope Z_scope.
Unset Lia Cache.

Definition ZCB : Z := 2 ^ 47.

Definition not_cr (w : window) : Prop := ~ (w_kind w = K_STACK /\ w_len w = 0 /\ ZCB <= w_lo w < 2 ^ 47 + 2 ^ 46).

Lemma in_band_spec : forall a, FaC.in_band a = true <-> ZCB <= w2Z a < 2 ^ 47 + 2 ^ 46.
Proof.
  intros a. unfold FaC.in_band. rewrite andb_true_iff, !ValP.wleu_w2Z, !Z.leb_le.
  change (w2Z ActrB.ZC_BASE) with (2 ^ 47). change (w2Z FaC.ZC_TOP) with (2 ^ 47 + 2 ^ 46 - 1). unfold ZCB. lia.
Qed.

Lemma band_dec_sound : forall E0 fs l b, facts_hold E0 fs -> FaC.band_dec fs l = Some b ->
  if b then ZCB <= bv_unsigned (den E0 l) < 2 ^ 47 + 2 ^ 46 else ~ (ZCB <= bv_unsigned (den E0 l) < 2 ^ 47 + 2 ^ 46).
Proof.
  intros E0 fs l b HF H. unfold FaC.band_dec in H.
  assert (SYM : (if known_leu fs (VL ActrB.ZC_BASE) l && known_leu fs l (VL FaC.ZC_TOP) then Some true
                 else if known_ltu fs l (VL ActrB.ZC_BASE) || known_ltu fs (VL FaC.ZC_TOP) l then Some false else None) = Some b ->
                if b then ZCB <= bv_unsigned (den E0 l) < 2 ^ 47 + 2 ^ 46 else ~ (ZCB <= bv_unsigned (den E0 l) < 2 ^ 47 + 2 ^ 46)).
  { clear H. intros H. destruct (known_leu fs (VL ActrB.ZC_BASE) l && known_leu fs l (VL FaC.ZC_TOP)) eqn:IN.
    - injection H as <-. apply andb_prop in IN as [I1 I2].
      pose proof (HeapCtr.known_leu_sound E0 fs _ _ HF I1) as Q1. pose proof (HeapCtr.known_leu_sound E0 fs _ _ HF I2) as Q2.
      rewrite unsigned_VL in Q1, Q2. change (w2Z ActrB.ZC_BASE) with (2 ^ 47) in Q1. change (w2Z FaC.ZC_TOP) with (2 ^ 47 + 2 ^ 46 - 1) in Q2. unfold ZCB. lia.
    - destruct (known_ltu fs l (VL ActrB.ZC_BASE) || known_ltu fs (VL FaC.ZC_TOP) l) eqn:OUT; [|discriminate H]. injection H as <-.
      apply orb_prop in OUT as [O|O]; pose proof (HeapCtr.known_ltu_sound E0 fs _ _ HF O) as Q; rewrite unsigned_VL in Q;
        [change (w2Z ActrB.ZC_BASE) with (2 ^ 47) in Q| change (w2Z FaC.ZC_TOP) with (2 ^ 47 + 2 ^ 46 - 1) in Q]; unfold ZCB; lia. }
  destruct l as [a| | | | | | | | | |]; try exact (SYM H).
  injection H as <-. rewrite unsigned_VL. destruct (FaC.in_band a) eqn:IB.
  - apply in_band_spec. exact IB.
  - intros X. apply (proj2 (in_band_spec a)) in X. congruence.
Qed.

Lemma triple_not_cr : forall E0 fs (l sz : sv) (k0 : w64), facts_hold E0 fs ->
  (if weqb k0 wzero then match sz with VL z => if weqb z wzero then match FaC.band_dec fs l with Some false => true | _ => false end else true | _ => false end else true) = true ->
  not_cr (Win (bv_unsigned (den E0 l)) (bv_unsigned (den E0 sz)) (bv_unsigned (den E0 (VL k0)))).
Proof.
  intros E0 fs l sz k0 HF H [K [Z0 B]]. cbn [w_kind w_len w_lo] in K, Z0, B. rewrite unsigned_VL in K. change K_STACK with (w2Z wzero) in K.
  assert (KW : weqb k0 wzero = true) by (rewrite weqb_eqb; apply Z.eqb_eq; exact K). rewrite KW in H.
  destruct sz as [z| | | | | | | | | |]; try discriminate H. rewrite unsigned_VL in Z0.
  assert (ZW : weqb z wzero = true) by (rewrite weqb_eqb; apply Z.eqb_eq; exact Z0). rewrite ZW in H.
  destruct (FaC.band_dec fs l) as [[|]|] eqn:BD; try discriminate H.
  exact (band_dec_sound E0 fs l false HF BD B).
Qed.

Lemma cr_free_sound : forall E0 fs, facts_hold E0 fs -> forall m ws, FaC.cr_free fs m ws = true -> forall w, In w (wins_of E0 m ws) -> not_cr w.
Proof.
  intros E0 fs HF m. induction m as [|m IH]; intros ws H w Hw; [destruct Hw|].
  destruct ws as [|wlo [|ln [|kdv ws0]]]; try (cbn in Hw; contradiction). cbn [FaC.cr_free] in H.
  destruct kdv as [kw| | | | | | | | | |]; try discriminate H. apply andb_prop in H as [H1 H2].
  rewrite wins_of_cons in Hw. destruct Hw as [<-|Hw]; [| exact (IH ws0 H2 w Hw)].
  exact (triple_not_cr E0 fs wlo ln kw HF H1).
Qed.

Lemma pay_split : forall E0 fs c m ws ws' wl, facts_hold E0 fs ->
  FaC.pay fs c m ws = Some ws' -> DefsA.CtrA.nonstack_windows m ws = Some wl -> (3 * m <= length ws)%nat ->
  exists l1 az l2 lsv,
       wins_of E0 m ws = l1 ++ Win az 0 K_STACK :: l2
    /\ wins_of E0 m ws' = l1 ++ Win (az - to_Z c) 0 K_STACK :: l2
    /\ ZCB + to_Z c <= az < 2 ^ 47 + 2 ^ 46
    /\ (forall w, In w (l1 ++ l2) -> not_cr w)
    /\ length ws' = length ws
    /\ DefsA.CtrA.nonstack_windows m ws' = Some wl
    /\ In lsv ws
    /\ (forall x, In x ws' -> In x ws \/ x = sv_alu ALU_SUB lsv (VL (wlit c))).
Proof.
  intros E0 fs c m ws ws' wl HF. revert ws ws' wl. induction m as [|m IH]; intros ws ws' wl H N L; [cbn in H; destruct ws; discriminate|].
  destruct ws as [|wlo [|ln [|kdv ws0]]]; try (cbn in H; discriminate). cbn [FaC.pay] in H. cbn [DefsA.CtrA.nonstack_windows] in N. cbn [length] in L |- *.
  destruct kdv as [kw| | | | | | | | | |]; try discriminate N.
  destruct (DefsA.CtrA.nonstack_windows m ws0) as [l|] eqn:NW; [|discriminate N].
  assert (REC : forall ws2, FaC.pay fs c m ws0 = Some ws2 -> Some (wlo :: ln :: VL kw :: ws2) = Some ws' ->
            not_cr (Win (bv_unsigned (den E0 wlo)) (bv_unsigned (den E0 ln)) (bv_unsigned (den E0 (VL kw)))) ->
            exists l1 az l2 lsv,
                 wins_of E0 (S m) (wlo :: ln :: VL kw :: ws0) = l1 ++ Win az 0 K_STACK :: l2
              /\ wins_of E0 (S m) ws' = l1 ++ Win (az - to_Z c) 0 K_STACK :: l2
              /\ ZCB + to_Z c <= az < 2 ^ 47 + 2 ^ 46
              /\ (forall w, In w (l1 ++ l2) -> not_cr w)
              /\ length ws' = S (S (S (length ws0)))
              /\ DefsA.CtrA.nonstack_windows (S m) ws' = Some wl
              /\ In lsv (wlo :: ln :: VL kw :: ws0)
              /\ (forall x, In x ws' -> In x (wlo :: ln :: VL kw :: ws0) \/ x = sv_alu ALU_SUB lsv (VL (wlit c)))).
  { intros ws2 P EQ NZ. injection EQ as <-.
    destruct (IH ws0 ws2 l P NW ltac:(lia)) as (l1 & az & l2 & lsv & W1 & W2 & RA & NZL & LEN & NW2 & INL & SUB).
    exists (Win (bv_unsigned (den E0 wlo)) (bv_unsigned (den E0 ln)) (bv_unsigned (den E0 (VL kw))) :: l1), az, l2, lsv.
    rewrite !wins_of_cons, W1, W2. cbn [app]. split; [reflexivity|]. split; [reflexivity|]. split; [exact RA|].
    split; [intros w [<-|Hw]; [exact NZ| exact (NZL w Hw)]|].
    cbn [length]. split; [lia|]. split; [cbn [DefsA.CtrA.nonstack_windows]; rewrite NW2; exact N|].
    split; [do 3 right; exact INL|].
    intros x [Hx|[Hx|[Hx|Hx]]]; [left; left; exact Hx| left; right; left; exact Hx| left; right; right; left; exact Hx|].
    destruct (SUB x Hx) as [X|X]; [left; do 3 right; exact X| right; exact X]. }
  destruct (weqb kw wzero) eqn:KW.
  - destruct ln as [z| | | | | | | | | |]; try discriminate H.
    destruct (weqb z wzero) eqn:ZW.
    + destruct (FaC.band_dec fs wlo) as [[|]|] eqn:BD; [| | discriminate H].
      * match type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:C; [|discriminate H] end. injection H as <-.
        apply andb_prop in C as [C2 ZLF]. pose proof (band_dec_sound E0 fs wlo true HF BD) as IB. cbv iota in IB.
        apply ValP.weqb_eq in KW, ZW. subst kw z.
        pose proof (HeapCtr.known_leu_sound E0 fs _ _ HF C2) as Q2. rewrite unsigned_VL in Q2.
        rewrite wadd_ok, wlit_ok in Q2. change (w2Z ActrB.ZC_BASE) with (2 ^ 47) in Q2.
        pose proof (to_Z_bounded c) as CB. rewrite wB_two63, two63_eq in CB.
        rewrite Z.mod_small in Q2 by (unfold two64; lia).
        set (az := bv_unsigned (den E0 wlo)) in *.
        assert (ES : bv_unsigned (den E0 (sv_alu ALU_SUB wlo (VL (wlit c)))) = az - to_Z c).
        { rewrite (ValP.den_sv_alu E0). change (alu64 ALU_SUB (den E0 wlo) (den E0 (VL (wlit c)))) with (bv_sub (den E0 wlo) (den E0 (VL (wlit c)))).
          rewrite bv_sub_unsigned, unsigned_VL, wlit_ok. fold az. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
          apply Z.mod_small. unfold ZCB in *. lia. }
        exists [], az, (wins_of E0 m ws0), wlo. rewrite !wins_of_cons, !unsigned_VL, ES. change (w2Z wzero) with 0. cbn [app].
        split; [reflexivity|]. split; [reflexivity|]. split; [unfold ZCB in *; lia|].
        split; [exact (cr_free_sound E0 fs HF m ws0 ZLF)|]. cbn [length]. split; [reflexivity|].
        split; [cbn [DefsA.CtrA.nonstack_windows]; rewrite NW; exact N|].
        split; [left; reflexivity|].
        intros x [Hx|Hx]; [right; symmetry; exact Hx| left; right; exact Hx].
      * destruct (FaC.pay fs c m ws0) as [ws2|] eqn:P; [| discriminate H]. apply (REC ws2 eq_refl H).
        apply (triple_not_cr E0 fs _ _ _ HF). rewrite KW, ZW, BD. reflexivity.
    + destruct (FaC.pay fs c m ws0) as [ws2|] eqn:P; [| discriminate H]. apply (REC ws2 eq_refl H).
      apply (triple_not_cr E0 fs _ _ _ HF). rewrite KW, ZW. reflexivity.
  - destruct (FaC.pay fs c m ws0) as [ws2|] eqn:P; [| discriminate H]. apply (REC ws2 eq_refl H).
    apply (triple_not_cr E0 fs _ _ _ HF). rewrite KW. reflexivity.
Qed.

Lemma heap_pay_facts : forall E0 fs md A nw rest n c h' wnl, facts_hold E0 fs ->
  wt nw = false -> n = Z.to_nat (to_Z (wl nw)) -> (3 * n <= length rest)%nat ->
  DefsA.CtrA.nonstack_windows n rest = Some wnl ->
  FaC.heap_pay fs (VL md :: A :: VL nw :: rest) c = Some h' ->
  exists ws' l1 az l2 lsv,
    h' = VL md :: A :: VL nw :: ws' ++ skipn (3 * n) rest
    /\ wins_of E0 n rest = l1 ++ Win az 0 K_STACK :: l2
    /\ wins_of E0 n (ws' ++ skipn (3 * n) rest) = l1 ++ Win (az - to_Z c) 0 K_STACK :: l2
    /\ ZCB + to_Z c <= az < 2 ^ 47 + 2 ^ 46
    /\ (forall w, In w (l1 ++ l2) -> not_cr w)
    /\ (3 * n <= length (ws' ++ skipn (3 * n) rest))%nat
    /\ skipn (3 * n) (ws' ++ skipn (3 * n) rest) = skipn (3 * n) rest
    /\ DefsA.CtrA.nonstack_windows n (ws' ++ skipn (3 * n) rest) = Some wnl
    /\ In lsv rest
    /\ (forall x, In x (ws' ++ skipn (3 * n) rest) -> In x rest \/ x = sv_alu ALU_SUB lsv (VL (wlit c))).
Proof.
  intros E0 fs md A nw rest n c h' wnl HF T N L NW H. unfold FaC.heap_pay in H.
  assert (HN : heap_nwin (VL md :: A :: VL nw :: rest) = Some n).
  { unfold heap_nwin. rewrite T, <- N. destruct (Nat.leb_spec (3 * n) (length rest)); [reflexivity| lia]. }
  rewrite HN in H. destruct (FaC.pay fs c n (firstn (3 * n) rest)) as [ws'|] eqn:D; [|discriminate]. injection H as <-.
  assert (NWf : DefsA.CtrA.nonstack_windows n (firstn (3 * n) rest) = Some wnl) by (rewrite HeapCtrB.nonstack_windows_firstn; exact NW).
  destruct (pay_split E0 fs c n (firstn (3 * n) rest) ws' wnl HF D NWf ltac:(rewrite firstn_length_le by lia; lia))
    as (l1 & az & l2 & lsv & W1 & W2 & RA & NZL & LEN & NW' & INL & SUB).
  rewrite firstn_length_le in LEN by lia.
  exists ws', l1, az, l2, lsv. split; [reflexivity|].
  split; [rewrite <- W1; rewrite <- (CtrFX.wins_of_firstn E0 n rest [] L), app_nil_r; reflexivity|].
  split; [rewrite <- W2; apply HeapCtrB.wins_of_prefix; lia|].
  split; [exact RA|]. split; [exact NZL|]. split; [rewrite length_app; lia|].
  split. { rewrite skipn_app, LEN, Nat.sub_diag. cbn [skipn]. rewrite skipn_all2 by lia. reflexivity. }
  split.
  { rewrite <- NW'. rewrite <- (HeapCtrB.nonstack_windows_firstn n (ws' ++ skipn (3 * n) rest)). f_equal.
    rewrite firstn_app, LEN, Nat.sub_diag. cbn [firstn]. rewrite app_nil_r. apply firstn_all2. lia. }
  split; [rewrite <- (firstn_skipn (3 * n) rest); apply in_or_app; left; exact INL|].
  intros x Hx. apply in_app_or in Hx as [Hx|Hx].
  - destruct (SUB x Hx) as [X|X]; [left; rewrite <- (firstn_skipn (3 * n) rest); apply in_or_app; left; exact X | right; exact X].
  - left. rewrite <- (firstn_skipn (3 * n) rest). apply in_or_app. right. exact Hx.
Qed.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.
Import Actr.TwinB.
Import ActrB.TwinB FaC.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib HeapOp CtrFX.
Open Scope Z_scope.
Unset Lia Cache.

Definition ZCB : Z := 2 ^ 47.

Definition not_cr (w : window) : Prop := ~ (w_kind w = K_STACK /\ w_len w = 0 /\ ZCB <= w_lo w < 2 ^ 47 + 2 ^ 46).

Lemma in_band_spec : forall a, FaC.TwinB.FaC.in_band a = true <-> ZCB <= w2Z a < 2 ^ 47 + 2 ^ 46.
Proof.
  intros a. unfold FaC.TwinB.FaC.in_band. rewrite andb_true_iff, !ValP.wleu_w2Z, !Z.leb_le.
  change (w2Z ActrB.TwinB.ActrB.ZC_BASE) with (2 ^ 47). change (w2Z FaC.TwinB.FaC.ZC_TOP) with (2 ^ 47 + 2 ^ 46 - 1). unfold ZCB. lia.
Qed.

Lemma band_dec_sound : forall E0 fs l b, facts_hold E0 fs -> FaC.TwinB.FaC.band_dec fs l = Some b ->
  if b then ZCB <= bv_unsigned (den E0 l) < 2 ^ 47 + 2 ^ 46 else ~ (ZCB <= bv_unsigned (den E0 l) < 2 ^ 47 + 2 ^ 46).
Proof.
  intros E0 fs l b HF H. unfold FaC.TwinB.FaC.band_dec in H.
  assert (SYM : (if known_leu fs (VL ActrB.TwinB.ActrB.ZC_BASE) l && known_leu fs l (VL FaC.TwinB.FaC.ZC_TOP) then Some true
                 else if known_ltu fs l (VL ActrB.TwinB.ActrB.ZC_BASE) || known_ltu fs (VL FaC.TwinB.FaC.ZC_TOP) l then Some false else None) = Some b ->
                if b then ZCB <= bv_unsigned (den E0 l) < 2 ^ 47 + 2 ^ 46 else ~ (ZCB <= bv_unsigned (den E0 l) < 2 ^ 47 + 2 ^ 46)).
  { clear H. intros H. destruct (known_leu fs (VL ActrB.TwinB.ActrB.ZC_BASE) l && known_leu fs l (VL FaC.TwinB.FaC.ZC_TOP)) eqn:IN.
    - injection H as <-. apply andb_prop in IN as [I1 I2].
      pose proof (HeapCtr.TwinB.known_leu_sound E0 fs _ _ HF I1) as Q1. pose proof (HeapCtr.TwinB.known_leu_sound E0 fs _ _ HF I2) as Q2.
      rewrite unsigned_VL in Q1, Q2. change (w2Z ActrB.TwinB.ActrB.ZC_BASE) with (2 ^ 47) in Q1. change (w2Z FaC.TwinB.FaC.ZC_TOP) with (2 ^ 47 + 2 ^ 46 - 1) in Q2. unfold ZCB. lia.
    - destruct (known_ltu fs l (VL ActrB.TwinB.ActrB.ZC_BASE) || known_ltu fs (VL FaC.TwinB.FaC.ZC_TOP) l) eqn:OUT; [|discriminate H]. injection H as <-.
      apply orb_prop in OUT as [O|O]; pose proof (HeapCtr.TwinB.known_ltu_sound E0 fs _ _ HF O) as Q; rewrite unsigned_VL in Q;
        [change (w2Z ActrB.TwinB.ActrB.ZC_BASE) with (2 ^ 47) in Q| change (w2Z FaC.TwinB.FaC.ZC_TOP) with (2 ^ 47 + 2 ^ 46 - 1) in Q]; unfold ZCB; lia. }
  destruct l as [a| | | | | | | | | |]; try exact (SYM H).
  injection H as <-. rewrite unsigned_VL. destruct (FaC.TwinB.FaC.in_band a) eqn:IB.
  - apply in_band_spec. exact IB.
  - intros X. apply (proj2 (in_band_spec a)) in X. congruence.
Qed.

Lemma triple_not_cr : forall E0 fs (l sz : sv) (k0 : w64), facts_hold E0 fs ->
  (if weqb k0 wzero then match sz with VL z => if weqb z wzero then match FaC.TwinB.FaC.band_dec fs l with Some false => true | _ => false end else true | _ => false end else true) = true ->
  not_cr (Win (bv_unsigned (den E0 l)) (bv_unsigned (den E0 sz)) (bv_unsigned (den E0 (VL k0)))).
Proof.
  intros E0 fs l sz k0 HF H [K [Z0 B]]. cbn [w_kind w_len w_lo] in K, Z0, B. rewrite unsigned_VL in K. change K_STACK with (w2Z wzero) in K.
  assert (KW : weqb k0 wzero = true) by (rewrite weqb_eqb; apply Z.eqb_eq; exact K). rewrite KW in H.
  destruct sz as [z| | | | | | | | | |]; try discriminate H. rewrite unsigned_VL in Z0.
  assert (ZW : weqb z wzero = true) by (rewrite weqb_eqb; apply Z.eqb_eq; exact Z0). rewrite ZW in H.
  destruct (FaC.TwinB.FaC.band_dec fs l) as [[|]|] eqn:BD; try discriminate H.
  exact (band_dec_sound E0 fs l false HF BD B).
Qed.

Lemma cr_free_sound : forall E0 fs, facts_hold E0 fs -> forall m ws, FaC.TwinB.FaC.cr_free fs m ws = true -> forall w, In w (wins_of E0 m ws) -> not_cr w.
Proof.
  intros E0 fs HF m. induction m as [|m IH]; intros ws H w Hw; [destruct Hw|].
  destruct ws as [|wlo [|ln [|kdv ws0]]]; try (cbn in Hw; contradiction). cbn [FaC.TwinB.FaC.cr_free] in H.
  destruct kdv as [kw| | | | | | | | | |]; try discriminate H. apply andb_prop in H as [H1 H2].
  rewrite wins_of_cons in Hw. destruct Hw as [<-|Hw]; [| exact (IH ws0 H2 w Hw)].
  exact (triple_not_cr E0 fs wlo ln kw HF H1).
Qed.

Lemma pay_split : forall E0 fs c m ws ws' wl, facts_hold E0 fs ->
  FaC.TwinB.FaC.pay fs c m ws = Some ws' -> DefsA.CtrA.nonstack_windows m ws = Some wl -> (3 * m <= length ws)%nat ->
  exists l1 az l2 lsv,
       wins_of E0 m ws = l1 ++ Win az 0 K_STACK :: l2
    /\ wins_of E0 m ws' = l1 ++ Win (az - to_Z c) 0 K_STACK :: l2
    /\ ZCB + to_Z c <= az < 2 ^ 47 + 2 ^ 46
    /\ (forall w, In w (l1 ++ l2) -> not_cr w)
    /\ length ws' = length ws
    /\ DefsA.CtrA.nonstack_windows m ws' = Some wl
    /\ In lsv ws
    /\ (forall x, In x ws' -> In x ws \/ x = sv_alu ALU_SUB lsv (VL (wlit c))).
Proof.
  intros E0 fs c m ws ws' wl HF. revert ws ws' wl. induction m as [|m IH]; intros ws ws' wl H N L; [cbn in H; destruct ws; discriminate|].
  destruct ws as [|wlo [|ln [|kdv ws0]]]; try (cbn in H; discriminate). cbn [FaC.TwinB.FaC.pay] in H. cbn [DefsA.CtrA.nonstack_windows] in N. cbn [length] in L |- *.
  destruct kdv as [kw| | | | | | | | | |]; try discriminate N.
  destruct (DefsA.CtrA.nonstack_windows m ws0) as [l|] eqn:NW; [|discriminate N].
  assert (REC : forall ws2, FaC.TwinB.FaC.pay fs c m ws0 = Some ws2 -> Some (wlo :: ln :: VL kw :: ws2) = Some ws' ->
            not_cr (Win (bv_unsigned (den E0 wlo)) (bv_unsigned (den E0 ln)) (bv_unsigned (den E0 (VL kw)))) ->
            exists l1 az l2 lsv,
                 wins_of E0 (S m) (wlo :: ln :: VL kw :: ws0) = l1 ++ Win az 0 K_STACK :: l2
              /\ wins_of E0 (S m) ws' = l1 ++ Win (az - to_Z c) 0 K_STACK :: l2
              /\ ZCB + to_Z c <= az < 2 ^ 47 + 2 ^ 46
              /\ (forall w, In w (l1 ++ l2) -> not_cr w)
              /\ length ws' = S (S (S (length ws0)))
              /\ DefsA.CtrA.nonstack_windows (S m) ws' = Some wl
              /\ In lsv (wlo :: ln :: VL kw :: ws0)
              /\ (forall x, In x ws' -> In x (wlo :: ln :: VL kw :: ws0) \/ x = sv_alu ALU_SUB lsv (VL (wlit c)))).
  { intros ws2 P EQ NZ. injection EQ as <-.
    destruct (IH ws0 ws2 l P NW ltac:(lia)) as (l1 & az & l2 & lsv & W1 & W2 & RA & NZL & LEN & NW2 & INL & SUB).
    exists (Win (bv_unsigned (den E0 wlo)) (bv_unsigned (den E0 ln)) (bv_unsigned (den E0 (VL kw))) :: l1), az, l2, lsv.
    rewrite !wins_of_cons, W1, W2. cbn [app]. split; [reflexivity|]. split; [reflexivity|]. split; [exact RA|].
    split; [intros w [<-|Hw]; [exact NZ| exact (NZL w Hw)]|].
    cbn [length]. split; [lia|]. split; [cbn [DefsA.CtrA.nonstack_windows]; rewrite NW2; exact N|].
    split; [do 3 right; exact INL|].
    intros x [Hx|[Hx|[Hx|Hx]]]; [left; left; exact Hx| left; right; left; exact Hx| left; right; right; left; exact Hx|].
    destruct (SUB x Hx) as [X|X]; [left; do 3 right; exact X| right; exact X]. }
  destruct (weqb kw wzero) eqn:KW.
  - destruct ln as [z| | | | | | | | | |]; try discriminate H.
    destruct (weqb z wzero) eqn:ZW.
    + destruct (FaC.TwinB.FaC.band_dec fs wlo) as [[|]|] eqn:BD; [| | discriminate H].
      * match type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:C; [|discriminate H] end. injection H as <-.
        apply andb_prop in C as [C2 ZLF]. pose proof (band_dec_sound E0 fs wlo true HF BD) as IB. cbv iota in IB.
        apply ValP.weqb_eq in KW, ZW. subst kw z.
        pose proof (HeapCtr.TwinB.known_leu_sound E0 fs _ _ HF C2) as Q2. rewrite unsigned_VL in Q2.
        rewrite wadd_ok, wlit_ok in Q2. change (w2Z ActrB.TwinB.ActrB.ZC_BASE) with (2 ^ 47) in Q2.
        pose proof (to_Z_bounded c) as CB. rewrite wB_two63, two63_eq in CB.
        rewrite Z.mod_small in Q2 by (unfold two64; lia).
        set (az := bv_unsigned (den E0 wlo)) in *.
        assert (ES : bv_unsigned (den E0 (sv_alu ALU_SUB wlo (VL (wlit c)))) = az - to_Z c).
        { rewrite (ValP.den_sv_alu E0). change (alu64 ALU_SUB (den E0 wlo) (den E0 (VL (wlit c)))) with (bv_sub (den E0 wlo) (den E0 (VL (wlit c)))).
          rewrite bv_sub_unsigned, unsigned_VL, wlit_ok. fold az. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
          apply Z.mod_small. unfold ZCB in *. lia. }
        exists [], az, (wins_of E0 m ws0), wlo. rewrite !wins_of_cons, !unsigned_VL, ES. change (w2Z wzero) with 0. cbn [app].
        split; [reflexivity|]. split; [reflexivity|]. split; [unfold ZCB in *; lia|].
        split; [exact (cr_free_sound E0 fs HF m ws0 ZLF)|]. cbn [length]. split; [reflexivity|].
        split; [cbn [DefsA.CtrA.nonstack_windows]; rewrite NW; exact N|].
        split; [left; reflexivity|].
        intros x [Hx|Hx]; [right; symmetry; exact Hx| left; right; exact Hx].
      * destruct (FaC.TwinB.FaC.pay fs c m ws0) as [ws2|] eqn:P; [| discriminate H]. apply (REC ws2 eq_refl H).
        apply (triple_not_cr E0 fs _ _ _ HF). rewrite KW, ZW, BD. reflexivity.
    + destruct (FaC.TwinB.FaC.pay fs c m ws0) as [ws2|] eqn:P; [| discriminate H]. apply (REC ws2 eq_refl H).
      apply (triple_not_cr E0 fs _ _ _ HF). rewrite KW, ZW. reflexivity.
  - destruct (FaC.TwinB.FaC.pay fs c m ws0) as [ws2|] eqn:P; [| discriminate H]. apply (REC ws2 eq_refl H).
    apply (triple_not_cr E0 fs _ _ _ HF). rewrite KW. reflexivity.
Qed.

Lemma heap_pay_facts : forall E0 fs md A nw rest n c h' wnl, facts_hold E0 fs ->
  wt nw = false -> n = Z.to_nat (to_Z (wl nw)) -> (3 * n <= length rest)%nat ->
  DefsA.CtrA.nonstack_windows n rest = Some wnl ->
  FaC.TwinB.FaC.heap_pay fs (VL md :: A :: VL nw :: rest) c = Some h' ->
  exists ws' l1 az l2 lsv,
    h' = VL md :: A :: VL nw :: ws' ++ skipn (3 * n) rest
    /\ wins_of E0 n rest = l1 ++ Win az 0 K_STACK :: l2
    /\ wins_of E0 n (ws' ++ skipn (3 * n) rest) = l1 ++ Win (az - to_Z c) 0 K_STACK :: l2
    /\ ZCB + to_Z c <= az < 2 ^ 47 + 2 ^ 46
    /\ (forall w, In w (l1 ++ l2) -> not_cr w)
    /\ (3 * n <= length (ws' ++ skipn (3 * n) rest))%nat
    /\ skipn (3 * n) (ws' ++ skipn (3 * n) rest) = skipn (3 * n) rest
    /\ DefsA.CtrA.nonstack_windows n (ws' ++ skipn (3 * n) rest) = Some wnl
    /\ In lsv rest
    /\ (forall x, In x (ws' ++ skipn (3 * n) rest) -> In x rest \/ x = sv_alu ALU_SUB lsv (VL (wlit c))).
Proof.
  intros E0 fs md A nw rest n c h' wnl HF T N L NW H. unfold FaC.TwinB.FaC.heap_pay in H.
  assert (HN : heap_nwin (VL md :: A :: VL nw :: rest) = Some n).
  { unfold heap_nwin. rewrite T, <- N. destruct (Nat.leb_spec (3 * n) (length rest)); [reflexivity| lia]. }
  rewrite HN in H. destruct (FaC.TwinB.FaC.pay fs c n (firstn (3 * n) rest)) as [ws'|] eqn:D; [|discriminate]. injection H as <-.
  assert (NWf : DefsA.CtrA.nonstack_windows n (firstn (3 * n) rest) = Some wnl) by (rewrite HeapCtrB.TwinB.nonstack_windows_firstn; exact NW).
  destruct (pay_split E0 fs c n (firstn (3 * n) rest) ws' wnl HF D NWf ltac:(rewrite firstn_length_le by lia; lia))
    as (l1 & az & l2 & lsv & W1 & W2 & RA & NZL & LEN & NW' & INL & SUB).
  rewrite firstn_length_le in LEN by lia.
  exists ws', l1, az, l2, lsv. split; [reflexivity|].
  split; [rewrite <- W1; rewrite <- (CtrFX.wins_of_firstn E0 n rest [] L), app_nil_r; reflexivity|].
  split; [rewrite <- W2; apply HeapCtrB.TwinB.wins_of_prefix; lia|].
  split; [exact RA|]. split; [exact NZL|]. split; [rewrite length_app; lia|].
  split. { rewrite skipn_app, LEN, Nat.sub_diag. cbn [skipn]. rewrite skipn_all2 by lia. reflexivity. }
  split.
  { rewrite <- NW'. rewrite <- (HeapCtrB.TwinB.nonstack_windows_firstn n (ws' ++ skipn (3 * n) rest)). f_equal.
    rewrite firstn_app, LEN, Nat.sub_diag. cbn [firstn]. rewrite app_nil_r. apply firstn_all2. lia. }
  split; [rewrite <- (firstn_skipn (3 * n) rest); apply in_or_app; left; exact INL|].
  intros x Hx. apply in_app_or in Hx as [Hx|Hx].
  - destruct (SUB x Hx) as [X|X]; [left; rewrite <- (firstn_skipn (3 * n) rest); apply in_or_app; left; exact X | right; exact X].
  - left. rewrite <- (firstn_skipn (3 * n) rest). apply in_or_app. right. exact Hx.
Qed.
End TwinB.
