(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec StoreOk AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.

Module AGX.
Section X.
Variable segs : list Segment.
Variable E : env.
Variable M : word -> option byte.
Local Notation u := bv_unsigned.

Lemma kx_range : forall e lo hi, lo <= u (edenot E e) <= hi -> kentry_ok segs E M (KRange e lo hi).
Proof. intros e lo hi H. exact H. Qed.

Lemma kx_disj : forall a1 n1 a2 n2,
  estart E a1 + elenZ E n1 <= estart E a2 \/ estart E a2 + elenZ E n2 <= estart E a1 -> kentry_ok segs E M (KDisj a1 n1 a2 n2).
Proof. intros a1 n1 a2 n2 H. exact H. Qed.

Lemma kx_wr : forall a n, flat E a (elenZ E n) -> wr_at segs M (estart E a) (elenZ E n) -> kentry_ok segs E M (KWr a n).
Proof.
  intros a n Hfl (W0 & W1 & W2). split; [exact Hfl|]. intros d m Hd Hm.
  destruct m as [|m']; [reflexivity|].
  destruct Hfl as (F1 & F2 & F3 & F4).
  assert (Hb : u (Z_to_bv 64 (estart E a + d)) = estart E a + d) by (rewrite u_small; [reflexivity | lia]).
  apply store_ok_of_all; [rewrite Hb; lia|]. intros x Hx. rewrite Hb in Hx.
  pose proof (bv_unsigned_in_range 64 x) as Rx; change (bv_modulus 64) with (2^64) in Rx.
  specialize (W2 (u x - estart E a) ltac:(lia)). replace (estart E a + (u x - estart E a)) with (u x) in W2 by lia.
  unfold wa in W2. rewrite Z_to_bv_bv_unsigned in W2. exact W2.
Qed.

Lemma kx_unk : forall a n, flat E a (elenZ E n) ->
  (forall i, 0 <= i < elenZ E n -> M (Z_to_bv 64 (estart E a + i)) <> None) -> kentry_ok segs E M (KUnk a n).
Proof. intros a n Hfl H. split; [exact Hfl | exact H]. Qed.

Lemma kx_zero : forall a n, flat E a (elenZ E n) ->
  (forall i, 0 <= i < elenZ E n -> M (Z_to_bv 64 (estart E a + i)) = Some (Z_to_bv 8 0)) -> kentry_ok segs E M (KZero a n).
Proof. intros a n Hfl H. split; [exact Hfl | exact H]. Qed.

Lemma kx_word : forall a w v, (w <= 8)%nat -> flat E a (Z.of_nat w) ->
  rdn segs M (adenot E a) w = Some (word_to_le_bytes w (edenot E v)) -> kentry_ok segs E M (KWord a w v).
Proof. intros a w v Hw Hfl H. split; [exact Hw|]. split; [exact Hfl | exact H]. Qed.

Lemma kx_img : forall lo hi, 0 <= lo -> hi <= 2^64 -> mem_inv segs M ->
  (forall a : word, lo <= u a < hi -> ro_addr segs a = true) -> kentry_ok segs E M (KImg lo hi).
Proof.
  intros lo hi H1 H2 MI HR. cbn [kentry_ok]. split; [exact H1|]. split; [exact H2|]. intros i Hi.
  destruct (M (Z_to_bv 64 i)) as [b|] eqn:Hm; [|reflexivity]. exfalso.
  pose proof (MI _ _ Hm) as Hro. rewrite HR in Hro; [discriminate|]. rewrite u_small by lia. exact Hi.
Qed.

(* [comment removed for export] *)
Lemma kx_stk_wr : forall a n lo hi, stk segs M lo hi -> flat E a (elenZ E n) -> lo <= estart E a -> estart E a + elenZ E n <= hi ->
  kentry_ok segs E M (KWr a n).
Proof.
  intros a n lo hi (S0 & S1 & S2) Hfl H1 H2. apply kx_wr; [exact Hfl|]. destruct Hfl as (F1 & F2 & F3 & F4).
  split; [lia|]. split; [lia|]. intros i Hi. apply (S2 (estart E a + i)). lia.
Qed.
Lemma kx_stk_unk : forall a n lo hi, stk segs M lo hi -> (forall x, lo <= x < hi -> seg_rom segs (Z_to_bv 64 x) = None) ->
  flat E a (elenZ E n) -> lo <= estart E a -> estart E a + elenZ E n <= hi ->
  kentry_ok segs E M (KUnk a n).
Proof.
  intros a n lo hi (S0 & S1 & S2) HRO Hfl H1 H2. apply kx_unk; [exact Hfl|]. intros i Hi.
  destruct (S2 (estart E a + i) ltac:(lia)) as [_ (b & Hb)]. unfold mrd in Hb. unfold wa in Hb.
  destruct (M (Z_to_bv 64 (estart E a + i))); [discriminate|]. rewrite (HRO (estart E a + i) ltac:(lia)) in Hb. discriminate.
Qed.

(* [comment removed for export] *)
Lemma kx_cells_wr : forall a n cs, rw_cells segs M (estart E a) cs -> Z.of_nat (cells_size cs) = elenZ E n -> flat E a (elenZ E n) ->
  kentry_ok segs E M (KWr a n).
Proof. intros a n cs [_ HW] Hs Hfl. apply kx_wr; [exact Hfl|]. rewrite <- Hs. exact HW. Qed.

(* [comment removed for export] *)
Lemma kx_word_cells : forall a w v A cs k c, rw_cells segs M A cs -> cell_at cs k = Some c ->
  estart E a = A + Z.of_nat k -> flat E a (Z.of_nat w) -> csize c = w -> cbytes c = word_to_le_bytes w (edenot E v) -> (w <= 8)%nat ->
  kentry_ok segs E M (KWord a w v).
Proof.
  intros a w v A cs k c HC Hc Hs Hfl Hw Hb H8. apply kx_word; [exact H8 | exact Hfl|].
  pose proof (flat_u E _ _ Hfl) as Hu. destruct Hfl as (F1 & F2 & F3 & F4).
  assert (Ea : adenot E a = wa (A + Z.of_nat k)).
  { apply bv_eq. rewrite Hu. unfold wa. rewrite u_small by lia. lia. }
  rewrite Ea, <- ov_rdn, <- Hb, <- Hw. exact (rw_cells_read segs M A cs k c HC Hc).
Qed.

(* [comment removed for export] *)
Definition reg_of (K : kentry) : option (expr * Z * expr) :=
  match K with
  | KWr (SA b k) n | KUnk (SA b k) n | KZero (SA b k) n => Some (b, k, n)
  | _ => None
  end.
Definition win_gen_b (kn : list kentry) (w : expr * Z * expr) : bool :=
  let '(b, off, n) := w in
  match b, n with
  | ELit zb, ELit zn => (Z.leb 0 zb && Z.ltb zb (2^64) && Z.leb 0 (zb + off) && Z.leb 0 zn && Z.ltb zn (2^64) && Z.leb (zb + off + zn) (2^64))%bool
  | _, _ => existsb (fun K => match reg_of K with
                              | Some (b', k', n') => (expr_eqb b b' && Z.eqb off k' && expr_eqb n n')%bool
                              | None => false end) kn
  end.
Lemma aw_genuine_of_know : forall kn W, know_ok segs E M kn -> forallb (win_gen_b kn) W = true -> SX.aw_genuine E (Some W).
Proof.
  intros kn W HK H w Hw. pose proof (proj1 (forallb_forall _ _) H w Hw) as Hg. destruct w as [[b off] n]. cbn [SX.awin_den].
  unfold win_gen_b in Hg.
  assert (GEN : (exists K, In K kn /\ reg_of K = Some (b, off, n)) -> 0 <= u (edenot E b) + off /\ u (edenot E b) + off + u (edenot E n) <= 2^64).
  { intros (K & HKin & HR). pose proof (proj1 (Forall_forall _ _) HK K HKin) as HK1.
    destruct K as [a w v|[kb kk] kn0|a kn0 kk|lo hi|ae am|re rlo rhi|[wb wk] wn0|da1 dn1 da2 dn2|a kn0 fc|[ub uk] un0];
      cbn [reg_of] in HR; try discriminate; injection HR as <- <- <-; cbn [kentry_ok] in HK1;
      destruct HK1 as [(F1 & F2 & F3 & F4) _]; unfold estart, elenZ in *; cbn [a_base a_off] in *; lia. }
  assert (EX : existsb (fun K => match reg_of K with Some (b', k', n') => (expr_eqb b b' && Z.eqb off k' && expr_eqb n n')%bool
                                                   | None => false end) kn = true -> 0 <= u (edenot E b) + off /\ u (edenot E b) + off + u (edenot E n) <= 2^64).
  { intros HX. apply existsb_exists in HX as (K & HKin & HKe). apply GEN. exists K. split; [exact HKin|].
    destruct (reg_of K) as [[[b' k'] n']|]; [|discriminate].
    apply andb_prop in HKe as [HKe Hn]. apply andb_prop in HKe as [Hb Hk].
    apply expr_eqb_eq in Hb. apply Z.eqb_eq in Hk. apply expr_eqb_eq in Hn. subst. reflexivity. }
  destruct b; destruct n; try (exact (EX Hg)).
  rewrite !andb_true_iff in Hg. destruct Hg as (((((H1 & H2) & H3) & H4) & H5) & H6).
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. apply Z.leb_le in H4. apply Z.ltb_lt in H5. apply Z.leb_le in H6.
  cbn [edenot fst snd]. rewrite !u_small by lia. lia.
Qed.

End X.

(* [comment removed for export] *)
Lemma stk_join : forall segs M1 M2 lo sp hi, stk segs M2 lo sp -> stk segs M1 sp hi ->
  (forall a, sp <= a < hi -> M2 (wa a) = M1 (wa a) /\ (wview segs M1 (wa a) <> None -> wview segs M2 (wa a) <> None)) ->
  stk segs M2 lo hi.
Proof.
  intros segs M1 M2 lo sp hi (A0 & A1 & A2) (B0 & B1 & B2) HK. split; [lia|]. split; [lia|]. intros a Ha.
  destruct (Z_lt_ge_dec a sp) as [H|H]; [apply A2; lia|].
  destruct (B2 a ltac:(lia)) as [W (b & Hb)]. destruct (HK a ltac:(lia)) as [E1 W1]. split; [exact (W1 W)|].
  exists b. unfold mrd in *. rewrite E1. exact Hb.
Qed.
End AGX.
