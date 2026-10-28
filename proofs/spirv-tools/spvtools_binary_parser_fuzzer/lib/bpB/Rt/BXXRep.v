(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BellsX BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section RB.
  Context {HCEIL : HeapCeil}.

  Definition rblock_range (A n : Z) : Prop :=
    0 < A /\ A mod 16 = 0 /\ 0 <= n /\ aapp A n /\ A + n <= aceil.

End RB.

Section WithH.
  Context {HCEIL : HeapCeil}.
  Variable HI : asr.

Record srep := mkS { sb : list byte ;
                     sown : option block }.

Definition slen (S : srep) : Z := zlength (sb S).
Definition scap (S : srep) : Z := match sown S with None => 22 | Some (_, _, alloc) => alloc - 1 end.
Definition sdata (a : Z) (S : srep) : Z := match sown S with None => a + 1 | Some (_, A, _) => A end.
Definition blocks_S (S : srep) : list block := match sown S with None => [] | Some b => [b] end.
Definition StrEmpty : srep := mkS [] None.
Definition is_long (S : srep) : bool := match sown S with None => false | Some _ => true end.

Definition str_alloc (n : Z) : Z := if Z.lor n 7 =? 23 then 26 else Z.lor n 7 + 1.

Definition short_cells (bs junk : list byte) : list cell :=
  [C1 (b8 (2 * zlength bs)); CB (length bs) bs; C1 (b8 0); CB (22 - length bs)%nat junk].

Definition long_hdr (alloc size A : Z) : list cell := [C8 (wz (alloc + 1)); C8 (wz size); C8 (wz A)].
Definition long_buf (bs junk : list byte) (alloc : Z) : list cell :=
  [CB (length bs) bs; C1 (b8 0); CB (Z.to_nat alloc - length bs - 1)%nat junk].

Definition StrObj (LB : list block) (m : mem) (a : Z) (S : srep) : Prop :=
  match sown S with
  | None =>
      slen S <= 22 /\ exists junk, rw_cells asegs m a (short_cells (sb S) junk)
  | Some (p, A, alloc) =>
      slen S <= alloc - 1 /\ In (p, A, alloc) LB /\ rblock_range A alloc /\ alloc mod 2 = 0 /\ 24 <= alloc /\ alloc < 2^63 /\
      (a + 24 <= A \/ A + alloc <= a) /\
      rw_cells asegs m a (long_hdr alloc (slen S) A) /\
      addressable m A alloc /\
      exists junk, rw_cells asegs m A (long_buf (sb S) junk alloc)
  end.

Fixpoint rin_ivs (X : list (Z * Z)) (a : Z) : Prop :=
  match X with [] => False | iv :: X' => (fst iv <= a < snd iv) \/ rin_ivs X' a end.

Definition xclient (LB : list block) (SP : Z) (X : list (Z * Z)) (a : Z) : Prop :=
  aclient_addr HI LB SP a /\ ~ rin_ivs X a.

Definition xpres (LB : list block) (SP : Z) (X : list (Z * Z)) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> xclient LB SP X a ->
    m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None).

Lemma xpres_refl : forall LB SP X m, xpres LB SP X m m.
Proof. intros LB SP X m a _ _. auto. Qed.

Lemma xpres_trans : forall LB SP X m1 m2 m3, xpres LB SP X m1 m2 -> xpres LB SP X m2 m3 -> xpres LB SP X m1 m3.
Proof.
  intros LB SP X m1 m2 m3 H1 H2 a Ha Hc. destruct (H1 a Ha Hc) as [E1 W1]. destruct (H2 a Ha Hc) as [E2 W2].
  split; [congruence| auto].
Qed.

Lemma xpres_weaken : forall LB LB' SP SP' X X' m m',
  xpres LB SP X m m' -> SP <= SP' -> (forall b, In b LB' -> In b LB) -> (forall a, rin_ivs X a -> rin_ivs X' a) ->
  xpres LB' SP' X' m m'.
Proof.
  intros LB LB' SP SP' X X' m m' H0 HS HL HX a Ha [Hc Hx]. apply H0; [exact Ha|]. split; [| intros K; apply Hx, HX, K].
  eapply aclient_addr_weaken; eauto.
Qed.

Lemma xpres_of_apres : forall LB SP X m m', apres HI LB SP m m' -> xpres LB SP X m m'.
Proof. intros LB SP X m m' H0 a Ha [Hc _]. apply H0; assumption. Qed.

Lemma rin_ivs_app : forall X1 X2 a, rin_ivs (X1 ++ X2) a <-> rin_ivs X1 a \/ rin_ivs X2 a.
Proof. induction X1 as [|iv X1 IH]; intros; cbn; [tauto|]. rewrite IH. tauto. Qed.

Lemma xpres_of_munch : forall s LB SP X W m0 m m',
  asan_rt_hyps HI -> as_RHEAP HI s LB m0 ->
  munch W m m' -> wmono asegs m m' ->
  Forall (fun iv : Z * Z => (aceil <= fst iv /\ snd iv <= SP) \/ (forall a, fst iv <= a < snd iv -> rin_ivs X a)) W ->
  xpres LB SP X m m'.
Proof.
  intros s LB SP X W m0 m m' HH RH MU WM FW a Ha [Hc Hx].
  assert (OUT : outside W a).
  { clear MU WM. induction W as [|[lo hi] W IH]; [exact I|]. cbn.
    pose proof (Forall_inv FW) as H1. cbn in H1.
    split; [| apply IH; apply (Forall_inv_tail FW)].
    destruct H1 as [[H1 H2]|H1].
    - intros K. assert (SP <= a \/ a < aceil) as [C|C]; [| lia | lia].
      pose proof (apres_of_munch HI HH s LB SP [(lo, hi)] m0 m m RH (munch_refl _ m) (wmono_refl asegs m)
                    ltac:(constructor; [cbn; lia| constructor])) as AP.

      unfold aclient_addr in Hc. destruct Hc as [Hc|Hc]; [left; exact Hc| right].
      pose proof (ah_fsb HI HH _ _ _ RH) as (F1 & F2 & F3).
      destruct Hc as [Hc|[(b & Hb & Hr)|[(b & Hb & Hr)|[Hc|[Hc|Hc]]]]].
      + acb; unfold aimg_client, ATLS_PRIV_LO, ATLS_PRIV_HI, ATSD0, ATP in *. lia.
      + pose proof (ah_blocks HI HH _ _ _ _ RH Hb) as (_ & _ & _ & _ & R & _). lia.
      + pose proof (ah_blocks HI HH _ _ _ _ RH Hb) as (_ & _ & R0 & R1 & R & _).
        pose proof (sh_below_aceil (blk_addr b + blk_size b + 8) ltac:(acb; unfold AIMG_TOP, AAPP_HI in *; lia)).
        unfold nsh, sh in *. rewrite ASHADOW_BASE_val in *. Z.div_mod_to_equations. lia.
      + lia.
      + pose proof (sh_below_aceil (as_FSB HI + AFS_SIZE) ltac:(acb; unfold AIMG_TOP, AAPP_HI, AFS_SIZE in *; lia)).
        acb; unfold AFS_SIZE in *. lia.
      + acb; unfold AHI_LO in *. lia.
    - intros R. apply Hx. apply H1. exact R. }
  split.
  - unfold wa. apply MU. rewrite unsigned_lit by lia. exact OUT.
  - intros Hw. apply WM. exact Hw.
Qed.

Definition xclient_range (LB : list block) (SP : Z) (X : list (Z * Z)) (A n : Z) : Prop :=
  aclient_range HI LB SP A n /\ Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) X.

Lemma xclient_range_addr : forall LB SP X A n a, xclient_range LB SP X A n -> A <= a < A + n -> xclient LB SP X a.
Proof.
  intros LB SP X A n a [HR HX] Ha. split; [eapply aclient_range_addr; eauto|].
  induction X as [|iv X IH]; cbn; [tauto|]. pose proof (Forall_inv HX) as H1. cbn in H1. pose proof (Forall_inv_tail HX) as H2.
  intros [K|K]; [lia| exact (IH H2 K)].
Qed.

Lemma xpres_bytes_at : forall LB SP X m m' A bs,
  xpres LB SP X m m' -> bytes_at asegs m A bs -> xclient_range LB SP X A (Z.of_nat (length bs)) -> bytes_at asegs m' A bs.
Proof.
  intros LB SP X m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(eapply xclient_range_addr; [exact HR|lia])) as [E _].
  rewrite E. reflexivity.
Qed.

Lemma xpres_wr_at : forall LB SP X m m' A n,
  xpres LB SP X m m' -> wr_at asegs m A n -> xclient_range LB SP X A n -> wr_at asegs m' A n.
Proof.
  intros LB SP X m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(eapply xclient_range_addr; [exact HR|lia])) as [_ W].
  apply W. apply HW. exact Hi.
Qed.

Lemma xpres_rw_cells : forall LB SP X m m' A cs,
  xpres LB SP X m m' -> rw_cells asegs m A cs -> xclient_range LB SP X A (Z.of_nat (cells_size cs)) -> rw_cells asegs m' A cs.
Proof.
  intros LB SP X m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply xpres_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply xpres_wr_at; eauto.
Qed.

Lemma xpres_stk : forall LB SP X m m' lo hi,
  xpres LB SP X m m' -> stk asegs m lo hi -> SP <= lo -> Forall (fun iv : Z * Z => hi <= fst iv \/ snd iv <= lo) X ->
  stk asegs m' lo hi.
Proof.
  intros LB SP X m m' lo hi HP ST HS HX. destruct ST as (H0 & H1 & HW). split; [exact H0|]. split; [exact H1|].
  intros i Hi.
  assert (XC : xclient LB SP X i).
  { split; [left; lia|]. clear HP HW. induction X as [|iv X IH]; cbn; [tauto|].
    pose proof (Forall_inv HX) as K1. cbn in K1. pose proof (Forall_inv_tail HX) as K2. intros [K|K]; [lia| exact (IH K2 K)]. }
  destruct (HP i ltac:(lia) XC) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
  split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

Definition StrObj_foot (a : Z) (S : srep) : list (Z * Z) :=
  (a, a + 24) :: match sown S with None => [] | Some (_, A, alloc) => [(A, A + alloc)] end.

End WithH.

Arguments xpres {HCEIL} HI LB SP X m m'.
Arguments xclient {HCEIL} HI LB SP X a.
Arguments xclient_range {HCEIL} HI LB SP X A n.
