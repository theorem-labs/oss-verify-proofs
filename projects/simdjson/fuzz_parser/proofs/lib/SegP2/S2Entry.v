(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec Mem Cells Step.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegBridge SegTmpl SegProg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.

Local Notation u := bv_unsigned.
Local Notation M64 := 18446744073709551616.

Definition mkEZ (ZL : list Z) : env := Env (fun n => Z_to_bv 64 (nth n ZL 0)) (fun _ => []).

Fixpoint zok (e : expr) : bool :=
  match e with
  | ELit _ | EVar _ => true
  | EAlu ALU_ADD a b | EAlu ALU_SUB a b => zok a && zok b
  | EMd M_MUL a b => zok a && zok b
  | _ => false
  end.
Fixpoint zden (ZL : list Z) (e : expr) : Z :=
  match e with
  | ELit z => z
  | EVar n => nth n ZL 0
  | EAlu ALU_ADD a b => zden ZL a + zden ZL b
  | EAlu ALU_SUB a b => zden ZL a - zden ZL b
  | EMd M_MUL a b => zden ZL a * zden ZL b
  | _ => 0
  end.

Lemma Z_to_bv_congr : forall x y, x mod M64 = y mod M64 -> Z_to_bv 64 x = Z_to_bv 64 y.
Proof.
  intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with M64. exact H.
Qed.
Lemma u_Z_to_bv : forall x, u (Z_to_bv 64 x) = x mod M64.
Proof. intros x. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. reflexivity. Qed.

Lemma zden_ok : forall ZL e, zok e = true -> edenot (mkEZ ZL) e = Z_to_bv 64 (zden ZL e).
Proof.
  intros ZL e. induction e as [z|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx k i n];
    intros H; cbn [zok] in H; try discriminate; try reflexivity.
  - destruct op; try discriminate; apply andb_prop in H as [Ha Hb]; cbn [edenot zden]; rewrite (IHa Ha), (IHb Hb).
    + rewrite alu_add. unfold v_add. apply Z_to_bv_congr. rewrite !u_Z_to_bv. rewrite <- Z.add_mod by lia. reflexivity.
    + rewrite alu_sub. unfold v_sub. apply Z_to_bv_congr. rewrite !u_Z_to_bv. symmetry. apply Zminus_mod.
  - destruct op; try discriminate; apply andb_prop in H as [Ha Hb]; cbn [edenot zden mul_div]; rewrite (IHa Ha), (IHb Hb).
    apply bv_eq. rewrite bv_mul_unsigned, !u_Z_to_bv. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with M64.
    rewrite <- Z.mul_mod by lia. reflexivity.
Qed.

Lemma u_zden : forall ZL e, zok e = true -> u (edenot (mkEZ ZL) e) = zden ZL e mod M64.
Proof. intros ZL e H. rewrite zden_ok by exact H. apply u_Z_to_bv. Qed.

Section K.
  Variable segs : list Segment.
  Variable ZL : list Z.
  Variable m : word -> option byte.
  Local Notation E := (mkEZ ZL).
  Local Notation zv e := (zden ZL e mod M64).

  Lemma kz_range : forall e lo hi, zok e = true -> lo <= zv e <= hi -> kentry_ok segs E m (KRange e lo hi).
  Proof. intros e lo hi Hz H. cbn [kentry_ok]. rewrite u_zden by exact Hz. exact H. Qed.

  Lemma kz_align : forall e k, zok e = true -> 0 < k -> (zv e) mod k = 0 -> kentry_ok segs E m (KAlign e k).
  Proof. intros e k Hz Hk H. cbn [kentry_ok]. rewrite u_zden by exact Hz. split; assumption. Qed.

  Lemma kz_disj : forall b1 k1 n1 b2 k2 n2, (zok b1 && zok n1 && zok b2 && zok n2)%bool = true ->
    zv b1 + k1 + zv n1 <= zv b2 + k2 \/ zv b2 + k2 + zv n2 <= zv b1 + k1 ->
    kentry_ok segs E m (KDisj (SA b1 k1) n1 (SA b2 k2) n2).
  Proof.
    intros b1 k1 n1 b2 k2 n2 Hz H. repeat (apply andb_prop in Hz as [Hz ?]).
    cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off]. rewrite !u_zden by assumption. exact H.
  Qed.

  Lemma kz_word : forall b k w v, (zok b && zok v)%bool = true -> (0 < w <= 8)%nat -> 0 <= zv b + k ->
    bytes_at segs m (zv b + k) (word_to_le_bytes w (Z_to_bv 64 (zden ZL v))) -> kentry_ok segs E m (KWord (SA b k) w v).
  Proof.
    intros b k w v Hz Hw H0 HB. apply andb_prop in Hz as [Hb Hv].
    apply SB.kb_word; [exact Hw | rewrite u_zden by exact Hb; exact H0 |]. rewrite u_zden, zden_ok by assumption. exact HB.
  Qed.

  Lemma kz_wr : forall b k n, (zok b && zok n)%bool = true -> 0 <= zv b + k -> zv b + k + zv n <= M64 -> zv b + k < M64 ->
    wr_at segs m (zv b + k) (zv n) -> kentry_ok segs E m (KWr (SA b k) n).
  Proof.
    intros b k n Hz H0 H1 H2 (_ & _ & HW). apply andb_prop in Hz as [Hb Hn].
    apply SB.kb_wr; rewrite ?u_zden by assumption; try lia.
    intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). replace (u x) with (zv b + k + (u x - (zv b + k))) by lia.
    apply HW. lia.
  Qed.

  Lemma kz_unk : forall b k n, (zok b && zok n)%bool = true -> 0 <= zv b + k -> zv b + k + zv n <= M64 -> zv b + k < M64 ->
    (forall i, 0 <= i < zv n -> m (Z_to_bv 64 (zv b + k + i)) <> None) -> kentry_ok segs E m (KUnk (SA b k) n).
  Proof.
    intros b k n Hz H0 H1 H2 HD. apply andb_prop in Hz as [Hb Hn].
    apply SB.kb_unk; rewrite ?u_zden by assumption; try lia. exact HD.
  Qed.

  Lemma kz_zero : forall b k n, (zok b && zok n)%bool = true -> 0 <= zv b + k -> zv b + k + zv n <= M64 -> zv b + k < M64 ->
    (forall i, 0 <= i < zv n -> m (Z_to_bv 64 (zv b + k + i)) = Some (Z_to_bv 8 0)) -> kentry_ok segs E m (KZero (SA b k) n).
  Proof.
    intros b k n Hz H0 H1 H2 HD. apply andb_prop in Hz as [Hb Hn]. cbn [kentry_ok]. unfold flat, estart, elenZ. cbn [a_base a_off].
    rewrite !u_zden by assumption. pose proof (Z.mod_pos_bound (zden ZL n) M64 ltac:(lia)).
    split; [lia | exact HD].
  Qed.

  Lemma kz_img : forall lo hi, 0 <= lo -> hi <= M64 -> mem_inv segs m ->
    (forall a : word, lo <= u a < hi -> ro_addr segs a = true) -> kentry_ok segs E m (KImg lo hi).
  Proof.
    intros lo hi H1 H2 MI HR. cbn [kentry_ok]. split; [exact H1|]. split; [exact H2|]. intros i Hi.
    destruct (m (Z_to_bv 64 i)) as [b|] eqn:Hm; [|reflexivity]. exfalso.
    pose proof (MI _ _ Hm) as Hro. rewrite HR in Hro; [discriminate|]. rewrite u_Z_to_bv, Z.mod_small by lia. exact Hi.
  Qed.
End K.

(* [comment removed for export] *)
Lemma rw_cells_cell : forall segs m A cs k c, rw_cells segs m A cs -> cell_at cs k = Some c ->
  bytes_at segs m (A + Z.of_nat k) (cbytes c).
Proof.
  intros segs m A cs k c [[Hwf Hb] _] Hc.
  destruct (cell_at_split _ _ _ c Hc) as (pre & post & Ecs & Hsz & _).
  rewrite Ecs in Hwf, Hb. apply cells_wf_app in Hwf. destruct Hwf as [Hwpre _].
  rewrite cells_bytes_app in Hb. cbn [cells_bytes] in Hb.
  apply bytes_at_app in Hb. destruct Hb as [_ Hb].
  rewrite cells_bytes_length in Hb by assumption. rewrite Hsz in Hb.
  apply bytes_at_app in Hb. exact (proj1 Hb).
Qed.



Section K2.
  Variable segs : list Segment.
  Variable ZL : list Z.
  Variable m : word -> option byte.
  Local Notation E := (mkEZ ZL).
  Local Notation zv e := (zden ZL e mod M64).

  Lemma kz_word_cells : forall b k w v A cs k', (zok b && zok v)%bool = true -> (0 < w <= 8)%nat ->
    rw_cells segs m A cs -> zv b + k = A + Z.of_nat k' ->
    match cell_at cs k' with Some c => cbytes c = word_to_le_bytes w (Z_to_bv 64 (zden ZL v)) | None => False end ->
    kentry_ok segs E m (KWord (SA b k) w v).
  Proof.
    intros b k w v A cs k' Hz Hw HR HA HB. destruct (cell_at cs k') as [c|] eqn:Hc; [|contradiction].
    pose proof (rw_cells_cell segs m A cs k' c HR Hc) as HBy.
    pose proof (bytes_at_bound segs m _ _ HBy) as [B0 _].
    apply (kz_word segs ZL m); [exact Hz | exact Hw | lia |]. rewrite HA, <- HB. exact HBy.
  Qed.

  Lemma kz_wr_sub : forall b k n A L, (zok b && zok n)%bool = true -> wr_at segs m A L ->
    A <= zv b + k -> zv b + k + zv n <= A + L -> zv b + k < M64 -> kentry_ok segs E m (KWr (SA b k) n).
  Proof.
    intros b k n A L Hz (W0 & W1 & W) H1 H2 H3. pose proof (Z.mod_pos_bound (zden ZL n) M64 ltac:(lia)).
    apply (kz_wr segs ZL m); [exact Hz | lia | lia | lia |]. split; [lia|]. split; [lia|].
    intros i Hi. replace (zv b + k + i) with (A + (zv b + k - A + i)) by lia. apply W. lia.
  Qed.

  Lemma kz_unk_bytes : forall b k n A bs, (zok b && zok n)%bool = true -> bytes_at segs m A bs ->
    (forall i, 0 <= i < Z.of_nat (length bs) -> seg_rom segs (Z_to_bv 64 (A + i)) = None) ->
    A <= zv b + k -> zv b + k + zv n <= A + Z.of_nat (length bs) -> zv b + k < M64 -> kentry_ok segs E m (KUnk (SA b k) n).
  Proof.
    intros b k n A bs Hz HB HR H1 H2 H3. pose proof (bytes_at_bound segs m _ _ HB) as [B0 B1].
    pose proof (Z.mod_pos_bound (zden ZL n) M64 ltac:(lia)).
    apply (kz_unk segs ZL m); [exact Hz | lia | lia | lia |]. intros i Hi.
    replace (zv b + k + i) with (A + (zv b + k - A + i)) by lia. apply (SB.bytes_at_overlay segs m A bs HB HR). lia.
  Qed.

  Lemma kz_zero_bytes : forall b k n A bs, (zok b && zok n)%bool = true -> bytes_at segs m A bs ->
    (forall i, 0 <= i < Z.of_nat (length bs) -> seg_rom segs (Z_to_bv 64 (A + i)) = None) ->
    A <= zv b + k -> zv b + k + zv n <= A + Z.of_nat (length bs) -> zv b + k < M64 ->
    (forall i, 0 <= i < zv n -> nth_error bs (Z.to_nat (zv b + k - A + i)) = Some (Z_to_bv 8 0)) ->
    kentry_ok segs E m (KZero (SA b k) n).
  Proof.
    intros b k n A bs Hz HB HR H1 H2 H3 HZ. pose proof (bytes_at_bound segs m _ _ HB) as [B0 B1].
    pose proof (Z.mod_pos_bound (zden ZL n) M64 ltac:(lia)).
    apply (kz_zero segs ZL m); [exact Hz | lia | lia | lia |]. intros i Hi.
    destruct HB as (_ & _ & HB). specialize (HB (Z.to_nat (zv b + k - A + i)) ltac:(lia)). rewrite Z2Nat.id in HB by lia.
    rewrite HZ in HB by lia. replace (A + (zv b + k - A + i)) with (zv b + k + i) in HB by lia.
    unfold mrd in HB. destruct (m (wa (zv b + k + i))) as [x|] eqn:Hm.
    - unfold wa in Hm. rewrite Hm. exact HB.
    - exfalso. specialize (HR (zv b + k - A + i) ltac:(lia)). replace (A + (zv b + k - A + i)) with (zv b + k + i) in HR by lia.
      unfold wa in HB. rewrite HR in HB. discriminate.
  Qed.
End K2.

(* [comment removed for export] *)
Lemma bytes_at_defined : forall segs m A bs, bytes_at segs m A bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> seg_rom segs (Z_to_bv 64 (A + i)) = None) ->
  forall i, 0 <= i < Z.of_nat (length bs) -> m (Z_to_bv 64 (A + i)) <> None.
Proof. intros segs m A bs HB HR. exact (SB.bytes_at_overlay segs m A bs HB HR). Qed.


(* [comment removed for export] *)
Lemma know_nth : forall segs E m kn k K, know_ok segs E m kn -> nth_error kn k = Some K -> kentry_ok segs E m K.
Proof. intros segs E m kn k K H Hk. exact (proj1 (Forall_forall _ _) H K (nth_error_In _ _ Hk)). Qed.

Lemma kx_word_g : forall segs G ZL E' m b k w v, SP.gagree G (mkEZ ZL) E' -> eb (mkEZ ZL) = eb E' ->
  expr_vars_lt G b = true -> expr_vars_lt G v = true -> (zok b && zok v)%bool = true ->
  kentry_ok segs E' m (KWord (SA b k) w v) ->
  bytes_at segs m (zden ZL b mod M64 + k) (word_to_le_bytes w (Z_to_bv 64 (zden ZL v))).
Proof.
  intros segs G ZL E' m b k w v Hg Hb Hvb Hvv Hz HK. apply andb_prop in Hz as [Hzb Hzv].
  pose proof (SB.kx_word segs E' m b k w v HK) as HB.
  rewrite <- (SP.edenot_gagree G (mkEZ ZL) E' b Hg Hb Hvb), <- (SP.edenot_gagree G (mkEZ ZL) E' v Hg Hb Hvv) in HB.
  rewrite u_zden, zden_ok in HB by assumption. exact HB.
Qed.

(* [comment removed for export] *)
Ltac kz_pure solver :=
  lazymatch goal with
  | |- kentry_ok _ (mkEZ _) _ (KRange _ _ _) => apply kz_range; [reflexivity | cbn [zden nth]; solver]
  | |- kentry_ok _ (mkEZ _) _ (KAlign _ _) => apply kz_align; [reflexivity | lia | cbn [zden nth]; solver]
  | |- kentry_ok _ (mkEZ _) _ (KDisj (SA _ _) _ (SA _ _) _) => apply kz_disj; [reflexivity | cbn [zden nth]; solver]
  end.
