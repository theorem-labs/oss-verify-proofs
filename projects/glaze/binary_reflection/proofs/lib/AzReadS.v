(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBss. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBss.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require AsVocab AsAinvDefs3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module RS.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section S.
Variable A : atable.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable ISP : expr.
Variable FS0 : Fs.Fs.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment ASEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_ok A.
Hypothesis IMG_le : img_lo A <= img_hi A.

#[local] Notation SEGS := ASEGS.
#[local] Notation CSOK := (APS.cs_ok ASEGS A LIMIT SINV argH ISP FS0).
#[local] Notation u := bv_unsigned.
#[local] Notation cellN := (AsVocab.cellN ASEGS).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma estart_lit : forall E z, estart E (SA (ELit 0) z) = z.
Proof. intros E z. unfold estart. cbn [a_base a_off]. rewrite edenot_lit, u_lit0. lia. Qed.
Lemma elenZ_lit : forall E z, 0 <= z < 2 ^ 64 -> elenZ E (ELit z) = z.
Proof. intros E z Hz. unfold elenZ. rewrite edenot_lit, u64_lit by lia. reflexivity. Qed.


(* [comment removed for export] *)
Lemma kzero_bytes : forall E M b off l i,
  kentry_ok SEGS E M (KZero (SA b off) l) ->
  estart E (SA b off) <= i < estart E (SA b off) + elenZ E l ->
  M (Z_to_bv 64 i) = Some (Z_to_bv 8 0) /\ cellN M i 1 0.
Proof.
  intros E M b off l i HK Hi. cbn [kentry_ok] in HK. destruct HK as [Hfl Hz].
  pose proof (Hz (i - estart E (SA b off)) ltac:(lia)) as Hb.
  replace (estart E (SA b off) + (i - estart E (SA b off))) with i in Hb by lia.
  split; [exact Hb|]. unfold AsVocab.cellN. cbn [rdn]. rewrite Hb. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma kfill_bytes : forall E M b off l c i,
  kentry_ok SEGS E M (KFill (SA b off) l c) -> 0 <= c < 256 ->
  estart E (SA b off) <= i < estart E (SA b off) + elenZ E l ->
  M (Z_to_bv 64 i) = Some (Z_to_bv 8 c) /\ cellN M i 1 c.
Proof.
  intros E M b off l c i HK Hc Hi. cbn [kentry_ok] in HK. destruct HK as [Hfl Hz].
  pose proof (Hz (i - estart E (SA b off)) ltac:(lia)) as Hb.
  replace (estart E (SA b off) + (i - estart E (SA b off))) with i in Hb by lia.
  split; [exact Hb|]. unfold AsVocab.cellN. cbn [rdn]. rewrite Hb. cbn [word_to_le_bytes Z_to_le_bytes].
  rewrite u64_lit by lia. reflexivity.
Qed.


(* [comment removed for export] *)
Lemma kwr_store_ok : forall E M b off l i,
  kentry_ok SEGS E M (KWr (SA b off) l) ->
  estart E (SA b off) <= i < estart E (SA b off) + elenZ E l -> store_ok SEGS M (Z_to_bv 64 i) 1 = true.
Proof.
  intros E M b off l i HK Hi. cbn [kentry_ok] in HK. destruct HK as [Hfl Hs].
  pose proof (Hs (i - estart E (SA b off)) 1%nat ltac:(lia) ltac:(cbn; lia)) as Hb.
  replace (estart E (SA b off) + (i - estart E (SA b off))) with i in Hb by lia. exact Hb.
Qed.

(* [comment removed for export] *)
Lemma krange_bounds : forall E M e lo hi,
  kentry_ok SEGS E M (KRange e lo hi) -> lo <= u (edenot E e) <= hi.
Proof. intros E M e lo hi HK. cbn [kentry_ok] in HK. exact HK. Qed.
Lemma kdisj_apart : forall E M b1 o1 n1 b2 o2 n2,
  kentry_ok SEGS E M (KDisj (SA b1 o1) n1 (SA b2 o2) n2) ->
  estart E (SA b1 o1) + elenZ E n1 <= estart E (SA b2 o2) \/ estart E (SA b2 o2) + elenZ E n2 <= estart E (SA b1 o1).
Proof. intros E M b1 o1 n1 b2 o2 n2 HK. cbn [kentry_ok] in HK. exact HK. Qed.

(* [comment removed for export] *)
Lemma know_ok_In : forall E M k K, know_ok SEGS E M k -> In K k -> kentry_ok SEGS E M K.
Proof. intros E M k K HK Hin. exact (proj1 (Forall_forall _ _) HK K Hin). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint bytes_eqb (xs ys : list byte) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => Z.eqb (u x) (u y) && bytes_eqb xs' ys'
  | _, _ => false
  end.
Lemma bytes_eqb_eq : forall xs ys, bytes_eqb xs ys = true -> xs = ys.
Proof.
  induction xs as [|x xs IH]; intros [|y ys] H; try discriminate; [reflexivity|].
  cbn [bytes_eqb] in H. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. f_equal; [apply bv_eq; exact H1 | exact (IH _ H2)].
Qed.

(* [comment removed for export] *)
Definition cell_z (k : list kentry) (b : expr) (off : Z) (n : nat) (v : Z) : bool :=
  flat_x k b off (ELit (Z.of_nat n)) &&
  match know_lookup SEGS k b off n false [] [] with
  | LHit v' [] _ =>
      match eval_closed v' with
      | Some z' => bytes_eqb (word_to_le_bytes n (Z_to_bv 64 z')) (word_to_le_bytes n (Z_to_bv 64 v))
      | None => false
      end
  | _ => false
  end.
(* [comment removed for export] *)
Definition cell_e (k : list kentry) (b : expr) (off : Z) (n : nat) (e : expr) : bool :=
  flat_x k b off (ELit (Z.of_nat n)) &&
  match know_lookup SEGS k b off n false [] [] with
  | LHit v' [] _ => expr_eqb v' e || respell_ok k v' e
  | _ => false
  end.

Lemma flat_x_flat : forall E M k b off n, know_ok SEGS E M k -> (n <= 8)%nat ->
  flat_x k b off (ELit (Z.of_nat n)) = true -> flat E (SA b off) (Z.of_nat n).
Proof.
  intros E M k b off n HK Hn H. pose proof (APS.flat_x_sound SEGS E M k b off _ HK H) as (F1 & F2 & F3).
  rewrite edenot_lit, u64_lit in F2, F3 by lia. unfold flat. lia.
Qed.

Lemma cell_z_sound : forall E M k b off n v,
  know_ok SEGS E M k -> (1 <= n <= 8)%nat -> cell_z k b off n v = true ->
  cellN M (estart E (SA b off)) n v.
Proof.
  intros E M k b off n v HK Hn H. unfold cell_z in H. apply andb_prop in H as [Hfl H].
  pose proof (flat_x_flat E M k b off n HK ltac:(lia) Hfl) as F.
  destruct (know_lookup SEGS k b off n false [] []) as [v' [|? ?] hs| |] eqn:HL; try discriminate.
  destruct (eval_closed v') as [z'|] eqn:Hz; [|discriminate]. apply bytes_eqb_eq in H.
  destruct (GCL.lookup_piece SEGS E M k b off n v' hs HK Hn HL F) as (bs & Hrd & Hlen & Hbs).
  unfold AsVocab.cellN. rewrite Hrd, <- Hbs, (eval_closed_sound E v' z' Hz), H. reflexivity.
Qed.

Lemma cell_e_sound : forall E M k b off n e,
  know_ok SEGS E M k -> (1 <= n <= 8)%nat -> cell_e k b off n e = true ->
  cellN M (estart E (SA b off)) n (u (edenot E e)).
Proof.
  intros E M k b off n e HK Hn H. unfold cell_e in H. apply andb_prop in H as [Hfl H].
  pose proof (flat_x_flat E M k b off n HK ltac:(lia) Hfl) as F.
  destruct (know_lookup SEGS k b off n false [] []) as [v' [|? ?] hs| |] eqn:HL; try discriminate.
  assert (EQ : edenot E v' = edenot E e).
  { apply Bool.orb_prop in H. destruct H as [H|H]; [apply expr_eqb_eq in H; subst; reflexivity | exact (APS.respell_ok_sound SEGS E M k v' e HK H)]. }
  destruct (GCL.lookup_piece SEGS E M k b off n v' hs HK Hn HL F) as (bs & Hrd & Hlen & Hbs).
  unfold AsVocab.cellN. rewrite Hrd, <- Hbs, EQ, Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint zcover1 (k : list kentry) (b : expr) (i stop : Z) : option Z :=
  match k with
  | [] => None
  | K :: rest =>
      let hit := match K with
                 | KWord (SA kb kk) w (ELit z) =>
                     if (Z.eqb z 0 && expr_eqb b kb && Z.leb kk i && Z.ltb i (kk + Z.of_nat w))%bool then Some (kk + Z.of_nat w) else None
                 | KZero (SA kb kk) (ELit l) =>
                     if (expr_eqb b kb && Z.leb 0 l && Z.ltb l two64 && Z.leb kk i && Z.ltb i (kk + l))%bool then Some (kk + l) else None
                 | KFill (SA kb kk) (ELit l) c =>
                     if (Z.eqb c 0 && expr_eqb b kb && Z.leb 0 l && Z.ltb l two64 && Z.leb kk i && Z.ltb i (kk + l))%bool then Some (kk + l) else None
                 | KImg lo hi =>
                     if (expr_eqb b (ELit 0) && Z.leb lo i && Z.ltb i hi && Z.leb BSS_LO i && Z.ltb i BSS_HI)%bool then Some (Z.min hi BSS_HI) else None
                 | _ => None
                 end in
      match hit with Some e => Some e | None => zcover1 rest b i stop end
  end.
Fixpoint zcover_x (fuel : nat) (k : list kentry) (b : expr) (i : Z) (stop : Z) : bool :=
  match fuel with
  | O => false
  | Datatypes.S f => if Z.leb stop i then true else
           match zcover1 k b i stop with
           | Some e => if Z.ltb i e then zcover_x f k b e stop else false
           | None => false
           end
  end.

(* [comment removed for export] *)
Lemma rdn_zero_bytes : forall M w a,
  rdn SEGS M (Z_to_bv 64 a) w = Some (word_to_le_bytes w (Z_to_bv 64 0)) -> 0 <= a -> a + Z.of_nat w <= 2 ^ 64 ->
  forall d, 0 <= d < Z.of_nat w -> cellN M (a + d) 1 0.
Proof.
  intros M w. induction w as [|w IH]; intros a Hrd Ha Hw d Hd; [lia|].
  rewrite AsAinvDefs3.rdn_S in Hrd. rewrite AsAinvDefs3.w2le_zero in Hrd. cbn [repeat] in Hrd.
  destruct (rdn SEGS M (Z_to_bv 64 a) 1) as [[|b0 [|]]|] eqn:H1; try discriminate.
  destruct (rdn SEGS M (Z_to_bv 64 a + 1)%bv w) as [r|] eqn:Hr; [|discriminate]. injection Hrd as E0 Er. subst b0 r.
  destruct (Z.eq_dec d 0) as [->|Hd0].
  - unfold AsVocab.cellN. rewrite Z.add_0_r, H1. reflexivity.
  - replace (a + d) with ((a + 1) + (d - 1)) by lia. apply (IH (a + 1)); try lia.
    rewrite <- AsAinvDefs3.w_succ by lia. rewrite Hr, AsAinvDefs3.w2le_zero. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma bss_cellN_zero : forall M n a,
  BSS_LO <= a -> a + Z.of_nat n <= BSS_HI -> (forall i, a <= i < a + Z.of_nat n -> M (Z_to_bv 64 i) = None) ->
  cellN M a n 0.
Proof. intros M n a H1 H2 H3. unfold AsVocab.cellN. rewrite (bss_rdn_zero M n a H1 H2 H3), AsAinvDefs3.w2le_zero. reflexivity. Qed.
Lemma bss_byte_zero : forall M i, BSS_LO <= i < BSS_HI -> M (Z_to_bv 64 i) = None -> cellN M i 1 0.
Proof.
  intros M i Hi HN. apply (bss_cellN_zero M 1 i); [lia | cbn; lia |]. intros j Hj. replace j with i by lia. exact HN.
Qed.

Lemma zcover1_sound : forall E M k b i stop en,
  know_ok SEGS E M k -> zcover1 k b i stop = Some en ->
  i < en /\ forall j, i <= j < en -> 0 <= uE E b + j < 2 ^ 64 /\ cellN M (uE E b + j) 1 0.
Proof.
  intros E M k b i stop en HK. induction k as [|K rest IH]; intros H; [discriminate|].
  apply Forall_cons_iff in HK as [HKK Hrest]. cbn [zcover1] in H.
  match type of H with (match ?h with Some e0 => Some e0 | None => _ end = Some en) =>
    destruct h as [e0|] eqn:Hhit; [injection H as ->|exact (IH Hrest H)] end.
  clear IH. destruct K as [[kb kk] w [z| | | | | | |]|[kb kk] [l| | | | | | |]| |ilo ihi| | | | |[kb kk] [l| | | | | | |] c| | |]; try discriminate.
  - (* [comment removed for export] *)
    destruct (Z.eqb z 0 && expr_eqb b kb && Z.leb kk i && Z.ltb i (kk + Z.of_nat w))%bool eqn:C; [|discriminate]. injection Hhit as <-.
    apply andb_prop in C as [C X3]. apply andb_prop in C as [C X2]. apply andb_prop in C as [X0 X1].
    apply Z.eqb_eq in X0. subst z. apply expr_eqb_eq in X1. subst kb. apply Z.leb_le in X2. apply Z.ltb_lt in X3.
    cbn [kentry_ok] in HKK. destruct HKK as (Hw & Hfl & Hrd).
    rewrite GCL.adenot_SA, edenot_lit in Hrd.
    destruct Hfl as (F1 & F2 & F3 & F4). unfold estart in *; cbn [a_base a_off] in *. unfold uE.
    split; [lia|]. intros j Hj. split; [lia|].
    replace (u (edenot E b) + j) with ((u (edenot E b) + kk) + (j - kk)) by lia.
    apply (rdn_zero_bytes M w); [exact Hrd | lia | lia | lia].
  - (* [comment removed for export] *)
    destruct (expr_eqb b kb && Z.leb 0 l && Z.ltb l two64 && Z.leb kk i && Z.ltb i (kk + l))%bool eqn:C; [|discriminate]. injection Hhit as <-.
    apply andb_prop in C as [C X4]. apply andb_prop in C as [C X3]. apply andb_prop in C as [C X2]. apply andb_prop in C as [X0 X1].
    apply expr_eqb_eq in X0. subst kb. apply Z.leb_le in X1. apply Z.ltb_lt in X2. apply Z.leb_le in X3. apply Z.ltb_lt in X4. unfold two64 in X2.
    pose proof HKK as HKK'. cbn [kentry_ok] in HKK'. destruct HKK' as [Hfl _]. rewrite (elenZ_lit E l) in Hfl by lia.
    destruct Hfl as (F1 & F2 & F3 & F4). unfold estart in F1, F2, F4; cbn [a_base a_off] in F1, F2, F4. unfold uE.
    split; [lia|]. intros j Hj. split; [lia|].
    destruct (kzero_bytes E M b kk (ELit l) (u (edenot E b) + j) HKK) as [_ C1];
      [unfold estart; cbn [a_base a_off]; rewrite (elenZ_lit E l) by lia; lia | exact C1].
  - (* [comment removed for export] *)
    destruct (expr_eqb b (ELit 0) && Z.leb ilo i && Z.ltb i ihi && Z.leb BSS_LO i && Z.ltb i BSS_HI)%bool eqn:C; [|discriminate]. injection Hhit as <-.
    apply andb_prop in C as [C X4]. apply andb_prop in C as [C X3]. apply andb_prop in C as [C X2]. apply andb_prop in C as [X0 X1].
    apply expr_eqb_eq in X0. subst b. apply Z.leb_le in X1. apply Z.ltb_lt in X2. apply Z.leb_le in X3. apply Z.ltb_lt in X4.
    cbn [kentry_ok] in HKK. destruct HKK as (I1 & I2 & I3). unfold uE. rewrite edenot_lit, u_lit0.
    pose proof X3 as X3'. pose proof X4 as X4'. unfold BSS_LO, BSS_HI in X3', X4'.
    split; [lia|]. intros j Hj. split; [unfold BSS_HI in *; lia|]. rewrite Z.add_0_l.
    apply bss_byte_zero; [unfold BSS_LO, BSS_HI in *; lia | apply I3; lia].
  - (* [comment removed for export] *)
    destruct (Z.eqb c 0 && expr_eqb b kb && Z.leb 0 l && Z.ltb l two64 && Z.leb kk i && Z.ltb i (kk + l))%bool eqn:C; [|discriminate]. injection Hhit as <-.
    apply andb_prop in C as [C X4]. apply andb_prop in C as [C X3]. apply andb_prop in C as [C X2]. apply andb_prop in C as [C X1]. apply andb_prop in C as [Xc X0].
    apply Z.eqb_eq in Xc. subst c.
    apply expr_eqb_eq in X0. subst kb. apply Z.leb_le in X1. apply Z.ltb_lt in X2. apply Z.leb_le in X3. apply Z.ltb_lt in X4. unfold two64 in X2.
    pose proof HKK as HKK'. cbn [kentry_ok] in HKK'. destruct HKK' as [Hfl _]. rewrite (elenZ_lit E l) in Hfl by lia.
    destruct Hfl as (F1 & F2 & F3 & F4). unfold estart in F1, F2, F4; cbn [a_base a_off] in F1, F2, F4. unfold uE.
    split; [lia|]. intros j Hj. split; [lia|].
    destruct (kfill_bytes E M b kk (ELit l) 0 (u (edenot E b) + j) HKK ltac:(lia)) as [_ C1];
      [unfold estart; cbn [a_base a_off]; rewrite (elenZ_lit E l) by lia; lia | exact C1].
Qed.

Lemma zcover_x_sound : forall fuel E M k b i stop,
  know_ok SEGS E M k -> zcover_x fuel k b i stop = true ->
  forall j, i <= j < stop -> 0 <= uE E b + j < 2 ^ 64 /\ cellN M (uE E b + j) 1 0.
Proof.
  induction fuel as [|f IH]; intros E M k b i stop HK H j Hj; [discriminate|].
  cbn [zcover_x] in H. destruct (Z.leb_spec stop i); [lia|].
  destruct (zcover1 k b i stop) as [en|] eqn:Hc; [|discriminate]. destruct (Z.ltb_spec i en); [|discriminate].
  destruct (zcover1_sound E M k b i stop en HK Hc) as [_ Hcov].
  destruct (Z.lt_ge_cases j en); [apply Hcov; lia | eapply IH; [exact HK | exact H | lia]].
Qed.

(* [comment removed for export] *)
Definition zfill_x (k : list kentry) (b : expr) (lo hi : Z) : bool := zcover_x (Datatypes.S (length k)) k b lo hi.
Lemma zfill_x_sound : forall E M k b lo hi,
  know_ok SEGS E M k -> zfill_x k b lo hi = true ->
  forall i, uE E b + lo <= i < uE E b + hi -> cellN M i 1 0.
Proof.
  intros E M k b lo hi HK H i Hi. unfold zfill_x in H.
  destruct (zcover_x_sound _ E M k b lo hi HK H (i - uE E b) ltac:(lia)) as [_ C].
  replace i with (uE E b + (i - uE E b)) by lia. exact C.
Qed.

(* [comment removed for export] *)
Definition kwr_in (k : list kentry) (b : expr) (lo hi : Z) : bool :=
  existsb (fun K => match K with
                    | KWr (SA wb wk) (ELit wn) => expr_eqb b wb && Z.leb wk lo && Z.leb hi (wk + wn) && Z.leb 0 wn && Z.ltb wn two64
                    | _ => false
                    end) k.
Lemma kwr_in_sound : forall E M k b lo hi,
  know_ok SEGS E M k -> kwr_in k b lo hi = true ->
  forall j, lo <= j < hi -> 0 <= uE E b + j < 2 ^ 64 /\ store_ok SEGS M (Z_to_bv 64 (uE E b + j)) 1 = true.
Proof.
  intros E M k b lo hi HK H j Hj. unfold kwr_in in H. apply existsb_exists in H as [K [Hin HKb]].
  destruct K as [| | | | | |[wb wk] [wn| | | | | | |]| | | | |]; try discriminate.
  repeat match type of HKb with (_ && _)%bool = true => apply andb_prop in HKb as [HKb ?X] end.
  apply expr_eqb_eq in HKb. subst wb. apply Z.leb_le in X2. apply Z.leb_le in X1. apply Z.leb_le in X0. apply Z.ltb_lt in X. unfold two64 in X.
  pose proof (know_ok_In E M k _ HK Hin) as HKK.
  pose proof HKK as HKK'. cbn [kentry_ok] in HKK'. destruct HKK' as [Hfl _]. rewrite (elenZ_lit E wn) in Hfl by lia.
  destruct Hfl as (F1 & F2 & F3 & F4). unfold estart in F1, F2, F4; cbn [a_base a_off] in F1, F2, F4. unfold uE.
  split; [lia|].
  apply (kwr_store_ok E M b wk (ELit wn) (u (edenot E b) + j) HKK).
  unfold estart; cbn [a_base a_off]. rewrite (elenZ_lit E wn) by lia. lia.
Qed.

(* [comment removed for export] *)
Definition wwin_x (k : list kentry) (b : expr) (lo hi : Z) : bool :=
  (lo <? hi) && (hi - lo <? two64) && kwr_in k b lo hi && off_image_x A k b lo (ELit (hi - lo)) && cover_x (Datatypes.S (length k)) k b lo hi.
Lemma wwin_x_sound : forall E M k b lo hi,
  know_ok SEGS E M k -> lo < hi -> wwin_x k b lo hi = true ->
  forall i, uE E b + lo <= i < uE E b + hi -> M (Z_to_bv 64 i) <> None /\ store_ok SEGS M (Z_to_bv 64 i) 1 = true.
Proof.
  intros E M k b lo hi HK Hlt H i Hi. unfold wwin_x in H. apply andb_prop in H as [H Hc]. apply andb_prop in H as [H Ho].
  apply andb_prop in H as [H Hw]. apply andb_prop in H as [_ H64]. apply Z.ltb_lt in H64. unfold two64 in H64.
  destruct (kwr_in_sound E M k b lo hi HK Hw (i - uE E b) ltac:(lia)) as [B S1].
  replace (uE E b + (i - uE E b)) with i in S1, B by lia. split; [|exact S1].
  pose proof (ranges_apart_x_sound SEGS E M k _ _ _ _ _ _ HK Ho) as AP0.
  rewrite (elenZ_lit E (hi - lo)) in AP0 by lia. rewrite (elenZ_lit E (img_hi A - img_lo A)) in AP0 by (pose proof HULL_ok as HU; pose proof IMG_le; unfold hull_ok, KHI in HU; lia).
  rewrite estart_lit in AP0. unfold estart in AP0; cbn [a_base a_off] in AP0.
  destruct (APS.cover_x_sound SEGS A SEGS_in_hull _ E M k b lo hi HK Hc (i - uE E b) ltac:(lia)) as [_ D].
  - unfold in_hull, uE in *. apply andb_false_iff. destruct AP0 as [AP0|AP0]; [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia].
  - replace (uE E b + (i - uE E b)) with i in D by lia. exact D.
Qed.

(* [comment removed for export] *)
Definition kimg_in (k : list kentry) (lo hi : Z) : bool :=
  Z.leb hi lo || ((BSS_LO <=? lo) && (hi <=? BSS_HI) && existsb (fun K => match K with KImg lo' hi' => Z.leb lo' lo && Z.leb hi hi' | _ => false end) k).
Lemma kimg_in_sound : forall E M k lo hi, know_ok SEGS E M k -> kimg_in k lo hi = true ->
  forall a n, lo <= a -> a + Z.of_nat n <= hi -> cellN M a n 0.
Proof.
  intros E M k lo hi HK H a n Ha Hn. unfold kimg_in in H. apply Bool.orb_prop in H. destruct H as [H|H].
  - apply Z.leb_le in H. destruct n; [unfold AsVocab.cellN; cbn; reflexivity | cbn in Hn; lia].
  - apply andb_prop in H as [H Hx]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    apply existsb_exists in Hx as [K [Hin HKb]]. destruct K as [| | |lo' hi'| | | | | | | |]; try discriminate.
    apply andb_prop in HKb as [H3 H4]. apply Z.leb_le in H3. apply Z.leb_le in H4.
    pose proof (know_ok_In E M k _ HK Hin) as HKK. cbn [kentry_ok] in HKK. destruct HKK as (I1 & I2 & I3).
    apply bss_cellN_zero; [lia | lia |]. intros i Hi. apply I3. lia.
Qed.

(* [comment removed for export] *)
Inductive cval := CZ (z : Z) | CE (e : expr).
Definition cval_den (E : env) (c : cval) : Z := match c with CZ z => z | CE e => u (edenot E e) end.
Definition const_x (k : list kentry) (c : Z * nat * cval) : bool :=
  let '(a, n, v) := c in
  ((1 <=? Z.of_nat n) && (Z.of_nat n <=? 8))%Z &&
  match v with CZ z => cell_z k (ELit 0) a n z | CE e => cell_e k (ELit 0) a n e end.
Lemma const_x_sound : forall E M k c, know_ok SEGS E M k -> const_x k c = true ->
  cellN M (fst (fst c)) (snd (fst c)) (cval_den E (snd c)).
Proof.
  intros E M k [[a n] v] HK H. unfold const_x in H. apply andb_prop in H as [Hn H]. apply andb_prop in Hn as [H1 H8].
  apply Z.leb_le in H1. apply Z.leb_le in H8. cbn [fst snd].
  rewrite <- (estart_lit E a). destruct v as [z|e]; cbn [cval_den].
  - eapply cell_z_sound; [exact HK | lia | exact H].
  - eapply cell_e_sound; [exact HK | lia | exact H].
Qed.
Lemma consts_x_sound : forall E M k cs, know_ok SEGS E M k -> forallb (const_x k) cs = true ->
  Forall (fun c => cellN M (fst (fst c)) (snd (fst c)) (snd c)) (map (fun c => (fst (fst c), snd (fst c), cval_den E (snd c))) cs).
Proof.
  intros E M k cs HK H. apply Forall_map. apply Forall_forall. intros c Hin. cbn [fst snd].
  apply (const_x_sound E M k c HK). exact (proj1 (forallb_forall _ _) H c Hin).
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition vpg (i : nat) : expr := EMd M_MUL (ELit 4096) (EVar i).
Definition V_G6 : nat := 227.  Definition V_W6 : nat := 229.  Definition V_G8 : nat := 246.

Definition V_G10 : nat := 248.


   (* [comment removed for export] *)
Definition V_T : nat := 10.

Definition e_P6 : expr := vpg V_G6.
(* [comment removed for export] *)
Definition e_SPB : expr := EAlu ALU_ADD (vpg V_G6) (vpg V_W6).
Definition e_RI : expr := EAlu ALU_ADD (EAlu ALU_ADD (vpg V_G6) (vpg V_W6)) (ELit 137438953472).
Definition e_TOP : expr := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 4096) (EVar V_T)).
Definition e_BOT : expr := EAlu ALU_ADD e_TOP (ELit (-8388608)).








(* [comment removed for export] *)
Definition I0 : Z := 0x103f18.

















End S.
End RS.
