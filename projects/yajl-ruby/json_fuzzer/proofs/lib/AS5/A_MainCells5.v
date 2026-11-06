(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.yajl_ruby.json_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import PropExec CatExec ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.XQ Require Import
  AgentLib AsanAcct AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.AS5 Require Import AsanPlanImages5 HS2Asan A_MainFacts A_ImgZero5.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require AImages AImageFacts.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require InitMem Step Cells Mem Arr MState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive xv := XL (z : Z) | XS (e : expr).
(* [comment removed for export] *)
Inductive cx :=
| CX8 (v : xv) | CX4 (z : Z) | CX2 (z : Z) | CX1 (z : Z)   (* [comment removed for export] *)
| CXB (zs : list Z)                                         (* [comment removed for export] *)
| CXZ (n : Z)                                               (* [comment removed for export] *)
| CXA (n : Z).                                              (* [comment removed for export] *)

Definition cx_len (c : cx) : Z :=
  match c with CX8 _ => 8 | CX4 _ => 4 | CX2 _ => 2 | CX1 _ => 1 | CXB zs => Z.of_nat (length zs) | CXZ n => n | CXA n => n end.
Fixpoint cxs_len (l : list cx) : Z := match l with [] => 0 | c :: r => cx_len c + cxs_len r end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition A_RW_LO : Z := 0xa4000.
Fixpoint img_zero (a : Z) (n : nat) : bool :=
  match n with O => true | S n' => match img_byte a with Some b => bv_eqb b (Z_to_bv 8 0) && img_zero (a + 1) n' | None => false end end.
Definition is_abs (be : expr) : bool := expr_eqb be (ELit 0).
Definition u64b (n : Z) : bool := (0 <=? n) && (n <? 2 ^ 64).

(* [comment removed for export] *)
Definition byte_of_fact (K : kentry) (be : expr) (a : Z) : option (option byte) :=
  match K with
  | KWord (SA b o) w v => if (expr_eqb b be && (o <=? a) && (a <? o + Z.of_nat w))%bool then
                            match v with
                            | ELit z => match nth_error (word_to_le_bytes w (Z_to_bv 64 z)) (Z.to_nat (a - o)) with Some bt => Some (Some bt) | None => None end
                            | _ => Some None
                            end
                          else None
  | KZero (SA b o) (ELit n) => if (expr_eqb b be && (o <=? a) && (a <? o + n) && u64b n)%bool then Some (Some (Z_to_bv 8 0)) else None
  | KFill (SA b o) (ELit n) c => if (expr_eqb b be && (o <=? a) && (a <? o + n) && u64b n)%bool then Some (Some (Z_to_bv 8 c)) else None
  | KUnk (SA b o) (ELit n) => if (expr_eqb b be && (o <=? a) && (a <? o + n) && u64b n)%bool then Some None else None
  | KImg lo hi => if (is_abs be && (lo <=? a) && (a <? hi) && (A_RW_LO <=? a))%bool then match img_byte a with Some bt => Some (Some bt) | None => None end else None
  | _ => None
  end.
(* [comment removed for export] *)
Definition byte_matches (want : option byte) (got : option (option byte)) : bool :=
  match want, got with
  | _, None => false
  | None, Some _ => true
  | Some b, Some (Some b') => bv_eqb b b'
  | Some _, Some None => false
  end.
(* [comment removed for export] *)
Definition covers_def (K : kentry) (be : expr) (a : Z) : bool :=
  match K with
  | KWr (SA b o) (ELit n) | KZero (SA b o) (ELit n) | KFill (SA b o) (ELit n) _ | KUnk (SA b o) (ELit n) =>
      expr_eqb b be && (o <=? a) && (a <? o + n) && u64b n
  | _ => false
  end.
Definition wr_ev (k : list kentry) (be : expr) (a : Z) : bool :=
  (is_abs be && (A_RW_LO <=? a) && (a <? A_IMG_HI)) || existsb (fun K => covers_def K be a) k.
Definition byte_ok (k : list kentry) (be : expr) (a : Z) (want : option byte) : bool :=
  existsb (fun K => byte_matches want (byte_of_fact K be a)) k && wr_ev k be a.
Fixpoint wr_evs (k : list kentry) (be : expr) (a : Z) (n : nat) : bool :=
  match n with O => true | S n' => wr_ev k be a && wr_evs k be (a + 1) n' end.
Fixpoint lbytes_ok (k : list kentry) (be : expr) (a : Z) (bs : list byte) : bool :=
  match bs with [] => true | b :: r => byte_ok k be a (Some b) && lbytes_ok k be (a + 1) r end.
Fixpoint any_ok (k : list kentry) (be : expr) (a : Z) (n : nat) : bool :=
  match n with O => true | S n' => byte_ok k be a None && any_ok k be (a + 1) n' end.
(* [comment removed for export] *)
Definition word_ok (k : list kentry) (be : expr) (a : Z) (e : expr) : bool :=
  existsb (fun K => match K with KWord (SA b o) 8%nat v => expr_eqb b be && Z.eqb o a && expr_eqb v e | _ => false end) k.
(* [comment removed for export] *)
Definition zero_ok (k : list kentry) (be : expr) (a n : Z) : bool :=
  existsb (fun K => match K with
                    | KZero (SA b o) (ELit m) => expr_eqb b be && (o <=? a) && (a + n <=? o + m) && u64b m
                    | KImg lo hi => if (is_abs be && (lo <=? a) && (a + n <=? hi) && (A_RW_LO <=? a))%bool        (* [comment removed for export] *)
                                  then (if (A_BSS_LO <=? a) && (a + n <=? A_IMG_HI) then true else img_zero a (Z.to_nat n)) else false
                    | _ => false end) k.

Definition lit_bytes (w : nat) (z : Z) : list byte := word_to_le_bytes w (Z_to_bv 64 z).
Definition cx_ok (k : list kentry) (be : expr) (a : Z) (c : cx) : bool :=
  (match c with
   | CX8 (XL z) => lbytes_ok k be a (lit_bytes 8 z)
   | CX8 (XS e) => word_ok k be a e && wr_evs k be a 8
   | CX4 z => lbytes_ok k be a (lit_bytes 4 z)
   | CX2 z => lbytes_ok k be a (lit_bytes 2 z)
   | CX1 z => lbytes_ok k be a (lit_bytes 1 z)
   | CXB zs => match zs with [] => false | _ => lbytes_ok k be a (map (Z_to_bv 8) zs) end
   | CXZ n => (0 <? n) && zero_ok k be a n
   | CXA n => (0 <? n) && any_ok k be a (Z.to_nat n)
   end).
Fixpoint cxs_okk (k : list kentry) (be : expr) (a : Z) (l : list cx) : bool :=
  match l with [] => true | c :: r => cx_ok k be a c && cxs_okk k be (a + cx_len c) r end.
(* [comment removed for export] *)
Definition cxs_ok (be : expr) (a : Z) (l : list cx) : bool :=
  (0 <? cxs_len l) && cxs_okk (kn HS_s2_00) be a l && cxs_okk (kn HS_s2_01) be a l
  && cxs_okk (kn HS_s2_10) be a l && cxs_okk (kn HS_s2_11) be a l.

(* [comment removed for export] *)
Definition xv_den (E : env) (v : xv) : word := match v with XL z => Z_to_bv 64 z | XS e => edenot E e end.
(* [comment removed for export] *)
Definition cx_prop (E : env) (m : word -> option byte) (A : Z) (c : cx) : Prop :=
  match c with
  | CX8 v => Mem.bytes_at AImages.asegs m A (Mem.le8 (xv_den E v))
  | CX4 z => Mem.bytes_at AImages.asegs m A (Mem.le4 (Z_to_bv 64 z))
  | CX2 z => Mem.bytes_at AImages.asegs m A (Mem.le2 (Z_to_bv 64 z))
  | CX1 z => Mem.bytes_at AImages.asegs m A [Z_to_bv 8 z]
  | CXB zs => Mem.bytes_at AImages.asegs m A (map (Z_to_bv 8) zs)
  | CXZ n => Mem.bytes_at AImages.asegs m A (repeat (Z_to_bv 8 0) (Z.to_nat n))
  | CXA n => exists bs, Z.of_nat (length bs) = n /\ Mem.bytes_at AImages.asegs m A bs
  end.
Fixpoint cxs_prop (E : env) (m : word -> option byte) (A : Z) (l : list cx) : Prop :=
  match l with [] => True | c :: r => cx_prop E m A c /\ cxs_prop E m (A + cx_len c) r end.


Definition pgE (v : nat) : expr := EMd Instr.M_MUL (ELit 4096) (EVar v).
(* [comment removed for export] *)
Definition e_sb : expr := EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 226)) (EMd Instr.M_MUL (ELit (-4096)) (EVar 227))) (ELit 65536).
Definition e_rib : expr := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 226)) (EMd Instr.M_MUL (ELit (-4096)) (EVar 227)).

(* [comment removed for export] *)
Lemma w2lb_1 : forall z, word_to_le_bytes 1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof.
  intros z. cbn. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64)%Z with (2^8 * 2^56)%Z. change (2 ^ Z.of_N 8)%Z with (2^8)%Z.
  rewrite Z.rem_mul_r by lia. set (q := ((z / 2 ^ 8) mod 2 ^ 56)%Z). replace (z mod 2^8 + 2^8 * q)%Z with (z mod 2^8 + q * 2^8)%Z by lia.
  rewrite Z.mod_add by lia. apply Z.mod_mod. lia.
Qed.
Lemma img_zero_sound : forall n a, img_zero a n = true -> forall i, 0 <= i < Z.of_nat n -> img_byte (a + i) = Some (Z_to_bv 8 0).
Proof.
  induction n as [|n IH]; intros a H i Hi; [lia|]. cbn [img_zero] in H.
  destruct (img_byte a) as [b|] eqn:Hb; [|discriminate]. apply andb_prop in H as [H1 H2].
  destruct (Z.eq_dec i 0) as [->|Hne].
  - rewrite Z.add_0_r, Hb. unfold bv_eqb in H1. apply Z.eqb_eq in H1. f_equal. apply bv_eq. exact H1.
  - replace (a + i) with (a + 1 + (i - 1)) by lia. apply (IH (a + 1) H2). lia.
Qed.

Lemma img_byte_inside : forall a b, 0 <= a < 2 ^ 64 -> img_byte a = Some b -> 0x10000 <= a < 0x603000.
Proof.
  intros a b Ha Hb. unfold img_byte in Hb.
  destruct (Z_lt_le_dec a 0x10000) as [L|L]; [|destruct (Z_lt_le_dec a 0x603000) as [L2|L2]; [lia|]];
    exfalso; rewrite AImageFacts.asan_seg_rom_none in Hb by (unfold Mem.wa; rewrite u64_lit by lia; lia); discriminate.
Qed.

Section Sound.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variable hw : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable uid : word.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Variable E : env.
  Variable R : bvmap 5 word.
  Variable FULL : word -> option byte.
  Variable model : Model.
  Variable hs : acs.
  Hypothesis Hhs : HS_MAIN hs.
  Hypothesis HC : cs_ok ASEGS ASAN5 AsanInit.LIMIT (SINV0 APH sp rdraw brk0 argv envp uid hw) (argH0 APH sp rdraw argv envp uid hw) fs E hs R FULL model.

  #[local] Notation MR := (Mr ASAN5 (argH0 APH sp rdraw argv envp uid hw) E hs model FULL).
  #[local] Notation BYTES := (Mem.bytes_at AImages.asegs).
  #[local] Notation WR := (Mem.wr_at AImages.asegs).

  Lemma know_hs : know_ok ASEGS E MR (kn hs).
  Proof. exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

  Lemma fact_in : forall K, In K (kn hs) -> kentry_ok ASEGS E MR K.
  Proof. intros K HK. exact (proj1 (Forall_forall _ _) know_hs K HK). Qed.

  (* [comment removed for export] *)
  Lemma mrd_MR_FULL : forall x b, Mem.mrd AImages.asegs MR x = Some b ->
    Mem.mrd AImages.asegs FULL x = Some b /\ (0x14d000 <= bv_unsigned x -> wview AImages.asegs FULL x <> None).
  Proof.
    intros x b H. unfold Mem.mrd in H |- *. pose proof (u64_range x) as Rx.
    destruct (MR x) as [b0|] eqn:HM.
    - injection H as <-. rewrite (Mr_some0 sp rdraw hw argv envp uid E FULL model hs x b0 HM).
      split; [reflexivity|]. intros _. unfold wview. rewrite (Mr_some0 sp rdraw hw argv envp uid E FULL model hs x b0 HM). discriminate.
    - assert (IB : img_byte (bv_unsigned x) = Some b).
      { unfold img_byte, Mem.wa. rewrite Z_to_bv_bv_unsigned. exact H. }
      pose proof (img_byte_inside (bv_unsigned x) b Rx IB) as IN.
      rewrite <- (A_MainFacts.Mr_hull sp rdraw hw argv envp uid Hsp Hva E FULL model hs x IN), HM.
      split; [exact H|]. intros Hw. apply AsanPlanImages5.asan_rw_window. lia.
  Qed.

  Lemma wview_MR_FULL : forall x, wview AImages.asegs MR x <> None -> wview AImages.asegs FULL x <> None.
  Proof.
    intros x H. unfold wview in *. destruct (MR x) as [b|] eqn:HM.
    - rewrite (Mr_some0 sp rdraw hw argv envp uid E FULL model hs x b HM). discriminate.
    - destruct (FULL x); [discriminate | exact H].
  Qed.

  Lemma expr_eqb_true : forall a b, expr_eqb a b = true -> a = b.
  Proof. intros a b H. apply expr_eqb_eq. exact H. Qed.

  (* [comment removed for export] *)
  Definition byteP (A : Z) (want : option byte) : Prop :=
    0 <= A < 2 ^ 64 /\ (exists b, Mem.mrd AImages.asegs FULL (Mem.wa A) = Some b /\ forall b', want = Some b' -> b = b')
    /\ wview AImages.asegs FULL (Mem.wa A) <> None.

  Lemma wa_lit : forall z, 0 <= z < 2 ^ 64 -> Mem.wa z = Z_to_bv 64 z. Proof. reflexivity. Qed.

  Lemma byte_of_fact_sound : forall K be a r, kentry_ok ASEGS E MR K -> byte_of_fact K be a = Some r ->
    0 <= uE E be + a < 2 ^ 64 /\ exists b, Mem.mrd AImages.asegs MR (Mem.wa (uE E be + a)) = Some b /\ forall b', r = Some b' -> b = b'.
  Proof.
    intros K be a r HK H.
    destruct K as [[b o] w v|[b o] nn|[b o] nn kb|lo hi|e m|e rlo rhi|[b o] nn|a1 n1 a2 n2|[b o] nn fc|[b o] nn]; cbn [byte_of_fact] in H; try discriminate.
    - (* [comment removed for export] *)
      destruct (expr_eqb b be && (o <=? a) && (a <? o + Z.of_nat w))%bool eqn:C; [|discriminate].
      apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2]. apply expr_eqb_true in C1. subst b. apply Z.leb_le in C2. apply Z.ltb_lt in C3.
      cbn [kentry_ok] in HK. destruct HK as (Hw & Hf & Hr). pose proof (flat_u E _ _ Hf) as FU. pose proof Hf as (F1 & F2 & F3 & F4).
      unfold estart in *. cbn [a_base a_off] in *. change (bv_unsigned (edenot E be)) with (uE E be) in *.
      assert (AD : adenot E (SA be o) = Mem.wa (uE E be + o)) by (unfold Mem.wa; apply bv_eq; rewrite FU, u64_lit by lia; reflexivity).
      rewrite AD, LibBridge.rdn_lib in Hr.
      pose proof (LibBridge.rdn_bytes_at MR (word_to_le_bytes w (edenot E v)) (uE E be + o) ltac:(lia) ltac:(rewrite CatExec.length_N_to_le_bytes; lia)) as BA.
      rewrite CatExec.length_N_to_le_bytes in BA. specialize (BA Hr). destruct BA as (_ & _ & BA).
      specialize (BA (Z.to_nat (a - o)) ltac:(rewrite CatExec.length_N_to_le_bytes; lia)). rewrite Z2Nat.id in BA by lia.
      replace (uE E be + o + (a - o)) with (uE E be + a) in BA by lia.
      split; [lia|].
      assert (GEN : r = None -> exists b0, Mem.mrd AImages.asegs MR (Mem.wa (uE E be + a)) = Some b0 /\ (forall b', r = Some b' -> b0 = b')).
      { intros ->. destruct (nth_error (word_to_le_bytes w (edenot E v)) (Z.to_nat (a - o))) as [bt|] eqn:Hn;
          [exists bt; split; [exact BA | intros b' X; discriminate X] | exfalso; apply nth_error_None in Hn; rewrite CatExec.length_N_to_le_bytes in Hn; lia]. }
      destruct v as [z|v1|o1 x1 y1|o1 x1 y1|o1 x1 y1|o1 x1 y1|sx lo1 n1 e1|sx k1 i1 n1]; try (injection H as <-; exact (GEN eq_refl)).
      cbn [edenot] in BA. destruct (nth_error (word_to_le_bytes w (Z_to_bv 64 z)) (Z.to_nat (a - o))) as [bt|] eqn:Hn; [|discriminate].
      injection H as <-. exists bt. split; [exact BA | intros b' X; injection X; auto].
    - (* [comment removed for export] *) destruct nn as [n|?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ? ?|? ? ? ?]; try discriminate.
      destruct (expr_eqb b be && (o <=? a) && (a <? o + n) && u64b n)%bool eqn:C; [|discriminate]. injection H as <-.
      apply andb_prop in C as [C C4]. apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2]. apply expr_eqb_true in C1. subst b. apply Z.leb_le in C2. apply Z.ltb_lt in C3.
      unfold u64b in C4. apply andb_prop in C4 as [C4 C5]. apply Z.leb_le in C4. apply Z.ltb_lt in C5.
      cbn [kentry_ok] in HK. destruct HK as (Hf & Hz). pose proof Hf as (F1 & F2 & F3 & F4). unfold estart, elenZ in *. cbn [a_base a_off edenot] in *.
      rewrite u64_lit in * by lia. change (bv_unsigned (edenot E be)) with (uE E be) in *.
      split; [lia|]. exists (Z_to_bv 8 0). split; [| intros b' X; injection X; auto].
      unfold Mem.mrd, Mem.wa. replace (uE E be + a) with (uE E be + o + (a - o)) by lia. rewrite (Hz (a - o)) by lia. reflexivity.
    - (* [comment removed for export] *)
      destruct (is_abs be && (lo <=? a) && (a <? hi) && (A_RW_LO <=? a))%bool eqn:C; [|discriminate].
      apply andb_prop in C as [C C4]. apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2].
      unfold is_abs in C1. apply expr_eqb_true in C1. subst be. apply Z.leb_le in C2. apply Z.ltb_lt in C3.
      cbn [kentry_ok] in HK. destruct HK as (L1 & L2 & Hn).
      replace (uE E (ELit 0)) with 0 in * by (unfold uE; cbn [edenot]; rewrite u64_lit by lia; reflexivity). rewrite Z.add_0_l.
      destruct (img_byte a) as [bt|] eqn:Hb; [|discriminate]. injection H as <-.
      split; [lia|]. exists bt. split; [| intros b' X; injection X; auto].
      unfold Mem.mrd. unfold Mem.wa. rewrite (Hn a) by lia. unfold img_byte, Mem.wa in Hb. exact Hb.
    - (* [comment removed for export] *) destruct nn as [n|?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ? ?|? ? ? ?]; try discriminate.
      destruct (expr_eqb b be && (o <=? a) && (a <? o + n) && u64b n)%bool eqn:C; [|discriminate]. injection H as <-.
      apply andb_prop in C as [C C4]. apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2]. apply expr_eqb_true in C1. subst b. apply Z.leb_le in C2. apply Z.ltb_lt in C3.
      unfold u64b in C4. apply andb_prop in C4 as [C4 C5]. apply Z.leb_le in C4. apply Z.ltb_lt in C5.
      cbn [kentry_ok] in HK. destruct HK as (Hf & Hz). pose proof Hf as (F1 & F2 & F3 & F4). unfold estart, elenZ in *. cbn [a_base a_off edenot] in *.
      rewrite u64_lit in * by lia. change (bv_unsigned (edenot E be)) with (uE E be) in *.
      split; [lia|]. exists (Z_to_bv 8 fc). split; [| intros b' X; injection X; auto].
      unfold Mem.mrd, Mem.wa. replace (uE E be + a) with (uE E be + o + (a - o)) by lia. rewrite (Hz (a - o)) by lia. reflexivity.
    - (* [comment removed for export] *) destruct nn as [n|?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ? ?|? ? ? ?]; try discriminate.
      destruct (expr_eqb b be && (o <=? a) && (a <? o + n) && u64b n)%bool eqn:C; [|discriminate]. injection H as <-.
      apply andb_prop in C as [C C4]. apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2]. apply expr_eqb_true in C1. subst b. apply Z.leb_le in C2. apply Z.ltb_lt in C3.
      unfold u64b in C4. apply andb_prop in C4 as [C4 C5]. apply Z.leb_le in C4. apply Z.ltb_lt in C5.
      cbn [kentry_ok] in HK. destruct HK as (Hf & Hz). pose proof Hf as (F1 & F2 & F3 & F4). unfold estart, elenZ in *. cbn [a_base a_off edenot] in *.
      rewrite u64_lit in * by lia. change (bv_unsigned (edenot E be)) with (uE E be) in *.
      split; [lia|]. specialize (Hz (a - o) ltac:(lia)). replace (uE E be + o + (a - o)) with (uE E be + a) in Hz by lia.
      unfold Mem.mrd, Mem.wa. destruct (MR (Z_to_bv 64 (uE E be + a))) as [bt|]; [|exfalso; exact (Hz eq_refl)].
      exists bt. split; [reflexivity | intros b' X; discriminate X].
  Qed.

  Lemma covers_def_sound : forall K be a, kentry_ok ASEGS E MR K -> covers_def K be a = true ->
    wview AImages.asegs FULL (Mem.wa (uE E be + a)) <> None.
  Proof.
    intros K be a HK H. apply wview_MR_FULL.
    destruct K as [[b o] w v|[b o] nn|[b o] nn kb|lo hi|e m|e rlo rhi|[b o] nn|a1 n1 a2 n2|[b o] nn fc|[b o] nn]; cbn [covers_def] in H; try discriminate;
      destruct nn as [n|?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ? ?|? ? ? ?]; try discriminate;
      apply andb_prop in H as [H C4]; apply andb_prop in H as [H C3]; apply andb_prop in H as [C1 C2]; apply expr_eqb_true in C1; subst b; apply Z.leb_le in C2; apply Z.ltb_lt in C3;
      unfold u64b in C4; apply andb_prop in C4 as [C4 C5]; apply Z.leb_le in C4; apply Z.ltb_lt in C5;
      cbn [kentry_ok] in HK; destruct HK as (Hf & Hz); pose proof Hf as (F1 & F2 & F3 & F4); unfold estart, elenZ in *; cbn [a_base a_off edenot] in *;
      rewrite u64_lit in * by lia; change (bv_unsigned (edenot E be)) with (uE E be) in *;
      unfold Mem.wa; replace (uE E be + a) with (uE E be + o + (a - o)) by lia.
    - (* [comment removed for export] *) unfold wview. rewrite (Hz (a - o)) by lia. discriminate.
    - (* [comment removed for export] *) specialize (Hz (a - o) 1%nat ltac:(lia) ltac:(lia)). cbn [store_ok] in Hz.
      destruct (wview ASEGS MR (Z_to_bv 64 (uE E be + o + (a - o)))) eqn:W; [|discriminate]. change AImages.asegs with ASEGS. rewrite W. discriminate.
    - (* [comment removed for export] *) unfold wview. rewrite (Hz (a - o)) by lia. discriminate.
    - (* [comment removed for export] *) unfold wview. specialize (Hz (a - o) ltac:(lia)). destruct (MR (Z_to_bv 64 (uE E be + o + (a - o)))); [discriminate | exfalso; exact (Hz eq_refl)].
  Qed.

  Lemma wr_ev_sound : forall be a, wr_ev (kn hs) be a = true -> 0 <= uE E be + a < 2 ^ 64 -> wview AImages.asegs FULL (Mem.wa (uE E be + a)) <> None.
  Proof.
    intros be a H HR. unfold wr_ev in H. apply orb_prop in H as [H|H].
    - apply andb_prop in H as [H C3]. apply andb_prop in H as [C1 C2]. unfold is_abs in C1. apply expr_eqb_true in C1. subst be.
      apply Z.leb_le in C2. apply Z.ltb_lt in C3. unfold A_RW_LO, A_IMG_HI in *.
      replace (uE E (ELit 0)) with 0 in * by (unfold uE; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
      apply AsanPlanImages5.asan_rw_window. unfold Mem.wa. rewrite u64_lit by lia. lia.
    - apply existsb_exists in H as (K & HK & HC'). exact (covers_def_sound K be a (fact_in K HK) HC').
  Qed.

  Lemma byte_ok_sound : forall be a want, byte_ok (kn hs) be a want = true -> byteP (uE E be + a) want.
  Proof.
    intros be a want H. unfold byte_ok in H. apply andb_prop in H as [H W]. apply existsb_exists in H as (K & HK & HM).
    unfold byte_matches in HM. destruct (byte_of_fact K be a) as [r|] eqn:HB; [|destruct want; discriminate].
    destruct (byte_of_fact_sound K be a r (fact_in K HK) HB) as (HR & b & Hb & Hr).
    split; [exact HR|]. split; [| exact (wr_ev_sound be a W HR)].
    exists b. split; [exact (proj1 (mrd_MR_FULL _ _ Hb))|]. intros b' ->. destruct r as [b''|]; [|discriminate]. unfold bv_eqb in HM. apply Z.eqb_eq in HM.
    rewrite (Hr b'' eq_refl). apply bv_eq. symmetry. exact HM.
  Qed.

  Lemma lbytes_ok_sound : forall bs be a, lbytes_ok (kn hs) be a bs = true ->
    forall i b, nth_error bs i = Some b -> byteP (uE E be + a + Z.of_nat i) (Some b).
  Proof.
    induction bs as [|b0 bs IH]; intros be a H i b Hn; [destruct i; discriminate|].
    cbn [lbytes_ok] in H. apply andb_prop in H as [H1 H2].
    destruct i as [|i]; cbn in Hn.
    - injection Hn as ->. rewrite Z.add_0_r. exact (byte_ok_sound be a (Some b) H1).
    - replace (uE E be + a + Z.of_nat (S i)) with (uE E be + (a + 1) + Z.of_nat i) by lia. exact (IH be (a + 1) H2 i b Hn).
  Qed.

  Lemma any_ok_sound : forall n be a, any_ok (kn hs) be a n = true -> forall i, (i < n)%nat -> byteP (uE E be + a + Z.of_nat i) None.
  Proof.
    induction n as [|n IH]; intros be a H i Hi; [lia|]. cbn [any_ok] in H. apply andb_prop in H as [H1 H2].
    destruct i as [|i].
    - rewrite Z.add_0_r. exact (byte_ok_sound be a None H1).
    - replace (uE E be + a + Z.of_nat (S i)) with (uE E be + (a + 1) + Z.of_nat i) by lia. exact (IH be (a + 1) H2 i ltac:(lia)).
  Qed.

  (* [comment removed for export] *)
  Lemma byteP_bytes_at : forall A bs, bs <> [] -> (forall i b, nth_error bs i = Some b -> byteP (A + Z.of_nat i) (Some b)) ->
    BYTES FULL A bs /\ WR FULL A (Z.of_nat (length bs)).
  Proof.
    intros A bs Hne H.
    assert (R0 : 0 <= A /\ A + Z.of_nat (length bs) <= 2 ^ 64).
    { destruct bs as [|b0 bs']; [congruence|].
      destruct (H 0%nat b0 eq_refl) as (RR & _). rewrite Z.add_0_r in RR.
      destruct (nth_error (b0 :: bs') (length bs')) as [bl|] eqn:Hl; [| apply nth_error_None in Hl; cbn [length] in Hl; lia].
      destruct (H _ bl Hl) as (RL & _). cbn [length]. lia. }
    split.
    - split; [lia|]. split; [lia|]. intros i Hi. destruct (nth_error bs i) as [b|] eqn:Hn; [| apply nth_error_None in Hn; lia].
      destruct (H i b Hn) as (_ & (b1 & Hb1 & Heq) & _). rewrite Hb1, (Heq b eq_refl). reflexivity.
    - split; [lia|]. split; [lia|]. intros i Hi. destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:Hn; [| apply nth_error_None in Hn; lia].
      destruct (H (Z.to_nat i) b Hn) as (_ & _ & W). rewrite Z2Nat.id in W by lia. exact W.
  Qed.

  Lemma anyP_bytes_at : forall A n, (0 < n)%nat -> (forall i, (i < n)%nat -> byteP (A + Z.of_nat i) None) ->
    exists bs, length bs = n /\ BYTES FULL A bs /\ WR FULL A (Z.of_nat n).
  Proof.
    intros A n Hn H.
    set (bs := map (fun i => match Mem.mrd AImages.asegs FULL (Mem.wa (A + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end) (seq 0 n)).
    assert (LEN : length bs = n) by (subst bs; rewrite length_map, length_seq; reflexivity).
    exists bs. split; [exact LEN|].
    destruct (H 0%nat Hn) as (R0 & _). rewrite Z.add_0_r in R0. destruct (H (n - 1)%nat ltac:(lia)) as (RL & _).
    split.
    - split; [lia|]. split; [rewrite LEN; lia|]. intros i Hi. rewrite LEN in Hi.
      subst bs. rewrite nth_error_map, nth_error_seq. replace (Nat.ltb i n) with true by (symmetry; apply Nat.ltb_lt; exact Hi). cbn [option_map Nat.add].
      destruct (H i Hi) as (_ & (b & Hb & _) & _). rewrite Hb. reflexivity.
    - split; [lia|]. split; [lia|]. intros i Hi. destruct (H (Z.to_nat i) ltac:(lia)) as (_ & _ & W). rewrite Z2Nat.id in W by lia. exact W.
  Qed.

  Lemma wr_evs_sound : forall n be a, wr_evs (kn hs) be a n = true ->
    forall i, 0 <= i < Z.of_nat n -> 0 <= uE E be + a + i < 2 ^ 64 -> wview AImages.asegs FULL (Mem.wa (uE E be + a + i)) <> None.
  Proof.
    induction n as [|n IH]; intros be a H i Hi HR; [lia|]. cbn [wr_evs] in H. apply andb_prop in H as [H1 H2].
    destruct (Z.eq_dec i 0) as [->|Hne].
    - rewrite Z.add_0_r in *. exact (wr_ev_sound be a H1 HR).
    - replace (uE E be + a + i) with (uE E be + (a + 1) + (i - 1)) in * by lia. apply (IH be (a + 1) H2); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma word_ok_sound : forall be a e, word_ok (kn hs) be a e = true -> wr_evs (kn hs) be a 8 = true ->
    BYTES FULL (uE E be + a) (Mem.le8 (edenot E e)) /\ WR FULL (uE E be + a) 8.
  Proof.
    intros be a e H W. unfold word_ok in H. apply existsb_exists in H as (K & HK & HM).
    destruct K as [[b o] w v| | | | | | | | | ]; try discriminate. do 8 (destruct w as [|w]; try discriminate). destruct w; [|discriminate].
    apply andb_prop in HM as [HM C3]. apply andb_prop in HM as [C1 C2]. apply expr_eqb_true in C1. apply Z.eqb_eq in C2. apply expr_eqb_true in C3. subst b o v.
    pose proof (fact_in _ HK) as X. cbn [kentry_ok] in X. destruct X as (Hw & Hf & Hr). pose proof (flat_u E _ _ Hf) as FU. pose proof Hf as (F1 & F2 & F3 & F4).
    unfold estart in *. cbn [a_base a_off] in *. change (bv_unsigned (edenot E be)) with (uE E be) in *.
    assert (AD : adenot E (SA be a) = Mem.wa (uE E be + a)) by (unfold Mem.wa; apply bv_eq; rewrite FU, u64_lit by lia; reflexivity).
    rewrite AD, LibBridge.rdn_lib in Hr.
    pose proof (LibBridge.rdn_bytes_at MR (word_to_le_bytes 8 (edenot E e)) (uE E be + a) ltac:(lia) ltac:(rewrite CatExec.length_N_to_le_bytes; cbn; lia)) as BA.
    rewrite CatExec.length_N_to_le_bytes in BA. specialize (BA Hr). destruct BA as (_ & _ & BA).
    unfold Mem.le8. split.
    - split; [lia|]. split; [rewrite CatExec.length_N_to_le_bytes; cbn; lia|]. intros i Hi.
      specialize (BA i Hi). destruct (nth_error (word_to_le_bytes 8 (edenot E e)) i) as [bt|] eqn:Hn; [| apply nth_error_None in Hn; lia].
      exact (proj1 (mrd_MR_FULL _ _ BA)).
    - split; [lia|]. split; [cbn; lia|]. intros i Hi. apply (wr_evs_sound 8 be a W i); cbn; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma zero_ok_sound : forall be a n, 0 < n -> zero_ok (kn hs) be a n = true ->
    BYTES FULL (uE E be + a) (repeat (Z_to_bv 8 0) (Z.to_nat n)) /\ WR FULL (uE E be + a) n.
  Proof.
    intros be a n Hn H. unfold zero_ok in H. apply existsb_exists in H as (K & HK & HM). pose proof (fact_in _ HK) as X.
    assert (G : 0 <= uE E be + a /\ uE E be + a + n <= 2 ^ 64 /\
                forall i, 0 <= i < n -> Mem.mrd AImages.asegs FULL (Mem.wa (uE E be + a + i)) = Some (Z_to_bv 8 0) /\ wview AImages.asegs FULL (Mem.wa (uE E be + a + i)) <> None).
    { destruct K as [[b o] w v|[b o] nn|[b o] nn kb|lo hi|e m|e rlo rhi|[b o] nn|a1 n1 a2 n2|[b o] nn fc|[b o] nn]; try discriminate.
      - (* [comment removed for export] *) destruct nn as [m|?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ? ?|? ? ? ?]; try discriminate.
        apply andb_prop in HM as [HM C4]. apply andb_prop in HM as [HM C3]. apply andb_prop in HM as [C1 C2]. apply expr_eqb_true in C1. subst b. apply Z.leb_le in C2. apply Z.leb_le in C3.
        unfold u64b in C4. apply andb_prop in C4 as [C4 C5]. apply Z.leb_le in C4. apply Z.ltb_lt in C5.
        cbn [kentry_ok] in X. destruct X as (Hf & Hz). pose proof Hf as (F1 & F2 & F3 & F4). unfold estart, elenZ in *. cbn [a_base a_off edenot] in *.
        rewrite u64_lit in * by lia. change (bv_unsigned (edenot E be)) with (uE E be) in *.
        split; [lia|]. split; [lia|]. intros i Hi.
        assert (Z0 : MR (Mem.wa (uE E be + a + i)) = Some (Z_to_bv 8 0)).
        { unfold Mem.wa. replace (uE E be + a + i) with (uE E be + o + (a - o + i)) by lia. apply Hz. lia. }
        split; [exact (proj1 (mrd_MR_FULL _ _ ltac:(unfold Mem.mrd; rewrite Z0; reflexivity)))|].
        apply wview_MR_FULL. unfold wview. rewrite Z0. discriminate.
      - (* [comment removed for export] *)
        destruct (is_abs be && (lo <=? a) && (a + n <=? hi) && (A_RW_LO <=? a))%bool eqn:C; [|discriminate].
        apply andb_prop in C as [C C4]. apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2].
        unfold is_abs in C1. apply expr_eqb_true in C1. subst be. apply Z.leb_le in C2. apply Z.leb_le in C3. apply Z.leb_le in C4. unfold A_RW_LO in C4.
        cbn [kentry_ok] in X. destruct X as (L1 & L2 & Hnone).
        replace (uE E (ELit 0)) with 0 in * by (unfold uE; cbn [edenot]; rewrite u64_lit by lia; reflexivity). rewrite Z.add_0_l.
        assert (IZ : forall i, 0 <= i < n -> img_byte (a + i) = Some (Z_to_bv 8 0)).
        { intros i Hi. destruct ((A_BSS_LO <=? a) && (a + n <=? A_IMG_HI))%bool eqn:B.
          - apply andb_prop in B as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2. apply bss_zero. lia.
          - apply (img_zero_sound (Z.to_nat n) a HM). lia. }
        split; [lia|]. split; [lia|]. intros i Hi. specialize (IZ i Hi).
        pose proof (img_byte_inside (a + i) _ ltac:(lia) IZ) as IN.
        assert (FN : FULL (Mem.wa (a + i)) = None).
        { rewrite <- (A_MainFacts.Mr_hull sp rdraw hw argv envp uid Hsp Hva E FULL model hs) by (unfold Mem.wa, A_MainFacts.A_IMG_LO, A_MainFacts.A_IMG_HI; rewrite u64_lit by lia; lia).
          unfold Mem.wa. apply Hnone. lia. }
        split; [unfold Mem.mrd; rewrite FN; exact IZ|].
        apply AsanPlanImages5.asan_rw_window. unfold Mem.wa. rewrite u64_lit by lia. lia. }
    destruct G as (G1 & G2 & G3). split.
    - split; [lia|]. split; [rewrite repeat_length; lia|]. intros i Hi. rewrite repeat_length in Hi.
      rewrite (proj1 (G3 (Z.of_nat i) ltac:(lia))). symmetry. apply nth_error_repeat. exact Hi.
    - split; [lia|]. split; [lia|]. intros i Hi. exact (proj2 (G3 i Hi)).
  Qed.

  Lemma lit_cell_sound : forall be a bs, bs <> [] -> lbytes_ok (kn hs) be a bs = true ->
    BYTES FULL (uE E be + a) bs /\ WR FULL (uE E be + a) (Z.of_nat (length bs)).
  Proof. intros be a bs Hne H. apply byteP_bytes_at; [exact Hne|]. exact (lbytes_ok_sound bs be a H). Qed.

  Lemma lit_bytes_ne : forall w z, (0 < w)%nat -> lit_bytes w z <> [].
  Proof. intros w z Hw E0. apply (f_equal (@length byte)) in E0. unfold lit_bytes in E0. rewrite CatExec.length_N_to_le_bytes in E0. cbn in E0. lia. Qed.

  Lemma cx_ok_sound : forall be a c, cx_ok (kn hs) be a c = true ->
    cx_prop E FULL (uE E be + a) c /\ WR FULL (uE E be + a) (cx_len c).
  Proof.
    intros be a c H. destruct c as [[z|e]|z|z|z|zs|n|n]; cbn [cx_ok cx_prop cx_len xv_den] in H |- *.
    - pose proof (lit_cell_sound be a _ (lit_bytes_ne 8 z ltac:(lia)) H) as [B W]. unfold lit_bytes in *. rewrite CatExec.length_N_to_le_bytes in W. exact (conj B W).
    - apply andb_prop in H as [H1 H2]. exact (word_ok_sound be a e H1 H2).
    - pose proof (lit_cell_sound be a _ (lit_bytes_ne 4 z ltac:(lia)) H) as [B W]. unfold lit_bytes, Mem.le4 in *. rewrite CatExec.length_N_to_le_bytes in W.
      split; [| exact W]. eapply Mem.bytes_at_ext; [exact B|]. unfold word_to_le_bytes. reflexivity.
    - pose proof (lit_cell_sound be a _ (lit_bytes_ne 2 z ltac:(lia)) H) as [B W]. unfold lit_bytes, Mem.le2 in *. rewrite CatExec.length_N_to_le_bytes in W.
      split; [| exact W]. eapply Mem.bytes_at_ext; [exact B|]. unfold word_to_le_bytes. reflexivity.
    - pose proof (lit_cell_sound be a _ (lit_bytes_ne 1 z ltac:(lia)) H) as [B W]. unfold lit_bytes in *. rewrite CatExec.length_N_to_le_bytes in W.
      split; [| exact W]. eapply Mem.bytes_at_ext; [exact B|]. apply w2lb_1.
    - destruct zs as [|z0 zs']; [discriminate|]. pose proof (lit_cell_sound be a (map (Z_to_bv 8) (z0 :: zs')) ltac:(cbn; discriminate) H) as [B W]. rewrite length_map in W. exact (conj B W).
    - apply andb_prop in H as [H1 H2]. apply Z.ltb_lt in H1. exact (zero_ok_sound be a n H1 H2).
    - apply andb_prop in H as [H1 H2]. apply Z.ltb_lt in H1.
      destruct (anyP_bytes_at (uE E be + a) (Z.to_nat n) ltac:(lia) (any_ok_sound _ be a H2)) as (bs & L & B & W).
      rewrite Z2Nat.id in W by lia. split; [| exact W]. exists bs. split; [lia | exact B].
  Qed.

  Lemma cx_len_pos : forall be a c, cx_ok (kn hs) be a c = true -> 0 < cx_len c.
  Proof.
    intros be a c H. destruct c as [[z|e]|z|z|z|zs|n|n]; cbn [cx_ok cx_len] in H |- *; try lia.
    all: try (destruct zs; [discriminate | cbn; lia]).
    all: apply andb_prop in H as [H _]; apply Z.ltb_lt in H; lia.
  Qed.

  Lemma wr_at_app : forall A n1 n2, 0 <= n1 -> 0 <= n2 -> WR FULL A n1 -> WR FULL (A + n1) n2 -> WR FULL A (n1 + n2).
  Proof.
    intros A n1 n2 H1 H2 (W1 & W2 & W3) (V1 & V2 & V3). split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_le_dec i n1); [apply W3; lia|]. replace (A + i) with (A + n1 + (i - n1)) by lia. apply V3. lia.
  Qed.

  Lemma cxs_len_nonneg : forall k be a l, cxs_okk k be a l = true -> k = kn hs -> 0 <= cxs_len l.
  Proof.
    intros k be a l. revert a. induction l as [|c l IH]; intros a H ->; cbn [cxs_len]; [lia|].
    cbn [cxs_okk] in H. apply andb_prop in H as [H1 H2]. pose proof (cx_len_pos be a c H1). pose proof (IH _ H2 eq_refl). lia.
  Qed.

  Lemma cxs_okk_sound : forall l be a, cxs_okk (kn hs) be a l = true -> l <> [] ->
    cxs_prop E FULL (uE E be + a) l /\ WR FULL (uE E be + a) (cxs_len l).
  Proof.
    induction l as [|c l IH]; intros be a H Hne; [congruence|]. cbn [cxs_okk] in H. apply andb_prop in H as [H1 H2].
    destruct (cx_ok_sound be a c H1) as [P W]. cbn [cxs_prop cxs_len].
    destruct l as [|c2 l'].
    - cbn [cxs_prop cxs_len]. rewrite Z.add_0_r. split; [split; [exact P | exact I] | exact W].
    - destruct (IH be (a + cx_len c) H2 ltac:(discriminate)) as [P2 W2].
      replace (uE E be + (a + cx_len c)) with (uE E be + a + cx_len c) in P2 by lia.
      replace (uE E be + (a + cx_len c)) with (uE E be + a + cx_len c) in W2 by lia.
      split; [exact (conj P P2)|]. apply wr_at_app; [pose proof (cx_len_pos be a c H1); lia | exact (cxs_len_nonneg _ be _ _ H2 eq_refl) | exact W | exact W2].
  Qed.

  (* [comment removed for export] *)
  Theorem cxs_sound : forall be a l, cxs_ok be a l = true ->
    cxs_prop E FULL (uE E be + a) l /\ WR FULL (uE E be + a) (cxs_len l).
  Proof.
    intros be a l H. unfold cxs_ok in H. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H H2]. apply andb_prop in H as [H0 H1]. apply Z.ltb_lt in H0.
    assert (Hne : l <> []) by (intros ->; cbn in H0; lia).
    destruct Hhs as [Eh|[Eh|[Eh|Eh]]]; [pose proof H1 as X | pose proof H2 as X | pose proof H3 as X | pose proof H4 as X]; rewrite <- Eh in X; exact (cxs_okk_sound l be a X Hne).
  Qed.
End Sound.

(* [comment removed for export] *)
Definition cx_cell (E : env) (c : cx) : Cells.cell :=
  match c with
  | CX8 v => Cells.C8 (xv_den E v) | CX4 z => Cells.C4 (Z_to_bv 64 z) | CX2 z => Cells.C2 (Z_to_bv 64 z) | CX1 z => Cells.C1 (Z_to_bv 8 z)
  | CXB zs => Cells.CB (length zs) (map (Z_to_bv 8) zs)
  | CXZ n => Cells.CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))
  | CXA n => Cells.CB 0 []
  end.
Definition not_any (c : cx) : bool := match c with CXA _ => false | _ => true end.

Lemma cx_cell_wf : forall E c, Cells.cell_wf (cx_cell E c).
Proof. intros E c. destruct c as [v|z|z|z|zs|n|n]; cbn; try exact I; rewrite ?length_map, ?repeat_length; reflexivity. Qed.

Lemma cx_cell_size : forall E c, not_any c = true -> 0 <= cx_len c -> Z.of_nat (Cells.csize (cx_cell E c)) = cx_len c.
Proof. intros E c H Hn. destruct c as [v|z|z|z|zs|n|n]; cbn -[Z.of_nat Z.to_nat] in *; try lia; discriminate. Qed.

Section Cells.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variable hw : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable uid : word.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Variable E : env.
  Variable R : bvmap 5 word.
  Variable FULL : word -> option byte.
  Variable model : Model.
  Variable hs : acs.
  Hypothesis Hhs : HS_MAIN hs.
  Hypothesis HC : cs_ok ASEGS ASAN5 AsanInit.LIMIT (SINV0 APH sp rdraw brk0 argv envp uid hw) (argH0 APH sp rdraw argv envp uid hw) fs E hs R FULL model.

  #[local] Notation BYTES := (Mem.bytes_at AImages.asegs).

  Lemma cx_prop_bytes : forall A c, not_any c = true -> cx_prop E FULL A c -> BYTES FULL A (Cells.cbytes (cx_cell E c)).
  Proof. intros A c Hna P. destruct c as [v|z|z|z|zs|n|n]; cbn [cx_prop cx_cell Cells.cbytes] in *; try exact P. discriminate. Qed.

  Lemma cx_cell_len : forall c, not_any c = true -> Z.of_nat (length (Cells.cbytes (cx_cell E c))) = Z.max 0 (cx_len c).
  Proof.
    intros c Hc. rewrite Cells.cbytes_length by apply cx_cell_wf.
    destruct c as [v|z|z|z|zs|n|n]; cbn [Cells.csize cx_cell cx_len]; rewrite ?length_map; try lia. discriminate Hc.
  Qed.

  Lemma cxs_prop_bytes : forall l A be a, l <> [] -> forallb not_any l = true -> cxs_okk (kn hs) be a l = true -> cxs_prop E FULL A l ->
    BYTES FULL A (Cells.cells_bytes (map (cx_cell E) l)) /\ Z.of_nat (Cells.cells_size (map (cx_cell E) l)) = cxs_len l.
  Proof.
    induction l as [|c l IH]; intros A be a Hne Hna OK P; [congruence|].
    cbn [forallb] in Hna. apply andb_prop in Hna as [Hc Hl]. cbn [cxs_okk] in OK. apply andb_prop in OK as [O1 O2].
    pose proof (cx_len_pos hs be a c O1) as LP.
    cbn [map Cells.cells_bytes Cells.cells_size cxs_prop cxs_len] in *. destruct P as [P1 P2].
    pose proof (cx_prop_bytes A c Hc P1) as B1. pose proof (cx_cell_len c Hc) as L1.
    assert (SZ : Z.of_nat (Cells.csize (cx_cell E c)) = cx_len c) by (rewrite <- (Cells.cbytes_length _ (cx_cell_wf E c)); lia).
    destruct l as [|c2 l'].
    - cbn [map Cells.cells_bytes Cells.cells_size cxs_len]. rewrite app_nil_r, Nat.add_0_r, Z.add_0_r. exact (conj B1 SZ).
    - destruct (IH (A + cx_len c) be (a + cx_len c) ltac:(discriminate) Hl O2 P2) as [B2 S2].
      split; [| rewrite Nat2Z.inj_add, SZ, S2; reflexivity].
      apply (proj2 (Mem.bytes_at_app _ _ _ _ _)). split; [exact B1|]. replace (A + Z.of_nat (length (Cells.cbytes (cx_cell E c)))) with (A + cx_len c) by lia. exact B2.
  Qed.

  Lemma cxs_cells_wf : forall l, Cells.cells_wf (map (cx_cell E) l).
  Proof. induction l as [|c l IH]; cbn; [exact I|]. split; [apply cx_cell_wf | exact IH]. Qed.

  (* [comment removed for export] *)
  Theorem cxs_rw : forall be a l, cxs_ok be a l = true -> forallb not_any l = true ->
    Step.rw_cells AImages.asegs FULL (uE E be + a) (map (cx_cell E) l).
  Proof.
    intros be a l H Hna. pose proof (cxs_sound sp rdraw brk0 hw argv envp fs uid Hsp Hva E R FULL model hs Hhs HC be a l H) as [P W].
    unfold cxs_ok in H. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H H2]. apply andb_prop in H as [H0 H1]. apply Z.ltb_lt in H0.
    assert (Hne : l <> []) by (intros ->; cbn in H0; lia).
    assert (OK : cxs_okk (kn hs) be a l = true) by (destruct Hhs as [-> | [-> | [-> | ->]]]; assumption).
    destruct (cxs_prop_bytes l (uE E be + a) be a Hne Hna OK P) as [B S].
    split; [split; [apply cxs_cells_wf | exact B]|]. rewrite S. exact W.
  Qed.

  (* [comment removed for export] *)
  Theorem cxs_u8 : forall be a l, cxs_ok be a l = true -> forallb not_any l = true ->
    Arr.u8arr AImages.asegs FULL (uE E be + a) (Cells.cells_bytes (map (cx_cell E) l)).
  Proof.
    intros be a l H Hna. destruct (cxs_rw be a l H Hna) as [[WF B] W]. split; [exact B|].
    rewrite (Cells.cells_bytes_length _ (cxs_cells_wf l)). exact W.
  Qed.

  (* [comment removed for export] *)
  Theorem cxs_u8_1 : forall be a c, cxs_ok be a [c] = true -> not_any c = true ->
    Arr.u8arr AImages.asegs FULL (uE E be + a) (Cells.cbytes (cx_cell E c)).
  Proof.
    intros be a c H Hc. pose proof (cxs_u8 be a [c] H ltac:(cbn; rewrite Hc; reflexivity)) as X.
    cbn [map Cells.cells_bytes] in X. rewrite app_nil_r in X. exact X.
  Qed.

  (* [comment removed for export] *)
  Theorem cxs_zero : forall be a n, cxs_ok be a [CXZ n] = true ->
    Arr.u8arr AImages.asegs FULL (uE E be + a) (repeat (Z_to_bv 8 0) (Z.to_nat n)).
  Proof. intros be a n H. exact (cxs_u8_1 be a (CXZ n) H eq_refl). Qed.

  (* [comment removed for export] *)
  Theorem cxs_rw_k : forall be a l, 0 < cxs_len l -> cxs_okk (kn hs) be a l = true -> forallb not_any l = true ->
    Step.rw_cells AImages.asegs FULL (uE E be + a) (map (cx_cell E) l).
  Proof.
    intros be a l Hl H Hna. assert (Hne : l <> []) by (intros ->; cbn in Hl; lia).
    pose proof (cxs_okk_sound sp rdraw brk0 hw argv envp fs uid Hsp Hva E R FULL model hs HC l be a H Hne) as [P W].
    destruct (cxs_prop_bytes l (uE E be + a) be a Hne Hna H P) as [B S].
    split; [split; [apply cxs_cells_wf | exact B]|]. rewrite S. exact W.
  Qed.
  Theorem cxs_sound_k : forall be a l, 0 < cxs_len l -> cxs_okk (kn hs) be a l = true ->
    cxs_prop E FULL (uE E be + a) l /\ Mem.wr_at AImages.asegs FULL (uE E be + a) (cxs_len l).
  Proof.
    intros be a l Hl H. assert (Hne : l <> []) by (intros ->; cbn in Hl; lia).
    exact (cxs_okk_sound sp rdraw brk0 hw argv envp fs uid Hsp Hva E R FULL model hs HC l be a H Hne).
  Qed.
  Theorem cxs_zero_k : forall be a n, 0 < n -> cxs_okk (kn hs) be a [CXZ n] = true ->
    Arr.u8arr AImages.asegs FULL (uE E be + a) (repeat (Z_to_bv 8 0) (Z.to_nat n)).
  Proof.
    intros be a n Hn H. destruct (cxs_rw_k be a [CXZ n] ltac:(cbn; lia) H eq_refl) as [[WF B] W].
    cbn [map Cells.cells_bytes Cells.cells_size cx_cell Cells.cbytes Cells.csize] in B, W. rewrite app_nil_r in B. rewrite Nat.add_0_r in W.
    split; [exact B|]. rewrite repeat_length. exact W.
  Qed.

  (* [comment removed for export] *)
  Lemma u_abs : forall a, uE E (ELit 0) + a = a.
  Proof. intros a. unfold uE. cbn [edenot]. rewrite u64_lit by lia. lia. Qed.
End Cells.
