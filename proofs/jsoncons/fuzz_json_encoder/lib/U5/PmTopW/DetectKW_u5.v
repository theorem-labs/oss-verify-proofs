(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun L5Defs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmRef_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module DKW.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition M64 : Z := 18446744073709551616.
Lemma M64_eq : M64 = 2 ^ 64. Proof. reflexivity. Qed.
Definition w64 (z : Z) : Z := z mod M64.
Definition bget (B : nat -> Z) (sx : bool) (i : Z) : Z := let u := B (Z.to_nat i) in if sx then (if u <? 128 then u else M64 - 256 + u) else u.
Fixpoint zevb (B : nat -> Z) (e : expr) : option Z :=
  match e with
  | ELit z => Some (w64 z)
  | EBlob sx O i (S O) => if 0 <=? i then Some (bget B sx i) else None
  | EAlu op a b =>
      match zevb B a, zevb B b with
      | Some x, Some y =>
          match op with
          | ALU_ADD => Some (w64 (x + y))
          | ALU_SUB => Some (w64 (x - y))
          | ALU_AND => Some (Z.land x y)
          | ALU_SRL => Some (Z.shiftr x (Z.land y 63))
          | ALU_SLTU => Some (if x <? y then 1 else 0)
          | _ => None
          end
      | _, _ => None
      end
  | EMd M_MUL a b => match zevb B a, zevb B b with Some x, Some y => Some (w64 (x * y)) | _, _ => None end
  | _ => None
  end.

Definition brange (s : list Z) : Prop := Forall (fun b => 0 <= b <= 255) s.
Definition Bof (s : list Z) : nat -> Z := fun n => nth n s 0.
Lemma Bof_range : forall s n, brange s -> 0 <= Bof s n <= 255.
Proof.
  intros s n H. unfold Bof. destruct (Nat.lt_ge_cases n (length s)) as [L|L].
  - exact (proj1 (Forall_nth _ _) H n 0 L). 
  - rewrite nth_overflow by lia. lia.
Qed.
Lemma nth_skipn0 : forall {A} n (l : list A) d, nth n l d = nth 0 (skipn n l) d.
Proof. intros A n. induction n as [|n IH]; intros [|x r] d; cbn; try reflexivity. apply IH. Qed.
Lemma modulus64 : bv_modulus 64 = 2 ^ 64. Proof. reflexivity. Qed.
Lemma lit64_u : forall z, bv_unsigned (Z_to_bv 64 z) = w64 z.
Proof. intros z. rewrite Z_to_bv_unsigned. unfold bv_wrap, w64. rewrite modulus64, M64_eq. reflexivity. Qed.
Lemma u64_range : forall b : bv 64, 0 <= bv_unsigned b < 2 ^ 64.
Proof. intros b. pose proof (bv_unsigned_in_range 64 b) as H. rewrite modulus64 in H. lia. Qed.
Lemma blob_val_1 : forall s (sx : bool) i, 0 <= i -> brange s -> bv_unsigned (blob_val sx (map (Z_to_bv 8) s) i 1) = bget (Bof s) sx i.
Proof.
  intros s sx i Hi Hs. unfold blob_val, blob_bytes, bget, Bof. rewrite skipn_map, firstn_map. rewrite lit64_u.
  pose proof (Bof_range s (Z.to_nat i) Hs) as R. unfold Bof in R. rewrite (nth_skipn0 (Z.to_nat i) s 0) in *.
  destruct (skipn (Z.to_nat i) s) as [|b r]; cbn [firstn map nth] in *.
  - change (bytes_le_to_Z []) with 0. destruct sx; reflexivity.
  - rewrite bytes_le_single. rewrite Z_to_bv_unsigned. change (bv_wrap 8 b) with (b mod 2 ^ 8). rewrite Z.mod_small by lia. cbv zeta.
    destruct sx.
    + unfold bv_swrap, bv_wrap, bv_half_modulus. change (bv_modulus (8 * N.of_nat 1)) with 256. change (256 `div` 2) with 128.
      unfold w64. rewrite M64_eq. destruct (Z.ltb_spec b 128) as [L|L].
      * rewrite (Z.mod_small (b + 128) 256) by lia. rewrite Z.mod_small by lia. lia.
      * rewrite <- (Z.mod_add (b + 128) (-1) 256) by lia. rewrite (Z.mod_small (b + 128 + -1 * 256) 256) by lia.
        rewrite <- (Z.mod_add _ 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
    + unfold w64. rewrite M64_eq. rewrite Z.mod_small by lia. reflexivity.
Qed.

Section Sound.
Variable E : env.
Variable s : list Z.
Hypothesis EB : eb E 0%nat = map (Z_to_bv 8) s.
Hypothesis BR : brange s.
Theorem zevb_sound : forall e v, zevb (Bof s) e = Some v -> bv_unsigned (edenot E e) = v.
Proof.
  induction e as [z0|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx k i n]; intros v H; cbn [zevb] in H; cbn [edenot]; try discriminate H.
  - injection H as <-. apply lit64_u.
  - destruct (zevb (Bof s) a) as [x|] eqn:Ha; [|discriminate H]. destruct (zevb (Bof s) b) as [y|] eqn:Hb; [|destruct op; discriminate H].
    rewrite <- (IHa x eq_refl), <- (IHb y eq_refl) in H. unfold alu64, alu. destruct op; try discriminate H; injection H as <-.
    + rewrite bv_add_unsigned. unfold bv_wrap, w64. rewrite modulus64, M64_eq. reflexivity.
    + rewrite bv_sub_unsigned. unfold bv_wrap, w64. rewrite modulus64, M64_eq. reflexivity.
    + unfold bv_ltu. destruct (_ <? _); reflexivity.
    + rewrite bv_shiftr_unsigned, bv_and_unsigned. change (bv_unsigned (Z_to_bv 64 63)) with 63. reflexivity.
    + apply bv_and_unsigned.
  - destruct op; try discriminate H.
    destruct (zevb (Bof s) a) as [x|] eqn:Ha; [|discriminate H]. destruct (zevb (Bof s) b) as [y|] eqn:Hb; [|discriminate H]. injection H as <-.
    rewrite <- (IHa x eq_refl), <- (IHb y eq_refl). unfold mul_div. rewrite bv_mul_unsigned. unfold bv_wrap, w64. rewrite modulus64, M64_eq. reflexivity.
  - destruct k; [|discriminate H]. destruct n as [|[|n]]; try discriminate H. destruct (Z.leb_spec 0 i) as [Hi|Hi]; [|discriminate H]. injection H as <-.
    rewrite EB. apply blob_val_1; [exact Hi | exact BR].
Qed.
Lemma range_fact : forall e v lo hi, zevb (Bof s) e = Some v -> lo <= bv_unsigned (edenot E e) <= hi -> lo <= v <= hi.
Proof. intros e v lo hi Hz H. rewrite (zevb_sound e v Hz) in H. exact H. Qed.
End Sound.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SPEC : list Z := [0; 187; 191; 239; 254; 255].
Definition special (z : Z) : bool := existsb (Z.eqb z) SPEC.
Definition canon (z : Z) : Z := if special z then z else 1.
Definition REPS : list Z := 1 :: SPEC.
Lemma canon_special : forall z, special z = true -> canon z = z.
Proof. intros z H. unfold canon. rewrite H. reflexivity. Qed.
Lemma canon_in : forall z, In (canon z) REPS.
Proof.
  intros z. unfold canon. destruct (special z) eqn:H; [|left; reflexivity]. right.
  unfold special in H. apply existsb_exists in H as (x & Hx & E). apply Z.eqb_eq in E. subst x. exact Hx.
Qed.
Lemma canon_range : forall z, 0 <= canon z <= 255.
Proof. intros z. pose proof (canon_in z) as H. unfold REPS, SPEC in H. cbn [In app] in H. lia. Qed.
Lemma canon_idem : forall z, canon (canon z) = canon z.
Proof. intros z. unfold canon. destruct (special z) eqn:H; [rewrite H; reflexivity | reflexivity]. Qed.
(* [comment removed for export] *)
Lemma ceq_l : forall a b, special a = true -> (a =? canon b) = (a =? b).
Proof.
  intros a b Ha. unfold canon. destruct (special b) eqn:Hb; [reflexivity|].
  destruct (Z.eqb_spec a 1) as [->|N]; [discriminate Ha|]. destruct (Z.eqb_spec a b) as [->|N2]; [rewrite Ha in Hb; discriminate Hb | reflexivity].
Qed.
Lemma ceq_r : forall a b, special a = true -> (canon b =? a) = (b =? a).
Proof. intros a b Ha. rewrite (Z.eqb_sym (canon b) a), (Z.eqb_sym b a). apply ceq_l. exact Ha. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma detect_first4 : forall s, PMR.detect s = PMR.detect (firstn 4 s).
Proof. intros [|b0 [|b1 [|b2 [|b3 r]]]]; reflexivity. Qed.
Lemma detect_canon : forall s, PMR.detect (map canon s) = PMR.detect s.
Proof.
  intros s. rewrite (detect_first4 (map canon s)), (detect_first4 s). rewrite firstn_map.
  destruct s as [|b0 [|b1 [|b2 [|b3 r]]]]; cbn [firstn map]; [reflexivity| | | |];
    unfold PMR.detect, PMR.pfx; cbn [length Nat.leb Nat.ltb combine forallb fst snd andb];
    rewrite ?(ceq_l 255), ?(ceq_l 254), ?(ceq_l 0), ?(ceq_l 239), ?(ceq_l 187), ?(ceq_l 191), ?(ceq_r 0) by reflexivity; reflexivity.
Qed.
Lemma detect_le : forall s j, PMR.detect s = Some j -> (j <= 3 /\ j <= length s)%nat.
Proof.
  intros s j H. unfold PMR.detect in H.
  destruct (PMR.pfx [255; 254; 0; 0] s); [discriminate H|]. destruct (PMR.pfx [0; 0; 254; 255] s); [discriminate H|].
  destruct (PMR.pfx [255; 254] s); [discriminate H|]. destruct (PMR.pfx [254; 255] s); [discriminate H|].
  destruct (PMR.pfx [239; 187; 191] s) eqn:P3.
  - injection H as <-. unfold PMR.pfx in P3. apply andb_prop in P3 as [P3 _]. apply Nat.leb_le in P3. cbn [length] in P3. lia.
  - destruct (Nat.ltb_spec (length s) 4) as [L|L]; [injection H as <-; lia|].
    destruct s as [|b0 [|b1 [|b2 [|b3 r]]]]; cbn [length] in L; try lia.
    repeat match goal with H : (if ?c then _ else _) = Some j |- _ => destruct c; [try discriminate H|] end; injection H as <-; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint bpos (e : expr) : option (list nat) :=
  match e with
  | ELit _ => Some []
  | EBlob _ O i (S O) => if 0 <=? i then Some [Z.to_nat i] else None
  | EAlu _ a b | EMd _ a b => match bpos a, bpos b with Some x, Some y => Some (x ++ y) | _, _ => None end
  | _ => None
  end.
Lemma zevb_agree : forall e l B B', bpos e = Some l -> (forall i, In i l -> B i = B' i) -> zevb B e = zevb B' e.
Proof.
  induction e as [z0|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx k i n]; intros l B B' H AG; cbn [bpos] in H; try discriminate H; cbn [zevb].
  - reflexivity.
  - destruct (bpos a) as [x|] eqn:Ha; [|discriminate H]. destruct (bpos b) as [y|] eqn:Hb; [|discriminate H]. injection H as <-.
    rewrite (IHa x B B' eq_refl) by (intros j Hj; apply AG; apply in_or_app; left; exact Hj).
    rewrite (IHb y B B' eq_refl) by (intros j Hj; apply AG; apply in_or_app; right; exact Hj). reflexivity.
  - destruct (bpos a) as [x|] eqn:Ha; [|discriminate H]. destruct (bpos b) as [y|] eqn:Hb; [|discriminate H]. injection H as <-.
    rewrite (IHa x B B' eq_refl) by (intros j Hj; apply AG; apply in_or_app; left; exact Hj).
    rewrite (IHb y B B' eq_refl) by (intros j Hj; apply AG; apply in_or_app; right; exact Hj). reflexivity.
  - destruct k; [|discriminate H]. destruct n as [|[|n]]; try discriminate H. destruct (0 <=? i); [|discriminate H]. injection H as <-.
    unfold bget. rewrite (AG (Z.to_nat i)) by (left; reflexivity). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition W4X : expr :=
  EAlu ALU_ADD (EBlob false 0 0 1) (EAlu ALU_ADD (EMd M_MUL (ELit 256) (EBlob false 0 1 1))
                                     (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EBlob false 0 2 1)) (EMd M_MUL (ELit 16777216) (EBlob true 0 3 1)))).
Definition w4_atom (K : kentry) : option (bool * list Z) :=
  match K with
  | KRange (EAlu ALU_SLTU (EAlu ALU_SUB e (ELit c)) (ELit 1)) lo hi =>
      if expr_eqb e W4X then
        match (if (lo =? 1) && (hi =? 1) then Some true else if (lo =? 0) && (hi =? 0) then Some false else None) with
        | Some pos => if c =? 65279 then Some (pos, [255; 254; 0; 0]) else if c =? 18446744073709420544 then Some (pos, [0; 0; 254; 255]) else None
        | None => None
        end
      else None
  | _ => None
  end.
Definition w4val (B : nat -> Z) : Z :=
  let u3 := B 3%nat in B 0%nat + 256 * B 1%nat + 65536 * B 2%nat + 16777216 * u3 + (if u3 <? 128 then 0 else 2 ^ 64 - 2 ^ 32).
Arguments M64 : simpl never.
Lemma w64_small : forall z, 0 <= z < 2 ^ 64 -> w64 z = z. Proof. intros z H. unfold w64. rewrite M64_eq. apply Z.mod_small. exact H. Qed.
Lemma w64_big : forall z, 2 ^ 64 <= z < 2 * 2 ^ 64 -> w64 z = z - 2 ^ 64.
Proof. intros z H. unfold w64. rewrite M64_eq. rewrite <- (Z.mod_add z (-1) (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia. Qed.
Lemma w64_sx3 : forall u, 128 <= u <= 255 -> w64 (16777216 * (M64 - 256 + u)) = 2 ^ 64 - 2 ^ 32 + 16777216 * u.
Proof.
  intros u Hu. unfold w64. rewrite M64_eq. replace (16777216 * (2 ^ 64 - 256 + u)) with ((16777216 * u - 2 ^ 32 + 2 ^ 64) + (16777216 - 1) * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma zevb_W4X : forall B, (forall i, 0 <= B i <= 255) -> zevb B W4X = Some (w4val B).
Proof.
  intros B HB. pose proof (HB 0%nat) as H0. pose proof (HB 1%nat) as H1. pose proof (HB 2%nat) as H2. pose proof (HB 3%nat) as H3.
  unfold W4X. cbn [zevb Z.leb Z.to_nat Pos.to_nat bget]. cbv iota. cbn [Z.to_nat].
  change (Z.to_nat 0) with 0%nat. change (Z.to_nat 1) with 1%nat. change (Z.to_nat 2) with 2%nat. change (Z.to_nat 3) with 3%nat.
  f_equal. unfold w4val. rewrite (w64_small 256), (w64_small 65536), (w64_small 16777216) by lia.
  rewrite (w64_small (256 * B 1%nat)), (w64_small (65536 * B 2%nat)) by lia.
  destruct (Z.ltb_spec (B 3%nat) 128) as [L|L].
  - rewrite (w64_small (16777216 * B 3%nat)) by lia.
    rewrite (w64_small (65536 * B 2%nat + 16777216 * B 3%nat)) by lia.
    rewrite (w64_small (256 * B 1%nat + (65536 * B 2%nat + 16777216 * B 3%nat))) by lia.
    rewrite w64_small by lia. lia.
  - rewrite (w64_sx3 (B 3%nat)) by lia.
    rewrite (w64_small (65536 * B 2%nat + (2 ^ 64 - 2 ^ 32 + 16777216 * B 3%nat))) by lia.
    rewrite (w64_small (256 * B 1%nat + (65536 * B 2%nat + (2 ^ 64 - 2 ^ 32 + 16777216 * B 3%nat)))) by lia.
    rewrite w64_small by lia. lia.
Qed.
Lemma canon_eq_special : forall z c, special c = true -> canon z = c -> z = c.
Proof. intros z c Hc H. unfold canon in H. destruct (special z); [exact H | subst c; discriminate Hc]. Qed.
Lemma w4_sound : forall E s K pos d, eb E 0%nat = map (Z_to_bv 8) s -> brange s -> w4_atom K = Some (pos, d) -> (exists M, kentry_ok RSEGS E M K) ->
  (pos = true -> map (Bof s) [0; 1; 2; 3]%nat = d) /\ (pos = false -> map (fun n => canon (Bof s n)) [0; 1; 2; 3]%nat <> d) /\ map canon d = d.
Proof.
  intros E s K pos d EB BR HA (M & HK).
  unfold w4_atom in HA. destruct K as [| | | | |e lo hi| | | |]; try discriminate HA.
  destruct e as [| |op e1 e2| | | | |]; try discriminate HA. destruct op; try discriminate HA.
  destruct e1 as [| |op1 e c1| | | | |]; try discriminate HA. destruct op1; try discriminate HA. destruct c1 as [c| | | | | | |]; try discriminate HA.
  destruct e2 as [o| | | | | | |]; try discriminate HA. destruct o as [|p|]; try discriminate HA. destruct p; try discriminate HA.
  destruct (expr_eqb e W4X) eqn:EQ; [|discriminate HA]. apply expr_eqb_eq in EQ. subst e.
  assert (HB : forall i, 0 <= Bof s i <= 255) by (intros i; apply Bof_range; exact BR).
  pose proof (zevb_W4X (Bof s) HB) as ZW.
  assert (ZV : zevb (Bof s) (EAlu ALU_SLTU (EAlu ALU_SUB W4X (ELit c)) (ELit 1)) = Some (if w64 (w4val (Bof s) - w64 c) <? w64 1 then 1 else 0)).
  { cbn [zevb]. rewrite ZW. reflexivity. }
  cbn [kentry_ok] in HK. pose proof (range_fact E s EB BR _ _ lo hi ZV HK) as RF. change (w64 1) with 1 in RF.
  pose proof (HB 0%nat) as H0. pose proof (HB 1%nat) as H1. pose proof (HB 2%nat) as H2. pose proof (HB 3%nat) as H3.
  assert (WR : 0 <= w4val (Bof s) < 2 ^ 64) by (unfold w4val; destruct (Bof s 3%nat <? 128); lia).
  assert (CR : 0 <= w64 c < 2 ^ 64) by (unfold w64; rewrite M64_eq; apply Z.mod_pos_bound; lia).
  assert (DEC : (w64 (w4val (Bof s) - w64 c) <? 1) = (w4val (Bof s) =? w64 c)).
  { destruct (Z.eqb_spec (w4val (Bof s)) (w64 c)) as [X|X].
    - rewrite X, Z.sub_diag. reflexivity.
    - destruct (Z.ltb_spec (w64 (w4val (Bof s) - w64 c)) 1) as [L|L]; [|reflexivity]. exfalso.
      destruct (Z_lt_le_dec (w4val (Bof s)) (w64 c)).
      + unfold w64 at 1 in L. rewrite M64_eq in L. rewrite <- (Z.mod_add _ 1 (2 ^ 64)) in L by lia. rewrite Z.mod_small in L by lia. lia.
      + rewrite (w64_small (w4val (Bof s) - w64 c)) in L by lia. lia. }
  rewrite DEC in RF.
  (* [comment removed for export] *)
  remember (if (lo =? 1) && (hi =? 1) then Some true else if (lo =? 0) && (hi =? 0) then Some false else None) as po eqn:EPO in HA.
  destruct po as [pos'|]; [|discriminate HA].
  assert (PT : pos' = true -> w4val (Bof s) = w64 c).
  { intros ->. destruct ((lo =? 1) && (hi =? 1)) eqn:P1.
    - apply andb_prop in P1 as [P1 P2]. apply Z.eqb_eq in P1. apply Z.eqb_eq in P2. subst lo hi. destruct (Z.eqb_spec (w4val (Bof s)) (w64 c)); [assumption | lia].
    - destruct ((lo =? 0) && (hi =? 0)); discriminate EPO. }
  assert (PF : pos' = false -> w4val (Bof s) <> w64 c).
  { intros ->. destruct ((lo =? 1) && (hi =? 1)) eqn:P1; [discriminate EPO|]. destruct ((lo =? 0) && (hi =? 0)) eqn:P0; [|discriminate EPO].
    apply andb_prop in P0 as [P0 P2]. apply Z.eqb_eq in P0. apply Z.eqb_eq in P2. subst lo hi. destruct (Z.eqb_spec (w4val (Bof s)) (w64 c)); [lia | assumption]. }
  unfold w4val in PT, PF.
  destruct (Z.eqb_spec c 65279) as [->|N1]; [|destruct (Z.eqb_spec c 18446744073709420544) as [->|N2]; [|discriminate HA]]; injection HA as <- <-;
    (split; [|split; [|reflexivity]]); cbn [map].
  - intros P. specialize (PT P). change (w64 65279) with 65279 in PT.
    destruct (Z.ltb_spec (Bof s 3%nat) 128) as [L|L]; [|lia].
    assert (Bof s 3%nat = 0) by lia. assert (Bof s 2%nat = 0) by lia. assert (Bof s 1%nat = 254) by lia. assert (Bof s 0%nat = 255) by lia.
    repeat match goal with H : Bof s _ = _ |- _ => rewrite H; clear H end. reflexivity.
  - intros P X. specialize (PF P). apply PF. change (w64 65279) with 65279. injection X as X0 X1 X2 X3.
    apply (canon_eq_special _ 255 eq_refl) in X0. apply (canon_eq_special _ 254 eq_refl) in X1. apply (canon_eq_special _ 0 eq_refl) in X2. apply (canon_eq_special _ 0 eq_refl) in X3.
    unfold w4val. rewrite X0, X1, X2, X3. reflexivity.
  - intros P. specialize (PT P). change (w64 18446744073709420544) with 18446744073709420544 in PT.
    destruct (Z.ltb_spec (Bof s 3%nat) 128) as [L|L]; [lia|].
    assert (Bof s 3%nat = 255) by lia. assert (Bof s 2%nat = 254) by lia. assert (Bof s 1%nat = 0) by lia. assert (Bof s 0%nat = 0) by lia.
    repeat match goal with H : Bof s _ = _ |- _ => rewrite H; clear H end. reflexivity.
  - intros P X. specialize (PF P). apply PF. change (w64 18446744073709420544) with 18446744073709420544. injection X as X0 X1 X2 X3.
    apply (canon_eq_special _ 0 eq_refl) in X0. apply (canon_eq_special _ 0 eq_refl) in X1. apply (canon_eq_special _ 254 eq_refl) in X2. apply (canon_eq_special _ 255 eq_refl) in X3.
    unfold w4val. rewrite X0, X1, X2, X3. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint kbounds (cells : list kentry) : Z * Z :=
  match cells with
  | [] => (0, M64)
  | KRange (EVar v) lo hi :: r => let p := kbounds r in if Nat.eqb v 43 then (Z.max lo (fst p), Z.min hi (snd p)) else p
  | _ :: r => kbounds r
  end.
Lemma kbounds_sound : forall E (M : mem) cells, (forall K, In K cells -> kentry_ok RSEGS E M K) ->
  fst (kbounds cells) <= bv_unsigned (ev E 43) <= snd (kbounds cells).
Proof.
  intros E M cells. induction cells as [|K r IH]; intros H.
  - cbn [kbounds fst snd]. rewrite M64_eq. pose proof (u64_range (ev E 43)). lia.
  - assert (Hr : fst (kbounds r) <= bv_unsigned (ev E 43) <= snd (kbounds r)) by (apply IH; intros K' HK'; apply H; right; exact HK').
    destruct K as [| | | | |e lo hi| | | |]; cbn [kbounds]; try exact Hr. destruct e as [|v| | | | | |]; try exact Hr.
    cbv zeta. destruct (Nat.eqb_spec v 43) as [->|_]; [|exact Hr].
    pose proof (H _ (or_introl eq_refl)) as HK. cbn [kentry_ok edenot] in HK. cbn [fst snd]. lia.
Qed.
(* [comment removed for export] *)
Definition gpos (e : expr) : option (list nat) :=
  match bpos e with Some l => let q := nodup Nat.eq_dec l in if ((length q <=? 2) && forallb (fun i => i <? 4) q)%nat then Some q else None | None => None end.
Fixpoint gcons (cells : list kentry) : list (expr * Z * Z) :=
  match cells with
  | [] => []
  | KRange e lo hi :: r => match gpos e with Some _ => (e, lo, hi) :: gcons r | None => gcons r end
  | _ :: r => gcons r
  end.
Lemma gcons_in : forall cells e lo hi, In (e, lo, hi) (gcons cells) -> In (KRange e lo hi) cells /\ exists q, gpos e = Some q.
Proof.
  intros cells e lo hi. induction cells as [|K r IH]; intros H; [destruct H|].
  assert (STEP : In (e, lo, hi) (gcons r) -> In (KRange e lo hi) (K :: r) /\ (exists q, gpos e = Some q)) by (intros X; destruct (IH X) as [A Q]; split; [right; exact A | exact Q]).
  destruct K as [| | | | |e' lo' hi'| | | |]; cbn [gcons] in H; try exact (STEP H).
  destruct (gpos e') as [q|] eqn:G; [|exact (STEP H)]. destruct H as [H|H]; [|exact (STEP H)].
  injection H as <- <- <-. split; [left; reflexivity | exists q; exact G].
Qed.
Definition inrange (c : expr * Z * Z) (B : nat -> Z) : bool :=
  let '(e, lo, hi) := c in match zevb B e with Some v => (lo <=? v) && (v <=? hi) | None => true end.
(* [comment removed for export] *)
Fixpoint w4s (cells : list kentry) : list (bool * list Z) :=
  match cells with [] => [] | K :: r => match w4_atom K with Some d => d :: w4s r | None => w4s r end end.
Lemma w4s_in : forall cells d, In d (w4s cells) -> exists K, In K cells /\ w4_atom K = Some d.
Proof.
  intros cells d. induction cells as [|K r IH]; intros H; [destruct H|]. cbn [w4s] in H.
  destruct (w4_atom K) as [d'|] eqn:A.
  - destruct H as [<-|H]; [exists K; split; [left; reflexivity | exact A]|]. destruct (IH H) as (K' & HK' & A'). exists K'. split; [right; exact HK' | exact A'].
  - destruct (IH H) as (K' & HK' & A'). exists K'. split; [right; exact HK' | exact A'].
Qed.
Definition zl_eqb (a b : list Z) : bool := (length a =? length b)%nat && forallb (fun p => fst p =? snd p) (combine a b).
Lemma zl_eqb_refl : forall a, zl_eqb a a = true.
Proof. intros a. unfold zl_eqb. rewrite Nat.eqb_refl. cbn [andb]. induction a as [|x r IH]; [reflexivity|]. cbn [combine forallb fst snd]. rewrite Z.eqb_refl. exact IH. Qed.
Lemma zl_eqb_eq : forall a b, zl_eqb a b = true -> a = b.
Proof.
  intros a b H. unfold zl_eqb in H. apply andb_prop in H as [L F]. apply Nat.eqb_eq in L. revert b L F.
  induction a as [|x r IH]; intros [|y q] L F; [reflexivity | discriminate L | discriminate L |].
  cbn [combine forallb fst snd] in F. apply andb_prop in F as [F1 F2]. apply Z.eqb_eq in F1. subst y. f_equal. apply IH; [cbn in L; lia | exact F2].
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint alll {A} (f : A -> bool) (l : list A) : bool := match l with [] => true | x :: r => if f x then alll f r else false end.
Lemma alll_forallb : forall {A} (f : A -> bool) l, alll f l = forallb f l.
Proof. intros A f l. induction l as [|x r IH]; [reflexivity|]. cbn [alll forallb]. rewrite IH. destruct (f x); reflexivity. Qed.
Definition admk (kb : Z * Z) (gc : list (expr * Z * Z)) (ws : list (bool * list Z)) (t : list Z) (kk : nat) : bool :=
  if (if (kk <? 4)%nat then (fst kb <=? Z.of_nat kk) && (Z.of_nat kk <=? snd kb) else (4 <=? snd kb)) then
    if alll (fun c => inrange c (Bof t)) gc then alll (fun pd => Bool.eqb (zl_eqb t (map canon (snd pd))) (fst pd)) ws else false
  else false.
Definition adm (cells : list kentry) (t : list Z) (kk : nat) : bool := admk (kbounds cells) (gcons cells) (w4s cells) t kk.
(* [comment removed for export] *)
Definition off_expr (a0e : expr) : option (option expr) :=
  match a0e with
  | EVar v => if Nat.eqb v 42 then Some None else None
  | EAlu ALU_ADD (EVar v) e' => if Nat.eqb v 42 then Some (Some e') else None
  | _ => None
  end.
Definition gpos4 (e : expr) : option (list nat) := match bpos e with Some l => if forallb (fun i => (i <? 4)%nat) l then Some l else None | None => None end.
Definition ment (oe : option expr) : option (list nat) := match oe with None => Some [] | Some e => gpos4 e end.
Definition claim (a0e a1e : expr) (t : list Z) (kk : nat) : bool :=
  match off_expr a0e with
  | Some oe =>
      match ment oe, gpos4 a1e with
      | Some l1, Some l2 =>
          forallb (fun i => special (nth i t 0)) (l1 ++ l2) &&
          let off := match oe with None => Some 0 | Some e => zevb (Bof t) e end in
          match off, zevb (Bof t) a1e with
          | Some o, Some kd =>
              (0 <=? o) && (o <=? 4) && (o <=? Z.of_nat kk) &&
              match PMR.detect (firstn kk t) with Some j => (o =? Z.of_nat j) && (kd =? 1) | None => (2 <=? kd) && (kd <=? 5) end
          | _, _ => false
          end
      | _, _ => false
      end
  | None => false
  end.
Fixpoint tuples (n : nat) : list (list Z) := match n with O => [[]] | S m => flat_map (fun z => map (cons z) (tuples m)) REPS end.
Definition ALLTK : list (list Z * nat) := list_prod (tuples 4) [1; 2; 3; 4]%nat.
Definition leaf_chk (cells : list kentry) (a0e a1e : expr) : bool :=
  let kb := kbounds cells in let gc := gcons cells in let ws := w4s cells in
  alll (fun tk => if admk kb gc ws (fst tk) (snd tk) then claim a0e a1e (fst tk) (snd tk) else true) ALLTK.
(* [comment removed for export] *)
Definition BYTES : list Z := map Z.of_nat (seq 0 256).
Definition B1of (i : nat) (v : Z) : nat -> Z := fun n => if Nat.eqb n i then v else 0.
Definition B2of (i j : nat) (v w : Z) : nat -> Z := fun n => if Nat.eqb n i then v else if Nat.eqb n j then w else 0.
Definition inv_ok (c : expr * Z * Z) : bool :=
  match gpos (fst (fst c)) with
  | Some [] => true
  | Some [i] => forallb (fun v => Bool.eqb (inrange c (B1of i v)) (inrange c (B1of i (canon v)))) BYTES
  | Some [i; j] => forallb (fun v => forallb (fun w => Bool.eqb (inrange c (B2of i j v w)) (inrange c (B2of i j (canon v) (canon w)))) BYTES) BYTES
  | _ => false
  end.
(* [comment removed for export] *)
Definition c_eqb (a b : expr * Z * Z) : bool := expr_eqb (fst (fst a)) (fst (fst b)) && (snd (fst a) =? snd (fst b)) && (snd a =? snd b).
Fixpoint dedup (l : list (expr * Z * Z)) : list (expr * Z * Z) :=
  match l with [] => [] | c :: r => let d := dedup r in if existsb (c_eqb c) d then d else c :: d end.
Lemma c_eqb_eq : forall a b, c_eqb a b = true -> a = b.
Proof.
  intros [[e lo] hi] [[e' lo'] hi'] H. unfold c_eqb in H. cbn [fst snd] in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply expr_eqb_eq in H1. apply Z.eqb_eq in H2. apply Z.eqb_eq in H3. subst. reflexivity.
Qed.
Lemma dedup_in : forall l c, In c l -> In c (dedup l).
Proof.
  intros l c. induction l as [|x r IH]; intros H; [destruct H|]. cbn [dedup]. cbv zeta.
  destruct H as [->|H].
  - destruct (existsb (c_eqb c) (dedup r)) eqn:X; [|left; reflexivity]. apply existsb_exists in X as (y & Hy & E). apply c_eqb_eq in E. subst y. exact Hy.
  - destruct (existsb (c_eqb x) (dedup r)); [exact (IH H) | right; exact (IH H)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma in_BYTES : forall z, 0 <= z <= 255 -> In z BYTES.
Proof. intros z Hz. unfold BYTES. apply in_map_iff. exists (Z.to_nat z). split; [lia|]. apply in_seq. lia. Qed.
Lemma in_tuples : forall n t, length t = n -> Forall (fun z => In z REPS) t -> In t (tuples n).
Proof.
  induction n as [|n IH]; intros t L F.
  - destruct t; [left; reflexivity | discriminate L].
  - destruct t as [|z r]; [discriminate L|]. cbn [tuples]. apply in_flat_map. exists z. inversion F; subst. split; [assumption|].
    apply in_map. apply IH; [cbn in L; lia | assumption].
Qed.
Lemma gpos_bpos : forall e q, gpos e = Some q -> exists l, bpos e = Some l /\ (forall i, In i l -> In i q) /\ (forall i, In i q -> (i < 4)%nat) /\ (length q <= 2)%nat /\ List.NoDup q.
Proof.
  intros e q H. unfold gpos in H. destruct (bpos e) as [l|] eqn:Hb; [|discriminate H]. cbv zeta in H.
  destruct ((length (nodup Nat.eq_dec l) <=? 2)%nat && forallb (fun i => (i <? 4)%nat) (nodup Nat.eq_dec l)) eqn:C; [|discriminate H]. injection H as <-.
  apply andb_prop in C as [C1 C2]. apply Nat.leb_le in C1. exists l. split; [reflexivity|]. split; [intros i Hi; apply nodup_In; exact Hi|].
  split; [|split; [exact C1 | apply NoDup_nodup]]. intros i Hi. pose proof (proj1 (forallb_forall _ _) C2 i Hi) as X. apply Nat.ltb_lt in X. exact X.
Qed.
Lemma gpos4_bpos : forall e l, gpos4 e = Some l -> bpos e = Some l /\ (forall i, In i l -> (i < 4)%nat).
Proof.
  intros e l H. unfold gpos4 in H. destruct (bpos e) as [l'|] eqn:Hb; [|discriminate H].
  destruct (forallb _ l') eqn:C; [|discriminate H]. injection H as <-. split; [reflexivity|].
  intros i Hi. pose proof (proj1 (forallb_forall _ _) C i Hi) as X. apply Nat.ltb_lt in X. exact X.
Qed.
(* [comment removed for export] *)
Lemma inrange_agree : forall e lo hi l B B', bpos e = Some l -> (forall i, In i l -> B i = B' i) -> inrange (e, lo, hi) B = inrange (e, lo, hi) B'.
Proof. intros e lo hi l B B' Hb AG. unfold inrange. rewrite (zevb_agree e l B B' Hb AG). reflexivity. Qed.
Lemma inv_sound : forall e lo hi B, inv_ok (e, lo, hi) = true -> (forall i, 0 <= B i <= 255) ->
  inrange (e, lo, hi) B = inrange (e, lo, hi) (fun n => canon (B n)).
Proof.
  intros e lo hi B H HB. unfold inv_ok in H. cbn [fst snd] in H. destruct (gpos e) as [q|] eqn:G; [|discriminate H].
  destruct (gpos_bpos e q G) as (l & Hb & SUB & _ & _ & ND).
  destruct q as [|i [|j [|x r]]]; [| | |discriminate H].
  - rewrite (inrange_agree e lo hi l B (fun n => canon (B n)) Hb); [reflexivity|]. intros i Hi. destruct (SUB i Hi).
  - pose proof (proj1 (forallb_forall _ _) H (B i) (in_BYTES _ (HB i))) as X. apply Bool.eqb_prop in X.
    rewrite (inrange_agree e lo hi l B (B1of i (B i)) Hb) by (intros n Hn; destruct (SUB n Hn) as [<-|[]]; unfold B1of; rewrite Nat.eqb_refl; reflexivity).
    rewrite (inrange_agree e lo hi l (fun n => canon (B n)) (B1of i (canon (B i))) Hb) by (intros n Hn; destruct (SUB n Hn) as [<-|[]]; unfold B1of; rewrite Nat.eqb_refl; reflexivity).
    exact X.
  - pose proof (proj1 (forallb_forall _ _) H (B i) (in_BYTES _ (HB i))) as X. pose proof (proj1 (forallb_forall _ _) X (B j) (in_BYTES _ (HB j))) as Y. apply Bool.eqb_prop in Y.
    assert (NIJ : i <> j) by (intros ->; inversion ND as [|a b N1 N2]; apply N1; left; reflexivity).
    assert (AG1 : forall n, In n l -> B n = B2of i j (B i) (B j) n).
    { intros n Hn. unfold B2of. destruct (SUB n Hn) as [<-|[<-|[]]]; [rewrite Nat.eqb_refl; reflexivity|]. destruct (Nat.eqb_spec j i) as [E|_]; [exfalso; exact (NIJ (eq_sym E))|]. rewrite Nat.eqb_refl. reflexivity. }
    assert (AG2 : forall n, In n l -> canon (B n) = B2of i j (canon (B i)) (canon (B j)) n).
    { intros n Hn. unfold B2of. destruct (SUB n Hn) as [<-|[<-|[]]]; [rewrite Nat.eqb_refl; reflexivity|]. destruct (Nat.eqb_spec j i) as [E|_]; [exfalso; exact (NIJ (eq_sym E))|]. rewrite Nat.eqb_refl. reflexivity. }
    rewrite (inrange_agree e lo hi l B _ Hb AG1). rewrite (inrange_agree e lo hi l (fun n => canon (B n)) _ Hb AG2). exact Y.
Qed.
Lemma firstn4_Bof : forall s, firstn (Nat.min (length s) 4) (map (Bof s) [0; 1; 2; 3]%nat) = firstn 4 s.
Proof. intros [|b0 [|b1 [|b2 [|b3 r]]]]; try reflexivity. cbn [length]. rewrite Nat.min_r by lia. reflexivity. Qed.
Lemma special_canon : forall z, special (canon z) = true -> canon z = z.
Proof. intros z H. unfold canon in *. destruct (special z) eqn:X; [reflexivity | exfalso; revert H; generalize X; clear; intros X H; cbn in H; discriminate H]. Qed.

Lemma off_expr_cases : forall a0e oe, off_expr a0e = Some oe -> (a0e = EVar 42 /\ oe = None) \/ (exists e', a0e = EAlu ALU_ADD (EVar 42) e' /\ oe = Some e').
Proof.
  intros a0e oe H. destruct a0e as [|v|op a b| | | | |]; cbn [off_expr] in H; try discriminate H.
  - destruct (Nat.eqb_spec v 42) as [->|]; [|discriminate H]. injection H as <-. left. split; reflexivity.
  - destruct op; try discriminate H. destruct a as [|v| | | | | |]; try discriminate H. destruct (Nat.eqb_spec v 42) as [->|]; [|discriminate H]. injection H as <-.
    right. exists b. split; reflexivity.
Qed.
Lemma add_lit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= a + b < 2 ^ 64 -> alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b Ha Hab. change (alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b)) with (bv_add (Z_to_bv 64 a) (Z_to_bv 64 b)).
  apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite modulus64.
  rewrite <- Zplus_mod. reflexivity.
Qed.

Theorem leaf_sound : forall cells (a0e a1e : expr) GC E (M : mem) s k p,
  leaf_chk cells a0e a1e = true -> forallb inv_ok GC = true -> (forall c, In c (gcons cells) -> In c GC) ->
  (forall K, In K cells -> kentry_ok RSEGS E M K) ->
  eb E 0%nat = map (Z_to_bv 8) s -> brange s -> Z.of_nat (length s) = k -> 1 <= k -> bv_unsigned (ev E 43) = k -> bv_unsigned (ev E 42) = p -> p + 4 < 2 ^ 64 ->
  exists c kind, 0 <= c <= 4 /\ c <= k /\ edenot E a0e = Z_to_bv 64 (p + c) /\ bv_unsigned (edenot E a1e) = kind /\
    match PMR.detect s with Some j => c = Z.of_nat j /\ kind = 1 | None => 2 <= kind <= 5 end.
Proof.
  intros cells a0e a1e GC E M s k p CHK INV GCI HK EB BR Lk K1 U43 U42 P4.
  set (B := Bof s). set (t := map (fun n => canon (B n)) [0; 1; 2; 3]%nat). set (kk := Nat.min (length s) 4).
  assert (HB : forall i, 0 <= B i <= 255) by (intros i; apply Bof_range; exact BR).
  assert (Tt : forall i, (i < 4)%nat -> Bof t i = canon (B i)).
  { intros i Hi. unfold Bof, t. destruct i as [|[|[|[|i]]]]; try reflexivity. lia. }
  (* [comment removed for export] *)
  assert (IN : In (t, kk) ALLTK).
  { unfold ALLTK. apply in_prod.
    - apply in_tuples; [reflexivity|]. unfold t. cbn [map]. repeat (apply Forall_cons; [apply canon_in|]). apply Forall_nil.
    - unfold kk. rewrite <- Lk in K1. destruct (length s) as [|[|[|[|n]]]]; [cbn in K1; lia | | | | rewrite Nat.min_r by lia]; cbn; tauto. }
  unfold leaf_chk in CHK. cbv zeta in CHK. rewrite alll_forallb in CHK. pose proof (proj1 (forallb_forall _ _) CHK (t, kk) IN) as L. cbn [fst snd] in L. change (admk _ _ _ t kk) with (adm cells t kk) in L.
  (* [comment removed for export] *)
  assert (ADM : adm cells t kk = true).
  { unfold adm, admk. pose proof (kbounds_sound E M cells HK) as KB. rewrite U43 in KB. destruct (kbounds cells) as [klo khi]. cbn [fst snd] in KB |- *.
    rewrite !alll_forallb.
    match goal with |- (if ?a then if ?b then ?c else false else false) = true => enough (AND3 : a = true /\ b = true /\ c = true) by (destruct AND3 as (-> & -> & ->); reflexivity) end.
    split; [|split].
    - unfold kk. destruct (Nat.ltb_spec (Nat.min (length s) 4) 4) as [X|X].
      + rewrite Nat.min_l by lia. apply andb_true_intro. split; apply Z.leb_le; lia.
      + apply Z.leb_le. lia.
    - apply forallb_forall. intros [[e lo] hi] Hc. destruct (gcons_in cells e lo hi Hc) as [HKc (q & G)].
      destruct (gpos_bpos e q G) as (l & Hb & SUB & LT4 & _ & _).
      rewrite (inrange_agree e lo hi l (Bof t) (fun n => canon (B n)) Hb) by (intros i Hi; apply Tt; apply LT4; apply SUB; exact Hi).
      rewrite <- (inv_sound e lo hi B (proj1 (forallb_forall _ _) INV _ (GCI _ Hc)) HB).
      unfold inrange. destruct (zevb B e) as [v|] eqn:Z0; [|reflexivity].
      pose proof (HK _ HKc) as KOK. cbn [kentry_ok] in KOK. pose proof (range_fact E s EB BR e v lo hi Z0 KOK) as RF.
      apply andb_true_intro. split; apply Z.leb_le; lia.
    - apply forallb_forall. intros [pos d] Hd. destruct (w4s_in cells _ Hd) as (K & HKin & A). cbn [fst snd].
      destruct (w4_sound E s K pos d EB BR A (ex_intro _ M (HK K HKin))) as (WT & WF & CD).
      destruct pos.
      + cbn [map] in WT. replace t with (map canon d) by (rewrite <- (WT eq_refl); reflexivity). rewrite zl_eqb_refl. reflexivity.
      + destruct (zl_eqb t (map canon d)) eqn:ZE; [|reflexivity]. exfalso. apply (WF eq_refl). apply zl_eqb_eq in ZE. rewrite CD in ZE. exact ZE. }
  rewrite ADM in L.
  (* [comment removed for export] *)
  unfold claim in L. destruct (off_expr a0e) as [oe|] eqn:OE; [|discriminate L].
  destruct (ment oe) as [l1|] eqn:M1; [|discriminate L]. destruct (gpos4 a1e) as [l2|] eqn:M2; [|discriminate L].
  apply andb_prop in L as [SP L]. cbv zeta in L.
  assert (AG : forall i, In i (l1 ++ l2) -> Bof t i = B i).
  { intros i Hi. pose proof (proj1 (forallb_forall _ _) SP i Hi) as X. cbn beta in X. change (special (Bof t i) = true) in X.
    assert (I4 : (i < 4)%nat).
    { apply in_app_or in Hi as [Hi|Hi].
      - destruct oe as [e'|]; [|cbn in M1; injection M1 as <-; destruct Hi]. cbn [ment] in M1. exact (proj2 (gpos4_bpos e' l1 M1) i Hi).
      - exact (proj2 (gpos4_bpos a1e l2 M2) i Hi). }
    rewrite (Tt i I4) in X. rewrite (Tt i I4). exact (special_canon _ X). }
  destruct (gpos4_bpos a1e l2 M2) as [B2 _].
  rewrite (zevb_agree a1e l2 (Bof t) B B2) in L by (intros i Hi; apply AG; apply in_or_app; right; exact Hi).
  destruct (match oe with None => Some 0 | Some e => zevb (Bof t) e end) as [o|] eqn:HO; [|discriminate L].
  destruct (zevb B a1e) as [kd|] eqn:HKD; [|discriminate L].
  apply andb_prop in L as [L DM]. apply andb_prop in L as [L O3]. apply andb_prop in L as [O1 O2]. apply Z.leb_le in O1. apply Z.leb_le in O2. apply Z.leb_le in O3.
  exists o, kd.
  split; [lia|]. split; [unfold kk in O3; pose proof (Nat.le_min_l (length s) 4); lia|].
  split.
  { pose proof (u64_range (ev E 42)) as PR. rewrite U42 in PR.
    destruct (off_expr_cases a0e oe OE) as [(-> & ->)|(e' & -> & ->)].
    - injection HO as <-. cbn [edenot]. rewrite Z.add_0_r. symmetry. rewrite <- U42. apply Z_to_bv_bv_unsigned.
    - cbn [ment] in M1. destruct (gpos4_bpos e' l1 M1) as [B1 _].
      rewrite (zevb_agree e' l1 (Bof t) B B1) in HO by (intros i Hi; apply AG; apply in_or_app; left; exact Hi).
      pose proof (zevb_sound E s EB BR e' o HO) as V. cbn [edenot].
      rewrite <- (Z_to_bv_bv_unsigned 64 (ev E 42)), <- (Z_to_bv_bv_unsigned 64 (edenot E e')). rewrite U42, V. apply add_lit; lia. }
  split; [exact (zevb_sound E s EB BR a1e kd HKD)|].
  assert (DT : PMR.detect (firstn kk t) = PMR.detect s).
  { unfold t, kk. change (map (fun n => canon (B n)) [0; 1; 2; 3]%nat) with (map canon (map B [0; 1; 2; 3]%nat)).
    rewrite firstn_map. unfold B. rewrite firstn4_Bof. rewrite detect_canon. symmetry. apply detect_first4. }
  rewrite DT in DM. destruct (PMR.detect s) as [j|].
  - apply andb_prop in DM as [D1 D2]. apply Z.eqb_eq in D1. apply Z.eqb_eq in D2. split; [exact D1 | exact D2].
  - apply andb_prop in DM as [D1 D2]. apply Z.leb_le in D1. apply Z.leb_le in D2. lia.
Qed.
End DKW.
