(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun HeapIface HeapIfaceA L5Defs PmLibDefs PmLibDefsA PmIcptIfaceA PmRef.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module DKAW.
Section WithL.
Variable AL : asan_layout.   (* [comment removed for export] *)
Abbreviation RSEGS := (hl_segs AL).
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
  | EBlob sx O i (Datatypes.S O) => if 0 <=? i then Some (bget B sx i) else None
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
  | EBlob _ O i (Datatypes.S O) => if 0 <=? i then Some [Z.to_nat i] else None
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
Definition hist := list (nat * list Z).
Fixpoint hget (h : hist) (v : nat) : option (list Z) := match h with [] => None | vd :: r => if Nat.eqb (fst vd) v then Some (snd vd) else hget r v end.
Definition bc_atom (h : hist) (K : kentry) : option (bool * list Z) :=
  match K with
  | KRange (EVar v) lo hi =>
      match hget h v with
      | Some d => if ((lo =? 0) && (hi =? 0))%bool then Some (true, d) else if 1 <=? lo then Some (false, d) else None
      | None => None
      end
  | _ => None
  end.
(* [comment removed for export] *)
Definition hent_ok (E : env) (s : list Z) (vd : nat * list Z) : Prop :=
  (length (snd vd) <= length s)%nat /\ (length (snd vd) <= 4)%nat /\ forallb special (snd vd) = true /\ (bv_unsigned (ev E (fst vd)) = 0 <-> firstn (length (snd vd)) s = snd vd).
Definition hsem (h : hist) (E : env) (s : list Z) : Prop := Forall (hent_ok E s) h.
Lemma hsem_nil : forall E s, hsem [] E s. Proof. intros E s. apply Forall_nil. Qed.
Lemma hget_in : forall h v d, hget h v = Some d -> In (v, d) h.
Proof.
  intros h v d. induction h as [|[w d'] r IH]; intros H; [discriminate H|]. cbn [hget fst snd] in H.
  destruct (Nat.eqb_spec w v) as [->|N]; [injection H as <-; left; reflexivity | right; exact (IH H)].
Qed.
Lemma hsem_in : forall h E s v d, hsem h E s -> In (v, d) h -> hent_ok E s (v, d).
Proof. intros h E s v d HS Hin. exact (proj1 (Forall_forall _ _) HS _ Hin). Qed.
Lemma canon_eq_special : forall z c, special c = true -> canon z = c -> z = c.
Proof. intros z c Hc H. unfold canon in H. destruct (special z); [exact H | subst c; discriminate Hc]. Qed.
Lemma canon_map_eq : forall x d, forallb special d = true -> (map canon x = d <-> x = d).
Proof.
  intros x d SP. split.
  - revert d SP. induction x as [|a r IH]; intros [|b q] SP H; try discriminate H; [reflexivity|]. cbn [map] in H. injection H as Ha Hr.
    cbn [forallb] in SP. apply andb_prop in SP as [Sb Sq]. f_equal; [exact (canon_eq_special _ _ Sb Ha) | exact (IH q Sq Hr)].
  - intros ->. induction d as [|b q IH]; [reflexivity|]. cbn [forallb] in SP. apply andb_prop in SP as [Sb Sq]. cbn [map]. rewrite (canon_special _ Sb). f_equal. exact (IH Sq).
Qed.
Lemma firstn_t : forall s n, (n <= 4)%nat -> (n <= length s)%nat -> firstn n (map (fun i => canon (Bof s i)) [0; 1; 2; 3]%nat) = map canon (firstn n s).
Proof. intros s n H4 HL. destruct s as [|b0 [|b1 [|b2 [|b3 r]]]]; cbn [length] in HL; destruct n as [|[|[|[|[|n]]]]]; try lia; reflexivity. Qed.
Lemma bc_sound : forall h E s K pos d, hsem h E s -> bc_atom h K = Some (pos, d) -> (exists M, kentry_ok RSEGS E M K) ->
  (length d <= length s)%nat /\ (length d <= 4)%nat /\ forallb special d = true /\ (pos = true -> firstn (length d) s = d) /\ (pos = false -> firstn (length d) s <> d).
Proof.
  intros h E s K pos d HS HA (M & HK). unfold bc_atom in HA. destruct K as [| | | | |e lo hi| | | |]; try discriminate HA.
  destruct e as [|v| | | | | |]; try discriminate HA. destruct (hget h v) as [d'|] eqn:G; [|discriminate HA].
  pose proof (hsem_in h E s v d' HS (hget_in _ _ _ G)) as (L1 & L2 & SP & IFF). cbn [fst snd] in L1, L2, SP, IFF. cbn [kentry_ok edenot] in HK.
  destruct ((lo =? 0) && (hi =? 0))%bool eqn:P0.
  - injection HA as <- <-. apply andb_prop in P0 as [P1 P2]. apply Z.eqb_eq in P1. apply Z.eqb_eq in P2. subst lo hi.
    split; [exact L1|]. split; [exact L2|]. split; [exact SP|]. split; [intros _; apply (proj1 IFF); lia | intros X; discriminate X].
  - destruct (1 <=? lo) eqn:P1; [|discriminate HA]. injection HA as <- <-. apply Z.leb_le in P1.
    split; [exact L1|]. split; [exact L2|]. split; [exact SP|]. split; [intros X; discriminate X | intros _ EQ]. apply (proj2 IFF) in EQ. lia.
Qed.
(* [comment removed for export] *)
Definition SLT3E (w : nat) : expr := EAlu ALU_AND (EMd M_MUL (ELit (-1)) (EAlu ALU_SLTU (EVar w) (ELit 1))) (ELit 3).
Lemma slt3_u : forall E w, bv_unsigned (edenot E (SLT3E w)) = (if bv_unsigned (ev E w) =? 0 then 3 else 0).
Proof.
  intros E w. unfold SLT3E. cbn [edenot]. rewrite u_and64, u_mul64, u_sltu64, !u_lit64a.
  pose proof (u64_range (ev E w)) as R. change (1 mod 2 ^ 64) with 1. change (3 mod 2 ^ 64) with 3.
  destruct (Z.ltb_spec (bv_unsigned (ev E w)) 1) as [L|L].
  - replace (bv_unsigned (ev E w) =? 0) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
  - replace (bv_unsigned (ev E w) =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition VP : nat := 10%nat.
Definition VK : nat := 11%nat.
(* [comment removed for export] *)
Fixpoint kbounds (cells : list kentry) : Z * Z :=
  match cells with
  | [] => (0, M64)
  | KRange (EVar v) lo hi :: r => let p := kbounds r in if Nat.eqb v VK then (Z.max lo (fst p), Z.min hi (snd p)) else p
  | _ :: r => kbounds r
  end.
Lemma kbounds_sound : forall E (M : mem) cells, (forall K, In K cells -> kentry_ok RSEGS E M K) ->
  fst (kbounds cells) <= bv_unsigned (ev E VK) <= snd (kbounds cells).
Proof.
  intros E M cells. induction cells as [|K r IH]; intros H.
  - cbn [kbounds fst snd]. rewrite M64_eq. pose proof (u64_range (ev E VK)). lia.
  - assert (Hr : fst (kbounds r) <= bv_unsigned (ev E VK) <= snd (kbounds r)) by (apply IH; intros K' HK'; apply H; right; exact HK').
    destruct K as [| | | | |e lo hi| | | |]; cbn [kbounds]; try exact Hr. destruct e as [|v| | | | | |]; try exact Hr.
    cbv zeta. destruct (Nat.eqb_spec v VK) as [->|_]; [|exact Hr].
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
Fixpoint bcs (h : hist) (cells : list kentry) : list (bool * list Z) :=
  match cells with [] => [] | K :: r => match bc_atom h K with Some d => d :: bcs h r | None => bcs h r end end.
Lemma bcs_in : forall h cells d, In d (bcs h cells) -> exists K, In K cells /\ bc_atom h K = Some d.
Proof.
  intros h cells d. induction cells as [|K r IH]; intros H; [destruct H|]. cbn [bcs] in H.
  destruct (bc_atom h K) as [d'|] eqn:A.
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
    if alll (fun c => inrange c (Bof t)) gc then alll (fun pd => Bool.eqb (zl_eqb (firstn (length (snd pd)) t) (snd pd)) (fst pd)) ws else false
  else false.
Definition adm (h : hist) (cells : list kentry) (t : list Z) (kk : nat) : bool := admk (kbounds cells) (gcons cells) (bcs h cells) t kk.
(* [comment removed for export] *)
Inductive offe : Type := ONone | OExp (e : expr) | OCmp (w : nat) (d : list Z).
Definition off_expr (h : hist) (a0e : expr) : option offe :=
  match a0e with
  | EVar v => if Nat.eqb v VP then Some ONone else None
  | EAlu ALU_ADD (EVar v) e' =>
      if Nat.eqb v VP then Some (match find (fun vd : nat * list Z => expr_eqb e' (SLT3E (fst vd))) h with Some vd => OCmp (fst vd) (snd vd) | None => OExp e' end) else None
  | _ => None
  end.
Definition gpos4 (e : expr) : option (list nat) := match bpos e with Some l => if forallb (fun i => (i <? 4)%nat) l then Some l else None | None => None end.
Definition ment (oe : offe) : option (list nat) := match oe with ONone => Some [] | OExp e => gpos4 e | OCmp _ _ => Some [] end.
Definition claim (h : hist) (a0e a1e : expr) (t : list Z) (kk : nat) : bool :=
  match off_expr h a0e with
  | Some oe =>
      match ment oe, gpos4 a1e with
      | Some l1, Some l2 =>
          forallb (fun i => special (nth i t 0)) (l1 ++ l2) &&
          let off := match oe with ONone => Some 0 | OExp e => zevb (Bof t) e | OCmp _ d => Some (if zl_eqb (firstn (length d) t) d then 3 else 0) end in
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
Fixpoint tuples (n : nat) : list (list Z) := match n with O => [[]] | Datatypes.S m => flat_map (fun z => map (cons z) (tuples m)) REPS end.
Definition ALLTK : list (list Z * nat) := list_prod (tuples 4) [1; 2; 3; 4]%nat.
Definition leaf_chk (h : hist) (cells : list kentry) (a0e a1e : expr) : bool :=
  let kb := kbounds cells in let gc := gcons cells in let ws := bcs h cells in
  alll (fun tk => if admk kb gc ws (fst tk) (snd tk) then claim h a0e a1e (fst tk) (snd tk) else true) ALLTK.
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

Lemma off_expr_cases : forall h a0e oe, off_expr h a0e = Some oe ->
  (a0e = EVar VP /\ oe = ONone) \/ (exists e', a0e = EAlu ALU_ADD (EVar VP) e' /\ oe = OExp e') \/ (exists w d, a0e = EAlu ALU_ADD (EVar VP) (SLT3E w) /\ oe = OCmp w d /\ In (w, d) h).
Proof.
  intros h a0e oe H. destruct a0e as [|v|op a b| | | | |]; cbn [off_expr] in H; try discriminate H.
  - destruct (Nat.eqb_spec v VP) as [->|]; [|discriminate H]. injection H as <-. left. split; reflexivity.
  - destruct op; try discriminate H. destruct a as [|v| | | | | |]; try discriminate H. destruct (Nat.eqb_spec v VP) as [->|]; [|discriminate H].
    destruct (find _ h) as [[w d]|] eqn:F; injection H as <-.
    + apply find_some in F as [Hin Heq]. cbn [fst snd] in Heq. apply expr_eqb_eq in Heq. subst b. right; right. exists w, d. split; [reflexivity|]. split; [reflexivity | exact Hin].
    + right; left. exists b. split; reflexivity.
Qed.
Lemma add_lit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= a + b < 2 ^ 64 -> alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b Ha Hab. change (alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b)) with (bv_add (Z_to_bv 64 a) (Z_to_bv 64 b)).
  apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite modulus64.
  rewrite <- Zplus_mod. reflexivity.
Qed.

Theorem leaf_sound : forall h cells (a0e a1e : expr) GC E (M : mem) s k p,
  leaf_chk h cells a0e a1e = true -> forallb inv_ok GC = true -> (forall c, In c (gcons cells) -> In c GC) ->
  (forall K, In K cells -> kentry_ok RSEGS E M K) -> hsem h E s ->
  eb E 0%nat = map (Z_to_bv 8) s -> brange s -> Z.of_nat (length s) = k -> 1 <= k -> bv_unsigned (ev E VK) = k -> bv_unsigned (ev E VP) = p -> p + 4 < 2 ^ 64 ->
  exists c kind, 0 <= c <= 4 /\ c <= k /\ edenot E a0e = Z_to_bv 64 (p + c) /\ bv_unsigned (edenot E a1e) = kind /\
    match PMR.detect s with Some j => c = Z.of_nat j /\ kind = 1 | None => 2 <= kind <= 5 end.
Proof.
  intros h cells a0e a1e GC E M s k p CHK INV GCI HK HS EB BR Lk K1 U43 U42 P4.
  set (B := Bof s). set (t := map (fun n => canon (B n)) [0; 1; 2; 3]%nat). set (kk := Nat.min (length s) 4).
  assert (HB : forall i, 0 <= B i <= 255) by (intros i; apply Bof_range; exact BR).
  assert (Tt : forall i, (i < 4)%nat -> Bof t i = canon (B i)).
  { intros i Hi. unfold Bof, t. destruct i as [|[|[|[|i]]]]; try reflexivity. lia. }
  (* [comment removed for export] *)
  assert (IN : In (t, kk) ALLTK).
  { unfold ALLTK. apply in_prod.
    - apply in_tuples; [reflexivity|]. unfold t. cbn [map]. repeat (apply Forall_cons; [apply canon_in|]). apply Forall_nil.
    - unfold kk. rewrite <- Lk in K1. destruct (length s) as [|[|[|[|n]]]]; [cbn in K1; lia | | | | rewrite Nat.min_r by lia]; cbn; tauto. }
  unfold leaf_chk in CHK. cbv zeta in CHK. rewrite alll_forallb in CHK. pose proof (proj1 (forallb_forall _ _) CHK (t, kk) IN) as L. cbn [fst snd] in L. change (admk _ _ _ t kk) with (adm h cells t kk) in L.
  (* [comment removed for export] *)
  assert (ADM : adm h cells t kk = true).
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
    - apply forallb_forall. intros [pos d] Hd. destruct (bcs_in h cells _ Hd) as (K & HKin & A). cbn [fst snd].
      destruct (bc_sound h E s K pos d HS A (ex_intro _ M (HK K HKin))) as (Ld & L4 & SPd & WT & WF).
      unfold t, B. rewrite (firstn_t s (length d) L4 Ld).
      destruct pos.
      + rewrite (proj2 (canon_map_eq _ _ SPd) (WT eq_refl)). rewrite zl_eqb_refl. reflexivity.
      + destruct (zl_eqb (map canon (firstn (length d) s)) d) eqn:ZE; [|reflexivity]. exfalso. apply (WF eq_refl). apply zl_eqb_eq in ZE. exact (proj1 (canon_map_eq _ _ SPd) ZE). }
  rewrite ADM in L.
  (* [comment removed for export] *)
  unfold claim in L. destruct (off_expr h a0e) as [oe|] eqn:OE; [|discriminate L].
  destruct (ment oe) as [l1|] eqn:M1; [|discriminate L]. destruct (gpos4 a1e) as [l2|] eqn:M2; [|discriminate L].
  apply andb_prop in L as [SP L]. cbv zeta in L.
  assert (AG : forall i, In i (l1 ++ l2) -> Bof t i = B i).
  { intros i Hi. pose proof (proj1 (forallb_forall _ _) SP i Hi) as X. cbn beta in X. change (special (Bof t i) = true) in X.
    assert (I4 : (i < 4)%nat).
    { apply in_app_or in Hi as [Hi|Hi].
      - destruct oe as [|e'|w' d']; [cbn in M1; injection M1 as <-; destruct Hi | | cbn in M1; injection M1 as <-; destruct Hi]. cbn [ment] in M1. exact (proj2 (gpos4_bpos e' l1 M1) i Hi).
      - exact (proj2 (gpos4_bpos a1e l2 M2) i Hi). }
    rewrite (Tt i I4) in X. rewrite (Tt i I4). exact (special_canon _ X). }
  destruct (gpos4_bpos a1e l2 M2) as [B2 _].
  rewrite (zevb_agree a1e l2 (Bof t) B B2) in L by (intros i Hi; apply AG; apply in_or_app; right; exact Hi).
  destruct (match oe with ONone => Some 0 | OExp e => zevb (Bof t) e | OCmp _ d => Some (if zl_eqb (firstn (length d) t) d then 3 else 0) end) as [o|] eqn:HO; [|discriminate L].
  destruct (zevb B a1e) as [kd|] eqn:HKD; [|discriminate L].
  apply andb_prop in L as [L DM]. apply andb_prop in L as [L O3]. apply andb_prop in L as [O1 O2]. apply Z.leb_le in O1. apply Z.leb_le in O2. apply Z.leb_le in O3.
  exists o, kd.
  split; [lia|]. split; [unfold kk in O3; pose proof (Nat.le_min_l (length s) 4); lia|].
  split.
  { pose proof (u64_range (ev E VP)) as PR. rewrite U42 in PR.
    destruct (off_expr_cases h a0e oe OE) as [(-> & ->)|[(e' & -> & ->)|(w & d & -> & -> & Hwd)]].
    - injection HO as <-. cbn [edenot]. rewrite Z.add_0_r. symmetry. rewrite <- U42. apply Z_to_bv_bv_unsigned.
    - cbn [ment] in M1. destruct (gpos4_bpos e' l1 M1) as [B1 _].
      rewrite (zevb_agree e' l1 (Bof t) B B1) in HO by (intros i Hi; apply AG; apply in_or_app; left; exact Hi).
      pose proof (zevb_sound E s EB BR e' o HO) as V. cbn [edenot].
      rewrite <- (Z_to_bv_bv_unsigned 64 (ev E VP)), <- (Z_to_bv_bv_unsigned 64 (edenot E e')). rewrite U42, V. apply add_lit; lia.
    - (* [comment removed for export] *)
      pose proof (hsem_in h E s w d HS Hwd) as (Ld & L4 & SPd & IFF). cbn [fst snd] in Ld, L4, SPd, IFF.
      unfold t, B in HO. rewrite (firstn_t s (length d) L4 Ld) in HO.
      assert (OV : o = (if bv_unsigned (ev E w) =? 0 then 3 else 0)).
      { injection HO as <-. destruct (Z.eqb_spec (bv_unsigned (ev E w)) 0) as [Z0|Z0].
        - rewrite (proj2 (canon_map_eq _ _ SPd) (proj1 IFF Z0)). rewrite zl_eqb_refl. reflexivity.
        - destruct (zl_eqb (map canon (firstn (length d) s)) d) eqn:ZE; [|reflexivity]. exfalso. apply Z0. apply (proj2 IFF). apply zl_eqb_eq in ZE. exact (proj1 (canon_map_eq _ _ SPd) ZE). }
      cbn [edenot]. fold (SLT3E w). change (edenot E (EVar VP)) with (ev E VP).
      rewrite <- (Z_to_bv_bv_unsigned 64 (ev E VP)), <- (Z_to_bv_bv_unsigned 64 (edenot E (SLT3E w))). rewrite U42, slt3_u, <- OV. apply add_lit; lia. }
  split; [exact (zevb_sound E s EB BR a1e kd HKD)|].
  assert (DT : PMR.detect (firstn kk t) = PMR.detect s).
  { unfold t, kk. change (map (fun n => canon (B n)) [0; 1; 2; 3]%nat) with (map canon (map B [0; 1; 2; 3]%nat)).
    rewrite firstn_map. unfold B. rewrite firstn4_Bof. rewrite detect_canon. symmetry. apply detect_first4. }
  rewrite DT in DM. destruct (PMR.detect s) as [j|].
  - apply andb_prop in DM as [D1 D2]. apply Z.eqb_eq in D1. apply Z.eqb_eq in D2. split; [exact D1 | exact D2].
  - apply andb_prop in DM as [D1 D2]. apply Z.leb_le in D1. apply Z.leb_le in D2. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ps_reg (ps : SR.post_spec) (q : nat) : option expr :=
  match find (fun ie : nat * expr => Nat.eqb (fst ie) q) (SR.ps_regs ps) with Some ie => Some (snd ie) | None => None end.
Lemma ps_reg_in : forall ps q e, ps_reg ps q = Some e -> In (q, e) (SR.ps_regs ps).
Proof.
  intros ps q e H. unfold ps_reg in H. destruct (find _ (SR.ps_regs ps)) as [[i e']|] eqn:Hf; [|discriminate H].
  injection H as <-. apply find_some in Hf as [Hin Hq]. cbn [fst] in Hq. apply Nat.eqb_eq in Hq. subst i. exact Hin.
Qed.
Definition hist_eqb (a b : hist) : bool :=
  (length a =? length b)%nat && forallb (fun p : (nat * list Z) * (nat * list Z) => Nat.eqb (fst (fst p)) (fst (snd p)) && zl_eqb (snd (fst p)) (snd (snd p))) (combine a b).
Lemma hist_eqb_eq : forall a b, hist_eqb a b = true -> a = b.
Proof.
  intros a b H. unfold hist_eqb in H. apply andb_prop in H as [Ln F]. apply Nat.eqb_eq in Ln. revert b Ln F.
  induction a as [|[v d] r IH]; intros [|[v' d'] q] Ln F; [reflexivity | discriminate Ln | discriminate Ln |].
  cbn [combine forallb fst snd] in F. apply andb_prop in F as [F1 F2]. apply andb_prop in F1 as [Fv Fd]. apply Nat.eqb_eq in Fv. apply zl_eqb_eq in Fd. subst v' d'.
  f_equal. apply IH; [cbn in Ln; lia | exact F2].
Qed.
Lemma hsem_agree : forall h E E' s, hsem h E s -> (forall v d, In (v, d) h -> ev E' v = ev E v) -> hsem h E' s.
Proof.
  intros h E E' s HS AG. unfold hsem in *. apply Forall_forall. intros [v d] Hin. pose proof (proj1 (Forall_forall _ _) HS _ Hin) as (A & B & C & D).
  unfold hent_ok. cbn [fst snd] in *. rewrite (AG v d Hin). exact (conj A (conj B (conj C D))).
Qed.
Lemma hsem_lt_agree : forall h E E' s n, hsem h E s -> forallb (fun vd : nat * list Z => (fst vd <? n)%nat) h = true -> env_agree n E E' -> hsem h E' s.
Proof.
  intros h E E' s n HS LT AG. apply (hsem_agree h E E' s HS). intros v d Hin. symmetry. apply (proj1 AG).
  pose proof (proj1 (forallb_forall _ _) LT _ Hin) as X. cbn [fst] in X. apply Nat.ltb_lt in X. exact X.
Qed.
Lemma hsem_app1 : forall h E s vd, hsem h E s -> hent_ok E s vd -> hsem (h ++ [vd]) E s.
Proof. intros h E s vd HS H1. unfold hsem. apply Forall_app. split; [exact HS | apply Forall_cons; [exact H1 | apply Forall_nil]]. Qed.
Lemma bytes_at_tl : forall (M : mem) p b r, L5.bytes_at RSEGS M p (b :: r) -> L5.bytes_at RSEGS M (p + 1) r.
Proof. intros M p b r H i Hi. replace (p + 1 + Z.of_nat i) with (p + Z.of_nat (Datatypes.S i)) by lia. exact (H (Datatypes.S i) ltac:(cbn; lia)). Qed.
Lemma rdn_bytes_at : forall (M : mem) n p bs, L5.bytes_at RSEGS M p bs -> (n <= length bs)%nat -> rdn RSEGS M (Z_to_bv 64 p) n = Some (map (Z_to_bv 8) (firstn n bs)).
Proof.
  intros M n. induction n as [|n IH]; intros p bs HB Hn; [reflexivity|].
  destruct bs as [|b r]; [cbn in Hn; lia|]. cbn [firstn map].
  pose proof (HB 0%nat ltac:(cbn; lia)) as H0. unfold L5.u8_at in H0. rewrite Z.add_0_r in H0. cbn [rdn nth] in H0. cbn [rdn].
  destruct (match M (Z_to_bv 64 p) with Some b0 => Some b0 | None => seg_rom RSEGS (Z_to_bv 64 p) end) as [b0|]; [|discriminate H0]. injection H0 as ->.
  rewrite CH.bv_succ_Z. rewrite (IH (p + 1) r (bytes_at_tl M p b r HB) ltac:(cbn in Hn; lia)). reflexivity.
Qed.
Lemma map_unsigned_bytes : forall l, brange l -> map bv_unsigned (map (Z_to_bv 8) l) = l.
Proof.
  intros l H. induction l as [|x r IH]; [reflexivity|]. inversion H; subst. cbn [map]. rewrite (IH ltac:(assumption)). f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. lia.
Qed.
Lemma brange_firstn : forall n l, brange l -> brange (firstn n l).
Proof. intros n l H. unfold brange in *. rewrite <- (firstn_skipn n l) in H. apply Forall_app in H as [A _]. exact A. Qed.
Lemma memcmp_val_zero : forall b1 b2, length b1 = length b2 -> (memcmp_val b1 b2 = 0 <-> map bv_unsigned b1 = map bv_unsigned b2).
Proof.
  induction b1 as [|x r1 IH]; intros [|y r2] Ln; [split; intros; reflexivity | discriminate Ln | discriminate Ln |].
  cbn [memcmp_val map]. pose proof (bv_unsigned_in_range 8 x) as Rx. pose proof (bv_unsigned_in_range 8 y) as Ry.
  destruct (Z.eqb_spec (bv_unsigned x) (bv_unsigned y)) as [EQ|NE].
  - rewrite EQ. destruct (IH r2 ltac:(cbn in Ln; lia)) as [A B]. split; [intros H; f_equal; exact (A H) | intros H; injection H as H; exact (B H)].
  - split; [intros H; exfalso; lia | intros H; injection H as H1 H2; exfalso; exact (NE H1)].
Qed.
Lemma memcmp_val_bound : forall b1 b2, -256 < memcmp_val b1 b2 < 256.
Proof.
  induction b1 as [|x r1 IH]; intros [|y r2]; cbn [memcmp_val]; try lia.
  pose proof (bv_unsigned_in_range 8 x) as Rx. pose proof (bv_unsigned_in_range 8 y) as Ry. change (bv_modulus 8) with 256 in Rx, Ry.
  destruct (Z.eqb (bv_unsigned x) (bv_unsigned y)); [apply IH | lia].
Qed.
Lemma memcmp_zero_iff : forall b1 b2, length b1 = length b2 -> (bv_unsigned (Z_to_bv 64 (memcmp_val b1 b2)) = 0 <-> map bv_unsigned b1 = map bv_unsigned b2).
Proof.
  intros b1 b2 Ln. rewrite <- (memcmp_val_zero b1 b2 Ln). rewrite u_lit64a. pose proof (memcmp_val_bound b1 b2) as B.
  split; intros H.
  - destruct (Z_lt_le_dec (memcmp_val b1 b2) 0) as [N|N].
    + exfalso. rewrite <- (Z.mod_add _ 1 (2 ^ 64)) in H by lia. rewrite Z.mod_small in H by lia. lia.
    + rewrite Z.mod_small in H by lia. exact H.
  - rewrite H. reflexivity.
Qed.
End WithL.
End DKAW.
