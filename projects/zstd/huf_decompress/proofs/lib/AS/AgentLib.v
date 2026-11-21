(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (26 recorded proofs replaced by written proofs (t_emit_app, t_emit_congr, t_alt2_congr and 23 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import
  PropExec CatExec CatSim SeqExec StreamExec ShapeAlg StoreOk.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AgentLib () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List7existsbC46Stdlib5Lists4List9app_assocC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC59OSSVerify5KrLib2AS8ShapeAlg?is_prefix_app_rC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlgCis_prefix_app_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS6CatSimBis_prefix_app_monoC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List8map_consI47Corelib4Init9Datatypes4list00I47Corelib4Init5Logic2ex00I47Corelib4Init5Logic2or00I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or02C59OSSVerify5KrLib2AS8ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC59OSSVerify5KrLib2AS8ShapeAlg4t_eqC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixI4ELinuxProcessSemantics?LinuxProcessSem5State5event00C59OSSVerify5KrLib2AS8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes>Morphisms_Prop?or_iff_morphismC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes?RelationClasses;reflexivityC59OSSVerify5KrLib2AS8ShapeAlg6t_alt2C1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC47Corelib7Classes?RelationClasses>iff_TransitiveC47Corelib7Classes?RelationClasses=iff_ReflexiveC59OSSVerify5KrLib2AS8ShapeAlg=t_emit_nil_eqC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS8ShapeAlg8realizes03C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00c59OSSVerify5KrLib2AS8AgentLib:t_emit_appC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AgentLib<t_emit_congrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg:t_eq_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg8t_eq_symC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List7map_appK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC45stdpp9bitvector;definitions7Z_to_bvK47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC4ELinuxProcessSemantics?LinuxProcessSem6BvBase;word_to_natC4ELinuxProcessSemantics?LinuxProcessSem5State>read_bytes_auxK47Corelib4Init9Datatypes6option01C56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib2AS7StoreOkAstore_ok_read_auxC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z2idC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z4of_NC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions=Z_to_bv_smallC4ELinuxProcessSemantics?LinuxProcessSem5State>read_bytes_mapC4ELinuxProcessSemantics?LinuxProcessSem5StateAread_bytes_map_eqC56Stdlib6ZArith6BinInt1Z2leC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1N00I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes3nat00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes4negbC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC46Stdlib5Lists4List6filterK47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib2AS8PropExec;bv_eqb_reflC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_insertI4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupC47Corelib4Init5Logic9False_indI47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes4bool02c59OSSVerify5KrLib2AS8AgentLib<filter_fd_idC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03c59OSSVerify5KrLib2AS8AgentLib7u64_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec5v_addC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib2AS8PropExec5v_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6v_addiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7bv_wrapK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7mod_modC59OSSVerify5KrLib2AS8PropExec=bv_wrap64_modC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions@Z_to_bv_unsignedK46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith6BinInt1Z3ltbC59OSSVerify5KrLib2AS8PropExec5c_ltuC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib2AS8PropExec4c_eqC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C45stdpp9bitvector;definitions8bv_swrapC56Stdlib6ZArith6BinInt1Z3divK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z9mod_smallC45stdpp9bitvector;definitions?bv_half_modulusC45stdpp9bitvector;definitions9bv_signedC45stdpp9bitvector;definitions>Z_to_bv_signedC56Stdlib6ZArith6BinInt1Z3oppK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z6ltb_gec59OSSVerify5KrLib2AS8AgentLib?bv_signed_smallC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec5c_ltsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_ltK46Stdlib9micromega5Tauto8GFormula03c59OSSVerify5KrLib2AS8AgentLib=bv_signed_negC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec3rdnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AgentLib4zallC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C47Corelib4Init9Datatypes7nat_indC56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6NArith6BinNat1N6to_natC56Stdlib6ZArith4Znat3N2Z9is_nonnegC46Stdlib6ZArith4Znat7N_nat_Zc59OSSVerify5KrLib2AS8AgentLib9zall_specC1?~~~~~~~~~~~~~~~".  (* [comment removed for export] *)
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma t_emit_app : forall (a b : list event) (T : TSet),
  t_eq (t_emit (a ++ b) T) (t_emit a (t_emit b T)).
Proof.
  intros a b T tr. unfold t_emit. split.
  - intros [Hp | (tr' & -> & HT)].
    + apply is_prefix_app_split in Hp as [Hp | (b' & -> & Hp)].
      * left. exact Hp.
      * right. exists b'. split; [reflexivity | left; exact Hp].
    + right. exists (b ++ tr'). split; [rewrite app_assoc; reflexivity|].
      right. exists tr'. auto.
  - intros [Hp | (tr' & -> & [Hp | (tr'' & -> & HT)])].
    + left. apply is_prefix_app_r. exact Hp.
    + left. apply is_prefix_app_mono. exact Hp.
    + right. exists tr''. rewrite app_assoc. auto.
Qed.

Lemma t_emit_congr : forall (e : list event) (T T' : TSet),
  t_eq T T' -> t_eq (t_emit e T) (t_emit e T').
Proof.
  intros e T T' H tr. unfold t_emit. split.
  - intros [Hp | (tr' & -> & HT)]; [left; exact Hp | right; exists tr'; split; [reflexivity | apply H; exact HT]].
  - intros [Hp | (tr' & -> & HT)]; [left; exact Hp | right; exists tr'; split; [reflexivity | apply H; exact HT]].
Qed.

Lemma t_alt2_congr : forall A A' B B' : TSet,
  t_eq A A' -> t_eq B B' -> t_eq (t_alt2 A B) (t_alt2 A' B').
Proof. intros A A' B B' HA HB tr. unfold t_alt2. rewrite (HA tr), (HB tr). reflexivity. Qed.

Lemma t_emit_nil_l : forall (T : TSet), T [] -> t_eq (t_emit [] T) T.
Proof. exact t_emit_nil_eq. Qed.

(* [comment removed for export] *)
Lemma rz_eq : forall segs c (T T' : TSet),
  t_eq T' T -> realizes segs c T' -> realizes segs c T.
Proof. intros segs c T T' Heq H. eapply rz_conseq; [exact H | exact Heq]. Qed.

(* [comment removed for export] *)
Lemma t_emit_app3 : forall (a b c : list event) (T : TSet),
  t_eq (t_emit a (t_emit b (t_emit c T))) (t_emit (a ++ b ++ c) T).
Proof.
  intros a b c T. apply t_eq_sym.
  eapply t_eq_trans; [apply t_emit_app|].
  apply t_emit_congr. apply t_emit_app.
Qed.

(* [comment removed for export] *)
Lemma map_app3 {A B} (f : A -> B) (a b c : list A) :
  map f (a ++ b ++ c) = map f a ++ map f b ++ map f c.
Proof. rewrite !map_app. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma len_word_of_nat : forall (bs : list byte),
  len_word bs = Z_to_bv 64 (Z.of_nat (length bs)).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma read_bytes_map_of_store_ok : forall segs mem (a : word) (n : nat),
  store_ok segs mem a n = true -> (Z.of_nat n < 2 ^ 64)%Z ->
  exists w, read_bytes_map (wview segs mem) a (Z_to_bv 64 (Z.of_nat n)) = Some w.
Proof.
  intros segs mem a n H Hn. rewrite read_bytes_map_eq. unfold word_to_nat.
  rewrite Z_to_bv_small by (unfold bv_modulus; lia). rewrite Nat2Z.id.
  apply store_ok_read_aux. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fd_insert_head_same : forall fds (fd : word) e e',
  fd_insert ((fd, e) :: fds) fd e' = fd_insert fds fd e'.
Proof.
  intros fds fd e e'. unfold fd_insert. cbn [List.filter fst].
  rewrite bv_eqb_refl. cbn [negb]. reflexivity.
Qed.

Lemma filter_fd_id : forall (fds : list (word * FdEntry)) (fd : word),
  fd_lookup fds fd = None ->
  List.filter (fun p => negb (bv_eqb (fst p) fd)) fds = fds.
Proof.
  induction fds as [|[k e] r IH]; intros fd H; [reflexivity|].
  cbn [List.filter fst fd_lookup] in *.
  destruct (bv_eqb k fd) eqn:E; [discriminate|]. cbn [negb].
  rewrite (IH fd H). reflexivity.
Qed.

Lemma fd_insert_fresh_eq : forall fds (fd : word) e,
  fd_lookup fds fd = None -> fd_insert fds fd e = (fd, e) :: fds.
Proof. intros fds fd e H. unfold fd_insert. rewrite (filter_fd_id fds fd H). reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u64_lit : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. apply Z_to_bv_small. unfold bv_modulus. lia. Qed.

(* [comment removed for export] *)
Lemma v_add_lit : forall a b, (0 <= a)%Z -> (0 <= b)%Z -> (a + b < 2 ^ 64)%Z ->
  v_add (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b Ha Hb Hab. unfold v_add. rewrite !u64_lit by lia. reflexivity.
Qed.

Lemma v_sub_lit : forall a b, (0 <= b <= a)%Z -> (a < 2 ^ 64)%Z ->
  v_sub (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof.
  intros a b Hab Ha. unfold v_sub. rewrite !u64_lit by lia. reflexivity.
Qed.

Lemma v_addi_lit : forall a i, (0 <= a < 2 ^ 64)%Z ->
  v_addi (Z_to_bv 64 a) i = Z_to_bv 64 (a + i).
Proof. intros a i Ha. unfold v_addi. rewrite u64_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma Z_to_bv_64_mod : forall z, Z_to_bv 64 z = Z_to_bv 64 (z mod 2 ^ 64).
Proof.
  intro z. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma c_ltu_lit : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
  c_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b)%Z.
Proof. intros a b Ha Hb. unfold c_ltu, bv_ltu. rewrite !u64_lit by lia. reflexivity. Qed.

Lemma c_eq_lit : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
  c_eq (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b)%Z.
Proof. intros a b Ha Hb. unfold c_eq, bv_eqb. rewrite !u64_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma bv_signed_small : forall z, (0 <= z < 2 ^ 63)%Z -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_signed. unfold bv_swrap.
  unfold bv_wrap, bv_half_modulus, bv_modulus.
  replace (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z by reflexivity.
  replace (2 ^ 64 `div` 2)%Z with (2 ^ 63)%Z by reflexivity.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma bv_signed_neg : forall e, (0 < e <= 2 ^ 63)%Z -> bv_signed (Z_to_bv 64 (- e)) = (- e)%Z.
Proof.
  intros e He. rewrite Z_to_bv_signed. unfold bv_swrap.
  unfold bv_wrap, bv_half_modulus, bv_modulus.
  replace (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z by reflexivity.
  replace (2 ^ 64 `div` 2)%Z with (2 ^ 63)%Z by reflexivity.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma c_lts_zero_nonneg : forall z, (0 <= z < 2 ^ 63)%Z ->
  c_lts (Z_to_bv 64 z) (Z_to_bv 64 0) = false.
Proof.
  intros z Hz. unfold c_lts, bv_lts. rewrite !bv_signed_small by lia. apply Z.ltb_ge. lia.
Qed.

Lemma c_lts_zero_errno : forall e, (0 < e <= 2 ^ 63)%Z ->
  c_lts (Z_to_bv 64 (- e)) (Z_to_bv 64 0) = true.
Proof.
  intros e He. unfold c_lts, bv_lts. rewrite bv_signed_neg by lia.
  rewrite bv_signed_small by lia. apply Z.ltb_lt. lia.
Qed.

(* [comment removed for export] *)
Lemma errno_ret_lit : forall e, errno_ret e = Z_to_bv 64 (- e).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Ltac show_goal_marker := match goal with |- ?g => idtac "=====GOAL=====" g end.

(* [comment removed for export] *)
Lemma rdn_addr_eq : forall segs m (a b : word) n r,
  a = b -> rdn segs m b n = r -> rdn segs m a n = r.
Proof. intros segs m a b n r -> H. exact H. Qed.

Ltac rdn_at b :=
  apply (rdn_addr_eq _ _ _ b);
  [ first [ f_equal; lia
          | lazymatch goal with |- ?g => StepTac.check_closed_term g end;
            apply bv_eq; vm_compute; reflexivity ]
  | ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint zall (n : nat) (f : Z -> bool) (z : Z) : bool :=
  match n with
  | O => true
  | S n' => if f z then zall n' f (z + 1)%Z else false
  end.

Lemma zall_spec : forall n f z,
  zall n f z = true -> forall x, (z <= x < z + Z.of_nat n)%Z -> f x = true.
Proof.
  induction n as [|n IH]; intros f z H x Hx; [lia|].
  cbn [zall] in H. destruct (f z) eqn:E; [|discriminate].
  destruct (Z.eq_dec x z) as [->|Hne]; [exact E|].
  apply (IH f (z + 1)%Z H). lia.
Qed.

(* [comment removed for export] *)
Lemma zallN_spec : forall (n : N) f,
  zall (N.to_nat n) f 0%Z = true -> forall x, (0 <= x < Z.of_N n)%Z -> f x = true.
Proof. intros n f H x Hx. apply (zall_spec (N.to_nat n) f 0%Z H). rewrite N_nat_Z. lia. Qed.

(* [comment removed for export] *)
Ltac rdn_at_hyp Hb :=
  lazymatch type of Hb with
  | rdn _ _ ?b _ = _ => rdn_at b; exact Hb
  end.
