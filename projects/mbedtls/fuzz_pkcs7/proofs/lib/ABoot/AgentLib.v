(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import
  PropExec CatExec CatSim SeqExec StreamExec ShapeAlg StoreOk.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AgentLib () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "OSSVerify.KrLib.ABoot.ShapeAlg.TSet"; "OSSVerify.KrLib.ABoot.ShapeAlg.t_eq"; "OSSVerify.KrLib.ABoot.ShapeAlg.t_emit"; "Corelib.Init.Datatypes.app"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "Corelib.Init.Datatypes.true"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.ex"; "LinuxProcessSemantics.LinuxProcessSem.State.read_bytes_map"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.prod"; "LinuxProcessSemantics.LinuxProcessSem.State.FdEntry"; "LinuxProcessSemantics.LinuxProcessSem.State.fd_lookup"; "Corelib.Init.Datatypes.None"; "Stdlib.Lists.List.filter"; "Corelib.Init.Datatypes.negb"; "LinuxProcessSemantics.Riscv.Prelude.bv_eqb"; "Corelib.Init.Datatypes.fst"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.ABoot.PropExec.v_add"; "Corelib.Init.Logic.and"; "OSSVerify.KrLib.ABoot.PropExec.v_sub"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.ABoot.PropExec.c_ltu"; "Stdlib.ZArith.BinInt.Z.ltb"; "OSSVerify.KrLib.ABoot.PropExec.c_eq"; "Stdlib.ZArith.BinInt.Z.eqb"; "Corelib.Numbers.BinNums.N"; "zall"; "Stdlib.NArith.BinNat.N.to_nat"; "Stdlib.ZArith.BinInt.Z.of_N"].


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
Lemma t_emit_app3 : ltac2:(CDefT.buildp (gd_tbl_AgentLib ()) "Pa,(0.$1.)Pb,(0.$1.)Pc,(0.$1.)PT,$2.(3.(4.R4.(4.R3.(4.R2.R1.)))(4.(5.$1.R4.(5.$1.R3.R2.))R1.))")
(* [comment removed for export] *).
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
Lemma read_bytes_map_of_store_ok : ltac2:(CDefT.buildp (gd_tbl_AgentLib ()) "Psegs,(0.$6.)Pmem,P,(7.&40.)(8.(7.&8.))Pa,(7.&40.)Pn,$9.P,(:.$;.(<.R4.R3.R2.R1.)$=.)P,(>.(?.R2.)(10.+2.+40.))(11.(0.(7.&8.))Lw,(0.(7.&8.))(:.(8.(0.(7.&8.)))(12.(13.R7.R6.)R5.(14.&40.(?.R4.)))(15.(0.(7.&8.))R1.)))")
(* [comment removed for export] *).
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

Lemma filter_fd_id : ltac2:(CDefT.buildp (gd_tbl_AgentLib ()) "Pfds,(0.(16.(7.&40.)$17.))Pfd,(7.&40.)P,(:.(8.$17.)(18.R2.R1.)(19.$17.))(:.(0.(16.(7.&40.)$17.))(1:.(16.(7.&40.)$17.)Lp,(16.(7.&40.)$17.)(1;.(1<.&40.(1=.(7.&40.)$17.R1.)R3.))R3.)R3.)")
(* [comment removed for export] *).
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
Lemma v_add_lit : ltac2:(CDefT.buildp (gd_tbl_AgentLib ()) "Pa,$1>.Pb,$1>.P,(1?.=R2.)P,(1?.=R2.)P,(>.(20.R4.R3.)(10.+2.+40.))(:.(7.&40.)(21.(14.&40.R5.)(14.&40.R4.))(14.&40.(20.R5.R4.)))")
(* [comment removed for export] *).
Proof.
  intros a b Ha Hb Hab. unfold v_add. rewrite !u64_lit by lia. reflexivity.
Qed.

Lemma v_sub_lit : ltac2:(CDefT.buildp (gd_tbl_AgentLib ()) "Pa,$1>.Pb,$1>.P,(22.(1?.=R1.)(1?.R1.R2.))P,(>.R3.(10.+2.+40.))(:.(7.&40.)(23.(14.&40.R4.)(14.&40.R3.))(14.&40.(24.R4.R3.)))")
(* [comment removed for export] *).
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
Lemma c_ltu_lit : ltac2:(CDefT.buildp (gd_tbl_AgentLib ()) "Pa,$1>.Pb,$1>.P,(22.(1?.=R2.)(>.R2.(10.+2.+40.)))P,(22.(1?.=R2.)(>.R2.(10.+2.+40.)))(:.$;.(25.(14.&40.R4.)(14.&40.R3.))(26.R4.R3.))")
(* [comment removed for export] *).
Proof. intros a b Ha Hb. unfold c_ltu, bv_ltu. rewrite !u64_lit by lia. reflexivity. Qed.

Lemma c_eq_lit : ltac2:(CDefT.buildp (gd_tbl_AgentLib ()) "Pa,$1>.Pb,$1>.P,(22.(1?.=R2.)(>.R2.(10.+2.+40.)))P,(22.(1?.=R2.)(>.R2.(10.+2.+40.)))(:.$;.(27.(14.&40.R4.)(14.&40.R3.))(28.R4.R3.))")
(* [comment removed for export] *).
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
Lemma zallN_spec : ltac2:(CDefT.buildp (gd_tbl_AgentLib ()) "Pn,$29.Pf,P,$1>.$;.P,(:.$;.(2:.(2;.R2.)R1.=)$=.)Px,$1>.P,(22.(1?.=R1.)(>.R1.(2<.R4.)))(:.$;.A1.R4.R2.$=.)")
(* [comment removed for export] *).
Proof. intros n f H x Hx. apply (zall_spec (N.to_nat n) f 0%Z H). rewrite N_nat_Z. lia. Qed.

(* [comment removed for export] *)
Ltac rdn_at_hyp Hb :=
  lazymatch type of Hb with
  | rdn _ _ ?b _ = _ => rdn_at b; exact Hb
  end.
