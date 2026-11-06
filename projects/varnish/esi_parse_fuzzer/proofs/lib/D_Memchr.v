(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require StepTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require AllocSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require StoreOk WalkTac MmapSim Muslx94 RefMocc D_Me92w D_co2ld.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StepTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim.Hoare OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WalkTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Muslx94 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Me92w OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_co2ld.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition Mc : Z := 0x0101010101010100.   (* [comment removed for export] *)
Definition Hc : Z := 0x8080808080808080.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition LDv (l : list byte) : word := Z_to_bv 64 (bytes_le_to_Z l).

(* [comment removed for export] *)
Definition stn_mark {A : Type} (x : A) : Prop := True.
Definition stn_markm {A : Type} (x : A) : Prop := True.      (* [comment removed for export] *)
Lemma stn_ex_by_eq : forall (A : Type) (P : A -> Prop) (w : A), (forall x, x = w -> P x) -> exists x, P x.
Proof. intros A P w H. exists w. exact (H w eq_refl). Qed.
Lemma stn_msteps_tgt : forall segs st tgt, (forall stF, stF = tgt -> msteps segs st stF) -> msteps segs st tgt.
Proof. intros segs st tgt H. exact (H tgt eq_refl). Qed.
Local Ltac stn_K := constr:(8%nat).
Local Ltac stn_depth R := lazymatch R with regupd ?R' _ _ => let d := stn_depth R' in constr:(S d) | _ => constr:(O) end.
Local Ltac stn_innermost m := lazymatch m with wbytes ?m' _ _ => lazymatch m' with wbytes _ _ _ => stn_innermost m' | _ => m end end.
Local Ltac stn_set t base :=
  let x := fresh base in set (x := t); pose proof (I : stn_mark x).
Local Ltac stn_grow_fact x :=
  let body := eval unfold x in x in
  lazymatch body with wbytes ?p ?a ?bs =>
    let H := fresh "HMG" in
    first [ match goal with Hp : mem_grows ?b0 p |- _ => assert (H : mem_grows b0 x) by (exact (mem_grows_trans b0 p x Hp (wbytes_grows bs p a))) end
          | assert (H : mem_grows p x) by (exact (wbytes_grows bs p a)) ]
  end.
Local Ltac stn_setm t base :=
  let x := fresh base in set (x := t); pose proof (I : stn_markm x); try stn_grow_fact x.
Local Ltac stn_name_regs R :=
  let d := stn_depth R in let k := stn_K in
  lazymatch eval cbv in (Nat.leb k d) with true => stn_set R ident:(RN) | false => idtac end.
Local Ltac stn_name_M :=
  repeat (lazymatch goal with |- msteps _ (mkst _ _ ?M _) _ =>
    lazymatch M with wbytes _ _ _ => idtac end;
    let t := stn_innermost M in stn_setm t ident:(MN) end).
(* [comment removed for export] *)
Local Ltac stn_eexists :=
  lazymatch goal with
  | |- @ex (bvmap _ _) _ => eapply stn_ex_by_eq; (let x := fresh "regsW" in let E := fresh "EregsW" in intros x E; pose proof (I : stn_mark E))
  | |- _ => eexists
  end.
Local Ltac stn_wit :=
  repeat match goal with
  | M : stn_mark ?E |- ?g => lazymatch type of E with ?x = _ => lazymatch g with context [x] => rewrite E end end
  end.
Local Ltac stn_begin :=
  lazymatch goal with
  | |- msteps _ _ ?t => tryif is_var t then idtac else (apply stn_msteps_tgt; let s := fresh "stF" in let E := fresh "EstF" in intros s E)
  | |- _ => idtac
  end.
Local Ltac renm :=
  stn_begin;
  lazymatch goal with
  | |- msteps _ (mkst ?R _ _ _) _ => stn_name_regs R; stn_name_M
  | |- _ => idtac
  end.
Local Ltac stn_open := repeat match goal with H : stn_markm ?x |- ?g => lazymatch g with context [x] => unfold x end end.
Local Ltac stn_done :=
  repeat first [ match goal with H : stn_mark ?x |- ?g => lazymatch g with context [x] => unfold x end end
               | match goal with H : stn_markm ?x |- ?g => lazymatch g with context [x] => unfold x end end ];
  try lazymatch goal with E : ?s = _ |- msteps _ _ ?s => rewrite E end;
  stn_wit.
Local Ltac stn_demand1 :=
  match goal with
  | M : stn_mark ?E |- context [getr ?x _] => lazymatch type of E with x = _ => rewrite E end
  | H : getr ?b ?x = _ |- context [getr ?b ?x] => is_var b; (let body := eval unfold b in b in idtac); rewrite !H
  | |- context [getr ?b ?x] =>
      is_var b;
      let body := eval unfold b in b in
      lazymatch body with regupd _ _ _ => idtac end;
      let l := gresl_list body in
      let bb := gresl_base body in
      let v := gresl_val body x in
      let H := fresh "HGN" in
      assert (H : getr b x = v) by (exact (getr_regupds l bb x (@eq_refl bool false)));
      rewrite !H
  end.
Local Ltac stn_gres_old :=
  repeat match goal with
         | |- context [getr ?X ?r] =>
             lazymatch X with regupd _ _ _ => idtac end;
             let l := gresl_list X in
             let b := gresl_base X in
             let v := gresl_val X r in
             let p := constr:(getr_regupds l b r (@eq_refl bool false) : getr X r = v) in
             rewrite p
         end;
  match goal with |- context [getr _ 0] => rewrite ?getr_zero | _ => idtac end.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WalkTac.gres ::= stn_gres_old; repeat (stn_demand1; stn_gres_old).
Local Ltac stn_sok_old :=
  lazymatch goal with
  | |- store_ok ?segs ?M ?a ?n = true =>
      let b := sokl_base M in
      lazymatch b with
      | M => idtac
      | _ => let l := sokl_list M in
             refine ((store_ok_layers segs n l b a _) : store_ok segs M a n = true)
      end
  | |- _ => idtac
  end.
Local Ltac stn_sok_named :=
  lazymatch goal with |- store_ok ?segs ?M ?a ?n = true =>
    is_var M; match goal with H : mem_grows ?b M |- _ => apply (store_ok_mono segs n b M a H) end end.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk.store_ok_peel ::= stn_sok_old; try stn_sok_named.

Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc.solve_keeps ::=
  stn_wit; repeat (apply keeps_upd; [| not_kept]); first [apply keeps_refl | assumption].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc.solve_keeps_cs ::=
  stn_wit;
  repeat (first [ apply keeps_cs_upd; [| not_kept]
                | apply keeps_cs_upd_same; [| solve [eauto | symmetry; eauto] | let X := fresh in intro X; discriminate X ] ]);
  first [apply keeps_cs_refl | assumption | apply keeps_keeps_cs; assumption].
(* [comment removed for export] *)
Lemma u_LDv : forall l, length l = 8%nat -> bv_unsigned (LDv l) = bytes_le_to_Z l.
Proof. intros l H. unfold LDv. pose proof (bytes_le_to_Z_range l H). apply u_Z2bv; lia. Qed.

(* [comment removed for export] *)
Definition TW (x : word) : word :=
  v_and (v_or (v_sub (Z_to_bv 64 Mc) (v_xor x (Z_to_bv 64 0))) (v_xor x (Z_to_bv 64 0))) (Z_to_bv 64 Hc).

Lemma v_xor_0 : forall x : word, v_xor x (Z_to_bv 64 0) = x.
Proof.
  intros x. unfold v_xor. rewrite (u_Z2bv 0) by lia. rewrite Z.lxor_0_r. apply Z_to_bv_bv_unsigned.
Qed.

(* [comment removed for export] *)
Lemma TW_bits : forall x : word, let y := bv_unsigned x in
  (forall i, (0 <= i)%Z ->
     Z.testbit (bv_unsigned (TW x)) i = (Z.testbit Hc i && negb (Z.testbit (HZ.Tz y) i))%bool)
  /\ (forall i, (0 <= i)%Z -> Z.testbit (HZ.Tz y) i = true -> Z.testbit Hc i = true).
Proof.
  intros x y. pose proof (u64_range x) as Hx. subst y.
  assert (A64 : (0 <= (bv_unsigned x + HZ.ONESNEG) mod 2 ^ 64 < 2 ^ 64)%Z) by (apply Z.mod_pos_bound; lia).
  set (A := ((bv_unsigned x + HZ.ONESNEG) mod 2 ^ 64)%Z) in *.
  (* [comment removed for export] *)
  assert (SUB : ((Mc - bv_unsigned x) mod 2 ^ 64 = 2 ^ 64 - 1 - A)%Z).
  { subst A. unfold Mc, HZ.ONESNEG.
    rewrite <- (Z.mod_add _ 1) by lia.
    replace (72340172838076672 - bv_unsigned x + 1 * 2 ^ 64)%Z
      with (2 ^ 64 - 1 - (bv_unsigned x + 18374403900871474943) + 1 * 2 ^ 64)%Z by lia.
    set (z := (bv_unsigned x + 18374403900871474943)%Z).
    rewrite Zminus_mod_idemp_r || idtac.
    pose proof (Z.div_mod z (2^64) ltac:(lia)). pose proof (Z.mod_pos_bound z (2^64) ltac:(lia)).
    set (q := (z / 2 ^ 64)%Z) in *. set (r := (z mod 2 ^ 64)%Z) in *.
    replace (2 ^ 64 - 1 - z + 1 * 2 ^ 64)%Z with ((2 ^ 64 - 1 - r) + (1 - q) * 2 ^ 64)%Z by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  assert (NOTA : forall i, (0 <= i < 64)%Z -> Z.testbit (2 ^ 64 - 1 - A) i = negb (Z.testbit A i)).
  { intros i Hi. replace (2 ^ 64 - 1 - A)%Z with ((Z.lnot A) mod 2 ^ 64)%Z.
    - rewrite Z.mod_pow2_bits_low by lia. apply Z.lnot_spec. lia.
    - unfold Z.lnot. replace (Z.pred (- A)) with ((2 ^ 64 - 1 - A) + (-1) * 2 ^ 64)%Z by lia.
      rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  assert (TWu : bv_unsigned (TW x) = Z.land (Z.lor ((Mc - bv_unsigned x) mod 2 ^ 64) (bv_unsigned x)) Hc).
  { unfold TW. rewrite !v_xor_0. unfold v_and, v_or, v_sub.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
    rewrite (Z.mod_small Mc) by (unfold Mc; lia). rewrite (Z.mod_small Hc) by (unfold Hc; lia).
    assert (R1 : (0 <= (Mc - bv_unsigned x) mod 2 ^ 64 < 2 ^ 64)%Z) by (apply Z.mod_pos_bound; lia).
    assert (R2 : (0 <= Z.lor ((Mc - bv_unsigned x) mod 2 ^ 64) (bv_unsigned x) < 2 ^ 64)%Z) by (apply Z_lor_range; lia).
    rewrite (Z.mod_small (Z.lor _ _)) by exact R2.
    apply Z.mod_small. apply Z_land_range; [exact R2 | unfold Hc; lia]. }
  split.
  - intros i Hi. rewrite TWu, SUB.
    unfold HZ.Tz. fold A.
    rewrite Z.land_spec. rewrite Z.lor_spec. rewrite Z.land_spec. rewrite Z.land_spec. rewrite Z.lxor_spec.
    change HZ.HIGHS with Hc.
    destruct (Z.lt_ge_cases i 64) as [Hl|Hh].
    + rewrite NOTA by lia.
      replace (Z.testbit HZ.ALLONES i) with true.
      2:{ symmetry. unfold HZ.ALLONES. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.ones_spec_low; [reflexivity|lia]. }
      destruct (Z.testbit A i), (Z.testbit (bv_unsigned x) i), (Z.testbit Hc i); reflexivity.
    + replace (Z.testbit Hc i) with false.
      2:{ symmetry. apply (Z_testbit_high 64); unfold Hc; lia. }
      rewrite andb_false_r. reflexivity.
  - intros i Hi H. unfold HZ.Tz in H. rewrite Z.land_spec in H. rewrite Z.land_spec in H.
    change HZ.HIGHS with Hc in H.
    destruct (Z.testbit Hc i); [reflexivity|]. rewrite andb_false_r in H. discriminate H.
Qed.

Lemma TW_eq_H : forall x : word, c_eq (TW x) (Z_to_bv 64 Hc) = Z.eqb (HZ.Tz (bv_unsigned x)) 0.
Proof.
  intros x. destruct (TW_bits x) as [B1 B2].
  unfold c_eq, bv_eqb. rewrite (u_Z2bv Hc) by (unfold Hc; lia).
  pose proof (HZ.Tz_range (bv_unsigned x)) as TR.
  destruct (Z.eqb_spec (HZ.Tz (bv_unsigned x)) 0) as [Z0|NZ].
  - apply Z.eqb_eq. apply Z.bits_inj'. intros i Hi. rewrite B1 by lia. rewrite Z0, Z.bits_0.
    rewrite andb_true_r. reflexivity.
  - apply Z.eqb_neq. intros E.
    apply NZ. apply Z.bits_inj'. intros i Hi. rewrite Z.bits_0.
    destruct (Z.testbit (HZ.Tz (bv_unsigned x)) i) eqn:T; [|reflexivity].
    pose proof (B2 i Hi T) as HH.
    pose proof (B1 i Hi) as BB. rewrite E, HH, T in BB. discriminate BB.
Qed.

(* [comment removed for export] *)
Lemma TW_nozero : forall l, length l = 8%nat ->
  (forall i, (i < 8)%nat -> bv_unsigned (nth i l (Z_to_bv 8 0)) <> 0%Z) ->
  c_eq (TW (LDv l)) (Z_to_bv 64 Hc) = true.
Proof.
  intros l Hl Hnz. rewrite TW_eq_H. apply Z.eqb_eq.
  rewrite u_LDv by exact Hl. apply HZ.Tz_nozero.
  - apply bytes_le_to_Z_range. exact Hl.
  - intros i Hi. rewrite zb_of_bytes by (rewrite Hl; exact Hi). apply Hnz. exact Hi.
Qed.

Lemma TW_haszero : forall l (i : nat), length l = 8%nat -> (i < 8)%nat ->
  bv_unsigned (nth i l (Z_to_bv 8 0)) = 0%Z ->
  (forall j, (j < i)%nat -> bv_unsigned (nth j l (Z_to_bv 8 0)) <> 0%Z) ->
  c_eq (TW (LDv l)) (Z_to_bv 64 Hc) = false.
Proof.
  intros l i Hl Hi Hz Hnz. rewrite TW_eq_H. apply Z.eqb_neq.
  rewrite u_LDv by exact Hl. apply (HZ.Tz_haszero _ i).
  - apply bytes_le_to_Z_range. exact Hl.
  - exact Hi.
  - rewrite zb_of_bytes by (rewrite Hl; exact Hi). exact Hz.
  - intros j Hj. rewrite zb_of_bytes by (rewrite Hl; lia). apply Hnz. exact Hj.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rodata_clear (mem : word -> option byte) : Prop :=
  forall i, (0x12950 <= i < 0x12968)%Z -> mem (Z_to_bv 64 i) = None.

Lemma rd_const_M : forall mem, rodata_clear mem ->
  exists bs, rdn RSEGS mem (Z_to_bv 64 0x12960) 8 = Some bs /\ bytes_le_to_Z bs = bv_unsigned (Z_to_bv 64 Mc).
Proof.
  intros mem Hr.
  rewrite (rdn_ext RSEGS 8 mem (fun _ => None)).
  - eexists. split; [vm_compute; reflexivity|]. vm_compute. reflexivity.
  - change (bv_unsigned (Z_to_bv 64 76128)) with 76128%Z. cbn. lia.
  - intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Hr.
    change (bv_unsigned (Z_to_bv 64 76128)) with 76128%Z in Hx. cbn in Hx. lia.
Qed.

Lemma rd_const_H : forall mem, rodata_clear mem ->
  exists bs, rdn RSEGS mem (Z_to_bv 64 0x12950) 8 = Some bs /\ bytes_le_to_Z bs = bv_unsigned (Z_to_bv 64 Hc).
Proof.
  intros mem Hr.
  rewrite (rdn_ext RSEGS 8 mem (fun _ => None)).
  - eexists. split; [vm_compute; reflexivity|]. vm_compute. reflexivity.
  - change (bv_unsigned (Z_to_bv 64 76112)) with 76112%Z. cbn. lia.
  - intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Hr.
    change (bv_unsigned (Z_to_bv 64 76112)) with 76112%Z in Hx. cbn in Hx. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nth_sub : forall (bs : list byte) j m i d,
  (i < m)%nat -> (j + m <= length bs)%nat -> nth i (sub bs j m) d = nth (j + i) bs d.
Proof.
  intros bs j m i d Hi Hjm. unfold sub.
  rewrite nth_firstn. replace (i <? m)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi).
  rewrite nth_skipn. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma c_eq_LBv_0 : forall b : byte, c_eq (LBv b) (Z_to_bv 64 0) = (bv_unsigned b =? 0)%Z.
Proof.
  intros b. unfold c_eq, bv_eqb, LBv. pose proof (bv_unsigned_in_range _ b) as R.
  change (bv_modulus 8) with 256%Z in R.
  rewrite (u_Z2bv (bv_unsigned b)) by lia. rewrite (u_Z2bv 0) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record mchrH (mem : word -> option byte) (s : word) (buf : list byte) (K n : Z) : Prop := MCHRH {
  (* [comment removed for export] *)
  Hbuf : rdn RSEGS mem s (length buf) = Some buf;
  (* [comment removed for export] *)
  Hwin : ((bv_unsigned s + K) / 8 * 8 + 8 <= bv_unsigned s + Z.of_nat (length buf))%Z;
  Hnw  : (bv_unsigned s + Z.of_nat (length buf) < 2 ^ 64)%Z;
  (* [comment removed for export] *)
  HK0  : (0 <= K)%Z;
  Hzero : bv_unsigned (nth (Z.to_nat K) buf (Z_to_bv 8 0)) = 0%Z;
  Hnz  : forall j, (j < Z.to_nat K)%nat -> bv_unsigned (nth j buf (Z_to_bv 8 0)) <> 0%Z;
  (* [comment removed for export] *)
  HKn  : (K + 8 <= n)%Z;
  Hn64 : (n < 2 ^ 64)%Z;
  Hro  : rodata_clear mem }.

Section MCHR.
  Variable mem : word -> option byte.
  Variable s : word.
  Variable buf : list byte.
  Variables K n : Z.
  Variable rom : word -> option byte.
  Hypothesis HOK : mchrH mem s buf K n.

  #[local] Notation L := (Z.of_nat (length buf)).
  Definition b_ (j : Z) : byte := nth (Z.to_nat j) buf (Z_to_bv 8 0).
  Definition sb_ (j : Z) (m : nat) : list byte := sub buf (Z.to_nat j) m.

  Let Hbuf := Hbuf _ _ _ _ _ HOK.
  Let Hwin : ((bv_unsigned s + K) / 8 * 8 + 8 <= bv_unsigned s + L)%Z := Hwin _ _ _ _ _ HOK.
  Let Hnw : (bv_unsigned s + L < 2 ^ 64)%Z := Hnw _ _ _ _ _ HOK.
  Let HK0 : (0 <= K)%Z := HK0 _ _ _ _ _ HOK.
  Let HKn : (K + 8 <= n)%Z := HKn _ _ _ _ _ HOK.
  Let Hn64 : (n < 2 ^ 64)%Z := Hn64 _ _ _ _ _ HOK.
  Let Hro := Hro _ _ _ _ _ HOK.

  Lemma KL : (K + 1 <= L)%Z.
  Proof.
    clear -Hwin HK0. pose proof (u64_range s).
    pose proof (Z.div_mod (bv_unsigned s + K) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (bv_unsigned s + K) 8 ltac:(lia)). lia.
  Qed.

  (* [comment removed for export] *)
  Definition KE : Z := ((bv_unsigned s + K) / 8 * 8 + 8 - bv_unsigned s)%Z.
  Lemma KE_facts : (K + 1 <= KE <= K + 8)%Z /\ (KE <= L)%Z /\ ((bv_unsigned s + KE) mod 8 = 0)%Z.
  Proof.
    unfold KE. clear -Hwin HK0. pose proof (u64_range s).
    pose proof (Z.div_mod (bv_unsigned s + K) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (bv_unsigned s + K) 8 ltac:(lia)).
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia.
    replace (bv_unsigned s + ((bv_unsigned s + K) / 8 * 8 + 8 - bv_unsigned s))%Z
      with (8 + ((bv_unsigned s + K) / 8) * 8)%Z by lia.
    rewrite Z.mod_add by lia. reflexivity.
  Qed.

  Lemma bz : bv_unsigned (b_ K) = 0%Z.
  Proof. exact (Hzero _ _ _ _ _ HOK). Qed.
  Lemma bnz : forall j, (0 <= j < K)%Z -> bv_unsigned (b_ j) <> 0%Z.
  Proof. intros j Hj. unfold b_. apply (Hnz _ _ _ _ _ HOK). lia. Qed.

  Lemma rd_w : forall j m, (0 <= j)%Z -> (j + Z.of_nat m <= L)%Z ->
    rdn RSEGS mem (at_ s j) m = Some (sb_ j m).
  Proof.
    intros j m Hj Hm. unfold sb_.
    replace (at_ s j) with (at_ s (Z.of_nat (Z.to_nat j))) by (f_equal; lia).
    apply (rdn_sub RSEGS mem (length buf)); [exact Hbuf | lia].
  Qed.

  Lemma rd_b : forall j, (0 <= j)%Z -> (j + 1 <= L)%Z ->
    rdn RSEGS mem (at_ s j) 1 = Some [b_ j].
  Proof.
    intros j Hj H1. rewrite (rd_w j 1) by lia. unfold sb_, b_.
    rewrite sub_nth; [reflexivity | lia].
  Qed.

  Lemma sb_len : forall j m, (0 <= j)%Z -> (j + Z.of_nat m <= L)%Z -> length (sb_ j m) = m.
  Proof. intros j m Hj Hm. unfold sb_. apply sub_length. lia. Qed.

  Lemma sb_nth : forall j (i : nat), (0 <= j)%Z -> (i < 8)%nat -> (j + 8 <= L)%Z ->
    nth i (sb_ j 8) (Z_to_bv 8 0) = b_ (j + Z.of_nat i).
  Proof.
    intros j i Hj Hi H8. unfold sb_, b_. rewrite nth_sub by lia. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma m_lbu : forall regs pc w rd rs (imm : bv 12) j0 j,
    fetch_word RSEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) ->
    getr regs rs = at_ s j0 -> (j0 + bv_signed imm = j)%Z ->
    (0 <= j)%Z -> (j + 1 <= L)%Z ->
    RiscvSemantics.step RSEGS (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (LBv (b_ j))) (v_addi pc 4) mem rom).
  Proof.
    intros regs pc w rd rs imm j0 j Hf He Hd Hrs Hj Hj0 Hj1.
    eapply step_lbu; [exact Hf | exact He | exact Hd |].
    rewrite Hrs, at_addi, Hj. apply rd_b; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma m_ld : forall regs pc w rd rs (imm : bv 12) j0 j,
    fetch_word RSEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Load SZ8 true rd rs imm, 4%Z) ->
    getr regs rs = at_ s j0 -> (j0 + bv_signed imm = j)%Z ->
    (0 <= j)%Z -> (j + 8 <= L)%Z ->
    RiscvSemantics.step RSEGS (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (LDv (sb_ j 8))) (v_addi pc 4) mem rom).
  Proof.
    intros regs pc w rd rs imm j0 j Hf He Hd Hrs Hj Hj0 Hj8.
    eapply step_ld; [exact Hf | exact He | exact Hd | |].
    - rewrite Hrs, at_addi, Hj. apply (rd_w j 8); lia.
    - symmetry. apply u_LDv. apply sb_len; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma al_room : forall j, ((bv_unsigned s + j) mod 8 = 0)%Z -> (0 <= j <= K)%Z -> (j + 8 <= KE)%Z.
  Proof.
    intros j Hal Hj. unfold KE. clear -Hal Hj HK0. pose proof (u64_range s).
    pose proof (Z.div_mod (bv_unsigned s + K) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (bv_unsigned s + K) 8 ltac:(lia)).
    pose proof (Z.div_mod (bv_unsigned s + j) 8 ltac:(lia)).
    assert ((bv_unsigned s + j) / 8 <= (bv_unsigned s + K) / 8)%Z by (apply Z.div_le_mono; lia).
    lia.
  Qed.

  (* [comment removed for export] *)
  Lemma tw_hit : forall j, (0 <= j <= K)%Z -> (K < j + 8)%Z -> (j + 8 <= L)%Z ->
    c_eq (TW (LDv (sb_ j 8))) (Z_to_bv 64 Hc) = false.
  Proof.
    intros j Hj HKj HL.
    apply (TW_haszero _ (Z.to_nat (K - j))).
    - apply sb_len; lia.
    - lia.
    - rewrite sb_nth by lia. rewrite <- bz. f_equal. unfold b_. f_equal. lia.
    - intros jj Hjj. rewrite sb_nth by lia. apply bnz. lia.
  Qed.

  Lemma tw_miss : forall j, (0 <= j)%Z -> (j + 8 <= K)%Z -> (j + 8 <= L)%Z ->
    c_eq (TW (LDv (sb_ j 8))) (Z_to_bv 64 Hc) = true.
  Proof.
    intros j Hj HKj HL. apply TW_nozero.
    - apply sb_len; lia.
    - intros i Hi. rewrite sb_nth by lia. apply bnz. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Ltac mlbu F D jj :=
    chain_step; [reflexivity
      | eapply m_lbu with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; first [reflexivity | f_equal; lia] | imm_norm; lia | lia | lia]
      | step_simpl]; vnorm.
  Ltac mld F D jj :=
    chain_step; [reflexivity
      | eapply m_ld with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; first [reflexivity | f_equal; lia] | imm_norm; lia | lia | lia]
      | step_simpl]; vnorm.

  (* [comment removed for export] *)
  Ltac condb :=
    rwH; rewrite c_eq_LBv_0;
    first [ apply Z.eqb_eq; rewrite <- bz; f_equal; f_equal; lia
          | apply Z.eqb_neq; apply bnz; lia ].
  (* [comment removed for export] *)
  Ltac cond := try unfold v_addi; cond_lia.
  (* [comment removed for export] *)
  Ltac condw lem :=
    rwH;
    lazymatch goal with |- c_eq (v_and (v_or (v_sub _ (v_xor ?x _)) _) _) _ = ?b =>
      change (c_eq (TW x) (Z_to_bv 64 Hc) = b) end;
    apply lem; lia.

  Ltac post := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; gres; rwH; rewrite ?at_addi; try reflexivity; try (f_equal; lia);
               try (unfold v_addi; unorm; f_equal; lia); try solve_keeps_cs.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma t_found : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret -> getr regs 10 = at_ s K -> getr regs 11 = Z_to_bv 64 0 ->
    exists regs',
      msteps RSEGS (mkst regs (0x2abf8 : word) mem rom) (mkst regs' ret mem rom)
      /\ getr regs' 10 = at_ s K /\ keeps_cs regs regs'.
  Proof.
    intros regs ret Hret H1 H10 H11. pose proof KL. stn_eexists. split.
    - mlbu F_2abf8 D_2abf8 K.                       (* [comment removed for export] *)
      renm. stepb_tk F_2abfc D_2abfc ltac:(condb).        (* [comment removed for export] *)
      renm. stepret F_2ac10 D_2ac10 ret ltac:(exact H1).
      stn_done. apply mst_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma t_loop : forall (i : nat) regs (ret : word) j m,
    ret_ok ret -> getr regs 1 = ret -> getr regs 10 = at_ s j -> getr regs 11 = Z_to_bv 64 0 ->
    getr regs 13 = Z_to_bv 64 m ->
    (0 <= j < K)%Z -> (Z.of_nat i = K - 1 - j)%Z -> (K - j + 1 <= m < 2 ^ 64)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x2ac00 : word) mem rom) (mkst regs' ret mem rom)
      /\ getr regs' 10 = at_ s K /\ keeps_cs regs regs'.
  Proof.
    pose proof KL as HKL.
    induction i as [|i IH]; intros regs ret j m Hret H1 H10 H11 H13 Hj Hi Hm.
    - (* [comment removed for export] *)
      stn_eexists. split.
      + renm. stepn F_2ac00 D_2ac00.                      (* [comment removed for export] *)
        renm. stepn F_2ac04 D_2ac04.                      (* [comment removed for export] *)
        renm. stepb_tk F_2ac08 D_2ac08 ltac:(cond).       (* [comment removed for export] *)
        mlbu F_2abf8 D_2abf8 K.                     (* [comment removed for export] *)
        renm. stepb_tk F_2abfc D_2abfc ltac:(condb).      (* [comment removed for export] *)
        renm. stepret F_2ac10 D_2ac10 ret ltac:(exact H1).
        stn_done. apply mst_refl.
      + post.
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x2ac00 : word) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = at_ s (j + 1) /\ getr r 11 = Z_to_bv 64 0
                         /\ getr r 13 = Z_to_bv 64 (m - 1) /\ keeps_cs regs r)).
      + stn_eexists. split.
        * renm. stepn F_2ac00 D_2ac00.                    (* [comment removed for export] *)
          renm. stepn F_2ac04 D_2ac04.                    (* [comment removed for export] *)
          renm. stepb_tk F_2ac08 D_2ac08 ltac:(cond).     (* [comment removed for export] *)
          mlbu F_2abf8 D_2abf8 (j + 1)%Z.           (* [comment removed for export] *)
          renm. stepb_ft F_2abfc D_2abfc ltac:(condb).    (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * post.
      + cbv beta. (intros r1; (first [ intro dR_17; dand5 dR_17 as R1 R10 R11 R13 KC | intros (R1 & R10 & R11 & R13 & KC) ])).
        (first [ pose proof ((IH r1 ret (j + 1)%Z (m - 1)%Z Hret R1 R10 R11 R13 ltac:(lia) ltac:(lia) ltac:(lia))) as dR_1; dex1 dR_1 as r2; dand3 dR_1 as RUN A10 K2 | pose proof ((IH r1 ret (j + 1)%Z (m - 1)%Z Hret R1 R10 R11 R13 ltac:(lia) ltac:(lia) ltac:(lia))) as dR_1; dand4 dR_1 as r2 RUN A10 K2 | destruct (IH r1 ret (j + 1)%Z (m - 1)%Z Hret R1 R10 R11 R13 ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & A10 & K2) ]).
        exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma w_loop : forall (i : nat) regs (ret : word) j m,
    ret_ok ret -> getr regs 1 = ret -> getr regs 10 = at_ s j -> getr regs 11 = Z_to_bv 64 0 ->
    getr regs 12 = Z_to_bv 64 m -> getr regs 13 = Z_to_bv 64 Mc -> getr regs 14 = Z_to_bv 64 Hc ->
    getr regs 15 = Z_to_bv 64 0 -> getr regs 16 = Z_to_bv 64 7 ->
    (0 <= j <= K)%Z -> ((bv_unsigned s + j) mod 8 = 0)%Z -> (Z.of_nat i = (K - j) / 8)%Z ->
    (K - j + 8 <= m < 2 ^ 64)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x2abcc : word) mem rom) (mkst regs' ret mem rom)
      /\ getr regs' 10 = at_ s K /\ keeps_cs regs regs'.
  Proof.
    pose proof KL as HKL. (first [ pose proof (KE_facts) as dR_2; dand3 dR_2 as HKE1 HKE2 HKE3 | pose proof KE_facts as (HKE1 & HKE2 & HKE3) ]).
    induction i as [|i IH]; intros regs ret j m Hret H1 H10 H11 H12 H13 H14 H15 H16 Hj Hal Hi Hm;
      pose proof (al_room j Hal Hj) as HR.
    - (* [comment removed for export] *)
      assert (HKj : (K < j + 8)%Z).
      { clear -Hi Hj. pose proof (Z.div_mod (K - j) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (K - j) 8 ltac:(lia)). lia. }
      destruct (Z.eq_dec j K) as [HjK|HjK].
      + (* [comment removed for export] *)
        stn_eexists. split.
        * renm. mld F_2abcc D_2abcc j.                    (* [comment removed for export] *)
          renm. stepn F_2abd0 D_2abd0.                    (* [comment removed for export] *)
          renm. stepn F_2abd4 D_2abd4.                    (* [comment removed for export] *)
          renm. stepn F_2abd8 D_2abd8.                    (* [comment removed for export] *)
          renm. stepn F_2abdc D_2abdc.                    (* [comment removed for export] *)
          renm. stepb_tk F_2abe0 D_2abe0 ltac:(condw tw_hit).   (* [comment removed for export] *)
          renm. stepn F_2ac14 D_2ac14.                    (* [comment removed for export] *)
          mlbu F_2ac18 D_2ac18 j.                   (* [comment removed for export] *)
          renm. stepb_ft F_2ac1c D_2ac1c ltac:(condb).    (* [comment removed for export] *)
          renm. stepn F_2ac20 D_2ac20.                    (* [comment removed for export] *)
          renm. stepret F_2ac10 D_2ac10 ret ltac:(exact H1).
          stn_done. apply mst_refl.
        * post.
      + (* [comment removed for export] *)
        eapply (runs_trans RSEGS _ (fun r => mkst r (0x2ac00 : word) mem rom)
                 (fun r => getr r 1 = ret /\ getr r 10 = at_ s j /\ getr r 11 = Z_to_bv 64 0
                           /\ getr r 13 = Z_to_bv 64 m /\ keeps_cs regs r)).
        * stn_eexists. split.
          -- renm. mld F_2abcc D_2abcc j.
             renm. stepn F_2abd0 D_2abd0.
             renm. stepn F_2abd4 D_2abd4.
             renm. stepn F_2abd8 D_2abd8.
             renm. stepn F_2abdc D_2abdc.
             renm. stepb_tk F_2abe0 D_2abe0 ltac:(condw tw_hit).
             renm. stepn F_2ac14 D_2ac14.                 (* [comment removed for export] *)
             mlbu F_2ac18 D_2ac18 j.                (* [comment removed for export] *)
             renm. stepb_tk F_2ac1c D_2ac1c ltac:(condb). (* [comment removed for export] *)
             stn_done. apply mst_refl.
          -- post.
        * cbv beta. (intros r1; (first [ intro dR_18; dand5 dR_18 as R1 R10 R11 R13 KC | intros (R1 & R10 & R11 & R13 & KC) ])).
          (first [ pose proof ((t_loop (Z.to_nat (K - 1 - j)) r1 ret j m Hret R1 R10 R11 R13
                      ltac:(lia) ltac:(lia) ltac:(lia))) as dR_3; dex1 dR_3 as r2; dand3 dR_3 as RUN A10 K2 | pose proof ((t_loop (Z.to_nat (K - 1 - j)) r1 ret j m Hret R1 R10 R11 R13
                      ltac:(lia) ltac:(lia) ltac:(lia))) as dR_3; dand4 dR_3 as r2 RUN A10 K2 | destruct (t_loop (Z.to_nat (K - 1 - j)) r1 ret j m Hret R1 R10 R11 R13
                      ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & A10 & K2) ]).
          exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
    - (* [comment removed for export] *)
      assert (HKj : (j + 8 <= K)%Z).
      { clear -Hi Hj. pose proof (Z.div_mod (K - j) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (K - j) 8 ltac:(lia)). lia. }
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x2abcc : word) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = at_ s (j + 8) /\ getr r 11 = Z_to_bv 64 0
                         /\ getr r 12 = Z_to_bv 64 (m - 8) /\ getr r 13 = Z_to_bv 64 Mc /\ getr r 14 = Z_to_bv 64 Hc
                         /\ getr r 15 = Z_to_bv 64 0 /\ getr r 16 = Z_to_bv 64 7 /\ keeps_cs regs r)).
      + stn_eexists. split.
        * renm. mld F_2abcc D_2abcc j.
          renm. stepn F_2abd0 D_2abd0.
          renm. stepn F_2abd4 D_2abd4.
          renm. stepn F_2abd8 D_2abd8.
          renm. stepn F_2abdc D_2abdc.
          renm. stepb_ft F_2abe0 D_2abe0 ltac:(condw tw_miss).  (* [comment removed for export] *)
          renm. stepn F_2abe4 D_2abe4.                    (* [comment removed for export] *)
          renm. stepn F_2abe8 D_2abe8.                    (* [comment removed for export] *)
          renm. stepb_tk F_2abec D_2abec ltac:(cond).     (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * post.
      + cbv beta. (intros r1; (first [ intro dR_19; dand9 dR_19 as R1 R10 R11 R12 R13 R14 R15 R16 KC | intros (R1 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & KC) ])).
        (first [ pose proof ((IH r1 ret (j + 8)%Z (m - 8)%Z Hret R1 R10 R11 R12 R13 R14 R15 R16 ltac:(lia)
                    ltac:(rewrite Z.add_assoc, <- Zplus_mod_idemp_l, Hal; reflexivity)
                    ltac:(clear -Hi HKj; pose proof (Z.div_mod (K - j) 8 ltac:(lia));
                          pose proof (Z.mod_pos_bound (K - j) 8 ltac:(lia));
                          pose proof (Z.div_mod (K - (j + 8)) 8 ltac:(lia));
                          pose proof (Z.mod_pos_bound (K - (j + 8)) 8 ltac:(lia)); nia)
                    ltac:(lia))) as dR_4; dex1 dR_4 as r2; dand3 dR_4 as RUN A10 K2 | pose proof ((IH r1 ret (j + 8)%Z (m - 8)%Z Hret R1 R10 R11 R12 R13 R14 R15 R16 ltac:(lia)
                    ltac:(rewrite Z.add_assoc, <- Zplus_mod_idemp_l, Hal; reflexivity)
                    ltac:(clear -Hi HKj; pose proof (Z.div_mod (K - j) 8 ltac:(lia));
                          pose proof (Z.mod_pos_bound (K - j) 8 ltac:(lia));
                          pose proof (Z.div_mod (K - (j + 8)) 8 ltac:(lia));
                          pose proof (Z.mod_pos_bound (K - (j + 8)) 8 ltac:(lia)); nia)
                    ltac:(lia))) as dR_4; dand4 dR_4 as r2 RUN A10 K2 | destruct (IH r1 ret (j + 8)%Z (m - 8)%Z Hret R1 R10 R11 R12 R13 R14 R15 R16 ltac:(lia)
                    ltac:(rewrite Z.add_assoc, <- Zplus_mod_idemp_l, Hal; reflexivity)
                    ltac:(clear -Hi HKj; pose proof (Z.div_mod (K - j) 8 ltac:(lia));
                          pose proof (Z.mod_pos_bound (K - j) 8 ltac:(lia));
                          pose proof (Z.div_mod (K - (j + 8)) 8 ltac:(lia));
                          pose proof (Z.mod_pos_bound (K - (j + 8)) 8 ltac:(lia)); nia)
                    ltac:(lia)) as (r2 & RUN & A10 & K2) ]).
        exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac ldc F D vv RD :=
    chain_step; [reflexivity
      | eapply step_ld with (v := vv);
        [exact F | reflexivity | exact D
        | gres; imm_norm;
          lazymatch goal with |- rdn _ _ ?a _ = _ =>
            lazymatch type of RD with rdn _ _ ?c _ = _ =>
              replace a with c by (apply bv_eq; vm_compute; reflexivity) end end;
          exact RD
        | assumption ]
      | step_simpl]; vnorm.

  Lemma a_entry : forall regs (ret : word) j m,
    ret_ok ret -> getr regs 1 = ret -> getr regs 10 = at_ s j -> getr regs 11 = Z_to_bv 64 0 ->
    getr regs 12 = Z_to_bv 64 m -> getr regs 14 = Z_to_bv 64 1 ->
    (0 <= j <= K)%Z -> ((bv_unsigned s + j) mod 8 = 0)%Z -> (K - j + 8 <= m < 2 ^ 64)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x2ab9c : word) mem rom) (mkst regs' ret mem rom)
      /\ getr regs' 10 = at_ s K /\ keeps_cs regs regs'.
  Proof.
    intros regs ret j m Hret H1 H10 H11 H12 H14 Hj Hal Hm.
    pose proof KL as HKL. (first [ pose proof (KE_facts) as dR_5; dand3 dR_5 as HKE1 HKE2 HKE3 | pose proof KE_facts as (HKE1 & HKE2 & HKE3) ]). pose proof (al_room j Hal Hj) as HR.
    (first [ pose proof ((rd_const_M mem Hro)) as dR_6; dex1 dR_6 as bsM; destruct dR_6 as [RM EM] | pose proof ((rd_const_M mem Hro)) as dR_6; dand3 dR_6 as bsM RM EM | destruct (rd_const_M mem Hro) as (bsM & RM & EM) ]).
    (first [ pose proof ((rd_const_H mem Hro)) as dR_7; dex1 dR_7 as bsH; destruct dR_7 as [RH EH] | pose proof ((rd_const_H mem Hro)) as dR_7; dand3 dR_7 as bsH RH EH | destruct (rd_const_H mem Hro) as (bsH & RH & EH) ]).
    destruct (Z.eq_dec j K) as [HjK|HjK].
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x2abf8 : word) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = at_ s K /\ getr r 11 = Z_to_bv 64 0 /\ keeps_cs regs r)).
      + stn_eexists. split.
        * renm. stepb_ft F_2ab9c D_2ab9c ltac:(cond).     (* [comment removed for export] *)
          mlbu F_2aba0 D_2aba0 j.                   (* [comment removed for export] *)
          renm. stepb_tk F_2aba4 D_2aba4 ltac:(condb).    (* [comment removed for export] *)
          renm. stepn F_2abf0 D_2abf0.                    (* [comment removed for export] *)
          renm. stepb_ft F_2abf4 D_2abf4 ltac:(cond).     (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * post.
      + cbv beta. (intros r1; (first [ intro dR_20; dand4 dR_20 as R1 R10 R11 KC | intros (R1 & R10 & R11 & KC) ])).
        (first [ pose proof ((t_found r1 ret Hret R1 R10 R11)) as dR_8; dex1 dR_8 as r2; dand3 dR_8 as RUN A10 K2 | pose proof ((t_found r1 ret Hret R1 R10 R11)) as dR_8; dand4 dR_8 as r2 RUN A10 K2 | destruct (t_found r1 ret Hret R1 R10 R11) as (r2 & RUN & A10 & K2) ]).
        exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x2abcc : word) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = at_ s j /\ getr r 11 = Z_to_bv 64 0
                         /\ getr r 12 = Z_to_bv 64 m /\ getr r 13 = Z_to_bv 64 Mc /\ getr r 14 = Z_to_bv 64 Hc
                         /\ getr r 15 = Z_to_bv 64 0 /\ getr r 16 = Z_to_bv 64 7 /\ keeps_cs regs r)).
      + stn_eexists. split.
        * renm. stepb_ft F_2ab9c D_2ab9c ltac:(cond).     (* [comment removed for export] *)
          mlbu F_2aba0 D_2aba0 j.                   (* [comment removed for export] *)
          renm. stepb_ft F_2aba4 D_2aba4 ltac:(condb).    (* [comment removed for export] *)
          renm. stepn F_2aba8 D_2aba8.                    (* [comment removed for export] *)
          renm. stepb_ft F_2abac D_2abac ltac:(cond).     (* [comment removed for export] *)
          renm. stepn F_2abb0 D_2abb0.                    (* [comment removed for export] *)
          ldc F_2abb4 D_2abb4 (Z_to_bv 64 Mc) RM.   (* [comment removed for export] *)
          renm. stepn F_2abb8 D_2abb8.                    (* [comment removed for export] *)
          ldc F_2abbc D_2abbc (Z_to_bv 64 Hc) RH.   (* [comment removed for export] *)
          renm. stepn F_2abc0 D_2abc0.                    (* [comment removed for export] *)
          renm. stepiv F_2abc4 D_2abc4 (Z_to_bv 64 0)
            ltac:(gres; rwH; apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
          vnorm.
          renm. stepn F_2abc8 D_2abc8.                    (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * post.
      + cbv beta. (intros r1; (first [ intro dR_21; dand9 dR_21 as R1 R10 R11 R12 R13 R14 R15 R16 KC | intros (R1 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & KC) ])).
        (first [ pose proof ((w_loop (Z.to_nat ((K - j) / 8)) r1 ret j m Hret R1 R10 R11 R12 R13 R14 R15 R16 Hj Hal
                    ltac:(clear -Hj; pose proof (Z.div_pos (K - j) 8); lia) Hm)) as dR_9; dex1 dR_9 as r2; dand3 dR_9 as RUN A10 K2 | pose proof ((w_loop (Z.to_nat ((K - j) / 8)) r1 ret j m Hret R1 R10 R11 R12 R13 R14 R15 R16 Hj Hal
                    ltac:(clear -Hj; pose proof (Z.div_pos (K - j) 8); lia) Hm)) as dR_9; dand4 dR_9 as r2 RUN A10 K2 | destruct (w_loop (Z.to_nat ((K - j) / 8)) r1 ret j m Hret R1 R10 R11 R12 R13 R14 R15 R16 Hj Hal
                    ltac:(clear -Hj; pose proof (Z.div_pos (K - j) 8); lia) Hm) as (r2 & RUN & A10 & K2) ]).
        exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac snez1 :=
    match goal with |- context [v_sltu ?a ?b] =>
      replace (v_sltu a b) with (Z_to_bv 64 1)
        by (symmetry; rwH; unfold v_sltu; rewrite c_ltu_ltb; try unfold v_addi; unorm;
            rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity) end.

  Lemma andi7_u : forall j, (0 <= bv_unsigned s + j < 2 ^ 64)%Z ->
    bv_unsigned (v_andi (at_ s j) 7) = ((bv_unsigned s + j) mod 8)%Z.
  Proof.
    intros j Hj. rewrite u_andi by lia. rewrite at_u by lia.
    change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity.
  Qed.

  Lemma h_loop : forall (i : nat) regs (ret : word) j m,
    ret_ok ret -> getr regs 1 = ret -> getr regs 10 = at_ s j -> getr regs 11 = Z_to_bv 64 0 ->
    getr regs 12 = Z_to_bv 64 m -> getr regs 15 = at_ s (j + 1) -> getr regs 16 = Z_to_bv 64 1 ->
    (0 <= j <= K)%Z -> (Z.of_nat i = 7 - (bv_unsigned s + j) mod 8)%Z -> (K - j + 8 <= m < 2 ^ 64)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x2ab74 : word) mem rom) (mkst regs' ret mem rom)
      /\ getr regs' 10 = at_ s K /\ keeps_cs regs regs'.
  Proof.
    pose proof KL as HKL. pose proof (u64_range s) as Hs.
    induction i as [|i IH]; intros regs ret j m Hret H1 H10 H11 H12 H15 H16 Hj Hi Hm.
    - (* [comment removed for export] *)
      destruct (Z.eq_dec j K) as [HjK|HjK].
      + eapply (runs_trans RSEGS _ (fun r => mkst r (0x2abf8 : word) mem rom)
                 (fun r => getr r 1 = ret /\ getr r 10 = at_ s K /\ getr r 11 = Z_to_bv 64 0 /\ keeps_cs regs r)).
        * stn_eexists. split.
          -- mlbu F_2ab74 D_2ab74 j.                (* [comment removed for export] *)
             renm. stepn F_2ab78 D_2ab78.                 (* [comment removed for export] *)
             renm. stepb_tk F_2ab7c D_2ab7c ltac:(condb). (* [comment removed for export] *)
             stn_done. apply mst_refl.
          -- post.
        * cbv beta. (intros r1; (first [ intro dR_22; dand4 dR_22 as R1 R10 R11 KC | intros (R1 & R10 & R11 & KC) ])).
          (first [ pose proof ((t_found r1 ret Hret R1 R10 R11)) as dR_10; dex1 dR_10 as r2; dand3 dR_10 as RUN A10 K2 | pose proof ((t_found r1 ret Hret R1 R10 R11)) as dR_10; dand4 dR_10 as r2 RUN A10 K2 | destruct (t_found r1 ret Hret R1 R10 R11) as (r2 & RUN & A10 & K2) ]).
          exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
      + eapply (runs_trans RSEGS _ (fun r => mkst r (0x2ab9c : word) mem rom)
                 (fun r => getr r 1 = ret /\ getr r 10 = at_ s (j + 1) /\ getr r 11 = Z_to_bv 64 0
                           /\ getr r 12 = Z_to_bv 64 (m - 1) /\ getr r 14 = Z_to_bv 64 1 /\ keeps_cs regs r)).
        * stn_eexists. split.
          -- mlbu F_2ab74 D_2ab74 j.                (* [comment removed for export] *)
             renm. stepn F_2ab78 D_2ab78.                 (* [comment removed for export] *)
             renm. stepb_ft F_2ab7c D_2ab7c ltac:(condb). (* [comment removed for export] *)
             renm. stepn F_2ab80 D_2ab80.                 (* [comment removed for export] *)
             renm. stepn F_2ab84 D_2ab84.                 (* [comment removed for export] *)
             renm. stepn F_2ab88 D_2ab88.                 (* [comment removed for export] *)
             renm. stepn F_2ab8c D_2ab8c. snez1.          (* [comment removed for export] *)
             renm. stepb_tk F_2ab90 D_2ab90
               ltac:(rwH; unfold c_eq, bv_eqb; rewrite andi7_u by lia; unorm; apply Z.eqb_eq;
                     rewrite Z.add_assoc, <- Zplus_mod_idemp_l;
                     replace ((bv_unsigned s + j) mod 8)%Z with 7%Z by lia; reflexivity).  (* [comment removed for export] *)
             stn_done. apply mst_refl.
          -- post.
        * cbv beta. (intros r1; (first [ intro dR_23; dand6 dR_23 as R1 R10 R11 R12 R14 KC | intros (R1 & R10 & R11 & R12 & R14 & KC) ])).
          (first [ pose proof ((a_entry r1 ret (j + 1)%Z (m - 1)%Z Hret R1 R10 R11 R12 R14 ltac:(lia)
                      ltac:(rewrite Z.add_assoc, <- Zplus_mod_idemp_l;
                            replace ((bv_unsigned s + j) mod 8)%Z with 7%Z by lia; reflexivity)
                      ltac:(lia))) as dR_11; dex1 dR_11 as r2; dand3 dR_11 as RUN A10 K2 | pose proof ((a_entry r1 ret (j + 1)%Z (m - 1)%Z Hret R1 R10 R11 R12 R14 ltac:(lia)
                      ltac:(rewrite Z.add_assoc, <- Zplus_mod_idemp_l;
                            replace ((bv_unsigned s + j) mod 8)%Z with 7%Z by lia; reflexivity)
                      ltac:(lia))) as dR_11; dand4 dR_11 as r2 RUN A10 K2 | destruct (a_entry r1 ret (j + 1)%Z (m - 1)%Z Hret R1 R10 R11 R12 R14 ltac:(lia)
                      ltac:(rewrite Z.add_assoc, <- Zplus_mod_idemp_l;
                            replace ((bv_unsigned s + j) mod 8)%Z with 7%Z by lia; reflexivity)
                      ltac:(lia)) as (r2 & RUN & A10 & K2) ]).
          exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
    - (* [comment removed for export] *)
      destruct (Z.eq_dec j K) as [HjK|HjK].
      + eapply (runs_trans RSEGS _ (fun r => mkst r (0x2abf8 : word) mem rom)
                 (fun r => getr r 1 = ret /\ getr r 10 = at_ s K /\ getr r 11 = Z_to_bv 64 0 /\ keeps_cs regs r)).
        * stn_eexists. split.
          -- mlbu F_2ab74 D_2ab74 j.
             renm. stepn F_2ab78 D_2ab78.
             renm. stepb_tk F_2ab7c D_2ab7c ltac:(condb).
             stn_done. apply mst_refl.
          -- post.
        * cbv beta. (intros r1; (first [ intro dR_24; dand4 dR_24 as R1 R10 R11 KC | intros (R1 & R10 & R11 & KC) ])).
          (first [ pose proof ((t_found r1 ret Hret R1 R10 R11)) as dR_12; dex1 dR_12 as r2; dand3 dR_12 as RUN A10 K2 | pose proof ((t_found r1 ret Hret R1 R10 R11)) as dR_12; dand4 dR_12 as r2 RUN A10 K2 | destruct (t_found r1 ret Hret R1 R10 R11) as (r2 & RUN & A10 & K2) ]).
          exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
      + pose proof (Z.mod_pos_bound (bv_unsigned s + j + 1) 8 ltac:(lia)) as HM1.
        assert (HM : ((bv_unsigned s + j + 1) mod 8 = (bv_unsigned s + j) mod 8 + 1)%Z).
        { clear -Hi Hs Hj. stn_open. rewrite <- (Zplus_mod_idemp_l (bv_unsigned s + j)).
          pose proof (Z.mod_pos_bound (bv_unsigned s + j) 8 ltac:(lia)). apply Z.mod_small. lia. }
        eapply (runs_trans RSEGS _ (fun r => mkst r (0x2ab74 : word) mem rom)
                 (fun r => getr r 1 = ret /\ getr r 10 = at_ s (j + 1) /\ getr r 11 = Z_to_bv 64 0
                           /\ getr r 12 = Z_to_bv 64 (m - 1) /\ getr r 15 = at_ s (j + 1 + 1)
                           /\ getr r 16 = Z_to_bv 64 1 /\ keeps_cs regs r)).
        * stn_eexists. split.
          -- mlbu F_2ab74 D_2ab74 j.                (* [comment removed for export] *)
             renm. stepn F_2ab78 D_2ab78.                 (* [comment removed for export] *)
             renm. stepb_ft F_2ab7c D_2ab7c ltac:(condb). (* [comment removed for export] *)
             renm. stepn F_2ab80 D_2ab80.                 (* [comment removed for export] *)
             renm. stepn F_2ab84 D_2ab84.                 (* [comment removed for export] *)
             renm. stepn F_2ab88 D_2ab88.                 (* [comment removed for export] *)
             renm. stepn F_2ab8c D_2ab8c. snez1.          (* [comment removed for export] *)
             renm. stepb_ft F_2ab90 D_2ab90
               ltac:(rwH; unfold c_eq, bv_eqb; rewrite andi7_u by lia; unorm; apply Z.eqb_neq;
                     rewrite Z.add_assoc; lia).     (* [comment removed for export] *)
             renm. stepn F_2ab94 D_2ab94.                 (* [comment removed for export] *)
             renm. stepb_tk F_2ab98 D_2ab98 ltac:(cond).  (* [comment removed for export] *)
             stn_done. apply mst_refl.
          -- post.
        * cbv beta. (intros r1; (first [ intro dR_25; dand7 dR_25 as R1 R10 R11 R12 R15 R16 KC | intros (R1 & R10 & R11 & R12 & R15 & R16 & KC) ])).
          (first [ pose proof ((IH r1 ret (j + 1)%Z (m - 1)%Z Hret R1 R10 R11 R12 R15 R16 ltac:(lia)
                      ltac:(rewrite Z.add_assoc; lia) ltac:(lia))) as dR_13; dex1 dR_13 as r2; dand3 dR_13 as RUN A10 K2 | pose proof ((IH r1 ret (j + 1)%Z (m - 1)%Z Hret R1 R10 R11 R12 R15 R16 ltac:(lia)
                      ltac:(rewrite Z.add_assoc; lia) ltac:(lia))) as dR_13; dand4 dR_13 as r2 RUN A10 K2 | destruct (IH r1 ret (j + 1)%Z (m - 1)%Z Hret R1 R10 R11 R12 R15 R16 ltac:(lia)
                      ltac:(rewrite Z.add_assoc; lia) ltac:(lia)) as (r2 & RUN & A10 & K2) ]).
          exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma memchr0_run : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = s -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps RSEGS (mkst regs (0x2ab58 : word) mem rom) (mkst regs' ret mem rom)
      /\ getr regs' 10 = at_ s K /\ keeps_cs regs regs'.
  Proof.
    intros regs ret Hret H1 H10 H11 H12.
    pose proof KL as HKL. pose proof (u64_range s) as Hs. rewrite <- (at_0 s) in H10.
    pose proof (Z.mod_pos_bound (bv_unsigned s) 8 ltac:(lia)) as HM.
    destruct (Z.eq_dec (bv_unsigned s mod 8) 0) as [Hal|Hal].
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x2ab9c : word) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = at_ s 0 /\ getr r 11 = Z_to_bv 64 0
                         /\ getr r 12 = Z_to_bv 64 n /\ getr r 14 = Z_to_bv 64 1 /\ keeps_cs regs r)).
      + stn_eexists. split.
        * renm. stepn F_2ab58 D_2ab58. rwH. vals_lit.     (* [comment removed for export] *)
          renm. stepn F_2ab5c D_2ab5c.                    (* [comment removed for export] *)
          renm. stepn F_2ab60 D_2ab60. snez1.             (* [comment removed for export] *)
          renm. stepb_tk F_2ab64 D_2ab64
            ltac:(rwH; unfold c_eq, bv_eqb; rewrite andi7_u by lia; unorm; apply Z.eqb_eq;
                  rewrite Z.add_0_r; exact Hal).    (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * post.
      + cbv beta. (intros r1; (first [ intro dR_26; dand6 dR_26 as R1 R10 R11 R12 R14 KC | intros (R1 & R10 & R11 & R12 & R14 & KC) ])).
        (first [ pose proof ((a_entry r1 ret 0 n Hret R1 R10 R11 R12 R14 ltac:(lia) ltac:(rewrite Z.add_0_r; exact Hal) ltac:(lia))) as dR_14; dex1 dR_14 as r2; dand3 dR_14 as RUN A10 K2 | pose proof ((a_entry r1 ret 0 n Hret R1 R10 R11 R12 R14 ltac:(lia) ltac:(rewrite Z.add_0_r; exact Hal) ltac:(lia))) as dR_14; dand4 dR_14 as r2 RUN A10 K2 | destruct (a_entry r1 ret 0 n Hret R1 R10 R11 R12 R14 ltac:(lia) ltac:(rewrite Z.add_0_r; exact Hal) ltac:(lia))
          as (r2 & RUN & A10 & K2) ]).
        exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x2ab74 : word) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = at_ s 0 /\ getr r 11 = Z_to_bv 64 0
                         /\ getr r 12 = Z_to_bv 64 n /\ getr r 15 = at_ s (0 + 1) /\ getr r 16 = Z_to_bv 64 1
                         /\ keeps_cs regs r)).
      + stn_eexists. split.
        * renm. stepn F_2ab58 D_2ab58. rwH. vals_lit.     (* [comment removed for export] *)
          renm. stepn F_2ab5c D_2ab5c.                    (* [comment removed for export] *)
          renm. stepn F_2ab60 D_2ab60. snez1.             (* [comment removed for export] *)
          renm. stepb_ft F_2ab64 D_2ab64
            ltac:(rwH; unfold c_eq, bv_eqb; rewrite andi7_u by lia; unorm; apply Z.eqb_neq;
                  rewrite Z.add_0_r; exact Hal).    (* [comment removed for export] *)
          renm. stepb_ft F_2ab68 D_2ab68 ltac:(cond).     (* [comment removed for export] *)
          renm. stepn F_2ab6c D_2ab6c.                    (* [comment removed for export] *)
          renm. stepn F_2ab70 D_2ab70.                    (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * post.
      + cbv beta. (intros r1; (first [ intro dR_27; dand7 dR_27 as R1 R10 R11 R12 R15 R16 KC | intros (R1 & R10 & R11 & R12 & R15 & R16 & KC) ])).
        (first [ pose proof ((h_loop (Z.to_nat (7 - bv_unsigned s mod 8)) r1 ret 0 n Hret R1 R10 R11 R12 R15 R16
                    ltac:(lia) ltac:(rewrite Z.add_0_r; lia) ltac:(lia))) as dR_15; dex1 dR_15 as r2; dand3 dR_15 as RUN A10 K2 | pose proof ((h_loop (Z.to_nat (7 - bv_unsigned s mod 8)) r1 ret 0 n Hret R1 R10 R11 R12 R15 R16
                    ltac:(lia) ltac:(rewrite Z.add_0_r; lia) ltac:(lia))) as dR_15; dand4 dR_15 as r2 RUN A10 K2 | destruct (h_loop (Z.to_nat (7 - bv_unsigned s mod 8)) r1 ret 0 n Hret R1 R10 R11 R12 R15 R16
                    ltac:(lia) ltac:(rewrite Z.add_0_r; lia) ltac:(lia)) as (r2 & RUN & A10 & K2) ]).
        exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
  Qed.

End MCHR.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem ref_memchr0 : forall mem (s : word) buf K n rom regs (ret : word),
  mchrH mem s buf K n ->
  ret_ok ret -> getr regs 1 = ret ->
  getr regs 10 = s -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 n ->
  exists regs',
    msteps RSEGS (mkst regs (0x2ab58 : word) mem rom) (mkst regs' ret mem rom)
    /\ keeps_cs regs regs'
    /\ getr regs' 10 = Z_to_bv 64 (bv_unsigned s + K).
Proof.
  intros mem s buf K n rom regs ret HOK Hret H1 H10 H11 H12.
  (first [ pose proof ((memchr0_run mem s buf K n rom HOK regs ret Hret H1 H10 H11 H12)) as dR_16; dex1 dR_16 as r; dand3 dR_16 as RUN A10 KC | pose proof ((memchr0_run mem s buf K n rom HOK regs ret Hret H1 H10 H11 H12)) as dR_16; dand4 dR_16 as r RUN A10 KC | destruct (memchr0_run mem s buf K n rom HOK regs ret Hret H1 H10 H11 H12) as (r & RUN & A10 & KC) ]).
  exists r. split; [exact RUN | split; [exact KC | exact A10]].
Qed.
