(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare Frame RefMemcpyLib FuzzMem
  S6MemcpyBase S6Memcpy S6AdlerBase S6AdlerIface S6Adler.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.cks Require Import CkTables CkModel CkMathAdler.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel MemFill.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface ZChecksum ZChkAdl AdlerModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Segs6 Callee6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


Definition all_regs : list reg :=
  [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

Lemma reg_enum_nat : forall k : nat, (k < 32)%nat -> In (Z_to_bv 5 (Z.of_nat k)) all_regs.
Proof.
  intros k Hk. unfold all_regs.
  do 32 (destruct k as [|k];
    [ cbn [In]; repeat first [ left; apply bv_eq; vm_compute; reflexivity | right ] | ]).
  lia.
Qed.

Lemma reg_enum : forall r : reg, In r all_regs.
Proof.
  intros r. rewrite <- (Z_to_bv_bv_unsigned 5 r).
  pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
  rewrite <- (Z2Nat.id (bv_unsigned r)) by lia. apply reg_enum_nat. lia.
Qed.

Lemma reg_in_true_In : forall (r : reg) l, reg_in r l = true -> In r l.
Proof.
  intros r l. induction l as [|x l IH]; cbn; [discriminate|].
  intros H. apply Bool.orb_true_iff in H. destruct H as [H|H].
  - left. symmetry. apply bv_eq. unfold bv_eqb in H. apply Z.eqb_eq in H. exact H.
  - right. exact (IH H).
Qed.

Lemma frame_of_keeps : forall (kept clob : list reg) (regs regs' : bvmap 5 word),
  (forall r : reg, In r kept -> getr regs' r = getr regs r) ->
  forallb (fun r : reg => reg_in r clob || bv_eqb r 0%bv || reg_in r kept) all_regs = true ->
  forall r : reg, reg_in r clob = false -> getr regs' r = getr regs r.
Proof.
  intros kept clob regs regs' Hk Hall r Hr.
  pose proof (proj1 (forallb_forall _ _) Hall r (reg_enum r)) as H. cbn beta in H.
  rewrite Hr in H. cbn [orb] in H.
  destruct (bv_eqb r 0%bv) eqn:E0.
  - unfold getr. rewrite E0. reflexivity.
  - cbn [orb] in H. apply Hk. apply reg_in_true_In. exact H.
Qed.

Lemma getr_nz : forall (regs : bvmap 5 word) (r : reg), bv_eqb r 0%bv = false -> getr regs r = reg_get regs r.
Proof. intros regs r H. unfold getr. rewrite H. reflexivity. Qed.


Theorem memcpy_run6_ok : memcpy_run6.
Proof.
  unfold memcpy_run6. intros mem regs dst src n bs ra Hrd Hd0 Hd1 Hs0 Hs1 Hdisj Hmap Hret H1 H10 H11 H12.
  pose proof (rdn_length _ _ _ _ _ Hrd) as Hlen.
  assert (HOK : mcH mem (zw dst) (zw src) (Z.of_nat n) bs).
  { constructor.
    - lia.
    - rewrite Hlen, Nat2Z.id. reflexivity.
    - rewrite Hlen. exact Hrd.
    - rewrite Hlen. destruct n as [|n']; [reflexivity|].
      apply symex_store_ok; [lia | lia | lia |]. intros x Hx. apply Hmap. lia.
    - rewrite !u_zw_small by lia. lia.
    - rewrite u_zw_small by lia. lia.
    - rewrite u_zw_small by lia. lia. }
  rewrite <- (getr_nz regs 1 eq_refl) in H1. rewrite <- (getr_nz regs 10 eq_refl) in H10.
  rewrite <- (getr_nz regs 11 eq_refl) in H11. rewrite <- (getr_nz regs 12 eq_refl) in H12.
  destruct (ref_memcpy mem (zw dst) (zw src) (Z.of_nat n) bs s6_rom HOK regs ra Hret H1 H10 H11 H12) as (regs' & Hms & Hk).
  exists regs'. split; [|split].
  - replace (zw A6_MEMCPY) with (0x27800%bv : word) by (apply bv_eq; reflexivity). exact Hms.
  - rewrite <- (getr_nz regs' 10 eq_refl), <- H10. apply Hk. cbn. tauto.
  - apply (frame_of_keeps callee_kept memcpy_clob regs regs' Hk). vm_compute. reflexivity.
Qed.


Definition ROM6 : (word -> option byte) -> Prop := S6AdlerBase.img_ok.

Lemma rom_local6_ok : rom_local6 ROM6.
Proof.
  intros m m' Hm Hag i Hi. unfold ROM6, img_ok, RO_LO, RO_HI, IMG6_LO, IMG6_HI in *.
  rewrite Hag; [apply Hm; exact Hi|]. change (Z_to_bv 64 i) with (zw i). rewrite u_zw_small by lia. lia.
Qed.



Lemma adl_sums : forall bs a b, adl bs a b = adler_sums (a, b) bs.
Proof.
  induction bs as [|x bs IH]; intros a b; [reflexivity|].
  cbn [adl]. rewrite adler_sums_cons. unfold adler_stepm. cbn [fst snd]. apply IH.
Qed.

Lemma lo16_agree : forall a, CkModel.lo16 a = AdlerModel.lo16 a.
Proof. intros a. rewrite CkMathAdler.lo16_mod. reflexivity. Qed.

Lemma hi16_agree : forall a, 0 <= a -> CkModel.hi16 a = AdlerModel.hi16 a.
Proof. intros a Ha. rewrite CkMathAdler.hi16_div_mod. unfold AdlerModel.hi16. symmetry. apply mod32_div16. exact Ha. Qed.

Lemma adler_models_agree : forall adler P d,
  adler_canon adler -> P <> 0 ->
  adler32_z_model adler (bZ d) = adler32_z_spec adler P d.
Proof.
  intros adler P d Hcan HP.
  pose proof Hcan as (Ha & Hl & Hh).
  assert (Hok : adler_ok adler).
  { unfold adler_ok. rewrite lo16_agree, hi16_agree by lia. unfold BASE. unfold ABASE in Hl, Hh. lia. }
  rewrite (adler32_z_model_spec adler (bZ d) Hok (bZ_range d)).
  rewrite (adler32_z_spec_canon adler P d Hcan HP).
  unfold adler_spec, adler32_model.
  assert (E1 : Z.land adler 65535 mod ABASE = CkModel.lo16 adler).
  { unfold CkModel.lo16. apply Z.mod_small. pose proof (lo16_agree adler) as EE. unfold CkModel.lo16 in EE. rewrite EE.
    split; [apply (proj1 (AdlerModel.lo16_range adler)) | exact Hl]. }
  assert (E2 : Z.land (Z.shiftr adler 16) 65535 mod ABASE = CkModel.hi16 adler).
  { unfold CkModel.hi16. apply Z.mod_small. pose proof (hi16_agree adler ltac:(lia)) as EE. unfold CkModel.hi16 in EE. rewrite EE.
    split; [apply (proj1 (AdlerModel.hi16_range adler)) | exact Hh]. }
  rewrite E1, E2, adl_sums.
  pose proof (adler_sums_range (bZ d) (CkModel.lo16 adler) (CkModel.hi16 adler)
                ltac:(destruct Hok as (_ & A & _); pose proof (CkMathAdler.lo16_range adler); lia)
                ltac:(destruct Hok as (_ & _ & A); pose proof (CkMathAdler.hi16_range adler); lia)) as Hr.
  destruct (adler_sums (CkModel.lo16 adler, CkModel.hi16 adler) (bZ d)) as [a b]. cbn [fst snd] in *.
  unfold adler_comb. rewrite Z.lor_comm. apply combine_lor; unfold BASE in Hr; lia.
Qed.


Theorem adler32_run6_ok : adler32_run6 ROM6.
Proof.
  unfold adler32_run6.
  intros mem regs adler P d usp ra Hrd Ha Hcan HP HPl Hl32 Husp1 Husp2 Hmap Hbelow HROM Hret H1 H2 H10 H11 H12.
  unfold ADLER_FR6 in *.
  rewrite <- (getr_nz regs 1 eq_refl) in H1. rewrite <- (getr_nz regs 2 eq_refl) in H2.
  rewrite <- (getr_nz regs 10 eq_refl) in H10. rewrite <- (getr_nz regs 11 eq_refl) in H11.
  rewrite <- (getr_nz regs 12 eq_refl) in H12.
  set (len := Z.of_nat (length d)) in *.
  assert (Hrd1 : forall i, 0 <= i < len -> exists b : byte, rdn RSEGS mem (Z_to_bv 64 (P + i)) 1 = Some [b]).
  { intros i Hi. exists (nth (Z.to_nat i) d (Z_to_bv 8 0)).
    replace (Z_to_bv 64 (P + i)) with (zw P + nat_to_word (Z.to_nat i))%bv
      by (rewrite <- zw_add_nat, Z2Nat.id by lia; reflexivity).
    apply (rdn_nth _ mem (length d)); [exact Hrd | lia]. }
  destruct (rdn_bytes_at RSEGS mem (length d) P ltac:(lia) ltac:(lia) Hrd1) as (bs' & Hbs' & Hmap').
  unfold zw, s6_segs in Hrd. rewrite Hrd in Hbs'. injection Hbs' as <-.
  destruct (s6_adler32 regs mem s6_rom ra usp adler P len len H1 Hret H2 H10 H11 H12
              ltac:(lia) ltac:(apply Z.mod_small; lia) Ha HP ltac:(lia) ltac:(lia)
              ltac:(apply symex_store_ok; [lia | lia | lia | intros x Hx; apply Hmap; lia])
              Hbelow HROM Hrd1)
    as (r & m' & Hms & Hv & Hk & Hfm).
  exists r, m'. split; [|split; [|split; [|split; [|split]]]].
  - replace (zw A6_ADLER32) with (0x1a3d4%bv : word) by (apply bv_eq; reflexivity). exact Hms.
  - rewrite <- (getr_nz r 10 eq_refl), Hv. subst len. rewrite Nat2Z.id, <- Hmap'.
    change (map (fun b : byte => bv_unsigned b) d) with (bZ d).
    rewrite (adler_models_agree adler P d) by first [assumption | lia]. reflexivity.
  - rewrite <- (getr_nz r 2 eq_refl), <- H2. apply Hk. cbn. tauto.
  - apply (frame_of_keeps callee_saved c_clob regs r Hk). vm_compute. reflexivity.
  - intros x Hx. apply (proj1 Hfm). cbn [outside]. split; [|exact I].
    unfold in_rng. change (Z_to_bv 64 (usp - 32)) with (zw (usp - 32)). rewrite u_zw_small by lia. cbn in Hx. lia.
  - exact (proj2 Hfm).
Qed.
End FXG.
