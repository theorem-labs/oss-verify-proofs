(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare Frame RefMemcpyLib FuzzMem
  U6MemcpyBase U6Memcpy U6AdlerBase U6AdlerIface U6Adler.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.cks Require Import CkTables CkModel CkMathAdler.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel MemFill.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface ZChecksum ZChkAdl AdlerModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import CalleeKits6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Import Segs6u Callee6u DeflBlkApi6u Defl6uApi.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


Theorem memcpy_run6u_ok : memcpy_run6u.
Proof.
  unfold memcpy_run6u. intros mem regs dst src n bs ra Hrd Hd0 Hd1 Hs0 Hs1 Hdisj Hmap Hret H1 H10 H11 H12.
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
  destruct (ref_memcpy mem (zw dst) (zw src) (Z.of_nat n) bs s6u_rom HOK regs ra Hret H1 H10 H11 H12) as (regs' & Hms & Hk).
  exists regs'. split; [|split].
  - replace (zw A6U_MEMCPY) with (0x2a824%bv : word) by (apply bv_eq; reflexivity). exact Hms.
  - rewrite <- (getr_nz regs' 10 eq_refl), <- H10. apply Hk. cbn. tauto.
  - apply (frame_of_keeps callee_kept memcpy_clob regs regs' Hk). vm_compute. reflexivity.
Qed.


Definition ROM6u : (word -> option byte) -> Prop := U6AdlerBase.img_ok.

Lemma rom_local6u_ok : rom_local6u ROM6u.
Proof.
  intros m m' Hm Hag i Hi. unfold ROM6u, img_ok, RO_LO, RO_HI, IMG6U_LO, IMG6U_HI in *.
  rewrite Hag; [apply Hm; exact Hi|]. change (Z_to_bv 64 i) with (zw i). rewrite u_zw_small by lia. lia.
Qed.



Theorem adler32_run6u_ok : adler32_run6u ROM6u.
Proof.
  unfold adler32_run6u.
  intros mem regs adler P d usp ra Hrd Ha Hcan HP HPl Hl32 Husp1 Husp2 Hmap Hbelow HROM Hret H1 H2 H10 H11 H12.
  unfold ADLER_FR6U in *.
  rewrite <- (getr_nz regs 1 eq_refl) in H1. rewrite <- (getr_nz regs 2 eq_refl) in H2.
  rewrite <- (getr_nz regs 10 eq_refl) in H10. rewrite <- (getr_nz regs 11 eq_refl) in H11.
  rewrite <- (getr_nz regs 12 eq_refl) in H12.
  set (len := Z.of_nat (length d)) in *.
  assert (Hrd1 : forall i, 0 <= i < len -> exists b : byte, rdn USEGS mem (Z_to_bv 64 (P + i)) 1 = Some [b]).
  { intros i Hi. exists (nth (Z.to_nat i) d (Z_to_bv 8 0)).
    replace (Z_to_bv 64 (P + i)) with (zw P + nat_to_word (Z.to_nat i))%bv
      by (rewrite <- zw_add_nat, Z2Nat.id by lia; reflexivity).
    apply (rdn_nth _ mem (length d)); [exact Hrd | lia]. }
  destruct (rdn_bytes_at USEGS mem (length d) P ltac:(lia) ltac:(lia) Hrd1) as (bs' & Hbs' & Hmap').
  unfold zw, s6u_segs in Hrd. rewrite Hrd in Hbs'. injection Hbs' as <-.
  destruct (u6_adler32 regs mem s6u_rom ra usp adler P len len H1 Hret H2 H10 H11 H12
              ltac:(lia) ltac:(apply Z.mod_small; lia) Ha HP ltac:(lia) ltac:(lia)
              ltac:(apply symex_store_ok; [lia | lia | lia | intros x Hx; apply Hmap; lia])
              Hbelow HROM Hrd1)
    as (r & m' & Hms & Hv & Hk & Hfm).
  exists r, m'. split; [|split; [|split; [|split; [|split]]]].
  - replace (zw A6U_ADLER32) with (0x1af3c%bv : word) by (apply bv_eq; reflexivity). exact Hms.
  - rewrite <- (getr_nz r 10 eq_refl), Hv. subst len. rewrite Nat2Z.id, <- Hmap'.
    change (map (fun b : byte => bv_unsigned b) d) with (bZ d).
    rewrite (adler_models_agree adler P d) by first [assumption | lia]. reflexivity.
  - rewrite <- (getr_nz r 2 eq_refl), <- H2. apply Hk. cbn. tauto.
  - apply (frame_of_keeps callee_saved c_clob regs r Hk). vm_compute. reflexivity.
  - intros x Hx. apply (proj1 Hfm). cbn [outside]. split; [|exact I].
    unfold in_rng. change (Z_to_bv 64 (usp - 128)) with (zw (usp - 128)). rewrite u_zw_small by lia. cbn in Hx. lia.
  - exact (proj2 Hfm).
Qed.

Theorem adler32_null_run6u_ok : adler32_null_run6u.
Proof.
  unfold adler32_null_run6u.
  intros mem regs usp ra Husp1 Husp2 Hmap Hret H1 H2 H11 H12.
  unfold ADLER_FR6U in *.
  rewrite <- (getr_nz regs 1 eq_refl) in H1. rewrite <- (getr_nz regs 2 eq_refl) in H2.
  rewrite <- (getr_nz regs 11 eq_refl) in H11. rewrite <- (getr_nz regs 12 eq_refl) in H12.
  destruct (u6_adler32_null regs mem s6u_rom ra usp H1 Hret H2 H11 H12 ltac:(lia)
              ltac:(apply symex_store_ok; [lia | lia | lia | intros x Hx; apply Hmap; lia]))
    as (r & m' & Hms & Hv & Hk & Hfm).
  exists r, m'. split; [|split; [|split; [|split; [|split]]]].
  - replace (zw A6U_ADLER32) with (0x1af3c%bv : word) by (apply bv_eq; reflexivity). exact Hms.
  - rewrite <- (getr_nz r 10 eq_refl), Hv. reflexivity.
  - rewrite <- (getr_nz r 2 eq_refl), <- H2. apply Hk. cbn. tauto.
  - apply (frame_of_keeps callee_saved c_clob regs r Hk). vm_compute. reflexivity.
  - intros x Hx. apply (proj1 Hfm). cbn [outside]. split; [|exact I].
    unfold in_rng. change (Z_to_bv 64 (usp - 128)) with (zw (usp - 128)). rewrite u_zw_small by lia. cbn in Hx. lia.
  - exact (proj2 Hfm).
Qed.
End FXG.
