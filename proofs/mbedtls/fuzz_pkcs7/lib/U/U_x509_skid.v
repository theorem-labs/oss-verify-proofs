(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux X509Aux AStep CellsX Cells Mem.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import CrtExtStmts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_asn1_get_tag.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_Sums1.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P01d5359787447a67 2 24 1 1 8 3 1 1 38 1 39 1 5 0 2 27 2 37 2 40 2 41 16 1 1 8 3 2 1 37 1 40 1 4 0 2 38 2 39 2 41 16P022a5459e538f7bb 2 24 1 1 8 3 1 1 38 1 39 1 5 0 2 27 2 37 2 40 2 41 16 1 1 8 3 2 1 37 1 40 1 4 0 2 38 2 39 2 41 16P02d5bc7126353406 0 4 0 1 23 1 33 1 34 1P02d83275fa858fcb 2 25 1 1 8 3 1 1 38 1 39 1 5 0 2 27 2 37 2 40 2 41 16 1 1 8 3 2 1 37 1 40 1 4 0 2 38 2 39 2 41 16P034efd15e9522836 0 5 1 1 2 1 18 1 28 1 29 1P03725e97a8baf60d 2 16 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P05e319ae30c8e403 2 14 0 5 0 1 3 1 19 1 29 1 30 1 0 4 0 1 2 1 29 1 30 1P06f847cc0ac038b7 0 2 0 1 1 1P0a88d06d4f58ee60 2 24 1 1 8 3 1 1 38 1 39 1 5 0 2 27 2 37 2 40 2 41 16 1 1 8 3 2 1 37 1 40 1 4 0 2 38 2 39 2 41 16P0bdb764f145d01b8 2 16 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P0cf7e184ec48e56a 1 1 8 3 1 1 28 1 31 1 4 2 2 29 2 30 2 32 16P0f4503a2493cef8b 2 15 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P1027646196cfcf6f 2 24 1 1 8 3 1 1 38 1 39 1 5 0 2 27 2 37 2 40 2 41 16 1 1 8 3 2 1 37 1 40 1 4 0 2 38 2 39 2 41 16P103639d34f534372 0 2 0 1 17 1P10fda9b9a0c811a9 0 2 0 1 20 1P12a2b0a8f7e69646 0 2 0 1 23 1P12cb087073bd27cc 0 2 0 1 6 1P149a19109385a93f 0 4 0 1 23 1 33 1 34 1P15080305d6caf302 0 2 0 1 7 1P16f9e9adeb25fdb4 1 1 16 4 14 1 15 1 16 1 27 1 3 0 1 26 1 28 16P1af8fe9d8e1b825e 2 15 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P1beeb2d832d972f5 2 24 1 1 8 3 1 1 38 1 39 1 5 0 2 27 2 37 2 40 2 41 16 1 1 8 3 2 1 37 1 40 1 4 0 2 38 2 39 2 41 16P1da3b9d1b01dbd16 2 24 1 1 8 3 1 1 38 1 39 1 5 0 2 27 2 37 2 40 2 41 16 1 1 8 3 2 1 37 1 40 1 4 0 2 38 2 39 2 41 16P1dfbdeab9ab6b82f 2 14 0 5 0 1 3 1 19 1 29 1 30 1 0 4 0 1 2 1 29 1 30 1P200a7cc4ec21d8fe 1 1 8 3 1 1 29 1 30 1 5 2 2 18 2 28 2 31 2 32 16P20813d7922e28bfd 2 15 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P20e887304e49d083 0 4 0 1 25 1 35 1 36 1P2238ba8fee7d0732 2 14 0 5 0 1 3 1 19 1 29 1 30 1 0 4 0 1 2 1 29 1 30 1P24c5ef29dccbb7b5 2 15 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P257da89e01df2bcf 0 4 0 1 2 1 28 1 29 1P258afa72675341e0 0 2 0 1 5 1P25ae6a4308e36f0c 0 4 0 1 25 1 35 1 36 1P25b71546e130fb71 2 16 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P26e84279e74dd068 0 2 0 1 5 1P29be43591d60b6d1 2 25 1 1 8 3 1 1 38 1 39 1 5 0 2 27 2 37 2 40 2 41 16 1 1 8 3 2 1 37 1 40 1 4 0 2 38 2 39 2 41 16P2c846de83be2e29b 2 14 0 5 0 1 3 1 19 1 29 1 30 1 0 4 0 1 2 1 29 1 30 1P2d2d645765c610d3 0 4 0 1 2 1 30 1 31 1P2d54e8d56a81457b 2 16 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P2da94cee562761cd 2 16 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P318dec03651e112b 0 2 0 1 22 1P32102dee5f5da53d 2 14 0 5 0 1 3 1 19 1 29 1 30 1 0 4 0 1 2 1 29 1 30 1P3231a7e349450655 0 2 0 1 5 1P324fe17f3189b6fb 2 16 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P32cd422268dc2656 0 4 0 1 3 1 29 1 30 1P32ee785c549a994c 0 2 0 1 1 1P34e27c5361d8cf69 1 1 8 3 1 1 28 1 31 1 4 2 2 29 2 30 2 32 16P35507806eb8a1611 1 1 8 3 0 1 28 1 31 1 4 2 2 29 2 30 2 32 16P35b01f4ebfcc54e7 2 14 0 5 0 1 3 1 19 1 29 1 30 1 0 4 0 1 2 1 29 1 30 1P36e2b3bf11e686f2 1 1 8 3 1 1 29 1 30 1 4 2 2 28 2 31 2 32 16P37525919bb51a1de 2 15 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P390bacefae3e1d14 0 2 0 1 21 1P39bb7674ac22fbff 1 1 8 2 19 1 27 1 3 0 1 26 1 28 8P39cb1e8ada1d55a8 2 15 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P39f4e421386efb8f 0 1 1 1P3c6df7d7f4e5753c 1 1 8 3 0 1 29 1 30 1 5 2 2 18 2 28 2 31 2 32 16P3d0296d0b13f58e5 1 1 8 3 0 1 29 1 30 1 5 2 2 18 2 28 2 31 2 32 16P3dd3013a11f833b2 0 5 1 1 3 1 19 1 29 1 30 1N0026f8fea105e45dN00e1a0a805186181N0154abda6d92b217N030b5f61310d9a4aN03e56c3993b51f81N041030b493735b2aN04f05131fae3a72fN05cb897b1b662e95N067fc0bf5dc32d6cN06ea5530ef5de6a4N07239f0d8a0f5604N07783ab8ab147c2eN089724dd80e2ae5eN0c597f784e0fb4bfN0df2f0c95a00131eN0df4efa73ed0d5dfN0e4d6efc8b64ac42N0f3263777cce2b08N1134640cf7c2af58N11d6cbe881a0c583N139eef0510f164b0N13c775ee635f5e22N142803aa0f5f1196N195fc6c9a905eb55N1a0871bfcb078468N1a9985fd679e266bN1aa9412418a5c863N1c60de224f03cff6N1c64200a2ba3a6b5N1f3cfb657a8d00b0N2156b8d6064b5b03N21e25df3d635c4fcN2212bf715a907935N2291c63c144ec223N22fa46fb7e5a1bdeN2423cabe27383da9N242b3745d785ccc4N28601837b71b9204N2ab04f35b79398e5N2bbc73169cbcfe97N2cc2777c410e39feN2cf5d2debbba7f92N2d35800b5a89476aN2f9268096410612bN2f9a879b09a09fe4N2fb2a54c856cc39cN30712e3172ab9c62N31ae8548f8608826N33d6e5f2bd3cb3f8N34216f1b805da4d7N35129eb42b6c7e86N35ed81acb72b2db4N36de178c35110af7N36f5a15be4f6d213N39cc12042d3f6bd3N39ee6abee8112958N3bc7e74235374de3N3bde015f149554f0N3bea4d058cbab475"%lxh.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac addr_diff E A ::=
  let k := lazymatch E with
  | Z.add ?X ?c1 =>
      lazymatch A with
      | Z.add X ?c2 => let c1 := zlit c1 in let c2 := zlit c2 in eval vm_compute in (c1 - c2)%Z
      | X => zlit c1
      | _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
      end
  | _ =>
      lazymatch A with
      | Z.add E ?c2 => let c2 := zlit c2 in eval vm_compute in (- c2)%Z
      | E => constr:(0%Z)
      | _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
      end
  end in
  lazymatch eval vm_compute in (Z.leb 0 k) with true => k end.

Definition U_X509_SKID : Z := 0x27294.

Lemma land64_zero : forall r, -2^63 <= r < 2^63 -> Z.land r 18446744073709551615 = 0 -> r = 0.
Proof.
  intros r Hr H. change 18446744073709551615 with (Z.ones 64) in H. rewrite Z.land_ones in H by lia.
  destruct (Z.lt_ge_cases r 0); [| rewrite Z.mod_small in H by lia; exact H].
  rewrite <- (Z.mod_add r 1 (2^64)) in H by lia. rewrite Z.mod_small in H by lia. lia.
Qed.

(* [comment removed for export] *)
Ltac joinr H1 H2 :=
  lazymatch type of H1 with rw_cells ?sg ?mm ?A1 ?cs1 =>
  lazymatch type of H2 with rw_cells _ _ ?A2 ?cs2 =>
    replace A2 with (A1 + Z.of_nat (cells_size cs1)) in H2 by (cbn; lia);
    let Hj := fresh "J" in
    pose proof (proj2 (rw_cells_app sg mm A1 cs1 cs2) (conj H1 H2)) as Hj; clear H1 H2; rename Hj into H1;
    cbn [app] in H1
  end end.
Ltac zofnat H := cbn [cells_size csize Nat.add length] in H;
  repeat match type of H with context [Z.of_nat (Datatypes.S ?k)] => let v := eval vm_compute in (Z.of_nat (Datatypes.S k)) in change (Z.of_nat (Datatypes.S k)) with v in H end;
  repeat match type of H with context [Z.add (Z.add ?a ?b) ?c] => is_Zlit b; is_Zlit c; let v := eval vm_compute in (Z.add b c) in replace (Z.add (Z.add a b) c) with (Z.add a v) in H by lia end.
(* [comment removed for export] *)
Ltac spine_firstn k cs :=
  let k := eval cbv in k in
  lazymatch k with
  | Datatypes.O => eval lazy beta iota delta [firstn] in (firstn Datatypes.O cs)
  | Datatypes.S ?k' => lazymatch cs with
             | ?c :: ?cs' => let r := spine_firstn k' cs' in constr:(c :: r)
             | _ => eval cbv beta iota delta [firstn] in (firstn k cs)
             end
  end.
Ltac spine_skipn k cs :=
  let k := eval cbv in k in
  lazymatch k with
  | Datatypes.O => cs
  | Datatypes.S ?k' => lazymatch cs with
             | _ :: ?cs' => spine_skipn k' cs'
             | _ => eval cbv beta iota delta [skipn] in (skipn k cs)
             end
  end.
Ltac splitat H k H2 :=
  lazymatch type of H with rw_cells ?sg ?mm ?A0 ?cs =>
    let l1 := spine_firstn k cs in
    let l2 := spine_skipn k cs in
    change (rw_cells sg mm A0 (l1 ++ l2)) in H;
    let H1 := fresh "SP" in
    destruct (proj1 (rw_cells_app sg mm A0 l1 l2) H) as [H1 H2]; clear H; rename H1 into H; zofnat H2
  end.

Lemma U_x509_skid_spec {L : heap_layout} : x509_skid_stmt usegs L U_X509_SKID.
Proof.
  unfold x509_skid_stmt, U_X509_SKID.
  intros until q0.
  intros HPP HSK HBUF B1 B2 B3 B4 D1 D2 D3 AL1 AL2 NZ1 NZ2 NZ3 ST SLO ACL SPA DS1 DS2 DS3 MI -> -> ->.
  pose proof alloc_ceiling_pos as ACP.
  unfold X509_SKID_STACK in SLO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR.
  unfold bv_modulus in SPR.
  cbn in SPR.
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PPB.
  change (Z.of_nat 8) with 8 in PPB.
  pose proof (rw_cells_bound _ _ _ _ HSK) as SKB.
  cbn [cells_size csize Nat.add] in SKB.
  change (Z.of_nat 24) with 24 in SKB.
  pose proof (munch_refl [(PP, PP + 8); (SK, SK + 24); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  carve_frame 48%nat ST.
  lxp_split_frame [8;8;8;8;8;8]%nat. lxp_seps 48.
  pose proof (@sums1_ok) as LXSUMS.
  lxp_run (PLANS [] [] 80%N SUMS1).
  all: lxp_ret.
Qed.
