(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux X509Aux AStep CellsX Cells Mem.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepCrt CrtStmts CrtParseStmts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_asn1_get_tag.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_Sums1.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P025fa1e359e21b5b 0 2 0 1 5 1P02c3a3a55ad29bf5 0 2 0 1 7 1P02e55bfb67856a04 0 2 0 1 3 1P02f03e8909f8a50d 1 1 8 3 1 1 34 1 35 1 4 2 2 33 2 36 2 37 16P037d4ee361fbda8d 0 4 0 8 18 8 31 8 32 8P04a2a773dd369eca 0 4 0 1 28 1 38 1 39 1P0680dbce096e8a44 0 2 0 1 26 1P08576ac75ae3e63b 0 3 0 1 22 1 23 1P092e928a94ad06df 0 4 1 1 2 1 33 1 34 1P0b2d696271aadfce 2 16 0 5 0 1 3 1 21 1 31 1 32 1 0 4 0 1 2 1 31 1 32 1P0b99d71f3fedc7aa 2 20 1 1 8 3 1 1 34 1 35 1 5 0 2 23 2 33 2 36 2 37 16 1 1 8 3 2 1 33 1 36 1 4 0 2 34 2 35 2 37 16P0c3e0dfaec063d4f 0 2 0 1 24 1P0e819d9708eaa00b 0 2 0 1 26 1P0f406677cd7421ba 2 16 0 5 0 1 3 1 21 1 31 1 32 1 0 4 0 1 2 1 31 1 32 1P0f574d2ccb816288 1 1 8 3 1 1 33 1 36 1 4 2 1 34 1 35 1 37 8P10dec479f4a504a7 2 17 1 1 8 3 2 1 31 1 32 1 5 0 2 20 2 30 2 33 2 34 16 1 1 8 3 1 1 30 1 33 1 4 0 2 31 2 32 2 34 16P12c7b59c45941a3d 0 4 0 1 22 1 23 1 24 1P135c032206b83321 1 1 8 2 24 1 32 1 3 0 1 31 1 33 8P143094a1f6c8c755 0 4 0 1 31 1 41 1 42 1P144f0139543eb092 0 4 0 1 19 1 24 1 25 1P15648588fa5ed8b2 0 4 0 1 2 1 33 1 34 1P172617959f941281 0 4 0 1 29 1 39 1 40 1P184ea19aedf16b38 0 3 0 1 19 1 25 1P1aa5d5ffed40dc30 1 1 8 3 1 1 33 1 36 1 4 2 2 34 2 35 2 37 16P1de96f93cc502220 0 2 0 1 6 1P1e4ca47b9e475479 0 2 0 1 5 1P1ee1097cbcb16a7b 0 2 0 1 5 1P1f8634aa52c9dd98 0 2 0 1 5 1P2049e4e3419a7e9d 0 2 0 1 5 1P205875d23eb561ea 2 31 1 1 8 3 1 1 44 1 45 1 5 0 2 33 2 43 2 46 2 47 16 1 1 8 3 2 1 43 1 46 1 4 0 2 44 2 45 2 47 16P2124f35bd158d227 0 3 0 1 19 1 25 1P21276ee8f78ba81d 2 30 1 1 8 3 1 1 44 1 45 1 5 0 2 33 2 43 2 46 2 47 16 1 1 8 3 2 1 43 1 46 1 4 0 2 44 2 45 2 47 16P2301c4a36c12a4f5 0 3 0 1 22 1 23 1P231e8610f0f9b800 0 4 0 1 22 1 23 1 24 1P23bf0701f39e67fd 0 4 0 1 19 1 24 1 25 1P25c19293bb4fc236 0 3 0 1 1 1 24 1P25d9c3c2f1ef0a5d 2 16 0 5 0 1 3 1 21 1 31 1 32 1 0 4 0 1 2 1 31 1 32 1P25fdddf0cb6b4df3 0 2 0 1 6 1P26e5ea9f073fe26e 1 1 8 3 1 1 33 1 36 1 4 2 2 34 2 35 2 37 16P27915ff5ead967e3 0 4 0 1 19 1 29 1 30 1P2a223b0d0ace8367 2 17 1 1 8 3 2 1 31 1 32 1 5 0 2 20 2 30 2 33 2 34 16 1 1 8 3 1 1 30 1 33 1 4 0 2 31 2 32 2 34 16P2a67a3735ca9500d 0 2 0 1 24 1P33a2b599d9a99716 2 18 1 1 8 3 2 1 31 1 32 1 5 0 2 20 2 30 2 33 2 34 16 1 1 8 3 1 1 30 1 33 1 4 0 2 31 2 32 2 34 16P35b5d00979182a65 1 1 8 3 0 1 34 1 35 1 5 2 2 23 2 33 2 36 2 37 16P35e77eac228fd6f8 0 4 0 1 2 1 35 1 36 1P3941e226a6cdc489 1 1 8 3 1 1 34 1 35 1 4 2 2 33 2 36 2 37 16P3a2e1f1fab719408 1 1 8 3 0 1 34 1 35 1 4 2 1 33 1 36 1 37 8P3aac50877cbc337c 2 18 1 1 8 3 2 1 31 1 32 1 5 0 2 20 2 30 2 33 2 34 16 1 1 8 3 1 1 30 1 33 1 4 0 2 31 2 32 2 34 16P3abbbb5a8bfe4212 0 2 0 1 1 1P3bb5df39be1f4e4c 0 2 0 1 1 1P3c884ca3271862ff 2 18 1 1 8 3 2 1 31 1 32 1 5 0 2 20 2 30 2 33 2 34 16 1 1 8 3 1 1 30 1 33 1 4 0 2 31 2 32 2 34 16P3cd74710ec60bbb0 0 2 0 1 22 1P3d327845eea97d7a 0 2 0 1 28 1P3d3f465ce4ca4076 2 17 1 1 8 3 2 1 31 1 32 1 5 0 2 20 2 30 2 33 2 34 16 1 1 8 3 1 1 30 1 33 1 4 0 2 31 2 32 2 34 16P3d41a6766147055e 0 2 0 1 1 1P3db5edf7c592d973 1 1 8 3 0 1 34 1 35 1 5 2 2 23 2 33 2 36 2 37 16P3e41641ac4fe93ec 0 4 0 1 2 1 35 1 36 1P3fc8e689043d44e4 0 2 0 1 25 1N00dbb3af54ba9075N00f7acf84431e0bcN01191a493ede9e4fN01eb02b0c0bf9052N025504d58fa1a513N0445b3df3bc51458N044a191428b03815N045a7f0156af8278N0509d390e2d4c7bbN055459cecf894f49N061e07a292b5e1ecN062b7cfb3c2c51ecN0640d8d26865f753N07fa63bf02bfed0fN08c817771b8ab4e5N08f2df188a6856e5N0a8b9e9b3dd7feabN0b421c27e414e66cN0b7d372352a7bc4eN0bc5c050ced7dcb9N0d3675a9b052a688N0d3883d7fe970909N0d8e6bc62edc0b92N0da5f0c33de0ad61N0deef34da167009bN0df04cdb5b16bbf0N0e19502b7b626ce8N0e343bea7f1bafa0N0ec388c7ca8387deN0f398dd4b55290baN10317429d01bd3efN10de6092f6b7f73aN10def0347fa8171eN1385921b2ac99849N13ab97f5c039e9c1N143ff504d943959dN1448bfa05c7037f0N145d1ba1c0da151fN146f611ebc6fff84N147e0cd604faae8fN149fda14edd0e894N151033770a2830b6N153ba93ffd7143c4N1593a4039b09467fN15cb51883ffcb5f1N16025ea4b651c4f7N1722879845dd2bc7N18e5e5c534026475N1930468b21a2cc39N193ff3f865c6aed3N1968268d8a750f2fN1a2d09c45c24034fN1b335f1d9f840340N1b3b5d2132d1664cN1b3cd1fac252ab87N1b48aa1cd28d16e5N1c20cd7ef72312a4N1c63f048dd39cff5N1ce9de989121326fN1def917a2d3e202fN1eef8ba3aed9caa7N1f069762a87fe95bN1f53221dce3d92c3N1fedddb51bf35202N2007728ef4fd1b8fN201acdb1cd8fdb3aN21254fb17932d40bN218de7fb77a7407bN21fcaee4b635872bN224f25d9771e08e6N2325fe720d84c918N236c276fe5e2a30cN23dea5294e8a60b7N2540b5d6cde08126N25b2e345ee9c6978N25fc0f9f15714e3eN269463a0a980914bN26f4e636814b0f28N2927106ae96c571eN2929c06726f2edf1N299c95d45c89330cN29bbef9e7a6af2a2N29f9c129525c3a71N2a428674570b4699N2a8c614c449d1b87N2c641cd3925bc96dN2e3d5aae296248c8N2f44c51a80ebfb3bN2f5105c0f7a99443N2f83d94176b133a9N2f8fbab3b332c678N2fa657d401ce8009N303dec9dd614be25N30d56e1d6e7e21c4N31760049306c99dbN32000cc0d2b75191N326f73d414758927N339a72addb6545fbN346d70d4c8c50332N34ce93673bc9e9cfN35215dfb2b90d1afN35cd875a882349e0N3644c133b7cbe64aN36a098554eede40bN3717ef871fbed470N37184ea14a7826f1N376c0963a2487aa7N37efda2a30a2508eN38b662e1c0c934daN39ab530a64e71971N3a9bd51a73b97c33N3bddd59ee7cdee9cN3d12feee3959577eN3d40351ea3d6be67N3d71f9d507138ed8N3dddf3b34aa01159N3de12fd539e5af0aN3ef9a6c598be97deN3f84195267d30854N3fcf2c3af541df9c"%lxh.
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

Definition U_X509_GET_UID : Z := 0x26be4.

Lemma land64_zero : forall r, -2^63 <= r < 2^63 -> Z.land r 18446744073709551615 = 0 -> r = 0.
Proof.
  intros r Hr H. change 18446744073709551615 with (Z.ones 64) in H. rewrite Z.land_ones in H by lia.
  destruct (Z.lt_ge_cases r 0); [| rewrite Z.mod_small in H by lia; exact H].
  rewrite <- (Z.mod_add r 1 (2^64)) in H by lia. rewrite Z.mod_small in H by lia. lia.
Qed.
Lemma land64_nonzero : forall r, -2^63 <= r < 2^63 -> Z.land r 18446744073709551615 <> 0 -> r <> 0.
Proof. intros r Hr H ->. apply H. reflexivity. Qed.

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

Lemma U_x509_get_uid_spec {L : heap_layout} : x509_get_uid_stmt usegs L U_X509_GET_UID.
Proof.
  unfold x509_get_uid_stmt, U_X509_GET_UID.
  intros until q0.
  intros HPP HUID HBUF B1 B2 B3 B4 D1 D2 D3 AL1 AL2 NZ1 NZ2 NZ3 Hn ST SLO ACL SPA DS1 DS2 DS3 MI -> -> -> ->.
  pose proof alloc_ceiling_pos as ACP.
  unfold X509_GET_UID_STACK in SLO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR.
  unfold bv_modulus in SPR.
  cbn in SPR.
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PPB.
  change (Z.of_nat 8) with 8 in PPB.
  pose proof (rw_cells_bound _ _ _ _ HUID) as UIB.
  cbn [cells_size csize Nat.add] in UIB.
  change (Z.of_nat 24) with 24 in UIB.
  pose proof (munch_refl [(PP, PP + 8); (UID, UID + 24); (bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  carve_frame 32%nat ST.
  lxp_split_frame [8;8;8;8]%nat. lxp_seps 32.
  (* [comment removed for export] *)
  pose proof (@sums1_ok) as LXSUMS.
  lxp_run (PLANS [] [] 53%N SUMS1).
  { (* [comment removed for export] *)
    lxp_ret.
  }
  { (* [comment removed for export] *)
    lxp_ret.
  }
  { (* [comment removed for export] *)
    lxp_ret.
  }
  { (* [comment removed for export] *)
    lxp_ret.
  }
Qed.
