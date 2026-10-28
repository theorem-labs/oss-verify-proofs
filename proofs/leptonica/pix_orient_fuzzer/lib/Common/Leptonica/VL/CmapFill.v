(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import StartupTac RefMemcpyLib.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import RelocKitVL RelocTacVL CanonImgVL RCodeVL_24000_25000.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import RelocLept.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Musl Require Import MuslTac.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation SEGS := rl_segs.

Section VPORT.
Context {fx : FPState} {RLOC : Reloc} {RCODE : RelocCode RLOC} {RSITES : RelocSites RLOC} {RCODEF : RelocCodeVL RLOC} {RSITESF : RelocSitesVL RLOC} {RLEPT : RelocLept RLOC} {RIMGF : RelocImgVL RLOC}.   (* [comment removed for export] *)


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition ULITS : list (nat * Z) := [(23%nat, 0%Z); (9%nat, 4%Z); (22%nat, 4%Z)].
Definition UCLOB : list nat := [5; 10; 11; 12; 13; 14; 15; 16; 17; 23]%nat.

Lemma lez4 : forall z, (0 <= z < 2 ^ 32)%Z -> bytes_le_to_Z (Z_to_le_bytes 4 z) = bv_unsigned (Z_to_bv 64 z).
Proof.
  intros z Hz. rewrite bytes_le_Z_to_le by lia. change (2 ^ (8 * Z.of_nat 4))%Z with (2 ^ 32)%Z.
  rewrite Z.mod_small by lia. rewrite u_Z2bv by lia. reflexivity.
Qed.
Lemma lez8 : forall z, (0 <= z < 2 ^ 64)%Z -> bytes_le_to_Z (Z_to_le_bytes 8 z) = bv_unsigned (Z_to_bv 64 z).
Proof.
  intros z Hz. rewrite bytes_le_Z_to_le by lia. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z.
  rewrite Z.mod_small by lia. rewrite u_Z2bv by lia. reflexivity.
Qed.
Lemma w2b4_Z : forall z, (0 <= z < 2 ^ 64)%Z -> word_to_le_bytes 4 (Z_to_bv 64 z) = Z_to_le_bytes 4 z.
Proof. intros z Hz. unfold word_to_le_bytes. rewrite u_Z2bv by lia. reflexivity. Qed.

Section CF.
  Variable M : word -> option byte.          (* [comment removed for export] *)
  Variable rom : word -> option byte.
  Variables cmap dd nc arr nalloc : Z.       (* [comment removed for export] *)
  Variable bs : list byte.                   (* [comment removed for export] *)

  Hypothesis Hcmap : (1 <= cmap /\ cmap + 24 <= 2 ^ 64)%Z.
  Hypothesis Hnc : (1 <= nc <= 256)%Z.
  Hypothesis Hnal : (nc <= nalloc <= 256)%Z.
  Hypothesis Harr : (1 <= arr /\ arr + 4 * nalloc <= 2 ^ 64)%Z.
  Hypothesis Hdat : (1 <= dd /\ dd + 4 * nc <= 2 ^ 64)%Z.
  Hypothesis Carr : rdn SEGS M (Z_to_bv 64 cmap) 8 = Some (Z_to_le_bytes 8 arr).
  Hypothesis Cnal : rdn SEGS M (Z_to_bv 64 (cmap + 12)) 4 = Some (Z_to_le_bytes 4 nalloc).
  Hypothesis Cn0 : rdn SEGS M (Z_to_bv 64 (cmap + 16)) 4 = Some (Z_to_le_bytes 4 0).
  Hypothesis Dbs : rdn SEGS M (Z_to_bv 64 dd) (Z.to_nat (4 * nc)) = Some bs.
  Hypothesis SOKa : store_ok SEGS M (Z_to_bv 64 arr) (Z.to_nat (4 * nalloc)) = true.
  Hypothesis SOKc : store_ok SEGS M (Z_to_bv 64 cmap) 24 = true.
  Hypothesis A_ca : (cmap + 24 <= arr \/ arr + 4 * nalloc <= cmap)%Z.
  Hypothesis A_cd : (cmap + 24 <= dd \/ dd + 4 * nc <= cmap)%Z.
  Hypothesis A_ad : (arr + 4 * nalloc <= dd \/ dd + 4 * nc <= arr)%Z.

  Definition b_ (j : Z) : byte := nth (Z.to_nat j) bs (Z_to_bv 8 0).

  Lemma rd_b : forall j, (0 <= j < 4 * nc)%Z ->
    rdn SEGS M (Z_to_bv 64 (dd + j)) 1 = Some [b_ j].
  Proof.
    intros j Hj. clear A_ca A_cd A_ad.
    pose proof (rdn_sub SEGS M (Z.to_nat (4 * nc)) (Z_to_bv 64 dd) bs (Z.to_nat j) 1 Dbs ltac:(lia)) as H.
    unfold at_ in H. rewrite u_Z2bv, Z2Nat.id in H by lia. rewrite H. f_equal.
    unfold b_. apply sub_nth. rewrite (rdn_length _ _ _ _ _ Dbs). lia.
  Qed.

  Definition CInv (i : Z) (Mi : word -> option byte) : Prop :=
    (forall x : word,
        ~ (arr <= bv_unsigned x < arr + 4 * i)%Z -> ~ (cmap + 16 <= bv_unsigned x < cmap + 20)%Z ->
        Mi x = M x)
    /\ mem_grows M Mi
    /\ rdn SEGS Mi (Z_to_bv 64 (cmap + 16)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 i)).

  Lemma CInv_0 : CInv 0 M.
  Proof.
    split; [intros; reflexivity|]. split; [apply mem_grows_refl|].
    rewrite Cn0. reflexivity.
  Qed.

  Lemma CInv_rd : forall i Mi (a : Z) (n : nat) r,
    CInv i Mi -> (0 <= a)%Z -> (a + Z.of_nat n <= 2 ^ 64)%Z ->
    (a + Z.of_nat n <= arr \/ arr + 4 * i <= a)%Z -> (a + Z.of_nat n <= cmap + 16 \/ cmap + 20 <= a)%Z ->
    rdn SEGS M (Z_to_bv 64 a) n = Some r -> rdn SEGS Mi (Z_to_bv 64 a) n = Some r.
  Proof.
    intros i Mi a n r [HI _] Ha Hn A1 A2 HM. clear A_ca A_cd A_ad. rewrite <- HM.
    destruct n as [|n']; [reflexivity|].
    apply rdn_ext; rewrite u_Z2bv by lia; [lia|]. intros x Hx. apply HI; lia.
  Qed.

  Lemma CInv_sok : forall i Mi (a : word) (n : nat),
    CInv i Mi -> store_ok SEGS M a n = true -> store_ok SEGS Mi a n = true.
  Proof. intros i Mi a n [_ [HG _]] H. eapply store_ok_mono; [exact HG | exact H]. Qed.

  Lemma sok_arr : forall (a : Z) (n : nat), (arr <= a)%Z -> (a + Z.of_nat n <= arr + 4 * nalloc)%Z ->
    store_ok SEGS M (Z_to_bv 64 a) n = true.
  Proof.
    intros a n Ha Hn. clear A_ca A_cd A_ad. destruct n as [|n']; [reflexivity|].
    eapply (store_ok_sub SEGS M (Z_to_bv 64 arr) _ (Z.to_nat (4 * nalloc))); [ | exact SOKa | | ];
      rewrite ?u_Z2bv by lia; lia.
  Qed.

  Lemma sok_ncell : store_ok SEGS M (Z_to_bv 64 (cmap + 16)) 4 = true.
  Proof.
    clear A_ca A_cd A_ad.
    eapply (store_ok_sub SEGS M (Z_to_bv 64 cmap) _ 24); [ | exact SOKc | | ]; rewrite ?u_Z2bv by lia; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma CInv_step : forall i Mi (v0 v1 v2 v3 : word),
    CInv i Mi -> (0 <= i < nc)%Z ->
    CInv (i + 1)
      (wbytes (wbytes (wbytes (wbytes (wbytes Mi
         (Z_to_bv 64 (arr + 4 * i + 2)) [Z_to_bv 8 (bv_unsigned v2)])
         (Z_to_bv 64 (arr + 4 * i)) [Z_to_bv 8 (bv_unsigned v0)])
         (Z_to_bv 64 (arr + 4 * i + 1)) [Z_to_bv 8 (bv_unsigned v1)])
         (Z_to_bv 64 (arr + 4 * i + 3)) [Z_to_bv 8 (bv_unsigned v3)])
         (Z_to_bv 64 (cmap + 16)) (word_to_le_bytes 4 (Z_to_bv 64 (i + 1)))).
  Proof.
    intros i Mi v0 v1 v2 v3 [HI [HG HN]] Hi. split; [|split].
    - intros x Hx1 Hx2.
      rewrite !wbytes_outside by (zlen; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ?u_Z2bv by lia; lia).
      apply HI; lia.
    - eapply mem_grows_trans; [exact HG|]. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl.
    - apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia.
  Qed.

  Ltac ldb F D j HIv :=
    stepLBU F D (b_ j)
      ltac:(rdn_addr (dd + j)%Z; apply (CInv_rd _ _ _ 1%nat _ HIv); [lia | lia | lia | lia | apply rd_b; lia]).

  (* [comment removed for export] *)
  Lemma cf_iter : forall regs Mi (i : Z),
    (0 <= i < nc)%Z -> CInv i Mi ->
    getr regs 9 = Z_to_bv 64 4 -> getr regs 22 = Z_to_bv 64 4 ->
    getr regs 19 = Z_to_bv 64 cmap -> getr regs 18 = Z_to_bv 64 dd -> getr regs 8 = Z_to_bv 64 nc ->
    getr regs 23 = Z_to_bv 64 i ->
    exists regs' M',
      msteps SEGS (mkst regs (rl dVL_2486c 0x24a60) Mi rom) (mkst regs' (rl dVL_2486c 0x24a5c) M' rom)
      /\ CInv (i + 1) M'
      /\ getr regs' 9 = Z_to_bv 64 4 /\ getr regs' 22 = Z_to_bv 64 4
      /\ getr regs' 19 = Z_to_bv 64 cmap /\ getr regs' 18 = Z_to_bv 64 dd /\ getr regs' 8 = Z_to_bv 64 nc
      /\ getr regs' 23 = Z_to_bv 64 (i + 1)
      /\ regs_agree (fun x : reg => In x [5; 10; 11; 12; 13; 14; 15; 16; 17; 23]%list) regs regs'.
  Proof.
    intros regs Mi i Hi HIv H9 H22 H19 H18 H8 H23.
    eexists. eexists. split; [|split].
    - stepat F_24a60 D_24a60 (Z_to_bv 64 (4 * i))
        ltac:(gres; pin; rewrite zbv_mulw_small by lia; reflexivity).   (* [comment removed for export] *)
      zv F_24a64 D_24a64 (Z_to_bv 64 (4 * i)).              (* [comment removed for export] *)
      stepb_ft F_24a68 D_24a68 ltac:(condZ).                (* [comment removed for export] *)
      zv F_24a6c D_24a6c (Z_to_bv 64 (dd + 4 * i)).         (* [comment removed for export] *)
      stepb_ft F_24a70 D_24a70 ltac:(condZ).                (* [comment removed for export] *)
      stepat F_24a74 D_24a74 (Z_to_bv 64 0)
        ltac:(gres; pin; rewrite v_sltu_Z by lia; rewrite Zltb_f by lia; reflexivity).   (* [comment removed for export] *)
      stepat F_24a78 D_24a78 (Z_to_bv 64 0)
        ltac:(gres; pin; imm_norm; rewrite v_slti_Z by lia; rewrite Zltb_f by lia; reflexivity).   (* [comment removed for export] *)
      sn F_24a7c D_24a7c.                                   (* [comment removed for export] *)
      sn F_24a80 D_24a80.                                   (* [comment removed for export] *)
      stepb_ft F_24a84 D_24a84 ltac:(condZ).                (* [comment removed for export] *)
      stepiv F_24a88 D_24a88 (Z_to_bv 64 (4 * i + 1))
        ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).   (* [comment removed for export] *)
      stepb_ft F_24a8c D_24a8c ltac:(condZ).                (* [comment removed for export] *)
      zv F_24a90 D_24a90 (Z_to_bv 64 (dd + 4 * i + 1)).     (* [comment removed for export] *)
      stepb_ft F_24a94 D_24a94 ltac:(condZ).                (* [comment removed for export] *)
      stepat F_24a98 D_24a98 (Z_to_bv 64 0)
        ltac:(gres; pin; rewrite v_sltu_Z by lia; rewrite Zltb_f by lia; reflexivity).   (* [comment removed for export] *)
      stepat F_24a9c D_24a9c (Z_to_bv 64 0)
        ltac:(gres; pin; imm_norm; rewrite v_slti_Z by lia; rewrite Zltb_f by lia; reflexivity).   (* [comment removed for export] *)
      sn F_24aa0 D_24aa0.                                   (* [comment removed for export] *)
      sn F_24aa4 D_24aa4.                                   (* [comment removed for export] *)
      stepb_ft F_24aa8 D_24aa8 ltac:(condZ).                (* [comment removed for export] *)
      stepiv F_24aac D_24aac (Z_to_bv 64 (4 * i + 2))
        ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).   (* [comment removed for export] *)
      stepb_ft F_24ab0 D_24ab0 ltac:(condZ).                (* [comment removed for export] *)
      zv F_24ab4 D_24ab4 (Z_to_bv 64 (dd + 4 * i + 2)).     (* [comment removed for export] *)
      stepb_ft F_24ab8 D_24ab8 ltac:(condZ).                (* [comment removed for export] *)
      stepat F_24abc D_24abc (Z_to_bv 64 0)
        ltac:(gres; pin; rewrite v_sltu_Z by lia; rewrite Zltb_f by lia; reflexivity).   (* [comment removed for export] *)
      stepat F_24ac0 D_24ac0 (Z_to_bv 64 0)
        ltac:(gres; pin; imm_norm; rewrite v_slti_Z by lia; rewrite Zltb_f by lia; reflexivity).   (* [comment removed for export] *)
      sn F_24ac4 D_24ac4.                                   (* [comment removed for export] *)
      sn F_24ac8 D_24ac8.                                   (* [comment removed for export] *)
      stepb_ft F_24acc D_24acc ltac:(condZ).                (* [comment removed for export] *)
      ldb F_24ad0 D_24ad0 (4 * i)%Z HIv.                    (* [comment removed for export] *)
      ldb F_24ad4 D_24ad4 (4 * i + 1)%Z HIv.                (* [comment removed for export] *)
      ldb F_24ad8 D_24ad8 (4 * i + 2)%Z HIv.                (* [comment removed for export] *)
      stepb_ft F_24adc D_24adc ltac:(condZ).                (* [comment removed for export] *)
      zv F_24ae0 D_24ae0 (Z_to_bv 64 (4 * i + 3)).          (* [comment removed for export] *)
      zv F_24ae4 D_24ae4 (Z_to_bv 64 (dd + 4 * i + 3)).     (* [comment removed for export] *)
      stepb_ft F_24ae8 D_24ae8 ltac:(condZ).                (* [comment removed for export] *)
      stepat F_24aec D_24aec (Z_to_bv 64 0)
        ltac:(gres; pin; rewrite v_sltu_Z by lia; rewrite Zltb_f by lia; reflexivity).   (* [comment removed for export] *)
      sn F_24af0 D_24af0.                                   (* [comment removed for export] *)
      sn F_24af4 D_24af4.                                   (* [comment removed for export] *)
      stepb_ft F_24af8 D_24af8 ltac:(condZ).                (* [comment removed for export] *)
      ldb F_24afc D_24afc (4 * i + 3)%Z HIv.                (* [comment removed for export] *)
      sn F_24b00 D_24b00.                                   (* [comment removed for export] *)
      stepLD F_24b08 D_24b08 (Z_to_le_bytes 4 nalloc) (Z_to_bv 64 nalloc)
        ltac:(rdn_addr (cmap + 12)%Z; apply (CInv_rd _ _ _ 4%nat _ HIv); [lia | lia | lia | lia | exact Cnal])
        ltac:(apply lez4; lia).                             (* [comment removed for export] *)
      rewrite (v_lw_small nalloc) by lia.
      stepLD F_24b0c D_24b0c (word_to_le_bytes 4 (Z_to_bv 64 i)) (Z_to_bv 64 i)
        ltac:(rdn_addr (cmap + 16)%Z; exact (proj2 (proj2 HIv)))
        ltac:(apply bytes_le_to_Z_4; unorm; lia).          (* [comment removed for export] *)
      rewrite (v_lw_small i) by lia.
      stepb_ft F_24b10 D_24b10 ltac:(condZ).                (* [comment removed for export] *)
      stepLD F_24b14 D_24b14 (Z_to_le_bytes 8 arr) (Z_to_bv 64 arr)
        ltac:(rdn_addr cmap; apply (CInv_rd _ _ _ 8%nat _ HIv); [lia | lia | lia | lia | exact Carr])
        ltac:(apply lez8; lia).                             (* [comment removed for export] *)
      stepiv F_24b18 D_24b18 (Z_to_bv 64 (4 * i))
        ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).  (* [comment removed for export] *)
      zv F_24b1c D_24b1c (Z_to_bv 64 (arr + 4 * i)).        (* [comment removed for export] *)
      stepat F_24b20 D_24b20 (Z_to_bv 64 1)
        ltac:(gres; pin; rewrite v_sltu_Z by lia; rewrite Zltb_t by lia; reflexivity).   (* [comment removed for export] *)
      stepiv F_24b24 D_24b24 (Z_to_bv 64 0)
        ltac:(gres; pin; imm_norm; rewrite v_sltiu_Z by lia; rewrite Zltb_f by lia; reflexivity).   (* [comment removed for export] *)
      stepb_ft F_24b28 D_24b28 ltac:(condZ).                (* [comment removed for export] *)
      stepat F_24b2c D_24b2c (Z_to_bv 64 0)
        ltac:(gres; pin; rewrite v_sltu_Z by lia; rewrite Zltb_f by lia; reflexivity).   (* [comment removed for export] *)
      stepat F_24b30 D_24b30 (Z_to_bv 64 0)
        ltac:(gres; pin; imm_norm; rewrite v_slti_Z by lia; rewrite Zltb_f by lia; reflexivity).   (* [comment removed for export] *)
      sn F_24b34 D_24b34.                                   (* [comment removed for export] *)
      sn F_24b38 D_24b38.                                   (* [comment removed for export] *)
      stepb_ft F_24b3c D_24b3c ltac:(condZ).                (* [comment removed for export] *)
      stepb_ft F_24b40 D_24b40 ltac:(condZ).                (* [comment removed for export] *)
      stepST F_24b44 D_24b44 (Z_to_bv 64 (arr + 4 * i + 2)) (Z_to_bv 64 (bv_unsigned (b_ (4 * i))))
        ltac:(apply (CInv_sok _ _ _ _ HIv); apply sok_arr; cbn; lia).            (* [comment removed for export] *)
      stepb_tk F_24b48 D_24b48 ltac:(condZ).                (* [comment removed for export] *)
      stepST F_24a44 D_24a44 (Z_to_bv 64 (arr + 4 * i)) (Z_to_bv 64 (bv_unsigned (b_ (4 * i + 2))))
        ltac:(store_ok_peel; apply (CInv_sok _ _ _ _ HIv); apply sok_arr; cbn; lia).   (* [comment removed for export] *)
      stepST F_24a48 D_24a48 (Z_to_bv 64 (arr + 4 * i + 1)) (Z_to_bv 64 (bv_unsigned (b_ (4 * i + 1))))
        ltac:(store_ok_peel; apply (CInv_sok _ _ _ _ HIv); apply sok_arr; cbn; lia).   (* [comment removed for export] *)
      stepST F_24a4c D_24a4c (Z_to_bv 64 (arr + 4 * i + 3)) (Z_to_bv 64 (bv_unsigned (b_ (4 * i + 3))))
        ltac:(store_ok_peel; apply (CInv_sok _ _ _ _ HIv); apply sok_arr; cbn; lia).   (* [comment removed for export] *)
      zv F_24a50 D_24a50 (Z_to_bv 64 (i + 1)).              (* [comment removed for export] *)
      stepST F_24a54 D_24a54 (Z_to_bv 64 (cmap + 16)) (Z_to_bv 64 (i + 1))
        ltac:(store_ok_peel; apply (CInv_sok _ _ _ _ HIv); apply sok_ncell).           (* [comment removed for export] *)
      stepiv F_24a58 D_24a58 (Z_to_bv 64 (i + 1))
        ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).   (* [comment removed for export] *)
      apply mst_refl.
    - apply (CInv_step i Mi); [exact HIv | exact Hi].
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma cf_loop : forall (k : nat) regs Mi (i : Z),
    (Z.of_nat k = nc - i - 1)%Z -> (0 <= i)%Z -> CInv i Mi ->
    getr regs 9 = Z_to_bv 64 4 -> getr regs 22 = Z_to_bv 64 4 ->
    getr regs 19 = Z_to_bv 64 cmap -> getr regs 18 = Z_to_bv 64 dd -> getr regs 8 = Z_to_bv 64 nc ->
    getr regs 23 = Z_to_bv 64 i ->
    exists regs' M',
      msteps SEGS (mkst regs (rl dVL_2486c 0x24a60) Mi rom) (mkst regs' (rl dVL_2486c 0x24984) M' rom)
      /\ CInv nc M'
      /\ getr regs' 9 = Z_to_bv 64 4 /\ getr regs' 22 = Z_to_bv 64 4
      /\ getr regs' 19 = Z_to_bv 64 cmap /\ getr regs' 18 = Z_to_bv 64 dd /\ getr regs' 8 = Z_to_bv 64 nc
      /\ regs_agree (fun x : reg => In x [5; 10; 11; 12; 13; 14; 15; 16; 17; 23]%list) regs regs'.
  Proof.
    induction k as [|k IH]; intros regs Mi i Hk Hi HIv H9 H22 H19 H18 H8 H23;
      destruct (cf_iter regs Mi i ltac:(lia) HIv H9 H22 H19 H18 H8 H23)
        as (r1 & M1 & S1 & HI1 & R9 & R22 & R19 & R18 & R8 & R23 & AG1).
    - exists r1, M1. replace (i + 1)%Z with nc in HI1 by lia.
      split; [|split; [exact HI1 | repeat split; try assumption]].
      eapply msteps_trans; [exact S1|].
      stepb_tk F_24a5c D_24a5c ltac:(condZ).                (* [comment removed for export] *)
      apply mst_refl.
    - destruct (IH r1 M1 (i + 1)%Z ltac:(lia) ltac:(lia) HI1 R9 R22 R19 R18 R8 R23)
        as (r2 & M2 & S2 & HI2 & Q9 & Q22 & Q19 & Q18 & Q8 & AG2).
      exists r2, M2. split; [|split; [exact HI2 | repeat split; try assumption; eapply regs_agree_trans; eassumption]].
      eapply msteps_trans; [exact S1|].
      stepb_ft F_24a5c D_24a5c ltac:(condZ).                (* [comment removed for export] *)
      exact S2.
  Qed.

End CF.

Theorem cmapfill_contract :
  SSP.sum_contract SEGS (SSP.spec_cmapfill (0x24a60 + dVL_2486c) (0x24984 + dVL_2486c) 19 18 0 8 ULITS UCLOB).
Proof.
  intros ins R M rom Hlen PRE.
  destruct ins as [|cmap [|dd [|nc [|arr [|nalloc [|n0 [|l23 [|l9 [|l22 [|? ?]]]]]]]]]]; try discriminate Hlen.
  unfold SSP.spec_cmapfill, ULITS, UCLOB in PRE. cbn [SSP.lit_items app] in PRE. SSP.spec_unfold_in PRE.
  destruct PRE as (ITEMS & EFF & FR & _).
  destruct ITEMS as ((H19 & _) & Hcmap & _ & (H18 & Rdd) & (H8 & _) & Hnc & Hdnz & (_ & _ & (Rarr & Carr)) & Harr
                     & (_ & _ & (Rnal & Cnal)) & Hle & Hnal & (_ & (_ & _ & Fc16) & (_ & Cn)) & Hn0
                     & ((Fd1 & _ & Fd2) & (bs & Dbs)) & ((_ & _ & Fa) & SOKa) & ((_ & _ & Fc) & SOKc)
                     & A_ca & A_cd & A_ad & (H23 & _) & Hl23 & (H9 & _) & Hl9 & (H22 & _) & Hl22 & _).
  subst n0 l23 l9 l22.
  rewrite Z.add_0_r in Carr. replace (dd + - 0)%Z with dd in * by lia.
  change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in Rarr. change (2 ^ (8 * Z.of_nat 4))%Z with (2 ^ 32)%Z in Rnal.
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Fc16.
  exists []. unfold SSP.spec_cmapfill, ULITS, UCLOB. cbn [SSP.lit_items app]. SSP.spec_unfold.
  replace (dd + - 0)%Z with dd by lia.
  destruct (cf_loop M rom cmap dd nc arr nalloc bs ltac:(lia) Hnc ltac:(lia) ltac:(lia) ltac:(lia)
              Carr Cnal Dbs SOKa ltac:(exact SOKc) A_ca A_cd A_ad
              (Z.to_nat (nc - 1)) R M 0 ltac:(lia) ltac:(lia) (CInv_0 M cmap arr Cn) H9 H22 H19 H18 H8 H23)
    as (R' & M' & RUN & HI & A9 & A22 & A19 & A18 & A8 & AG).
  exists R', M'.
  split; [reflexivity|]. split; [exact RUN|].
  destruct HI as (HO & HG & HN).
  split; [repeat split; first [apply AG; notin_list | rewrite ?A9, ?A22, ?A19, ?A18, ?A8; symmetry; assumption]|].
  split; [exact I|].
  split.
  { intros x (Hx1 & Hx2 & _). cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx2. apply HO; clear A_ca A_cd A_ad; lia. }
  split; [exact HG|].
  split; [|exact I]. split; [exact I|]. split; [|exact I].
  split; [clear A_ca A_cd A_ad; change (2 ^ (8 * Z.of_nat 4))%Z with (2 ^ 32)%Z; rewrite Z.mod_small by lia; lia|].
  rewrite HN. change (2 ^ (8 * Z.of_nat 4))%Z with (2 ^ 32)%Z. rewrite Z.mod_small by lia.
  rewrite w2b4_Z by lia. reflexivity.
Qed.


End VPORT.
