(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import StartupTac RefMemcpyLib.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require Import RelocKitVL RelocTacVL CanonImgVL RCodeVL_237d4_24000 RCodeVL_24000_25000.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import RelocLept.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require Import MuslTac.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac zval ::= rl_zval.      (* [comment removed for export] *)
#[local] Ltac condZ ::= rl_condZ.

Abbreviation SEGS := rl_segs.

Section VPORT.
Context {fx : FPState} {RLOC : Reloc} {RCODE : RelocCode RLOC} {RSITES : RelocSites RLOC} {RCODEF : RelocCodeVL RLOC} {RSITESF : RelocSitesVL RLOC} {RLEPT : RelocLept RLOC} {RIMGF : RelocImgVL RLOC}.   (* [comment removed for export] *)


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma wr_readable_u16 : wr_readable SEGS.
Proof. exact rl_wr_readable. Qed.

(* [comment removed for export] *)
Lemma rmask_tbl : exists T, rdn SEGS (fun _ => None) (rl dA_10a80 0x10a80) 132 = Some T.
Proof. rl_dbounds (dA_10a80 :: nil). rl_limg_VL. Qed.

Lemma rmask_read : forall m e, (0 <= e <= 32)%Z ->
  exists bs, rdn SEGS m (Z_to_bv 64 ((0x10a80 + dA_10a80) + 4 * e)) 4 = Some bs /\ length bs = 4%nat.
Proof. rl_dbounds (dA_10a80 :: nil).
  intros m e He. destruct rmask_tbl as [T HT].
  pose proof (rdn_sub SEGS (fun _ => None) 132 (rl dA_10a80 0x10a80) T (Z.to_nat (4 * e)) 4 HT ltac:(lia)) as HS.
  unfold at_ in HS. rewrite rl_delta_u in HS by lia. rewrite Z2Nat.id in HS by lia.
  exact (rdn_rom_any SEGS m 4 _ _ HS).
Qed.

Section PB.
  (* [comment removed for export] *)
  Variable M : word -> option byte.          (* [comment removed for export] *)
  Variable rom : word -> option byte.
  Variables pix w h d wpl data sp : Z.
  Variables ra s0v s1v s2v : word.           (* [comment removed for export] *)

  Hypothesis Hpix : (1 <= pix /\ pix + 12 <= 2 ^ 64)%Z.
  Hypothesis Hpix64 : (pix + 64 <= 2 ^ 64)%Z.
  Hypothesis ALpix : is_aligned pix 8.
  Hypothesis Rw : (0 <= w < 2 ^ 32)%Z.
  Hypothesis Rh : (0 <= h < 2 ^ 32)%Z.
  Hypothesis Hw : (1 <= w <= 20000)%Z.
  Hypothesis Hh : (1 <= h <= 20000)%Z.
  Hypothesis Hd : (d = 1 \/ d = 2 \/ d = 4 \/ d = 8 \/ d = 16 \/ d = 24)%Z.
  Hypothesis Hsp : (48 <= sp /\ sp < 2 ^ 64)%Z.
  Hypothesis ALsp : is_aligned sp 16.
  Hypothesis Hra : ret_ok ra.
  Hypothesis Cw : rdn SEGS M (Z_to_bv 64 pix) 4 = Some (Z_to_le_bytes 4 w).
  Hypothesis Ch : rdn SEGS M (Z_to_bv 64 (pix + 4)) 4 = Some (Z_to_le_bytes 4 h).
  Hypothesis Cd : rdn SEGS M (Z_to_bv 64 (pix + 8)) 4 = Some (Z_to_le_bytes 4 d).
  Hypothesis Cwpl : rdn SEGS M (Z_to_bv 64 (pix + 16)) 4 = Some (Z_to_le_bytes 4 wpl).
  Hypothesis Cdata : rdn SEGS M (Z_to_bv 64 (pix + 56)) 8 = Some (Z_to_le_bytes 8 data).
  Hypothesis Hwpl : (0 <= wpl <= 20000)%Z.
  Hypothesis Hdata : (1 <= data /\ data < 2 ^ 64)%Z.
  Hypothesis ALdata : is_aligned data 4.
  Hypothesis HR : (data + 4 * (wpl * h) <= 2 ^ 64)%Z.
  Hypothesis SOKr : store_ok SEGS M (Z_to_bv 64 data) (Z.to_nat (4 * (wpl * h))) = true.
  Hypothesis FR : disj_apart data (4 * (wpl * h)) (sp - 48) 48.
  Hypothesis SOKf : store_ok SEGS M (Z_to_bv 64 (sp - 48)) 48 = true.
  Hypothesis FP12 : disj_apart pix 12 (sp - 48) 48.
  Hypothesis FP : disj_apart pix 64 (sp - 48) 48.


  Definition M1 : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes M (Z_to_bv 64 (sp - 8)) (word_to_le_bytes 8 ra))
                           (Z_to_bv 64 (sp - 16)) (word_to_le_bytes 8 s0v))
                   (Z_to_bv 64 (sp - 24)) (word_to_le_bytes 8 s1v))
           (Z_to_bv 64 (sp - 32)) (word_to_le_bytes 8 s2v).
  Definition M2g (vw vh : word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M1
      (Z_to_bv 64 (sp - 36)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 (sp - 40)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 (sp - 44)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 (sp - 36)) (word_to_le_bytes 4 vw))
      (Z_to_bv 64 (sp - 40)) (word_to_le_bytes 4 vh))
      (Z_to_bv 64 (sp - 44)) (word_to_le_bytes 4 (Z_to_bv 64 d)).
  Definition M2x : word -> option byte := M2g (v_lw (Z_to_bv 64 w)) (v_lw (Z_to_bv 64 h)).
  Definition M2 : word -> option byte := M2g (Z_to_bv 64 w) (Z_to_bv 64 h).

  Lemma M2x_M2 : M2x = M2.
  Proof. unfold M2x, M2. rewrite !v_lw_small by lia. reflexivity. Qed.

  Lemma sok_frame : forall m k (n : nat), mem_grows M m -> (Z.of_nat n <= k <= 48)%Z ->
    store_ok SEGS m (Z_to_bv 64 (sp - k)) n = true.
  Proof.
    intros m k n Hg Hk. eapply store_ok_mono; [exact Hg|].
    destruct n as [|n']; [reflexivity|].
    eapply (store_ok_sub SEGS M (Z_to_bv 64 (sp - 48)) _ 48%nat); [ | exact SOKf | | ];
      rewrite ?u_Z2bv by lia; lia.
  Qed.

  Ltac grows := repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl.
  Ltac sokf := apply sok_frame; [ unfold M1, M2, M2x, M2g; grows | cbn; lia ].
  Ltac peelf := unfold M2, M2x, M2g, M1; repeat (rewrite rdn_wbytes_out_Z by (zlen; rewrite ?length_Z_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)).

  Lemma lez8 : forall z, (0 <= z < 2 ^ 64)%Z -> bytes_le_to_Z (Z_to_le_bytes 8 z) = bv_unsigned (Z_to_bv 64 z).
  Proof.
    intros z Hz. rewrite bytes_le_Z_to_le by lia. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z.
    rewrite Z.mod_small by lia. rewrite u_Z2bv by lia. reflexivity.
  Qed.
  Lemma lez4 : forall z, (0 <= z < 2 ^ 32)%Z -> bytes_le_to_Z (Z_to_le_bytes 4 z) = bv_unsigned (Z_to_bv 64 z).
  Proof.
    intros z Hz. rewrite bytes_le_Z_to_le by lia. change (2 ^ (8 * Z.of_nat 4))%Z with (2 ^ 32)%Z.
    rewrite Z.mod_small by lia. rewrite u_Z2bv by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma sp_slot4 : forall k, (k mod 4 = 0)%Z -> ((sp - k) mod 4 = 0)%Z.
  Proof. intros k Hk. pose proof ALsp as AL. use_aligned AL. apply mod0_sub; [lia | apply mod16_mod4; exact AL | exact Hk]. Qed.

  Lemma pix_al8 : (pix mod 8 = 0)%Z.
  Proof. pose proof ALpix as AL. use_aligned AL. exact AL. Qed.

  Ltac stf F D k v := stepST F D (Z_to_bv 64 (sp - k)) v ltac:(sokf).
  Ltac ldpixg F D z C :=
    stepLD F D (Z_to_le_bytes 4 z) (Z_to_bv 64 z)
      ltac:(unfold v_addi; unorm; rewrite ?Z.add_0_r; peelf; exact C)
      ltac:(apply lez4; lia).
  Ltac ldpix F D z C := ldpixg F D z C; rewrite (v_lw_small z) by lia.
  (* [comment removed for export] *)
  Ltac andi_slot F D k :=
    stepiv F D (Z_to_bv 64 0)
      ltac:(gres; pin; imm_norm; rewrite andi_3, u_Z2bv by lia; rewrite (sp_slot4 k) by reflexivity; reflexivity).
  (* [comment removed for export] *)
  Ltac andi_pix F D :=
    stepiv F D (Z_to_bv 64 0)
      ltac:(gres; pin; imm_norm; rewrite andi_7, u_Z2bv by lia; rewrite pix_al8; reflexivity).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma pb_A : forall regs,
    getr regs 1 = ra -> getr regs 2 = Z_to_bv 64 sp -> getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v ->
    getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_242cc 0x242cc) M rom) (mkst regs' (rl dVL_242cc 0x2430c) M2x rom)
      /\ getr regs' 2 = Z_to_bv 64 (sp - 48) /\ getr regs' 18 = Z_to_bv 64 pix /\ getr regs' 8 = Z_to_bv 64 0
      /\ getr regs' 10 = Z_to_bv 64 d /\ getr regs' 11 = Z_to_bv 64 24
      /\ regs_agree (fun r : reg => In r [1; 2; 8; 10; 11; 12; 13; 14; 15; 16; 17; 18]%list) regs regs'.
  Proof.
    intros regs H1 H2 H8 H9 H18 H10 H11. use_apart FP12. clear Hpix64.
    pose proof (u64_range ra) as Hrar.
    unfold M2x. eexists. split.
    - zv F_242cc D_242cc (Z_to_bv 64 (sp - 48)).           (* [comment removed for export] *)
      stf F_242d0 D_242d0 8%Z ra.                           (* [comment removed for export] *)
      stf F_242d4 D_242d4 16%Z s0v.                         (* [comment removed for export] *)
      stf F_242d8 D_242d8 24%Z s1v.                         (* [comment removed for export] *)
      stf F_242dc D_242dc 32%Z s2v.                         (* [comment removed for export] *)
      fold M1.
      stepb_ft F_242e0 D_242e0 ltac:(condZ).                (* [comment removed for export] *)
      zv F_242e4 D_242e4 (Z_to_bv 64 0).                    (* [comment removed for export] *)
      zv F_242e8 D_242e8 (Z_to_bv 64 pix).                  (* [comment removed for export] *)
      zv F_242ec D_242ec (Z_to_bv 64 (sp - 36)).           (* [comment removed for export] *)
      zv F_242f0 D_242f0 (Z_to_bv 64 (sp - 40)).           (* [comment removed for export] *)
      zv F_242f4 D_242f4 (Z_to_bv 64 (sp - 44)).           (* [comment removed for export] *)
      sn F_242f8 D_242f8.                                   (* [comment removed for export] *)
      (* [comment removed for export] *)
      andi_slot F_23e10 D_23e10 36%Z.                       (* [comment removed for export] *)
      stepb_ft F_23e14 D_23e14 ltac:(condZ).                (* [comment removed for export] *)
      stepb_ft F_23e18 D_23e18 ltac:(condZ).                (* [comment removed for export] *)
      stf F_23e1c D_23e1c 36%Z (Z_to_bv 64 0).              (* [comment removed for export] *)
      andi_slot F_23e20 D_23e20 40%Z.                       (* [comment removed for export] *)
      stepb_ft F_23e24 D_23e24 ltac:(condZ).                (* [comment removed for export] *)
      stepb_ft F_23e28 D_23e28 ltac:(condZ).                (* [comment removed for export] *)
      stf F_23e2c D_23e2c 40%Z (Z_to_bv 64 0).              (* [comment removed for export] *)
      andi_slot F_23e30 D_23e30 44%Z.                       (* [comment removed for export] *)
      stepb_ft F_23e34 D_23e34 ltac:(condZ).                (* [comment removed for export] *)
      stepb_ft F_23e38 D_23e38 ltac:(condZ).                (* [comment removed for export] *)
      stf F_23e3c D_23e3c 44%Z (Z_to_bv 64 0).              (* [comment removed for export] *)
      stepb_ft F_23e40 D_23e40 ltac:(condZ).                (* [comment removed for export] *)
      andi_pix F_23e44 D_23e44.                             (* [comment removed for export] *)
      stepb_ft F_23e48 D_23e48 ltac:(condZ).                (* [comment removed for export] *)
      sn F_23e4c D_23e4c.                                   (* [comment removed for export] *)
      stepb_ft F_23e50 D_23e50 ltac:(condZ).                (* [comment removed for export] *)
      ldpixg F_23e54 D_23e54 w Cw.                          (* [comment removed for export] *)
      stf F_23e58 D_23e58 36%Z (v_lw (Z_to_bv 64 w)).       (* [comment removed for export] *)
      stepb_ft F_23e5c D_23e5c ltac:(condZ).                (* [comment removed for export] *)
      sn F_23e60 D_23e60.                                   (* [comment removed for export] *)
      stepb_ft F_23e64 D_23e64 ltac:(condZ).                (* [comment removed for export] *)
      ldpixg F_23e68 D_23e68 h Ch.                          (* [comment removed for export] *)
      stf F_23e6c D_23e6c 40%Z (v_lw (Z_to_bv 64 h)).       (* [comment removed for export] *)
      stepb_ft F_23e70 D_23e70 ltac:(condZ).                (* [comment removed for export] *)
      sn F_23e74 D_23e74.                                   (* [comment removed for export] *)
      stepb_ft F_23e78 D_23e78 ltac:(condZ).                (* [comment removed for export] *)
      ldpix F_23e7c D_23e7c d Cd.                           (* [comment removed for export] *)
      stf F_23e80 D_23e80 44%Z (Z_to_bv 64 d).              (* [comment removed for export] *)
      sn F_23e84 D_23e84.                                   (* [comment removed for export] *)
      stepretF F_23e88 D_23e88 F_242fc. (* [comment removed for export] *)
      fold (M2g (v_lw (Z_to_bv 64 w)) (v_lw (Z_to_bv 64 h))).
      stepLD F_242fc D_242fc (word_to_le_bytes 4 (Z_to_bv 64 d)) (Z_to_bv 64 d)
        ltac:(unfold v_addi; unorm; unfold M2g; replace (Z_to_bv 64 (sp - 48 + 4)) with (Z_to_bv 64 (sp - 44)) by (f_equal; lia);
              apply (rdn_wbytes_hit SEGS (word_to_le_bytes 4 (Z_to_bv 64 d)));
              zlen; unorm; lia)
        ltac:(apply bytes_le_to_Z_4; unorm; lia).          (* [comment removed for export] *)
      rewrite (v_lw_small d) by lia.
      sn F_24300 D_24300.                                   (* [comment removed for export] *)
      stepb_ft F_24304 D_24304 ltac:(condZ).                (* [comment removed for export] *)
      sn F_24308 D_24308.                                   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Ltac ldf F D k z :=
    stepLD F D (word_to_le_bytes 4 (Z_to_bv 64 z)) (Z_to_bv 64 z)
      ltac:(unfold M2, M2g, M1; rdn_addr (sp - k)%Z; rdn_chain)
      ltac:(apply bytes_le_to_Z_4; unorm; lia);
    rewrite (v_lw_small z) by lia.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma pb_B : forall regs q r,
    (w * d = 32 * q + r)%Z -> (0 <= r < 32)%Z -> (d <> 24)%Z ->
    getr regs 2 = Z_to_bv 64 (sp - 48) -> getr regs 18 = Z_to_bv 64 pix ->
    getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 24 ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_242cc 0x2430c) M2 rom) (mkst regs' (rl dVL_242cc 0x243bc) M2 rom)
      /\ getr regs' 9 = Z_to_bv 64 data /\ getr regs' 10 = Z_to_bv 64 wpl
      /\ getr regs' 12 = Z_to_bv 64 (w * d) /\ getr regs' 11 = Z_to_bv 64 r
      /\ regs_agree (fun x : reg => In x [1; 9; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs q r Hqr Hr Hd24 H2 H18 H10 H11. use_apart FP.
    assert (Hwd : (0 <= w * d <= 20000 * 24)%Z).
    { split; [lia|]. apply Z.mul_le_mono_nonneg; lia. }
    eexists. split.
    - stepb_tk F_2430c D_2430c ltac:(condZ).                (* [comment removed for export] *)
      zv F_24388 D_24388 (Z_to_bv 64 pix).                  (* [comment removed for export] *)
      sn F_2438c D_2438c.                                   (* [comment removed for export] *)
      stepb_ft F_241e4 D_241e4 ltac:(condZ).                (* [comment removed for export] *)
      andi_pix F_241e8 D_241e8.                             (* [comment removed for export] *)
      stepb_ft F_241ec D_241ec ltac:(condZ).                (* [comment removed for export] *)
      stepLD F_241f0 D_241f0 (Z_to_le_bytes 8 data) (Z_to_bv 64 data)
        ltac:(unfold v_addi; unorm; peelf; exact Cdata)
        ltac:(apply lez8; lia).                             (* [comment removed for export] *)
      stepretF F_241f4 D_241f4 F_24390.
      zv F_24390 D_24390 (Z_to_bv 64 data).                 (* [comment removed for export] *)
      zv F_24394 D_24394 (Z_to_bv 64 pix).                  (* [comment removed for export] *)
      sn F_24398 D_24398.                                   (* [comment removed for export] *)
      stepb_ft F_23ce4 D_23ce4 ltac:(condZ).                (* [comment removed for export] *)
      andi_pix F_23ce8 D_23ce8.                             (* [comment removed for export] *)
      stepb_ft F_23cec D_23cec ltac:(condZ).                (* [comment removed for export] *)
      ldpix F_23cf0 D_23cf0 wpl Cwpl.                       (* [comment removed for export] *)
      stepretF F_23cf4 D_23cf4 F_2439c.
      ldf F_2439c D_2439c 36%Z w.                           (* [comment removed for export] *)
      ldf F_243a0 D_243a0 44%Z d.                           (* [comment removed for export] *)
      zv F_243a4 D_243a4 (Z_to_bv 64 (w * d)).              (* [comment removed for export] *)
      stepiv F_243a8 D_243a8 (Z_to_bv 64 0)
        ltac:(gres; pin; imm_norm; rewrite zbv_srai_small by lia; f_equal; apply Z.div_small; lia).  (* [comment removed for export] *)
      stepiv F_243ac D_243ac (Z_to_bv 64 0) ltac:(gres; pin; reflexivity).   (* [comment removed for export] *)
      zv F_243b0 D_243b0 (Z_to_bv 64 (w * d)).              (* [comment removed for export] *)
      stepiv F_243b4 D_243b4 (Z_to_bv 64 (32 * q))
        ltac:(gres; pin; imm_norm; rewrite andi_m32, (u_Z2bv (w * d)) by lia; f_equal;
              rewrite <- (Zmod_unique (w * d) 32 q r) by lia; lia).   (* [comment removed for export] *)
      zv F_243b8 D_243b8 (Z_to_bv 64 r).                    (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pb_C0 : forall regs,
    getr regs 11 = Z_to_bv 64 0 ->
    msteps SEGS (mkst regs (rl dVL_242cc 0x243bc) M2 rom) (mkst regs (rl dVL_242cc 0x2449c) M2 rom).
  Proof.
    intros regs H11.
    stepb_tk F_243bc D_243bc ltac:(condZ).
    apply mst_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma pb_C : forall regs q r,
    (w * d = 32 * q + r)%Z -> (1 <= r < 32)%Z ->
    getr regs 2 = Z_to_bv 64 (sp - 48) -> getr regs 9 = Z_to_bv 64 data -> getr regs 10 = Z_to_bv 64 wpl ->
    getr regs 12 = Z_to_bv 64 (w * d) -> getr regs 11 = Z_to_bv 64 r ->
    exists regs' (nm : word),
      msteps SEGS (mkst regs (rl dVL_242cc 0x243bc) M2 rom) (mkst regs' (rl dVL_242cc 0x2442c) M2 rom)
      /\ getr regs' 2 = Z_to_bv 64 (sp - 48) /\ getr regs' 9 = Z_to_bv 64 data
      /\ getr regs' 10 = Z_to_bv 64 wpl /\ getr regs' 11 = Z_to_bv 64 0
      /\ getr regs' 13 = Z_to_bv 64 1 /\ getr regs' 14 = Z_to_bv 64 (4 * q)
      /\ getr regs' 15 = nm /\ getr regs' 16 = Z_to_bv 64 0
      /\ regs_agree (fun x : reg => In x [11; 12; 13; 14; 15; 16]%list) regs regs'.
  Proof. rl_dbounds (dA_10a80 :: nil).
    intros regs q r Hqr Hr H2 H9 H10 H12 H11.
    assert (Hwd : (0 <= w * d <= 20000 * 24)%Z).
    { split; [lia|]. apply Z.mul_le_mono_nonneg; lia. }
    assert (Hq : (0 <= q <= 20000)%Z) by lia.
    destruct (rmask_read M2 (32 - r) ltac:(lia)) as (mb & Hmb & Lmb).
    eexists. eexists. split.
    - stepb_ft F_243bc D_243bc ltac:(condZ).                (* [comment removed for export] *)
      sn F_243c0 D_243c0.                                   (* [comment removed for export] *)
      zv F_243c4 D_243c4 (Z_to_bv 64 (32 - r)).             (* [comment removed for export] *)
      stepb_ft F_243c8 D_243c8 ltac:(condZ).                (* [comment removed for export] *)
      stepiv F_243cc D_243cc (Z_to_bv 64 (4 * (32 - r)))
        ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).  (* [comment removed for export] *)
      sn F_243d0 D_243d0.                                   (* [comment removed for export] *)
      sn F_243d4 D_243d4.                                   (* [comment removed for export] *)
      sn F_243d8 D_243d8.                                   (* [comment removed for export] *)
      stepb_ft F_243dc D_243dc ltac:(condZ).                (* [comment removed for export] *)
      ldf F_243e0 D_243e0 40%Z h.                           (* [comment removed for export] *)
      stepb_ft F_243e4 D_243e4 ltac:(condZ).                (* [comment removed for export] *)
      sn F_243e8 D_243e8.                                   (* [comment removed for export] *)
      stepiv F_243ec D_243ec (Z_to_bv 64 q)
        ltac:(gres; pin; imm_norm; rewrite zbv_srai_small by lia; f_equal; change (2 ^ 5)%Z with 32%Z;
              symmetry; apply (Zdiv_unique (w * d) 32 q r); lia).    (* [comment removed for export] *)
      zv F_243f0 D_243f0 (Z_to_bv 64 ((0x10a80 + dA_10a80) + 4 * (32 - r))).   (* [comment removed for export] *)
      stepLD F_243f4 D_243f4 mb (Z_to_bv 64 (bytes_le_to_Z mb))
        ltac:(rdn_addr ((0x10a80 + dA_10a80) + 4 * (32 - r))%Z; exact Hmb)
        ltac:(symmetry; apply u_lez4; exact Lmb).          (* [comment removed for export] *)
      stepat F_243f8 D_243f8 (Z_to_bv 64 1)
        ltac:(gres; pin; rewrite v_sltu_Z by lia; rewrite Zltb_t by lia; reflexivity).   (* [comment removed for export] *)
      stepiv F_243fc D_243fc (Z_to_bv 64 q)
        ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; f_equal; lia).   (* [comment removed for export] *)
      stepiv F_24400 D_24400 (Z_to_bv 64 (4 * q))
        ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).  (* [comment removed for export] *)
      sn F_24404 D_24404.                                   (* [comment removed for export] *)
      stepat F_24408 D_24408 (Z_to_bv 64 0)
        ltac:(gres; pin; imm_norm; rewrite v_slti_Z by lia; rewrite Zltb_f by lia; reflexivity).   (* [comment removed for export] *)
      sn F_2440c D_2440c.                                   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[local] Notation RS := (4 * (wpl * h))%Z (only parsing).

  Definition Inv (Mi : word -> option byte) : Prop :=
    (forall x : word, (bv_unsigned x < data \/ data + RS <= bv_unsigned x)%Z -> Mi x = M2 x)
    /\ mem_grows M2 Mi.

  Lemma Inv_M2 : Inv M2.
  Proof. split; [intros; reflexivity | apply mem_grows_refl]. Qed.
  Lemma M2g_grows : forall vw vh, mem_grows M (M2g vw vh).
  Proof. intros. unfold M2g, M1. grows. Qed.
  Lemma M2_grows : mem_grows M M2.
  Proof. apply M2g_grows. Qed.

  Lemma Inv_store : forall Mi (a : Z) (bs : list byte),
    Inv Mi -> (data <= a)%Z -> (a + Z.of_nat (length bs) <= data + RS)%Z ->
    Inv (wbytes Mi (Z_to_bv 64 a) bs).
  Proof.
    intros Mi a bs [HI HG] Ha Hb. destruct bs as [|b0 bs']; [split; [exact HI | exact HG]|].
    cbn [length] in Hb. split.
    - intros x Hx. rewrite wbytes_outside by (cbn [length]; rewrite u_Z2bv by lia; lia). apply HI, Hx.
    - eapply mem_grows_trans; [exact HG | apply wbytes_grows].
  Qed.

  Definition FrameSame (vw vh : word) (Mx : word -> option byte) : Prop :=
    forall x : word, (sp - 48 <= bv_unsigned x < sp)%Z -> Mx x = M2g vw vh x.

  Lemma Inv_FrameSame : forall Mi, Inv Mi -> FrameSame (Z_to_bv 64 w) (Z_to_bv 64 h) Mi.
  Proof. use_apart FR. intros Mi [HI _] x Hx. unfold M2 in HI. apply HI. lia. Qed.

  Lemma FS_rdn_frame : forall vw vh Mx k (n : nat) bs,
    FrameSame vw vh Mx -> (Z.of_nat n <= k <= 48)%Z ->
    rdn SEGS (M2g vw vh) (Z_to_bv 64 (sp - k)) n = Some bs -> rdn SEGS Mx (Z_to_bv 64 (sp - k)) n = Some bs.
  Proof.
    intros vw vh Mx k n bs HF Hk HM2. rewrite <- HM2. apply rdn_ext; rewrite u_Z2bv by lia; [lia|].
    intros x Hx. apply HF. lia.
  Qed.

  Lemma Inv_rdn_frame : forall Mi k (n : nat) bs,
    Inv Mi -> (Z.of_nat n <= k <= 48)%Z ->
    rdn SEGS M2 (Z_to_bv 64 (sp - k)) n = Some bs -> rdn SEGS Mi (Z_to_bv 64 (sp - k)) n = Some bs.
  Proof. intros Mi k n bs HIv. unfold M2. apply FS_rdn_frame, Inv_FrameSame, HIv. Qed.

  Lemma Inv_sok : forall Mi (a : Z) (n : nat),
    Inv Mi -> (data <= a)%Z -> (a + Z.of_nat n <= data + RS)%Z ->
    store_ok SEGS Mi (Z_to_bv 64 a) n = true.
  Proof.
    intros Mi a n [_ HG] Ha Hn. eapply store_ok_mono; [exact HG|]. eapply store_ok_mono; [apply M2_grows|].
    destruct n as [|n']; [reflexivity|].
    eapply (store_ok_sub SEGS M (Z_to_bv 64 data) _ (Z.to_nat RS)); [ | exact SOKr | | ];
      rewrite ?u_Z2bv by lia; lia.
  Qed.

  Lemma Inv_rdn_raster : forall Mi (a : Z),
    Inv Mi -> (data <= a)%Z -> (a + 4 <= data + RS)%Z ->
    exists bs, rdn SEGS Mi (Z_to_bv 64 a) 4 = Some bs /\ length bs = 4%nat.
  Proof.
    intros Mi a HIv Ha H4. apply (store_ok_rdn SEGS Mi 4 _ wr_readable_u16). apply Inv_sok; cbn; try lia. exact HIv.
  Qed.

  (* [comment removed for export] *)
  Lemma pb_iter : forall regs Mi (i q : Z) (nm : word),
    (0 <= i < h)%Z -> (0 <= q < wpl)%Z ->
    getr regs 2 = Z_to_bv 64 (sp - 48) -> getr regs 8 = Z_to_bv 64 0 -> getr regs 9 = Z_to_bv 64 data ->
    getr regs 10 = Z_to_bv 64 wpl -> getr regs 11 = Z_to_bv 64 i -> getr regs 13 = Z_to_bv 64 1 ->
    getr regs 14 = Z_to_bv 64 (4 * q) -> getr regs 15 = nm -> getr regs 16 = Z_to_bv 64 0 ->
    Inv Mi ->
    exists regs' M',
      msteps SEGS (mkst regs (rl dVL_242cc 0x2442c) Mi rom) (mkst regs' (rl dVL_242cc 0x24428) M' rom)
      /\ Inv M'
      /\ getr regs' 2 = Z_to_bv 64 (sp - 48) /\ getr regs' 8 = Z_to_bv 64 0 /\ getr regs' 9 = Z_to_bv 64 data
      /\ getr regs' 10 = Z_to_bv 64 wpl /\ getr regs' 11 = Z_to_bv 64 (i + 1) /\ getr regs' 13 = Z_to_bv 64 1
      /\ getr regs' 14 = Z_to_bv 64 (4 * q) /\ getr regs' 15 = nm /\ getr regs' 16 = Z_to_bv 64 0
      /\ getr regs' 17 = Z_to_bv 64 h
      /\ regs_agree (fun x : reg => In x [5; 6; 11; 17]%list) regs regs'.
  Proof.
    intros regs Mi i q nm Hi Hq H2 H8 H9 H10 H11 H13 H14 H15 H16 HIv. use_apart FR.
    assert (Hiw : (0 <= wpl * i /\ wpl * i <= wpl * (h - 1))%Z).
    { split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_l; lia]. }
    assert (Hwh : (wpl * (h - 1) <= 20000 * 20000)%Z).
    { apply Z.le_trans with (m := (wpl * 20000)%Z); [apply Z.mul_le_mono_nonneg_l; lia | apply Z.mul_le_mono_nonneg_r; lia]. }
    assert (Hrow : (4 * q + 4 * (i * wpl) + 4 <= RS)%Z) by lia.
    assert (ALp : ((data + 4 * (i * wpl) + 4 * q) mod 4 = 0)%Z).
    { pose proof ALdata as AL. use_aligned AL.
      apply mod0_add; [lia | apply mod0_add; [lia | exact AL | apply mod0_mul_l; [lia|reflexivity]] | apply mod0_mul_l; [lia|reflexivity]]. }
    destruct (Inv_rdn_raster Mi (data + 4 * (i * wpl) + 4 * q) HIv ltac:(lia) ltac:(lia)) as (bs & Hbs & Lbs).
    eexists. eexists. split; [|split].
    - zv F_2442c D_2442c (Z_to_bv 64 (i * wpl)).           (* [comment removed for export] *)
      stepat F_24430 D_24430 (Z_to_bv 64 (i * wpl))
        ltac:(gres; pin; rewrite zbv_mulw_small by lia; reflexivity).   (* [comment removed for export] *)
      stepb_ft F_24434 D_24434 ltac:(condZ).                (* [comment removed for export] *)
      stepiv F_24438 D_24438 (Z_to_bv 64 (i * wpl))
        ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; f_equal; lia).   (* [comment removed for export] *)
      stepiv F_2443c D_2443c (Z_to_bv 64 (4 * (i * wpl)))
        ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).  (* [comment removed for export] *)
      zv F_24440 D_24440 (Z_to_bv 64 (data + 4 * (i * wpl))).   (* [comment removed for export] *)
      stepiv F_24444 D_24444 (Z_to_bv 64 0)
        ltac:(gres; pin; imm_norm; rewrite v_sltiu_Z by lia; rewrite Zltb_f by lia; reflexivity).   (* [comment removed for export] *)
      stepb_ft F_24448 D_24448 ltac:(condZ).                (* [comment removed for export] *)
      stepat F_2444c D_2444c (Z_to_bv 64 0)
        ltac:(gres; pin; rewrite v_sltu_Z by lia; rewrite Zltb_f by lia; reflexivity).   (* [comment removed for export] *)
      stepat F_24450 D_24450 (Z_to_bv 64 0)
        ltac:(gres; pin; imm_norm; rewrite v_slti_Z by lia; rewrite Zltb_f by lia; reflexivity).   (* [comment removed for export] *)
      sn F_24454 D_24454.                                   (* [comment removed for export] *)
      sn F_24458 D_24458.                                   (* [comment removed for export] *)
      stepb_ft F_2445c D_2445c ltac:(condZ).                (* [comment removed for export] *)
      zv F_24460 D_24460 (Z_to_bv 64 (data + 4 * (i * wpl) + 4 * q)).   (* [comment removed for export] *)
      stepiv F_24464 D_24464 (Z_to_bv 64 0)
        ltac:(gres; pin; imm_norm; rewrite v_sltiu_Z by lia; rewrite Zltb_f by lia; reflexivity).   (* [comment removed for export] *)
      stepb_ft F_24468 D_24468 ltac:(condZ).                (* [comment removed for export] *)
      stepat F_2446c D_2446c (Z_to_bv 64 0)
        ltac:(gres; pin; rewrite v_sltu_Z by lia; rewrite Zltb_f by lia; reflexivity).   (* [comment removed for export] *)
      sn F_24470 D_24470.                                   (* [comment removed for export] *)
      sn F_24474 D_24474.                                   (* [comment removed for export] *)
      stepb_ft F_24478 D_24478 ltac:(condZ).                (* [comment removed for export] *)
      stepiv F_2447c D_2447c (Z_to_bv 64 0)
        ltac:(gres; pin; imm_norm; rewrite andi_3, u_Z2bv by lia; rewrite ALp; reflexivity).   (* [comment removed for export] *)
      sn F_24480 D_24480.                                   (* [comment removed for export] *)
      sn F_24484 D_24484.                                   (* [comment removed for export] *)
      stepb_ft F_24488 D_24488 ltac:(condZ).                (* [comment removed for export] *)
      stepb_ft F_2448c D_2448c ltac:(condZ).                (* [comment removed for export] *)
      stepLD F_24490 D_24490 bs (Z_to_bv 64 (bytes_le_to_Z bs))
        ltac:(rdn_addr (data + 4 * (i * wpl) + 4 * q)%Z; exact Hbs)
        ltac:(symmetry; apply u_lez4; exact Lbs).          (* [comment removed for export] *)
      sn F_24494 D_24494.                                   (* [comment removed for export] *)
      sn F_24498 D_24498.                                   (* [comment removed for export] *)
      stepST F_2441c D_2441c (Z_to_bv 64 (data + 4 * (i * wpl) + 4 * q))
        (v_and (v_lw (Z_to_bv 64 (bytes_le_to_Z bs))) nm)
        ltac:(apply Inv_sok; [exact HIv | lia | cbn; lia]).   (* [comment removed for export] *)
      stepLD F_24420 D_24420 (word_to_le_bytes 4 (Z_to_bv 64 h)) (Z_to_bv 64 h)
        ltac:(rdn_addr (sp - 40)%Z; rewrite rdn_wbytes_out_Z by (zlen; lia);
              apply (Inv_rdn_frame Mi 40 4); [exact HIv | cbn; lia | unfold M2, M2g, M1; rdn_chain])
        ltac:(apply bytes_le_to_Z_4; unorm; lia).          (* [comment removed for export] *)
      rewrite (v_lw_small h) by lia.
      stepiv F_24424 D_24424 (Z_to_bv 64 (i + 1))
        ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).   (* [comment removed for export] *)
      apply mst_refl.
    - apply Inv_store; [exact HIv | lia | zlen; lia].
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma pb_loop : forall (k : nat) regs Mi (i q : Z) (nm : word),
    (Z.of_nat k = h - 1 - i)%Z -> (0 <= i)%Z -> (0 <= q < wpl)%Z ->
    getr regs 2 = Z_to_bv 64 (sp - 48) -> getr regs 8 = Z_to_bv 64 0 -> getr regs 9 = Z_to_bv 64 data ->
    getr regs 10 = Z_to_bv 64 wpl -> getr regs 11 = Z_to_bv 64 i -> getr regs 13 = Z_to_bv 64 1 ->
    getr regs 14 = Z_to_bv 64 (4 * q) -> getr regs 15 = nm -> getr regs 16 = Z_to_bv 64 0 ->
    Inv Mi ->
    exists regs' M',
      msteps SEGS (mkst regs (rl dVL_242cc 0x2442c) Mi rom) (mkst regs' (rl dVL_242cc 0x2449c) M' rom)
      /\ Inv M' /\ getr regs' 2 = Z_to_bv 64 (sp - 48)
      /\ regs_agree (fun x : reg => In x [5; 6; 11; 17]%list) regs regs'.
  Proof.
    induction k as [|k IH]; intros regs Mi i q nm Hk Hi Hq H2 H8 H9 H10 H11 H13 H14 H15 H16 HIv;
      destruct (pb_iter regs Mi i q nm ltac:(lia) Hq H2 H8 H9 H10 H11 H13 H14 H15 H16 HIv)
        as (r1 & M1' & S1 & HI1 & R2 & R8 & R9 & R10 & R11 & R13 & R14 & R15 & R16 & R17 & AG1).
    - exists r1, M1'. split; [|split; [exact HI1 | split; [exact R2 | exact AG1]]].
      eapply msteps_trans; [exact S1|].
      stepb_tk F_24428 D_24428 ltac:(condZ).                (* [comment removed for export] *)
      apply mst_refl.
    - destruct (IH r1 M1' (i + 1)%Z q nm ltac:(lia) ltac:(lia) Hq R2 R8 R9 R10 R11 R13 R14 R15 R16 HI1)
        as (r2 & M' & S2 & HI2 & Q2 & AG2).
      exists r2, M'. split; [|split; [exact HI2 | split; [exact Q2 | eapply regs_agree_trans; eassumption]]].
      eapply msteps_trans; [exact S1|].
      stepb_ft F_24428 D_24428 ltac:(condZ).                (* [comment removed for export] *)
      exact S2.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma pb_E' : forall vw vh regs Mx,
    FrameSame vw vh Mx -> getr regs 2 = Z_to_bv 64 (sp - 48) ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_242cc 0x244a0) Mx rom) (mkst regs' ra Mx rom)
      /\ getr regs' 10 = getr regs 10 /\ getr regs' 1 = ra /\ getr regs' 2 = Z_to_bv 64 sp
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v
      /\ regs_agree (fun x : reg => In x [1; 2; 8; 9; 18]%list) regs regs'.
  Proof.
    intros vw vh regs Mx HF H2.
    pose proof (u64_range ra). pose proof (u64_range s0v). pose proof (u64_range s1v). pose proof (u64_range s2v).
    eexists. split.
    - stepLD F_244a0 D_244a0 (word_to_le_bytes 8 ra) ra
        ltac:(rdn_addr (sp - 8)%Z; apply (FS_rdn_frame vw vh Mx 8 8); [exact HF | cbn; lia | unfold M2g, M1; rdn_chain])
        ltac:(apply bytes_le_to_Z_8).                      (* [comment removed for export] *)
      stepLD F_244a4 D_244a4 (word_to_le_bytes 8 s0v) s0v
        ltac:(rdn_addr (sp - 16)%Z; apply (FS_rdn_frame vw vh Mx 16 8); [exact HF | cbn; lia | unfold M2g, M1; rdn_chain])
        ltac:(apply bytes_le_to_Z_8).                      (* [comment removed for export] *)
      stepLD F_244a8 D_244a8 (word_to_le_bytes 8 s1v) s1v
        ltac:(rdn_addr (sp - 24)%Z; apply (FS_rdn_frame vw vh Mx 24 8); [exact HF | cbn; lia | unfold M2g, M1; rdn_chain])
        ltac:(apply bytes_le_to_Z_8).                      (* [comment removed for export] *)
      stepLD F_244ac D_244ac (word_to_le_bytes 8 s2v) s2v
        ltac:(rdn_addr (sp - 32)%Z; apply (FS_rdn_frame vw vh Mx 32 8); [exact HF | cbn; lia | unfold M2g, M1; rdn_chain])
        ltac:(apply bytes_le_to_Z_8).                      (* [comment removed for export] *)
      zv F_244b0 D_244b0 (Z_to_bv 64 sp).                   (* [comment removed for export] *)
      stepret F_244b4 D_244b4 ra ltac:(reflexivity).        (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma pb_E : forall regs Mx,
    Inv Mx -> getr regs 2 = Z_to_bv 64 (sp - 48) ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_242cc 0x2449c) Mx rom) (mkst regs' ra Mx rom)
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 1 = ra /\ getr regs' 2 = Z_to_bv 64 sp
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v
      /\ regs_agree (fun x : reg => In x [1; 2; 8; 9; 10; 18]%list) regs regs'.
  Proof.
    intros regs Mx HIv H2.
    destruct (pb_E' _ _ (regupd regs 10 (Z_to_bv 64 0)) Mx (Inv_FrameSame Mx HIv) ltac:(gres; exact H2))
      as (r1 & S1 & E10 & E1 & E2 & E8 & E9 & E18 & AG1).
    exists r1. split.
    - sn F_2449c D_2449c.                                   (* [comment removed for export] *)
      exact S1.
    - rewrite E10. repeat split; gres; try reflexivity; try assumption.
      eapply regs_agree_trans; [|regs_agree_weaken AG1]. solve_regs_agree.
  Qed.

  Lemma M2g_outside : forall vw vh (x : word),
    (bv_unsigned x < sp - 48 \/ sp <= bv_unsigned x)%Z -> M2g vw vh x = M x.
  Proof.
    intros vw vh x Hx. unfold M2g, M1.
    rewrite !wbytes_outside by (zlen; rewrite ?u_Z2bv by lia; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem padbits_run : forall regs,
    (d <> 24)%Z -> (wpl = (w * d + 31) / 32)%Z ->
    getr regs 1 = ra -> getr regs 2 = Z_to_bv 64 sp -> getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v ->
    getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 0 ->
    exists regs' M',
      msteps SEGS (mkst regs (rl dVL_242cc 0x242cc) M rom) (mkst regs' ra M' rom)
      /\ Inv M'
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 sp
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v
      /\ regs_agree (fun x : reg => In x [1; 2; 5; 6; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18]%list) regs regs'.
  Proof.
    intros regs Hd24 Hwpl' H1 H2 H8 H9 H18 H10 H11.
    assert (Hwd : (0 <= w * d <= 20000 * 24)%Z).
    { split; [lia|]. apply Z.mul_le_mono_nonneg; lia. }
    set (q := ((w * d) / 32)%Z). set (r := ((w * d) mod 32)%Z).
    assert (Hqr : (w * d = 32 * q + r)%Z) by (apply Z.div_mod; lia).
    assert (Hr : (0 <= r < 32)%Z) by (apply Z.mod_pos_bound; lia).
    clearbody q r.
    destruct (pb_A regs H1 H2 H8 H9 H18 H10 H11) as (r1 & S1 & A2 & A18 & A8 & A10 & A11 & AG1).
    rewrite M2x_M2 in S1.
    destruct (pb_B r1 q r Hqr Hr Hd24 A2 A18 A10 A11) as (r2 & S2 & B9 & B10 & B12 & B11 & AG2).
    pose proof (AG2 2 ltac:(notin_list)) as B2. rewrite A2 in B2.
    pose proof (AG2 8 ltac:(notin_list)) as B8. rewrite A8 in B8.
    destruct (Z.eq_dec r 0) as [Hr0|Hr0].
    - rewrite Hr0 in B11.
      destruct (pb_E r2 M2 Inv_M2 B2) as (r3 & S3 & E10 & E1 & E2 & E8 & E9 & E18 & AG3).
      exists r3, M2. split.
      + eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2|].
        eapply msteps_trans; [apply (pb_C0 r2 B11) | exact S3].
      + split; [exact Inv_M2|]. repeat split; try assumption.
        eapply regs_agree_trans; [regs_agree_weaken AG1|].
        eapply regs_agree_trans; [regs_agree_weaken AG2|]. regs_agree_weaken AG3.
    - assert (Hq : (0 <= q < wpl)%Z).
      { subst wpl. rewrite Hqr. replace (32 * q + r + 31)%Z with ((q + 1) * 32 + (r - 1))%Z by lia.
        rewrite Z.div_add_l by lia. rewrite (Z.div_small (r - 1) 32) by lia. lia. }
      destruct (pb_C r2 q r Hqr ltac:(lia) B2 B9 B10 B12 B11) as (r3 & nm & S3 & C2 & C9 & C10 & C11 & C13 & C14 & C15 & C16 & AG3).
      pose proof (AG3 8 ltac:(notin_list)) as C8. rewrite B8 in C8.
      destruct (pb_loop (Z.to_nat (h - 1)) r3 M2 0 q nm ltac:(lia) ltac:(lia) Hq C2 C8 C9 C10 C11 C13 C14 C15 C16 Inv_M2)
        as (r4 & M4 & S4 & HI4 & D2 & AG4).
      destruct (pb_E r4 M4 HI4 D2) as (r5 & S5 & E10 & E1 & E2 & E8 & E9 & E18 & AG5).
      exists r5, M4. split.
      + eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2|].
        eapply msteps_trans; [exact S3|]. eapply msteps_trans; [exact S4 | exact S5].
      + split; [exact HI4|]. repeat split; try assumption.
        eapply regs_agree_trans; [regs_agree_weaken AG1|].
        eapply regs_agree_trans; [regs_agree_weaken AG2|].
        eapply regs_agree_trans; [regs_agree_weaken AG3|].
        eapply regs_agree_trans; [regs_agree_weaken AG4|]. regs_agree_weaken AG5.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable L : SSP.ls_addrs.
  Variable sv : Z.                                 (* [comment removed for export] *)
  Hypothesis HLe : SSP.ls_entry L = (0x13694 + dF_13694)%Z.
  Hypothesis HLsg : SSP.ls_sev_got L = (0x1e3b0 + dA_1e3a0)%Z.
  Hypothesis HLfmt : In (0x10591 + dVLS_10591)%Z (SSP.ls_fmts1 L).
  Hypothesis HLimg : (0 <= SSP.ls_img_lo L /\ SSP.ls_img_lo L <= (0x10591 + dVLS_10591) /\ SSP.ls_img_lo L <= (0x10693 + dVLS_10693) /\ (0x10591 + dVLS_10591) + 216 <= SSP.ls_img_hi L /\ (0x10693 + dVLS_10693) + 216 <= SSP.ls_img_hi L /\ SSP.ls_img_hi L <= SSP.ls_sp_lo L)%Z.
  Hypothesis HLfr : (0 <= SSP.ls_frame L)%Z.
  #[local] Notation LSF := (SSP.ls_frame L) (only parsing).
  Hypothesis Csg : rdn SEGS M (rl dA_1e3a0 0x1e3b0) 8 = Some (Z_to_le_bytes 8 (SSP.ls_sev L)).
  Hypothesis Rsev : (0 <= SSP.ls_sev L /\ SSP.ls_sev L + 4 <= 2 ^ 64)%Z.
  Hypothesis Csv : rdn SEGS M (Z_to_bv 64 (SSP.ls_sev L)) 4 = Some (Z_to_le_bytes 4 sv).
  Hypothesis Rsv : (0 <= sv < 2 ^ 32)%Z.
  Hypothesis IMG : forall i, (SSP.ls_img_lo L <= i < SSP.ls_img_hi L)%Z -> M (Z_to_bv 64 i) = None.
  Hypothesis SPR : (SSP.ls_sp_lo L + (48 + LSF) <= sp <= SSP.ls_sp_hi L)%Z.

  (* [comment removed for export] *)
  Lemma pb_D1 : forall regs, (d = 24)%Z ->
    ((0x1e3b8 + dA_1e3a0) <= sp - 48 \/ sp <= (0x1e3b0 + dA_1e3a0))%Z -> (SSP.ls_sev L + 4 <= sp - 48 \/ sp <= SSP.ls_sev L)%Z ->
    getr regs 2 = Z_to_bv 64 (sp - 48) -> getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 24 ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_242cc 0x2430c) M2x rom) (mkst regs' (rl dVL_242cc 0x24324) M2x rom)
      /\ getr regs' 2 = Z_to_bv 64 (sp - 48) /\ getr regs' 10 = Z_to_bv 64 1
      /\ getr regs' 11 = v_lw (Z_to_bv 64 sv) /\ getr regs' 12 = Z_to_bv 64 3
      /\ regs_agree (fun x : reg => In x [10; 11; 12]%list) regs regs'.
  Proof. rl_dbounds (dA_1e3a0 :: nil).
    intros regs Hd24 Fsg Fsv H2 H10 H11.
    eexists. split.
    - stepb_ft F_2430c D_2430c ltac:(condZ).                (* [comment removed for export] *)
      sn F_24310 D_24310.                                   (* [comment removed for export] *)
      stepLD F_24314 D_24314 (Z_to_le_bytes 8 (SSP.ls_sev L)) (Z_to_bv 64 (SSP.ls_sev L))
        ltac:(rdn_addr (0x1e3b0 + dA_1e3a0)%Z; peelf; exact Csg)
        ltac:(apply lez8; lia).                             (* [comment removed for export] *)
      stepLD F_24318 D_24318 (Z_to_le_bytes 4 sv) (Z_to_bv 64 sv)
        ltac:(rdn_addr (SSP.ls_sev L); peelf; exact Csv)
        ltac:(apply lez4; lia).                             (* [comment removed for export] *)
      sn F_2431c D_2431c.                                   (* [comment removed for export] *)
      sn F_24320 D_24320.                                   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pb_D2 : forall regs,
    getr regs 11 = v_lw (Z_to_bv 64 sv) -> getr regs 12 = Z_to_bv 64 3 ->
    c_lts (Z_to_bv 64 3) (v_lw (Z_to_bv 64 sv)) = false ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_242cc 0x24324) M2x rom) (mkst regs' (rl dF_13694 0x13694) M2x rom)
      /\ getr regs' 1 = rl dVL_242cc 0x2433c /\ getr regs' 10 = rl dVLS_10591 0x10591 /\ getr regs' 11 = rl dVLS_10693 0x10693
      /\ regs_agree (fun x : reg => In x [1; 10; 11]%list) regs regs'.
  Proof. rl_dbounds (dF_13694 :: dVLS_10591 :: dVLS_10693 :: nil).
    intros regs H11 H12 Hc.
    eexists. split.
    - stepb_ft F_24324 D_24324 ltac:(pin; exact Hc).        (* [comment removed for export] *)
      sn F_24328 D_24328.                                   (* [comment removed for export] *)
      sn F_2432c D_2432c.                                   (* [comment removed for export] *)
      sn F_24330 D_24330.                                   (* [comment removed for export] *)
      sn F_24334 D_24334.                                   (* [comment removed for export] *)
      sn F_24338 D_24338.                                   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pb_D3 : forall regs Mx,
    exists regs',
      msteps SEGS (mkst regs (rl dVL_242cc 0x2433c) Mx rom) (mkst regs' (rl dVL_242cc 0x244a0) Mx rom)
      /\ getr regs' 10 = Z_to_bv 64 1
      /\ regs_agree (fun x : reg => In x [10]%list) regs regs'.
  Proof.
    intros regs Mx. eexists. split.
    - sn F_2433c D_2433c.                                   (* [comment removed for export] *)
      sn F_24380 D_24380.                                   (* [comment removed for export] *)
      sn F_24384 D_24384.                                   (* [comment removed for export] *)
      apply mst_refl.
    - split; [gres; reflexivity | solve_regs_agree].
  Qed.

  Lemma M2x_img_none : forall i, (SSP.ls_img_lo L <= i < SSP.ls_img_hi L)%Z -> M2x (Z_to_bv 64 i) = None.
  Proof.
    intros i Hi. unfold M2x, M2g, M1.
    rewrite !wbytes_outside by (zlen; rewrite ?u_Z2bv by lia; lia). apply IMG. exact Hi.
  Qed.

  Ltac rostr_win_eval :=
    match goal with |- context [SSP.rostr_win ?a ?k] =>
      let v := eval vm_compute in (SSP.rostr_win a k) in change (SSP.rostr_win a k) with v end.

  Lemma rostr_fmt : SSP.rostr SEGS M2x (0x10591 + dVLS_10591) 26.
  Proof.
    assert (HS : str_okP (0x10591 + dVLS_10591) 26) by rl_str_tac_VL.
    destruct HS as (HSc & HSk & HSa & HSw). pose proof (rostr_win_bd (0x10591 + dVLS_10591) 26) as HSwin. pose proof rl_pages as HSpg.
    apply rostr_intro; [lia | unfold SSP.flatZ; lia | exact HSc |].
    intros i Hi. apply M2x_img_none. lia.
  Qed.

  Lemma rostr_func : SSP.rostr SEGS M2x (0x10693 + dVLS_10693) 13.
  Proof.
    assert (HS : str_okP (0x10693 + dVLS_10693) 13) by rl_str_tac_VL.
    destruct HS as (HSc & HSk & HSa & HSw). pose proof (rostr_win_bd (0x10693 + dVLS_10693) 13) as HSwin. pose proof rl_pages as HSpg.
    apply rostr_intro; [lia | unfold SSP.flatZ; lia | exact HSc |].
    intros i Hi. apply M2x_img_none. lia.
  Qed.

  Lemma cell_lift : forall a (n : nat) v,
    SSP.cell_holds SEGS M a n v -> (0 <= a < 2 ^ 64)%Z -> (a + Z.of_nat n <= sp - 48 \/ sp <= a)%Z -> (a + Z.of_nat n <= 2 ^ 64)%Z ->
    SSP.cell_holds SEGS M2x a n v.
  Proof.
    intros a n v [Hv Hr] Ha Hapart Hnw. split; [exact Hv|]. rewrite <- Hr.
    apply rdn_ext; rewrite u_Z2bv by lia; [lia|]. intros x Hx. unfold M2x. apply M2g_outside. lia.
  Qed.

  Lemma M2x_grows : mem_grows M M2x.
  Proof. unfold M2x. apply M2g_grows. Qed.

  Lemma sp48_al16 : ((sp - 48) mod 16 = 0)%Z.
  Proof.
    pose proof ALsp as H16. use_aligned H16. apply Z.mod_divide in H16; [|lia]. destruct H16 as [c Hc].
    apply Z.mod_divide; [lia|]. exists (c - 3)%Z. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pb_D : forall regs hv cg cv, (d = 24)%Z ->
    ((0x1e3b8 + dA_1e3a0) <= sp - 48 \/ sp <= (0x1e3b0 + dA_1e3a0))%Z -> (SSP.ls_sev L + 4 <= sp - 48 \/ sp <= SSP.ls_sev L)%Z ->
    SSP.flatZ (SSP.ls_handler_cell L + 0) (Z.of_nat 8) -> SSP.cell_holds SEGS M (SSP.ls_handler_cell L + 0) 8 hv ->
    hv = SSP.ls_devnull L ->
    SSP.flatZ (SSP.ls_canary_got L + 0) (Z.of_nat 8) -> SSP.cell_holds SEGS M (SSP.ls_canary_got L + 0) 8 cg ->
    cg = SSP.ls_canary L ->
    SSP.flatZ (SSP.ls_canary L + 0) (Z.of_nat 8) -> SSP.cell_holds SEGS M (SSP.ls_canary L + 0) 8 cv ->
    (SSP.ls_handler_cell L + 0 + Z.of_nat 8 <= sp - (48 + LSF) \/ sp <= SSP.ls_handler_cell L + 0)%Z ->
    (SSP.ls_canary_got L + 0 + Z.of_nat 8 <= sp - (48 + LSF) \/ sp <= SSP.ls_canary_got L + 0)%Z ->
    (SSP.ls_canary L + 0 + Z.of_nat 8 <= sp - (48 + LSF) \/ sp <= SSP.ls_canary L + 0)%Z ->
    store_ok SEGS M (Z_to_bv 64 (sp - (48 + LSF))) (Z.to_nat (48 + LSF)) = true ->
    SSP.sum_contract SEGS (SSP.spec_lept_stderr_s1 L) ->
    getr regs 2 = Z_to_bv 64 (sp - 48) -> getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 24 ->
    exists regs' M',
      msteps SEGS (mkst regs (rl dVL_242cc 0x2430c) M2x rom) (mkst regs' ra M' rom)
      /\ (forall x : word, (bv_unsigned x < sp - (48 + LSF) \/ sp - 48 <= bv_unsigned x)%Z -> M' x = M2x x)
      /\ mem_grows M2x M'
      /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 1 = ra /\ getr regs' 2 = Z_to_bv 64 sp
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v
      /\ regs_agree (fun x : reg => In x [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 28; 29; 30; 31]%list) regs regs'.
  Proof. rl_dbounds (dA_1e3a0 :: dVLS_10591 :: dVLS_10693 :: nil).
    intros regs hv cg cv Hd24 Fsg Fsv Fl1 C1 E1 Fl2 C2 E2 Fl3 C3 A1 A2 A3 SOKF HC H2 H10 H11.
   
    destruct (pb_D1 regs Hd24 Fsg Fsv H2 H10 H11) as (r1 & S1 & B2 & B10 & B11 & B12 & AG1).
    destruct (c_lts (Z_to_bv 64 3) (v_lw (Z_to_bv 64 sv))) eqn:Hsev.
    - (* [comment removed for export] *)
      destruct (pb_E' (v_lw (Z_to_bv 64 w)) (v_lw (Z_to_bv 64 h)) r1 M2x ltac:(intros x Hx; reflexivity) B2)
        as (r2 & S2 & C10 & C1r & C2r & C8 & C9 & C18 & AG2).
      exists r2, M2x. split.
      + eapply msteps_trans; [exact S1|].
        stepb_tk F_24324 D_24324 ltac:(pin; exact Hsev).     (* [comment removed for export] *)
        exact S2.
      + split; [intros; reflexivity|]. split; [apply mem_grows_refl|].
        rewrite B10 in C10. repeat split; try assumption.
        eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2].
    - (* [comment removed for export] *)
      destruct (pb_D2 r1 B11 B12 Hsev) as (r2 & S2 & C1r & C10 & C11 & AG2).
      pose proof (AG2 2 ltac:(notin_list)) as C2r. rewrite B2 in C2r.
      assert (PRE : SSP.spec_pre SEGS (SSP.spec_lept_stderr_s1 L) [(0x10591 + dVLS_10591); (0x10693 + dVLS_10693); hv; cg; cv]%Z r2 M2x).
      { unfold SSP.spec_lept_stderr_s1. SSP.spec_unfold. rewrite C2r, C1r. rewrite !u_Z2bv by lia.
        cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *.
        destruct Fl1 as (Fl1a & _ & Fl1b). destruct Fl2 as (Fl2a & _ & Fl2b). destruct Fl3 as (Fl3a & _ & Fl3b).
        split; [|split; [|split]].
        - split; [split; [exact C10 | lia]|].
          split; [exact HLfmt|].
          split; [exists 26%Z; split; [lia | exact rostr_fmt]|].
          split; [split; [exact C11 | lia]|].
          split; [exists 13%Z; split; [lia | exact rostr_func]|].
          split; [split; [cbn; lia | split; [split; [lia|split; [lia|lia]] | apply cell_lift; [exact C1 | lia | lia | lia]]]|].
          split; [exact E1|].
          split; [split; [cbn; lia | split; [split; [lia|split; [lia|lia]] | apply cell_lift; [exact C2 | lia | lia | lia]]]|].
          split; [exact E2|].
          split; [split; [cbn; lia | split; [split; [lia|split; [lia|lia]] | apply cell_lift; [exact C3 | lia | lia | lia]]]|].
          split; [exact M2x_img_none|].
          split; [split; [lia | apply sp48_al16]|].
          split; [lia | exact I].
        - split; [lia|]. split; [split; [lia | split; [lia|lia]]|]. split; [|exact I].
          eapply store_ok_mono; [apply M2x_grows|].
          destruct (Z.to_nat LSF) as [|n'] eqn:En; [reflexivity|]. rewrite <- En.
          eapply (store_ok_sub SEGS M (Z_to_bv 64 (sp - (48 + LSF))) _ (Z.to_nat (48 + LSF)));
            [ | exact SOKF | | ]; rewrite ?u_Z2bv by lia; lia.
        - split; [|exact I]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia| exact I].
        - rl_vmc_VL. }
      destruct (HC [(0x10591 + dVLS_10591); (0x10693 + dVLS_10693); hv; cg; cv]%Z r2 M2x rom eq_refl PRE) as (outs & r3 & M3 & _ & RUNC & POST).
      unfold SSP.spec_lept_stderr_s1 in POST. SSP.spec_unfold_in POST.
      destruct POST as (KEPT & _ & FRM & GR & _).
      cbn [SSP.su_entry SSP.exit_target SSP.su_exit SSP.spec_lept_stderr_s1] in RUNC.
      rewrite HLe, C1r in RUNC. rewrite C2r in FRM. rewrite u_Z2bv in FRM by lia.
      destruct KEPT as (K2 & K3 & K4 & K8 & K9 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27 & _).
      destruct (pb_D3 r3 M3) as (r4 & S4 & D10 & AG4).
      pose proof (AG4 2 ltac:(notin_list)) as D2r. rewrite K2, C2r in D2r.
      assert (HF : FrameSame (v_lw (Z_to_bv 64 w)) (v_lw (Z_to_bv 64 h)) M3).
      { intros x Hx. unfold M2x in FRM. apply FRM. split; [lia | exact I]. }
      destruct (pb_E' _ _ r4 M3 HF D2r) as (r5 & S5 & E10 & E1r & E2r & E8 & E9 & E18 & AG5).
      exists r5, M3. split.
      + eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2|].
        eapply msteps_trans.
        { exact RUNC. }
        eapply msteps_trans; [|exact S5].
        exact S4.
      + split; [intros x Hx; apply FRM; split; [lia | exact I]|].
        split; [exact GR|].
        rewrite D10 in E10. repeat split; try assumption.
        regs_agree_enum ltac:(
          first [ rewrite !getr_zero; reflexivity
                | rewrite AG5 by notin_list; rewrite AG4 by notin_list;
                  first [ rewrite K3 | rewrite K4 | rewrite K19 | rewrite K20 | rewrite K21 | rewrite K22
                        | rewrite K23 | rewrite K24 | rewrite K25 | rewrite K26 | rewrite K27 ];
                  rewrite AG2 by notin_list; apply AG1; notin_list ]).
  Qed.

End PB.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem padbits_contract : SSP.sum_contract SEGS (SSP.spec_padbits (0x242cc + dVL_242cc) 48).
Proof.
  apply SSP.sum_contract_in7; [reflexivity | reflexivity |].
  intros pix val w h d wpl data R M rom PRE.
  unfold SSP.spec_padbits in PRE. SSP.spec_unfold_in PRE.
  destruct PRE as (ITEMS & EFF & FR & RET).
  destruct ITEMS as ((H10 & _) & Hpix & (_ & ALpix) & (H11 & _) & Hval & (_ & _ & (Rw & Cw)) & Hw & (_ & _ & (Rh & Ch)) & Hh
                     & (_ & _ & (Rd & Cd)) & Hd & (_ & _ & (Rwpl & Cwpl)) & Hwpl & (_ & (_ & _ & Fdata) & (Rdata & Cdata)) & Hdata & (_ & ALdata)
                     & ((_ & _ & FRS) & SOKr) & PR & (_ & ALsp) & _).
  destruct EFF as (_ & (Fsp & _ & Fsp2) & SOKf & _).
  destruct FR as ((F0 & F4 & F8 & F16 & F56 & FRR & _) & _).
  subst val.
  cbn [Z.of_nat Z.add] in F0, F4, F8, F16, F56.
  change (2 ^ (8 * Z.of_nat 4))%Z with (2 ^ 32)%Z in Rw, Rh, Rd, Rwpl.
  set (sp := bv_unsigned (getr R 2)) in *.
  assert (FP : disj_apart pix 64 (sp - 48) 48) by (unfold disj_apart; clear FRR PR; lia).
  assert (FP12 : disj_apart pix 12 (sp - 48) 48) by (unfold disj_apart in FP |- *; clear FRR PR F0 F4 F8 F16 F56; lia).
  assert (FRR' : disj_apart data (4 * (wpl * h)) (sp - 48) 48) by (unfold disj_apart; clear PR FP FP12; lia).
  clear F0 F4 F8 F16 F56.
  assert (H2 : getr R 2 = Z_to_bv 64 sp) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (u64_range (getr R 2)) as Hsp. fold sp in Hsp.
  rewrite Z.add_0_r in Cw.
  assert (Hd' : (d = 1 \/ d = 2 \/ d = 4 \/ d = 8 \/ d = 16 \/ d = 24)%Z) by (clear FRR PR FP FP12; cbn in Hd; intuition lia).
  assert (Hd24 : (d <> 24)%Z) by (clear FRR PR FP FP12; cbn in Hd; intuition lia).
  assert (Hwpl2 : (0 <= wpl <= 20000)%Z).
  { clear FRR PR FP FP12. subst wpl. split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|].
    assert (w * d <= 20000 * 16)%Z by (apply Z.mul_le_mono_nonneg; lia). lia. }
  unfold SSP.spec_padbits. SSP.spec_unfold.
  destruct (padbits_run M rom pix w h d wpl data sp (getr R 1) (getr R 8) (getr R 9) (getr R 18)
              ltac:(lia) ltac:(lia) ALpix Rw Rh Hw Hh Hd' ltac:(lia) ALsp RET Cw Ch Cd Cwpl Cdata Hwpl2
              ltac:(lia) ALdata ltac:(lia) SOKr FRR' SOKf FP12 FP
              R Hd24 Hwpl eq_refl H2 eq_refl eq_refl eq_refl H10 H11)
    as (R' & M' & RUN & HI & A10 & A2 & A8 & A9 & A18 & AG).
  exists R', M'.
  split; [exact RUN|].
  split.
  { rewrite <- H2 in A2. repeat split; try assumption; apply AG; notin_list. }
  split; [exact A10|].
  split.
  { intros x (Hx1 & Hx2 & _). destruct HI as [HO _]. rewrite (HO x Hx2).
    unfold M2. apply M2g_outside; lia. }
  split; [|exact (conj (conj I (conj I I)) I)].
  destruct HI as [_ HG]. eapply mem_grows_trans; [|exact HG].
  apply M2_grows; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition padbits24_L_ok (L : SSP.ls_addrs) : Prop :=
  (SSP.ls_entry L = (0x13694 + dF_13694) /\ SSP.ls_sev_got L = (0x1e3b0 + dA_1e3a0) /\ In (0x10591 + dVLS_10591) (SSP.ls_fmts1 L)
   /\ (0 <= SSP.ls_img_lo L /\ SSP.ls_img_lo L <= (0x10591 + dVLS_10591) /\ SSP.ls_img_lo L <= (0x10693 + dVLS_10693) /\ (0x10591 + dVLS_10591) + 216 <= SSP.ls_img_hi L /\ (0x10693 + dVLS_10693) + 216 <= SSP.ls_img_hi L /\ SSP.ls_img_hi L <= SSP.ls_sp_lo L)
   /\ 0 <= SSP.ls_frame L)%Z.

Theorem padbits24_contract : forall L : SSP.ls_addrs,
  padbits24_L_ok L ->
  SSP.sum_contract SEGS (SSP.spec_lept_stderr_s1 L) ->
  SSP.sum_contract SEGS (SSP.spec_padbits24 (0x242cc + dVL_242cc) (48 + SSP.ls_frame L) L).
Proof.
  intros L (HLe & HLsg & HLfmt & HLimg & HLfr) HC.
  intros ins R M rom Hlen PRE.
  destruct ins as [|pix [|val [|w [|h [|d [|hv [|cg [|cv [|sg [|sv [|? ?]]]]]]]]]]]; try discriminate Hlen.
  unfold SSP.spec_padbits24 in PRE. SSP.spec_unfold_in PRE.
  destruct PRE as (ITEMS & EFF & FR & RET).
  destruct ITEMS as ((H10 & _) & Hpix & (_ & ALpix) & (H11 & _) & Hval & (_ & _ & (Rw & Cw)) & (_ & _ & (Rh & Ch))
                     & (_ & Fd8 & (Rd & Cd)) & Hd & (_ & Fl1 & C1) & E1 & (_ & Fl2 & C2) & E2 & (_ & Fl3 & C3)
                     & (_ & (Fsg1 & _ & Fsg2) & (Rsg & Csg)) & Esg & (_ & (Fsv1 & _ & Fsv2) & (Rsv & Csv)) & IMG & (_ & SP16) & SPR & _).
  destruct EFF as (_ & (Fsp & _ & Fsp2) & SOKF & _).
  destruct FR as ((F0 & F4 & F8 & A1 & A2 & A3 & Asg & Asv & _) & _).
  subst val. rewrite HLsg in *. subst sg.
  cbn [Z.of_nat Z.add] in F0, F4, F8, Asg, Asv.
  change (2 ^ (8 * Z.of_nat 4))%Z with (2 ^ 32)%Z in Rw, Rh, Rd, Rsv. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in Rsg.
  set (sp := bv_unsigned (getr R 2)) in *.
  assert (H2 : getr R 2 = Z_to_bv 64 sp) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (u64_range (getr R 2)) as Hsp. fold sp in Hsp.
  rewrite Z.add_0_r in Cw. rewrite Z.add_0_r in Csg, Csv, Fsv1, Fsv2, Asv.
  assert (FP12 : disj_apart pix 12 (sp - 48) 48) by (unfold disj_apart; clear A1 A2 A3 Asg Asv; lia).
  clear F0 F4 F8.
  assert (SOKf : store_ok SEGS M (Z_to_bv 64 (sp - 48)) 48 = true).
  { eapply (store_ok_sub SEGS M (Z_to_bv 64 (sp - (48 + SSP.ls_frame L))) _ (Z.to_nat (48 + SSP.ls_frame L)));
      [ | exact SOKF | | ]; rewrite ?u_Z2bv by lia; lia. }
  assert (Hd' : (d = 1 \/ d = 2 \/ d = 4 \/ d = 8 \/ d = 16 \/ d = 24)%Z) by lia.
  unfold SSP.flatZ in Fd8. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Fd8.
  destruct (pb_A M rom pix w h d sp (getr R 1) (getr R 8) (getr R 9) (getr R 18)
              ltac:(clear A1 A2 A3 Asg Asv FP12; lia) ALpix Rw Rh Hd' ltac:(lia) SP16 Cw Ch Cd SOKf FP12 R eq_refl H2 eq_refl eq_refl eq_refl H10 H11)
    as (r1 & S1 & A2r & A18 & A8 & A10 & A11 & AG1).
  destruct (pb_D M rom w h d sp (getr R 1) (getr R 8) (getr R 9) (getr R 18)
              Hd' ltac:(lia) SP16 RET L sv HLe HLfmt HLimg HLfr Csg ltac:(lia) Csv Rsv IMG SPR
              r1 hv cg cv Hd ltac:(clear A1 A2 A3 Asv; lia) ltac:(clear A1 A2 A3 Asg; lia)
              Fl1 C1 E1 Fl2 C2 E2 Fl3 C3 A1 A2 A3 SOKF HC A2r A10 A11)
    as (R' & M' & S2 & FRM & GR & B10 & B1 & B2 & B8 & B9 & B18 & AG2).
  exists [], R', M'.
  split; [reflexivity|].
  unfold SSP.spec_padbits24. SSP.spec_unfold.
  split; [eapply msteps_trans; [exact S1 | exact S2]|].
  split.
  { rewrite <- H2 in B2. repeat split; try assumption;
      (rewrite AG2 by notin_list; apply AG1; notin_list). }
  split; [exact B10|].
  split.
  { intros x [Hx _]. rewrite FRM by (clear FP12 A1 A2 A3 Asg Asv; lia).
    unfold M2x. apply M2g_outside; clear A1 A2 A3 Asg Asv; lia. }
  split; [|exact (conj (conj I I) I)].
  eapply mem_grows_trans; [|exact GR]. unfold M2x. apply M2g_grows; assumption.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

End VPORT.
