(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Image ZBridge SysStep ITree Nodes Decode Arr FP Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessP ProgA AsanProgDeps SjStage1 SjS1Bytes.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import SjInvPath SjInv SjS1Lem SjS1Ghost.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface AU_rt.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AU_kit AU_iface AHarnessU_iface AU_client_kit AU_fuzz_kit AU_parts_iface AU_steptac Stdio_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosRegs PIosKitA PIosKit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegGhost SegProg SegExplore SegLib SegBridge.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2Entry.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import PA2_kz.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegT Require A1G_defs A1G_mcb.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegT Require Import A1G_soundH.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import APC_kit2 APC_s12iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.

Local Notation M64 := 18446744073709551616.
Local Notation u := bv_unsigned.
Local Notation SH := 2147450880%Z (only parsing).

Ltac mods := repeat match goal with |- context [?x mod 18446744073709551616] => rewrite (Z.mod_small x 18446744073709551616) by lia end.
(* [comment removed for export] *)
Ltac a1u := unfold A1G_defs.vSP, A1G_defs.vTHIS, A1G_defs.vBUF, A1G_defs.vA1, A1G_defs.idxlen, A1G_defs.spo;
  unfold A1G_defs.vRA, A1G_defs.vSP16, A1G_defs.vGP, A1G_defs.vTP, A1G_defs.vS0, A1G_defs.vS1, A1G_defs.vS2, A1G_defs.vS3,
  A1G_defs.vS4, A1G_defs.vS5, A1G_defs.vS6, A1G_defs.vS7, A1G_defs.vS8, A1G_defs.vS9, A1G_defs.vS10, A1G_defs.vS11, A1G_defs.vT8,
  A1G_defs.vB8, A1G_defs.vLEN, A1G_defs.vI8, A1G_defs.vG, A1G_defs.vIG, A1G_defs.vBO;
  unfold A1G_defs.V, A1G_defs.add, A1G_defs.sub, A1G_defs.mul.
Ltac a1uh H := unfold A1G_defs.vSP, A1G_defs.vTHIS, A1G_defs.vBUF, A1G_defs.vA1, A1G_defs.idxlen, A1G_defs.spo in H;
  unfold A1G_defs.vRA, A1G_defs.vSP16, A1G_defs.vGP, A1G_defs.vTP, A1G_defs.vS0, A1G_defs.vS1, A1G_defs.vS2, A1G_defs.vS3,
  A1G_defs.vS4, A1G_defs.vS5, A1G_defs.vS6, A1G_defs.vS7, A1G_defs.vS8, A1G_defs.vS9, A1G_defs.vS10, A1G_defs.vS11, A1G_defs.vT8,
  A1G_defs.vB8, A1G_defs.vLEN, A1G_defs.vI8, A1G_defs.vG, A1G_defs.vIG, A1G_defs.vBO in H;
  unfold A1G_defs.V, A1G_defs.add, A1G_defs.sub, A1G_defs.mul in H.

Lemma u_rngW : forall (w : word), 0 <= u w < M64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. unfold bv_modulus in H. exact H. Qed.

(* [comment removed for export] *)
Lemma bytes_at_of_mbytesA : forall m A bs, mbytes m A bs -> 0x665000 <= A -> A + Z.of_nat (length bs) <= 2^64 -> bytes_at asegs m A bs.
Proof.
  intros m A bs H H0 H1. split; [lia|]. split; [exact H1|]. intros i Hi.
  rewrite ref_mrd_overlay by (unfold wa; rewrite unsigned_lit by lia; lia). unfold wa.
  rewrite (H (Z.of_nat i) ltac:(lia)). rewrite Nat2Z.id. symmetry. apply nth_error_nth'. exact Hi.
Qed.
(* [comment removed for export] *)
Lemma rw_cells_ofA : forall m A cs, cells_wf cs -> bytes_at asegs m A (cells_bytes cs) -> wr_at asegs m A (Z.of_nat (cells_size cs)) ->
  rw_cells asegs m A cs.
Proof. intros m A cs H1 H2 H3. split; [split; assumption| exact H3]. Qed.
Lemma wr_at_subA : forall m A n A' n', wr_at asegs m A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' -> wr_at asegs m A' n'.
Proof. intros m A n A' n' (H0 & H1 & H) Ha Hb Hn. split; [lia|]. split; [lia|]. intros i Hi. replace (A' + i) with (A + (A' - A + i)) by lia. apply H. lia. Qed.
Lemma ez_wA : forall ZL e (w : word), zok e = true -> zden ZL e mod M64 = u w -> edenot (mkEZ ZL) e = w.
Proof. intros ZL e w Hz H. rewrite zden_ok by exact Hz. apply bv_eq. rewrite u_Z_to_bv. exact H. Qed.

(* [comment removed for export] *)
Lemma fp_of_rng : forall E W RNG,
  (forall w, In w W -> rng RNG (fst (SX.awin_den E w)) (snd (SX.awin_den E w) - fst (SX.awin_den E w))) ->
  (forall b j, SX.fp_of (Some W) E b j -> RNG b j) /\ SX.aw_genuine E (Some W).
Proof.
  intros E W RNG H. split.
  - intros b j (w & Hw & H1 & H2). destruct (H w Hw) as (_ & _ & R). apply R; lia.
  - intros w Hw. destruct (H w Hw) as (R1 & R2 & _). lia.
Qed.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ZL_a1 (zra SP16 zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 T8 B8 LEN I8 G IG BO : Z) (rest : list Z) : list Z :=
  [zra; SP16; zgp; ztp; zs0; zs1; zs2; zs3; zs4; zs5; zs6; zs7; zs8; zs9; zs10; zs11; T8; B8; LEN; I8; G; IG; BO] ++ rest.

Section KN.
  Variables (zra SP16 zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 T8 B8 LEN I8 G IG BO : Z) (rest : list Z).
  Local Notation ZL := (ZL_a1 zra SP16 zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 T8 B8 LEN I8 G IG BO rest).
  Variables (SPv THIS BUF ASI lo : Z) (m : amem) (bs : list byte).
  Hypothesis E_SP : SPv = 16 * SP16.
  Hypothesis E_T8 : THIS = 8 * T8.
  Hypothesis E_B8 : BUF = 8 * B8 + BO.
  Hypothesis E_I8 : ASI = 8 * I8.
  Hypothesis H_LEN : 0 <= LEN <= 1048512.
  Hypothesis H_SP : 0x7fff00000000 <= SPv <= 2^47.
  Hypothesis H_THIS : 0x665000 <= THIS /\ THIS + 96 <= ATOPM /\ THIS + 96 <= SPv - 8192.
  Hypothesis H_BUF : 0 <= BO <= 7 /\ 0x665000 <= 8 * B8 /\ BUF + LEN + 64 <= ATOPM /\ BUF + LEN + 64 <= SPv - 8192.
  Hypothesis H_IDX : 0x665000 <= ASI /\ ASI + 4 * LEN + 36 <= ATOPM /\ ASI + 4 * LEN + 36 <= SPv - 8192.
  Hypothesis HB_THIS : DJ 0x7fff7000 0x100000001000 THIS 96.
  Hypothesis HB_BUF : DJ 0x7fff7000 0x100000001000 BUF (LEN + 64).
  Hypothesis HB_IDX : DJ 0x7fff7000 0x100000001000 ASI (4 * LEN + 36).
  Hypothesis D_TB : DJ THIS 96 BUF (LEN + 64).
  Hypothesis D_TI : DJ THIS 96 ASI (4 * LEN + 36).
  Hypothesis D_BI : DJ BUF (LEN + 64) ASI (4 * LEN + 36).
  Hypothesis H_G : 57 <= 8 * G - (LEN + BO) <= 64 /\ 8 <= G <= 131080.
  Hypothesis H_IG : 32 <= 8 * IG - 4 * LEN <= 0x800000 /\ 5 <= IG <= 0x100000.
  Hypothesis S_T8 : forall i, 0 <= i < 12 -> m (Z_to_bv 64 (SH + T8 + i)) = Some (Z_to_bv 8 0).
  Hypothesis S_B8 : forall i, 0 <= i < G -> m (Z_to_bv 64 (SH + B8 + i)) = Some (Z_to_bv 8 0).
  Hypothesis S_I8 : forall i, 0 <= i < IG -> m (Z_to_bv 64 (SH + I8 + i)) = Some (Z_to_bv 8 0).
  Hypothesis S_STK : forall i, 0 <= i < 1024 -> m (Z_to_bv 64 (SH + 2 * SP16 - 1024 + i)) = Some (Z_to_bv 8 0).
  Hypothesis M_A1 : rw_cells asegs m (THIS + 16) [C8 (Z_to_bv 64 ASI)].
  Hypothesis M_GOT : rt_got m.
  Hypothesis M_SHB : rt_shbase m.
  Hypothesis M_CT : rt_ctab_sh m.
  Hypothesis W_STKSH : wr_at asegs m (SH + 2 * SP16 - 1024) 1024.
  Hypothesis W_THIS : wr_at asegs m THIS 96.
  Hypothesis W_IDX : wr_at asegs m ASI (4 * LEN + 36).
  Hypothesis M_STK : stk asegs m lo SPv.
  Hypothesis H_LO : 0x665000 <= lo <= SPv - 2656.
  Hypothesis M_BUF : bytes_at asegs m BUF bs.
  Hypothesis M_BUFL : Z.of_nat (length bs) = LEN + 64.
  Hypothesis HMI : mem_inv asegs m.

  Local Ltac zc := cbn [zden nth ZL_a1 app]; mods.
  Local Ltac dj H := unfold DJ in H; lia.

  Lemma a1_t0_kn : know_ok asegs (mkEZ ZL) m A1G_defs.T0_kn.
  Proof using All.
    atop_facts.
    unfold A1G_defs.T0_kn. a1u.
    repeat apply Forall_cons; try apply Forall_nil.
    (* [comment removed for export] *)
    - eapply (kz_word_cells asegs ZL m _ _ 8 _ (THIS + 16) _ 0); [reflexivity | lia | exact M_A1 | zc; lia | ].
      cbn [cell_at Nat.eqb]. zc. rewrite <- E_I8. reflexivity.
    (* [comment removed for export] *)
    - apply kz_range; [reflexivity| zc; lia].
    - apply kz_range; [reflexivity| zc; lia].
    - apply kz_range; [reflexivity| zc; lia].
    - apply kz_range; [reflexivity| zc; lia].
    - apply kz_disj; [reflexivity| zc; dj HB_THIS].
    - apply kz_range; [reflexivity| zc; lia].
    - apply kz_range; [reflexivity| zc; lia].
    - apply kz_disj; [reflexivity| zc; dj HB_BUF].
    - apply kz_range; [reflexivity| zc; lia].
    - apply kz_range; [reflexivity| zc; lia].
    - apply kz_disj; [reflexivity| zc; dj HB_IDX].
    - apply kz_disj; [reflexivity| zc; lia].
    - apply kz_disj; [reflexivity| zc; lia].
    - apply kz_disj; [reflexivity| zc; lia].
    - apply kz_disj; [reflexivity| zc; dj D_TB].
    - apply kz_disj; [reflexivity| zc; dj D_TI].
    - apply kz_disj; [reflexivity| zc; dj D_BI].
    - apply kz_range; [reflexivity| zc; lia].
    - apply kz_range; [reflexivity| zc; lia].
    - apply kz_range; [reflexivity| zc; lia].
    - apply kz_range; [reflexivity| zc; lia].
    - apply kz_range; [reflexivity| zc; lia].
    (* [comment removed for export] *)
    - apply kz_zero; [reflexivity| zc; lia .. |]. zc. intros i Hi. rewrite <- (S_T8 i Hi). f_equal. f_equal. lia.
    - apply kz_zero; [reflexivity| zc; lia .. |]. zc. intros i Hi. rewrite <- (S_B8 i Hi). f_equal. f_equal. lia.
    - apply kz_zero; [reflexivity| zc; lia .. |]. zc. intros i Hi. rewrite <- (S_I8 i Hi). f_equal. f_equal. lia.
    (* [comment removed for export] *)
    - eapply (kz_word_cells asegs ZL m _ _ 8 _ 0x1072f0 _ 16); [reflexivity | lia | exact M_GOT | zc; lia | reflexivity].
    - eapply (kz_word_cells asegs ZL m _ _ 8 _ 0x10faf8 _ 0); [reflexivity | lia | exact M_SHB | zc; lia | reflexivity].
    (* [comment removed for export] *)
    - eapply (kz_wr_sub asegs ZL m _ _ _ (SPv - 2656) 2656); [reflexivity | eapply stk_wr_atA; [exact M_STK| lia| lia| lia] | zc; lia .. ].
    - eapply (kz_wr_sub asegs ZL m _ _ _ THIS 96); [reflexivity | exact W_THIS | zc; lia .. ].
    - eapply (kz_wr_sub asegs ZL m _ _ _ THIS 96); [reflexivity | exact W_THIS | zc; lia .. ].
    - eapply (kz_wr_sub asegs ZL m _ _ _ THIS 96); [reflexivity | exact W_THIS | zc; lia .. ].
    - eapply (kz_wr_sub asegs ZL m _ _ _ ASI (4 * LEN + 36)); [reflexivity | exact W_IDX | zc; lia .. ].
    (* [comment removed for export] *)
    - eapply (kz_unk_bytes asegs ZL m _ _ _ BUF bs); [reflexivity | exact M_BUF | | zc; lia .. ].
      intros i Hi. apply seg_rom_above. lia.
    (* [comment removed for export] *)
    - apply kz_img; [lia | lia | exact HMI |]. intros a Ha. rewrite a_ro_addr. apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
    (* [comment removed for export] *)
    - eapply (stk_unkA ZL m lo SPv); [exact M_STK | reflexivity | lia | lia | zc; lia | zc; lia].
    (* [comment removed for export] *)
    - unfold rt_ctab_sh in M_CT. replace (shad ACTAB) with 0x7fffd028 in M_CT by reflexivity.
      eapply (kz_zero_cells ZL m _ _ _ 0x7fffd028 _); [reflexivity | exact M_CT | lia | cbn; lia | zc; lia | zc; cbn; lia | zc; lia |].
      zc. intros i Hi. cbn [cells_bytes cbytes]. rewrite app_nil_r. rewrite nth_error_repeat by lia. reflexivity.
    - unfold rt_ctab_sh in M_CT. replace (shad ACTAB) with 0x7fffd028 in M_CT by reflexivity.
      eapply (kz_wr_sub asegs ZL m _ _ _ 0x7fffd028 32); [reflexivity | exact (rw_cells_wr_at _ _ _ _ 32 M_CT ltac:(cbn; lia)) | zc; lia .. ].
    (* [comment removed for export] *)
    - apply kz_zero; [reflexivity| zc; lia .. |]. zc. intros i Hi. rewrite <- (S_STK i Hi). f_equal. f_equal. lia.
    - eapply (kz_wr_sub asegs ZL m _ _ _ (SH + 2 * SP16 - 1024) 1024); [reflexivity | exact W_STKSH | zc; lia .. ].
  Qed.
End KN.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma shad_d8 : forall x, shad x = SH + x / 8.
Proof. intros x. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma zero_gran : forall m A n X cnt, ablock_shadow m A n -> A mod 8 = 0 -> 0 <= A -> A <= 8 * X -> 8 * (X + cnt) <= A + n ->
  forall i, 0 <= i < cnt -> m (Z_to_bv 64 (SH + X + i)) = Some (Z_to_bv 8 0).
Proof.
  intros m A n X cnt HS HA H0 H1 H2 i Hi.
  assert (EA : A = 8 * (A / 8)) by (Z.div_mod_to_equations; lia).
  specialize (HS (X - A / 8 + i) ltac:(lia) ltac:(lia)).
  replace (8 * (X - A / 8 + i) + 8 <=? n) with true in HS by (symmetry; apply Z.leb_le; lia).
  rewrite shad_d8 in HS. unfold wa in HS. replace (SH + A / 8 + (X - A / 8 + i)) with (SH + X + i) in HS by lia. exact HS.
Qed.

Lemma sval0_byteA : forall b : byte, sval b = 0 -> b = Z_to_bv 8 0.
Proof.
  intros b H. apply bv_eq. rewrite Z_to_bv_unsigned. pose proof (bv_unsigned_in_range 8 b) as R.
  unfold sval, bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in *.
  change (256 `div` 2) with 128 in *. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma clean_shadowA : forall m lo hi X cnt, unpoisoned m lo hi -> lo <= 8 * X -> 8 * (X + cnt) <= hi ->
  forall i, 0 <= i < cnt -> m (Z_to_bv 64 (SH + X + i)) = Some (Z_to_bv 8 0).
Proof.
  intros m lo hi X cnt (H0 & H1 & HU) HL HH i Hi.
  destruct (HU (X + i) ltac:(lia) ltac:(lia) ltac:(lia)) as (b & Hb & Hg).
  replace (Z.min (8 * (X + i) + 8) hi - 8 * (X + i)) with 8 in Hg by lia.
  unfold gran_ok in Hg. assert (Hs : sval b = 0) by lia. rewrite (sval0_byteA b Hs) in Hb.
  unfold wa, ASHOFF in Hb. replace (SH + X + i) with (2147450880 + (X + i)) by lia. exact Hb.
Qed.

(* [comment removed for export] *)
Lemma mbytes_of_bytes_atA : forall m A bs, bytes_at asegs m A bs -> 0x665000 <= A -> mbytes m A bs.
Proof.
  intros m A bs (H0 & H1 & HB) HA i Hi. specialize (HB (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in HB by lia.
  rewrite ref_mrd_overlay in HB by (unfold wa; rewrite unsigned_lit by lia; lia).
  unfold wa in HB. rewrite HB. rewrite (nth_error_nth' bs (Z_to_bv 8 0)) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma glob_w : forall ZL E' e (w : word), SP.gagree 23 (mkEZ ZL) E' -> eb (mkEZ ZL) = eb E' -> expr_vars_lt 23 e = true -> zok e = true ->
  zden ZL e mod M64 = u w -> edenot E' e = w.
Proof. intros ZL E' e w Hg Hb Hv Hz H. rewrite <- (SP.edenot_gagree 23 (mkEZ ZL) E' e Hg Hb Hv). exact (ez_wA ZL e w Hz H). Qed.

(* [comment removed for export] *)
Lemma a1_t0_regs : forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (SP16 T8 B8 LEN I8 G IG BO THIS BUF : Z),
  u sp = 16 * SP16 -> THIS = 8 * T8 -> BUF = 8 * B8 + BO -> 0 <= THIS < M64 -> 0 <= BUF < M64 ->
  regs_ok (mkEZ (ZL_a1 (u ra) SP16 (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8) (u s9) (u s10) (u s11)
                       T8 B8 LEN I8 G IG BO [u t0; u t1; u t2; u a4; u a5; u a6; u a7; u t3; u t4; u t5; u t6]))
    A1G_defs.T0_regs
    (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 THIS) (Z_to_bv 64 BUF) (Z_to_bv 64 LEN) (Z_to_bv 64 0) a4 a5 a6 a7
         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP16 T8 B8 LEN I8 G IG BO THIS BUF ESP ET EB HT HB.
  apply regs_ok_mkR.
  change (map (fun k => edenot ?E (sr_get A1G_defs.T0_regs (Z_to_bv 5 k))) rkeys) with (map (edenot E) (tl A1G_defs.T0_regs)).
  cbn [tl A1G_defs.T0_regs map]. a1u.
  repeat (apply (f_equal2 (@cons word)); [apply ez_wA; [reflexivity|]; cbn [zden nth ZL_a1 app]; rewrite ?u_Z_to_bv;
            first [ reflexivity | (apply Z.mod_small; apply u_rngW) | (rewrite <- ESP; apply Z.mod_small; apply u_rngW)
                  | (rewrite <- ET; reflexivity) | (rewrite <- EB; reflexivity) ] |]).
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition A1G_Aw := ltac:(let x := eval cbv [A1G_defs.A1G SP.PGCA SP.PGX SP.p_A] in (SP.p_A A1G_defs.A1G) in
                           match x with Some ?w => exact w end).
Lemma A1G_pA : SP.p_A A1G_defs.A1G = Some A1G_Aw.
Proof. reflexivity. Qed.
Definition A1G_Ww := ltac:(let x := eval cbv [A1G_defs.A1G SP.PGCA SP.PGX SP.p_W] in (SP.p_W A1G_defs.A1G) in exact x).
Lemma A1G_pW : SP.p_W A1G_defs.A1G = A1G_Ww.
Proof. reflexivity. Qed.
Lemma A1G_pPS : SP.p_PS A1G_defs.A1G = None.
Proof. reflexivity. Qed.

Section FP.
  Variables (zra SP16 zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 T8 B8 LEN I8 G IG BO : Z) (rest : list Z).
  Local Notation ZL := (ZL_a1 zra SP16 zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 T8 B8 LEN I8 G IG BO rest).
  Variables (SPv THIS BUF ASI : Z) (RNG : footprint).
  Hypothesis E_SP : SPv = 16 * SP16.
  Hypothesis E_T8 : THIS = 8 * T8.
  Hypothesis E_B8 : BUF = 8 * B8 + BO.
  Hypothesis E_I8 : ASI = 8 * I8.
  Hypothesis H_TB : 0 <= THIS <= 2^47.
  Hypothesis H_BB : 0 <= 8 * B8 /\ 0 <= BO <= 7 /\ BUF <= 2^47.
  Hypothesis H_IB : 0 <= ASI <= 2^47.
  Hypothesis H_LEN : 0 <= LEN <= 2^20.
  Hypothesis H_G : 0 <= G <= 2^20.
  Hypothesis H_IG : 0 <= IG <= 2^20.
  Hypothesis R_STK : rng RNG (SPv - 2656) 2656.
  Hypothesis R_THIS : rng RNG THIS 96.
  Hypothesis R_TSH : rng RNG (SH + T8) 12.
  Hypothesis R_BUF : rng RNG BUF (LEN + 64).
  Hypothesis R_BSH : rng RNG (SH + B8) G.
  Hypothesis R_IDX : rng RNG ASI (4 * LEN + 36).
  Hypothesis R_ISH : rng RNG (SH + I8) IG.
  Hypothesis R_IMG : rng RNG 0x10000 0x655000.
  Hypothesis R_CSH : rng RNG 0x7fffd028 32.
  Hypothesis R_SSH : rng RNG (SH + 2 * SP16 - 1024) 1024.
  Hypothesis H_SP : 0x7fff00000000 <= SPv <= 2^47.

  Local Ltac fw R := cbn [SX.awin_den fst snd]; a1u; rewrite ?u_zden by reflexivity; cbn [zden nth ZL_a1 app]; mods;
    eapply rng_sub; [exact R | lia | lia].

  Lemma a1_fp : (forall b j, SX.fp_of (SP.p_A A1G_defs.A1G) (mkEZ ZL) b j -> RNG b j) /\ SX.aw_genuine (mkEZ ZL) (SP.p_A A1G_defs.A1G).
  Proof using All.
    rewrite A1G_pA. apply fp_of_rng. intros w Hw. unfold A1G_Aw in Hw. cbn [In] in Hw.
    destruct Hw as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]];
      [ fw R_STK | fw R_THIS | fw R_TSH | fw R_BUF | fw R_BSH | fw R_IDX | fw R_ISH | fw R_IMG | fw R_IMG | fw R_IMG | fw R_CSH
      | fw R_SSH | fw R_IMG ].
  Qed.
End FP.

Section CND.
  Context (AI : AMallocIface).
  Variables (zra SP16 zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 T8 B8 LEN I8 G IG BO : Z) (rest : list Z).
  Local Notation ZL := (ZL_a1 zra SP16 zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 T8 B8 LEN I8 G IG BO rest).
  Variables (SPv THIS ASI : Z) (LB : list ablock) (pim psi : AsanCtrl.aptr) (nim nsi : Z).
  Hypothesis E_SP : SPv = 16 * SP16.
  Hypothesis E_T8 : THIS = 8 * T8.
  Hypothesis E_I8 : ASI = 8 * I8.
  Hypothesis H_TB : 0 <= THIS <= 2^47.
  Hypothesis H_IB : 0 <= ASI <= 2^47.
  Hypothesis H_LEN : 0 <= LEN <= 2^20.
  Hypothesis H_SP : ATOP + 4096 <= SPv - 2656 /\ SPv <= 2^47.
  Hypothesis INM : In (HB pim THIS nim) LB.
  Hypothesis NIM : 96 <= nim.
  Hypothesis INS : In (HB psi ASI nsi) LB.
  Hypothesis NSI : 4 * LEN + 36 <= nsi.

  Local Ltac cw := cbn [SP.win_den fst snd]; a1u; rewrite ?u_zden by reflexivity; cbn [zden nth ZL_a1 app]; mods.

  Lemma a1_cnd : A1G_cnd AI LB (mkEZ ZL).
  Proof using All.
    atop_facts. unfold A1G_cnd, SP.wins_client. rewrite A1G_pW. unfold A1G_Ww.
    repeat apply Forall_cons; try apply Forall_nil; cw; unfold A1G_mcb.A1B.hmC.
    - left. left. split; lia.
    - right. left. exists (HB pim THIS nim). split; [exact INM| cbn [ab_addr ab_size]; lia].
    - right. left. exists (HB pim THIS nim). split; [exact INM| cbn [ab_addr ab_size]; lia].
    - right. left. exists (HB pim THIS nim). split; [exact INM| cbn [ab_addr ab_size]; lia].
    - right. left. exists (HB psi ASI nsi). split; [exact INS| cbn [ab_addr ab_size]; lia].
  Qed.

  Variables (m m' : amem).
  Lemma a1_frame : SP.frame_ok (A1G_mcb.A1B.hmA AI LB) (mkEZ ZL) (SP.p_W A1G_defs.A1G) (SP.p_PS A1G_defs.A1G) m m' ->
    munch (s1_winA SPv THIS ASI LEN) m m'.
  Proof using All.
    atop_facts. rewrite A1G_pW, A1G_pPS. cbn [SP.frame_ok]. intros FRM x Hx. apply FRM. unfold SP.outside_wins, A1G_Ww.
    unfold s1_winA in Hx. cbn [outside] in Hx. pose proof (u_rngW x).
    repeat apply Forall_cons; try apply Forall_nil; cw; lia.
  Qed.
End CND.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section MAIN.
Variable AI : AMallocIface.

Theorem s1l_proofA : s1l_stmtA AI.
Proof.
  unfold s1l_stmtA. intros until rstk.
  intros AH MI ND INM NIM INC BUF1 BUF2 INS NSI NSI40 BB DB DL W16 CT ST LOA LOS SPA STOP RCL RCL1 RCL2 RRNG RSTK RIMG RIMGSH FZ A0 A1 A2 A3.
  atop_facts. unfold AS1_STACK in LOS.
  pose proof (u_rngW sp) as RSP.
  pose proof (AI_layout AI _ _ _ _ _ AH) as (_ & _ & HTOP & _).
  destruct (AI_block AI _ _ _ _ _ _ _ _ AH INM) as (NM1 & (BM1 & BM2 & BM3 & BM4) & RM1 & RM2 & SHM & WRM & _).
  destruct (AI_block AI _ _ _ _ _ _ _ _ AH INC) as (NC1 & (BC1 & BC2 & BC3 & BC4) & RC1 & RC2 & SHC & WRC & _).
  destruct (AI_block AI _ _ _ _ _ _ _ _ AH INS) as (NS1 & (BS1 & BS2 & BS3 & BS4) & RS1 & RS2 & SHS & WRS & _).
  assert (LBM : DJ 0x7fff7000 0x100000001000 THIS nim /\ 0x665000 <= THIS) by (clear - BM1; unfold DJ, ablk, AIMG_HI, KLS in *; lia).
  assert (LBC : DJ 0x7fff7000 0x100000001000 ACP ncp /\ 0x665000 <= ACP) by (clear - BC1; unfold DJ, ablk, AIMG_HI, KLS in *; lia).
  assert (LBS : DJ 0x7fff7000 0x100000001000 ASI nsi /\ 0x665000 <= ASI) by (clear - BS1; unfold DJ, ablk, AIMG_HI, KLS in *; lia).
  clear BM1 BC1 BS1. destruct LBM as [LBM LBM0]. destruct LBC as [LBC LBC0]. destruct LBS as [LBS LBS0].
  assert (NDs : pim <> pcp /\ pim <> psi /\ pcp <> psi).
  { apply NoDup_cons_iff in ND as [N1 N]. apply NoDup_cons_iff in N as [N2 _]. cbn [In] in N1, N2. repeat split; intros E; subst; tauto. }
  destruct NDs as (N12 & N13 & N23).
  assert (DMC : DJ THIS nim ACP ncp) by exact (heap_blk_disj AI _ _ _ _ _ _ _ _ _ _ _ AH INM INC N12).
  assert (DMS : DJ THIS nim ASI nsi) by exact (heap_blk_disj AI _ _ _ _ _ _ _ _ _ _ _ AH INM INS N13).
  assert (DCS : DJ ACP ncp ASI nsi) by exact (heap_blk_disj AI _ _ _ _ _ _ _ _ _ _ _ AH INC INS N23).
  clear N12 N13 N23 ND.
  (* [comment removed for export] *)
  set (LEN := zlength d) in *.
  assert (ZD0 : 0 <= LEN) by (unfold LEN, zlength; lia).
  assert (E_SP : u sp = 16 * (u sp / 16)) by (clear - SPA; Z.div_mod_to_equations; lia).
  assert (E_T8 : THIS = 8 * (THIS / 8)) by (clear - BM4; Z.div_mod_to_equations; lia).
  assert (E_B8 : BUF = 8 * (BUF / 8) + BUF mod 8) by (apply Z.div_mod; lia).
  assert (E_I8 : ASI = 8 * (ASI / 8)) by (clear - BS4; Z.div_mod_to_equations; lia).
  assert (E_C8 : ACP = 8 * (ACP / 8)) by (clear - BC4; Z.div_mod_to_equations; lia).
  pose proof (Z.mod_pos_bound BUF 8 ltac:(lia)) as RBO.
  assert (H_G : 57 <= 8 * ((LEN + BUF mod 8 + 64) / 8) - (LEN + BUF mod 8) <= 64 /\ 8 <= (LEN + BUF mod 8 + 64) / 8 <= 131080)
    by (clear - DL ZD0 RBO; Z.div_mod_to_equations; lia).
  assert (H_IG : 32 <= 8 * Z.max 5 ((4 * LEN + 39) / 8) - 4 * LEN <= 0x800000 /\ 5 <= Z.max 5 ((4 * LEN + 39) / 8) <= 0x100000)
    by (clear - DL ZD0; Z.div_mod_to_equations; lia).
  assert (IGN : 8 * Z.max 5 ((4 * LEN + 39) / 8) <= nsi) by (clear - NSI NSI40 ZD0; Z.div_mod_to_equations; lia).
  set (SP16 := u sp / 16) in *. set (T8 := THIS / 8) in *. set (B8 := BUF / 8) in *. set (BO := BUF mod 8) in *.
  set (I8 := ASI / 8) in *. set (CP8 := ACP / 8) in *. set (G := (LEN + BO + 64) / 8) in *. set (IG := Z.max 5 ((4 * LEN + 39) / 8)) in *.
  clearbody SP16 T8 B8 BO I8 CP8 G IG.
  (* [comment removed for export] *)
  assert (S_T8 : forall i, 0 <= i < 12 -> m (Z_to_bv 64 (SH + T8 + i)) = Some (Z_to_bv 8 0))
    by (apply (zero_gran m THIS nim T8 12 SHM); clear - E_T8 NIM LBM0; lia).
  assert (S_B8 : forall i, 0 <= i < G -> m (Z_to_bv 64 (SH + B8 + i)) = Some (Z_to_bv 8 0))
    by (apply (zero_gran m ACP ncp B8 G SHC); clear - E_C8 E_B8 BUF1 BUF2 RBO H_G LBC0; lia).
  assert (S_I8 : forall i, 0 <= i < IG -> m (Z_to_bv 64 (SH + I8 + i)) = Some (Z_to_bv 8 0))
    by (apply (zero_gran m ASI nsi I8 IG SHS); clear - E_I8 IGN LBS0; lia).
  destruct RCL as [(UNP & (HL1 & HL2 & HL3 & HL4 & HL5 & HL6) & WSH & _) _].
  assert (S_STK : forall i, 0 <= i < 1024 -> m (Z_to_bv 64 (SH + 2 * SP16 - 1024 + i)) = Some (Z_to_bv 8 0)).
  { intros i Hi. replace (SH + 2 * SP16 - 1024 + i) with (SH + (2 * SP16 - 1024) + i) by lia.
    apply (clean_shadowA m (r_lo rstk) (r_hi rstk) (2 * SP16 - 1024) 1024 UNP); [clear - E_SP RCL1 LOS; lia | clear - E_SP RCL2; lia | exact Hi]. }
  assert (W_STKSH : wr_at asegs m (SH + 2 * SP16 - 1024) 1024).
  { eapply wr_at_subA; [exact WSH | | | lia]; rewrite !shad_d8; clear - E_SP RCL1 RCL2 LOS HL1 HL2; Z.div_mod_to_equations; lia. }
  (* [comment removed for export] *)
  set (ZL := ZL_a1 (u ra) SP16 (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8) (u s9) (u s10) (u s11)
                   T8 B8 LEN I8 G IG BO [u t0; u t1; u t2; u a4; u a5; u a6; u a7; u t3; u t4; u t5; u t6]).
  assert (HR : regs_ok (mkEZ ZL) A1G_defs.T0_regs (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)).
  { subst a0 a1 a2 a3. apply a1_t0_regs; [exact E_SP | exact E_T8 | exact E_B8 | lia | lia]. }
  assert (HK : know_ok asegs (mkEZ ZL) m A1G_defs.T0_kn).
  { eapply (a1_t0_kn (u ra) SP16 (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8) (u s9) (u s10) (u s11)
                     T8 B8 LEN I8 G IG BO [u t0; u t1; u t2; u a4; u a5; u a6; u a7; u t3; u t4; u t5; u t6] (u sp) THIS BUF ASI lo m (s1buf d));
      [ exact E_SP | exact E_T8 | exact E_B8 | exact E_I8 | lia | lia | lia | lia | lia
      | clear - LBM NIM; unfold DJ in *; lia | clear - LBC BUF1 BUF2 ZD0; unfold DJ in *; lia | clear - LBS NSI ZD0; unfold DJ in *; lia
      | clear - DMC NIM BUF1 BUF2 ZD0; unfold DJ in *; lia | clear - DMS NIM NSI ZD0; unfold DJ in *; lia
      | clear - DCS BUF1 BUF2 NSI ZD0; unfold DJ in *; lia
      | exact H_G | exact H_IG | exact S_T8 | exact S_B8 | exact S_I8 | exact S_STK | exact W16
      | destruct (client_rt_of_aheap AI _ _ _ _ _ AH) as (X & _); exact X
      | destruct (client_rt_of_aheap AI _ _ _ _ _ AH) as (_ & _ & _ & X & _); exact X
      | exact CT | exact W_STKSH
      | eapply wr_at_subA; [exact WRM | lia | lia | lia] | eapply wr_at_subA; [exact WRS | lia | lia | lia]
      | exact ST | lia | exact BB
      | unfold s1buf, LEN, zlength; rewrite length_map, length_app, repeat_length; lia | exact MI ]. }
  (* [comment removed for export] *)
  assert (HG : SG.gholds (s1_gp d) (mkEZ ZL) m (ST.t_ghost A1G_defs.T0)).
  { unfold A1G_defs.T0, ST.t_ghost, SG.gholds. apply Forall_cons; [| apply Forall_nil].
    cbn [ST.g_id ST.g_args map]. a1u. rewrite !zden_ok by reflexivity. unfold ZL. cbn [zden nth ZL_a1 app].
    cbn [s1_gp]. unfold g_buf. rewrite !u_Z_to_bv. rewrite <- E_B8. mods.
    split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact DB|].
    apply mbytes_of_bytes_atA; [exact BB| lia]. }
  assert (RF : rfull (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)) by apply rfull_mkR.
  (* [comment removed for export] *)
  rewrite shad_d8 in RM2, RC2, RS2. unfold shlen in RM2, RC2, RS2. rewrite Z.shiftr_div_pow2 in RM2, RC2, RS2 by lia.
  change (2 ^ 3) with 8 in RM2, RC2, RS2.
  unfold rrng in RRNG. rewrite !shad_d8 in RRNG.
  assert (FP : (forall b j, SX.fp_of (SP.p_A A1G_defs.A1G) (mkEZ ZL) b j -> RNG b j) /\ SX.aw_genuine (mkEZ ZL) (SP.p_A A1G_defs.A1G)).
  { eapply (a1_fp (u ra) SP16 (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8) (u s9) (u s10) (u s11)
                  T8 B8 LEN I8 G IG BO [u t0; u t1; u t2; u a4; u a5; u a6; u a7; u t3; u t4; u t5; u t6] (u sp) THIS BUF ASI RNG);
      [ exact E_SP | exact E_T8 | exact E_B8 | exact E_I8 | lia | lia | lia | lia | lia | lia
      | eapply rng_sub; [exact RSTK | lia | lia] | eapply rng_sub; [exact RM1 | lia | lia]
      | eapply rng_sub; [exact RM2 | clear - E_T8 NIM | clear - E_T8 NIM]; Z.div_mod_to_equations; lia
      | eapply rng_sub; [exact RC1 | lia | lia]
      | eapply rng_sub; [exact RC2 | clear - E_C8 E_B8 BUF1 BUF2 RBO H_G | clear - E_C8 E_B8 BUF1 BUF2 RBO H_G]; Z.div_mod_to_equations; lia
      | eapply rng_sub; [exact RS1 | lia | lia]
      | eapply rng_sub; [exact RS2 | clear - E_I8 IGN | clear - E_I8 IGN]; Z.div_mod_to_equations; lia
      | exact RIMG | eapply rng_sub; [exact RIMGSH | lia | lia]
      | eapply rng_sub; [exact RRNG | clear - E_SP HL1 RCL1 LOS | clear - E_SP HL2 RCL2]; Z.div_mod_to_equations; lia
      | lia ]. }
  destruct FP as [FPLE HAG].
  assert (HCnd : A1G_cnd AI LB (mkEZ ZL)).
  { eapply (a1_cnd AI (u ra) SP16 (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8) (u s9) (u s10) (u s11)
                   T8 B8 LEN I8 G IG BO [u t0; u t1; u t2; u a4; u a5; u a6; u a7; u t3; u t4; u t5; u t6] (u sp) THIS ASI LB pim psi nim nsi);
      [ exact E_SP | exact E_T8 | exact E_I8 | lia | lia | lia | lia | exact INM | exact NIM | exact INS | exact NSI ]. }
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply evtF_weaken; [exact FPLE|].
    change (Z_to_bv 64 ASTAGE1) with (Z_to_bv 64 (ST.t_pc A1G_defs.T0)).
    exact (a1g_evtH AI L RNG st LB asan_memcpy_proof d (mkEZ ZL) m (seg_rom asegs) _ F fc eq_refl HAG HCnd (conj AH MI) RF HR HK HG MI FZ). }
  intros ms' XP.
  destruct XP as (X & E' & m' & R' & F' & fc' & HX & -> & FZ' & RF' & HR' & HK' & HG' & GA & EB & HH' & FRM & WM' & MI' & STK').
  destruct HX as [<-|[]].
  destruct HH' as [AH' _].
  (* [comment removed for export] *)
  assert (RR : R' = mkR (edenot E' A1G_defs.vRA) (edenot E' A1G_defs.vSP) (edenot E' A1G_defs.vGP) (edenot E' A1G_defs.vTP)
        (ev E' 25) (ev E' 26) (ev E' 27) (edenot E' A1G_defs.vS0) (edenot E' A1G_defs.vS1) (ev E' 23) (ev E' 28) (ev E' 29) (ev E' 30)
        (ev E' 31) (ev E' 32) (ev E' 33) (ev E' 34) (edenot E' A1G_defs.vS2) (edenot E' A1G_defs.vS3) (edenot E' A1G_defs.vS4)
        (edenot E' A1G_defs.vS5) (edenot E' A1G_defs.vS6) (edenot E' A1G_defs.vS7) (edenot E' A1G_defs.vS8) (edenot E' A1G_defs.vS9)
        (edenot E' A1G_defs.vS10) (edenot E' A1G_defs.vS11) (ev E' 35) (ev E' 36) (ev E' 37) (ev E' 38)).
  { rewrite (regs_ok_canon _ _ _ RF' HR'). reflexivity. }
  assert (G_RA : edenot E' A1G_defs.vRA = ra) by (apply (glob_w ZL E' _ _ GA (eq_sym EB)); [reflexivity | reflexivity | unfold ZL; a1u; cbn [zden nth ZL_a1 app]; apply Z.mod_small; apply u_rngW]).
  assert (G_SP : edenot E' A1G_defs.vSP = sp) by (apply (glob_w ZL E' _ _ GA (eq_sym EB)); [reflexivity | reflexivity | unfold ZL; a1u; cbn [zden nth ZL_a1 app]; rewrite <- E_SP; apply Z.mod_small; apply u_rngW]).
  assert (G_GP : edenot E' A1G_defs.vGP = gp) by (apply (glob_w ZL E' _ _ GA (eq_sym EB)); [reflexivity | reflexivity | unfold ZL; a1u; cbn [zden nth ZL_a1 app]; apply Z.mod_small; apply u_rngW]).
  assert (G_TP : edenot E' A1G_defs.vTP = tp) by (apply (glob_w ZL E' _ _ GA (eq_sym EB)); [reflexivity | reflexivity | unfold ZL; a1u; cbn [zden nth ZL_a1 app]; apply Z.mod_small; apply u_rngW]).
  assert (G_S0 : edenot E' A1G_defs.vS0 = s0) by (apply (glob_w ZL E' _ _ GA (eq_sym EB)); [reflexivity | reflexivity | unfold ZL; a1u; cbn [zden nth ZL_a1 app]; apply Z.mod_small; apply u_rngW]).
  assert (G_S1 : edenot E' A1G_defs.vS1 = s1) by (apply (glob_w ZL E' _ _ GA (eq_sym EB)); [reflexivity | reflexivity | unfold ZL; a1u; cbn [zden nth ZL_a1 app]; apply Z.mod_small; apply u_rngW]).
  assert (G_S2 : edenot E' A1G_defs.vS2 = s2) by (apply (glob_w ZL E' _ _ GA (eq_sym EB)); [reflexivity | reflexivity | unfold ZL; a1u; cbn [zden nth ZL_a1 app]; apply Z.mod_small; apply u_rngW]).
  assert (G_S3 : edenot E' A1G_defs.vS3 = s3) by (apply (glob_w ZL E' _ _ GA (eq_sym EB)); [reflexivity | reflexivity | unfold ZL; a1u; cbn [zden nth ZL_a1 app]; apply Z.mod_small; apply u_rngW]).
  assert (G_S4 : edenot E' A1G_defs.vS4 = s4) by (apply (glob_w ZL E' _ _ GA (eq_sym EB)); [reflexivity | reflexivity | unfold ZL; a1u; cbn [zden nth ZL_a1 app]; apply Z.mod_small; apply u_rngW]).
  assert (G_S5 : edenot E' A1G_defs.vS5 = s5) by (apply (glob_w ZL E' _ _ GA (eq_sym EB)); [reflexivity | reflexivity | unfold ZL; a1u; cbn [zden nth ZL_a1 app]; apply Z.mod_small; apply u_rngW]).
  assert (G_S6 : edenot E' A1G_defs.vS6 = s6) by (apply (glob_w ZL E' _ _ GA (eq_sym EB)); [reflexivity | reflexivity | unfold ZL; a1u; cbn [zden nth ZL_a1 app]; apply Z.mod_small; apply u_rngW]).
  assert (G_S7 : edenot E' A1G_defs.vS7 = s7) by (apply (glob_w ZL E' _ _ GA (eq_sym EB)); [reflexivity | reflexivity | unfold ZL; a1u; cbn [zden nth ZL_a1 app]; apply Z.mod_small; apply u_rngW]).
  assert (G_S8 : edenot E' A1G_defs.vS8 = s8) by (apply (glob_w ZL E' _ _ GA (eq_sym EB)); [reflexivity | reflexivity | unfold ZL; a1u; cbn [zden nth ZL_a1 app]; apply Z.mod_small; apply u_rngW]).
  assert (G_S9 : edenot E' A1G_defs.vS9 = s9) by (apply (glob_w ZL E' _ _ GA (eq_sym EB)); [reflexivity | reflexivity | unfold ZL; a1u; cbn [zden nth ZL_a1 app]; apply Z.mod_small; apply u_rngW]).
  assert (G_S10 : edenot E' A1G_defs.vS10 = s10) by (apply (glob_w ZL E' _ _ GA (eq_sym EB)); [reflexivity | reflexivity | unfold ZL; a1u; cbn [zden nth ZL_a1 app]; apply Z.mod_small; apply u_rngW]).
  assert (G_S11 : edenot E' A1G_defs.vS11 = s11) by (apply (glob_w ZL E' _ _ GA (eq_sym EB)); [reflexivity | reflexivity | unfold ZL; a1u; cbn [zden nth ZL_a1 app]; apply Z.mod_small; apply u_rngW]).
  rewrite G_RA, G_SP, G_GP, G_TP, G_S0, G_S1, G_S2, G_S3, G_S4, G_S5, G_S6, G_S7, G_S8, G_S9, G_S10, G_S11 in RR. subst R'.
  assert (ETHIS : edenot E' A1G_defs.vTHIS = Z_to_bv 64 THIS)
    by (apply (glob_w ZL E' _ _ GA (eq_sym EB)); [reflexivity | reflexivity | unfold ZL; a1u; cbn [zden nth ZL_a1 app]; rewrite u_Z_to_bv, <- E_T8; reflexivity]).
  assert (EASI : edenot E' A1G_defs.vA1 = Z_to_bv 64 ASI)
    by (apply (glob_w ZL E' _ _ GA (eq_sym EB)); [reflexivity | reflexivity | unfold ZL; a1u; cbn [zden nth ZL_a1 app]; rewrite u_Z_to_bv, <- E_I8; reflexivity]).
  change (ST.t_pc A1G_defs.X) with 0x9938c.
  zstep.
  apply evtF_done. unfold s1l_postA.
  exists (ev E' 25), (ev E' 26), (ev E' 27), (ev E' 28), (ev E' 29), (ev E' 30), (ev E' 31), (ev E' 32), (ev E' 33), (ev E' 34),
         (ev E' 35), (ev E' 36), (ev E' 37), (ev E' 38), F', fc', m', (u (ev E' 23)).
  split; [rewrite Z_to_bv_bv_unsigned; reflexivity|].
  split; [exact FZ'|].
  split; [pose proof (u_rngW (ev E' 23)); lia|].
  split; [exact MI'|]. split; [exact (STK' _ _ ST)|]. split; [exact WM'|].
  (* [comment removed for export] *)
  split.
  { eapply (a1_frame AI (u ra) SP16 (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8) (u s9) (u s10) (u s11)
                     T8 B8 LEN I8 G IG BO [u t0; u t1; u t2; u a4; u a5; u a6; u a7; u t3; u t4; u t5; u t6] (u sp) THIS ASI LB pim psi nim nsi);
      [ exact E_SP | exact E_T8 | exact E_I8 | lia | lia | lia | lia | exact INM | exact NIM | exact INS | exact NSI | exact FRM ]. }
  split; [exact AH'|].
  (* [comment removed for export] *)
  inversion HG' as [|? ? G1 HG'']. inversion HG'' as [|? ? G2 _]. clear HG' HG'' G1.
  cbn [ST.g_id ST.g_args map] in G2. cbn [s1_gp] in G2. rewrite EASI, ETHIS in G2. unfold A1G_defs.V in G2. cbn [edenot] in G2.
  destruct G2 as [GC GS].
  split; [exact GC|].
  destruct (AI_block AI _ _ _ _ _ _ _ _ AH' INM) as (_ & _ & _ & _ & _ & WRM' & _).
  destruct (AI_block AI _ _ _ _ _ _ _ _ AH' INS) as (_ & _ & _ & _ & _ & WRS' & _).
  pose proof (know_nth _ _ _ _ 40%nat _ HK' eq_refl) as K72. pose proof (know_nth _ _ _ _ 41%nat _ HK' eq_refl) as K80.
  pose proof (kx_word_g asegs 23 ZL E' m' A1G_defs.vTHIS 72 8 A1G_defs.vBUF GA (eq_sym EB) eq_refl eq_refl eq_refl K72) as B72.
  pose proof (kx_word_g asegs 23 ZL E' m' A1G_defs.vTHIS 80 8 A1G_defs.vLEN GA (eq_sym EB) eq_refl eq_refl eq_refl K80) as B80.
  unfold ZL in B72, B80. a1uh B72. a1uh B80. cbn [zden nth ZL_a1 app] in B72, B80.
  rewrite <- E_T8, <- E_B8 in B72. rewrite <- E_T8 in B80. rewrite (Z.mod_small THIS) in B72 by lia. rewrite (Z.mod_small THIS) in B80 by lia.
  split.
  { apply rw_cells_ofA; [cbn; repeat split; exact I| |].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. unfold le8. apply bytes_at_app_join; [exact B72|].
      rewrite length_word_to_le_bytes. replace (THIS + 72 + Z.of_nat 8) with (THIS + 80) by lia. exact B80.
    - eapply wr_at_subA; [exact WRM'| lia| cbn; lia| cbn; lia]. }
  intros R0. destruct (GS R0) as (GN & GA1 & GM & GT & G24).
  rewrite unsigned_lit in G24 by lia. rewrite unsigned_lit in GM by lia. rewrite unsigned_lit in GA1 by lia.
  pose proof (know_nth _ _ _ _ 0%nat _ HK' eq_refl) as K8.
  pose proof (SB.kx_word asegs E' m' A1G_defs.vTHIS 8 4 (A1G_defs.V 24) K8) as B8'. rewrite ETHIS, unsigned_lit in B8' by lia.
  unfold A1G_defs.V in B8'. cbn [edenot] in B8'.
  pose proof (u_rngW (ev E' 24)) as R24.
  assert (E24 : ev E' 24 = Z_to_bv 64 (zlength (snd (scan d)))) by (apply bv_eq; rewrite GN; rewrite unsigned_lit; [reflexivity| lia]).
  rewrite E24 in B8'.
  destruct (scan d) as [ok idx] eqn:ES. cbn [fst snd] in *.
  assert (OK : ok = true) by (apply GC; exact R0). subst ok.
  pose proof (scan_S1OUT d idx ES) as S1O. destruct S1O as [NIX _ _ _ _ _].
  split; [|split].
  - apply rw_cells_ofA; [cbn; repeat split; exact I| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact B8'|].
    eapply wr_at_subA; [exact WRM'| lia| cbn; lia| cbn; lia].
  - apply rw_cells_ofA; [cbn; repeat split; exact I| cbn [cells_bytes cbytes]; rewrite app_nil_r; apply bytes_at_of_mbytesA; [exact G24| lia| cbn; lia]|].
    eapply wr_at_subA; [exact WRM'| lia| cbn; lia| cbn; lia].
  - assert (UL : length (u32bytes (idx ++ [zlength d; zlength d; 0])) = (4 * (length idx + 3))%nat)
      by (rewrite u32bytes_length, length_app; cbn [length]; lia).
    apply rw_cells_ofA; [cbn; split; [exact UL| exact I]| cbn [cells_bytes cbytes]; rewrite app_nil_r; apply bytes_at_of_mbytesA; [exact GM| lia| rewrite UL; unfold zlength in *; lia]|].
    eapply wr_at_subA; [exact WRS'| lia| cbn [cells_size csize]; clear - NSI NIX; unfold LEN in *; unfold zlength in *; lia| cbn; lia].
Qed.
End MAIN.
End CANSEC1.
