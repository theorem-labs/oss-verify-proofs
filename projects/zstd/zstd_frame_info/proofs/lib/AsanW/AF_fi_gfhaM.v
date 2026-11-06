(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import DrvAgree StrFun Stdio_pure.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg ABase RtCells AProto AMalloc_iface AHarness_iface AH_fi_iface AF_fi_kit AF_fi_chk.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
#[using="Type"] Lemma zrange_allM : forall (P : Z -> bool) n, forallb P (map Z.of_nat (seq 0 n)) = true -> forall c, 0 <= c < Z.of_nat n -> P c = true.
Proof.
  intros P n H c Hc. apply (proj1 (forallb_forall _ _) H). apply in_map_iff. exists (Z.to_nat c). Local Ltac2 Set LiaHints.tbl := fun () => "0020=25492742081.629765743970.6000004008S2HcS2Hc".
split; [lia|]. apply in_seq. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma fhd_decompA : forall c, 0 <= c < 256 ->
  (Z.land c 3 = 0 \/ Z.land c 3 = 1 \/ Z.land c 3 = 2 \/ Z.land c 3 = 3)
  /\ (Z.shiftr c 6 = 0 \/ Z.shiftr c 6 = 1 \/ Z.shiftr c 6 = 2 \/ Z.shiftr c 6 = 3)
  /\ (Z.land c 32 = 0 \/ Z.land c 32 = 32) /\ (Z.land c 8 = 0 \/ Z.land c 8 = 8)
  /\ Z.land (Z.shiftr c 3) 24 = 8 * Z.shiftr c 6 /\ (c <? 64) = (Z.shiftr c 6 =? 0).
Proof.
  intros c Hc.
  pose proof (zrange_allM (fun c =>
     ((Z.land c 3 =? 0) || (Z.land c 3 =? 1) || (Z.land c 3 =? 2) || (Z.land c 3 =? 3))
     && ((Z.shiftr c 6 =? 0) || (Z.shiftr c 6 =? 1) || (Z.shiftr c 6 =? 2) || (Z.shiftr c 6 =? 3))
     && ((Z.land c 32 =? 0) || (Z.land c 32 =? 32)) && ((Z.land c 8 =? 0) || (Z.land c 8 =? 8))
     && (Z.land (Z.shiftr c 3) 24 =? 8 * Z.shiftr c 6) && (Bool.eqb (c <? 64) (Z.shiftr c 6 =? 0)))%bool 256 ltac:(vm_compute; reflexivity) c Hc) as H.
  cbn beta in H. rewrite !Bool.andb_true_iff, !Bool.orb_true_iff, !Z.eqb_eq in H. destruct H as (((((H1 & H2) & H3) & H4) & H5) & H6).
  apply Bool.eqb_prop in H6. split; [tauto|]. split; [tauto|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5| exact H6].
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma ckflag_small : forall c, 0 <= c < 256 -> 0 <= Z.shiftr (Z.shiftl c 61 mod 2^64) 63 <= 1.
Proof. intros c Hc. Local Ltac2 Set LiaHints.tbl := fun () => "0020=32982217803.351409119742.3000001002SS".
rewrite Z.shiftr_div_pow2 by lia. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Definition FHTABM : list Z := [0;0;0;0;0;0;0;0; 1;0;0;0;0;0;0;0; 2;0;0;0;0;0;0;0; 4;0;0;0;0;0;0;0;
                               0;0;0;0;0;0;0;0; 0;0;0;0;0;0;0;0; 0;0;0;0;0;0;0;0; 0;0;0;0;0;0;0;0;
                               0;0;0;0;0;0;0;0; 2;0;0;0;0;0;0;0; 4;0;0;0;0;0;0;0; 8;0;0;0;0;0;0;0]%Z.
#[using="Type"] Lemma fhtabM_bytes : forall m, mem_inv asegs m -> bytes_at asegs m AFI_DIDTAB (map (Z_to_bv 8) FHTABM).
Proof.
  intros m MI. apply ro_bytes_at. { exact MI. } { unfold AFI_DIDTAB. Local Ltac2 Set LiaHints.tbl := fun () => "0020=1121359246.3 36321585685.3000001002SS".
lia. } { cbn. unfold AFI_DIDTAB. lia. }
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma fhtabM_read : forall m k A, mem_inv asegs m -> 0 <= k < 12 -> A = AFI_DIDTAB + 8 * k ->
  ov_read_bytes asegs m (wa A) 8 = Some (map (Z_to_bv 8) (firstn 8 (skipn (Z.to_nat (8 * k)) FHTABM))).
Proof.
  intros m k A MI Hk ->.
  rewrite (bytes_at_read asegs m AFI_DIDTAB (map (Z_to_bv 8) FHTABM) (8 * k) 8 (fhtabM_bytes m MI)); [| lia| cbn; lia].
  f_equal. rewrite <- List.firstn_map, <- List.skipn_map. reflexivity.
Qed.

(* [comment removed for export] *)
Definition GSHC : list cell :=
  [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 249); C1 (Z_to_bv 8 249); C1 (Z_to_bv 8 249); C1 (Z_to_bv 8 249);
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 249); C1 (Z_to_bv 8 249); C1 (Z_to_bv 8 249); C1 (Z_to_bv 8 249)].
Definition GSC (m : amem) : Prop := rw_cells asegs m 2147467688 GSHC.
#[using="Type"] Lemma gsc_of_gshA : forall m, gshA m -> GSC m.
Proof.
  intros m G. unfold GSC. unfold harness_invA, GSH_ADDR in G.
  eapply rw_cells_recast; [exact G| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity].
Qed.
#[using="Type"] Lemma gshA_of_gsc : forall m, GSC m -> gshA m.
Proof.
  intros m G. unfold GSC in G. unfold harness_invA, GSH_ADDR.
  eapply rw_cells_recast; [exact G| cbn; repeat split; reflexivity| vm_compute; reflexivity| reflexivity].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sh_zero_in : forall m1 A B a, unpoisoned m1 A B -> A mod 8 = 0 -> (B - A) mod 8 = 0 -> A <= a < B -> B <= 2^47 ->
  ov_read_bytes asegs m1 (Z_to_bv 64 (Z.shiftr a 3 + 2147450880)) 1 = Some [Z_to_bv 8 0].
Proof.
  intros m1 A B a U A8 L8 Ha HB.
  replace (Z.shiftr a 3) with (Z.shiftr (a - a mod 8) 3) by (rewrite !Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; nia).
  apply (chk8_zero m1 A B (a - a mod 8) U); Z.div_mod_to_equations; nia.
Qed.

(* [comment removed for export] *)
Section MAINA.
  Variables (gp tp s11 : word) (F : bvmap 5 word) (fc : bv 32) (SP FF ZF S : Z) (bl : list Z) (mM : amem) (RNG : footprint).
  Notation n := (zlen bl).
  Notation shF := (Z.shiftr FF 3 + 2147450880).
  Notation SPA := ((SP - 128) - (SP - 128) mod 32).
  Notation W := [(ZF, ZF + 48)].
  Hypothesis PLR : Forall (fun c => 0 <= c < 256) bl.
  Hypothesis NB : n < 2^62.
  Hypothesis SB : 0 < S /\ S + n <= ATOP.
  Hypothesis ZA : ZF mod 8 = 0.
  Hypothesis ZB : AIMG_HI <= ZF /\ ZF + 48 <= ATOP /\ (ZF + 48 <= KLS \/ KHIGH <= ZF).
  Hypothesis SEPZ : S + n <= ZF \/ ZF + 48 <= S.
  Hypothesis USRC : unpoisoned mM S (S + n).
  Hypothesis UZF : unpoisoned mM ZF (ZF + 48).
  Hypothesis RS : rng RNG S n.
  Hypothesis RSS : rng RNG (Z.shiftr S 3 + 2147450880) (Z.shiftr (S + n - 1) 3 - Z.shiftr S 3 + 1).
  Hypothesis RZ : rng RNG ZF 48.
  Hypothesis RSZ : rng RNG (Z.shiftr ZF 3 + 2147450880) 6.
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RIS : rng RNG 0x7fffa000 0xbcc00.

  #[using="rc bl ZA"] Lemma ZA7 : Z.land ZF 7 = 0.
  Proof. change 7 with (2^3 - 1). Local Ltac2 Set LiaHints.tbl := fun () => "0010>29782367974.28000001S".
rewrite zb_land_mask by lia. change (2^3) with 8. exact ZA. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  Definition QX : machine_state -> Prop :=
    fun ms' => exists (r : Z) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x25 x26 x28 x29 x30 x31 : word) (m2 : amem) (j1 hb j2 : list byte),
      ms' = MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPA) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                     (Z_to_bv 64 FF) x19 x20 x21 x22 (Z_to_bv 64 FF) (Z_to_bv 64 shF) x25 x26 s11 x28 x29 x30 x31)
               F (Z_to_bv 64 0x801dc) fc None m2 (seg_rom asegs)
      /\ munch W mM m2 /\ wmono asegs mM m2 /\ mem_inv asegs m2
      /\ rw_cells asegs m2 ZF [CB 24 j1; CB 4 hb; CB 20 j2]
      /\ (r mod 2^64 = 0 -> exists h, hb = le4 (Z_to_bv 64 h) /\ 6 <= h <= n /\ h <= 18).

  (* [comment removed for export] *)
  #[using="Type"] Lemma xdone : forall m1 (r : Z) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x25 x26 x28 x29 x30 x31 : word) (j1 hb j2 : list byte),
    (r mod 2^64 = 0 -> exists h, hb = le4 (Z_to_bv 64 h) /\ 6 <= h <= n /\ h <= 18) ->
    rw_cells asegs m1 ZF [CB 24 j1; CB 4 hb; CB 20 j2] ->
    munch W mM m1 -> wmono asegs mM m1 -> mem_inv asegs m1 ->
    evtF asegs RNG QX
      (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPA) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FF) x19 x20 x21 x22 (Z_to_bv 64 FF) (Z_to_bv 64 shF) x25 x26 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x801dc) fc None m1 (seg_rom asegs)).
  Proof.
    intros until j2. intros RH CZ MU WM MI. apply evtF_done. unfold QX.
    exists r, x1, x5, x6, x7, x11, x12, x13, x14, x15. exists x16, x17, x19, x20, x21, x22, x25, x26, x28, x29. exists x30, x31, m1, j1, hb. exists j2.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact CZ| exact RH].
  Qed.

  (* [comment removed for export] *)
  #[using="rc SB ZB SEPZ USRC"] Lemma src_unp : forall m1, munch W mM m1 -> unpoisoned m1 S (S + n).
  Proof.
    intros m1 MU. pose proof atop_range as ATR. pose proof USRC as (U0 & U1 & _).
    eapply unpoisoned_munch; [exact USRC| exact MU|].
    cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF, AIMG_HI, KLS, KHIGH in *. split; [| exact I]. Local Ltac2 Set LiaHints.tbl := fun () => "0010>45645051205.3200000@S2SB2ZB4SEPZ3ATR".
OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
  #[using="rc bl ZA ZB UZF"] Lemma zfh_unp : forall m1, munch W mM m1 -> unpoisoned m1 ZF (ZF + 48).
  Proof.
    intros m1 MU. pose proof atop_range as ATR.
    eapply unpoisoned_munch; [exact UZF| exact MU|].
    cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF, AIMG_HI, KLS, KHIGH in *. split; [| exact I]. Local Ltac2 Set LiaHints.tbl := fun () => "0010>45643269860.30000007S2ZA2ZB".
OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
  (* [comment removed for export] *)
  #[using="rc SB ZB SEPZ USRC"] Lemma src_chk : forall m1 a, munch W mM m1 -> S <= a < S + n ->
    exists b, ov_read_bytes asegs m1 (Z_to_bv 64 (Z.shiftr a 3 + 2147450880)) 1 = Some [b]
              /\ (sval b = 0 \/ (0 < sval b <= 7 /\ a mod 8 < sval b)) /\ -128 <= sval b <= 127.
  Proof. intros m1 a MU Ha. apply (chkB m1 S (S + n) a (src_unp m1 MU)); lia. Qed.
  (* [comment removed for export] *)
  #[using="rc bl ZA ZB UZF"] Lemma zfh_sh_zero : forall m1 a, munch W mM m1 -> ZF <= a < ZF + 48 ->
    ov_read_bytes asegs m1 (Z_to_bv 64 (Z.shiftr a 3 + 2147450880)) 1 = Some [Z_to_bv 8 0].
  Proof.
    intros m1 a MU Ha. pose proof atop_range as ATR.
    apply (sh_zero_in m1 ZF (ZF + 48) a (zfh_unp m1 MU)); [exact ZA| replace (ZF + 48 - ZF) with 48 by lia; reflexivity| exact Ha| lia].
  Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma fhtab_read_at : forall m1 k A, mem_inv asegs m1 -> 0 <= k < 12 -> A = AFI_DIDTAB + 8 * k ->
    ov_read_bytes asegs m1 (wa A) 8 = Some (map (Z_to_bv 8) (firstn 8 (skipn (Z.to_nat (8 * k)) FHTABM))).
  Proof. intros m1 k A MI1 Hk E. apply fhtabM_read; assumption. Qed.

  (* [comment removed for export] *)
  Definition zcellA := Z_to_bv 64 0.
  Definition ZCELLS : list cell :=
    [C8 zcellA; C8 zcellA; C4 zcellA; C4 zcellA; C4 zcellA; C4 zcellA; C4 zcellA; C4 zcellA; C8 zcellA].
  #[using="Type"] Lemma zcells_of_memset : forall m1, rw_cells asegs m1 ZF [CB 48 (repeat (Z_to_bv 8 0) 48)] -> rw_cells asegs m1 ZF ZCELLS.
  Proof.
    intros m1 H. eapply rw_cells_recast; [exact H| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Definition decA_at (m1 : amem) (x1 x5 x6 x7 x11 x14 x16 x17 x28 x29 x30 x31 : word) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPA) (Z_to_bv 64 (S + 4)) x11 (Z_to_bv 64 5) (Z_to_bv 64 (Znth 4 bl))
             x14 (Z_to_bv 64 5) x16 x17 (Z_to_bv 64 FF) (Z_to_bv 64 ZF) (Z_to_bv 64 S) (Z_to_bv 64 n) (Z_to_bv 64 0) (Z_to_bv 64 FF) (Z_to_bv 64 shF)
             (Z_to_bv 64 2147450880) (Z_to_bv 64 5) s11 x28 x29 x30 x31)
       F (Z_to_bv 64 0x80398) fc None m1 (seg_rom asegs).
  Definition dec_okA (D : Z) : Prop := forall m1 x1 x5 x6 x7 x11 x14 x16 x17 x28 x29 x30 x31,
    5 <= n -> Z.land (Znth 4 bl) 3 = D ->
    rw_cells asegs m1 ZF ZCELLS ->
    bytes_at asegs m1 S (map (Z_to_bv 8) bl) ->
    GSC m1 ->
    munch W mM m1 -> wmono asegs mM m1 -> mem_inv asegs m1 ->
    evtF asegs RNG QX (decA_at m1 x1 x5 x6 x7 x11 x14 x16 x17 x28 x29 x30 x31).

  (* [comment removed for export] *)
  Definition dec_okB (D SS : Z) : Prop := forall m1 x1 x5 x6 x7 x11 x14 x16 x17 x28 x29 x30 x31,
    5 <= n -> Z.land (Znth 4 bl) 3 = D -> Z.land (Znth 4 bl) 32 = SS ->
    rw_cells asegs m1 ZF ZCELLS ->
    bytes_at asegs m1 S (map (Z_to_bv 8) bl) ->
    GSC m1 ->
    munch W mM m1 -> wmono asegs mM m1 -> mem_inv asegs m1 ->
    evtF asegs RNG QX (decA_at m1 x1 x5 x6 x7 x11 x14 x16 x17 x28 x29 x30 x31).

  (* [comment removed for export] *)
  Definition mainA_at (m0 : amem) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPA) (Z_to_bv 64 ZF) x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 FF) (Z_to_bv 64 ZF) (Z_to_bv 64 S) (Z_to_bv 64 n) (Z_to_bv 64 0) (Z_to_bv 64 FF) (Z_to_bv 64 shF)
             (Z_to_bv 64 2147450880) (Z_to_bv 64 5) s11 x28 x29 x30 x31)
       F (Z_to_bv 64 0x80310) fc None m0 (seg_rom asegs).
  Definition main_okA : Prop := forall m0 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    5 <= n ->
    rw_cells asegs m0 ZF [CB 48 (repeat (Z_to_bv 8 0) 48)] ->
    bytes_at asegs m0 S (map (Z_to_bv 8) bl) ->
    GSC m0 ->
    munch W mM m0 -> wmono asegs mM m0 -> mem_inv asegs m0 ->
    evtF asegs RNG QX (mainA_at m0 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31).
End MAINA.
End CANSEC1.
