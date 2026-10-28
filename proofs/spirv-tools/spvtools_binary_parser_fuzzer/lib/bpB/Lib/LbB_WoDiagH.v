From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps SymExec3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtB_Td.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_ContStmt LbB_PrsStmt LbB_FKit LbB_Own LbB_PmBase LbB_Call LbB_Bridge.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_DStat LbB_SR LbB_WoGen LbB_WoDefs LbB_WoKit LbB_PiStmt LbB_PiInit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRepFacts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BllocRep BG_Free6.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_WoBP LbB_PmExit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_DiagStmt LbB_WoDiagP LbB_WoKit2 LbB_WoDiagF LbB_PmMagW LbB_PmHTK.
Import ListNotations.

Open Scope Z_scope.

#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section WDH.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma w_junk : forall (e : went H) ff fp XSc s LB m a n, wpre H e -> winv H e ff fp XSc s LB m -> ff <= a -> a + n <= ff + WO_FLAGP -> 0 <= n -> exists junk : list byte, rw_cells asegs m a [CB (Z.to_nat n) junk].
  Proof.
    intros e ff fp XSc s LB m a n HP HI Ha Hb Hn.
    pose proof HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & W & _).
    destruct (hdr_geo H e ff fp XSc s LB m HP HI) as (_ & G1 & _).
    apply LbB_WoGen.wr_at_rw_cells; [eapply LbB_PmCall.wr_at_sub; [exact W | exact Ha | exact Hb | exact Hn] | lia | exact Hn].
  Qed.

  Lemma w_acc : forall m a n, addressable m a n -> a + n <= 2 ^ 47 -> accessible m a n.
  Proof.
    intros m a n (Hn & A0 & A8 & (B0 & B1 & B) & _) Hhi.
    split; [lia|]. split; [unfold AAPP_HI; lia|]. intros x Hx.
    pose proof (Z.div_mod a 8 ltac:(lia)) as Da. rewrite A8, Z.add_0_r in Da.
    assert (Ex : x = (x - a) + a / 8 * 8) by lia.
    assert (Q : 0 <= (x - a) / 8 <= n / 8) by (split; [apply Z.div_pos | apply Z.div_le_mono]; lia).
    assert (SX : sh x = sh a + Z.of_nat (Z.to_nat ((x - a) / 8))).
    { rewrite Z2Nat.id by lia. unfold sh. rewrite Ex at 1. rewrite Z.div_add by lia. lia. }
    assert (MX : x mod 8 = (x - a) mod 8) by (rewrite Ex at 1; apply Z.mod_add; lia).
    pose proof (shadow_of_length n Hn) as SL. unfold nsh in SL.
    assert (Q2 : (x - a) / 8 < (n + 7) / 8) by (clear - Hx; Z.div_mod_to_equations; lia).
    assert (LEN : (Z.to_nat ((x - a) / 8) < length (shadow_of n))%nat) by lia.
    destruct (Z_lt_le_dec ((x - a) / 8) (n / 8)) as [LT|GE].
    - exists 0. split; [lia|]. split; [|left; reflexivity].
      rewrite SX, (B _ LEN). apply shadow_of_nth_full; lia.
    - assert (R : (x - a) mod 8 + 1 <= n mod 8) by (clear - Hx Q GE; Z.div_mod_to_equations; lia).
      pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as NB. pose proof (Z.mod_pos_bound (x - a) 8 ltac:(lia)) as XB.
      exists (n mod 8). split; [lia|]. split; [|right; lia].
      rewrite SX, (B _ LEN). replace (Z.to_nat ((x - a) / 8)) with (Z.to_nat (n / 8)) by (f_equal; lia).
      apply shadow_of_nth_last; lia.
  Qed.

  Lemma w_shvis : forall (e : went H) ff fp XSc s LB m a n, wpre H e -> winv H e ff fp XSc s LB m -> ff <= a -> 0 <= n -> a + n <= ff + 4096 -> shvis m a (a + n).
  Proof.
    intros e ff fp XSc s LB m a n HP HI Ha Hn Hb.
    pose proof HI as (RF & _).
    destruct (wframe_bounds H e ff fp XSc s LB m HP HI) as (F0 & _).
    pose proof (ah_frm_shvis H HH _ m (6, ff, fp) RF (or_introl eq_refl)) as SV.
    unfold ff_addr, ff_class in SV. cbn [fst snd] in SV.
    assert (FS : fsz 6 = 4096) by reflexivity. rewrite FS in SV.
    eapply shvis_sub; [exact SV | lia | lia | lia | lia | lia].
  Qed.

  Lemma w_fld_of_cells8 : forall m p v, rw_cells asegs m p [C8 (Z_to_bv 64 v)] -> 0 <= v < 2 ^ 64 -> fldA m p 8 v.
  Proof.
    intros m p v Hc _. unfold fldA, fld.
    pose proof (rw_cells_read asegs m p _ 0%nat _ Hc eq_refl) as RD. replace (p + Z.of_nat 0) with p in RD by lia.
    rewrite <- LbB_Conv.rdn_of_ov. exact RD.
  Qed.

  Lemma w_cells8_of_fld : forall m p v, fldA m p 8 v -> wr_at asegs m p 8 -> rw_cells asegs m p [C8 (Z_to_bv 64 v)].
  Proof.
    intros m p v HF HW. pose proof HW as (HW0 & HW1 & _). split; [|exact HW].
    split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    apply LbB_Conv.bytes_at_of_rdn; [lia | rewrite BMem.length_le8; lia | rewrite BMem.length_le8; exact HF].
  Qed.

  Lemma w_u64arr3 : forall m p v0 v1 v2, fldA m p 8 v0 -> fldA m (p + 8) 8 v1 -> fldA m (p + 16) 8 v2 -> wr_at asegs m p 24 -> 0 <= v0 < 2 ^ 64 -> 0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 -> u64arr asegs m p [Z_to_bv 64 v0; Z_to_bv 64 v1; Z_to_bv 64 v2].
  Proof.
    intros m p v0 v1 v2 F0 F1 F2 W _ _ _. pose proof W as (W0 & W1 & _).
    split; [|exact W].
    cbn [u64s]. rewrite app_nil_r.
    apply BMem.bytes_at_app. rewrite BMem.length_le8. change (Z.of_nat 8) with 8.
    split; [apply LbB_Conv.bytes_at_of_rdn; [lia | rewrite BMem.length_le8; lia | rewrite BMem.length_le8; exact F0]|].
    apply BMem.bytes_at_app. rewrite BMem.length_le8. change (Z.of_nat 8) with 8. replace (p + 8 + 8) with (p + 16) by lia.
    split; [apply LbB_Conv.bytes_at_of_rdn; [lia | rewrite BMem.length_le8; lia | rewrite BMem.length_le8; exact F1]|].
    apply LbB_Conv.bytes_at_of_rdn; [lia | rewrite BMem.length_le8; lia | rewrite BMem.length_le8; exact F2].
  Qed.

  Lemma w_zero_fld : forall m p n k, rw_cells asegs m p [CB n (poison_bytes n 0)] -> 0 <= k -> k + 8 <= Z.of_nat n -> fldA m (p + k) 8 0.
  Proof.
    intros m p n k ((_ & B) & _) Hk Hn. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
    unfold fldA, fld.
    pose proof (BMem.bytes_at_rdn asegs m p _ (Z.to_nat k) 8 B) as R.
    unfold poison_bytes in R. rewrite repeat_length in R. specialize (R ltac:(lia)).
    rewrite Z2Nat.id in R by lia. unfold wa in R.
    etransitivity; [exact R|].
    rewrite LbB_WoGen.skipn_repeat', LbB_WoGen.firstn_repeat'.
    replace (Nat.min 8 (n - Z.to_nat k)) with 8%nat by lia.
    vm_compute. reflexivity.
  Qed.

  Lemma w_str : forall m p (j : list byte), fldA m p 2 0 -> wr_at asegs m p 2 -> rw_cells asegs m (p + 2) [CB 22 j] -> rw_cells asegs m p [C2 (Z_to_bv 64 0); CB 22 j].
  Proof.
    intros m p j F W C. pose proof W as (W0 & W1 & _).
    change [C2 (Z_to_bv 64 0); CB 22 j] with ([C2 (Z_to_bv 64 0)] ++ [CB 22 j]).
    apply rw_cells_app. split; [|exact C].
    split; [|exact W].
    split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    replace (le2 (Z_to_bv 64 0)) with (word_to_le_bytes 2 (Z_to_bv 64 0)) by (vm_compute; reflexivity).
    apply LbB_Conv.bytes_at_of_rdn; [lia | change (length (word_to_le_bytes 2 (Z_to_bv 64 0))) with 2%nat; lia | change (length (word_to_le_bytes 2 (Z_to_bv 64 0))) with 2%nat; exact F].
  Qed.
End WDH.
