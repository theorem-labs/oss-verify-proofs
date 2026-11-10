(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Trevor Hansen, 2026-11: plain_find_high is made from rn_find_segment_high of UI39, for libtasn1's plain image; the rest of this file is new. *)
(* libtasn1's LLVMFuzzerTestOneInput meets cgif_rgb_fuzzer's library contract (YL0e.lib_contract_all) on
   the plain image: the contract cgif's driver proof (YL0f.src2_realizes_spec) takes for the code it
   calls.  The behaviour comes from the cjson-style harness proof (H.GldUbsan.harness_plain); runs
   carry over through OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.B.Runs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.Lib.PropExec.
Module PropExec := OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.Lib.PropExec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.B Require Import RegsExt Runs.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YK1j YK11 YK0p YK15 YQ0b YN06 YN05 YP0c YL0e YH04 YH07 YH06 YL0o YO0d.
Require OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.H.GldUbsan OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.H.GldHarness.
Require OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.Lib.Frame.
Require OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.Lib.Mem.
Require OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.Lib.MState.
Module H := OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.H.GldUbsan.
Module CJF := OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.Lib.Frame.
Module CJM := OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.Lib.Mem.
Module CJS := OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.Lib.MState.
Import ListNotations.
Local Open Scope Z_scope.

Lemma with_vmmaps_self : forall md, md = with_vmmaps (m_vmmaps md) md.
Proof. intros [fd [h lz mt] io fs pr lim tm]. reflexivity. Qed.

(* no segment of libtasn1's plain image reaches 0x4e000 *)
Lemma plain_find_high : forall a n, 0x4e000 <= a -> 0 < n -> find_segment src2segs a n = None.
Proof.
  intros a n Ha Hn. destruct (find_segment src2segs a n) as [sg|] eqn:Hf; [|reflexivity]. exfalso.
  pose proof (YK1j.find_segment_in _ _ _ _ Hf) as Hin. pose proof (YK1j.find_segment_range _ _ _ _ Hf) as [Hlo Hhi].
  assert (Hall : forallb (fun sg => Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <=? 0x4e000) src2segs = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) Hall sg Hin) as Hb. cbn beta in Hb. apply Z.leb_le in Hb. lia.
Qed.

(* above the image, a byte that is writable is in the overlay, so it reads *)
Lemma high_writable_reads : forall (m : word -> option byte) a, 0x4e000 <= a < 2 ^ 64 ->
  wview src2segs m (Z_to_bv 64 a) <> None -> exists b, m (Z_to_bv 64 a) = Some b.
Proof.
  intros m a Ha Hw. unfold wview in Hw. destruct (m (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity|].
  rewrite CJS.unsigned_lit, plain_find_high in Hw by lia. exfalso. apply Hw. reflexivity.
Qed.

Lemma nth_map_seq : forall {T} (f : nat -> T) N i, (i < N)%nat -> nth_error (map f (seq 0 N)) i = Some (f i).
Proof.
  intros T f N i H. replace (f i) with (f (0 + i)%nat) by reflexivity. revert i H. generalize 0%nat as s. induction N as [|N IH]; intros s i H; [lia|].
  destruct i as [|i]; cbn; [f_equal; f_equal; lia|]. rewrite IH by lia. f_equal. f_equal. lia.
Qed.

Lemma getr_of_rext : forall R1 R2 r, rext R1 R2 -> getr R2 r = getr R1 r.
Proof. intros R1 R2 r H. unfold getr. destruct (bv_eqb r 0) eqn:E; [reflexivity|]. symmetry. apply H. exact E. Qed.

Section P.
Context {rc : RunCeil}.
Variable API : AllocAPI src2_msyms.

Theorem tasn1_lib_plain : lib_contract_all src2_msyms API LIBPC RA_LIB EMPTY LIB_STACK_RGB.
Proof.
  intros fx L A regs mem md p n PRE FZ.
  destruct PRE as (HMR & HWF & HBD & HID & Hra & Hal & Hstk & Hsp63 & Hwr & Htp & Herr & Ha0 & Ha1 & Hp & Hro).
  pose proof (aa_laws API) as LW.
  pose proof alloc_ceiling_value as (HC & _). change (YN05.CEIL_MIN) with 140735332483072 in HC.
  assert (ELIB : LIBPC = 0x12a54) by (vm_compute; reflexivity).
  assert (ERA : RA_LIB = 0x12950) by (vm_compute; reflexivity).
  assert (EEMP : EMPTY = 0x2d0e0) by (vm_compute; reflexivity).
  assert (ESTK : LIB_STACK_RGB = 61440) by reflexivity.
  assert (ESEG : ms_segs src2_msyms = src2segs) by reflexivity.
  set (g k := getr regs (Z_to_bv 5 k)).
  set (spv := spZ regs) in *.
  (* the input: n bytes at p, read from memory *)
  set (der := map (fun i : nat => match CJM.mrd src2segs mem (CJM.wa (p + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end)
                  (seq 0 (Z.to_nat n))).
  assert (Hlen : length der = Z.to_nat n) by (unfold der; rewrite length_map, length_seq; reflexivity).
  assert (Hpn : (n = 0 /\ p = 0x2d0e0) \/ (0 < n /\ 4096 <= p /\ p + n <= alloc_ceiling /\
                   forall i, 0 <= i < n -> exists b, mem (Z_to_bv 64 (p + i)) = Some b)).
  { destruct Hp as [(-> & ->) | (Hn & q & Hq & <-)]; [left; rewrite EEMP; split; reflexivity|right].
    pose proof (mr_blocks_range _ _ LW L A mem md q n HMR Hq) as (R1 & R2).
    split; [exact Hn|]. split; [exact R1|]. split; [exact R2|].
    intros i Hi. exact (proj1 (mr_blocks _ _ LW L A mem md q n i HMR Hq Hi)). }
  assert (Hn0 : 0 <= n) by (destruct Hpn as [(-> & _)|(? & _)]; lia).
  assert (Hpz : 0 < p < 2 ^ 64) by (destruct Hpn as [(_ & ->)|(_ & ? & ? & _)]; lia).
  assert (Hpe : p + n <= alloc_ceiling) by (destruct Hpn as [(-> & ->)|(_ & _ & ? & _)]; lia).
  assert (DER : CJM.bytes_at src2segs mem p der).
  { unfold CJM.bytes_at. split; [lia|]. split; [rewrite Hlen; lia|].
    intros i Hi. rewrite Hlen in Hi. unfold der. rewrite nth_map_seq by exact Hi. cbn beta.
    destruct Hpn as [(-> & _)|(_ & _ & _ & HB)]; [cbn in Hi; lia|].
    destruct (HB (Z.of_nat i) ltac:(lia)) as (b & Hb).
    assert (HM : CJM.mrd src2segs mem (CJM.wa (p + Z.of_nat i)) = Some b) by (unfold CJM.mrd, CJM.wa; rewrite Hb; reflexivity).
    rewrite HM. reflexivity. }
  (* the stack: sp is 16-aligned, far above the image and the heap *)
  assert (Hspr : 0 <= spv < 2 ^ 64) by (unfold spv, spZ; apply bv_unsigned_in_range).
  assert (STK : CJF.stk src2segs mem (spv - 16) spv).
  { unfold CJF.stk. split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at src2segs mem a) by (apply Hwr; rewrite ESTK; lia).
    unfold writable_at in W. split; [exact W|].
    destruct (high_writable_reads mem a ltac:(lia) W) as (b & Hb). exists b. unfold CJM.mrd, CJM.wa. rewrite Hb. reflexivity. }
  (* the registers, as the harness proof states them *)
  assert (G2 : bv_unsigned (g 2) = spv) by reflexivity.
  assert (G10 : g 10 = Z_to_bv 64 p) by exact Ha0.
  assert (G11 : g 11 = Z_to_bv 64 (Z.of_nat (length der))) by (rewrite Hlen, Z2Nat.id by lia; exact Ha1).
  assert (U10 : bv_unsigned (g 10) = p) by (rewrite G10; apply CJS.unsigned_lit; lia).
  pose proof (H.harness_plain (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) (g 7) (g 8) (g 9) (g 10) (g 11) (g 12) (g 13) (g 14) (g 15)
                (g 16) (g 17) (g 18) (g 19) (g 20) (g 21) (g 22) (g 23) (g 24) (g 25) (g 26) (g 27) (g 28) (g 29) (g 30) (g 31)
                fp_regs fp_csr mem der (spv - 16)) as HH.
  rewrite G2, U10 in HH.
  specialize (HH STK ltac:(lia) Hal DER ltac:(lia) G11 ltac:(left; lia)).
  destruct (evt_cg _ _ _ HH) as (s1' & HS1 & HP1).
  (* the same run from cgif's register file *)
  assert (HE : msext (CJS.MS (canon regs) fp_regs (Z_to_bv 64 0x12a54) fp_csr None mem (PropExec.seg_rom src2segs))
                     (mkst regs (Z_to_bv 64 LIBPC) mem (seg_rom (ms_segs src2_msyms)))).
  { unfold msext, mkst, CJS.MS; cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom].
    rewrite ELIB. repeat split; try reflexivity. apply canon_rext. }
  destruct (msteps_ext _ _ _ HS1 _ HE) as (s2' & HS2 & HE2).
  destruct (mr_model _ _ LW L A mem md HMR) as (Mh & Ml & Mm).
  unfold lib_contract.
  eapply SR_msteps; [exact Mh | exact Ml | exact HS2 |].
  apply SR_ret.
  destruct HP1 as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & MU & WM & _ & _).
  destruct s2' as [r2 f2 pc2 sv2 rv2 fc2 mm2 ro2].
  destruct HE2 as (HR & HF & HPc & HSv & HRv & HFc & HM & HRo); cbn [CJS.MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *.
  subst f2 pc2 sv2 rv2 fc2 mm2 ro2.
  (* memory outside the harness's 16-byte frame is unchanged *)
  assert (UNCH : forall a, 0 <= a < 2 ^ 64 -> (a < spv - 16 \/ spv <= a) -> m' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hout. apply MU. cbn [CJF.outside]. rewrite CJS.unsigned_lit by lia. split; [|exact I]. unfold g in *. lia. }
  assert (UMB : forall a, 0 <= a < 2 ^ 64 -> (a < spv - 16 \/ spv <= a) -> mbyte src2segs m' a = mbyte src2segs mem a)
    by (intros a Ha Hout; unfold mbyte; rewrite (UNCH a Ha Hout); reflexivity).
  assert (UWR : forall a, 0 <= a < 2 ^ 64 -> (a < spv - 16 \/ spv <= a) -> (writable_at src2segs mem a <-> writable_at src2segs m' a))
    by (intros a Ha Hout; unfold writable_at, wview; rewrite (UNCH a Ha Hout); tauto).
  rewrite ESTK in Hstk, Hwr.
  exists fx, L, A, r2, m', md. split; [|split; [exact FZ|]].
  { (* the final state returns to RA_LIB *)
    assert (G1 : g 1 = Z_to_bv 64 RA_LIB) by exact Hra.
    assert (RP : CJS.ret_pc (Z_to_bv 64 0x12950) = Z_to_bv 64 0x12950) by (apply bv_eq; vm_compute; reflexivity).
    unfold mkst. rewrite G1, ERA, RP. reflexivity. }
  try rewrite ESEG.
  pose proof (mr_owned_low _ _ LW) as OWN.
  refine (conj _ (conj HWF (conj HBD (conj HID (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))).
  - (* the allocator invariant: nothing it owns is in the frame *)
    eapply (mr_frame _ _ LW L A mem m' md md HMR); try reflexivity; try assumption.
    + intros a Ha. pose proof (OWN L A mem md a HMR Ha). apply UMB; lia.
    + intros a Ha (b & Hb). pose proof (OWN L A mem md a HMR Ha). exists b. rewrite UNCH by lia. exact Hb.
    + intros q k i Hq Hi. destruct (mr_blocks _ _ LW L A mem md q k i HMR Hq Hi) as ((b & Hb) & H1 & H2 & _).
      exists b. rewrite UNCH by lia. exact Hb.
  - (* a0 = 0 *)
    rewrite (getr_of_rext _ _ _ HR). reflexivity.
  - (* callee-saved registers hold their values *)
    intros r Hr. rewrite (getr_of_rext _ _ _ HR).
    unfold callee_saved in Hr.
    assert (r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end; subst r; reflexivity.
  - exists (m_vmmaps md). apply with_vmmaps_self.
  - intros q k Hq. exists q. split; [exact Hq | reflexivity].
  - (* above the heap and outside the scratch area: unchanged *)
    intros a Ha Hns. unfold lib_scratch in Hns. assert (Hout : a < spv - 16 \/ spv <= a) by (unfold spv in *; lia).
    split; [apply UMB; lia | apply UWR; lia].
  - (* the image: below the heap, unchanged *)
    intros a Ha _ _ _. pose proof (src2_img_range a Ha). split; [apply UMB; lia | apply UWR; lia].
  - (* user blocks: unchanged *)
    intros q k i Hq _ Hi. destruct (mr_blocks _ _ LW L A mem md q k i HMR Hq Hi) as (_ & H1 & H2 & _). apply UMB; lia.
  - (* the scratch area stays writable *)
    intros a [Ha | Ha]; unfold writable_at; apply WM; [apply Hwr; exact Ha | apply Herr; exact Ha].
Qed.
End P.
