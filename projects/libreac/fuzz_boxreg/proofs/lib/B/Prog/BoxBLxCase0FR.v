(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v, with its module paths and module names changed; 909 of its 980 lines of code are new or changed and 860 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/B/Prog/BoxBLxCase0TN.v; 74 of its 118 lines of code are new or changed and 936 lines of the source are left out. *)
(* Case op & 3 = 0 of the B walk of LLVMFuzzerTestOneInput, piece FR -> K: from the cut C0_FR (0x808f8, free (name)
   returned) `addi a0, zero, -1; srli s8, a0, 0x20` sets s8 = 2 ^ 32 - 1 (ren = -1) and `j 0x208` reaches the cut LI_K
   (0x80b08). No call and no store: the run's state has no region, so the memory stays the cut's (frame_of over no
   region) and every register but a0 and s8 keeps its value. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow PaJournal BoxBase YC4b.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa BoxBPaLib BoxBFrame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import YC1g YC1h BoxBCJ BoxBReadName.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBLxDefs BoxBLxSeat BoxBLxCase0Defs.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg read_name_c LLVMFuzzerTestOneInput_case0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.


Definition c0fr_SB : Z := 0x7fff8000.
Definition c0fr_Bspan : Z * Z := (c0fr_SB, c0fr_SB + 2 ^ 44 - 1).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HY : lx_hyps B MT.

Let LAWS := lh_laws B MT HY.

(* A machine state at a cut, as the engine's entry state. *)
Lemma c0fr_shape : forall pc (W : world SEGS) ms,
  ms_pc_val ms = w64 (BASE + pc) -> ms_resv ms = None -> ms_svc_pending ms = None -> ms_rom ms = seg_rom SEGS ->
  ms_fregs ms = fp_regs -> ms_fcsr ms = fp_csr ->
  restrict (w_H W) ms = mkst (ms_regs ms) (Z_to_bv 64 (BASE + pc)) (mrestrict (w_H W) (ms_mem ms)) (seg_rom SEGS).
Proof.
intros pc W ms Hpc Hresv Hpend Hrom Hfregs Hfcsr.
destruct ms as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0].
cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem] in Hpc, Hresv, Hpend, Hrom, Hfregs, Hfcsr.
subst. reflexivity.
Qed.

(* A register the run left as it was: its symbolic value is its own atom. *)
Lemma c0fr_reg : forall E ss H ms (regs3 : bvmap 5 word) (x : bv 5) n,
  E = Eimg (Ereg regs3 []) -> st_ok_pi SEGS VAL E ss (restrict H ms) ->
  sr_get (ss_regs ss) x = SOff n 0 -> Z.of_nat n = bv_unsigned x -> getr (ms_regs ms) x = getr regs3 x.
Proof.
  intros E ss H ms regs3 x n HE HS Hx Hn. rewrite (st_ok_pi_restrict_reg _ _ _ _ x HS), Hx. cbn [sv_denot].
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned, HE. apply ew_Eimg_Ereg_nat. exact Hn.
Qed.

Theorem c0_fr : forall POST i, lx_from B MT POST (LI_K B MT i) -> lx_from B MT POST (C0_FR B MT i).
Proof.
  intros POST i HK cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HC.
  destruct HC as (pos & r & fab & op & bs & bs' & HCOM & Hk & Hacc & Hblk & Hcur & Hreg' & Hinv' & Hfab' & Hkept).
  destruct HCOM as (HBD & Hi & Hprev & Hinv & Hfab & Hpos & Hop & Hop3 & Hsl & S58 & S48 & R20 & R21 & R27).
  pose proof HBD as (Hpc & Hresv & Hsvc & Hrom & Hfreg & Hfcsr & HREGS & HSAVED & HSH & HFLAG & HS10 & HS18 & HS80 & HINP).
  pose proof HREGS as (G2 & G8 & G9 & G3 & G4 & G18 & G22).
  set (E := Eimg (Ereg (ms_regs ms3) [])).
  assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
  assert (HS : st_ok_pi SEGS VAL E (mkSS C0P_FR sr_atoms [] None (mkFacts [] [] [])) (restrict (w_H W3) ms3)).
  { rewrite (c0fr_shape C0P_FR W3 ms3 Hpc Hresv Hsvc Hrom Hfreg Hfcsr).
    apply pa_entry_st_ok_full; [apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | apply Forall_nil | cbn; exact I
      | split; [exact I | split; exact I]]. }
  assert (SHOK : sh_ok SEGS (SLit c0fr_SB) [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
  pose (RUNTO := paj_run_to B LAWS).
  (* 0x808f8 addi a0, zero, -1; srli s8, a0, 0x20; j 0x208: at LP_K *)
  paj_run_to_tok RUNTO HS HJ SHOK c0fr_Bspan LP_K; [apply awr_ok_nil |].
  pose proof (frame_of_read_only E [] (ms_mem ms3) (ms_mem ms) eq_refl HF) as HM.
  assert (HKP : forall rs, lx_keep cx fp W3 rs (ms_mem ms3) (ms_mem ms)) by (intros rs a _; rewrite HM; reflexivity).
  pose proof (st_ok_pi_restrict_mkst (w_H W3) _ _ ms HS eq_refl) as Hshape. cbn [ss_pc] in Hshape.
  assert (KR : forall (x : bv 5) n, Z.of_nat n = bv_unsigned x -> (n <> 0 /\ n <> 10 /\ n <> 24)%nat ->
    getr (ms_regs ms) x = getr (ms_regs ms3) x).
  { intros x n Hn Hne. apply (c0fr_reg E _ _ ms (ms_regs ms3) x n eq_refl HS); [|exact Hn].
    pose proof (bv_unsigned_in_range 5 x) as Hx. change (bv_modulus 5) with 32 in Hx.
    assert (Hn32 : (n < 32)%nat) by lia.
    replace x with (Z_to_bv 5 (Z.of_nat n)) by (rewrite Hn; apply Z_to_bv_bv_unsigned).
    clear Hn Hx. destruct Hne as (N0 & N10 & N24).
    do 32 (destruct n as [|n]; [first [exfalso; lia | reflexivity] |]). lia. }
  prreg HS (24%bv : bv 5) Q24.
  apply (HK cx fp k acc ly3 S3 W3 ms _ HB HJ HFR HMO).
  exists (c0_pos2 (lc_pl cx) pos), r, fab, (-1), bs, bs'.
  split.
  { split; [rewrite Hshape; reflexivity|]. split; [rewrite Hshape; reflexivity|]. split; [rewrite Hshape; reflexivity|].
    split; [rewrite Hshape; reflexivity|]. split; [rewrite Hshape; reflexivity|]. split; [rewrite Hshape; reflexivity|].
    split.
    { split; [rewrite (KR 2%bv 2%nat) by (reflexivity || lia); exact G2|].
      split; [rewrite (KR 8%bv 8%nat) by (reflexivity || lia); exact G8|].
      split; [rewrite (KR 9%bv 9%nat) by (reflexivity || lia); exact G9|].
      split; [rewrite (KR 3%bv 3%nat) by (reflexivity || lia); exact G3|].
      split; [rewrite (KR 4%bv 4%nat) by (reflexivity || lia); exact G4|].
      split; [rewrite (KR 18%bv 18%nat) by (reflexivity || lia); exact G18|].
      rewrite (KR 22%bv 22%nat) by (reflexivity || lia); exact G22. }
    split; [exact (lx_saved_keep B MT cx fp W3 HB [] ms3 ms (HKP []) HSAVED)|].
    split; [apply (lx_shadow_keep cx fp W3 [] ms3 ms _ (HKP [])); [vm_compute; discriminate | exact HSH]|].
    split; [exact (lx_flag_keep cx fp W3 [] ms3 ms (HKP []) HFLAG)|].
    split; [apply (lx_slot_keep B MT cx fp W3 HB [] ms3 ms _ _ (HKP [])); [lia | lia | exact HS10]|].
    split; [apply (lx_slot_keep B MT cx fp W3 HB [] ms3 ms _ _ (HKP [])); [lia | lia | exact HS18]|].
    split; [apply (lx_slot_keep B MT cx fp W3 HB [] ms3 ms _ _ (HKP [])); [lia | lia | exact HS80]|].
    exact (lx_input_keep cx fp W3 [] ms3 ms (HKP []) HINP). }
  split; [exact Hi|]. split; [exact Hk|]. split; [exact Hacc|]. split; [exact Hblk|].
  split; [exact (lx_prev_keep cx fp W3 [] ms3 ms bs (HKP []) Hprev)|].
  split; [exact Hinv|]. split; [exact Hfab|].
  split; [apply (lx_reg_keep cx fp W3 [(r, LX_REG)] ms3 ms r bs' (HKP _)); [left; reflexivity | exact Hreg']|].
  split; [exact Hinv'|]. split; [exact Hfab'|]. split; [exact Hkept|].
  split; [pose proof Hinv as ((_ & HB1 & _) & _); unfold Boxreg.boxreg_B1 in HB1; lia|].
  split; [exact (lx_cur_keep B MT cx fp W3 HB [] ms3 ms _ (HKP []) Hcur)|].
  split; [exact (lx_slots_loop_keep B MT cx fp W3 HB [] ms3 ms r fab (HKP []) Hsl)|].
  split; [apply (lx_slot_keep B MT cx fp W3 HB [] ms3 ms _ _ (HKP [])); [lia | lia | exact S58]|].
  split; [rewrite (KR 20%bv 20%nat) by (reflexivity || lia); exact R20|].
  split; [rewrite (KR 21%bv 21%nat) by (reflexivity || lia); exact R21|].
  split; [rewrite Q24; reflexivity|].
  rewrite (KR 27%bv 27%nat) by (reflexivity || lia); exact R27.
Qed.

End a.
