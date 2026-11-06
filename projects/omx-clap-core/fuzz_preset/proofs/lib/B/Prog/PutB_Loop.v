(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image B' (asan-ubsan #102 pin d663f82d7f48), the walk of put (lane PutB): THE
   GROW BLOCK'S HEAD AND DOUBLING LOOP (B' index 46 `bnez a1`, 47 `lui a1, 1`, 48 .. 50 `mv s6, a1; slli a1, a1, 1;
   bltu s6, a0`, exit at index 51). From cap (a1) and the need (a0): s6 = newcap cap need and a1 = 2 s6 at index 51,
   memory and every other register kept. Port of h-rw-pre-5's A walk S7a_put.v put_loop_body / put_loop (A keeps the
   need in a2; B' in a0). Numerals: indices are DERIVED (PutB_Base.PK); 4096 (WORD: `lui a1, 1`), 2 ^ 28, 2 ^ 29, 2 ^ 62,
   2 ^ 64 (DERIVED bounds), 64 (fuel: WriterSpec.newcap's). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC81.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YK06 YImgTop YK1g.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YCbqG YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcall YGcallMx YSRrMemnorm YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PutB_Kit PutB_Base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_B.
Context {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs rc B_prog_listing PA).
#[local] Notation VAL := (@pa_val rc B_prog_listing PA).
#[local] Notation BASE := (@pa_val rc B_prog_listing PA A_TEXT).

Section h.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis PE : putb_env (SK := SK) B ARx.
Let LAWS : AR_laws_x SEGS B ARx cf_head := pe_laws B ARx PE.
Let RUN := paj_run_x (SK := SK) (PL := PL_prog_B) (PI := PA) B (@prh_pst prh_img_B) ARx LAWS.
Let BR := paj_branch (PI := PA).

Lemma putb_loop_body : forall (P : (word -> option byte) -> Prop), srr_inv_laws SEGS P ->
  forall (fuel : nat) (W1 : world SEGS) (regs1 : bvmap 5 word) mem1 md1 c need
    STK sp0 (FP : list (Z * Z)) ly S Hp W mem md lyc Sc Hpc k1 (Q : world SEGS -> config -> Prop),
  ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_B) ARx STK sp0 FP ly S Hp W mem md [] lyc Sc Hpc W1 mem1 md1 k1 ->
  P mem1 ->
  getr regs1 11 = Z_to_bv 64 c -> getr regs1 10 = Z_to_bv 64 need ->
  0 < c <= 2 ^ 29 -> 0 <= need <= 2 ^ 28 -> need <= c * 2 ^ Z.of_nat fuel ->
  (forall (regs3 : bvmap 5 word) mem3 md3,
     ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_B) ARx STK sp0 FP ly S Hp W mem md [] lyc Sc Hpc W1 mem3 md3 k1 ->
     P mem3 ->
     (forall x, mrestrict (w_H W1) mem3 x = mrestrict (w_H W1) mem1 x) ->
     getr regs3 22 = Z_to_bv 64 (WriterSpec.dbl fuel c need) ->
     getr regs3 11 = Z_to_bv 64 (2 * WriterSpec.dbl fuel c need) ->
     (forall r : bv 5, r <> 11%bv -> r <> 22%bv -> getr regs3 r = getr regs1 r) ->
     SRr SEGS W1 (mkCfg (YK11.mkst regs3 (Z_to_bv 64 (BASE + PK 51)) mem3 (YK11.seg_rom SEGS)) md3) Q) ->
  SRr SEGS W1 (mkCfg (YK11.mkst regs1 (Z_to_bv 64 (BASE + PK 48)) mem1 (YK11.seg_rom SEGS)) md1) Q.
Proof.
intros P PLAW.
pose (RUNI := paj_run_x_inv (SK := SK) (PL := PL_prog_B) (PI := PA) B (@prh_pst prh_img_B) ARx LAWS P PLAW).
pose (RUNTOI := paj_run_to_x_inv (SK := SK) (PL := PL_prog_B) (PI := PA) B (@prh_pst prh_img_B) ARx LAWS P PLAW).
induction fuel as [|f IH]; intros W1 regs1 mem1 md1 c need STK sp0 FP ly S Hp W mem md lyc Sc Hpc k1 Q
  HJ HPM R11 R10 Hcr Hneed Hfuel HK.
all: destruct (put_seat_r (PK 48) W1 regs1 mem1) as (HS & SHOK).
all: set (E := Eimg (Ereg regs1 [])) in *.
all: assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
all: assert (EG : forall (kk : nat) (r : bv 5), (kk < 32)%nat -> Z.of_nat kk = bv_unsigned r -> ew E kk = getr regs1 r)
  by (intros kk r Hk Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ kk r Hr)).
all: assert (U11 : U E (SOff 11 0) = c) by (apply U_atom; [rewrite (EG 11%nat 11%bv) by (lia || reflexivity); exact R11 | lia]).
all: assert (U10 : U E (SOff 10 0) = need)
  by (apply U_atom; [rewrite (EG 10%nat 10%bv) by (lia || reflexivity); exact R10 | lia]).
all: paj_run_tok_x_inv RUNI HS HJ SHOK HPM put_Bspan.
all: try solve [put_awr].
all: psrr_branch_tok RUN BR HS SHOK put_Bspan.
all: match goal with Hb : branch_taken BC_LTU _ _ = _ |- _ => rewrite branch_ltu_U, U11, U10 in Hb end.
(* fuel 0 and c < need contradicts need <= c * 2 ^ 0 *)
1: (exfalso; apply Z.ltb_lt in Hc; cbn [Z.of_nat] in Hfuel; rewrite Z.pow_0_r, Z.mul_1_r in Hfuel; lia).
all: [> apply Z.ltb_ge in Hc; paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HPM put_Bspan (PK 51)
     | apply Z.ltb_lt in Hc; paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HPM put_Bspan (PK 48)
     | apply Z.ltb_ge in Hc; paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HPM put_Bspan (PK 51) ].
all: try solve [put_awr].
all: pmkst HS.
all: assert (GR : forall rr : bv 5, getr (ms_regs ms0) rr = sv_denot E (sr_get (ss_regs _) rr))
  by (intros rr; exact (st_ok_pi_restrict_reg (w_H W1) E _ ms0 rr HS)).
all: assert (Hreg : regs_ok E sr_atoms regs1) by (subst E; apply regs_ok_Eimg_Ereg).
all: assert (OTH : forall r : bv 5, r <> 11%bv -> r <> 22%bv -> getr (ms_regs ms0) r = getr regs1 r)
  by (intros r H11 H22; rewrite GR, (Hreg r); f_equal; unfold sr_get; destruct (bv_eqb r 0); [reflexivity|];
      match goal with |- nth _ ?L _ = nth _ ?L2 _ =>
        let L' := eval vm_compute in L in change L with L';
        let L2' := eval vm_compute in L2 in change L2 with L2' end;
      assert (Hi : (ridx r < 32)%nat) by (unfold ridx; pose proof (u5_range r); lia);
      assert (Hi11 : ridx r <> 11%nat)
        by (intros Hq; apply H11; apply bv_eq; change (bv_unsigned (11%bv : bv 5)) with 11; unfold ridx in Hq;
            pose proof (u5_range r); lia);
      assert (Hi22 : ridx r <> 22%nat)
        by (intros Hq; apply H22; apply bv_eq; change (bv_unsigned (22%bv : bv 5)) with 22; unfold ridx in Hq;
            pose proof (u5_range r); lia);
      generalize (ridx r) Hi Hi11 Hi22; intros i Hi' Hi11' Hi22';
      do 32 (destruct i as [|i]; [first [reflexivity | lia] |]); lia).
all: assert (MEM : forall x, mrestrict (w_H W1) (ms_mem ms0) x = mrestrict (w_H W1) mem1 x)
  by (intros x; rewrite (HFr0 x), (HFr x); [reflexivity | |]; intros (r & Hr & _); vm_compute in Hr; destruct Hr).
all: assert (S22 : getr (ms_regs ms0) 22 = Z_to_bv 64 c)
  by (rewrite GR; match goal with |- sv_denot ?EE ?e = _ => let v := eval vm_compute in e in change e with v end;
      cbn [sv_denot]; rewrite (EG 11%nat 11%bv) by (lia || reflexivity); rewrite R11, Z.add_0_r, unsigned_lit_small by lia;
      reflexivity).
all: assert (S11 : getr (ms_regs ms0) 11 = Z_to_bv 64 (2 * c))
  by (rewrite GR; match goal with |- sv_denot ?EE ?e = _ => let v := eval vm_compute in e in change e with v end;
      cbn [sv_denot]; rewrite (EG 11%nat 11%bv) by (lia || reflexivity); rewrite R11, Z.add_0_r, unsigned_lit_small by lia;
      apply put_sll1; lia).
(* fuel 0, need <= c: the exit *)
1: { apply (HK (ms_regs ms0) (ms_mem ms0) _ HJ HPM MEM); [cbn [WriterSpec.dbl]; exact S22 | cbn [WriterSpec.dbl]; exact S11 | exact OTH]. }
(* fuel S f, c < need: one more doubling, the induction hypothesis at 2 c *)
1: { assert (R10' : getr (ms_regs ms0) 10 = Z_to_bv 64 need)
       by (rewrite OTH; [exact R10 | intros Hq; apply (f_equal (@bv_unsigned 5)) in Hq; vm_compute in Hq; discriminate Hq
                                   | intros Hq; apply (f_equal (@bv_unsigned 5)) in Hq; vm_compute in Hq; discriminate Hq]).
     apply (IH W1 (ms_regs ms0) (ms_mem ms0) _ (2 * c) need STK sp0 FP ly S Hp W mem md lyc Sc Hpc k1 Q HJ HPM S11 R10'
       ltac:(lia) Hneed).
     { replace (2 * c * 2 ^ Z.of_nat f) with (c * 2 ^ Z.of_nat (Datatypes.S f)) by (rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; ring).
       exact Hfuel. }
     intros regs3 mem3 md3 HJ3 HPM3 HM3 H22 H11 HO3. apply (HK regs3 mem3 md3 HJ3 HPM3).
     - intros x. rewrite HM3. exact (MEM x).
     - rewrite H22. cbn [WriterSpec.dbl]. rewrite (proj2 (Z.leb_gt need c) Hc). reflexivity.
     - rewrite H11. cbn [WriterSpec.dbl]. rewrite (proj2 (Z.leb_gt need c) Hc). reflexivity.
     - intros r Hr11 Hr22. rewrite (HO3 r Hr11 Hr22). exact (OTH r Hr11 Hr22). }
(* fuel S f, need <= c: the exit *)
1: { apply (HK (ms_regs ms0) (ms_mem ms0) _ HJ HPM MEM).
     - cbn [WriterSpec.dbl]. rewrite (proj2 (Z.leb_le need c) Hc). exact S22.
     - cbn [WriterSpec.dbl]. rewrite (proj2 (Z.leb_le need c) Hc). exact S11.
     - exact OTH. }
Qed.

(* ---- the grow block's head (index 46 `bnez a1`, the cap = 0 arm `lui a1, 1`) and the doubling loop ---- *)
Lemma putb_loop : forall (P : (word -> option byte) -> Prop), srr_inv_laws SEGS P ->
  forall (W1 : world SEGS) (regs1 : bvmap 5 word) mem1 md1 cap need
    STK sp0 (FP : list (Z * Z)) ly S Hp W mem md lyc Sc Hpc k1 (Q : world SEGS -> config -> Prop),
  ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_B) ARx STK sp0 FP ly S Hp W mem md [] lyc Sc Hpc W1 mem1 md1 k1 ->
  P mem1 ->
  getr regs1 11 = Z_to_bv 64 cap -> getr regs1 10 = Z_to_bv 64 need ->
  0 <= cap < need -> need <= 2 ^ 28 ->
  (forall (regs3 : bvmap 5 word) mem3 md3,
     ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_B) ARx STK sp0 FP ly S Hp W mem md [] lyc Sc Hpc W1 mem3 md3 k1 ->
     P mem3 ->
     (forall x, mrestrict (w_H W1) mem3 x = mrestrict (w_H W1) mem1 x) ->
     getr regs3 22 = Z_to_bv 64 (WriterSpec.newcap cap need) ->
     getr regs3 11 = Z_to_bv 64 (2 * WriterSpec.newcap cap need) ->
     (forall r : bv 5, r <> 11%bv -> r <> 22%bv -> getr regs3 r = getr regs1 r) ->
     SRr SEGS W1 (mkCfg (YK11.mkst regs3 (Z_to_bv 64 (BASE + PK 51)) mem3 (YK11.seg_rom SEGS)) md3) Q) ->
  SRr SEGS W1 (mkCfg (YK11.mkst regs1 (Z_to_bv 64 (BASE + PK 46)) mem1 (YK11.seg_rom SEGS)) md1) Q.
Proof.
intros P PLAW.
pose (RUNTOI := paj_run_to_x_inv (SK := SK) (PL := PL_prog_B) (PI := PA) B (@prh_pst prh_img_B) ARx LAWS P PLAW).
intros W1 regs1 mem1 md1 cap need STK sp0 FP ly S Hp W mem md lyc Sc Hpc k1 Q HJ HPM R11 R10 Hcap Hneed HK.
destruct (put_seat_r (PK 46) W1 regs1 mem1) as (HS & SHOK).
set (E := Eimg (Ereg regs1 [])) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EG : forall (kk : nat) (r : bv 5), (kk < 32)%nat -> Z.of_nat kk = bv_unsigned r -> ew E kk = getr regs1 r)
  by (intros kk r Hk Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ kk r Hr)).
assert (U11 : U E (SOff 11 0) = cap) by (apply U_atom; [rewrite (EG 11%nat 11%bv) by (lia || reflexivity); exact R11 | lia]).
psrr_branch_tok RUN BR HS SHOK put_Bspan.
all: match goal with Hb : branch_taken _ _ _ = _ |- _ => rewrite branch_ne_U, U11, (U_lit E 0 ltac:(lia)) in Hb end.
all: [> destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0]; [discriminate Hc|];
        paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HPM put_Bspan (PK 48)
     | destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0]; [|discriminate Hc];
        paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HPM put_Bspan (PK 48) ].
all: try solve [put_awr].
all: pmkst HS.
all: assert (GR : forall rr : bv 5, getr (ms_regs ms) rr = sv_denot E (sr_get (ss_regs _) rr))
  by (intros rr; exact (st_ok_pi_restrict_reg (w_H W1) E _ ms rr HS)).
all: assert (Hreg : regs_ok E sr_atoms regs1) by (subst E; apply regs_ok_Eimg_Ereg).
all: assert (OTH : forall r : bv 5, r <> 11%bv -> getr (ms_regs ms) r = getr regs1 r)
  by (intros r H11; rewrite GR, (Hreg r);
      match goal with |- sv_denot _ (sr_get ?L _) = sv_denot _ (sr_get ?L2 _) =>
        let L' := eval vm_compute in L in let L2' := eval vm_compute in L2 in change L with L'; change L2 with L2' end;
      first [ (lazymatch goal with |- ?a = ?a => reflexivity end)
            | (f_equal; unfold sr_get; destruct (bv_eqb r 0); [reflexivity|];
      match goal with |- nth _ ?L _ = nth _ ?L2 _ =>
        let L' := eval vm_compute in L in change L with L';
        let L2' := eval vm_compute in L2 in change L2 with L2' end;
      assert (Hi : (ridx r < 32)%nat) by (unfold ridx; pose proof (u5_range r); lia);
      assert (Hi11 : ridx r <> 11%nat)
        by (intros Hq; apply H11; apply bv_eq; change (bv_unsigned (11%bv : bv 5)) with 11; unfold ridx in Hq;
            pose proof (u5_range r); lia);
      generalize (ridx r) Hi Hi11; intros i Hi' Hi11';
      do 32 (destruct i as [|i]; [first [reflexivity | lia] |]); lia) ]).
all: assert (MEM : forall x, mrestrict (w_H W1) (ms_mem ms) x = mrestrict (w_H W1) mem1 x)
  by (intros x; rewrite (HFr x); [reflexivity|]; intros (r & Hr & _); vm_compute in Hr; destruct Hr).
all: assert (R10' : getr (ms_regs ms) 10 = Z_to_bv 64 need)
  by (rewrite OTH; [exact R10 | intros Hq; apply (f_equal (@bv_unsigned 5)) in Hq; vm_compute in Hq; discriminate Hq]).
(* cap <> 0: the loop from cap *)
1: { assert (R11' : getr (ms_regs ms) 11 = Z_to_bv 64 cap)
       by (rewrite GR; match goal with |- sv_denot ?EE ?e = _ => let v := eval vm_compute in e in change e with v end;
           cbn [sv_denot]; rewrite (EG 11%nat 11%bv) by (lia || reflexivity); rewrite R11, Z.add_0_r, unsigned_lit_small by lia;
           reflexivity).
     apply (putb_loop_body P PLAW 64 W1 (ms_regs ms) (ms_mem ms) _ cap need STK sp0 FP ly S Hp W mem md lyc Sc Hpc k1 Q HJ HPM
       R11' R10' ltac:(lia) ltac:(lia)).
     { change (2 ^ Z.of_nat 64) with 18446744073709551616. lia. }
     intros regs3 mem3 md3 HJ3 HPM3 HM3 H22 H11 HO3. apply (HK regs3 mem3 md3 HJ3 HPM3).
     - intros x. rewrite HM3. exact (MEM x).
     - unfold WriterSpec.newcap. rewrite (proj2 (Z.eqb_neq cap 0) Hc0). exact H22.
     - unfold WriterSpec.newcap. rewrite (proj2 (Z.eqb_neq cap 0) Hc0). exact H11.
     - intros r Hr11 Hr22. rewrite (HO3 r Hr11 Hr22). exact (OTH r Hr11). }
(* cap = 0: `lui a1, 1`, the loop from 4096 *)
1: { clear U11. subst cap.
     assert (R11' : getr (ms_regs ms) 11 = Z_to_bv 64 4096)
       by (rewrite GR; match goal with |- sv_denot ?EE ?e = _ => let v := eval vm_compute in e in change e with v end;
           reflexivity).
     apply (putb_loop_body P PLAW 64 W1 (ms_regs ms) (ms_mem ms) _ 4096 need STK sp0 FP ly S Hp W mem md lyc Sc Hpc k1 Q HJ
       HPM R11' R10' ltac:(lia) ltac:(lia)).
     { change (2 ^ Z.of_nat 64) with 18446744073709551616. lia. }
     intros regs3 mem3 md3 HJ3 HPM3 HM3 H22 H11 HO3. apply (HK regs3 mem3 md3 HJ3 HPM3).
     - intros x. rewrite HM3. exact (MEM x).
     - rewrite put_newcap0. exact H22.
     - rewrite put_newcap0. exact H11.
     - intros r Hr11 Hr22. rewrite (HO3 r Hr11 Hr22). exact (OTH r Hr11). }
Qed.
End h.
End W.
