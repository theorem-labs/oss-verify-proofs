(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require Import AxAsan AXG_put AXG_put2 AXG_np AXG_np2.

Module AXG_npscp.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AxAsan AXG_put AXG_put2.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxBits.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AxAsan OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put2 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxBits.AxScChk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_np.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_np.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_np.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_np.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_np.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_np.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_np.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_np.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_np.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_np.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
Abbreviation SEGS := AsanUbsan.M.loaded_segments.
Ltac zlh H := clear - H; lia.
Definition ca_place (CA : Z) : Prop := (4304 <= CA /\ CA + 3888 <= 65536) \/ 6537424 <= CA.
Definition LOW : iv := (4304, 61648).
Definition HIGH : iv := (6537424, 2^47).
Definition B47 : iv := (4194304, 2^47).
Ltac zat R := repeat match goal with |- context [bv_unsigned (ev (Ez R ?V) ?n)] =>
              lazymatch eval cbn in (Nat.ltb n 32) with
              | true => change (bv_unsigned (ev (Ez R V) n)) with (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat n))))
              | false => let v := eval cbn [nth Nat.sub] in (nth (n - 32) V 0) in rewrite (zatom R V n v eq_refl eq_refl) by lia
              end end.
Ltac fact_go R HSPa HX HH :=
  try unfold rf_ok; try unfold df_ok; try unfold LOW; try unfold HIGH; try unfold B47; cbn [fst snd zeval edenot]; zat R; rewrite ?HSPa, ?HX; zlh HH.
Ltac facts_go R HSPa HX HH := repeat (first [apply Forall_nil | apply Forall_cons; [fact_go R HSPa HX HH|]]).
Ltac sc_refl rf df R HSPa HX HH :=
  apply (scs_chk_sound rf df); [ facts_go R HSPa HX HH | facts_go R HSPa HX HH | vm_compute; reflexivity ].
(* [comment removed for export] *)
(* [comment removed for export] *)

Section SCS.
Context {fx : FPState}.
Variables (R : bvmap 5 word) (m : word -> option byte).
Variables (SPa CA ND SB RIB : Z).
Hypothesis HSPa : bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 2))) = SPa.
Hypothesis HND : 33 <= ND <= 512.
Hypothesis HCA : ca_place CA /\ CA + 2592 + 256 <= SPa /\ 2^46 <= SPa <= 2^47.
Hypothesis HRI : 4194304 <= RIB /\ RIB + 4096 + 256 <= SPa.
Hypothesis HSEP : CA + 2592 <= RIB \/ RIB + 4096 <= CA.

(* [comment removed for export] *)
#[using="SPa HSPa HND HCA"] Lemma sc_np0p_p : forall cnt sz cp st, 1 <= cnt <= 16 ->
  scs_denot SEGS m (Ez R (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np.AXF_np0z.VALS_np0 CA ND cnt sz cp SB st)) (snd (fst OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np.AXF_np0.RES_pnp0p)).
Proof. LiaFast.lf_pins (fun (SPa HSPa HND HCA : LiaFast.U) => LiaFast.u0).
  intros cnt sz cp st Hc. unfold OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np.AXF_np0z.VALS_np0. destruct HCA as (HP & HC2). unfold ca_place in HP.
  destruct HP as [HP|HP]; assert (HH := conj HP (conj HC2 (conj HND Hc))).
  - sc_refl [(EVar 2, (2^46, 2^47)); (EVar 32, LOW); (EVar 33, (33, 512)); (EVar 34, (1, 16))] [(EVar 2, EVar 32, 2848)] R HSPa HSPa HH.
  - sc_refl [(EVar 2, (2^46, 2^47)); (EVar 32, HIGH); (EVar 33, (33, 512)); (EVar 34, (1, 16))] [(EVar 2, EVar 32, 2848)] R HSPa HSPa HH.
Qed.
(* [comment removed for export] *)
#[using="SPa HSPa HND HCA"] Lemma sc_np0r_p : forall sz st,
  scs_denot SEGS m (Ez R (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np.AXF_np0rz.VALS_np0r CA ND 0 sz SB st)) (snd (fst OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np.AXF_np0r.RES_pnp0r)).
Proof. LiaFast.lf_pins (fun (SPa HSPa HND HCA : LiaFast.U) => LiaFast.u0).
  intros sz st. unfold OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np.AXF_np0rz.VALS_np0r. destruct HCA as (HP & HC2). unfold ca_place in HP.
  destruct HP as [HP|HP]; assert (HH := conj HP (conj HC2 HND)).
  - sc_refl [(EVar 2, (2^46, 2^47)); (EVar 32, LOW); (EVar 33, (33, 512)); (EVar 34, (0, 0))] [(EVar 2, EVar 32, 2848)] R HSPa HSPa HH.
  - sc_refl [(EVar 2, (2^46, 2^47)); (EVar 32, HIGH); (EVar 33, (33, 512)); (EVar 34, (0, 0))] [(EVar 2, EVar 32, 2848)] R HSPa HSPa HH.
Qed.
(* [comment removed for export] *)
#[using="SPa HSPa HND HCA"] Lemma sc_npr_p : forall mc, 2 <= mc <= 16 ->
  scs_denot SEGS m (Ez R (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np.AXF_nprz.VALS_npr CA ND mc)) (snd (fst OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np.AXF_npr.RES_pnpr)).
Proof. LiaFast.lf_pins (fun (SPa HSPa HND HCA : LiaFast.U) => LiaFast.u0).
  intros mc Hmc. unfold OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np.AXF_nprz.VALS_npr. destruct HCA as (HP & HC2). unfold ca_place in HP.
  destruct HP as [HP|HP]; assert (HH := conj HP (conj HC2 (conj HND Hmc))).
  - sc_refl [(EVar 2, (2^46, 2^47)); (EVar 32, LOW); (EVar 33, (33, 512)); (EVar 34, (2, 16))] [(EVar 2, EVar 32, 2848)] R HSPa HSPa HH.
  - sc_refl [(EVar 2, (2^46, 2^47)); (EVar 32, HIGH); (EVar 33, (33, 512)); (EVar 34, (2, 16))] [(EVar 2, EVar 32, 2848)] R HSPa HSPa HH.
Qed.
(* [comment removed for export] *)
#[using="SPa HSPa HND HCA HRI HSEP"] Lemma sc_ng0_p : forall n nf, 1 <= n <= 8 -> n <= nf <= 16384 ->
  scs_denot SEGS m (Ez R (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np.AXF_ng0z.VALS_ng0 CA ND n SB RIB nf)) (snd (fst OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np.AXF_ng0.RES_png0)).
Proof. LiaFast.lf_pins (fun (SPa HSPa HND HCA HRI HSEP : LiaFast.U) => LiaFast.u0).
  intros n nf Hn Hnf. unfold OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np.AXF_ng0z.VALS_ng0. destruct HCA as (HP & HC2). unfold ca_place in HP.
  destruct HP as [HP|HP].
  - assert (HH := conj HP (conj HC2 (conj HND (conj Hn (conj Hnf HRI))))).
    sc_refl [(EVar 2, (2^46, 2^47)); (EVar 32, LOW); (EVar 33, (33, 512)); (EVar 34, (1, 8)); (EVar 36, B47); (EVar 37, (1, 16384))]
            [(EVar 2, EVar 32, 2848); (EVar 2, EVar 36, 4352); (EVar 37, EVar 34, 0); (EVar 36, EVar 32, 2592)] R HSPa HSPa HH.
  - destruct HSEP as [HD|HD]; assert (HH := conj HD (conj HP (conj HC2 (conj HND (conj Hn (conj Hnf HRI)))))).
    + sc_refl [(EVar 2, (2^46, 2^47)); (EVar 32, HIGH); (EVar 33, (33, 512)); (EVar 34, (1, 8)); (EVar 36, B47); (EVar 37, (1, 16384))]
              [(EVar 2, EVar 32, 2848); (EVar 2, EVar 36, 4352); (EVar 37, EVar 34, 0); (EVar 36, EVar 32, 2592)] R HSPa HSPa HH.
    + sc_refl [(EVar 2, (2^46, 2^47)); (EVar 32, HIGH); (EVar 33, (33, 512)); (EVar 34, (1, 8)); (EVar 36, B47); (EVar 37, (1, 16384))]
              [(EVar 2, EVar 32, 2848); (EVar 2, EVar 36, 4352); (EVar 37, EVar 34, 0); (EVar 32, EVar 36, 4096)] R HSPa HSPa HH.
Qed.
(* [comment removed for export] *)
#[using="SPa HSPa HND HCA HRI HSEP"] Lemma sc_ngt_p : forall n na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra, 1 <= n <= 8 ->
  scs_denot SEGS m (Ez R (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np.AXF_ngtz.VALS_ngt CA ND n SB RIB na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra)) (snd (fst OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np.AXF_ngt.RES_pngt)).
Proof. LiaFast.lf_pins (fun (SPa HSPa HND HCA HRI HSEP : LiaFast.U) => LiaFast.u0).
  intros n na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra Hn. unfold OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np.AXF_ngtz.VALS_ngt.
  destruct HCA as (HP & HC2). unfold ca_place in HP.
  destruct HP as [HP|HP].
  - assert (HH := conj HP (conj HC2 (conj HND (conj Hn HRI)))).
    sc_refl [(EVar 2, (2^46, 2^47)); (EVar 32, LOW); (EVar 33, (33, 512)); (EVar 34, (1, 8)); (EVar 36, B47)]
            [(EVar 2, EVar 32, 2848); (EVar 2, EVar 36, 4352); (EVar 36, EVar 32, 2592)] R HSPa HSPa HH.
  - destruct HSEP as [HD|HD]; assert (HH := conj HD (conj HP (conj HC2 (conj HND (conj Hn HRI))))).
    + sc_refl [(EVar 2, (2^46, 2^47)); (EVar 32, HIGH); (EVar 33, (33, 512)); (EVar 34, (1, 8)); (EVar 36, B47)]
              [(EVar 2, EVar 32, 2848); (EVar 2, EVar 36, 4352); (EVar 36, EVar 32, 2592)] R HSPa HSPa HH.
    + sc_refl [(EVar 2, (2^46, 2^47)); (EVar 32, HIGH); (EVar 33, (33, 512)); (EVar 34, (1, 8)); (EVar 36, B47)]
              [(EVar 2, EVar 32, 2848); (EVar 2, EVar 36, 4352); (EVar 32, EVar 36, 4096)] R HSPa HSPa HH.
Qed.
End SCS.
(* [comment removed for export] *)
End AXG_npscp.

Import OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np3.AXG_npscp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_np.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_np.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.

Definition KCALLEE : list nat := [1; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.

Lemma grows_wb : forall m m' a bs, mem_grows m m' -> mem_grows m (wbytes m' a bs).
Proof. intros m m' a bs H. eapply mem_grows_trans; [exact H | apply wbytes_grows]. Qed.
Ltac growsc := repeat apply grows_wb; apply mem_grows_refl.
Lemma addneg : forall x p, x + Zneg p = x - Zpos p.
Proof. reflexivity. Qed.
Lemma stk_ok_grows : forall m m' sp K, mem_grows m m' -> stk_ok SEGS m sp K -> stk_ok SEGS m' sp K.
Proof. intros m m' sp K G H a n H1 H2. apply (store_ok_mono SEGS n m m' _ G). apply H; assumption. Qed.
Ltac rgz := replace (Z_to_bv 5 (Z.of_nat 2)) with (@BV 5 2 I) in * by (apply bv_eq; reflexivity).
Ltac kcin Hk := clear - Hk; cbn [KCALLEE In] in Hk; repeat (destruct Hk as [<-|Hk]; [cbn [In]; memb|]); destruct Hk.

Section NP.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (m : word -> option byte) (regs : bvmap 5 word) (CA ND c SB sz nc newc j SP : Z).
Hypothesis Hc : c = (ND + 31) / 32.
Hypothesis I : INV_C m CA SB c sz nc newc j.
Hypothesis Hj : j + 1 + nc <= newc.
Hypothesis HND : 33 <= ND <= 512.
Hypothesis H2 : getr regs 2 = wa SP.
Hypothesis HSP : 2^46 + 4096 <= SP <= 2^47 /\ SP mod 16 = 0.
Hypothesis HSTK : stk_ok SEGS m (wa SP) 2048.
Hypothesis H10 : getr regs 10 = wa 929816.
Hypothesis H11 : getr regs 11 = wa CA.
Hypothesis H12 : getr regs 12 = wa ND.
Hypothesis H13 : getr regs 13 = wa 8.
Hypothesis HCA : ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6537424 <= CA) /\ CA mod 16 = 0 /\ CA + 2592 <= SP - 2048.
Hypothesis HSB : 4194304 <= SB /\ SB mod 4096 = 0 /\ SB + 137438953472 + 4096 <= SP - 2048.
Hypothesis HSEP : CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA.
Hypothesis HIMG : forall i, 65536 <= i < 143360 -> m (Z_to_bv 64 i) = None.

#[using="ND Hc I Hj HND H2 HSP HSTK H10 H11 H12 H13 HCA HSB HSEP"] Lemma np_pop : 1 <= cnt_of nc j ->
  exists R m', msteps SEGS (mkst regs (wa 0x44004) m rom) (mkst R (wa 0x44224) m' rom) /\
    getr R (Z_to_bv 5 (Z.of_nat 2)) = wa SP /\
    (forall k, In k KCALLEE -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
    getr R 10 = wa (SB + c * 4294967296 + j * sz) /\
    INV_C m' CA SB c sz nc newc (j + 1) /\
    (forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ owned_C CA SB c x -> m' (wa x) = m (wa x)) /\ mem_grows m m'.
Proof. LiaFast.lf_pins (fun (ND Hc I Hj HND H2 HSP HSTK H10 H11 H12 H13 HCA HSB HSEP : LiaFast.U) => LiaFast.u0).
  intros Hcnt.
  pose proof I as I0. destruct I0 as [Igeo ISB IRIB Icnt Imc Isz Ich Imu Inf Ina Ifa Ist Iwrec Iwri Iwst].
  pose proof (cnt_of_range nc j ltac:(slia) ltac:(slia)) as Hcr.
  set (cnt := cnt_of nc j) in *.
  destruct Ist as (st & Hst & Rst).
  assert (HC5 : Z.shiftr ((ND + 31) mod 2^64) 5 = c) by (rewrite Hc; apply c_of_nd; exact HND).
  pose proof (c_of_nd_range ND HND) as Hcr5. rewrite <- Hc in Hcr5.
  assert (Hsz16 : sz = 16 * (sz / 16)) by (pose proof (Z.div_mod sz 16 ltac:(lia)); slia).
  set (cp := j * (sz / 16)).
  assert (Hcp : 0 <= cp <= 16384).
  { unfold cp. assert (0 <= sz / 16) by (apply Z.div_pos; slia). destruct Igeo as (_ & _ & _ & _ & Hj1 & _ & Hns & _). nia. }
  assert (HSPa : bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) = SP) by (rgz; rewrite H2, u_wa_small by slia; reflexivity).
  assert (P : OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np.AXF_np0z.np0_pre regs m CA ND cnt sz cp SB st).
  { constructor; try assumption; try slia.
    - rewrite H2. apply (stk_ok_shrink m (wa SP) 2048 1024); [slia | exact HSTK].
    - rewrite HC5, Z.add_0_r. exact Icnt.
    - intros d k Hd Hk. rewrite HC5, Z.add_0_r. apply Iwrec; slia.
    - rewrite HC5. exact Isz.
    - rewrite HC5, chp_off by slia. replace (CA + (80 * c + 4 * (cnt - 1)) + 16) with (CA + 80 * c + 16 + 4 * (cnt - 1)) by ring.
      pose proof (Ich (cnt - 1) ltac:(slia)) as R7. replace ((j + cnt - 1 - (cnt - 1)) * (sz / 16)) with cp in R7 by (unfold cp; ring). exact R7.
    - intros d k Hd Hk. replace (CA + 2576 + d) with (CA + 2560 + (16 + d)) by ring. apply Iwst; slia. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np.AXF_np0z.np0_pnp0p regs m rom CA ND cnt sz cp SB st P
              (sc_np0p_p regs m SP CA ND SB HSPa HND ltac:(unfold ca_place; slia) cnt sz cp st ltac:(slia)))
    as (R & Hms & A10 & A11 & A12 & A13 & A14 & A15 & KK).
  set (m' := OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np.AXF_np0z.np0_mem_pnp0p m regs CA ND cnt sz cp SB st) in *.
  assert (EM : m' = wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
             (wa (SP - 8)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))))))
             (wa (SP - 16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))))))
             (wa (SP - 24)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))))))
             (wa (SP - 32)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))))))
             (wa (SP - 40)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))))))
             (wa (SP - 48)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))))))
             (wa (CA + 80 * c)) (word_to_le_bytes 4 (wa (cnt - 1))))
             (wa (CA + 2576)) (word_to_le_bytes 8 (wa (sz + st)))).
  { unfold m', OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np.AXF_np0z.np0_mem_pnp0p. rewrite HSPa, HC5, Z.add_0_r, ext_Z_lo32_small by slia. rewrite ?addneg. reflexivity. }
  clearbody m'. subst m'.
  assert (FRM : forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ (CA + 80 * c <= x < CA + 80 * c + 4) -> ~ (CA + 2576 <= x < CA + 2584) ->
            wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
             (wa (SP - 8)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))))))
             (wa (SP - 16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))))))
             (wa (SP - 24)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))))))
             (wa (SP - 32)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))))))
             (wa (SP - 40)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))))))
             (wa (SP - 48)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))))))
             (wa (CA + 80 * c)) (word_to_le_bytes 4 (wa (cnt - 1))))
             (wa (CA + 2576)) (word_to_le_bytes 8 (wa (sz + st))) (wa x) = m (wa x)).
  { intros x Hx F1 F2 F3. repeat (rewrite wb_other by first [exact Hx | (lenq; slia) | slia]). reflexivity. }
  eexists R, _. split; [exact Hms|].
  split; [rewrite (KK 2%nat ltac:(cbn; tauto)); rgz; exact H2|].
  split; [intros k Hk; apply KK; kcin Hk|].
  split.
  { rewrite A10, HC5, ext_Z_u32 by slia. f_equal. unfold cp. rewrite Hsz16 at 2. ring. }
  assert (G : mem_grows m (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
             (wa (SP - 8)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))))))
             (wa (SP - 16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))))))
             (wa (SP - 24)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))))))
             (wa (SP - 32)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))))))
             (wa (SP - 40)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))))))
             (wa (SP - 48)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))))))
             (wa (CA + 80 * c)) (word_to_le_bytes 4 (wa (cnt - 1))))
             (wa (CA + 2576)) (word_to_le_bytes 8 (wa (sz + st))))) by growsc.
  split.
  { apply (inv_pop m _ CA SB c sz nc newc j SP I Hj ltac:(slia) ltac:(slia) HSEP G Hcnt FRM).
    - apply wb_rd_other; [slia | lenq; slia | slia | lenq; slia | lenq; slia |]. apply wb_rd_hit; lenq; slia.
    - exists ((sz + st) mod 2^64). split; [apply Z.mod_pos_bound; lia|]. unfold rd.
      rewrite (wa_eqm ((sz + st) mod 2^64) (sz + st)) by (apply Z.mod_mod; lia). apply (wb_rd_hit _ _ 8 (sz + st)); lenq; slia. }
  split; [intros x Hx F1 F2; apply FRM; [exact Hx | exact F1 | unfold owned_C in F2; slia | unfold owned_C in F2; slia] | exact G].
Qed.

End NP.
(* [comment removed for export] *)
