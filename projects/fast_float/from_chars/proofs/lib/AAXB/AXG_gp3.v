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
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AxAsan AXG_put AXG_put2 AXG_np AXG_np2 AXG_np3 AXG_np4 AXG_nf1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.

Module AXG_gp2.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require Import AxAsan AXG_put AXG_put2 AXG_np AXG_np2 AXG_gp.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Section INVSTEP.
Variables (m m' : word -> option byte) (CA SB c sz nc newc j SP : Z).
Hypothesis I : INV_G m CA SB c sz nc newc j.
Hypothesis Hj : j + 1 + nc <= newc.
Hypothesis HCA : ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6537424 <= CA) /\ CA + 2592 <= SP - 2048.
Hypothesis HSB : 4194304 <= SB /\ SB + 137438953472 + 4096 <= SP - 2048 /\ SP <= 2^47.
Hypothesis HSEP : CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA.
Hypothesis G : mem_grows m m'.

Ltac frm FR := apply (rd_frame m m'); [slia | znq; slia | intros x Hx; znq; apply FR; unfold owned_C; slia | ].

#[using="I Hj HCA HSB HSEP G"] Lemma inv_pop : 1 <= cnt_of nc j ->
  (forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ (REC CA c <= x < REC CA c + 4) -> ~ (CA + 2576 <= x < CA + 2584) -> m' (wa x) = m (wa x)) ->
  rd m' (REC CA c) 4 (cnt_of nc j - 1) -> (exists st, 0 <= st < 2^64 /\ rd m' (CA + 2576) 8 st) ->
  INV_G m' CA SB c sz nc newc (j + 1).
Proof. LiaFast.lf_pins (fun (I Hj HCA HSB HSEP G : LiaFast.U) => LiaFast.u0).
  intros Hc FR Rc Rst. destruct I as [Igeo ISB IRIB Icnt Imc Isz Ich Imu Inf Ina Ifa Ist Iwrec Iwri Iwst].
  destruct (pop_step nc j ltac:(slia) ltac:(slia) Hc) as [Eb Ec].
  pose proof (b_of_pos nc j ltac:(slia) ltac:(slia)) as Hb. pose proof (b_of_bounds nc j ltac:(slia) ltac:(slia)) as Hbb.
  pose proof (cnt_of_range nc j ltac:(slia) ltac:(slia)) as Hcr.
  constructor.
  - slia.
  - frm FR. exact ISB.
  - frm FR. exact IRIB.
  - rewrite Ec. exact Rc.
  - frm FR. exact Imc.
  - frm FR. exact Isz.
  - intros i Hi. rewrite Ec in Hi |- *. replace (j + 1 + (cnt_of nc j - 1) - 1 - i) with (j + cnt_of nc j - 1 - i) by ring.
    frm FR. apply Ich. slia.
  - frm FR. exact Imu.
  - rewrite Eb. frm FR. exact Inf.
  - destruct Ina as (na & Hna & Rna). exists na. split; [exact Hna|]. frm FR. exact Rna.
  - intros k Hk. rewrite Eb in Hk. assert (Hnb : nc * b_of nc j <= newc) by slia.
    frm FR. apply Ifa. exact Hk.
  - exact Rst.
  - intros d k Hd Hk. apply (store_ok_mono SEGS k m m' _ G). apply Iwrec; assumption.
  - intros d k Hd Hk. apply (store_ok_mono SEGS k m m' _ G). apply Iwri; assumption.
  - intros d k Hd Hk. apply (store_ok_mono SEGS k m m' _ G). apply Iwst; assumption.
Qed.

#[using="I Hj HCA HSB HSEP G"] Lemma inv_refill : cnt_of nc j = 0 ->
  (forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ owned_C CA SB c x -> m' (wa x) = m (wa x)) ->
  rd m' (REC CA c) 4 (nc - 1) -> rd m' (REC CA c + 4) 4 (2 * nc) -> rd m' (REC CA c + 8) 8 sz ->
  (forall i, 0 <= i < nc -> rd m' (REC CA c + 16 + 4 * i) 4 ((j + nc - 1 - i) * (sz / 16))) ->
  rd m' (RIX SB c) 8 0 -> rd m' (RIX SB c + 16) 8 (newc - nc * b_of nc j - nc) ->
  (exists na, 0 <= na < 2^64 /\ rd m' (RIX SB c + 72) 8 na) ->
  (exists st, 0 <= st < 2^64 /\ rd m' (CA + 2576) 8 st) ->
  INV_G m' CA SB c sz nc newc (j + 1).
Proof. LiaFast.lf_pins (fun (I Hj HCA HSB HSEP G : LiaFast.U) => LiaFast.u0).
  intros Hc FR Rc Rmc Rsz Rch Rmu Rnf Rna Rst. destruct I as [Igeo ISB IRIB Icnt Imc Isz Ich Imu Inf Ina Ifa Ist Iwrec Iwri Iwst].
  destruct (refill_step nc j ltac:(slia) ltac:(slia) Hc) as (Ej & Eb & Ec).
  pose proof (b_of_pos nc j ltac:(slia) ltac:(slia)) as Hb.
  constructor.
  - slia.
  - frm FR. exact ISB.
  - frm FR. exact IRIB.
  - rewrite Ec. exact Rc.
  - exact Rmc.
  - exact Rsz.
  - intros i Hi. rewrite Ec in Hi |- *. replace (j + 1 + (nc - 1) - 1 - i) with (j + nc - 1 - i) by ring. apply Rch. slia.
  - exact Rmu.
  - rewrite Eb. replace (newc - nc * (b_of nc j + 1)) with (newc - nc * b_of nc j - nc) by ring. exact Rnf.
  - exact Rna.
  - intros k Hk. rewrite Eb in Hk. assert (Hnb : nc * b_of nc j <= newc) by slia.
    frm FR. apply Ifa. slia.
  - exact Rst.
  - intros d k Hd Hk. apply (store_ok_mono SEGS k m m' _ G). apply Iwrec; assumption.
  - intros d k Hd Hk. apply (store_ok_mono SEGS k m m' _ G). apply Iwri; assumption.
  - intros d k Hd Hk. apply (store_ok_mono SEGS k m m' _ G). apply Iwst; assumption.
Qed.
End INVSTEP.
(* [comment removed for export] *)
End AXG_gp2.

Import OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AxAsan OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put2 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np2 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np3 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np4 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf1 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXG_npb OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp3.AXG_gp2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.

Module AXF_ghsz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.

Section GHS.
Context {fx : FPState}.

Definition VALS_ghs (CA ND : Z) : list Z := [CA; ND].

Record ghs_pre (regs : bvmap 5 word) (m : word -> option byte) (CA ND : Z) : Prop := {
  ghs_R10 : getr regs 10 = wa 929816 ;
  ghs_R11 : getr regs 11 = wa CA ;
  ghs_R12 : getr regs 12 = wa ND ;
  ghs_R13 : getr regs 13 = wa 8 ;
  ghs_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  ghs_rng_CA : 1 <= CA <= 2^47 ;
  ghs_rng_ND : 1 <= ND <= 512 ;
  ghs_ka1 : CA mod 16 = 0 ;
  ghs_kr3 : (2^46) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47)
}.


#[using="Type"] Lemma ghs_setup : forall regs m CA ND, ghs_pre regs m CA ND ->
  regs_ok (Ez regs (VALS_ghs CA ND)) OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_ghs.sr_ghs regs /\ know_ok SEGS (Ez regs (VALS_ghs CA ND)) m OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_ghs.kn_ghs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m CA ND P. destruct P as [ghs_R10 ghs_R11 ghs_R12 ghs_R13 ghs_HSTK ghs_rng_CA ghs_rng_ND ghs_ka1 ghs_kr3].
  set (E := Ez regs (VALS_ghs CA ND)).
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ND) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.

  split.
  { unfold OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_ghs.sr_ghs.
    apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|]|]|].
    - rewrite ghs_R10. reflexivity.
    - rewrite ghs_R11. reflexivity.
    - rewrite ghs_R12. reflexivity.
    - rewrite ghs_R13. reflexivity. }
  unfold know_ok, OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_ghs.kn_ghs.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | assumption | first [lia | (replace (getr regs 2) with (getr regs (Z_to_bv 5 (Z.of_nat 2))) by (f_equal; apply bv_eq; reflexivity); lia)]])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_ghs.e_CA OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_ghs.e_ND OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_ghs.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range CA _ _ ghs_rng_CA eq_refl eq_refl), ?(mod64_of_range ND _ _ ghs_rng_ND eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - ghs_rng_CA ghs_rng_ND ghs_ka1 ghs_kr3; lia).
  all: first [lia].
Qed.


Definition ghs_mem_pghs (m : word -> option byte) (regs : bvmap 5 word) (CA ND : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -8)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -32)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -40)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -48)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))))).

#[using="Type"] Theorem ghs_pghs : forall regs m rom CA ND, ghs_pre regs m CA ND ->
  scs_denot SEGS m (Ez regs (VALS_ghs CA ND)) (snd (fst OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_ghs.RES_pghs)) ->
  exists R, msteps SEGS (mkst regs (wa 0x44004) m rom) (mkst R (wa 0x44198) (ghs_mem_pghs m regs CA ND) rom) /\
    getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -48) /\ getr R 8 = wa (Z.shiftr (((ND + 31)) mod 2^64) 5) /\ getr R 10 = wa 929816 /\ getr R 11 = wa CA /\ getr R 12 = wa 512 /\ getr R 13 = wa 8 /\ getr R 14 = wa (ND + 31) /\ getr R 15 = wa 65536 /\ (forall k, In k [1; 3; 4; 5; 6; 7; 9; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom CA ND P Hsc. destruct (ghs_setup regs m CA ND P) as [HR HK].
  set (E := Ez regs (VALS_ghs CA ND)) in *. destruct P as [ghs_R10 ghs_R11 ghs_R12 ghs_R13 ghs_HSTK ghs_rng_CA ghs_rng_ND ghs_ka1 ghs_kr3].
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ND) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.

  destruct (run_sound SEGS 60 [0x44198] OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_ghs.scr_pghs 0x44004 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_ghs.sr_ghs OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_ghs.kn_ghs 34 _ _ _ E m rom regs OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_ghs.RES_pghs_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_ghs.RES_pghs fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (ghs_mem_pghs m regs CA ND) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold ghs_mem_pghs. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End GHS.
(* [comment removed for export] *)
End AXF_ghsz.

From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.
Ltac zlh H := clear - H; lia.
Ltac memb' := first [ AxSymRun3.memb_refl | repeat first [left; reflexivity | right] ].      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition LHD (v1 v8 v9 v18 v19 v20 : Z) : list (Z * nat * Z) :=
  [(-48, 8%nat, v20); (-40, 8%nat, v19); (-32, 8%nat, v18); (-24, 8%nat, v9); (-16, 8%nat, v8); (-8, 8%nat, v1)].
Definition KHD : list nat := [1; 3; 4; 7; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.

Section HEAD.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (m : word -> option byte) (regs : bvmap 5 word) (CA ND SP : Z).
Hypothesis H2 : getr regs 2 = wa SP.
Hypothesis HSP : 2^46 + 4096 <= SP <= 2^47.
Hypothesis HSTK : stk_ok SEGS m (wa SP) 2048.
Hypothesis H10 : getr regs 10 = wa 929816.
Hypothesis H11 : getr regs 11 = wa CA.
Hypothesis H12 : getr regs 12 = wa ND.
Hypothesis H13 : getr regs 13 = wa 8.
Hypothesis HCA : 1 <= CA <= 2^47 /\ CA mod 16 = 0.
Hypothesis HND : 1 <= ND <= 65536.

#[using="H2 HSP HSTK H10 H11 H12 H13 HCA HND"] Lemma gp_head : exists R, msteps SEGS (mkst regs (wa 0x44004) m rom)
    (mkst R (wa 0x44198) (wchainS m SP (LHD (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))
                                             (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))))
                                             (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))))) rom) /\
    getr R 2 = wa (SP - 48) /\ getr R 8 = wa (cls_of ND) /\ 1 <= cls_of ND <= 30 /\
    getr R 10 = wa 929816 /\ getr R 11 = wa CA /\ getr R 13 = wa 8 /\
    (forall k, In k KHD -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins (fun (H2 HSP HSTK H10 H11 H12 H13 HCA HND : LiaFast.U) => LiaFast.u0).
  assert (HSPa : bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) = SP) by (rgz; rewrite H2, u_wa_small by (zlh HSP); reflexivity).
  assert (HS1 : stk_ok SEGS m (getr regs 2) 1024) by (rewrite H2; apply (stk_ok_shrink m (wa SP) 2048 1024); [lia | exact HSTK]).
  unfold cls_of. destruct (Z.leb ND 512) eqn:Hsm; [apply Z.leb_le in Hsm | apply Z.leb_gt in Hsm].
  - (* [comment removed for export] *)
    destruct (cls_small ND ltac:(lia)) as [E5 Hr5].
    assert (P : AXF_ghsz.ghs_pre regs m CA ND) by (constructor; try assumption; try lia; rewrite HSPa; lia).
    destruct (AXF_ghsz.ghs_pghs regs m rom CA ND P ltac:(cbn [OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_ghs.RES_pghs fst snd]; constructor))
      as (R & Hms & A2 & A8 & A10 & A11 & _ & A13 & _ & _ & KK).
    exists R. split.
    { lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => replace M with
        (wchainS m SP (LHD (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))
                           (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))))
                           (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))))) in Hms; [exact Hms|] end.
      unfold AXF_ghsz.ghs_mem_pghs, LHD. rewrite HSPa. reflexivity. }
    split; [rewrite A2, HSPa; f_equal; ring|]. split; [rewrite A8, E5; reflexivity|]. split; [clear - Hr5; lia|].
    split; [exact A10|]. split; [exact A11|]. split; [exact A13|].
    intros k Hk. apply KK. clear - Hk. cbn [KHD In] in Hk. repeat (destruct Hk as [<-|Hk]; [cbn [In]; memb'|]). destruct Hk.
  - (* [comment removed for export] *)
    assert (P : np0bc_pre regs m CA ND) by (constructor; try assumption; try lia; rewrite HSPa; lia).
    destruct (np_cls_big regs m rom CA ND P) as (R & Hms & A2 & A8 & A10 & A11 & A13 & KK).
    exists R. split.
    { lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => replace M with
        (wchainS m SP (LHD (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))
                           (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))))
                           (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))))) in Hms; [exact Hms|] end.
      unfold np0bc_mem, LHD. rewrite HSPa. reflexivity. }
    split; [rewrite A2, HSPa; f_equal; ring|]. split; [exact A8|]. split; [pose proof (cid_range ND ltac:(lia)); lia|].
    split; [exact A10|]. split; [exact A11|]. split; [exact A13|].
    intros k Hk. apply KK. exact Hk.
Qed.
End HEAD.

(* [comment removed for export] *)
Lemma u_rng64 : forall w : word, 0 <= bv_unsigned w <= 2^64 - 1.
Proof. intros w. pose proof (bv_unsigned_in_range _ w) as H. unfold bv_modulus in H. change (2 ^ Z.of_N 64) with (2^64) in H. lia. Qed.
Lemma hd_slot : forall m SP v1 v8 v9 v18 v19 v20 k v, 2^20 <= SP <= 2^47 -> 0 <= k <= 40 ->
  wl_chk (LHD v1 v8 v9 v18 v19 v20) (k - 48) 8 = Some v ->
  rdn SEGS (wchainS m SP (LHD v1 v8 v9 v18 v19 v20)) (wa (SP - 48 + k)) 8 = Some (word_to_le_bytes 8 (wa v)).
Proof.
  intros m SP v1 v8 v9 v18 v19 v20 k v HS Hk H.
  replace (SP - 48 + k) with (SP + (k - 48)) by ring.
  apply (rd_wchainS (LHD v1 v8 v9 v18 v19 v20) m SP (k - 48) 8 v); [lia | lia | reflexivity | lia | cbn; lia | lia | exact H].
Qed.
Lemma hd_frame : forall m SP v1 v8 v9 v18 v19 v20 x, 2^20 <= SP <= 2^47 -> 0 <= x < 2^64 -> ~ (SP - 48 <= x < SP) ->
  wchainS m SP (LHD v1 v8 v9 v18 v19 v20) (wa x) = m (wa x).
Proof.
  intros m SP v1 v8 v9 v18 v19 v20 x HS Hx H.
  apply (wchainS_frame_in (LHD v1 v8 v9 v18 v19 v20) m SP (-48) 0); [lia | lia | reflexivity | reflexivity | exact Hx | lia].
Qed.

Section GPOP.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (m : word -> option byte) (regs : bvmap 5 word) (CA ND c SB sz nc newc j SP : Z).
Hypothesis Hc : c = cls_of ND.
Hypothesis I : INV_G m CA SB c sz nc newc j.
Hypothesis Hj : j + 1 + nc <= newc.
Hypothesis HND : 1 <= ND <= 65536.
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

#[using="ND Hc I Hj HND H2 HSP HSTK H10 H11 H12 H13 HCA HSB HSEP"] Lemma gp_pop : 1 <= cnt_of nc j ->
  exists R m', msteps SEGS (mkst regs (wa 0x44004) m rom) (mkst R (wa 0x44224) m' rom) /\
    getr R (Z_to_bv 5 (Z.of_nat 2)) = wa SP /\
    (forall k, In k KCALLEE -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
    getr R 10 = wa (SB + c * 4294967296 + j * sz) /\
    INV_G m' CA SB c sz nc newc (j + 1) /\
    (forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ owned_C CA SB c x -> m' (wa x) = m (wa x)) /\ mem_grows m m'.
Proof. LiaFast.lf_pins (fun (ND Hc I Hj HND H2 HSP HSTK H10 H11 H12 H13 HCA HSB HSEP : LiaFast.U) => LiaFast.u0).
  intros Hcnt.
  destruct (gp_head rom m regs CA ND SP H2 ltac:(zlh HSP) HSTK H10 H11 H12 H13 ltac:(clear - HCA HSP; lia) HND)
    as (R1 & Hms1 & A2 & A8 & Hcr & A10 & A11 & A13 & KK1).
  rewrite <- Hc in A8, Hcr.
  set (v1 := bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) in *. set (v8 := bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))) in *.
  set (v9 := bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))) in *. set (v18 := bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) in *.
  set (v19 := bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))) in *. set (v20 := bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))) in *.
  set (m1 := wchainS m SP (LHD v1 v8 v9 v18 v19 v20)) in *.
  pose proof I as I0. destruct I0 as [Igeo ISB IRIB Icnt Imc Isz Ich Imu Inf Ina Ifa Ist Iwrec Iwri Iwst].
  pose proof (cnt_of_range nc j ltac:(slia) ltac:(slia)) as Hcntr.
  set (cnt := cnt_of nc j) in *.
  destruct Ist as (st & Hst & Rst).
  assert (Hsz16 : sz = 16 * (sz / 16)) by (pose proof (Z.div_mod sz 16 ltac:(lia)); slia).
  set (cp := j * (sz / 16)).
  assert (Hcp : 0 <= cp <= 16384).
  { unfold cp. assert (0 <= sz / 16) by (apply Z.div_pos; slia). destruct Igeo as (_ & _ & _ & _ & Hj1 & _ & Hns & _). nia. }
  assert (Hszr : 16 <= sz <= 262144) by (clear - Igeo; destruct Igeo as (_ & H1 & _ & H0 & H1' & H2' & H3 & _); nia).
  assert (HZ : ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6537424 <= CA) /\ CA mod 16 = 0 /\ CA + 2592 <= SP - 2048 /\ 4194304 <= SB /\ SB mod 4096 = 0 /\
               SB + 137438953472 + 4096 <= SP - 2048 /\ 2^46 + 4096 <= SP <= 2^47 /\ 1 <= c <= 30 /\ 1 <= cnt < nc /\ 1 <= nc <= 8 /\
               16 <= sz <= 262144 /\ 0 <= st < 2^64 /\ 0 <= cp <= 16384 /\ (CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA)) by slia.
  assert (G1 : mem_grows m m1) by (apply wchainS_grows).
  assert (F1 : forall x, 0 <= x < 2^64 -> ~ (SP - 48 <= x < SP) -> m1 (wa x) = m (wa x)) by (intros x Hx Hn; apply hd_frame; [zlh HZ | exact Hx | exact Hn]).
  assert (HSP1 : bv_unsigned (getr R1 (Z_to_bv 5 (Z.of_nat 2))) = SP - 48) by (rgz; rewrite A2, u_wa_small by (zlh HZ); reflexivity).
  assert (W1 : forall k, In k KHD -> bv_unsigned (getr R1 (Z_to_bv 5 (Z.of_nat k))) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat k)))) by (intros k Hk; rewrite (KK1 k Hk); reflexivity).
  assert (P : OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gnp0tz.gnp0t_pre R1 m1 CA c cnt sz cp SB st v8).
  { constructor; [exact A8 | exact A10 | exact A11 | exact A13 | | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ)
                 | (unfold v8; apply u_rng64) | (zlh HZ) | (rewrite HSP1; zlh HZ) | | | | | | | | | | | | | ].
    - rewrite A2. apply (stk_ok_move m1 SP (SP - 48) 1024); [(zlh HZ) | (zlh HZ) | exact (stk_ok_grows m m1 (wa SP) 2048 G1 HSTK) | (zlh HZ) | (zlh HZ) | (zlh HZ)].
    - rewrite HSP1, (W1 1%nat ltac:(cbn; memb')). apply hd_slot; [(zlh HZ) | clear; lia | reflexivity].
    - rewrite HSP1. apply hd_slot; [(zlh HZ) | clear; lia | reflexivity].
    - rewrite HSP1, (W1 9%nat ltac:(cbn; memb')). apply hd_slot; [(zlh HZ) | clear; lia | reflexivity].
    - rewrite HSP1, (W1 18%nat ltac:(cbn; memb')). apply hd_slot; [(zlh HZ) | clear; lia | reflexivity].
    - rewrite HSP1, (W1 19%nat ltac:(cbn; memb')). apply hd_slot; [(zlh HZ) | clear; lia | reflexivity].
    - rewrite HSP1, (W1 20%nat ltac:(cbn; memb')). apply hd_slot; [(zlh HZ) | clear; lia | reflexivity].
    - rewrite Z.add_0_r. apply (rd_frame m m1); [(zlh HZ) | znq; (zlh HZ) | intros x Hx; znq; apply F1; clear - HZ Hx; lia | exact Icnt].
    - intros d k Hd Hk. rewrite Z.add_0_r. apply (store_ok_mono SEGS k m m1 _ G1). apply Iwrec; clear - Hd Hk; lia.
    - apply (rd_frame m m1); [(zlh HZ) | znq; (zlh HZ) | intros x Hx; znq; apply F1; clear - HZ Hx; lia | exact Isz].
    - rewrite chp_off by (zlh HZ). replace (CA + (80 * c + 4 * (cnt - 1)) + 16) with (CA + 80 * c + 16 + 4 * (cnt - 1)) by ring.
      pose proof (Ich (cnt - 1) ltac:(zlh HZ)) as R7. replace ((j + cnt - 1 - (cnt - 1)) * (sz / 16)) with cp in R7 by (unfold cp; ring).
      apply (rd_frame m m1); [(zlh HZ) | znq; (zlh HZ) | intros x Hx; znq; apply F1; clear - HZ Hx; lia | exact R7].
    - apply (rd_frame m m1); [lia | znq; lia | intros x Hx; znq; apply F1; clear - HZ Hx; lia | exact ISB].
    - apply (rd_frame m m1); [(zlh HZ) | znq; (zlh HZ) | intros x Hx; znq; apply F1; clear - HZ Hx; lia | exact Rst].
    - intros d k Hd Hk. apply (store_ok_mono SEGS k m m1 _ G1). replace (CA + 2576 + d) with (CA + 2560 + (16 + d)) by ring. apply Iwst; clear - Hd Hk; lia. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gnp0tz.gnp0t_pnp0tp R1 m1 rom CA c cnt sz cp SB st v8 P
              (sc_gnp0t R1 m1 (SP - 48) HSP1 CA c cnt sz cp SB st v8 ltac:(zlh HZ)))
    as (R & Hms & B2 & B8 & B10 & _ & _ & _ & _ & KK).
  clear P.
  pose proof (msteps_trans SEGS _ _ _ Hms1 Hms) as Hms'. clear Hms1 Hms.
  assert (EM : OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gnp0tz.gnp0t_mem_pnp0tp m1 R1 CA c cnt sz cp SB st v8 =
               wbytes (wbytes m1 (wa (CA + 80 * c)) (word_to_le_bytes 4 (wa (cnt - 1)))) (wa (CA + 2576)) (word_to_le_bytes 8 (wa (sz + st)))).
  { unfold OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXF_gnp0tz.gnp0t_mem_pnp0tp. rewrite Z.add_0_r, ext_Z_lo32_small by (zlh HZ). rewrite ?addneg. reflexivity. }
  rewrite EM in Hms'. clear EM.
  set (m' := wbytes (wbytes m1 (wa (CA + 80 * c)) (word_to_le_bytes 4 (wa (cnt - 1)))) (wa (CA + 2576)) (word_to_le_bytes 8 (wa (sz + st)))) in *.
  assert (FRM : forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ (CA + 80 * c <= x < CA + 80 * c + 4) -> ~ (CA + 2576 <= x < CA + 2584) -> m' (wa x) = m (wa x)).
  { intros x Hx Q1 Q2 Q3. unfold m'. repeat (rewrite wb_other by first [exact Hx | (lenq; zlh HZ) | (lenq; clear - HZ Q2 Q3; lia)]). apply F1; [exact Hx | clear - Q1; lia]. }
  assert (G : mem_grows m m') by (unfold m'; apply grows_wb; apply grows_wb; exact G1).
  exists R, m'. split; [exact Hms'|].
  split; [rgz; rewrite B2, HSP1; f_equal; ring|].
  split.
  { intros k Hk. destruct (Nat.eq_dec k 8) as [->|Hk8].
    - unfold v8. replace (Z_to_bv 5 (Z.of_nat 8)) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite B8. apply wa_u.
    - assert (Hk' : In k [1; 3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat) by (clear - Hk Hk8; cbn [KCALLEE In] in Hk; cbn [In]; intuition congruence).
      rewrite (KK k ltac:(clear - Hk'; cbn [In] in *; intuition)). apply KK1. clear - Hk'. cbn [KHD In] in *. intuition. }
  split.
  { rewrite B10, ext_Z_u32 by (zlh HZ). f_equal. unfold cp. rewrite Hsz16 at 2. ring. }
  split.
  { apply (inv_pop m m' CA SB c sz nc newc j SP I Hj ltac:(zlh HZ) ltac:(zlh HZ) HSEP G Hcnt FRM).
    - unfold m'. apply wb_rd_other; [(zlh HZ) | lenq; (zlh HZ) | (zlh HZ) | lenq; (zlh HZ) | lenq; (zlh HZ) |]. apply wb_rd_hit; lenq; (zlh HZ).
    - exists ((sz + st) mod 2^64). split; [apply Z.mod_pos_bound; lia|]. unfold rd, m'.
      rewrite (wa_eqm ((sz + st) mod 2^64) (sz + st)) by (apply Z.mod_mod; lia). apply (wb_rd_hit _ _ 8 (sz + st)); lenq; (zlh HZ). }
  split; [intros x Hx Q1 Q2; apply FRM; [exact Hx | exact Q1 | unfold owned_C in Q2; clear - HZ Q2; lia | unfold owned_C in Q2; clear - HZ Q2; lia] | exact G].
Qed.
End GPOP.
(* [comment removed for export] *)
