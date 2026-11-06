(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ AxTry.

Module AXF_actb.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_sc := EVar 32.
Definition e_G3 := EVar 33.
Definition e_mem3 := EVar 34.
Definition e_hb := EVar 35.
Definition e_freed3 := EVar 36.
Definition e_W3 := EVar 37.
Definition e_bnc := EVar 38.
Definition BNC := EAlu ALU_SRL (EMd M_MUL (ELit 4503599627370496) (EExt true 0 4 e_W3)) (ELit 58).
Definition sr_actb := (sr_upd (sr_upd sr_id 10 (e_G3)) 22 (ELit 614096)).
Definition kn_actb : list kentry :=
  [ KRange e_sc 0 47;
    KRange e_G3 1 (2^63-1);
    KAlign e_G3 8;
    KRange e_mem3 1 (2^63-1);
    KRange e_hb 0 255;
    KRange e_freed3 0 (2^32-1);
    KRange e_W3 0 (2^32-1);
    KWord (SA e_G3 16) 8 e_mem3;
    KWord (SA e_mem3 8) 1 e_hb;
    KWord (SA e_G3 28) 4 e_freed3;
    KWord (SA e_G3 32) 4 e_W3;
    KWr (SA e_G3 24) (ELit 8);
    KRange e_bnc 0 255;
    KRange BNC 0 63;
    KWord (SA BNC 614977) 1 e_bnc;
    KWr (SA BNC 614977) (ELit 1);
    KDisj (SA BNC 614977) (ELit 1) (SA e_G3 24) (ELit 8) ].
Definition scr_actb : scripts := SCR [false; true; false; false] [] [].
Definition ss_actb := SS 0x52418 sr_actb [] kn_actb 39.
Definition RUN_actb := sym_exec SEGS 200 true [0x52490] scr_actb ss_actb [].

Definition scr_pactz : scripts := SCR [false; true; false; true] [] [].
Definition RES_pactz := Eval vm_compute in sym_exec SEGS 200 true [0x52490] scr_pactz ss_actb [].
Lemma RES_pactz_ok : sym_exec SEGS 200 true [0x52490] scr_pactz (SS 0x52418 sr_actb [] kn_actb 39) [] = RES_pactz.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pactd : scripts := SCR [false; true; false; false] [] [].
Definition RES_pactd := Eval vm_compute in sym_exec SEGS 200 true [0x52490] scr_pactd ss_actb [].
Lemma RES_pactd_ok : sym_exec SEGS 200 true [0x52490] scr_pactd (SS 0x52418 sr_actb [] kn_actb 39) [] = RES_pactd.
Proof. vm_compute. reflexivity. Qed.
End AXF_actb.

Import ListNotations AX2 AX2S.

Module AXF_act.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_sc := EVar 32.
Definition e_G3 := EVar 33.
Definition e_mem3 := EVar 34.
Definition e_hb := EVar 35.
Definition e_freed3 := EVar 36.
Definition e_W3 := EVar 37.
Definition sr_act := (sr_upd (sr_upd sr_id 10 (e_G3)) 22 (ELit 614096)).
Definition kn_act : list kentry :=
  [ KRange e_sc 0 47;
    KRange e_G3 1 (2^63-1);
    KAlign e_G3 8;
    KRange e_mem3 1 (2^63-1);
    KRange e_hb 0 255;
    KRange e_freed3 0 (2^32-1);
    KRange e_W3 0 (2^32-1);
    KWord (SA e_G3 16) 8 e_mem3;
    KWord (SA e_mem3 8) 1 e_hb;
    KWord (SA e_G3 28) 4 e_freed3;
    KWord (SA e_G3 32) 4 e_W3;
    KWr (SA e_G3 24) (ELit 8) ].
Definition scr_act : scripts := SCR [false; true; true] [] [].
Definition ss_act := SS 0x52418 sr_act [] kn_act 38.
Definition RUN_act := sym_exec SEGS 200 true [0x52490] scr_act ss_act [].

Definition scr_pact : scripts := SCR [false; true; true] [] [].
Definition RES_pact := Eval vm_compute in sym_exec SEGS 200 true [0x52490] scr_pact ss_act [].
Lemma RES_pact_ok : sym_exec SEGS 200 true [0x52490] scr_pact (SS 0x52418 sr_act [] kn_act 38) [] = RES_pact.
Proof. vm_compute. reflexivity. Qed.
End AXF_act.

Module AXF_actz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ AxTry.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section ACT.
Context {fx : FPState}.

Definition VALS_act (sc G3 mem3 hb freed3 W3 : Z) : list Z := [sc; G3; mem3; hb; freed3; W3].

Record act_pre (regs : bvmap 5 word) (m : word -> option byte) (sc G3 mem3 hb freed3 W3 : Z) : Prop := {
  act_R10 : getr regs 10 = wa G3 ;
  act_R22 : getr regs 22 = wa 614096 ;
  act_rng_sc : 0 <= sc <= 47 ;
  act_rng_G3 : 1 <= G3 <= 2^63-1 ;
  act_rng_mem3 : 1 <= mem3 <= 2^63-1 ;
  act_rng_hb : 0 <= hb <= 255 ;
  act_rng_freed3 : 0 <= freed3 <= 2^32-1 ;
  act_rng_W3 : 0 <= W3 <= 2^32-1 ;
  act_ka2 : G3 mod 8 = 0 ;
  act_kw7 : rdn SEGS m (wa (G3 + 16)) 8 = Some (word_to_le_bytes 8 (wa mem3)) ;
  act_kw8 : rdn SEGS m (wa (mem3 + 8)) 1 = Some (word_to_le_bytes 1 (wa hb)) ;
  act_kw9 : rdn SEGS m (wa (G3 + 28)) 4 = Some (word_to_le_bytes 4 (wa freed3)) ;
  act_kw10 : rdn SEGS m (wa (G3 + 32)) 4 = Some (word_to_le_bytes 4 (wa W3)) ;
  act_kwr11 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (G3 + 24 + d)) k = true
}.


#[using="Type"] Lemma act_setup : forall regs m sc G3 mem3 hb freed3 W3, act_pre regs m sc G3 mem3 hb freed3 W3 ->
  regs_ok (Ez regs (VALS_act sc G3 mem3 hb freed3 W3)) AXF_act.sr_act regs /\ know_ok SEGS (Ez regs (VALS_act sc G3 mem3 hb freed3 W3)) m AXF_act.kn_act.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sc G3 mem3 hb freed3 W3 P. destruct P as [act_R10 act_R22 act_rng_sc act_rng_G3 act_rng_mem3 act_rng_hb act_rng_freed3 act_rng_W3 act_ka2 act_kw7 act_kw8 act_kw9 act_kw10 act_kwr11].
  set (E := Ez regs (VALS_act sc G3 mem3 hb freed3 W3)).
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = G3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = mem3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = hb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = freed3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = W3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_act.sr_act.
    apply (regs_ok_pin E _ regs 22); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|].
    - rewrite act_R10. reflexivity.
    - rewrite act_R22. reflexivity. }
  unfold know_ok, AXF_act.kn_act.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_act.e_sc AXF_act.e_G3 AXF_act.e_mem3 AXF_act.e_hb AXF_act.e_freed3 AXF_act.e_W3 a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sc _ _ act_rng_sc eq_refl eq_refl), ?(mod64_of_range G3 _ _ act_rng_G3 eq_refl eq_refl), ?(mod64_of_range mem3 _ _ act_rng_mem3 eq_refl eq_refl), ?(mod64_of_range hb _ _ act_rng_hb eq_refl eq_refl), ?(mod64_of_range freed3 _ _ act_rng_freed3 eq_refl eq_refl), ?(mod64_of_range W3 _ _ act_rng_W3 eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply act_kwr11]; assumption).
  all: try (clear - act_rng_sc act_rng_G3 act_rng_mem3 act_rng_hb act_rng_freed3 act_rng_W3 act_ka2; lia).
  all: first [lia].
Qed.


Definition act_mem_pact (m : word -> option byte) (regs : bvmap 5 word) (sc G3 mem3 hb freed3 W3 : Z) : word -> option byte :=
  wbytes (wbytes (m) (wa (G3 + 28)) (word_to_le_bytes 4 (wa (Z.ldiff freed3 (2 ^ (Z.land hb 31 + 1) - 1))))) (wa (G3 + 24)) (word_to_le_bytes 4 (wa (Z.land freed3 (2 ^ (Z.land hb 31 + 1) - 1)))).

#[using="Type"] Theorem act_pact : forall regs m rom sc G3 mem3 hb freed3 W3, act_pre regs m sc G3 mem3 hb freed3 W3 ->
  scs_denot SEGS m (Ez regs (VALS_act sc G3 mem3 hb freed3 W3)) (snd (fst AXF_act.RES_pact)) ->
  exists R, msteps SEGS (mkst regs (wa 0x52418) m rom) (mkst R (wa 0x52490) (act_mem_pact m regs sc G3 mem3 hb freed3 W3) rom) /\
    getr R 10 = wa G3 /\ getr R 11 = wa (ext_Z true 0 4 (Z.land freed3 (2 ^ (Z.land hb 31 + 1) - 1))) /\ getr R 22 = wa 614096 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 18; 19; 20; 21; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc G3 mem3 hb freed3 W3 P Hsc. destruct (act_setup regs m sc G3 mem3 hb freed3 W3 P) as [HR HK].
  set (E := Ez regs (VALS_act sc G3 mem3 hb freed3 W3)) in *. destruct P as [act_R10 act_R22 act_rng_sc act_rng_G3 act_rng_mem3 act_rng_hb act_rng_freed3 act_rng_W3 act_ka2 act_kw7 act_kw8 act_kw9 act_kw10 act_kwr11].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = G3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = mem3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = hb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = freed3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = W3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 200 [0x52490] AXF_act.scr_pact 0x52418 AXF_act.sr_act AXF_act.kn_act 38 _ _ _ E m rom regs AXF_act.RES_pact_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_act.RES_pact fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (act_mem_pact m regs sc G3 mem3 hb freed3 W3) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold act_mem_pact. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.
    all: try (rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; apply act_avail_lew; assumption).
    all: try (rewrite zeval_sound; cbn [zeval edenot]; rewrite w_subw, w_sllw; unfold v_subw, v_sllw; rewrite ?u_wa; repeat dsc_rw; repeat dsc_mod; litmods; apply act_freed_le2; assumption).
  - clear Hms.      (* [comment removed for export] *)
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; apply act_a1; assumption)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; apply act_a1; assumption)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; apply act_a1; assumption)]|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End ACT.
End AXF_actz.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section ACTB.
Context {fx : FPState}.

Definition VALS_actb (sc G3 mem3 hb freed3 W3 bnc : Z) : list Z := [sc; G3; mem3; hb; freed3; W3; bnc].

Record actb_pre (regs : bvmap 5 word) (m : word -> option byte) (sc G3 mem3 hb freed3 W3 bnc : Z) : Prop := {
  actb_R10 : getr regs 10 = wa G3 ;
  actb_R22 : getr regs 22 = wa 614096 ;
  actb_rng_sc : 0 <= sc <= 47 ;
  actb_rng_G3 : 1 <= G3 <= 2^63-1 ;
  actb_rng_mem3 : 1 <= mem3 <= 2^63-1 ;
  actb_rng_hb : 0 <= hb <= 255 ;
  actb_rng_freed3 : 0 <= freed3 <= 2^32-1 ;
  actb_rng_W3 : 0 <= W3 <= 2^32-1 ;
  actb_rng_bnc : 0 <= bnc <= 255 ;
  actb_ka2 : G3 mod 8 = 0 ;
  actb_kw7 : rdn SEGS m (wa (G3 + 16)) 8 = Some (word_to_le_bytes 8 (wa mem3)) ;
  actb_kw8 : rdn SEGS m (wa (mem3 + 8)) 1 = Some (word_to_le_bytes 1 (wa hb)) ;
  actb_kw9 : rdn SEGS m (wa (G3 + 28)) 4 = Some (word_to_le_bytes 4 (wa freed3)) ;
  actb_kw10 : rdn SEGS m (wa (G3 + 32)) 4 = Some (word_to_le_bytes 4 (wa W3)) ;
  actb_kwr11 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (G3 + 24 + d)) k = true ;
  actb_kr13 : 0 <= SCW W3 <= 63 ;
  actb_kw14 : rdn SEGS m (wa (SCW W3 + 614977)) 1 = Some (word_to_le_bytes 1 (wa bnc)) ;
  actb_kwr15 : forall d k, 0 <= d -> d + Z.of_nat k <= 1 -> store_ok SEGS m (wa (SCW W3 + 614977 + d)) k = true ;
  actb_kd16 : SCW W3 + 614977 + 1 <= G3 + 24 \/ G3 + 24 + 8 <= SCW W3 + 614977
}.


#[using="Type"] Lemma actb_setup : forall regs m sc G3 mem3 hb freed3 W3 bnc, actb_pre regs m sc G3 mem3 hb freed3 W3 bnc ->
  regs_ok (Ez regs (VALS_actb sc G3 mem3 hb freed3 W3 bnc)) AXF_actb.sr_actb regs /\ know_ok SEGS (Ez regs (VALS_actb sc G3 mem3 hb freed3 W3 bnc)) m AXF_actb.kn_actb.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sc G3 mem3 hb freed3 W3 bnc P. destruct P as [actb_R10 actb_R22 actb_rng_sc actb_rng_G3 actb_rng_mem3 actb_rng_hb actb_rng_freed3 actb_rng_W3 actb_rng_bnc actb_ka2 actb_kw7 actb_kw8 actb_kw9 actb_kw10 actb_kwr11 actb_kr13 actb_kw14 actb_kwr15 actb_kd16].
  set (E := Ez regs (VALS_actb sc G3 mem3 hb freed3 W3 bnc)).
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = G3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = mem3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = hb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = freed3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = W3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = bnc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_actb.sr_actb.
    apply (regs_ok_pin E _ regs 22); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|].
    - rewrite actb_R10. reflexivity.
    - rewrite actb_R22. reflexivity. }
  unfold know_ok, AXF_actb.kn_actb.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_actb.e_sc AXF_actb.e_G3 AXF_actb.e_mem3 AXF_actb.e_hb AXF_actb.e_freed3 AXF_actb.e_W3 AXF_actb.e_bnc AXF_actb.BNC a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sc _ _ actb_rng_sc eq_refl eq_refl), ?(mod64_of_range G3 _ _ actb_rng_G3 eq_refl eq_refl), ?(mod64_of_range mem3 _ _ actb_rng_mem3 eq_refl eq_refl), ?(mod64_of_range hb _ _ actb_rng_hb eq_refl eq_refl), ?(mod64_of_range freed3 _ _ actb_rng_freed3 eq_refl eq_refl), ?(mod64_of_range W3 _ _ actb_rng_W3 eq_refl eq_refl), ?(mod64_of_range bnc _ _ actb_rng_bnc eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try (rewrite scw_ext32 by lia).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply actb_kwr11 | apply actb_kwr15]; assumption).
  all: try (clear - actb_rng_sc actb_rng_G3 actb_rng_mem3 actb_rng_hb actb_rng_freed3 actb_rng_W3 actb_rng_bnc actb_ka2 actb_kr13; lia).
  all: first [(clear - actb_rng_sc actb_rng_G3 actb_rng_mem3 actb_rng_hb actb_rng_freed3 actb_rng_W3 actb_rng_bnc actb_ka2 actb_kr13 actb_kd16; lia) | lia].
Qed.


Definition actb_mem_pactz (m : word -> option byte) (regs : bvmap 5 word) (sc G3 mem3 hb freed3 W3 bnc : Z) : word -> option byte :=
  wbytes (wbytes (m) (wa (G3 + 28)) (word_to_le_bytes 4 (wa (Z.ldiff freed3 (2 ^ (Z.land hb 31 + 1) - 1))))) (wa (G3 + 24)) (word_to_le_bytes 4 (wa (Z.land freed3 (2 ^ (Z.land hb 31 + 1) - 1)))).

#[using="Type"] Theorem actb_pactz : forall regs m rom sc G3 mem3 hb freed3 W3 bnc, actb_pre regs m sc G3 mem3 hb freed3 W3 bnc ->
  scs_denot SEGS m (Ez regs (VALS_actb sc G3 mem3 hb freed3 W3 bnc)) (snd (fst AXF_actb.RES_pactz)) ->
  exists R, msteps SEGS (mkst regs (wa 0x52418) m rom) (mkst R (wa 0x52490) (actb_mem_pactz m regs sc G3 mem3 hb freed3 W3 bnc) rom) /\
    getr R 10 = wa G3 /\ getr R 11 = wa (ext_Z true 0 4 (Z.land freed3 (2 ^ (Z.land hb 31 + 1) - 1))) /\ getr R 22 = wa 614096 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 18; 19; 20; 21; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc G3 mem3 hb freed3 W3 bnc P Hsc. destruct (actb_setup regs m sc G3 mem3 hb freed3 W3 bnc P) as [HR HK].
  set (E := Ez regs (VALS_actb sc G3 mem3 hb freed3 W3 bnc)) in *. destruct P as [actb_R10 actb_R22 actb_rng_sc actb_rng_G3 actb_rng_mem3 actb_rng_hb actb_rng_freed3 actb_rng_W3 actb_rng_bnc actb_ka2 actb_kw7 actb_kw8 actb_kw9 actb_kw10 actb_kwr11 actb_kr13 actb_kw14 actb_kwr15 actb_kd16].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = G3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = mem3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = hb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = freed3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = W3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = bnc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 200 [0x52490] AXF_actb.scr_pactz 0x52418 AXF_actb.sr_actb AXF_actb.kn_actb 39 _ _ _ E m rom regs AXF_actb.RES_pactz_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_actb.RES_pactz fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (actb_mem_pactz m regs sc G3 mem3 hb freed3 W3 bnc) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold actb_mem_pactz. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.
    all: try (rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; apply act_avail_lew; assumption).
    all: try (rewrite zeval_sound; cbn [zeval edenot]; rewrite w_subw, w_sllw; unfold v_subw, v_sllw; rewrite ?u_wa; repeat dsc_rw; repeat dsc_mod; litmods; apply act_freed_le2; assumption).
    all: try (rewrite adenot_z; cbn [zeval edenot AXF_actb.BNC]; repeat dsc_rw; repeat dsc_mod; litmods; change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w); rewrite scw_ext32 by lia; reflexivity).
  - clear Hms.      (* [comment removed for export] *)
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; apply act_a1; assumption)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; apply act_a1; assumption)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; apply act_a1; assumption)]|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition actb_mem_pactd (m : word -> option byte) (regs : bvmap 5 word) (sc G3 mem3 hb freed3 W3 bnc : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (m) (wa (G3 + 28)) (word_to_le_bytes 4 (wa (Z.ldiff freed3 (2 ^ (Z.land hb 31 + 1) - 1))))) (wa (G3 + 24)) (word_to_le_bytes 4 (wa (Z.land freed3 (2 ^ (Z.land hb 31 + 1) - 1))))) (wa (SCW W3 + 614977)) (word_to_le_bytes 1 (wa (bnc + -1))).

#[using="Type"] Theorem actb_pactd : forall regs m rom sc G3 mem3 hb freed3 W3 bnc, actb_pre regs m sc G3 mem3 hb freed3 W3 bnc ->
  scs_denot SEGS m (Ez regs (VALS_actb sc G3 mem3 hb freed3 W3 bnc)) (snd (fst AXF_actb.RES_pactd)) ->
  exists R, msteps SEGS (mkst regs (wa 0x52418) m rom) (mkst R (wa 0x52490) (actb_mem_pactd m regs sc G3 mem3 hb freed3 W3 bnc) rom) /\
    getr R 10 = wa G3 /\ getr R 11 = wa (ext_Z true 0 4 (Z.land freed3 (2 ^ (Z.land hb 31 + 1) - 1))) /\ getr R 22 = wa 614096 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 18; 19; 20; 21; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc G3 mem3 hb freed3 W3 bnc P Hsc. destruct (actb_setup regs m sc G3 mem3 hb freed3 W3 bnc P) as [HR HK].
  set (E := Ez regs (VALS_actb sc G3 mem3 hb freed3 W3 bnc)) in *. destruct P as [actb_R10 actb_R22 actb_rng_sc actb_rng_G3 actb_rng_mem3 actb_rng_hb actb_rng_freed3 actb_rng_W3 actb_rng_bnc actb_ka2 actb_kw7 actb_kw8 actb_kw9 actb_kw10 actb_kwr11 actb_kr13 actb_kw14 actb_kwr15 actb_kd16].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = G3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = mem3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = hb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = freed3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = W3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = bnc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 200 [0x52490] AXF_actb.scr_pactd 0x52418 AXF_actb.sr_actb AXF_actb.kn_actb 39 _ _ _ E m rom regs AXF_actb.RES_pactd_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_actb.RES_pactd fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (actb_mem_pactd m regs sc G3 mem3 hb freed3 W3 bnc) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold actb_mem_pactd. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.
    all: try (rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; apply act_avail_lew; assumption).
    all: try (rewrite zeval_sound; cbn [zeval edenot]; rewrite w_subw, w_sllw; unfold v_subw, v_sllw; rewrite ?u_wa; repeat dsc_rw; repeat dsc_mod; litmods; apply act_freed_le2; assumption).
    all: try (rewrite adenot_z; cbn [zeval edenot AXF_actb.BNC]; repeat dsc_rw; repeat dsc_mod; litmods; change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w); rewrite scw_ext32 by lia; reflexivity).
  - clear Hms.      (* [comment removed for export] *)
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; apply act_a1; assumption)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; apply act_a1; assumption)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; apply act_a1; assumption)]|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End ACTB.
