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
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ AXF_tfz.

Module AXF_t0.
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

Definition e_G := EVar 32.
Definition e_W := EVar 33.
Definition e_idx := EVar 34.
Definition e_p := EVar 35.
Definition e_avail := EVar 36.
Definition e_freed := EVar 37.
Definition e_ra := EVar 38.
Definition e_s0 := EVar 39.
Definition e_s1 := EVar 40.
Definition e_s2 := EVar 41.
Definition e_s3 := EVar 42.
Definition e_sp0 := EVar 43.
Definition STK := SA e_sp0 (-1024).
Definition sr_t0 := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 2 (EAlu ALU_ADD e_sp0 (ELit (-48)))) 8 (e_idx)) 9 (e_p)) 10 (e_G)) 11 (e_W)).
Definition kn_t0 : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KWr STK (ELit 1024);
    KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange e_idx 0 31;
    KRange e_p 5 (2^63-1);
    KRange e_avail 0 (2^32-1);
    KRange e_freed 0 (2^32-1);
    KWord (SA e_G 24) 4 e_avail;
    KWord (SA e_G 28) 4 e_freed;
    KWord (SA e_G 32) 8 e_W;
    KWord (SA (ELit 0) 0x95e63) 1 (ELit 0);
    KWord (SA e_sp0 (-8)) 8 e_ra;
    KWord (SA e_sp0 (-16)) 8 e_s0;
    KWord (SA e_sp0 (-24)) 8 e_s1;
    KWord (SA e_sp0 (-32)) 8 e_s2;
    KWord (SA e_sp0 (-40)) 8 e_s3;
    KWr (SA e_p (-3)) (ELit 3);
    KWr (SA e_G 28) (ELit 4);
    KDisj (SA e_G 0) (ELit 40) (SA e_p (-3)) (ELit 3);
    KDisj (SA (ELit 0) 0x95e63) (ELit 1) (SA e_p (-3)) (ELit 3);
    KDisj STK (ELit 1024) (SA e_p (-3)) (ELit 3);
    KDisj STK (ELit 1024) (SA e_G 0) (ELit 40) ].
Definition scr_t0 : scripts := SCR [true; true] [] [].
Definition ss_t0 := SS 0x516d0 sr_t0 [] kn_t0 44.
Definition RUN_t0 := sym_exec SEGS 100 true [0x518d0] scr_t0 ss_t0 [].

Definition scr_pt0a : scripts := SCR [true; true] [] [].
Definition RES_pt0a := Eval vm_compute in sym_exec SEGS 100 true [0x518d0] scr_pt0a ss_t0 [].
Lemma RES_pt0a_ok : sym_exec SEGS 100 true [0x518d0] scr_pt0a (SS 0x516d0 sr_t0 [] kn_t0 44) [] = RES_pt0a.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pt0b : scripts := SCR [true; false; true] [] [].
Definition RES_pt0b := Eval vm_compute in sym_exec SEGS 100 true [0x518d0] scr_pt0b ss_t0 [].
Lemma RES_pt0b_ok : sym_exec SEGS 100 true [0x518d0] scr_pt0b (SS 0x516d0 sr_t0 [] kn_t0 44) [] = RES_pt0b.
Proof. vm_compute. reflexivity. Qed.
End AXF_t0.


Module AXF_t0z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section T0.
Context {fx : FPState}.

Definition VALS_t0 (G W idx p avail freed ra s0 s1 s2 s3 sp0 : Z) : list Z := [G; W; idx; p; avail; freed; ra; s0; s1; s2; s3; sp0].

Record t0_pre (regs : bvmap 5 word) (m : word -> option byte) (G W idx p avail freed ra s0 s1 s2 s3 sp0 : Z) : Prop := {
  t0_R2 : getr regs 2 = wa (sp0 + -48) ;
  t0_R8 : getr regs 8 = wa idx ;
  t0_R9 : getr regs 9 = wa p ;
  t0_R10 : getr regs 10 = wa G ;
  t0_R11 : getr regs 11 = wa W ;
  t0_HSTK : stk_ok SEGS m (wa sp0) 1024 ;
  t0_rng_G : 1 <= G <= 2^63-1 ;
  t0_rng_W : 0 <= W <= 2^64-1 ;
  t0_rng_idx : 0 <= idx <= 31 ;
  t0_rng_p : 5 <= p <= 2^63-1 ;
  t0_rng_avail : 0 <= avail <= 2^32-1 ;
  t0_rng_freed : 0 <= freed <= 2^32-1 ;
  t0_rng_ra : 0 <= ra <= 2^64-1 ;
  t0_rng_s0 : 0 <= s0 <= 2^64-1 ;
  t0_rng_s1 : 0 <= s1 <= 2^64-1 ;
  t0_rng_s2 : 0 <= s2 <= 2^64-1 ;
  t0_rng_s3 : 0 <= s3 <= 2^64-1 ;
  t0_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  t0_ka1 : sp0 mod 16 = 0 ;
  t0_ka4 : G mod 8 = 0 ;
  t0_kw9 : rdn SEGS m (wa (G + 24)) 4 = Some (word_to_le_bytes 4 (wa avail)) ;
  t0_kw10 : rdn SEGS m (wa (G + 28)) 4 = Some (word_to_le_bytes 4 (wa freed)) ;
  t0_kw11 : rdn SEGS m (wa (G + 32)) 8 = Some (word_to_le_bytes 8 (wa W)) ;
  t0_kw12 : rdn SEGS m (wa (0 + 613987)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  t0_kw13 : rdn SEGS m (wa (sp0 + -8)) 8 = Some (word_to_le_bytes 8 (wa ra)) ;
  t0_kw14 : rdn SEGS m (wa (sp0 + -16)) 8 = Some (word_to_le_bytes 8 (wa s0)) ;
  t0_kw15 : rdn SEGS m (wa (sp0 + -24)) 8 = Some (word_to_le_bytes 8 (wa s1)) ;
  t0_kw16 : rdn SEGS m (wa (sp0 + -32)) 8 = Some (word_to_le_bytes 8 (wa s2)) ;
  t0_kw17 : rdn SEGS m (wa (sp0 + -40)) 8 = Some (word_to_le_bytes 8 (wa s3)) ;
  t0_kwr18 : forall d k, 0 <= d -> d + Z.of_nat k <= 3 -> store_ok SEGS m (wa (p + -3 + d)) k = true ;
  t0_kwr19 : forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (G + 28 + d)) k = true ;
  t0_kd20 : G + 0 + 40 <= p + -3 \/ p + -3 + 3 <= G + 0 ;
  t0_kd21 : 0 + 613987 + 1 <= p + -3 \/ p + -3 + 3 <= 0 + 613987 ;
  t0_kd22 : sp0 + -1024 + 1024 <= p + -3 \/ p + -3 + 3 <= sp0 + -1024 ;
  t0_kd23 : sp0 + -1024 + 1024 <= G + 0 \/ G + 0 + 40 <= sp0 + -1024
}.


#[using="Type"] Lemma t0_setup : forall regs m G W idx p avail freed ra s0 s1 s2 s3 sp0, t0_pre regs m G W idx p avail freed ra s0 s1 s2 s3 sp0 ->
  regs_ok (Ez regs (VALS_t0 G W idx p avail freed ra s0 s1 s2 s3 sp0)) AXF_t0.sr_t0 regs /\ know_ok SEGS (Ez regs (VALS_t0 G W idx p avail freed ra s0 s1 s2 s3 sp0)) m AXF_t0.kn_t0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G W idx p avail freed ra s0 s1 s2 s3 sp0 P. destruct P as [t0_R2 t0_R8 t0_R9 t0_R10 t0_R11 t0_HSTK t0_rng_G t0_rng_W t0_rng_idx t0_rng_p t0_rng_avail t0_rng_freed t0_rng_ra t0_rng_s0 t0_rng_s1 t0_rng_s2 t0_rng_s3 t0_rng_sp0 t0_ka1 t0_ka4 t0_kw9 t0_kw10 t0_kw11 t0_kw12 t0_kw13 t0_kw14 t0_kw15 t0_kw16 t0_kw17 t0_kwr18 t0_kwr19 t0_kd20 t0_kd21 t0_kd22 t0_kd23].
  set (E := Ez regs (VALS_t0 G W idx p avail freed ra s0 s1 s2 s3 sp0)).
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = W) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = idx) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = p) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = avail) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = freed) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = ra) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = s0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = s1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = s2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = s3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z43 : bv_unsigned (ev E 43) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_t0.sr_t0.
    apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 8); [apply (regs_ok_pin E _ regs 2); [apply regs_ok_id|]|]|]|]|].
    - rewrite t0_R2, zeval_sound. cbn [zeval edenot AXF_t0.e_G AXF_t0.e_W AXF_t0.e_idx AXF_t0.e_p AXF_t0.e_avail AXF_t0.e_freed AXF_t0.e_ra AXF_t0.e_s0 AXF_t0.e_s1 AXF_t0.e_s2 AXF_t0.e_s3 AXF_t0.e_sp0 AXF_t0.STK]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42, ?Z43. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite t0_R8. reflexivity.
    - rewrite t0_R9. reflexivity.
    - rewrite t0_R10. reflexivity.
    - rewrite t0_R11. reflexivity. }
  unfold know_ok, AXF_t0.kn_t0.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m AXF_t0.e_sp0 (wa sp0) 1024); [reflexivity | assumption | rewrite u_wa_small by lia; lia])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_t0.e_G AXF_t0.e_W AXF_t0.e_idx AXF_t0.e_p AXF_t0.e_avail AXF_t0.e_freed AXF_t0.e_ra AXF_t0.e_s0 AXF_t0.e_s1 AXF_t0.e_s2 AXF_t0.e_s3 AXF_t0.e_sp0 AXF_t0.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42, ?Z43.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range G _ _ t0_rng_G eq_refl eq_refl), ?(mod64_of_range idx _ _ t0_rng_idx eq_refl eq_refl), ?(mod64_of_range p _ _ t0_rng_p eq_refl eq_refl), ?(mod64_of_range avail _ _ t0_rng_avail eq_refl eq_refl), ?(mod64_of_range freed _ _ t0_rng_freed eq_refl eq_refl), ?(mod64_of_range sp0 _ _ t0_rng_sp0 eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply t0_kwr18 | apply t0_kwr19]; assumption).
  all: try (clear - t0_rng_G t0_rng_W t0_rng_idx t0_rng_p t0_rng_avail t0_rng_freed t0_rng_ra t0_rng_s0 t0_rng_s1 t0_rng_s2 t0_rng_s3 t0_rng_sp0 t0_ka1 t0_ka4; lia).
  all: first [(clear - t0_rng_G t0_rng_W t0_rng_idx t0_rng_p t0_rng_avail t0_rng_freed t0_rng_ra t0_rng_s0 t0_rng_s1 t0_rng_s2 t0_rng_s3 t0_rng_sp0 t0_ka1 t0_ka4 t0_kd20; lia) | (clear - t0_rng_G t0_rng_W t0_rng_idx t0_rng_p t0_rng_avail t0_rng_freed t0_rng_ra t0_rng_s0 t0_rng_s1 t0_rng_s2 t0_rng_s3 t0_rng_sp0 t0_ka1 t0_ka4 t0_kd21; lia) | (clear - t0_rng_G t0_rng_W t0_rng_idx t0_rng_p t0_rng_avail t0_rng_freed t0_rng_ra t0_rng_s0 t0_rng_s1 t0_rng_s2 t0_rng_s3 t0_rng_sp0 t0_ka1 t0_ka4 t0_kd22; lia) | (clear - t0_rng_G t0_rng_W t0_rng_idx t0_rng_p t0_rng_avail t0_rng_freed t0_rng_ra t0_rng_s0 t0_rng_s1 t0_rng_s2 t0_rng_s3 t0_rng_sp0 t0_ka1 t0_ka4 t0_kd23; lia) | lia].
Qed.


Definition t0_mem_pt0a (m : word -> option byte) (regs : bvmap 5 word) (G W idx p avail freed ra s0 s1 s2 s3 sp0 : Z) : word -> option byte :=
  wbytes (wbytes (m) (wa (p + -3)) (word_to_le_bytes 1 (wa 18446744073709551615))) (wa (p + -2)) (word_to_le_bytes 2 (wa 0)).

#[using="Type"] Theorem t0_pt0a : forall regs m rom G W idx p avail freed ra s0 s1 s2 s3 sp0, t0_pre regs m G W idx p avail freed ra s0 s1 s2 s3 sp0 ->
  scs_denot SEGS m (Ez regs (VALS_t0 G W idx p avail freed ra s0 s1 s2 s3 sp0)) (snd (fst AXF_t0.RES_pt0a)) ->
  exists R, msteps SEGS (mkst regs (wa 0x516d0) m rom) (mkst R (wa 0x518d0) (t0_mem_pt0a m regs G W idx p avail freed ra s0 s1 s2 s3 sp0) rom) /\
    getr R 1 = wa 333672 /\ getr R 2 = wa (sp0 + -48) /\ getr R 8 = wa idx /\ getr R 9 = wa p /\ getr R 10 = wa G /\ getr R 11 = wa idx /\ getr R 14 = wa 612084 /\ getr R 17 = wa 0 /\ (forall k, In k [3; 4; 5; 6; 7; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G W idx p avail freed ra s0 s1 s2 s3 sp0 P Hsc. destruct (t0_setup regs m G W idx p avail freed ra s0 s1 s2 s3 sp0 P) as [HR HK].
  set (E := Ez regs (VALS_t0 G W idx p avail freed ra s0 s1 s2 s3 sp0)) in *. destruct P as [t0_R2 t0_R8 t0_R9 t0_R10 t0_R11 t0_HSTK t0_rng_G t0_rng_W t0_rng_idx t0_rng_p t0_rng_avail t0_rng_freed t0_rng_ra t0_rng_s0 t0_rng_s1 t0_rng_s2 t0_rng_s3 t0_rng_sp0 t0_ka1 t0_ka4 t0_kw9 t0_kw10 t0_kw11 t0_kw12 t0_kw13 t0_kw14 t0_kw15 t0_kw16 t0_kw17 t0_kwr18 t0_kwr19 t0_kd20 t0_kd21 t0_kd22 t0_kd23].
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = W) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = idx) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = p) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = avail) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = freed) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = ra) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = s0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = s1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = s2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = s3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z43 : bv_unsigned (ev E 43) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x518d0] AXF_t0.scr_pt0a 0x516d0 AXF_t0.sr_t0 AXF_t0.kn_t0 44 _ _ _ E m rom regs AXF_t0.RES_pt0a_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_t0.RES_pt0a fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (t0_mem_pt0a m regs G W idx p avail freed ra s0 s1 s2 s3 sp0) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold t0_mem_pt0a. repeat (apply (f_equal3 wbytes)); try reflexivity.
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


Definition t0_mem_pt0b (m : word -> option byte) (regs : bvmap 5 word) (G W idx p avail freed ra s0 s1 s2 s3 sp0 : Z) : word -> option byte :=
  wbytes (wbytes (m) (wa (p + -3)) (word_to_le_bytes 1 (wa 18446744073709551615))) (wa (p + -2)) (word_to_le_bytes 2 (wa 0)).

#[using="Type"] Theorem t0_pt0b : forall regs m rom G W idx p avail freed ra s0 s1 s2 s3 sp0, t0_pre regs m G W idx p avail freed ra s0 s1 s2 s3 sp0 ->
  scs_denot SEGS m (Ez regs (VALS_t0 G W idx p avail freed ra s0 s1 s2 s3 sp0)) (snd (fst AXF_t0.RES_pt0b)) ->
  exists R, msteps SEGS (mkst regs (wa 0x516d0) m rom) (mkst R (wa 0x518d0) (t0_mem_pt0b m regs G W idx p avail freed ra s0 s1 s2 s3 sp0) rom) /\
    getr R 1 = wa 333672 /\ getr R 2 = wa (sp0 + -48) /\ getr R 8 = wa idx /\ getr R 9 = wa p /\ getr R 10 = wa G /\ getr R 11 = wa idx /\ getr R 14 = wa 612084 /\ getr R 17 = wa 0 /\ (forall k, In k [3; 4; 5; 6; 7; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G W idx p avail freed ra s0 s1 s2 s3 sp0 P Hsc. destruct (t0_setup regs m G W idx p avail freed ra s0 s1 s2 s3 sp0 P) as [HR HK].
  set (E := Ez regs (VALS_t0 G W idx p avail freed ra s0 s1 s2 s3 sp0)) in *. destruct P as [t0_R2 t0_R8 t0_R9 t0_R10 t0_R11 t0_HSTK t0_rng_G t0_rng_W t0_rng_idx t0_rng_p t0_rng_avail t0_rng_freed t0_rng_ra t0_rng_s0 t0_rng_s1 t0_rng_s2 t0_rng_s3 t0_rng_sp0 t0_ka1 t0_ka4 t0_kw9 t0_kw10 t0_kw11 t0_kw12 t0_kw13 t0_kw14 t0_kw15 t0_kw16 t0_kw17 t0_kwr18 t0_kwr19 t0_kd20 t0_kd21 t0_kd22 t0_kd23].
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = W) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = idx) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = p) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = avail) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = freed) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = ra) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = s0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = s1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = s2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = s3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z43 : bv_unsigned (ev E 43) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x518d0] AXF_t0.scr_pt0b 0x516d0 AXF_t0.sr_t0 AXF_t0.kn_t0 44 _ _ _ E m rom regs AXF_t0.RES_pt0b_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_t0.RES_pt0b fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (t0_mem_pt0b m regs G W idx p avail freed ra s0 s1 s2 s3 sp0) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold t0_mem_pt0b. repeat (apply (f_equal3 wbytes)); try reflexivity.
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

End T0.
End AXF_t0z.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
Abbreviation SEGS := Plain.M.loaded_segments.

Section SC.
Context {fx : FPState}.

#[using="Type"] Lemma t0_scs_b : forall regs m G W idx p avail freed ra s0 s1 s2 s3 sp0,
  1 <= G <= 2^63-1 -> 0 <= W <= 2^64-1 -> 0 <= idx <= 31 -> 5 <= p <= 2^63-1 -> 0 <= avail <= 2^32-1 -> 0 <= freed <= 2^32-1 ->
  0 <= ra <= 2^64-1 -> 0 <= s0 <= 2^64-1 -> 0 <= s1 <= 2^64-1 -> 0 <= s2 <= 2^64-1 -> 0 <= s3 <= 2^64-1 -> 2^20 <= sp0 <= 2^47 ->
  Z.testbit avail idx = false -> Z.testbit freed idx = false -> freed <> 0 -> Z.lor avail freed + 2 ^ idx = 2 ^ (Z.land W 31 + 1) - 1 ->
  scs_denot SEGS m (Ez regs (AXF_t0z.VALS_t0 G W idx p avail freed ra s0 s1 s2 s3 sp0)) (snd (fst AXF_t0.RES_pt0b)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G W idx p avail freed ra s0 s1 s2 s3 sp0 RG RW Ridx Rp Rav Rfr Rra Rs0 Rs1 Rs2 Rs3 Rsp A2 A3 F1 F2.
  set (E := Ez regs (AXF_t0z.VALS_t0 G W idx p avail freed ra s0 s1 s2 s3 sp0)).
  assert (Z33 : bv_unsigned (ev E 33) = W) by (apply zatom; [reflexivity | reflexivity | lia]).
  assert (Z34 : bv_unsigned (ev E 34) = idx) by (apply zatom; [reflexivity | reflexivity | lia]).
  assert (Z36 : bv_unsigned (ev E 36) = avail) by (apply zatom; [reflexivity | reflexivity | lia]).
  assert (Z37 : bv_unsigned (ev E 37) = freed) by (apply zatom; [reflexivity | reflexivity | lia]).
  assert (Rav32 : 0 <= avail < 2^32) by lia. assert (Rfr32 : 0 <= freed < 2^32) by lia.
  cbn [AXF_t0.RES_pt0b fst snd].
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: apply sc_br_z; cbn [zeval edenot].
  all: rewrite ?Z33, ?Z34, ?Z36, ?Z37.
  all: rewrite ?br_eq_z, ?br_ne_z, ?br_geu_z, ?br_ltu_z.
  all: rewrite ?(mod64_of_range idx _ _ Ridx eq_refl eq_refl), ?(mod64_of_range _ _ _ Rav eq_refl eq_refl), ?(mod64_of_range _ _ _ Rfr eq_refl eq_refl),
               ?(mod64_of_range W _ _ RW eq_refl eq_refl).
  all: litmods.
  all: rewrite ?(Z.mod_small idx 32) by lia.
  - rewrite (all_cond_z avail freed idx W Rav32 Rfr32 Ridx ltac:(lia) A2 A3). apply Z.eqb_eq. exact F2.
  - rewrite ext4_swrap, sx32_zero. apply Z.eqb_neq. rewrite (Z.mod_small freed _ Rfr32). exact F1.
  - rewrite !ext4_swrap, (mask2_bit_clear avail freed idx Rav32 Rfr32 Ridx A2 A3). reflexivity.
Qed.

#[using="Type"] Lemma t0_scs_a : forall regs m G W idx p avail freed ra s0 s1 s2 s3 sp0,
  1 <= G <= 2^63-1 -> 0 <= W <= 2^64-1 -> 0 <= idx <= 31 -> 5 <= p <= 2^63-1 -> 0 <= avail <= 2^32-1 -> 0 <= freed <= 2^32-1 ->
  0 <= ra <= 2^64-1 -> 0 <= s0 <= 2^64-1 -> 0 <= s1 <= 2^64-1 -> 0 <= s2 <= 2^64-1 -> 0 <= s3 <= 2^64-1 -> 2^20 <= sp0 <= 2^47 ->
  Z.testbit avail idx = false -> Z.testbit freed idx = false -> freed = 0 ->
  scs_denot SEGS m (Ez regs (AXF_t0z.VALS_t0 G W idx p avail freed ra s0 s1 s2 s3 sp0)) (snd (fst AXF_t0.RES_pt0a)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G W idx p avail freed ra s0 s1 s2 s3 sp0 RG RW Ridx Rp Rav Rfr Rra Rs0 Rs1 Rs2 Rs3 Rsp A2 A3 F1.
  set (E := Ez regs (AXF_t0z.VALS_t0 G W idx p avail freed ra s0 s1 s2 s3 sp0)).
  assert (Z33 : bv_unsigned (ev E 33) = W) by (apply zatom; [reflexivity | reflexivity | lia]).
  assert (Z34 : bv_unsigned (ev E 34) = idx) by (apply zatom; [reflexivity | reflexivity | lia]).
  assert (Z36 : bv_unsigned (ev E 36) = avail) by (apply zatom; [reflexivity | reflexivity | lia]).
  assert (Z37 : bv_unsigned (ev E 37) = freed) by (apply zatom; [reflexivity | reflexivity | lia]).
  assert (Rav32 : 0 <= avail < 2^32) by lia. assert (Rfr32 : 0 <= freed < 2^32) by lia.
  cbn [AXF_t0.RES_pt0a fst snd].
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: apply sc_br_z; cbn [zeval edenot].
  all: rewrite ?Z33, ?Z34, ?Z36, ?Z37.
  all: rewrite ?br_eq_z, ?br_ne_z, ?br_geu_z, ?br_ltu_z.
  all: rewrite ?(mod64_of_range idx _ _ Ridx eq_refl eq_refl), ?(mod64_of_range _ _ _ Rav eq_refl eq_refl), ?(mod64_of_range _ _ _ Rfr eq_refl eq_refl),
               ?(mod64_of_range W _ _ RW eq_refl eq_refl).
  all: litmods.
  all: rewrite ?(Z.mod_small idx 32) by lia.
  - rewrite ext4_swrap, F1. reflexivity.
  - rewrite !ext4_swrap, (mask2_bit_clear avail freed idx Rav32 Rfr32 Ridx A2 A3). reflexivity.
Qed.
End SC.

Section T0.
Context {fx : FPState}.

Definition t0_mem (m : word -> option byte) (p : Z) : word -> option byte :=
  wbytes (wbytes m (wa (p + -3)) (word_to_le_bytes 1 (wa 18446744073709551615))) (wa (p + -2)) (word_to_le_bytes 2 (wa 0)).

(* [comment removed for export] *)
#[using="Type"] Theorem t0_arm : forall (regs : bvmap 5 word) (m rom : word -> option byte) (G W idx p avail freed ra s0 s1 s2 s3 sp0 : Z),
  tail_pre regs m G W idx p ra s0 s1 s2 s3 sp0 ->
  0 <= avail <= 2^32-1 -> 0 <= freed <= 2^32-1 ->
  rdn SEGS m (wa (G + 24)) 4 = Some (word_to_le_bytes 4 (wa avail)) ->
  rdn SEGS m (wa (G + 28)) 4 = Some (word_to_le_bytes 4 (wa freed)) ->
  rdn SEGS m (wa (G + 32)) 8 = Some (word_to_le_bytes 8 (wa W)) ->
  rdn SEGS m (wa (0 + 613987)) 1 = Some (word_to_le_bytes 1 (wa 0)) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (G + 28 + d)) k = true) ->
  Z.testbit avail idx = false -> Z.testbit freed idx = false ->
  (freed = 0 \/ (freed <> 0 /\ Z.lor avail freed + 2 ^ idx = 2 ^ (Z.land W 31 + 1) - 1)) ->
  exists R, msteps SEGS (mkst regs (wa 0x516d0) m rom) (mkst R (wa 0x518d0) (t0_mem m p) rom) /\
    getr R 1 = wa 0x51768 /\ getr R 2 = wa (sp0 - 48) /\ getr R 8 = wa idx /\ getr R 9 = wa p /\ getr R 10 = wa G /\ getr R 11 = wa idx /\
    (forall k, In k [3; 4; 5; 6; 7; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G W idx p avail freed ra s0 s1 s2 s3 sp0 TP Rav Rfr Mav Mfr MW Mnl WG A2 A3 CASE.
  destruct TP as [R8 R9 R10 R11 R2 Rsp Asp HSTK RG AG RW Ridx Rp Rra Rs0 Rs1 Rs2 Rs3 Mra Ms0 Ms1 Ms2 Ms3 Whdr DSH DSG IH IG DHG].
  assert (P : AXF_t0z.t0_pre regs m G W idx p avail freed ra s0 s1 s2 s3 sp0).
  { constructor; try assumption.
    all: first [ (rewrite R2; f_equal; ring) | (clear - DHG; lia) | (clear - IH; lia) | (right; clear - DSH; lia) | (right; clear - DSG; lia) ]. }
  destruct CASE as [F0|(F1 & F2)].
  - destruct (AXF_t0z.t0_pt0a regs m rom G W idx p avail freed ra s0 s1 s2 s3 sp0 P
      (t0_scs_a regs m G W idx p avail freed ra s0 s1 s2 s3 sp0 RG RW Ridx Rp Rav Rfr Rra Rs0 Rs1 Rs2 Rs3 Rsp A2 A3 F0))
      as (R & Hms & T1 & T2 & T8 & T9 & T10 & T11 & _ & _ & Toth).
    exists R. split; [exact Hms|]. split; [exact T1|]. split; [rewrite T2; f_equal; ring|]. split; [exact T8|]. split; [exact T9|].
    split; [exact T10|]. split; [exact T11 | exact Toth].
  - destruct (AXF_t0z.t0_pt0b regs m rom G W idx p avail freed ra s0 s1 s2 s3 sp0 P
      (t0_scs_b regs m G W idx p avail freed ra s0 s1 s2 s3 sp0 RG RW Ridx Rp Rav Rfr Rra Rs0 Rs1 Rs2 Rs3 Rsp A2 A3 F1 F2))
      as (R & Hms & T1 & T2 & T8 & T9 & T10 & T11 & _ & _ & Toth).
    exists R. split; [exact Hms|]. split; [exact T1|]. split; [rewrite T2; f_equal; ring|]. split; [exact T8|]. split; [exact T9|].
    split; [exact T10|]. split; [exact T11 | exact Toth].
Qed.
End T0.
