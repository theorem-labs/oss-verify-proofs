(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ AxTry.

Module AXF_mcp0.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_dst := EVar 32.
Definition e_q := EVar 33.
Definition e_w := EVar 34.
Definition SRC := EMd M_MUL (ELit 4) e_q.
Definition sr_mcp0 := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 1 (ELit 342748)) 10 (e_dst)) 11 (EMd M_MUL (ELit 4) e_q)) 12 (ELit 8)).
Definition kn_mcp0 : list kentry :=
  [ KRange e_dst (2^20) (2^47);
    KAlign e_dst 16;
    KRange e_q 1 (2^45);
    KRange e_w 0 (2^64-1);
    KWord (SA (EMd M_MUL (ELit 4) e_q) 0) 8 e_w;
    KWr (SA e_dst 0) (ELit 8);
    KDisj (SA e_dst 0) (ELit 8) (SA (EMd M_MUL (ELit 4) e_q) 0) (ELit 8) ].
Definition scr_mcp0 : scripts := SCR [true] [] [].
Definition ss_mcp0 := SS 0x600a8 sr_mcp0 [] kn_mcp0 35.
Definition RUN_mcp0 := sym_exec SEGS 300 true [0x53adc] scr_mcp0 ss_mcp0 [].

Definition scr_pmcp0 : scripts := SCR [true] [] [].
Definition RES_pmcp0 := Eval vm_compute in sym_exec SEGS 300 true [0x53adc] scr_pmcp0 ss_mcp0 [].
Lemma RES_pmcp0_ok : sym_exec SEGS 300 true [0x53adc] scr_pmcp0 (SS 0x600a8 sr_mcp0 [] kn_mcp0 35) [] = RES_pmcp0.
Proof. vm_compute. reflexivity. Qed.
End AXF_mcp0.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section MCP0.
Context {fx : FPState}.

Definition VALS_mcp0 (dst q w : Z) : list Z := [dst; q; w].

Record mcp0_pre (regs : bvmap 5 word) (m : word -> option byte) (dst q w : Z) : Prop := {
  mcp0_R1 : getr regs 1 = wa 342748 ;
  mcp0_R10 : getr regs 10 = wa dst ;
  mcp0_R11 : getr regs 11 = wa (4 * q) ;
  mcp0_R12 : getr regs 12 = wa 8 ;
  mcp0_rng_dst : 2^20 <= dst <= 2^47 ;
  mcp0_rng_q : 1 <= q <= 2^45 ;
  mcp0_rng_w : 0 <= w <= 2^64-1 ;
  mcp0_ka1 : dst mod 16 = 0 ;
  mcp0_kw4 : rdn SEGS m (wa (4 * q + 0)) 8 = Some (word_to_le_bytes 8 (wa w)) ;
  mcp0_kwr5 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (dst + 0 + d)) k = true ;
  mcp0_kd6 : dst + 0 + 8 <= 4 * q + 0 \/ 4 * q + 0 + 8 <= dst + 0
}.


#[using="Type"] Lemma mcp0_setup : forall regs m dst q w, mcp0_pre regs m dst q w ->
  regs_ok (Ez regs (VALS_mcp0 dst q w)) AXF_mcp0.sr_mcp0 regs /\ know_ok SEGS (Ez regs (VALS_mcp0 dst q w)) m AXF_mcp0.kn_mcp0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m dst q w P. destruct P as [mcp0_R1 mcp0_R10 mcp0_R11 mcp0_R12 mcp0_rng_dst mcp0_rng_q mcp0_rng_w mcp0_ka1 mcp0_kw4 mcp0_kwr5 mcp0_kd6].
  set (E := Ez regs (VALS_mcp0 dst q w)).
  assert (Z32 : bv_unsigned (ev E 32) = dst) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = q) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = w) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mcp0.sr_mcp0.
    apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 1); [apply regs_ok_id|]|]|]|].
    - rewrite mcp0_R1. reflexivity.
    - rewrite mcp0_R10. reflexivity.
    - rewrite mcp0_R11, zeval_sound. cbn [zeval edenot AXF_mcp0.e_dst AXF_mcp0.e_q AXF_mcp0.e_w AXF_mcp0.SRC]. rewrite ?Z32, ?Z33, ?Z34. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite mcp0_R12. reflexivity. }
  unfold know_ok, AXF_mcp0.kn_mcp0.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mcp0.e_dst AXF_mcp0.e_q AXF_mcp0.e_w AXF_mcp0.SRC a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range dst _ _ mcp0_rng_dst eq_refl eq_refl), ?(mod64_of_range q _ _ mcp0_rng_q eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply mcp0_kwr5]; assumption).
  all: try (clear - mcp0_rng_dst mcp0_rng_q mcp0_rng_w mcp0_ka1; lia).
  all: first [(clear - mcp0_rng_dst mcp0_rng_q mcp0_rng_w mcp0_ka1 mcp0_kd6; lia) | lia].
Qed.


Definition mcp0_mem_pmcp0 (m : word -> option byte) (regs : bvmap 5 word) (dst q w : Z) : word -> option byte :=
  wbytes (wbytes (m) (wa (dst + 0)) (word_to_le_bytes 4 (wa (ext_Z true 0 4 w)))) (wa (dst + 4)) (word_to_le_bytes 4 (wa (Z.shiftr w 32))).

#[using="Type"] Theorem mcp0_pmcp0 : forall regs m rom dst q w, mcp0_pre regs m dst q w ->
  scs_denot SEGS m (Ez regs (VALS_mcp0 dst q w)) (snd (fst AXF_mcp0.RES_pmcp0)) ->
  exists R, msteps SEGS (mkst regs (wa 0x600a8) m rom) (mkst R (wa 0x53adc) (mcp0_mem_pmcp0 m regs dst q w) rom) /\
    getr R 1 = wa 342748 /\ getr R 10 = wa dst /\ getr R 11 = wa ((4 * q) + 8) /\ getr R 12 = wa 0 /\ getr R 13 = wa (dst + 8) /\ getr R 14 = wa 0 /\ (forall k, In k [2; 3; 4; 5; 6; 7; 8; 9; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom dst q w P Hsc. destruct (mcp0_setup regs m dst q w P) as [HR HK].
  set (E := Ez regs (VALS_mcp0 dst q w)) in *. destruct P as [mcp0_R1 mcp0_R10 mcp0_R11 mcp0_R12 mcp0_rng_dst mcp0_rng_q mcp0_rng_w mcp0_ka1 mcp0_kw4 mcp0_kwr5 mcp0_kd6].
  assert (Z32 : bv_unsigned (ev E 32) = dst) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = q) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = w) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 300 [0x53adc] AXF_mcp0.scr_pmcp0 0x600a8 AXF_mcp0.sr_mcp0 AXF_mcp0.kn_mcp0 35 _ _ _ E m rom regs AXF_mcp0.RES_pmcp0_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mcp0.RES_pmcp0 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mcp0_mem_pmcp0 m regs dst q w) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mcp0_mem_pmcp0. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.
    all: try (rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; apply ext44_le).
  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MCP0.
