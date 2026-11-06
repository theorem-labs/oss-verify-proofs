(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.skcms.iccprofile_info.images Require Import Asan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibDefs LibFrame LibTagsSpec FuzzContract.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsFuzzContract AsLibShadow AsLibDefs AsRtSpec AsLibTagsSpec AsLibWP1Spec AsLibTagsLib AsLibFPLib AsLibParseLib AsLibFrame AsLibEnv AsLibParseSpec AsLibKit AsLibPlace.
Import ListNotations.
Open Scope bv_scope.
Import ASX. Import ASXS.
Ltac Zify.zify_post_hook ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.   (* [comment removed for export] *)

#[local] Abbreviation SEGS := Asan.M.loaded_segments.
#[local] Abbreviation TP := 0x5d9b70%Z.
#[local] Abbreviation GF := 0x5d9240%Z.
#[local] Abbreviation DEPTH := 3584%Z.

(* [comment removed for export] *)
Ltac in_lit := cbn; repeat (first [left; reflexivity | right]).

(* [comment removed for export] *)
Lemma realign160 : forall sp : word, (bv_unsigned sp mod 16 = 0)%Z -> (176 <= bv_unsigned sp)%Z ->
  let u := bv_unsigned (alu64 ALU_AND (alu64 ALU_ADD sp (Z_to_bv 64 (-160))) (Z_to_bv 64 (-32))) in
  (u mod 32 = 0)%Z /\ (bv_unsigned sp - 176 <= u <= bv_unsigned sp - 160)%Z.
Proof.
  intros sp Hal Hge. cbv zeta. pose proof (u64_range sp).
  rewrite u_and64, u_add64, !u_lit64. unfold two64.
  change ((-32) mod 2 ^ 64)%Z with (2 ^ 64 - 2 ^ 5)%Z.
  Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.
  rewrite land_highmask by lia. lia.
  Ltac Zify.zify_post_hook ::= idtac.
Qed.

(* [comment removed for export] *)
Lemma gfool_apart :
  (forall a v, In (a, v) (aa_c64 asan_abi) -> (a + 8 <= GF \/ GF + 4 <= a)%Z) /\
  (forall a v, In (a, v) (aa_c32 asan_abi) -> (a + 4 <= GF \/ GF + 4 <= a)%Z) /\
  (forall a v, In (a, v) (aa_c8 asan_abi) -> (a + 1 <= GF \/ GF + 4 <= a)%Z) /\
  (forall a, In a (aa_r64 asan_abi) -> (a + 8 <= GF \/ GF + 4 <= a)%Z) /\
  (forall a v, In (a, v) (aa_shb asan_abi) -> (a + 1 <= GF \/ GF + 4 <= a)%Z) /\
  (forall lo hi, In (lo, hi) (aa_ro asan_abi) -> (hi <= GF \/ GF + 4 <= lo)%Z).
Proof.
  cbn -[Z.le Z.add].
  repeat split; intros;
  repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] | H : False |- _ => destruct H end;
  try match goal with H : (_, _) = (_, _) |- _ => injection H as <- <- end; try subst; cbn; lia.
Qed.

From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsLibFuzzADefs.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require AsLibFuzzA1 AsLibFuzzA2 AsLibFuzzA3 AsLibFuzzA4.
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac el_t1 := (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker.
(* [comment removed for export] *)
Local Ltac el_dm_pose x k := let v := eval vm_compute in k in lazymatch v with Zpos _ =>   (* [comment removed for export] *)
  lazymatch goal with _ : (x = k * (x / k) + x mod k)%Z |- _ => fail | _ =>
    pose proof (Z.div_mod x k ltac:(vm_compute; discriminate)); pose proof (Z.mod_pos_bound x k ltac:(vm_compute; reflexivity)) end end.
Local Ltac el_dm := repeat match goal with
  | |- context [ (?x / ?k)%Z ] => el_dm_pose x k
  | |- context [ (?x mod ?k)%Z ] => el_dm_pose x k
  | H : ?T |- _ => lazymatch T with (_ <= _)%Z => idtac | (_ < _)%Z => idtac | @eq Z _ _ => idtac | _ /\ _ => idtac | _ \/ _ => idtac end;
      match T with context [ (?x / ?k)%Z ] => el_dm_pose x k | context [ (?x mod ?k)%Z ] => el_dm_pose x k end
  end.
Local Ltac el_lia_core3 := first [ el_t1 | Zify.zify; xlia zchecker ].   (* [comment removed for export] *)
Local Ltac el_lia_core := first [ el_t1 | ((progress el_dm); el_t1) ].
Local Ltac el_goal_has_var := match goal with |- ?G => match G with context [?x] => is_var x end end.
Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].
(* [comment removed for export] *)
Definition parse0_contract (ceil : Z) : Prop := AsLibFuzzADefs.parse0_contract ceil.



Theorem as_fuzz_ok :
  (forall ceil, parse_contract_as SEGS as_asan ceil) -> (forall ceil, parse0_contract ceil) ->
  (forall ceil, getidx_contract_as SEGS as_asan ceil) -> (forall ceil, rte_contract_as SEGS as_asan ceil) ->
  (forall ceil, stkmalloc5_contract SEGS as_asan ceil) -> (forall ceil, stkfree5_contract SEGS as_asan ceil) ->
  setsh00_contract SEGS as_asan -> setshf8_contract SEGS as_asan ->
  as_fuzz_contract SEGS asan_abi.
Proof.
  intros C1 C2 C3 C4 C5 C6 C7 C8 FP regs mem rom ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 ceil.
  cbv zeta. cbn [aa_tp aa_depth aa_gfool aa_entry asan_abi].
  intros Hra Hret Hsp Htp Ha0 Ha1 Hn Hbs Hal Hdal Hclo Hsplo Hsphi Hdpl Hfslo Hfshi Hfsal Hblob Hshd Hstw Hstseg Hstsh Hgfw Hgfr Hro
         Hc64 Hc32 Hc8 Hr64 Hshb Htsd Hctxok Hctx Ht48ok Ht56ok Ht48 Ht56 Hdtls Hdtlsnz Hv24ok Hv24 Hv24nz Hfscell Hh0 Hh5 Hssl Hngc
         Hfl0 Hfl5 Hwh0 Hwh5 Hwfl0 Hwfl5 Hwfr0 Hwfr5 Hwsf0 Hwsf5.
  pose (HALL := MkFENV ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 Hra Hret Hsp Htp Ha0 Ha1 Hn Hbs Hal Hdal Hclo Hsplo Hsphi Hdpl Hfslo Hfshi Hfsal Hblob Hshd Hstw Hstseg Hstsh Hgfw Hgfr Hro Hc64 Hc32 Hc8 Hr64 Hshb Htsd Hctxok Hctx Ht48ok Ht56ok Ht48 Ht56 Hdtls Hdtlsnz Hv24ok Hv24 Hv24nz Hfscell Hh0 Hh5 Hssl Hngc Hfl0 Hfl5 Hwh0 Hwh5 Hwfl0 Hwfl5 Hwfr0 Hwfr5 Hwsf0 Hwsf5).
  pose proof (AsLibFuzzA1.phaseE ceil (C6 ceil) C8 regs mem rom ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL) as PE.
  pose proof (AsLibFuzzA1.phaseC ceil (C4 ceil) (C6 ceil) C8 regs mem rom ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL) as PC.
  pose proof (AsLibFuzzA1.phaseB2 ceil (C4 ceil) (C6 ceil) C8 regs mem rom ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL) as PB2.
  pose proof (AsLibFuzzA2.phaseB ceil (C4 ceil) regs mem rom ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL PE PC PB2) as PB.
  pose proof (AsLibFuzzA3.phaseA1 ceil (C3 ceil) (C4 ceil) regs mem rom ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL PE PB) as PA1.
  exact (AsLibFuzzA4.fuzz_Q ceil (C1 ceil) (C5 ceil) C7 C8 (C2 ceil) FP regs mem rom ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL PA1).
Qed.
