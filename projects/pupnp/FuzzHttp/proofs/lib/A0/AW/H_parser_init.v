(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling Arr.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import HttpRepA AWKit AWAuto H_freelist H_ListAddTail H_httpheader_free H_init_shw AWRng.
Import ListNotations.
Open Scope Z_scope.

Definition parser_request_init_entryA : Z := 0x8a534.
Definition parser_response_init_entryA : Z := 0x8a6f4.

Ltac split_chunk FR n H1 H2 :=
  lazymatch type of FR with rw_cells ?segs ?m ?A ?cs =>
    let cs1 := eval cbv beta iota delta [firstn skipn] in (firstn n cs) in
    let cs2 := eval cbv beta iota delta [firstn skipn] in (skipn n cs) in
    change (rw_cells segs m A (cs1 ++ cs2)) in FR;
    destruct (proj1 (rw_cells_app segs m A cs1 cs2) FR) as [H1 H2]; clear FR;
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in H2;
    try (lazymatch type of H2 with rw_cells _ _ (?a + ?b + ?c)%Z _ =>
           let v := eval vm_compute in (b + c)%Z in replace (a + b + c)%Z with (a + v)%Z in H2 by lia end)
  end.

Definition pinit_k5 (P pos : Z) : list cell :=
  [C8 (wz 0); C4 (wz 400); C4 (wz 0); C4 (wz pos); C4 (wz 1); C4 (wz 0); C4 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz (P + 400)); C8 (wz 0); C4 (wz 0); C4 (wz 0)].
Definition parser_init_cells_A (m : mem) (P isreq meth pos : Z) : Prop :=
  rw_cells asegs m P [C4 (wz 1); C4 (wz 0)]
  /\ rw_cells asegs m (P + 8) [CB 216 (repeat (Z_to_bv 8 0) 216)]
  /\ rw_cells asegs m (P + 224) [C4 (wz meth); C4 (wz 0)]
  /\ rw_cells asegs m (P + 232) (mbuf_cells 0 0 0)
  /\ rw_cells asegs m (P + 264) [C8 (wz 0); C4 (wz isreq); C4 (wz 0); C4 (wz 0); C4 (wz 0)]
  /\ rw_cells asegs m (P + 288) (lhead_cells (P + 312) (P + 288) 0)
  /\ rw_cells asegs m (P + 344) (fl_cells 0 0)
  /\ rw_cells asegs m (P + 368) [C8 (wz httpheader_free_entryA); C8 (wz httpmsg_compare_entryA)]
  /\ rw_cells asegs m (P + 384) [C8 (wz 0); C8 (wz 0)]
  /\ rw_cells asegs m (P + 400) (mbuf_cells 0 0 0)
  /\ rw_cells asegs m (P + 432) (pinit_k5 P pos).

Section W.
Context {HC : HasCeiling}.
Hypothesis IC : icpt_contracts.

#[using="IC"] Lemma parser_request_init_spec_A : forall (P lo : Z) (junk : list byte)
    (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc m,
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 32 - 48 - A0_RT_STACK -> q < 2^64 -> mem_inv asegs m -> asan_env asegs m ->
  rw_cells asegs m P [CB 504 junk] -> 0x609000 <= P -> P + 504 <= alloc_ceiling -> P mod 8 = 0 -> shw m P 504 ->
  evt asegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra (wz q) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(lo, q); (P, P + 504)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo q /\ asan_env asegs m'
      /\ parser_init_cells_A m' P 1 0 0)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz parser_request_init_entryA) fc None m (seg_rom asegs)).
Proof.
  intros P lo junk ra q gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  intros ST CLO LO QHI MI AE0 PC PLO PHI PAL SHWP. unfold parser_request_init_entryA. unfold A0_RT_STACK in LO.
  a0_prologue AE0 [(lo, q); (P, P + 504)]%Z m.
  carve_frame 32%nat ST.
  walk_lia_to 0x8a560%Z. step.

  pose proof SHWP as SHW1. shw_now SHW1 MU. env_now AE0 MU WM.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (ic_memset IC) with (P := P) (c := 0) (n := 504) (lo := lo);
      first [ rng_tac | exact PC | exact MI | exact AE | exact ST | reflexivity
            | (eapply accessible_sub; [exact (proj1 SHW1) | lia | lia])
            | (eapply sh_readable_sub; [exact (proj1 (proj2 SHW1)) | lia | lia | lia])
            | lia | (unfold A0_RT_STACK; lia)
            | (unfold env_safe; apply Forall_cons; [cbn [fst snd]; lia| apply Forall_nil]) ]
    | post_call asegs mm ] end.
  clear SHW1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mz end.
  apply (rw_cells_split_CB asegs mz P [] (Z.to_nat 504) _ [] [8; 216; 8; 32; 24; 96; 16; 32; 72]%nat) in POST; [| reflexivity].
  cbn [app mk_CB_cells] in POST.
  split_chunk POST 1%nat K1 R. split_chunk R 1%nat K2 R2. split_chunk R2 1%nat K3 R3. split_chunk R3 1%nat SB R4.
  split_chunk R4 1%nat K4 R5. split_chunk R5 1%nat LL R6. split_chunk R6 1%nat ENT R7. split_chunk R7 1%nat MBj K5.
  reshape K1 [C4 (wz 0); C4 (wz 0)]. reshape K3 [C4 (wz 0); C4 (wz 0)].
  reshape K4 [C8 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0)].
  reshape K5 [C8 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0)].
  reshape K2 [CB 216 (repeat (Z_to_bv 8 0) 216)]. reshape SB [CB 32 (repeat (Z_to_bv 8 0) 32)].
  reshape LL [CB 96 (repeat (Z_to_bv 8 0) 96)]. reshape MBj [CB 32 (repeat (Z_to_bv 8 0) 32)]. reshape ENT [CB 16 (repeat (Z_to_bv 8 0) 16)].
  replace (P + Z.of_nat 8)%Z with (P + 8)%Z in K2 by lia.
  walk_lia_to 0x8a5c0%Z. step.

  pose proof SHWP as SHW1. shw_now SHW1 MU. env_now AE0 MU WM.
  lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (ic_memset IC) with (P := P + 384) (c := 0) (n := 16) (lo := lo);
      first [ rng_tac | exact ENT | exact MIx | exact AE | reflexivity
            | (eapply accessible_sub; [exact (proj1 SHW1) | lia | lia])
            | (eapply sh_readable_sub; [exact (proj1 (proj2 SHW1)) | lia | lia | lia])
            | lia | (unfold A0_RT_STACK; lia)
            | (unfold env_safe; apply Forall_cons; [cbn [fst snd]; lia| apply Forall_nil]) | eassumption ]
    | post_call asegs mm ] end.
  clear SHW1. rename POST into ENT. reshape ENT [C8 (wz 0); C8 (wz 0)].
  walk_lia_to 0x8a5d8%Z. step.

  pose proof SHWP as SHW1. shw_now SHW1 MU. env_now AE0 MU WM.
  call (ListInit_shw (P + 288) httpmsg_compare_entryA httpheader_free_entryA lo (repeat (Z_to_bv 8 0) 96)).
  all: side (try (first [ eassumption | reflexivity | (eapply shw_sub; [exact SHW1| lia| lia| lia]) | (clear - PAL; Z.div_mod_to_equations; lia)
                        | (unfold httpmsg_compare_entryA, httpheader_free_entryA; lia) | lia ])).
  clear SHW1.
  lazymatch goal with H : rw_cells asegs _ (P + 288) (llist_cells _ _ _ _ _ _ _) |- _ => rename H into LLC end.
  replace (P + 288 + 24)%Z with (P + 312)%Z in LLC by lia. unfold llist_cells, LISTNODE_SIZEOF, FREELISTSIZE in LLC.
  walk_lia_to 0x8a5e4%Z. step.

  pose proof SHWP as SHW1. shw_now SHW1 MU. env_now AE0 MU WM.
  call (membuffer_init_shw IC (P + 400) lo (repeat (Z_to_bv 8 0) 32)).
  all: side (try (first [ eassumption | reflexivity | (eapply shw_sub; [exact SHW1| lia| lia| lia]) | (clear - PAL; Z.div_mod_to_equations; lia)
                        | (unfold A0_RT_STACK; lia) | lia ])).
  clear SHW1.
  lazymatch goal with H : rw_cells asegs _ (P + 400) (mbuf_cells _ _ _) |- _ => rename H into MBC end. unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in MBC.
  walk_lia_to 0x8a5ec%Z. step.

  pose proof SHWP as SHW1. shw_now SHW1 MU. env_now AE0 MU WM.
  call (membuffer_init_shw IC (P + 232) lo (repeat (Z_to_bv 8 0) 32)).
  all: side (try (first [ eassumption | reflexivity | (eapply shw_sub; [exact SHW1| lia| lia| lia]) | (clear - PAL; Z.div_mod_to_equations; lia)
                        | (unfold A0_RT_STACK; lia) | lia ])).
  clear SHW1.
  lazymatch goal with H : rw_cells asegs _ (P + 232) (mbuf_cells _ _ _) |- _ => rename H into SBC end. unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in SBC.
  walk_lia_to 0x8a67c%Z.
  release_to q. step. step.
  env_now AE0 MU WM.
  apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|]. repeat (split; [eassumption|]).
  unfold parser_init_cells_A, pinit_k5, lhead_cells, fl_cells, mbuf_cells, MEMBUF_DEF_SIZE_INC, httpheader_free_entryA, httpmsg_compare_entryA.
  destruct (rw_cells_take3 asegs _ _ [C8 (wz 0); C8 (wz (P + 312)); C8 (wz 0); C8 (wz (P + 288)); C8 (wz 0); C8 (wz 0); C8 (wz 0)]
              [C8 (wz 0); C8 (wz 24); C4 (wz 100); C4 (wz 0)] [C8 (wz 551320); C8 (wz 551196)] LLC) as (L1 & L2 & L3).
  cbn [cells_size csize Nat.add] in L2, L3.
  replace (P + 288 + Z.of_nat 56)%Z with (P + 344)%Z in L2 by (cbn; lia). replace (P + 288 + Z.of_nat 56 + Z.of_nat 24)%Z with (P + 368)%Z in L3 by (cbn; lia).
  repeat match goal with |- _ /\ _ => split end; eassumption.
Qed.

#[using="IC"] Lemma parser_response_init_spec_A : forall (P meth lo : Z) (junk : list byte)
    (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc m,
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 48 - 48 - A0_RT_STACK -> q < 2^64 -> mem_inv asegs m -> asan_env asegs m ->
  rw_cells asegs m P [CB 504 junk] -> 0x609000 <= P -> P + 504 <= alloc_ceiling -> P mod 8 = 0 -> shw m P 504 -> 0 <= meth < 2^32 ->
  evt asegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra (wz q) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(lo, q); (P, P + 504)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo q /\ asan_env asegs m'
      /\ parser_init_cells_A m' P 0 meth 1)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz P) (wz meth) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz parser_response_init_entryA) fc None m (seg_rom asegs)).
Proof.
  intros P meth lo junk ra q gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  intros ST CLO LO QHI MI AE0 PC PLO PHI PAL SHWP METH. unfold parser_response_init_entryA. unfold A0_RT_STACK in LO.
  a0_prologue AE0 [(lo, q); (P, P + 504)]%Z m.
  carve_frame 48%nat ST.
  walk_lia_to 0x8a728%Z. step.

  pose proof SHWP as SHW1. shw_now SHW1 MU. env_now AE0 MU WM.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (ic_memset IC) with (P := P) (c := 0) (n := 504) (lo := lo);
      first [ rng_tac | exact PC | exact MI | exact AE | exact ST | reflexivity
            | (eapply accessible_sub; [exact (proj1 SHW1) | lia | lia])
            | (eapply sh_readable_sub; [exact (proj1 (proj2 SHW1)) | lia | lia | lia])
            | lia | (unfold A0_RT_STACK; lia)
            | (unfold env_safe; apply Forall_cons; [cbn [fst snd]; lia| apply Forall_nil]) ]
    | post_call asegs mm ] end.
  clear SHW1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mz end.
  apply (rw_cells_split_CB asegs mz P [] (Z.to_nat 504) _ [] [8; 216; 8; 32; 24; 96; 16; 32; 72]%nat) in POST; [| reflexivity].
  cbn [app mk_CB_cells] in POST.
  split_chunk POST 1%nat K1 R. split_chunk R 1%nat K2 R2. split_chunk R2 1%nat K3 R3. split_chunk R3 1%nat SB R4.
  split_chunk R4 1%nat K4 R5. split_chunk R5 1%nat LL R6. split_chunk R6 1%nat ENT R7. split_chunk R7 1%nat MBj K5.
  reshape K1 [C4 (wz 0); C4 (wz 0)]. reshape K3 [C4 (wz 0); C4 (wz 0)].
  reshape K4 [C8 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0)].
  reshape K5 [C8 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0)].
  reshape K2 [CB 216 (repeat (Z_to_bv 8 0) 216)]. reshape SB [CB 32 (repeat (Z_to_bv 8 0) 32)].
  reshape LL [CB 96 (repeat (Z_to_bv 8 0) 96)]. reshape MBj [CB 32 (repeat (Z_to_bv 8 0) 32)]. reshape ENT [CB 16 (repeat (Z_to_bv 8 0) 16)].
  replace (P + Z.of_nat 8)%Z with (P + 8)%Z in K2 by lia.
  walk_lia_to 0x8a788%Z. step.

  pose proof SHWP as SHW1. shw_now SHW1 MU. env_now AE0 MU WM.
  lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (ic_memset IC) with (P := P + 384) (c := 0) (n := 16) (lo := lo);
      first [ rng_tac | exact ENT | exact MIx | exact AE | reflexivity
            | (eapply accessible_sub; [exact (proj1 SHW1) | lia | lia])
            | (eapply sh_readable_sub; [exact (proj1 (proj2 SHW1)) | lia | lia | lia])
            | lia | (unfold A0_RT_STACK; lia)
            | (unfold env_safe; apply Forall_cons; [cbn [fst snd]; lia| apply Forall_nil]) | eassumption ]
    | post_call asegs mm ] end.
  clear SHW1. rename POST into ENT. reshape ENT [C8 (wz 0); C8 (wz 0)].
  walk_lia_to 0x8a7a0%Z. step.

  pose proof SHWP as SHW1. shw_now SHW1 MU. env_now AE0 MU WM.
  call (ListInit_shw (P + 288) httpmsg_compare_entryA httpheader_free_entryA lo (repeat (Z_to_bv 8 0) 96)).
  all: side (try (first [ eassumption | reflexivity | (eapply shw_sub; [exact SHW1| lia| lia| lia]) | (clear - PAL; Z.div_mod_to_equations; lia)
                        | (unfold httpmsg_compare_entryA, httpheader_free_entryA; lia) | lia ])).
  clear SHW1.
  lazymatch goal with H : rw_cells asegs _ (P + 288) (llist_cells _ _ _ _ _ _ _) |- _ => rename H into LLC end.
  replace (P + 288 + 24)%Z with (P + 312)%Z in LLC by lia. unfold llist_cells, LISTNODE_SIZEOF, FREELISTSIZE in LLC.
  walk_lia_to 0x8a7ac%Z. step.

  pose proof SHWP as SHW1. shw_now SHW1 MU. env_now AE0 MU WM.
  call (membuffer_init_shw IC (P + 400) lo (repeat (Z_to_bv 8 0) 32)).
  all: side (try (first [ eassumption | reflexivity | (eapply shw_sub; [exact SHW1| lia| lia| lia]) | (clear - PAL; Z.div_mod_to_equations; lia)
                        | (unfold A0_RT_STACK; lia) | lia ])).
  clear SHW1.
  lazymatch goal with H : rw_cells asegs _ (P + 400) (mbuf_cells _ _ _) |- _ => rename H into MBC end. unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in MBC.
  walk_lia_to 0x8a7b4%Z. step.

  pose proof SHWP as SHW1. shw_now SHW1 MU. env_now AE0 MU WM.
  call (membuffer_init_shw IC (P + 232) lo (repeat (Z_to_bv 8 0) 32)).
  all: side (try (first [ eassumption | reflexivity | (eapply shw_sub; [exact SHW1| lia| lia| lia]) | (clear - PAL; Z.div_mod_to_equations; lia)
                        | (unfold A0_RT_STACK; lia) | lia ])).
  clear SHW1.
  lazymatch goal with H : rw_cells asegs _ (P + 232) (mbuf_cells _ _ _) |- _ => rename H into SBC end. unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in SBC.
  walk_lia_to 0x8a878%Z.
  release_to q. step. step.
  env_now AE0 MU WM.
  apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|]. repeat (split; [eassumption|]).
  unfold parser_init_cells_A, pinit_k5, lhead_cells, fl_cells, mbuf_cells, MEMBUF_DEF_SIZE_INC, httpheader_free_entryA, httpmsg_compare_entryA.
  destruct (rw_cells_take3 asegs _ _ [C8 (wz 0); C8 (wz (P + 312)); C8 (wz 0); C8 (wz (P + 288)); C8 (wz 0); C8 (wz 0); C8 (wz 0)]
              [C8 (wz 0); C8 (wz 24); C4 (wz 100); C4 (wz 0)] [C8 (wz 551320); C8 (wz 551196)] LLC) as (L1 & L2 & L3).
  cbn [cells_size csize Nat.add] in L2, L3.
  replace (P + 288 + Z.of_nat 56)%Z with (P + 344)%Z in L2 by (cbn; lia). replace (P + 288 + Z.of_nat 56 + Z.of_nat 24)%Z with (P + 368)%Z in L3 by (cbn; lia).
  repeat match goal with |- _ /\ _ => split end; eassumption.
Qed.

End W.
