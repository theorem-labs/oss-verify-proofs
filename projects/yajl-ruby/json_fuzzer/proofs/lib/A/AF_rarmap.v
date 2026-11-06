(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SysStepA MmStep AImages AImageFacts LazyModel NodesA ImplRzA NodesA_mm StepA2.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA.examples Require Import X_mmap_fixed.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AF_mmfix0 AF_mmfix1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac lia ::=
  first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTuning.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition a_rar_map := 0x6fb6c.
Definition a_rar_map_ret := 0x6fb98.       (* [comment removed for export] *)

Section X1.
Variable P : acc -> Prop.
Hypothesis PDATA : forall a n, 0xa4000 <= a -> a + Z.of_nat n <= 0x603000 -> P (Z_to_bv 64 a, n).

Definition rar_W (sp : word) (A L : Z) : list ivl := [(bv_unsigned sp - 400, bv_unsigned sp); (A, A + mmap_len L)].
(* [comment removed for export] *)
Definition rar_ret (r : word) : bool := negb (is_err r) && negb (bv_unsigned r =? 0).

Definition rar_map_gen_post {X} (R : X -> word -> bool -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A L : Z) (lo : Z) (m : mem) (a : X) : machine_state -> Prop :=
  fun ms' => exists (r : word) (u : bool) m',
    (rar_ret r = true ->
       (exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m' (seg_rom asegs))
       /\ stk asegs m' lo (bv_unsigned sp))
    /\ munch (rar_W sp A L) m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ statics m'
    /\ (u = true -> rw_cells asegs m' A [CB (Z.to_nat (mmap_len L)) (repeat (Z_to_bv 8 0) (Z.to_nat (mmap_len L)))])
    /\ R a r u.

Lemma rar_map_gen_specA : forall {X} (dec : resp -> option X) (R : X -> word -> bool -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (A L : Z) (lo : Z),
  (forall rsp a, dec rsp = Some a -> exists r u, R a r u /\ rsp = zshape A L r u) ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 400 -> bv_unsigned sp <= 2^47 ->
  mem_inv asegs m -> statics m ->
  a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 L ->
  A mod 4096 = 0 -> L mod 4096 = 0 ->
  a_image_end <= A -> 0 < L -> A + mmap_len L <= lo ->
  (forall a n, lo <= a -> a + Z.of_nat n <= bv_unsigned sp -> P (Z_to_bv 64 a, n)) ->
  implA asegs (at_nodeA asegs) P (enode (NMmap A L 3 MAP_FIXED_RW) dec)
       (epost (rar_map_gen_post R ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A L lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 a_rar_map) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until lo. intros DEC ST LOC LO SPH MI STA -> -> AA LA AI L0 AL PSTK. unfold a_rar_map.
  pose proof LOC as LOC'. aceil.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
  pose proof (mmap_len_bound L L0) as ML. pose proof (mmap_len_alignedA L LA) as MLA.
  pose proof (munch_refl (rar_W sp A L) m) as MU. unfold rar_W in MU.
  pose proof (wmono_refl asegs m) as WM.
  open_statics STA.
  iprefixA.
  carve_frame 32%nat ST.
  do 5 stepA.
  do 5 stepA.
  stepA.
  do 3 stepA.
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  icallxA (mmap_fixed_gen_specA P PDATA dec R (Z_to_bv 64 a_rar_map_ret) (Z_to_bv 64 (bv_unsigned sp + -32)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A L 1 lo);
    rewrite ?USP;
    [ exact DEC | exact ST | exact LOC' | lia | lia | exact MI | close_statics | reflexivity | reflexivity | reflexivity | right; reflexivity
    | exact AA | exact LA | exact AI | exact L0 | exact AL | intros; apply PSTK; lia | ].
  intros x ms' POST.
  destruct POST as (r & u & ra' & sp' & s4' & e4 & v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m' & E & MU' & WM' & MI' & SK' & ST' & ZB & DIE & HR).
  unfold mfr_W in MU'. rewrite USP in MU'.
  assert (MU2 : munch [(bv_unsigned sp - 400, bv_unsigned sp); (A, A + mmap_len L)] m m').
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU']. intros y; cbn; lia. }
  assert (WM2 : wmono asegs m m') by (eapply wmono_trans; [exact WM| exact WM']).
  destruct (rar_ret r) eqn:RR.
  2:{ apply evtA_done. exists r, u, m'. split; [intros H; congruence|]. split; [exact MU2|]. split; [exact WM2|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ZB| exact HR]. }
  unfold rar_ret in RR. apply andb_prop in RR. destruct RR as [RE RZ]. apply negb_true_iff in RE. apply negb_true_iff in RZ. apply Z.eqb_neq in RZ.
  assert (RRV : mfr_ret r 1 = true) by (unfold mfr_ret; rewrite RE; reflexivity).
  rewrite RRV in E, SK'. rewrite RE in E. subst ms'. clear DIE. rewrite USP in SK'.
  ret_pc_lit.
  unfold a_rar_map_ret. ret_pc_lit.
  assert (FR' : rw_cells asegs m' (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply rw_cells_transport; [exact FR| exact MU'| exact WM'|]. cbn [disjoint_from cells_size csize fst snd Nat.add]. lia. }
  clear FR MI ST. rename MI' into MI. rename SK' into ST.
  zstepA. if_cases K0; zify_cond K0; [exfalso; lia|].
  do 4 stepA.
  stepA.
  release_frame FR' ST (bv_unsigned sp).
  stepA.
  apply evtA_done. exists r, u, m'.
  split. { intros _. split; [do 14 eexists; reflexivity| exact ST]. }
  split; [exact MU2|]. split; [exact WM2|]. split; [exact MI|]. split; [exact ST'|]. split; [exact ZB| exact HR].
Qed.
End X1.
End RC__1.
