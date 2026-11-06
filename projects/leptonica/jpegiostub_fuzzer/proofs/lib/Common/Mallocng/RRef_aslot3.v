(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import decidable.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes
  PureModel VmLedger AllocIface AsanCeil AgentLib.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocShape RefLrSc RefStep RefStmts RefSys RefPieces RefStep3.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng Require Import RRef_syswrap RRef_enframe RRef_ameta RRef_loops RRef_aslot1 RRef_aslot2.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng Require Import RefStepR.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac sys_hyps :=
  pose proof (mmap_refines (fx:=_)) as MM; pose proof (mmap_fixed_refines (fx:=_)) as MF;
  pose proof (mprotect_refines (fx:=_)) as MP; pose proof (munmap_refines (fx:=_)) as MU.
Ltac as_calls Hp HS Hag HI HW t :=
  sys_calls Hp HS Hag HI HW t ltac:(fun t =>
    let am := rl_name_of (bv_unsigned PC_ALLOC_META)%Z in
    let en := rl_name_of (bv_unsigned PC_ENFRAME)%Z in
    let asl := rl_name_of (bv_unsigned PC_ALLOC_SLOT)%Z in
    tryif constr_eq t am then mach_call Hp HS Hag HI HW (alloc_meta_refines (fx:=_))
    else tryif constr_eq t en then mach_call Hp HS Hag HI HW (enframe_refines (fx:=_))
    else tryif constr_eq t asl then match goal with REC : aslot_at _ |- _ => mach_call Hp HS Hag HI HW REC end
    else mach_jal Hp HS).

Lemma addiw1_nat : forall c : word, bv_unsigned c < 256 ->
  v_addiw c 1 = Z_to_bv 64 (Z.of_nat (S (Z.to_nat (bv_unsigned c)))).
Proof.
  intros c Hc. pose proof (u64_range c). apply bv_eq. unfold v_addiw.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31); lia).
  rewrite !Z_to_bv_unsigned. f_equal. rewrite Nat2Z.inj_succ, Z2Nat.id by lia. lia.
Qed.

Section Pieces4.
Context {fx : FPState} {RL : Reloc} {RC : RelocCode RL} {RS : RelocSites RL}.
#[local] Existing Instance reloc_layout.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition NESTED_WL : list Z := [0;1;5;6;7;8;10;11;12;13;14;15;16;17;18;21;22;25;28;29;30;31]%Z.

Lemma as_nested_piece {B} : forall (fuel' : nat) md (R : bvmap 5 word) mm rom (s0 s : mstate)
    (sp s7 pm sc m size cnt1 a4 : word)
    (K : word -> M B) (P : B -> mstate -> Prop) (L : B -> mstate -> TSet),
  aslot_at fuel' ->
  md_pure md -> magree s mm -> minv s0 s ->
  getr R 2 = v_addi sp (-144) -> getr R 4 = A_TP ->
  getr R 23 = s7 -> getr R 21 = pm -> getr R 8 = sc -> getr R 9 = m -> getr R 24 = size ->
  getr R 19 = cnt1 -> getr R 14 = a4 -> getr R 22 = A_LOCK -> getr R 25 = A_SIZE_CLASSES ->
  bv_unsigned cnt1 < 256 ->
  bv_unsigned sp mod 16 = 0 ->
  ms_lo s0 <= bv_unsigned sp - (alloc_slot_D fuel' + 144) -> bv_unsigned sp <= ms_hi s0 ->
  (forall a, bv_unsigned sp - (alloc_slot_D fuel' + 144) <= bv_unsigned a < bv_unsigned sp -> mm a <> None) ->
  tsafe (MallocTree.mbind (as_nested fuel' (at_ sp (-144)) s7 pm sc m size cnt1 a4) K s) P ->
  (forall x s' mm' R',
     magree s' mm' -> minv s0 s' ->
     (forall a, ms_lo s0 <= bv_unsigned a < ms_hi s0 ->
                ~ (bv_unsigned sp - (alloc_slot_D fuel' + 144) <= bv_unsigned a < bv_unsigned sp - 96) -> mm' a = mm a) ->
     (forall a, bv_unsigned sp - (alloc_slot_D fuel' + 144) <= bv_unsigned a < bv_unsigned sp - 96 -> mm' a <> None) ->
     (forall r, wreg NESTED_WL r = false -> getr R' r = getr R r) ->
     getr R' 10 = x ->
     tsafe (K x s') P ->
     realizes ml_segs (mkCfg (mkst R' (pc+ PC_ALLOC_SLOT 0x860) mm' rom) (with_vmmaps (ms_vm s') md)) (tshape (K x s') L)) ->
  realizes ml_segs (mkCfg (mkst R (pc+ PC_ALLOC_SLOT 0x310) mm rom) (with_vmmaps (ms_vm s) md))
           (tshape (MallocTree.mbind (as_nested fuel' (at_ sp (-144)) s7 pm sc m size cnt1 a4) K s) L).
Proof.
  intros fuel' md R mm rom s0 s sp s7 pm sc m size cnt1 a4 K P L REC Hp Hag HI H2 H4 H23 H21 H8 H9 H24 H19 H14 H22 H25
         Hcnt1 Hal Hlo Hhi Hstk HS HK.
  pose proof I as Hret. note_win HI. sys_hyps.
  pose proof HI as HI0. destruct HI0 as (_ & _ & _ & Hlo0 & _ & Hhi64 & _).
  pose proof (alloc_slot_D_ge fuel') as HDge.
  pose proof (mwin_init s0 mm sp (alloc_slot_D fuel' + 144) Hstk) as HW.
  unfold as_nested, NESTED_WL in HS |- *. munf. mnorm HS.
  (* [comment removed for export] *)
  mrunx_until Hp HS Hag HI HW HK Hret as_calls (bv_unsigned PC_ALLOC_SLOT + 0x31c).
  mach_join Hp HS Hag HI HW (bv_unsigned PC_ALLOC_SLOT + 0x3d4) [10;12;13;14]%Z [14]%Z.
  (* [comment removed for export] *)
  mrunx_until Hp HS Hag HI HW HK Hret as_calls (bv_unsigned PC_ALLOC_SLOT + 0x3e0).
  mstepx Hp HS Hag HI HW HK Hret as_calls.
  { (* [comment removed for export] *)
    use_piece2 (as_fail_piece1 _) sp (alloc_slot_D fuel' + 144) Hp Hag HI HW HS.
    intros x HX HS. mnorm HS. piece_exit HK K Hag HI HS. }
  (* [comment removed for export] *)
  mrunx_until Hp HS Hag HI HW HK Hret as_calls (bv_unsigned PC_ALLOC_SLOT + 0x438).
  (* [comment removed for export] *)
  cur_mstate HS ltac:(fun sb => eapply (zl_run (Z.to_nat (bv_unsigned cnt1)) _ _ _ _ _ _ _ sb));
    [ mpure Hp | exact Hag | exact HI | val_tac | val_tac
    | regnorm; apply addiw1_nat; exact Hcnt1
    | rewrite Nat2Z.inj_succ, Z2Nat.id by (pose proof (u64_range cnt1); lia); clear -Hcnt1; lia
    | exact HS | ].
  clear HS Hag.
  intros sz mmz Rz Hag HIz HJz Hkeepz HS.
  clear HI; rename HIz into HI; note_win HI; frame_facts HW mmz; keep_facts Hkeepz. mnorm HS.
  (* [comment removed for export] *)
  mrunx_until Hp HS Hag HI HW HK Hret as_calls (bv_unsigned PC_ALLOC_SLOT + 0x708).
  use_piece as_tail_piece Hp Hag HI HW HS.
  intros x HX HS. mnorm HS.
  piece_exit HK K Hag HI HS.
Qed.

End Pieces4.




(* [comment removed for export] *)
Ltac br_15478 Hp HS sc pg a4 :=
  let t := rl_name_of (bv_unsigned PC_ALLOC_SLOT + 0x60c)%Z in
  cur_pc ltac:(fun u => tryif constr_eq u t then
    (let Ha5 := fresh "Hc" in let Hlt := fresh "Hc" in
     destruct (b_cases (c_eq (v_andi sc 3) (Z_to_bv 64 0))) as [Ha5|Ha5];
     [ destruct (b_cases (c_ltu (v_slli pg 3) a4)) as [Hlt|Hlt];
       [ mach_br_dir Hp HS true ltac:(rewrite and_seqz_sltu, Ha5, Hlt; reflexivity)
       | mach_br_dir Hp HS false ltac:(rewrite and_seqz_sltu, Ha5, Hlt; reflexivity) ]
     | mach_br_dir Hp HS false ltac:(rewrite and_seqz_sltu, Ha5; reflexivity) ])
    else idtac).

Section Pieces5.
Context {fx : FPState} {RL : Reloc} {RC : RelocCode RL} {RS : RelocSites RL}.
#[local] Existing Instance reloc_layout.

Definition MM2_WL : list Z := [0;1;5;6;7;8;10;11;12;13;14;15;16;17;18;19;21;22;25;28;29;30;31]%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma as_mm2_piece {B} : forall md (R : bvmap 5 word) mm rom (s0 s : mstate) (sp : word) (DD : Z)
    (s7 pm sc req m size usage pg cnt1 a4 : word) (ns : bool) (sq : word)
    (K : word -> M B) (P : B -> mstate -> Prop) (L : B -> mstate -> TSet),
  md_pure md -> magree s mm -> minv s0 s ->
  getr R 2 = v_addi sp (-144) -> getr R 4 = A_TP ->
  getr R 23 = s7 -> getr R 21 = pm -> getr R 8 = sc -> getr R 18 = req -> getr R 9 = m ->
  getr R 24 = size -> getr R 10 = usage -> getr R 11 = pg -> getr R 19 = cnt1 -> getr R 14 = a4 ->
  getr R 12 = v_addi size 16 -> getr R 16 = sq -> getr R 22 = A_LOCK ->
  ns = negb (c_eq (getr R 13) (Z_to_bv 64 0)) ->
  bv_unsigned sp mod 16 = 0 -> 224 <= DD ->
  ms_lo s0 <= bv_unsigned sp - DD -> bv_unsigned sp <= ms_hi s0 ->
  (forall a, bv_unsigned sp - DD <= bv_unsigned a < bv_unsigned sp -> mm a <> None) ->
  tsafe (MallocTree.mbind (as_mm2 s7 pm sc req m size usage pg cnt1 a4 ns sq) K s) P ->
  (forall x s' mm' R',
     magree s' mm' -> minv s0 s' ->
     (forall a, ms_lo s0 <= bv_unsigned a < ms_hi s0 ->
                ~ (bv_unsigned sp - DD <= bv_unsigned a < bv_unsigned sp - 96) -> mm' a = mm a) ->
     (forall a, bv_unsigned sp - DD <= bv_unsigned a < bv_unsigned sp - 96 -> mm' a <> None) ->
     (forall r, wreg MM2_WL r = false -> getr R' r = getr R r) ->
     getr R' 10 = x ->
     tsafe (K x s') P ->
     realizes ml_segs (mkCfg (mkst R' (pc+ PC_ALLOC_SLOT 0x860) mm' rom) (with_vmmaps (ms_vm s') md)) (tshape (K x s') L)) ->
  realizes ml_segs (mkCfg (mkst R (pc+ PC_ALLOC_SLOT 0x580) mm rom) (with_vmmaps (ms_vm s) md))
           (tshape (MallocTree.mbind (as_mm2 s7 pm sc req m size usage pg cnt1 a4 ns sq) K s) L).
Proof.
  intros md R mm rom s0 s sp DD s7 pm sc req m size usage pg cnt1 a4 ns sq K P L
         Hp Hag HI H2 H4 H23 H21 H8 H18 H9 H24 H10 H11 H19 H14 H12 H16 H22 Hns
         Hal HDD Hlo Hhi Hstk HS HK.
  subst ns.
  pose proof I as Hret. note_win HI. sys_hyps.
  pose proof HI as HI0. destruct HI0 as (_ & _ & _ & Hlo0 & _ & Hhi64 & _).
  pose proof (mwin_init s0 mm sp DD Hstk) as HW.
  unfold as_mm2, MM2_WL in HS |- *. munf. lits64 HS. mnorm HS.
  (* [comment removed for export] *)
  mrunx_until Hp HS Hag HI HW HK Hret as_calls (bv_unsigned PC_ALLOC_SLOT + 0x584).
  mach_join Hp HS Hag HI HW (bv_unsigned PC_ALLOC_SLOT + 0x5a4) [16]%Z [16]%Z.
  (* [comment removed for export] *)
  mrunx_until Hp HS Hag HI HW HK Hret as_calls (bv_unsigned PC_ALLOC_SLOT + 0x5ac).
  mach_join Hp HS Hag HI HW (bv_unsigned PC_ALLOC_SLOT + 0x5c0) [10;15]%Z [10]%Z.
  (* [comment removed for export] *)
  mach_vlet (bv_unsigned PC_ALLOC_SLOT + 0x634) [5;15;16;17;19;25]%Z (fun (e : word) (R' : bvmap 5 word) => getr R' 25 = e) as CUTc HS.
  { mach_pure_l Hp HS [bv_unsigned PC_ALLOC_SLOT + 0x60c; bv_unsigned PC_ALLOC_SLOT + 0x634]%Z.
    all: br_15478 Hp HS sc pg a4.
    all: mach_pure Hp HS (bv_unsigned PC_ALLOC_SLOT + 0x634).
    all: use_vcut CUTc. }
  intros cnt2 HXc HS.
  (* [comment removed for export] *)
  mach_vlet (bv_unsigned PC_ALLOC_SLOT + 0x650) [14;15;16;19]%Z
    (fun (e : word) (R' : bvmap 5 word) => getr R' 19 = e /\ getr R' 14 = v_addi pg (-1)) as CUTn HS.
  { mach_pure Hp HS (bv_unsigned PC_ALLOC_SLOT + 0x650). all: use_vcut CUTn. }
  intros needed [HXn HXn'] HS.
  (* [comment removed for export] *)
  mach_vlet (bv_unsigned PC_ALLOC_SLOT + 0x690) [11;13;19;25]%Z
    (fun (e : word * word) (R' : bvmap 5 word) => getr R' 25 = fst e /\ getr R' 19 = snd e) as CUTp HS.
  { mach_pure Hp HS (bv_unsigned PC_ALLOC_SLOT + 0x690). all: use_vcut CUTp. }
  intros [cnt3 needed3] [HX9 HX3] HS. cbn [fst snd] in HX9, HX3. mnorm HS.
  (* [comment removed for export] *)
  mrunx_until Hp HS Hag HI HW HK Hret as_calls (bv_unsigned PC_ALLOC_SLOT + 0x6ac).
  mstepx Hp HS Hag HI HW HK Hret as_calls.
  (* [comment removed for export] *)
  all: mrunx_until Hp HS Hag HI HW HK Hret as_calls (bv_unsigned PC_ALLOC_SLOT + 0x6b0).
  all: mstepx Hp HS Hag HI HW HK Hret as_calls.
  all: let tq := rl_name_of (bv_unsigned PC_ALLOC_SLOT + 0x7d8)%Z in cur_pc ltac:(fun u => tryif constr_eq u tq then
         (use_piece2 (as_fail_piece2 _) sp DD Hp Hag HI HW HS;
          let x := fresh "x" in let HX := fresh "HX" in intros x HX HS; mnorm HS; piece_exit HK K Hag HI HS)
         else idtac).
  (* [comment removed for export] *)
  mrunx_until Hp HS Hag HI HW HK Hret as_calls (bv_unsigned PC_ALLOC_SLOT + 0x6e8).
  mach_vlet (bv_unsigned PC_ALLOC_SLOT + 0x6f4) [12]%Z (fun (e : word) (R' : bvmap 5 word) => getr R' 12 = e) as CUTa HS.
  { mach_pure Hp HS (bv_unsigned PC_ALLOC_SLOT + 0x6f4). all: use_vcut CUTa. }
  intros a2v HXa HS.
  (* [comment removed for export] *)
  mrunx_until Hp HS Hag HI HW HK Hret as_calls (bv_unsigned PC_ALLOC_SLOT + 0x708).
  use_piece as_tail_piece Hp Hag HI HW HS.
  intros x HX HS. mnorm HS.
  piece_exit HK K Hag HI HS.
Qed.

End Pieces5.
