(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep InitMem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import MM_syscalls.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import SysStepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.BothW Require Import BImg AProto ABase ABytes AKit AKit2 RT_stubs F_ammap FsKit F_sysconf30 F_mmapfnr F_apoison APoisonR_iface.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT}.
Definition ARSRV : Z := 0x78330.
End CANSEC1.
Notation RSRV_STACK := 592 (only parsing).       (* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Definition got6 (m : amem) : Prop :=
  rw_cells bsegs m 0xd1390 [C8 (Z_to_bv 64 0x16b6a8); C8 (Z_to_bv 64 0xd7378); C8 (Z_to_bv 64 0xd9b78);
                            C8 (Z_to_bv 64 0xda868); C8 (Z_to_bv 64 0xda870); C8 (Z_to_bv 64 0xda860)].

Definition arelro0 (m : amem) : Prop := forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None.

Lemma arelro0_munch : forall W m m', arelro0 m -> munch W m m' ->
  Forall (fun iv => ARELRO_HI <= fst iv \/ snd iv <= ARELRO_LO) W -> arelro0 m'.
Proof.
  intros W m m' RR MU HW i Hi. rewrite <- (RR i Hi). pose proof (MU (wa i)) as E.
  rewrite wa_unsigned in E by (unfold ARELRO_LO, ARELRO_HI in Hi; lia). apply E.
  clear -HW Hi. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *.
  split; [lia| apply IH; assumption].
Qed.

(* [comment removed for export] *)
Lemma remu_lit : forall x y, 0 <= x < 2^64 -> 0 < y < 2^64 ->
  mul_div M_REMU (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x mod y).
Proof.
  intros x y Hx Hy. unfold mul_div. rewrite !unsigned_lit by lia.
  replace (y =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  apply bv_eq. rewrite bv_modu_unsigned, !unsigned_lit; [reflexivity| | lia | lia].
  split; [apply Z.mod_pos_bound; lia|]. eapply Z.lt_trans; [apply Z.mod_pos_bound; lia| lia].
Qed.

Lemma premap_cells_frame : forall m m' W, premap_cells m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv => AIMG_HI <= fst iv) W -> premap_cells m'.
Proof.
  intros m m' W (R1 & R2 & R3 & R4 & R5 & R6 & R7) MU WM HW. unfold AIMG_HI in HW.
  assert (D : forall A k, 0 <= k -> A + k <= 0x67f000 -> disjoint_from W A k).
  { clear -HW. intros A k Hk HA. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *. split; [lia| apply IH; assumption]. }
  unfold premap_cells. repeat lazymatch goal with |- _ /\ _ => split end;
    first [ apply premap_canary_any
          | (eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn; apply D; lia]) ].
Qed.

Lemma got6_frame : forall m m' W, got6 m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv => AIMG_HI <= fst iv) W -> got6 m'.
Proof.
  intros m m' W R MU WM HW. unfold AIMG_HI in HW.
  assert (D : forall A k, 0 <= k -> A + k <= 0x67f000 -> disjoint_from W A k).
  { clear -HW. intros A k Hk HA. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *. split; [lia| apply IH; assumption]. }
  unfold got6. eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn; apply D; lia].
Qed.

Definition rsrv_post (RNG : footprint) (sp : word) (beg size lo : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
     fp_le RNG RNG' /\ fp_bw RNG'
  /\ munch [(bv_unsigned sp - RSRV_STACK, bv_unsigned sp); (beg, beg + size)]%Z m m' /\ wmono bsegs m m'
  /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
  /\ rw_cells bsegs m' beg [CB (Z.to_nat size) (repeat (Z_to_bv 8 0) (Z.to_nat size))]
  /\ rng RNG' beg size
  /\ got6 m' /\ premap_cells m' /\ arelro0 m'.

(* [comment removed for export] *)
End CANSEC2.
