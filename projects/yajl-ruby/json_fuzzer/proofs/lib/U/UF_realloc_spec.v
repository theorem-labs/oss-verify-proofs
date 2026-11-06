(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import F_malloc_free MallocTree Malloc_iface Malloc_ifaceP F_free F_free_spec Malloc_fp F_malloc_join.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocFacts_A MallocBlocks MallocHINV MallocFacts_B MallocRealloc.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl Monad RawAlloc Realloc.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UMallocRep UMallocTree UMallocTreeX UMalloc_iface UMalloc_ifaceP UMalloc_fp UF_malloc_top UF_malloc_implT UF_realloc_hdr UF_realloc_mv UF_realloc.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require MallocFacts_inv2 MallocFacts_inv3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Notation RAREACH := (AREACH_from ref_reserved).

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition RREALLOC_SYM : Z := 0x19ad8.      (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rrealloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (b : block) (n lo B : Z) (old : list byte) (m : mem)
    (r : mstate * optr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' B
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ match snd r with
       | None => a0 = Z_to_bv 64 0 /\ RHEAP s' LB m' /\ rheap_pres LB (bv_unsigned sp) m m'
       | Some q => exists (p' : bptr) (A : Z) junk,
           let k := Z.min n (blk_size b) in
           a0 = Z_to_bv 64 A /\ A = conc (fst r) q /\ rblock_range A n
           /\ RHEAP s' ((p', A, n) :: lb_remove (blk_id b) LB) m'
           /\ rheap_pres (lb_remove (blk_id b) LB) (bv_unsigned sp) m m'
           /\ rw_cells usegs m' A [CB (Z.to_nat k) (firstn (Z.to_nat k) old); CB (Z.to_nat (n - k)) junk]
       end.

(* [comment removed for export] *)
Definition rrealloc_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (st : mstate) (LB0 : list block) (b : block) (pf : aptr)
         (n lo B : Z) (old : list byte) (errv : word),
  Permutation.Permutation LB0 LB -> strip st = ps_m s -> rmrep st m -> HINV_from ref_reserved st (ps_brk s) LB0 ->
  In b LB -> fst pf = fst (blk_slot b) -> conc st pf = blk_addr b ->
  bytes_at usegs m (blk_addr b) old -> Z.of_nat (length old) = blk_size b ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RREALLOC_STACK_MIN ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 (blk_addr b) -> a1 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  implM usegs (raw_realloc m st pf n) s
        (rrealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB b n lo B old m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RREALLOC_SYM) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
Lemma rheap_live_aptr : forall st s LB0 (b : block),
  HINV_from ref_reserved st (ps_brk s) LB0 -> In b LB0 ->
  exists pf : aptr, fst pf = fst (blk_slot b) /\ conc st pf = blk_addr b.
Proof.
  intros st s LB0 b [_ AR] Hb. pose proof (MallocFacts_inv3.areach_cinv_proof _ _ AR) as C.
  pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) b Hb) as [(g & i & bb & SL & HBg & FB & _ & _ & (off & _ & OA & _)) _ _].
  exists (aadd (blk_slot b) (UNIT * off)). split; [reflexivity|].
  rewrite conc_aadd; [rewrite OA; reflexivity|].
  destruct (go_region _ _ _ (ci_gmetas _ _ C bb g HBg)) as (r & Hr & _). rewrite <- FB, Hr. eexists; reflexivity.
Qed.

(* [comment removed for export] *)
Definition rrealloc_null_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (n lo B : Z) (m : mem)
    (r : option bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' B
    /\ rheap_pres LB (bv_unsigned sp) m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ match r with
       | None => a0 = Z_to_bv 64 0 /\ RHEAP s' LB m'
       | Some p => exists A junk,
           a0 = Z_to_bv 64 A /\ rblock_range A n
           /\ RHEAP s' ((p, A, n) :: LB) m'
           /\ rw_cells usegs m' A [CB (Z.to_nat n) junk]
       end.

Definition rrealloc_null_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (n lo B : Z) (errv : word),
  RHEAP s LB m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RREALLOC_STACK_MIN ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 0 -> a1 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  implM usegs (raw_malloc n) s
        (rrealloc_null_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RREALLOC_SYM) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)

Section SPEC.
Variable RBIG : forall gp tp s7 s8 s9 s10 s11 F fc lo B, rbig_stmt gp tp s7 s8 s9 s10 s11 F fc lo B.

Theorem rrealloc_spec_gen : rrealloc_stmt.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB st LB0 b pf n lo B old errv.
  intros PERM Hst MR [BL AR] Hb Hfst Hconc OLD LEN AUXB SB ST LO SLO ERR MI TP A0 A1 N.
  assert (Hb0 : In b LB0) by (eapply Permutation.Permutation_in; [apply Permutation.Permutation_sym; exact PERM| exact Hb]).
  pose proof (proj2 (brk_link_ps_iff st s) BL) as BLs.
  (* [comment removed for export] *)
  eapply (implM_evt usegs _ _ _ (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                                   F (Z_to_bv 64 rrealloc_entry) fc None m (seg_rom usegs))).
  { unfold RREALLOC_SYM. step. apply evt_done. reflexivity. }
  intros ms' ->.
  unfold raw_realloc.
  eapply implM_bind.
  { pose proof (rrealloc_walk_gen gp tp s7 s8 s9 s10 s11 F fc lo B LO TP (RBIG gp tp s7 s8 s9 s10 s11 F fc lo B)
                  ra sp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 t3 t4 t5 t6 m s st LB0 b pf n old errv
                  AR MR BLs Hb0 Hfst Hconc OLD LEN AUXB SB ST SLO ERR MI A0 A1 N) as W.
    unfold rimplTX in W. exact W. }
  cbv beta. intros [o1 [st' q]] s' ms1 POST. cbn [fst snd] in POST.
  unfold rreallocT_post in POST. cbn [fst snd] in POST.
  destruct POST as (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m' & errv' & -> & MR' & MI' & ST' & ERR' & AUX' & PSM & PSF & PSO & BL' & RES).
  eapply (implM_bind usegs _ _ _ (fun _ s2 ms2 => s2 = set_m (strip st') s' /\ ms2 = _)). { apply implM_upd. apply evt_done. split; reflexivity. }
  cbv beta. intros [] s'' ms2 [-> ->]. apply implM_ret. apply evt_done.
  unfold rrealloc_post. cbn [fst snd]. do 15 eexists. exists m', errv'.
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|].
  split; [exact PSF|]. split; [exact PSO|].
  assert (NDS : List.NoDup (map blk_slot LB0)) by exact (mf_nodup _ _ (MallocFacts_inv2.areach_facts_proof _ _ AR)).
  assert (HP2L : forall LB', (forall x, In x LB' -> In x (lbrm LB0 b)) -> rheap_pres (lbrm LB0 b) (bv_unsigned sp) m m' -> rheap_pres LB' (bv_unsigned sp) m m').
  { intros LB' HL HP'. eapply rheap_pres_weaken; [exact HP'| lia| exact HL]. }
  destruct q as [q|].
  - destruct RES as (bid & junk & Ha0 & BR & AR' & HP' & UCH).
    destruct b as [[bp bA] bsz]. cbn [blk_id blk_size blk_addr blk_slot fst snd] in *.
    pose proof (lb_remove_lbrm LB bp bA bsz (NoDup_map_perm blk_slot LB0 LB PERM NDS) Hb) as ELB.
    exists bid, (conc st' q), junk. cbv zeta. split; [exact Ha0|]. split; [reflexivity|]. split; [exact BR|].
    split.
    + exists st', ((bid, conc st' q, n) :: lbrm LB0 (bp, bA, bsz)). split.
      { rewrite ELB. apply Permutation.perm_skip. apply lbrm_perm. exact PERM. }
      split; [reflexivity|]. split; [exact MR'|]. split; [| exact AR'].
      apply (proj1 (brk_link_ps_iff st' _)). unfold brk_link_ps in *. cbn [ps_brk set_m]. exact BL'.
    + split; [| exact UCH]. rewrite ELB. apply HP2L; [| exact HP']. intros x Hx. eapply In_lbrm_perm; [apply Permutation.Permutation_sym; exact PERM| exact Hx].
  - destruct RES as (Ha0 & AR' & HP'). split; [exact Ha0|].
    split; [| eapply rheap_pres_weaken; [exact HP'| lia| intros x Hx; eapply Permutation.Permutation_in; [apply Permutation.Permutation_sym; exact PERM| exact Hx]]].
    exists st', LB0. split; [exact PERM|]. split; [reflexivity|]. split; [exact MR'|]. split; [| exact AR'].
    apply (proj1 (brk_link_ps_iff st' _)). unfold brk_link_ps in *. cbn [ps_brk set_m]. exact BL'.
Qed.
End SPEC.

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem rrealloc_null_spec : rrealloc_null_stmt.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv.
  intros HEAP AUXB SB ST LO SLO ERR MI TP A0 A1 N. unfold RREALLOC_STACK_MIN in SLO.
  destruct HEAP as (st & LB0 & PERM & Hst & MR & [BL AR]).
  pose proof (proj2 (brk_link_ps_iff st s) BL) as BLs.
  (* [comment removed for export] *)
  eapply (implM_evt usegs _ _ _ (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                                   F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom usegs))).
  { unfold RREALLOC_SYM. subst a0. step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } step. step. apply evt_done. reflexivity. }
  intros ms' ->.
  eapply (rraw_malloc_bridge2 st s n m); [exact Hst| |].
  { eapply (rmalloc_implT ra sp gp tp t0 t1 t2 s0 s1 a1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m m s st LB0 n lo B errv);
      first [exact AR| exact MR| exact BLs| apply unk_agree_refl| exact AUXB| exact SB| exact ST| exact LO| lia| exact ERR| exact MI| exact TP| exact A1| exact N]. }
  cbv beta. intros st' p s' ms'' r ans o' cst c POST PR F1 F2 Ecst Er.
  unfold rmallocT_post in POST. cbn [fst snd] in POST.
  destruct POST as (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m' & errv' & -> & MR' & TK' & MI' & ST' & ERR' & AUX' & HP' & PE' & REL' & BL' & PSM & PSF & PSO & _ & RES).
  unfold rrealloc_null_post. do 15 eexists. exists m', errv'.
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|].
  split. { eapply rheap_pres_weaken; [exact HP'| lia| intros x Hx; eapply Permutation.Permutation_in; [apply Permutation.Permutation_sym; exact PERM| exact Hx]]. }
  split; [exact PSF|]. split; [exact PSO|].
  destruct p as [pf|]; destruct c as [c|]; try (destruct PR; fail); subst r.
  - destruct RES as (c0 & cst0 & rg & junk & Ha0 & BR & _ & _ & _ & _ & _ & _ & UCH).
    exists (conc st' pf), junk. split; [exact Ha0|]. split; [exact BR|]. split; [| exact UCH].
    exists st', (((c, fresh_off cst c n), conc st' pf, n) :: LB0). split; [apply Permutation.perm_skip; exact PERM|].
    split; [reflexivity|]. split; [exact MR'|]. split.
    + apply (proj1 (brk_link_ps_iff st' _)). unfold brk_link_ps in *. cbn [ps_brk set_m]. exact BL'.
    + exact (areach_malloc_some st LB0 n m o' ans st' pf cst c AR ltac:(lia) F1 F2).
  - cbn in PR. destruct PR.
  - cbn in PR. destruct PR.
  - destruct RES as [Ha0 AR']. split; [exact Ha0|].
    exists st', LB0. split; [exact PERM|]. split; [reflexivity|]. split; [exact MR'|]. split; [| exact AR'].
    apply (proj1 (brk_link_ps_iff st' _)). unfold brk_link_ps in *. cbn [ps_brk set_m]. exact BL'.
Qed.
End RC__1.
