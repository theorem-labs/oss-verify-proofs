(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling Arr.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac IcptA0 AllocA0 ATacAp.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import HttpAllocA HttpRepA AWKit AWAuto HObjA HObjK H_membuffer_destroy H_freelist H_ListAddTail H_httpheader_free H_ListDestroy_seg H_ListDestroy.
Import ListNotations.
Open Scope Z_scope.

Definition httpmsg_destroy_entryA : Z := 0x869cc.

Section W.
Context {HC : HasCeiling}.
Hypothesis IC : icpt_contracts.

#[using="Type"] Lemma msegA : forall (lo P meth : Z) ra (q : Z) gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 32 -> q < 2^64 -> mem_inv asegs m -> asan_env asegs m ->
  rw_cells asegs m P [C4 (wz 1); C4 (wz meth)] -> 0x609000 <= P -> P + 440 <= alloc_ceiling -> P mod 8 = 0 -> shw m P 440 ->
  evt asegs (fun ms' => exists m',
      ms' = MS (mkR (wz 0x86a18) (wz (q + -32)) gp tp t0 t1 t2 (wz P) (wz (Z.shiftr P 3 + 2147450880)) (wz (P + 288)) (wz 1) a2 a3 a4 a5 a6 a7
                    (wz 0x7fff8000) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz ListDestroy_entryA) fc None m' (seg_rom asegs)
      /\ munch [(lo, q)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (q + -32) /\ rw_cells asegs m' (q + -32) [C8 s2; C8 s1; C8 s0; C8 ra]
      /\ rw_cells asegs m' P [C4 (wz 1); C4 (wz meth)])
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz httpmsg_destroy_entryA) fc None m (seg_rom asegs)).
Proof.
  intros lo P meth ra q gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  intros ST CLO LO QHI MI AE0 ICc PLO PHI PAL SHWP. unfold httpmsg_destroy_entryA, ListDestroy_entryA.
  a0_prologue AE0 [(lo, q)]%Z m.
  carve_frame 32%nat ST.
  walk_lia_to 0x86a14%Z.
  step.
  apply evt_done. eexists. split; [reflexivity|]. repeat (split; [eassumption|]). assumption.
Qed.

#[using="Type"] Lemma msegB : forall (P : Z) ra (q : Z) gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  0 <= P -> P + 440 < 2^64 ->
  evt asegs (fun ms' => ms' = MS (mkR (wz 0x86a20) (wz q) gp tp t0 t1 t2 (wz P) s1 (wz (P + 400)) a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (wz membuffer_destroy_entryA) fc None m (seg_rom asegs))
    (MS (mkR ra (wz q) gp tp t0 t1 t2 (wz P) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x86a18) fc None m (seg_rom asegs)).
Proof.
  intros P ra q gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P0 PHI.
  unfold membuffer_destroy_entryA.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. step. apply evt_done. reflexivity.
Qed.

#[using="Type"] Lemma msegC : forall (P : Z) ra (q : Z) gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  0 <= P -> P + 440 < 2^64 ->
  evt asegs (fun ms' => ms' = MS (mkR (wz 0x86a28) (wz q) gp tp t0 t1 t2 (wz P) s1 (wz (P + 232)) a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (wz membuffer_destroy_entryA) fc None m (seg_rom asegs))
    (MS (mkR ra (wz q) gp tp t0 t1 t2 (wz P) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x86a20) fc None m (seg_rom asegs)).
Proof.
  intros P ra q gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P0 PHI.
  unfold membuffer_destroy_entryA.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. step. apply evt_done. reflexivity.
Qed.

#[using="Type"] Lemma msegD : forall (P U : Z) ra (q : Z) gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  mem_inv asegs m -> rw_cells asegs m (P + 432) [C8 (wz U)] -> 0x609000 <= P -> P + 440 <= alloc_ceiling -> P mod 8 = 0 -> shw m P 440 ->
  0 <= U < 2^64 ->
  evt asegs (fun ms' => exists a1', ms' = MS (mkR (wz 0x86a44) (wz q) gp tp t0 t1 t2 (wz P) s1 (wz U) a1' a2 a3 a4 a5 a6 a7
                                      (wz 0x7fff8000) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (wz A0_free) fc None m (seg_rom asegs))
    (MS (mkR ra (wz q) gp tp t0 t1 t2 (wz P) s1 a0 a1 a2 a3 a4 a5 a6 a7 (wz 0x7fff8000) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x86a28) fc None m (seg_rom asegs)).
Proof.
  intros P U ra q gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  intros MI UC PLO PHI PAL SHWP UR. unfold A0_free.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  walk_lia_to 0x86a40%Z. step.
  apply evt_done. eexists. reflexivity.
Qed.

#[using="Type"] Lemma msegE : forall (lo P meth : Z) ra (q : Z) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 x18
    (F : bvmap 5 word) fc m,
  stk asegs m lo (q + -32) -> alloc_ceiling <= lo -> lo <= q - 32 -> q < 2^64 -> mem_inv asegs m ->
  rw_cells asegs m (q + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m P [C4 (wz 1); C4 (wz meth)] -> 0x609000 <= P -> P + 440 <= alloc_ceiling -> P mod 8 = 0 -> shw m P 440 ->
  evt asegs (fun ms' => exists m' a0',
      ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(P, P + 8)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo q
      /\ rw_cells asegs m' P [C4 (wz 0); C4 (wz meth)])
    (MS (mkR x1 (wz (q + -32)) gp tp t0 t1 t2 (wz P) (wz (Z.shiftr P 3 + 2147450880)) a0 a1 a2 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x86a44) fc None m (seg_rom asegs)).
Proof.
  intros lo P meth ra q gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 x18 F fc m.
  intros ST CLO LO QHI MI FR ICc PLO PHI PAL SHWP.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (munch_refl [(P, P + 8)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  walk_lia_to 0x86a60%Z.
  release_to q. step. step.
  apply evt_done. do 2 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). assumption.
Qed.

Variable FI : fs_if.
Variable AI : am_if FI.
Variable J : a0_judg FI AI.
Variable AC : am_contracts FI AI J.
Hypothesis ASL : forall lo hi, am_static FI AI lo hi -> a0_static lo hi.
Hypothesis AMS : forall lo hi, a0_static lo hi -> am_static FI AI lo hi.
Local Notation K := (am_K FI AI).
Local Notation BLK := (block K).
Local Notation BL := (list (block K)).
Local Notation lbrm k LB := (lb_remove (am_K_eqb FI AI) k LB).
Local Notation bsub := (bsub FI AI).
Local Notation dlseg := (dlseg FI AI).
Local Notation hd_addr := (hd_addr FI AI).
Local Notation last_addr := (last_addr FI AI).
Local Notation hdrs_mem := (hdrs_mem FI AI).
Local Notation hdrs_blocks := (hdrs_blocks FI AI).

Definition mbo (A cap : Z) (MBb : BL) : Prop :=
  match MBb with [] => A = 0 | [b] => b = (blk_id b, A, cap + 1) | _ => False end.
Definition ubo (U : Z) (UB : BL) : Prop :=
  match UB with [] => U = 0 | [b] => blk_addr b = U /\ U <> 0 | _ => False end.

Definition mbo_destroy_post_A (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : fsstate FI) (ns0 : Z) (LB LBK : BL) (MB lo : Z) (m : mem) (OWNED : BL) : aps FI AI -> BL -> machine_state -> Prop :=
  fun s' LB' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo q /\ asan_env asegs m' /\ RFAKE FI st m'
    /\ apx FI AI [(MB, MB + 32)] LBK q m m'
    /\ RHEAP_A FI AI s' LB' m' /\ bsub LBK LB' /\ (forall b, In b LB' -> In b LB)
    /\ (forall b, In b OWNED -> ~ In b LB')
    /\ rw_cells asegs m' MB (mbuf_cells 0 0 0)
    /\ am_nsec FI AI s' = ns0.

#[using="IC AC ASL AMS"] Lemma mbo_destroy_A : forall (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : aps FI AI) (LB LBK MBb : BL) (st : fsstate FI) (MB A len cap lo : Z),
  RHEAP_A FI AI s LB m -> RFAKE FI st m -> asan_env asegs m ->
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 32 - A0_RT_STACK -> q mod 16 = 0 -> q + 16 <= am_stack_top FI AI ->
  mem_inv asegs m ->
  rw_cells asegs m MB (mbuf_cells A len cap) -> mlocNB FI AI q st MB 32 -> MB + 32 <= alloc_ceiling -> MB mod 8 = 0 -> shw m MB 32 ->
  mbo A cap MBb -> bsub (MBb ++ LBK) LB -> NoDup (map blk_id (MBb ++ LBK)) ->
  a0 = wz MB ->
  AJ FI AI J (mbo_destroy_post_A ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st (am_nsec FI AI s) LB LBK MB lo m MBb)
    (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz membuffer_destroy_entryA) fc None m (seg_rom asegs))
    s LB.
Proof.
  intros ra q gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB LBK MBb st MB A len cap lo.
  intros HR RF AE ST CLO LO QAL QTOP MI MBC MBL MBHI MBAL SHWM MBO SUB ND ->.
  apply (bsub_app FI AI) in SUB. destruct SUB as [SUB1 SUB2].
  assert (CASE : exists LBrest, ((A = 0 /\ LBrest = LB) \/ (exists k, In (k, A, cap + 1) LB /\ LBrest = lbrm k LB)) /\ bsub LBK LBrest
                                /\ (forall b, In b LBrest -> In b LB) /\ (forall b, In b MBb -> ~ In b LBrest)).
  { destruct MBb as [|b [|b' ?]]; cbn in MBO; [| | destruct MBO].
    - exists LB. split; [left; auto|]. split; [exact SUB2|]. split; [auto| intros b0 []].
    - exists (lbrm (blk_id b) LB). split; [| split].
      + right. exists (blk_id b). split; [| reflexivity]. rewrite <- MBO. apply SUB1. left. reflexivity.
      + eapply (bsub_remove FI AI); [| exact ND]. intros y [<-|Hy]; [apply SUB1; left; reflexivity| apply SUB2; exact Hy].
      + split; [intros b0 Hb0; eapply (lb_remove_sub FI AI); exact Hb0|]. intros b0 [<-|[]] IN. exact (lb_remove_neq FI AI _ _ _ IN eq_refl). }
  destruct CASE as (LBrest & CASE & KSUB & INCL & GONEr).
  eapply (aj_mono FI AI J).
  { eapply (membuffer_destroy_spec_A IC FI AI J AC ASL AMS) with (lo := lo) (LBrest := LBrest) (st := st) (A := A) (len := len) (cap := cap);
      try eassumption; try reflexivity. apply (mlocNB_mblocA FI AI). exact MBL. }
  intros s' LB' ms' Q. unfold membuffer_destroy_post_A in Q. unfold mbo_destroy_post_A.
  destruct Q as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & Q1 & Q2 & Q3 & Q4 & Q5 & -> & Q7 & Q8 & Q9).
  do 15 eexists. exists m2. split; [reflexivity|].
  split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split.
  { eapply (apx_weaken FI AI); [exact Q5| intros y Hy; exact Hy| lia| exact KSUB]. }
  split; [exact Q7|]. split; [exact KSUB|]. split; [exact INCL|]. split; [exact GONEr|]. split; [exact Q8| exact Q9].
Qed.

Definition httpmsg_destroy_post_A (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : fsstate FI) (ns0 : Z) (LB LBK : BL) (P meth fcmp U lo : Z) (m : mem) (OWNED : BL) : aps FI AI -> BL -> machine_state -> Prop :=
  fun s' LB' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo q /\ asan_env asegs m' /\ RFAKE FI st m'
    /\ apx FI AI [(P, P + 440)] LBK q m m'
    /\ RHEAP_A FI AI s' LB' m' /\ bsub LBK LB' /\ (forall b, In b LB' -> In b LB)
    /\ (forall b, In b OWNED -> ~ In b LB')
    /\ rw_cells asegs m' P [C4 (wz 0); C4 (wz meth)]
    /\ rw_cells asegs m' (P + 288) (lhead_cells (P + 312) (P + 288) 0) /\ rw_cells asegs m' (P + 344) (fl_cells 0 0)
    /\ FFc m' (P + 288) httpheader_free_entryA fcmp
    /\ rw_cells asegs m' (P + 400) (mbuf_cells 0 0 0) /\ rw_cells asegs m' (P + 232) (mbuf_cells 0 0 0)
    /\ rw_cells asegs m' (P + 432) [C8 (wz U)]
    /\ shw m' P 440
    /\ am_nsec FI AI s' = ns0.

Definition httpmsg_destroy_stmt_A : Prop :=
  forall (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : aps FI AI) (LB LBK MBb SBb UB : BL) (st : fsstate FI)
         (ns : list (BLK * Z)) (hs : list (hdr FI AI)) (P meth fcmp Am lm cm As ls cs U lo : Z),
  RHEAP_A FI AI s LB m -> RFAKE FI st m -> asan_env asegs m ->
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 32 - 96 - 48 - A0_RT_STACK -> q mod 16 = 0 -> q + 16 <= am_stack_top FI AI ->
  mem_inv asegs m ->
  rw_cells asegs m P [C4 (wz 1); C4 (wz meth)] -> 0 <= meth < 2^32 ->
  rw_cells asegs m (P + 288) (lhead_cells (hd_addr ns (P + 312)) (last_addr ns (P + 288)) (zlength ns)) ->
  rw_cells asegs m (P + 344) (fl_cells 0 0) -> FFc m (P + 288) httpheader_free_entryA fcmp ->
  dlseg m ns (P + 288) (P + 312) -> hdrs_mem m hs -> map snd ns = map (hA FI AI) hs -> zlength ns < 2^40 -> 0 <= fcmp < 2^64 ->
  rw_cells asegs m (P + 400) (mbuf_cells Am lm cm) -> mbo Am cm MBb ->
  rw_cells asegs m (P + 232) (mbuf_cells As ls cs) -> mbo As cs SBb ->
  rw_cells asegs m (P + 432) [C8 (wz U)] -> ubo U UB ->
  mlocNB FI AI q st P 440 -> P + 440 <= alloc_ceiling -> P mod 8 = 0 -> shw m P 440 ->
  bsub (map fst ns ++ hdrs_blocks hs ++ MBb ++ SBb ++ UB ++ LBK) LB ->
  NoDup (map blk_id (map fst ns ++ hdrs_blocks hs ++ MBb ++ SBb ++ UB ++ LBK)) ->
  a0 = wz P ->
  AJ FI AI J (httpmsg_destroy_post_A ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st (am_nsec FI AI s) LB LBK P meth fcmp U lo m (map fst ns ++ hdrs_blocks hs ++ MBb ++ SBb ++ UB))
    (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz httpmsg_destroy_entryA) fc None m (seg_rom asegs))
    s LB.

#[using="IC AC ASL AMS"] Theorem httpmsg_destroy_spec_A : httpmsg_destroy_stmt_A.
Proof.
  intros ra q gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB LBK MBb SBb UB st ns hs P meth fcmp Am lm cm As ls cs U lo.
  intros HR RF AE ST CLO LO QAL QTOP MI ICc METH LC FLC FF DL HS ITEMS LEN FCMP MBC MBO SBC SBO UC UBO PL PHI PAL SHWP ASUB ND ->.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (am_stack_ok FI AI) as (TK1 & TK2 & TK3 & TK4).
  assert (LO' : lo <= q - 32 - 96 - 48 - 4096) by (unfold A0_RT_STACK in LO; exact LO). clear LO.
  assert (QC : alloc_ceiling <= q) by lia. assert (QC' : alloc_ceiling <= q + -32) by lia.
  pose proof (mlocNB_mblocA FI AI LB q st P 440 PL) as PM.
  destruct (mblocA_range FI AI s LB _ q st m P 440 HR (fun b H => H) RF PM QC ltac:(lia)) as (PLO & _ & _).

  eapply (aj_evt FI AI J). { eapply (msegA lo P meth); try eassumption; lia. }
  intros ms' (m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & IC1).
  destruct (cw_frames FI AI s LB st m m1 _ HR RF AE MU1 WM1) as (HR1 & RF1 & AE1).
  { constructor; [| constructor]. apply (cw_iv_stack FI AI); lia. }
  assert (BR : forall b, In b LB -> 0 < blk_addr b /\ 0 <= blk_size b /\ blk_addr b + blk_size b + 16 <= alloc_ceiling
                                    /\ (P + 440 <= blk_addr b \/ blk_addr b + blk_size b <= P)).
  { intros b Hb. destruct (am_block_range FI AI _ _ _ _ HR Hb) as (R1 & _ & R3 & R4 & _).
    pose proof (mlocNB_apart FI AI s LB m st q P 440 b HR RF PL Hb QC ltac:(lia)) as D. auto. }
  pose proof ASUB as ASUB0. pose proof ND as ND0.
  apply (bsub_app FI AI) in ASUB. destruct ASUB as [NSUB REST]. apply (bsub_app FI AI) in REST. destruct REST as [HSUB KSUB1].
  Ltac trm H MU WM := eapply rw_cells_transport; [exact H| exact MU| exact WM| unfold lhead_cells, fl_cells, mbuf_cells; cbn [disjoint_from cells_size csize Nat.add]; lia].
  assert (LC1 : rw_cells asegs m1 (P + 288) (lhead_cells (hd_addr ns (P + 312)) (last_addr ns (P + 288)) (zlength ns))) by (trm LC MU1 WM1).
  assert (FLC1 : rw_cells asegs m1 (P + 344) (fl_cells 0 0)) by (trm FLC MU1 WM1).
  assert (FF1 : FFc m1 (P + 288) httpheader_free_entryA fcmp) by (trm FF MU1 WM1).
  assert (MBC1 : rw_cells asegs m1 (P + 400) (mbuf_cells Am lm cm)) by (trm MBC MU1 WM1).
  assert (SBC1 : rw_cells asegs m1 (P + 232) (mbuf_cells As ls cs)) by (trm SBC MU1 WM1).
  assert (UC1 : rw_cells asegs m1 (P + 432) [C8 (wz U)]) by (trm UC MU1 WM1).
  assert (SHWP1 : shw m1 P 440) by (eapply (shw_frame _ m m1 P 440 SHWP MU1); app_ivs_tac).
  assert (DL1 : dlseg m1 ns (P + 288) (P + 312)).
  { eapply (dlseg_transport FI AI); [exact DL| exact MU1| exact WM1|]. intros b it H.
    pose proof (in_map fst _ _ H) as H'. cbn [fst] in H'. destruct (BR b (NSUB _ H')) as (? & ? & ? & _).
    destruct (dlseg_facts FI AI _ _ _ _ _ _ DL H) as (SZ0 & _). rewrite SZ0 in *. cbn. lia. }
  assert (HS1 : hdrs_mem m1 hs).
  { eapply (hdrs_mem_transport FI AI); [exact HS| exact MU1| exact WM1|]. intros h0 A n Hh HA.
    destruct (hregion_block FI AI h0 A n HA) as [k Hk]. destruct (BR _ (HSUB _ (in_hdrs_blocks FI AI _ _ _ Hh Hk))) as (? & ? & ? & _). cbn in *. lia. }
  assert (KSUB0 : bsub LBK LB).
  { intros b Hb. apply ASUB0. rewrite !in_app_iff. LiaTuning.ctauto. }
  assert (HP1 : apx FI AI [(P, P + 440)] LBK q m m1).
  { eapply (apx_seg FI AI ASL s LB _ q _ _ m m m1 HR KSUB0 MU1 WM1). constructor; [left; cbn; lia| constructor]. }
  clear MU1 WM1.

  assert (PLq : forall X n, P <= X -> X + n <= P + 440 -> mlocNB FI AI (q + -32) st X n).
  { intros X n H1 H2. eapply (mlocNB_weaken FI AI); [eapply (mlocNB_sub FI AI); [exact PL| exact H1| exact H2]| lia| auto]. }
  eapply (aj_bind FI AI J).
  { replace (P + 344) with (P + 288 + 56) in FLC1 by lia. replace (P + 312) with (P + 288 + 24) in LC1, DL1 by lia.
    eapply (ListDestroy_spec_A IC FI AI J AC ASL AMS) with (lo := lo) (L := P + 288) (LBK := MBb ++ SBb ++ UB ++ LBK) (ns := ns) (hs := hs) (st := st) (fcmp := fcmp).
    - exact HR1.
    - exact RF1.
    - exact AE1.
    - exact ST1.
    - exact CLO.
    - unfold A0_RT_STACK. clear - LO'. lia.
    - clear - QAL. Z.div_mod_to_equations. lia.
    - clear - QTOP. lia.
    - exact MI1.
    - exact LC1.
    - exact FLC1.
    - exact FF1.
    - exact DL1.
    - exact HS1.
    - exact ITEMS.
    - apply PLq; lia.
    - clear - PHI. lia.
    - clear - PAL. Z.div_mod_to_equations. lia.
    - eapply shw_sub; [exact SHWP1| lia| lia| lia].
    - exact LEN.
    - exact FCMP.
    - exact ASUB0.
    - exact ND0.
    - reflexivity.
    - reflexivity. }
  intros sx2 LB2 ms2 Q. unfold ListDestroy_post_A in Q.
  destruct Q as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MI2 & ST2 & AE2 & RF2 & HP2 & HR2 & KSUB2 & INCL2 & GONE2 & LC2 & FLC2 & FF2 & _ & NS2).
  replace (ret_pc (Z_to_bv 64 0x86a18)) with (Z_to_bv 64 0x86a18) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  replace (P + 288 + 24) with (P + 312) in LC2 by lia. replace (P + 288 + 56) with (P + 344) in FLC2 by lia.
  assert (PMc : forall (LBx : BL) mx X n, RFAKE FI st mx -> P <= X -> X + n <= P + 440 -> aclient_range FI AI LBx (q + -32) X n).
  { intros LBx mx X n RFx H1 H2. eapply (mblocA_client FI AI _ (q + -32) st mx); [exact RFx|]. apply (mlocNB_mblocA FI AI). apply PLq; assumption. }
  Ltac trx H HP PMc RF := eapply (apx_rw_cells FI AI); [exact HP| exact H| first [ apply aclient_range_above; cbn; lia | eapply PMc; [exact RF| unfold lhead_cells, fl_cells, mbuf_cells; cbn; lia| unfold lhead_cells, fl_cells, mbuf_cells; cbn; lia] ]
                                                   | unfold lhead_cells, fl_cells, mbuf_cells; cbn [disjoint_from cells_size csize Nat.add]; lia].
  assert (FR2 : rw_cells asegs m2 (q + -32) [C8 s2; C8 s1; C8 s0; C8 ra]) by (trx FR1 HP2 PMc RF1).
  assert (IC2 : rw_cells asegs m2 P [C4 (wz 1); C4 (wz meth)]) by (trx IC1 HP2 PMc RF1).
  assert (MBC2 : rw_cells asegs m2 (P + 400) (mbuf_cells Am lm cm)) by (trx MBC1 HP2 PMc RF1).
  assert (SBC2 : rw_cells asegs m2 (P + 232) (mbuf_cells As ls cs)) by (trx SBC1 HP2 PMc RF1).
  assert (UC2 : rw_cells asegs m2 (P + 432) [C8 (wz U)]) by (trx UC1 HP2 PMc RF1).
  assert (SHWP2 : shw m2 P 440).
  { eapply (mlocNB_shw_apx FI AI AMS _ _ (q + -32) st m1 m2 P 440); [apply PLq; lia| exact SHWP1| exact HP2| app_ivs_tac| exact RF1| lia]. }
  assert (HP02 : apx FI AI [(P, P + 440)] LBK q m m2).
  { eapply (apx_trans FI AI); [exact HP1|]. eapply (apx_weaken FI AI); [exact HP2| | lia|].
    - unfold sub_fp. cbn. intros y [Hy _]. lia.
    - intros b Hb. rewrite !in_app_iff. LiaTuning.ctauto. }
  clear HP1 HP2 FR1 IC1 MBC1 SBC1 UC1 LC1 FLC1 FF1 DL1 HS1 HR1 RF1 AE1 MI1 ST1 SHWP1.
  pose proof ND0 as NDt. apply nd_app in NDt. destruct NDt as (_ & _ & NDt). apply nd_app in NDt. destruct NDt as (_ & _ & NDt).

  eapply (aj_evt FI AI J). { eapply (msegB P); lia. } intros ms' ->.
  eapply (aj_bind FI AI J).
  { eapply mbo_destroy_A with (lo := lo) (MBb := MBb) (LBK := SBb ++ UB ++ LBK) (MB := P + 400) (A := Am) (len := lm) (cap := cm) (st := st).
    - exact HR2.
    - exact RF2.
    - exact AE2.
    - exact ST2.
    - exact CLO.
    - unfold A0_RT_STACK. clear - LO'. lia.
    - clear - QAL. Z.div_mod_to_equations. lia.
    - clear - QTOP. lia.
    - exact MI2.
    - exact MBC2.
    - apply PLq; lia.
    - clear - PHI. lia.
    - clear - PAL. Z.div_mod_to_equations. lia.
    - eapply shw_sub; [exact SHWP2| lia| lia| lia].
    - exact MBO.
    - exact KSUB2.
    - exact NDt.
    - reflexivity. }
  intros sx3 LB3 ms3 Q. unfold mbo_destroy_post_A in Q.
  destruct Q as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & -> & MI3 & ST3 & AE3 & RF3 & HP3 & HR3 & KSUB3 & INCL3 & GONE3 & MBC3 & NS3).
  replace (ret_pc (Z_to_bv 64 0x86a20)) with (Z_to_bv 64 0x86a20) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  assert (FR3 : rw_cells asegs m3 (q + -32) [C8 s2; C8 s1; C8 s0; C8 ra]) by (trx FR2 HP3 PMc RF2).
  assert (IC3 : rw_cells asegs m3 P [C4 (wz 1); C4 (wz meth)]) by (trx IC2 HP3 PMc RF2).
  assert (SBC3 : rw_cells asegs m3 (P + 232) (mbuf_cells As ls cs)) by (trx SBC2 HP3 PMc RF2).
  assert (UC3 : rw_cells asegs m3 (P + 432) [C8 (wz U)]) by (trx UC2 HP3 PMc RF2).
  assert (LC3 : rw_cells asegs m3 (P + 288) (lhead_cells (P + 312) (P + 288) 0)) by (trx LC2 HP3 PMc RF2).
  assert (FLC3 : rw_cells asegs m3 (P + 344) (fl_cells 0 0)) by (trx FLC2 HP3 PMc RF2).
  assert (FF3 : FFc m3 (P + 288) httpheader_free_entryA fcmp) by (trx FF2 HP3 PMc RF2).
  assert (SHWP3 : shw m3 P 440).
  { eapply (mlocNB_shw_apx FI AI AMS _ _ (q + -32) st m2 m3 P 440); [apply PLq; lia| exact SHWP2| exact HP3| app_ivs_tac| exact RF2| lia]. }
  assert (HP03 : apx FI AI [(P, P + 440)] LBK q m m3).
  { eapply (apx_trans FI AI); [exact HP02|]. eapply (apx_weaken FI AI); [exact HP3| | lia|].
    - unfold sub_fp. cbn. intros y [Hy _]. lia.
    - intros b Hb. rewrite !in_app_iff. LiaTuning.ctauto. }
  clear HP02 HP3 FR2 IC2 MBC2 SBC2 UC2 LC2 FLC2 FF2 HR2 RF2 AE2 MI2 ST2 KSUB2 SHWP2.
  apply nd_app in NDt. destruct NDt as (_ & _ & NDt).

  eapply (aj_evt FI AI J). { eapply (msegC P); lia. } intros ms' ->.
  eapply (aj_bind FI AI J).
  { eapply mbo_destroy_A with (lo := lo) (MBb := SBb) (LBK := UB ++ LBK) (MB := P + 232) (A := As) (len := ls) (cap := cs) (st := st).
    - exact HR3.
    - exact RF3.
    - exact AE3.
    - exact ST3.
    - exact CLO.
    - unfold A0_RT_STACK. clear - LO'. lia.
    - clear - QAL. Z.div_mod_to_equations. lia.
    - clear - QTOP. lia.
    - exact MI3.
    - exact SBC3.
    - apply PLq; lia.
    - clear - PHI. lia.
    - clear - PAL. Z.div_mod_to_equations. lia.
    - eapply shw_sub; [exact SHWP3| lia| lia| lia].
    - exact SBO.
    - exact KSUB3.
    - exact NDt.
    - reflexivity. }
  intros sx4 LB4 ms4 Q. unfold mbo_destroy_post_A in Q.
  destruct Q as (w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m4 & -> & MI4 & ST4 & AE4 & RF4 & HP4 & HR4 & KSUB4 & INCL4 & GONE4 & SBC4 & NS4).
  assert (NSX4 : am_nsec FI AI sx4 = am_nsec FI AI s) by (rewrite NS4, NS3, NS2; reflexivity).
  replace (ret_pc (Z_to_bv 64 0x86a28)) with (Z_to_bv 64 0x86a28) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  assert (FR4 : rw_cells asegs m4 (q + -32) [C8 s2; C8 s1; C8 s0; C8 ra]) by (trx FR3 HP4 PMc RF3).
  assert (IC4 : rw_cells asegs m4 P [C4 (wz 1); C4 (wz meth)]) by (trx IC3 HP4 PMc RF3).
  assert (MBC4 : rw_cells asegs m4 (P + 400) (mbuf_cells 0 0 0)) by (trx MBC3 HP4 PMc RF3).
  assert (UC4 : rw_cells asegs m4 (P + 432) [C8 (wz U)]) by (trx UC3 HP4 PMc RF3).
  assert (LC4 : rw_cells asegs m4 (P + 288) (lhead_cells (P + 312) (P + 288) 0)) by (trx LC3 HP4 PMc RF3).
  assert (FLC4 : rw_cells asegs m4 (P + 344) (fl_cells 0 0)) by (trx FLC3 HP4 PMc RF3).
  assert (FF4 : FFc m4 (P + 288) httpheader_free_entryA fcmp) by (trx FF3 HP4 PMc RF3).
  assert (SHWP4 : shw m4 P 440).
  { eapply (mlocNB_shw_apx FI AI AMS _ _ (q + -32) st m3 m4 P 440); [apply PLq; lia| exact SHWP3| exact HP4| app_ivs_tac| exact RF3| lia]. }
  assert (HP04 : apx FI AI [(P, P + 440)] LBK q m m4).
  { eapply (apx_trans FI AI); [exact HP03|]. eapply (apx_weaken FI AI); [exact HP4| | lia|].
    - unfold sub_fp. cbn. intros y [Hy _]. lia.
    - intros b Hb. rewrite !in_app_iff. LiaTuning.ctauto. }
  clear HP03 HP4 FR3 IC3 MBC3 SBC3 UC3 LC3 FLC3 FF3 HR3 RF3 AE3 MI3 ST3 KSUB3 SHWP3.
  apply nd_app in NDt. destruct NDt as (_ & JU & NDt).

  assert (TAIL : forall sx (LB5 : BL) m5 (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    mem_inv asegs m5 -> stk asegs m5 lo (q + -32) -> asan_env asegs m5 -> RFAKE FI st m5 ->
    RHEAP_A FI AI sx LB5 m5 -> bsub LBK LB5 -> (forall b, In b LB5 -> In b LB) ->
    (forall b, In b (map fst ns ++ hdrs_blocks hs ++ MBb ++ SBb ++ UB) -> ~ In b LB5) ->
    rw_cells asegs m5 (q + -32) [C8 s2; C8 s1; C8 s0; C8 ra] -> rw_cells asegs m5 P [C4 (wz 1); C4 (wz meth)] ->
    rw_cells asegs m5 (P + 400) (mbuf_cells 0 0 0) -> rw_cells asegs m5 (P + 232) (mbuf_cells 0 0 0) -> rw_cells asegs m5 (P + 432) [C8 (wz U)] ->
    rw_cells asegs m5 (P + 288) (lhead_cells (P + 312) (P + 288) 0) -> rw_cells asegs m5 (P + 344) (fl_cells 0 0) -> FFc m5 (P + 288) httpheader_free_entryA fcmp ->
    shw m5 P 440 -> apx FI AI [(P, P + 440)] LBK q m m5 -> am_nsec FI AI sx = am_nsec FI AI s ->
    AJ FI AI J (httpmsg_destroy_post_A ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st (am_nsec FI AI s) LB LBK P meth fcmp U lo m (map fst ns ++ hdrs_blocks hs ++ MBb ++ SBb ++ UB))
      (MS (mkR (wz 0x86a44) (wz (q + -32)) gp (wz A0_TP) t0' t1' t2' (wz P) (wz (Z.shiftr P 3 + 2147450880)) a0' a1' a2' a3' a4' a5' a6' a7'
               (wz 0x7fff8000) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
          F (wz 0x86a44) fc None m5 (seg_rom asegs)) sx LB5).
  { intros sx LB5 m5 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'.
    intros MI5 ST5 AE5 RF5 HR5 KSUB5 INCL5 GONE5 FR5 IC5 MBC5 SBC5 UC5 LC5 FLC5 FF5 SHWP5 HP5 NSX.
    eapply (aj_evt FI AI J). { eapply (msegE lo P meth ra q); try eassumption; lia. }
    intros ms' (m6 & a0x & -> & MU6 & WM6 & MI6 & ST6 & IC6).
    destruct (cw_frames FI AI sx LB5 st m5 m6 _ HR5 RF5 AE5 MU6 WM6) as (HR6 & RF6 & AE6).
    { constructor; [| constructor]. eapply (cw_iv_mlocNB FI AI LB5 q st P 440); [exact PL| exact QC| lia| lia| lia]. }
    apply (aj_ret FI AI J). unfold httpmsg_destroy_post_A.
    do 15 eexists. exists m6. split; [reflexivity|].
    split; [exact MI6|]. split; [exact ST6|]. split; [exact AE6|]. split; [exact RF6|]. split.
    { eapply (apx_trans FI AI); [exact HP5|]. eapply (apx_seg FI AI ASL sx LB5 _ q _ _ m5 m5 m6 HR5 KSUB5 MU6 WM6).
      constructor; [right; right; cbn; lia| constructor]. }
    split; [exact HR6|]. split; [exact KSUB5|]. split; [exact INCL5|]. split; [exact GONE5|]. split; [exact IC6|].
    split; [trm LC5 MU6 WM6|]. split; [trm FLC5 MU6 WM6|]. split; [trm FF5 MU6 WM6|]. split; [trm MBC5 MU6 WM6|]. split; [trm SBC5 MU6 WM6|].
    split; [trm UC5 MU6 WM6|]. split; [eapply (shw_frame _ m5 m6 P 440 SHWP5 MU6); app_ivs_tac| exact NSX]. }

  assert (INCL04 : forall b, In b LB4 -> In b LB) by (intros b Hb; apply INCL2, INCL3, INCL4; exact Hb).
  assert (GONE_U : forall LBx : BL, (forall b, In b LBx -> In b LB4) -> (forall b, In b UB -> ~ In b LBx) ->
             forall b0, In b0 (map fst ns ++ hdrs_blocks hs ++ MBb ++ SBb ++ UB) -> ~ In b0 LBx).
  { intros LBx SUBx GU b0 Hb0 INx. rewrite app_assoc in Hb0. apply in_app_or in Hb0. destruct Hb0 as [H|H].
    - rewrite <- app_assoc in H || idtac. exact (GONE2 b0 H (INCL3 _ (INCL4 _ (SUBx _ INx)))).
    - apply in_app_or in H. destruct H as [H|H]; [exact (GONE3 b0 H (INCL4 _ (SUBx _ INx)))|].
      apply in_app_or in H. destruct H as [H|H]; [exact (GONE4 b0 H (SUBx _ INx))| exact (GU b0 H INx)]. }
  assert (UR : 0 <= U < 2^64).
  { destruct UB as [|b [|b' ?]]; cbn in UBO; [lia| | destruct UBO]. destruct UBO as [<- _].
    destruct (BR b (ASUB0 b ltac:(rewrite !in_app_iff; cbn; LiaTuning.ctauto))) as (? & ? & ? & _). lia. }
  eapply (aj_evt FI AI J). { eapply (msegD P U); try eassumption; lia. } intros ms' [a1x ->].
  apply (bsub_app FI AI) in KSUB4. destruct KSUB4 as [USUB KSUB].
  assert (NVF : ~ valid_frame (am_stack_top FI AI) (q + -32) (bv_unsigned (wz P))).
  { unfold valid_frame. rewrite unsigned_lit by (clear - PLO PHI ACR; lia). clear - PHI CLO LO'. lia. }
  destruct UB as [|b [|b' ?]]; cbn in UBO; [| | destruct UBO].
  -
    subst U. eapply (aj_evt FI AI J).
    { eapply (ac_free_null FI AI J AC) with (lo := lo) (ras := []) (st := st).
      - exact HR4.
      - exact AE4.
      - exact RF4.
      - exact ST4.
      - exact CLO.
      - unfold A0_RT_STACK. clear - LO'. lia.
      - clear - QAL. Z.div_mod_to_equations. lia.
      - clear - QTOP. lia.
      - exact MI4.
      - cbn [fpchain]. exact NVF.
      - rewrite unsigned_lit by (clear; lia). unfold A0_TRACES. repeat first [left; reflexivity | right].
      - reflexivity. }

    intros ms' Q. destruct Q as (x0 & x1 & x2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & x3 & x4 & x5 & x6 & m5 & -> & AFR & WM5 & HR5).
    destruct AFR as (MI5 & ST5 & AE5 & RF5 & AP5).
    replace (ret_pc (Z_to_bv 64 0x86a44)) with (Z_to_bv 64 0x86a44) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    Ltac trp0 H AP PMc RF := eapply (apres_rw_cells FI AI); [exact AP| exact H| first [ apply aclient_range_above; cbn; lia | eapply PMc; [exact RF| unfold lhead_cells, fl_cells, mbuf_cells; cbn; lia| unfold lhead_cells, fl_cells, mbuf_cells; cbn; lia] ]].
    eapply (TAIL sx4 LB4 m5); try eassumption.
    + apply (GONE_U LB4); [auto| intros b0 []].
    + trp0 FR4 AP5 PMc RF4.
    + trp0 IC4 AP5 PMc RF4.
    + trp0 MBC4 AP5 PMc RF4.
    + trp0 SBC4 AP5 PMc RF4.
    + trp0 UC4 AP5 PMc RF4.
    + trp0 LC4 AP5 PMc RF4.
    + trp0 FLC4 AP5 PMc RF4.
    + trp0 FF4 AP5 PMc RF4.
    + eapply (mlocNB_shw_apx FI AI AMS [] _ (q + -32) st m4 m5 P 440); [apply PLq; lia| exact SHWP4| apply apx_of_apres; exact AP5| apply Forall_nil| exact RF4| lia].
    + eapply (apx_trans FI AI); [exact HP04|]. apply apx_of_apres. eapply (apres_weaken FI AI); [exact AP5| lia| exact KSUB].
  - destruct UBO as [EU UNZ].
    assert (BIN : In (blk_id b, U, blk_size b) LB4).
    { replace (blk_id b, U, blk_size b) with b by (destruct b as [[? ?] ?]; cbn in EU |- *; subst; reflexivity). apply USUB. left. reflexivity. }
    eapply (aj_bind FI AI J).
    { eapply (ac_free FI AI J AC) with (lo := lo) (k := blk_id b) (A := U) (n := blk_size b) (ras := []) (st := st).
      - exact HR4.
      - exact BIN.
      - exact AE4.
      - exact RF4.
      - exact ST4.
      - exact CLO.
      - unfold A0_RT_STACK. clear - LO'. lia.
      - clear - QAL. Z.div_mod_to_equations. lia.
      - clear - QTOP. lia.
      - exact MI4.
      - cbn [fpchain]. exact NVF.
      - rewrite unsigned_lit by (clear; lia). unfold A0_TRACES. repeat first [left; reflexivity | right].
      - reflexivity. }
    intros sx5 LB5 ms5 Q. unfold free_post_A in Q.
    destruct Q as (x0 & x1 & x2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & x3 & x4 & x5 & x6 & m5 & -> & AFR & -> & HR5 & NS5).
    destruct AFR as (MI5 & ST5 & AE5 & RF5 & AP5).
    assert (NSX5 : am_nsec FI AI sx5 = am_nsec FI AI s) by (rewrite NS5; exact NSX4).
    replace (ret_pc (Z_to_bv 64 0x86a44)) with (Z_to_bv 64 0x86a44) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (KSUB5 : bsub LBK (lbrm (blk_id b) LB4)).
    { eapply (bsub_remove FI AI); [| exact NDt]. intros y [<-|Hy]; [apply USUB; left; reflexivity| apply KSUB; exact Hy]. }
    Ltac trp H AP PMc RF := eapply (apres_rw_cells FI AI); [exact AP| exact H| first [ apply aclient_range_above; cbn; lia | eapply PMc; [exact RF| unfold lhead_cells, fl_cells, mbuf_cells; cbn; lia| unfold lhead_cells, fl_cells, mbuf_cells; cbn; lia] ]].
    eapply (TAIL sx5 (lbrm (blk_id b) LB4) m5); try eassumption.
    + intros b0 Hb0. apply INCL04. eapply (lb_remove_sub FI AI). exact Hb0.
    + apply (GONE_U (lbrm (blk_id b) LB4)); [intros b0 Hb0; eapply (lb_remove_sub FI AI); exact Hb0|]. intros b0 [<-|[]] IN. exact (lb_remove_neq FI AI _ _ _ IN eq_refl).
    + trp FR4 AP5 PMc RF4.
    + trp IC4 AP5 PMc RF4.
    + trp MBC4 AP5 PMc RF4.
    + trp SBC4 AP5 PMc RF4.
    + trp UC4 AP5 PMc RF4.
    + trp LC4 AP5 PMc RF4.
    + trp FLC4 AP5 PMc RF4.
    + trp FF4 AP5 PMc RF4.
    + eapply (mlocNB_shw_apx FI AI AMS [] _ (q + -32) st m4 m5 P 440); [apply PLq; lia| exact SHWP4| apply apx_of_apres; exact AP5| apply Forall_nil| exact RF4| lia].
    + eapply (apx_trans FI AI); [exact HP04|]. apply apx_of_apres. eapply (apres_weaken FI AI); [exact AP5| lia| exact KSUB5].
Qed.

End W.
