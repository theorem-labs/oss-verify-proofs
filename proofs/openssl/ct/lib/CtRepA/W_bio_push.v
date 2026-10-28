(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA AsStruct RtCallA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApUTacB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac ApRepDefs W_bio_ctrl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  end.

Definition BIO_PUSH : Z := 0x2397d8.
Definition BIO_POP : Z := 0x239888.
Definition BIO_POP_MEMSET_RET : Z := 0x239964.
(* [comment removed for export] *)
Definition BIO_PUSH_STACK : Z := 32 + BIO_CTRL_PREFIX_DFL_STACK.
(* [comment removed for export] *)
Definition BIO_POP_STACK : Z := 64 + RT_STACK.

(* [comment removed for export] *)
Definition apres_ex (LB OW : list block) (SP : Z) (EX : list (Z * Z)) (m m' : mem) : Prop :=
  agree_on (fun a => aclient_addr (OW ++ LB) SP a /\ outside EX a) m m'.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Definition bio_link_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Σ : rts RT) (OW LB : list block) (lo bio out rv : Z) (fin : (word -> option byte) -> Prop) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctasegs)
    /\ munch [(bv_unsigned sp - BIO_PUSH_STACK, bv_unsigned sp); (bio, bio + BIO_SIZE); (out, out + BIO_SIZE)]%Z m m'
    /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
    /\ stk ctasegs m' lo (bv_unsigned sp) /\ AHEAP Σ OW LB m' /\ fin m'.

(* [comment removed for export] *)
Lemma BIO_push_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Σ : rts RT) (OW LB : list block) (pb pc po : bptr)
    (bio out : Z) (ctxA onw : Z) (oprev onw2 : Z) (ctxp ind ls : Z) (lo : Z),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> ACEIL <= lo -> (lo <= bv_unsigned sp - BIO_PUSH_STACK)%Z ->
  In (pb, bio, BIO_SIZE) OW -> rw_cells ctasegs m bio (bio_cells AP_PREFIX_METH 1 ctxA 0 0 onw) ->
  In (pc, ctxA, PREFIX_CTX_SIZE) OW -> rw_cells ctasegs m ctxA (prefix_ctx_cells ctxp ind ls) ->
  In (po, out, BIO_SIZE) OW -> rw_cells ctasegs m out (bio_null_cells NULL_METHOD oprev onw2) ->
  (bio + BIO_SIZE <= out \/ out + BIO_SIZE <= bio)%Z ->
  (ctxA + PREFIX_CTX_SIZE <= bio \/ bio + BIO_SIZE <= ctxA)%Z -> (ctxA + PREFIX_CTX_SIZE <= out \/ out + BIO_SIZE <= ctxA)%Z ->
  a0 = Z_to_bv 64 bio -> a1 = Z_to_bv 64 out ->
  evt ctasegs (bio_link_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Σ OW LB lo bio out bio
                 (fun m' => rw_cells ctasegs m' bio (bio_prefix_cells AP_PREFIX_METH ctxA out onw)
                            /\ rw_cells ctasegs m' ctxA (prefix_ctx_cells ctxp ind ls)
                            /\ rw_cells ctasegs m' out (bio_null_cells NULL_METHOD bio onw2)) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BIO_PUSH) fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros HEAP ST MI CEIL LO HBIN HB HCIN HC HOIN HO DJBO DJCB DJCO -> ->.
  unfold BIO_PUSH_STACK, BIO_CTRL_PREFIX_DFL_STACK, BIO_CTRL_FRAME, PREFIX_CTRL_DEFAULT_CSTK, BIO_PUSH, BIO_SIZE, PREFIX_CTX_SIZE in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (stk_below ctasegs m lo _ MI ST ltac:(lia)) as SPT. unfold UTOP in SPT.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
  assert (HBIN' : In (pb, bio, 128) (OW ++ LB)) by (apply in_or_app; left; exact HBIN).
  assert (HCIN' : In (pc, ctxA, 16) (OW ++ LB)) by (apply in_or_app; left; exact HCIN).
  assert (HOIN' : In (po, out, 128) (OW ++ LB)) by (apply in_or_app; left; exact HOIN).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HBIN') as (BB0 & _ & _ & BBC & BBI). cbn [blk_addr blk_size fst snd] in BB0, BBC, BBI.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HCIN') as (BC0 & _ & _ & BCC & BCI). cbn [blk_addr blk_size fst snd] in BC0, BCC, BCI.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HOIN') as (BO0 & _ & _ & BOC & BOI). cbn [blk_addr blk_size fst snd] in BO0, BOC, BOI.
  pose proof (proj1 (AH_okA _ _ _ _ _ _ _ HEAP HBIN)) as ALB. pose proof (proj1 (AH_okA _ _ _ _ _ _ _ HEAP HOIN)) as ALO.
  ablock HEAP HBIN' ACCB OFFB. ablock HEAP HOIN' ACCO OFFO.
  destruct (AH_shb _ _ _ _ HEAP) as [SHB1 SHB2].
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp); (bio, bio + 128); (out, out + 128)]%Z m) as MU.
  pose proof (wmono_refl ctasegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 240, bv_unsigned sp); (bio, bio + 128); (out, out + 128)]%Z) by (cbn [offshW]; alia).
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (SEPB : bio + 128 <= bv_unsigned sp - 240 \/ bv_unsigned sp <= bio) by lia.
  assert (SEPC : ctxA + 16 <= bv_unsigned sp - 240 \/ bv_unsigned sp <= ctxA) by lia.
  assert (SEPO : out + 128 <= bv_unsigned sp - 240 \/ bv_unsigned sp <= out) by lia.
  unfold bio_null_cells, bio_cells, MallocRep.wz in HB, HO. unfold prefix_ctx_cells, MallocRep.wz in HC.
  carve_frame 32%nat ST.
  do 5 zstep. (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.
  zstep. if_cases K; zify_cond K; [exfalso; apply K; reflexivity|]. clear K.
  (* [comment removed for export] *)
  zstep.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  (* [comment removed for export] *)
  zstep.
  do 3 zstep. zstep. (* [comment removed for export] *)
  name_mem m1.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs m m1 |- _ => rename H into WM1 end.
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply AH_frame; [exact HEAP| exact MU1| exact WM1|].
    constructor; [left; cbn; alia|]. constructor; [right; right; exists (pb, bio, 128); split; [exact HBIN'| cbn; lia]|].
    constructor; [right; right; exists (po, out, 128); split; [exact HOIN'| cbn; lia]| constructor]. }
  eapply evt_cut.
  { eapply BIO_ctrl_prefix_default_spec with (cmd := BIO_CTRL_PUSH) (lo := lo) (bio := bio) (ctxA := ctxA) (out := out) (pb := pb) (pc := pc) (po := po);
      [exact HEAP1| rewrite ESP; exact ST| exact MI| exact CEIL| rewrite ESP; unfold BIO_CTRL_PREFIX_DFL_STACK, BIO_CTRL_FRAME, PREFIX_CTRL_DEFAULT_CSTK; lia
      | exact HBIN| unfold bio_prefix_cells, bio_cells, MallocRep.wz; exact HB| exact HCIN| unfold prefix_ctx_cells, MallocRep.wz; exact HC
      | exact HOIN| unfold bio_null_cells, bio_cells, MallocRep.wz; exact HO
      | reflexivity| unfold BIO_CTRL_PUSH; reflexivity| left; reflexivity]. }
  clear HB HC HO HEAP1. intros ms' PO. unfold bio_ctrl_post, BIO_CTRL_FRAME, PREFIX_CTRL_DEFAULT_CSTK in PO. rewrite ?ESP in PO. revert ms' PO.
  post_call ctasegs m1. rewrite ?ESP in *.
  match goal with H : stk ctasegs _ lo _ |- _ => rename H into ST end.
  match goal with H : rw_cells ctasegs _ bio _ |- _ => rename H into HB2 end.
  match goal with H : rw_cells ctasegs _ ctxA _ |- _ => rename H into HC2 end.
  match goal with H : rw_cells ctasegs _ out _ |- _ => rename H into HO2 end.
  match goal with H : AHEAP _ _ _ _ |- _ => rename H into HEAP2 end.
  zstep. zstep. (* [comment removed for export] *)
  do 4 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition bio_pop_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (lo bio out rv : Z) (fin : (word -> option byte) -> Prop) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp)
    /\ apres_ex LB OW (bv_unsigned sp) [(bio, bio + BIO_SIZE); (out, out + BIO_SIZE)]%Z m m'
    /\ wmono ctasegs m m' /\ AHEAP Σ OW LB m' /\ fin m'.

(* [comment removed for export] *)
Lemma zero16_link_cells : forall m A,
  bytes_at ctasegs m A (repeat (Z_to_bv 8 0) (Z.to_nat 16)) -> wr_at ctasegs m A 16 -> rw_cells ctasegs m A [C8 (wz 0); C8 (wz 0)].
Proof.
  intros m A HB HW. eapply (rw_cells_recast m A [CB 16%nat (repeat (Z_to_bv 8 0) 16%nat)]).
  - split; [split; [cbn; split; [reflexivity| exact I]| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact HB]| cbn; exact HW].
  - cbn; auto.
  - unfold MallocRep.wz. bytes_lit_eq.
  - reflexivity.
Qed.

(* [comment removed for export] *)
Lemma BIO_pop_cpsA : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Σ : rts RT) (OW LB : list block) (pb pc po : bptr)
    (bio out : Z) (ctxA onw : Z) (oprev onw2 : Z) (ctxp ind ls : Z) (lo : Z),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> ACEIL <= lo -> (lo <= bv_unsigned sp - BIO_POP_STACK)%Z ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> tp = wz TP_A ->
  In (pb, bio, BIO_SIZE) OW -> rw_cells ctasegs m bio (bio_prefix_cells AP_PREFIX_METH ctxA out onw) ->
  In (pc, ctxA, PREFIX_CTX_SIZE) OW -> rw_cells ctasegs m ctxA (prefix_ctx_cells ctxp ind ls) ->
  In (po, out, BIO_SIZE) OW -> rw_cells ctasegs m out (bio_null_cells NULL_METHOD oprev onw2) ->
  (bio + BIO_SIZE <= out \/ out + BIO_SIZE <= bio)%Z ->
  (ctxA + PREFIX_CTX_SIZE <= bio \/ bio + BIO_SIZE <= ctxA)%Z -> (ctxA + PREFIX_CTX_SIZE <= out \/ out + BIO_SIZE <= ctxA)%Z ->
  a0 = Z_to_bv 64 bio ->
  cps ctasegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (Z_to_bv 64 BIO_POP) fc None m (seg_rom ctasegs))))
    (ASTA RT Σ PMc (bio_pop_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo bio out out
                      (fun m' => rw_cells ctasegs m' bio (bio_cells AP_PREFIX_METH 1 ctxA 0 0 onw)
                                 /\ rw_cells ctasegs m' ctxA (prefix_ctx_cells ctxp ind ls)
                                 /\ rw_cells ctasegs m' out (bio_null_cells NULL_METHOD 0 onw2)) m)).
Proof.
  intros until lo. intros HEAP ST MI CEIL LO SPT SP16 -> HBIN HB HCIN HC HOIN HO DJBO DJCB DJCO ->.
  unfold BIO_POP_STACK, RT_STACK, BIO_POP, BIO_SIZE, PREFIX_CTX_SIZE, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3. unfold USTACK_TOP in SPT.
  assert (HBIN' : In (pb, bio, 128) (OW ++ LB)) by (apply in_or_app; left; exact HBIN).
  assert (HCIN' : In (pc, ctxA, 16) (OW ++ LB)) by (apply in_or_app; left; exact HCIN).
  assert (HOIN' : In (po, out, 128) (OW ++ LB)) by (apply in_or_app; left; exact HOIN).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HBIN') as (BB0 & _ & _ & BBC & BBI). cbn [blk_addr blk_size fst snd] in BB0, BBC, BBI.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HCIN') as (BC0 & _ & _ & BCC & BCI). cbn [blk_addr blk_size fst snd] in BC0, BCC, BCI.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HOIN') as (BO0 & _ & _ & BOC & BOI). cbn [blk_addr blk_size fst snd] in BO0, BOC, BOI.
  pose proof (proj1 (AH_okA _ _ _ _ _ _ _ HEAP HBIN)) as ALB. pose proof (proj1 (AH_okA _ _ _ _ _ _ _ HEAP HOIN)) as ALO.
  ablock HEAP HBIN' ACCB OFFB. ablock HEAP HOIN' ACCO OFFO.
  destruct (AH_shb _ _ _ _ HEAP) as [SHB1 SHB2].
  pose proof (munch_refl [(bv_unsigned sp - 272, bv_unsigned sp); (bio, bio + 128); (out, out + 128)]%Z m) as MU.
  pose proof (wmono_refl ctasegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 272, bv_unsigned sp); (bio, bio + 128); (out, out + 128)]%Z) by (cbn [offshW]; alia).
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (SEPB : bio + 128 <= bv_unsigned sp - 272 \/ bv_unsigned sp <= bio) by lia.
  assert (SEPC : ctxA + 16 <= bv_unsigned sp - 272 \/ bv_unsigned sp <= ctxA) by lia.
  assert (SEPO : out + 128 <= bv_unsigned sp - 272 \/ bv_unsigned sp <= out) by lia.
  unfold bio_prefix_cells, bio_null_cells, bio_cells, MallocRep.wz in HB, HO. unfold prefix_ctx_cells, MallocRep.wz in HC.
  apply cps_from_evt'.
  carve_frame 64%nat ST.
  do 9 zstep. (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  (* [comment removed for export] *)
  zstep. zstep. do 4 zstep. zstep.
  name_mem m1.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
  match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs m m1 |- _ => rename H into WM1 end.
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply AH_frame; [exact HEAP| exact MU1| exact WM1|].
    constructor; [left; cbn; alia|]. constructor; [right; right; exists (pb, bio, 128); split; [exact HBIN'| cbn; lia]|].
    constructor; [right; right; exists (po, out, 128); split; [exact HOIN'| cbn; lia]| constructor]. }
  eapply evt_cut.
  { eapply BIO_ctrl_prefix_default_spec with (cmd := BIO_CTRL_POP) (lo := lo) (bio := bio) (ctxA := ctxA) (out := out) (pb := pb) (pc := pc) (po := po);
      [exact HEAP1| rewrite ESP; exact ST| exact MI| exact CEIL| rewrite ESP; unfold BIO_CTRL_PREFIX_DFL_STACK, BIO_CTRL_FRAME, PREFIX_CTRL_DEFAULT_CSTK; lia
      | exact HBIN| unfold bio_prefix_cells, bio_cells, MallocRep.wz; exact HB| exact HCIN| unfold prefix_ctx_cells, MallocRep.wz; exact HC
      | exact HOIN| unfold bio_null_cells, bio_cells, MallocRep.wz; exact HO
      | reflexivity| unfold BIO_CTRL_POP; reflexivity| right; reflexivity]. }
  clear HB HC HO HEAP1. intros ms' PO. unfold bio_ctrl_post, BIO_CTRL_FRAME, PREFIX_CTRL_DEFAULT_CSTK in PO. rewrite ?ESP in PO. revert ms' PO.
  post_call ctasegs m1. rewrite ?ESP in *.
  match goal with H : stk ctasegs _ lo _ |- _ => rename H into ST end.
  match goal with H : rw_cells ctasegs _ bio _ |- _ => rename H into HB end.
  match goal with H : rw_cells ctasegs _ ctxA _ |- _ => rename H into HC end.
  match goal with H : rw_cells ctasegs _ out _ |- _ => rename H into HO end.
  match goal with H : AHEAP _ _ _ _ |- _ => rename H into HEAP2 end.
  unfold bio_prefix_cells, bio_null_cells, bio_cells, MallocRep.wz in HB, HO. unfold prefix_ctx_cells, MallocRep.wz in HC.
  (* [comment removed for export] *)
  zstep. zstep. if_cases K; zify_cond K; [|exfalso; apply K; reflexivity]. clear K.
  (* [comment removed for export] *)
  zstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  (* [comment removed for export] *)
  zstep.
  (* [comment removed for export] *)
  do 3 zstep. zstep.
  name_mem m2.
  match goal with H : munch _ m m2 |- _ => rename H into MU2 end. match goal with H : wmono ctasegs m m2 |- _ => rename H into WM2 end.
  assert (HEAP3 : AHEAP Σ OW LB m2).
  { eapply AH_frame; [exact HEAP| exact MU2| exact WM2|].
    constructor; [left; cbn; alia|]. constructor; [right; right; exists (pb, bio, 128); split; [exact HBIN'| cbn; lia]|].
    constructor; [right; right; exists (po, out, 128); split; [exact HOIN'| cbn; lia]| constructor]. }
  apply evt_done. eapply cps_step_same.
  { eapply (asan_memset_cpsA) with (d := bio + 72) (n := 16) (c := Z_to_bv 8 0) (bd := (pb, bio, 128)) (lo := lo) (OW := OW) (LB := LB); try reflexivity.
    - exact HEAP3.
    - rewrite ESP. exact ST.
    - exact CEIL.
    - rewrite ESP. unfold RT_STACK. lia.
    - rewrite ESP. unfold USTACK_TOP. lia.
    - rewrite ESP. uchk_open. clear - SP16 SPR. Z.div_mod_to_equations. lia.
    - match goal with H : mem_inv ctasegs m2 |- _ => exact H end.
    - exact HBIN'.
    - cbn [blk_addr blk_size fst snd]. lia.
    - cbn [blk_addr blk_size fst snd]. lia.
    - lia. }
  intros msM PO. unfold icall_post in PO. rewrite ?ESP in PO.
  destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F3 & fc3 & mM & -> & MIM & STM & HEAPM & WMM & AGM & BZ & WRM).
  unfold BIO_POP_MEMSET_RET. rewrite (ret_pc_even 2333028) by (clear; lia). unfold MallocRep.wz.
  (* [comment removed for export] *)
  apply (rw_cells_agree _ _ _ _ _ AGM) in FR; [| intros xa Hxa; cbn in Hxa; split; [left; unfold USTACK_TOP; lia| lia]].
  apply (rw_cells_agree _ _ _ _ _ AGM) in HC; [| intros xa Hxa; cbn in Hxa; split; [right; right; exists (pc, ctxA, 16); split; [exact HCIN'| cbn; lia]| lia]].
  apply (rw_cells_agree _ _ _ _ _ AGM) in HO; [| intros xa Hxa; cbn in Hxa; split; [right; right; exists (po, out, 128); split; [exact HOIN'| cbn; lia]| lia]].
  clear ST. rename STM into ST.
  lazymatch type of HB with rw_cells _ _ _ [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10; ?c11; ?c12; ?c13; ?c14; ?c15; ?c16; ?c17; ?c18; ?c19] =>
    change (rw_cells ctasegs m2 bio ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11] ++ [c12; c13] ++ [c14; c15; c16; c17; c18; c19])) in HB end.
  destruct (proj1 (rw_cells_app m2 bio _ _) HB) as [HBlo HBr]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in HBr.
  destruct (proj1 (rw_cells_app m2 _ _ _) HBr) as [_ HBhi]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in HBhi.
  replace (bio + 72 + 16) with (bio + 88) in HBhi by lia.
  clear HBr HB.
  apply (rw_cells_agree _ _ _ _ _ AGM) in HBlo; [| intros xa Hxa; cbn in Hxa; split; [right; right; exists (pb, bio, 128); split; [exact HBIN'| cbn; lia]| lia]].
  apply (rw_cells_agree _ _ _ _ _ AGM) in HBhi; [| intros xa Hxa; cbn in Hxa; split; [right; right; exists (pb, bio, 128); split; [exact HBIN'| cbn; lia]| lia]].
  pose proof (zero16_link_cells mM (bio + 72) BZ WRM) as HBmid.
  assert (HB : rw_cells ctasegs mM bio (bio_cells AP_PREFIX_METH 1 ctxA 0 0 onw)).
  { unfold bio_cells, MallocRep.wz. apply (proj2 (rw_cells_app mM bio [_; _; _; _; _; _; _; _; _; _; _; _] _)). split; [exact HBlo|].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add].
    apply (proj2 (rw_cells_app mM (bio + 72) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] _)). split; [exact HBmid|].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]. replace (bio + 72 + 16) with (bio + 88) by lia. exact HBhi. }
  clear HBlo HBhi HBmid.
  destruct (AH_shb _ _ _ _ HEAPM) as [SHB1' SHB2'].
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep. zstep. do 8 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  apply evt_done. apply cps_post. intros c Hc. eapply ASTA_conseq; [exact Hc|]. intros ms0 <-.
  unfold bio_pop_post, MallocRep.wz. do 16 eexists. exists mM. split; [reflexivity|].
  split; [exact MIM|]. split; [exact ST|].
  split.
  { unfold apres_ex. eapply agree_on_trans.
    - eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU2)|]. intros a [Ha Ho]. cbn [outside] in Ho |- *. destruct Ho as (Ho1 & Ho2 & _).
      unfold BIO_SIZE in Ho1, Ho2.
      split; [| split; [exact Ho1| split; [exact Ho2| exact I]]].
      destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [lia| |].
      + destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; alia.
      + pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & B3' & _). lia.
    - eapply agree_on_mono; [exact AGM|]. intros a [Ha Ho]. cbn [outside] in Ho. unfold BIO_SIZE in Ho.
      split; [destruct Ha as [Ha|[Ha|Ha]]; [left; lia| right; left; exact Ha| right; right; exact Ha]| lia]. }
  split; [eapply wmono_trans; [exact WM2| exact WMM]|].
  split; [exact HEAPM|].
  split; [exact HB|]. split; [unfold prefix_ctx_cells, MallocRep.wz; exact HC| unfold bio_null_cells, bio_cells, MallocRep.wz; exact HO].
Qed.
End WithRT.
