(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs W_bio_ctrl.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
Local Ltac al8chk A := zstep; let K := fresh "K" in if_cases K; zify_cond K;
  [exfalso; rewrite ?unsigned_lit in K by lia; try (change 7 with (Z.ones 3) in K; rewrite Z.land_ones in K by lia); clear - K A; Z.div_mod_to_equations; lia | clear K].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Definition obj_range (X n lo : Z) : Prop := (0 < X /\ X + n <= lo /\ (X + n <= 65536 \/ GLOBALS_TOP <= X))%Z.
Lemma obj_range_of_block : forall s L m p X n lo,
  RHEAP s L m -> In (p, X, n) L -> alloc_ceiling <= lo -> obj_range X n lo.
Proof.
  intros s L m p X n lo HEAP IN CEIL. pose proof (LH_block_range _ _ _ _ HEAP IN) as (B0 & B1 & B2 & B3 & B4).
  cbn [blk_addr blk_size fst snd] in *. unfold obj_range, GLOBALS_TOP. lia.
Qed.

Definition BIO_PUSH : Z := 0x10d264.
Definition BIO_POP : Z := 0x10d2dc.
(* [comment removed for export] *)
Definition BIO_PUSH_STACK : Z := 32 + BIO_CTRL_PREFIX_DFL_STACK.

(* [comment removed for export] *)
Definition bio_link_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo bio out rv : Z) (fin : (word -> option byte) -> Prop) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctusegs)
    /\ munch [(bv_unsigned sp - BIO_PUSH_STACK, bv_unsigned sp); (bio, bio + BIO_SIZE); (out, out + BIO_SIZE)]%Z m m'
    /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
    /\ stk ctusegs m' lo (bv_unsigned sp) /\ fin m'.

(* [comment removed for export] *)
Lemma BIO_push_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (bio out : Z) (ctxA onw : Z) (oprev onw2 : Z) (ctxp ind ls : Z) (lo : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> (lo <= bv_unsigned sp - BIO_PUSH_STACK)%Z ->
  rw_cells ctusegs m bio (bio_cells AP_PREFIX_METH 1 ctxA 0 0 onw) -> obj_range bio BIO_SIZE lo -> (bio mod 8 = 0)%Z ->
  rw_cells ctusegs m ctxA (prefix_ctx_cells ctxp ind ls) -> obj_range ctxA PREFIX_CTX_SIZE lo ->
  rw_cells ctusegs m out (bio_null_cells NULL_METHOD oprev onw2) -> obj_range out BIO_SIZE lo -> (out mod 8 = 0)%Z ->
  (bio + BIO_SIZE <= out \/ out + BIO_SIZE <= bio)%Z ->
  (ctxA + PREFIX_CTX_SIZE <= bio \/ bio + BIO_SIZE <= ctxA)%Z -> (ctxA + PREFIX_CTX_SIZE <= out \/ out + BIO_SIZE <= ctxA)%Z ->
  ro_cells ctusegs m (AP_PREFIX_METH + 64) [C8 (Z_to_bv 64 PREFIX_CTRL)] ->
  ro_cells ctusegs m (NULL_METHOD + 64) [C8 (Z_to_bv 64 NULL_CTRL)] ->
  a0 = Z_to_bv 64 bio -> a1 = Z_to_bv 64 out ->
  evt ctusegs (bio_link_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo bio out bio
                 (fun m' => rw_cells ctusegs m' bio (bio_prefix_cells AP_PREFIX_METH ctxA out onw)
                            /\ rw_cells ctusegs m' ctxA (prefix_ctx_cells ctxp ind ls)
                            /\ rw_cells ctusegs m' out (bio_null_cells NULL_METHOD bio onw2)) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BIO_PUSH) fc None m (seg_rom ctusegs)).
Proof.
  intros until lo. intros ST MI GLO LO HB HBLO HBAL HC HCLO HO HOLO HOAL DJBO DJCB DJCO HMT HMT0 -> ->.
  unfold obj_range in HBLO, HCLO, HOLO.
  unfold BIO_PUSH_STACK, BIO_CTRL_PREFIX_DFL_STACK, BIO_CTRL_FRAME, PREFIX_CTRL_DEFAULT_CSTK, BIO_PUSH, GLOBALS_TOP, BIO_SIZE, PREFIX_CTX_SIZE in *.
  pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp); (bio, bio + 128); (out, out + 128)]%Z m) as MU.
  pose proof (wmono_refl ctusegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (SEPB : bio + 128 <= bv_unsigned sp - 160 \/ bv_unsigned sp <= bio) by lia.
  assert (SEPC : ctxA + 16 <= bv_unsigned sp - 160 \/ bv_unsigned sp <= ctxA) by lia.
  assert (SEPO : out + 128 <= bv_unsigned sp - 160 \/ bv_unsigned sp <= out) by lia.
  unfold AP_PREFIX_METH in HMT. cbn [Z.add] in HMT. unfold NULL_METHOD in HMT0. cbn [Z.add] in HMT0.
  assert (SEPM : 2963608 + 64 + 8 <= bv_unsigned sp - 160 \/ bv_unsigned sp <= 2963608 + 64) by lia.
  assert (SEPM0 : 2978032 + 64 + 8 <= bv_unsigned sp - 160 \/ bv_unsigned sp <= 2978032 + 64) by lia.
  unfold bio_null_cells, bio_cells, MallocRep.wz in HB, HO. unfold prefix_ctx_cells, MallocRep.wz in HC.
  carve_frame 32%nat ST.
  do 5 zstep. (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  zstep. zstep. zstep. al8chk HBAL. zstep. (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K; [exfalso; apply K; reflexivity|]. clear K.
  zstep. (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  zstep. al8chk HOAL. zstep. (* [comment removed for export] *)
  do 3 zstep. zstep. (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { eapply BIO_ctrl_prefix_default_spec with (cmd := BIO_CTRL_PUSH) (lo := lo) (bio := bio) (ctxA := ctxA) (out := out);
      [rewrite ESP; exact ST| exact MI| unfold GLOBALS_TOP; lia| rewrite ESP; unfold BIO_CTRL_PREFIX_DFL_STACK, BIO_CTRL_FRAME, PREFIX_CTRL_DEFAULT_CSTK; lia
      | unfold bio_prefix_cells, bio_cells, MallocRep.wz; exact HB| unfold BIO_SIZE; lia| exact HBAL| unfold prefix_ctx_cells, MallocRep.wz; exact HC| unfold PREFIX_CTX_SIZE; lia
      | unfold bio_null_cells, bio_cells, MallocRep.wz; exact HO| unfold BIO_SIZE; lia| exact HOAL| exact HMT| exact HMT0
      | reflexivity| unfold BIO_CTRL_PUSH; reflexivity| left; reflexivity]. }
  clear HB HC HO. intros ms' PO. unfold bio_ctrl_post, BIO_CTRL_FRAME, PREFIX_CTRL_DEFAULT_CSTK in PO. rewrite ?ESP in PO. revert ms' PO.
  post_call ctusegs m1. rewrite ?ESP in *.
  match goal with H : stk ctusegs _ lo _ |- _ => rename H into ST end.
  match goal with H : rw_cells ctusegs _ bio _ |- _ => rename H into HB2 end.
  match goal with H : rw_cells ctusegs _ ctxA _ |- _ => rename H into HC2 end.
  match goal with H : rw_cells ctusegs _ out _ |- _ => rename H into HO2 end.
  zstep. zstep. (* [comment removed for export] *)
  do 4 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  finish.
Qed.

(* [comment removed for export] *)
Lemma BIO_pop_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (bio out : Z) (ctxA onw : Z) (oprev onw2 : Z) (ctxp ind ls : Z) (lo : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> (lo <= bv_unsigned sp - BIO_PUSH_STACK)%Z ->
  rw_cells ctusegs m bio (bio_prefix_cells AP_PREFIX_METH ctxA out onw) -> obj_range bio BIO_SIZE lo -> (bio mod 8 = 0)%Z ->
  rw_cells ctusegs m ctxA (prefix_ctx_cells ctxp ind ls) -> obj_range ctxA PREFIX_CTX_SIZE lo ->
  rw_cells ctusegs m out (bio_null_cells NULL_METHOD oprev onw2) -> obj_range out BIO_SIZE lo -> (out mod 8 = 0)%Z ->
  (bio + BIO_SIZE <= out \/ out + BIO_SIZE <= bio)%Z ->
  (ctxA + PREFIX_CTX_SIZE <= bio \/ bio + BIO_SIZE <= ctxA)%Z -> (ctxA + PREFIX_CTX_SIZE <= out \/ out + BIO_SIZE <= ctxA)%Z ->
  ro_cells ctusegs m (AP_PREFIX_METH + 64) [C8 (Z_to_bv 64 PREFIX_CTRL)] ->
  ro_cells ctusegs m (NULL_METHOD + 64) [C8 (Z_to_bv 64 NULL_CTRL)] ->
  a0 = Z_to_bv 64 bio ->
  evt ctusegs (bio_link_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo bio out out
                 (fun m' => rw_cells ctusegs m' bio (bio_cells AP_PREFIX_METH 1 ctxA 0 0 onw)
                            /\ rw_cells ctusegs m' ctxA (prefix_ctx_cells ctxp ind ls)
                            /\ rw_cells ctusegs m' out (bio_null_cells NULL_METHOD 0 onw2)) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BIO_POP) fc None m (seg_rom ctusegs)).
Proof.
  intros until lo. intros ST MI GLO LO HB HBLO HBAL HC HCLO HO HOLO HOAL DJBO DJCB DJCO HMT HMT0 ->.
  unfold obj_range in HBLO, HCLO, HOLO.
  unfold BIO_PUSH_STACK, BIO_CTRL_PREFIX_DFL_STACK, BIO_CTRL_FRAME, PREFIX_CTRL_DEFAULT_CSTK, BIO_POP, GLOBALS_TOP, BIO_SIZE, PREFIX_CTX_SIZE in *.
  pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp); (bio, bio + 128); (out, out + 128)]%Z m) as MU.
  pose proof (wmono_refl ctusegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (SEPB : bio + 128 <= bv_unsigned sp - 160 \/ bv_unsigned sp <= bio) by lia.
  assert (SEPC : ctxA + 16 <= bv_unsigned sp - 160 \/ bv_unsigned sp <= ctxA) by lia.
  assert (SEPO : out + 128 <= bv_unsigned sp - 160 \/ bv_unsigned sp <= out) by lia.
  unfold AP_PREFIX_METH in HMT. cbn [Z.add] in HMT. unfold NULL_METHOD in HMT0. cbn [Z.add] in HMT0.
  assert (SEPM : 2963608 + 64 + 8 <= bv_unsigned sp - 160 \/ bv_unsigned sp <= 2963608 + 64) by lia.
  assert (SEPM0 : 2978032 + 64 + 8 <= bv_unsigned sp - 160 \/ bv_unsigned sp <= 2978032 + 64) by lia.
  unfold bio_prefix_cells, bio_null_cells, bio_cells, MallocRep.wz in HB, HO. unfold prefix_ctx_cells, MallocRep.wz in HC.
  carve_frame 32%nat ST.
  do 6 zstep. (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  zstep. zstep. al8chk HBAL. zstep. (* [comment removed for export] *)
  do 4 zstep. zstep. (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { eapply BIO_ctrl_prefix_default_spec with (cmd := BIO_CTRL_POP) (lo := lo) (bio := bio) (ctxA := ctxA) (out := out);
      [rewrite ESP; exact ST| exact MI| unfold GLOBALS_TOP; lia| rewrite ESP; unfold BIO_CTRL_PREFIX_DFL_STACK, BIO_CTRL_FRAME, PREFIX_CTRL_DEFAULT_CSTK; lia
      | unfold bio_prefix_cells, bio_cells, MallocRep.wz; exact HB| unfold BIO_SIZE; lia| exact HBAL| unfold prefix_ctx_cells, MallocRep.wz; exact HC| unfold PREFIX_CTX_SIZE; lia
      | unfold bio_null_cells, bio_cells, MallocRep.wz; exact HO| unfold BIO_SIZE; lia| exact HOAL| exact HMT| exact HMT0
      | reflexivity| unfold BIO_CTRL_POP; reflexivity| right; reflexivity]. }
  clear HB HC HO. intros ms' PO. unfold bio_ctrl_post, BIO_CTRL_FRAME, PREFIX_CTRL_DEFAULT_CSTK in PO. rewrite ?ESP in PO. revert ms' PO.
  post_call ctusegs m1. rewrite ?ESP in *.
  match goal with H : stk ctusegs _ lo _ |- _ => rename H into ST end.
  match goal with H : rw_cells ctusegs _ bio _ |- _ => rename H into HB end.
  match goal with H : rw_cells ctusegs _ ctxA _ |- _ => rename H into HC end.
  match goal with H : rw_cells ctusegs _ out _ |- _ => rename H into HO end.
  unfold bio_prefix_cells, bio_null_cells, bio_cells, MallocRep.wz in HB, HO. unfold prefix_ctx_cells, MallocRep.wz in HC.
  zstep. (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K; [|exfalso; apply K; reflexivity]. clear K.
  zstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  zstep. al8chk HOAL. zstep. (* [comment removed for export] *)
  zstep. zstep. (* [comment removed for export] *)
  zstep. zstep. (* [comment removed for export] *)
  do 5 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  finish.
Qed.
End WithCeiling0.
