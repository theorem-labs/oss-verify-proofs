(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac RefMemcpyLib.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require Import SumWalkTac Frame.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require Import PFLib.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc Require Export RelocKit.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Musl Require Export RelocRW RelocPF MuslTac.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation SEGS := rl_segs.

Section Consts.
  Context {RL : Reloc}.
  (* [comment removed for export] *)
  Definition A_LEPT_STDERR : Z := 0x13694 + dF_13694.
  Definition A_DEVNULL : Z := 0x1365c + dF_1365c.      (* [comment removed for export] *)
  Definition A_VSNPRINTF : Z := 0x1c740 + dF_1c740.
  Definition A_SNWRITE : Z := 0x1c80c + dF_1c80c.
  Definition A_VFPRINTF : Z := 0x17dbc + dF_17dbc.
  Definition A_PRINTF_CORE : Z := 0x17f6c + dF_17f6c.
  Definition A_POP_ARG : Z := 0x18d9c + dF_18d9c.
  Definition A_FWRITEX : Z := 0x17b9c + dF_17b9c.
  Definition A_TOWRITE : Z := 0x17aec + dF_17aec.
  Definition A_STRNLEN : Z := 0x1cf40 + dF_1cf40.
  Definition A_MEMCPY : Z := 0x1c9b4 + dF_1c9b4.
  Definition A_MEMSET : Z := 0x1cdb8 + dF_1cdb8.
  (* [comment removed for export] *)
  Definition A_HANDLER_CELL : Z := 0x1f428 + dA_1f3f8.   (* [comment removed for export] *)
  Definition A_CANARY_GOT : Z := 0x1e3e0 + dA_1e3b8.     (* [comment removed for export] *)
  Definition A_CANARY : Z := 0x2f848 + dA_2f848.          (* [comment removed for export] *)
  Definition A_PREFIX : Z := 0x102e7 + dS_102e7.      (* [comment removed for export] *)
  Definition A_STATES : Z := 0x115f0 + dA_114a8.          (* [comment removed for export] *)
  Definition A_JT1 : Z := 0x114a8 + dA_114a8.             (* [comment removed for export] *)
  Definition A_JTPOP : Z := 0x115a8 + dA_114a8.           (* [comment removed for export] *)
  Definition IMG_LO : Z := rl_img_lo.
  Definition IMG_HI : Z := rl_rw_lo.                  (* [comment removed for export] *)
  Definition IMG_TOP : Z := rl_img_hi.                (* [comment removed for export] *)
End Consts.

(* [comment removed for export] *)
Section VP1.
  Context {RL : Reloc} {RLP : RelocPF RL}.
Lemma segs_lo_val : segs_lo SEGS = IMG_LO.
Proof. exact rl_segs_lo_val. Qed.
Lemma segs_hi_val : segs_hi SEGS = IMG_TOP.
Proof. exact rl_segs_hi_val. Qed.

Lemma rom_range : forall (x : word) b, seg_rom SEGS x = Some b -> IMG_LO <= bv_unsigned x < IMG_TOP.
Proof. exact rl_rom_range. Qed.
End VP1.

(* [comment removed for export] *)
Ltac pf_bounds :=
  lazymatch goal with
  | _ : rl_img_lo <= 0x102e7 + dS_102e7 |- _ => idtac
  | _ => rl_dwin_bounds;
         let F := fresh "RPF" in
         let a := fresh "RPa" in let b := fresh "RPb" in let c := fresh "RPc" in let d := fresh "RPd" in let e := fresh "RPe" in
         let f1 := fresh "RPf" in let f2 := fresh "RPg" in let f3 := fresh "RPj" in let f4 := fresh "RPk" in
         pose proof rl_pf_facts as F; destruct F as (a & b & c & d & e & f1 & f2 & f3 & f4);
         let h := fresh "RPh" in pose proof rl_img_lo_ge as h;
         let h2 := fresh "RPi" in pose proof rl_img_hi_le as h2
  end.

Section Ctx.
  Context {RL : Reloc}.
(* [comment removed for export] *)
Record ctxH (sp0 : Z) (mem0 : word -> option byte) (cv : Z) : Prop := CTXH {
  Csp   : IMG_TOP + FR <= sp0 <= 0x800000000000;
  Csp16 : sp0 mod 16 = 0;
  Cimg  : forall i, IMG_LO <= i < IMG_HI -> mem0 (Z_to_bv 64 i) = None;
  Csok  : store_ok SEGS mem0 (Z_to_bv 64 (sp0 - FR)) (Z.to_nat FR) = true;
  Chdl  : rdn SEGS mem0 (Z_to_bv 64 A_HANDLER_CELL) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 A_DEVNULL));
  Cgot  : rdn SEGS mem0 (Z_to_bv 64 A_CANARY_GOT) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 A_CANARY));
  Ccan  : rdn SEGS mem0 (Z_to_bv 64 A_CANARY) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 cv));
  Ccv   : 0 <= cv < 2 ^ 64 }.

(* [comment removed for export] *)
Definition FRM (sp0 : Z) (mem0 m : word -> option byte) : Prop :=
  frame_mod mem0 m [(Z_to_bv 64 (sp0 - FR), FR)].
End Ctx.

(* [comment removed for export] *)
Ltac lay := pf_bounds;
  unfold FR, oL, oMSG, oV, oCK, oF, oIB, oP, IMG_LO, IMG_HI, IMG_TOP,
  A_HANDLER_CELL, A_CANARY_GOT, A_CANARY, A_PREFIX, A_STATES, A_JT1, A_JTPOP in *.

Section Derived.
Context {fx : FPState} {RL : Reloc} {RLD : RelocData RL} {RLW : RelocRW RL RLD} {RLP : RelocPF RL}.
  Variables (sp0 : Z) (mem0 : word -> option byte) (cv : Z).
  Hypothesis CTX : ctxH sp0 mem0 cv.

  Lemma FRM_refl : FRM sp0 mem0 mem0.
  Proof. apply frame_mod_refl. Qed.

  Lemma FRM_trans : forall m1 m2, FRM sp0 mem0 m1 -> frame_mod m1 m2 [(Z_to_bv 64 (sp0 - FR), FR)] -> FRM sp0 mem0 m2.
  Proof. intros m1 m2 A B. eapply frame_mod_trans_same; eassumption. Qed.

  (* [comment removed for export] *)
  Lemma FRM_sub : forall m1 m2 rs,
    FRM sp0 mem0 m1 -> frame_mod m1 m2 rs ->
    (forall a, outside a [(Z_to_bv 64 (sp0 - FR), FR)] -> outside a rs) ->
    FRM sp0 mem0 m2.
  Proof.
    intros m1 m2 rs A B W. eapply FRM_trans; [exact A|]. eapply frame_mod_weaken; [exact W | exact B].
  Qed.

  (* [comment removed for export] *)
  Lemma FRM_rdn : forall m (a : Z) (n : nat),
    FRM sp0 mem0 m -> 0 <= a < 2 ^ 64 -> (a + Z.of_nat n <= sp0 - FR \/ sp0 <= a) -> a + Z.of_nat n <= 2 ^ 64 ->
    rdn SEGS m (Z_to_bv 64 a) n = rdn SEGS mem0 (Z_to_bv 64 a) n.
  Proof.
    intros m a n F Ha Hd Hn. destruct CTX.
    apply (frame_mod_rdn SEGS mem0 m _ n (Z_to_bv 64 a) F).
    - intros i Hi. cbn [outside]. split; [|exact I]. unfold in_rng. lay. unorm. lia.
    - lay. unorm. lia.
  Qed.

  Lemma FRM_none : forall m (i : Z),
    FRM sp0 mem0 m -> IMG_LO <= i < IMG_HI -> m (Z_to_bv 64 i) = None.
  Proof.
    intros m i F Hi. destruct CTX. destruct F as [E _].
    rewrite E; [apply Cimg0; exact Hi|].
    cbn [outside]. split; [|exact I]. unfold in_rng. lay.
    rewrite !u_Z2bv by lia. lia.
  Qed.

  Lemma FRM_sok : forall m (a : Z) (n : nat),
    FRM sp0 mem0 m -> sp0 - FR <= a -> a + Z.of_nat n <= sp0 ->
    store_ok SEGS m (Z_to_bv 64 a) n = true.
  Proof.
    intros m a n [_ G] H1 H2. destruct CTX. lay.
    eapply store_ok_mono; [exact G|].
    eapply (store_ok_sub SEGS mem0 (Z_to_bv 64 (sp0 - 3376)) _ (Z.to_nat 3376));
      [u_norm; lia | exact Csok0 | u_norm; lia | u_norm; lia].
  Qed.

  Lemma FRM_hdl : forall m, FRM sp0 mem0 m ->
    rdn SEGS m (Z_to_bv 64 A_HANDLER_CELL) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 A_DEVNULL)).
  Proof. intros m F. destruct CTX. rewrite FRM_rdn; [exact Chdl0|exact F|lay; lia|lay; cbn; lia|lay; cbn; lia]. Qed.
  Lemma FRM_got : forall m, FRM sp0 mem0 m ->
    rdn SEGS m (Z_to_bv 64 A_CANARY_GOT) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 A_CANARY)).
  Proof. intros m F. destruct CTX. rewrite FRM_rdn; [exact Cgot0|exact F|lay; lia|lay; cbn; lia|lay; cbn; lia]. Qed.
  Lemma FRM_can : forall m, FRM sp0 mem0 m ->
    rdn SEGS m (Z_to_bv 64 A_CANARY) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 cv)).
  Proof. intros m F. destruct CTX. rewrite FRM_rdn; [exact Ccan0|exact F|lay; lia|lay; cbn; lia|lay; cbn; lia]. Qed.

  (* [comment removed for export] *)
  Lemma FRM_img : forall m (a : Z) (n : nat),
    FRM sp0 mem0 m -> IMG_LO <= a -> a + Z.of_nat n <= IMG_HI ->
    rdn SEGS m (Z_to_bv 64 a) n = rdn SEGS (fun _ => None) (Z_to_bv 64 a) n.
  Proof.
    intros m a n F H1 H2.
    apply (rdn_img SEGS m a n IMG_LO IMG_HI); try (lay; lia).
    intros i Hi. apply (FRM_none m i F). exact Hi.
  Qed.
End Derived.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Musl Require Import MemcpyBase.

(* [comment removed for export] *)
#[export] Ltac unorm ::=
  rl_unorm;
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
         end.

(* [comment removed for export] *)
Ltac zval := gres; imm_norm; rwH; unfold v_addi, v_add, v_sub; unorm; f_equal; lia.

(* [comment removed for export] *)
Ltac soks CTX := store_ok_peel; eapply (FRM_sok _ _ _ CTX); [ eassumption | lay; lia | lay; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length]; lia ].

(* [comment removed for export] *)
Definition agree_but (l : list reg) (regs r : bvmap 5 word) : Prop :=
  forall x : reg, In x callee_saved -> ~ In x l -> getr r x = getr regs x.

Section VP2. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma agree_but_upd_out : forall l regs r (rd : reg) v,
  agree_but l regs r -> ~ In rd callee_saved -> agree_but l regs (regupd r rd v).
Proof. intros l regs r rd v A Hn x Hx Hl. rewrite getr_other; [apply A; assumption|]. intros ->. exact (Hn Hx). Qed.
Lemma agree_but_upd_in : forall l regs r (rd : reg) v,
  agree_but l regs r -> In rd l -> agree_but l regs (regupd r rd v).
Proof. intros l regs r rd v A Hi x Hx Hl. rewrite getr_other; [apply A; assumption|]. intros ->. exact (Hl Hi). Qed.
Lemma agree_but_keeps : forall l regs r r', agree_but l regs r -> keeps r r' -> agree_but l regs r'.
Proof.
  intros l regs r r' A K x Hx Hl. rewrite (K x); [apply A; assumption|].
  revert Hx. unfold callee_saved, callee_kept. cbn [In]. intuition.
Qed.
End VP2.
Lemma agree_but_keeps_cs : forall l regs r r', agree_but l regs r -> keeps_cs r r' -> agree_but l regs r'.
Proof. intros l regs r r' A K x Hx Hl. rewrite (K x Hx). apply A; assumption. Qed.
Lemma agree_but_refl : forall l regs, agree_but l regs regs.
Proof. intros l regs x _ _. reflexivity. Qed.
Ltac solve_ab :=
  repeat (first [ apply agree_but_upd_out; [| apply not_in_regs_dec; reflexivity]
                | apply agree_but_upd_in; [| apply in_regs_dec; reflexivity] ]);
  first [assumption | apply agree_but_refl
        | eapply agree_but_keeps; [|eassumption]; solve_ab | eapply agree_but_keeps_cs; [|eassumption]; solve_ab].

(* [comment removed for export] *)
Ltac postR := cbv beta; repeat split; gres; rwH; try reflexivity; try bveq; try (f_equal; lia); try solve_ab.

(* [comment removed for export] *)
Ltac frame_tac LEN :=
  repeat (eapply frame_mod_wb; [ | intros fTx fTH fTo; cbn [outside] in fTo; unfold in_rng in *; revert fTH fTo; zlen; rewrite ?LEN; unorm; intros fTH fTo; lia
                               | zlen; rewrite ?LEN; unorm; lia ]).

(* [comment removed for export] *)
Ltac keeps_cs_fin RCS :=
  intros x Hx; cbv [callee_saved In] in Hx;
  repeat (destruct Hx as [<-|Hx];
    [ gres; rwH; first [ reflexivity | assumption | symmetry; assumption
                       | apply RCS; [apply in_regs_dec; reflexivity | apply not_in_regs_dec; reflexivity] ] |]);
  destruct Hx.

(* [comment removed for export] *)
Definition CKst {RL : Reloc} (m : word -> option byte) (sp0 j : Z) : Prop :=
  rdn SEGS m (Z_to_bv 64 (sp0 - 2168)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (sp0 - 2080 + j)))
  /\ rdn SEGS m (Z_to_bv 64 (sp0 - 2160)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (1999 - j)))
  /\ (0 <= j <= 1999)%Z.

(* [comment removed for export] *)
Ltac cond_vm :=
  rwH;
  lazymatch goal with
  | |- ?l = _ => tryif check_closed_term l then (vm_compute; reflexivity) else fail "cond_vm: condition is not closed"
  end.
