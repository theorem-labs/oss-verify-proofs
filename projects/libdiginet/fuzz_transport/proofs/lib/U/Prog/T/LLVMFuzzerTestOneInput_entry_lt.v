(* The tactics of the config read of LLVMFuzzerTestOneInput (ubsan) 0x13854 .. 0x138d4 (the main path and the
   ladder 0x14628-0x1481c), and the statement of one cursor length's walk (ent_lad_stmt). The cases are proved in
   U/Prog/T/LLVMFuzzerTestOneInput_entry_l{a,b,c}.v, joined in U/Prog/T/LLVMFuzzerTestOneInput_entry_lad.v. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_entry_m LLVMFuzzerTestOneInput_entry_d.
Import ListNotations.
Open Scope Z_scope.

(* the walk 0x13854 .. 0x138d4 for the cursor lengths n with P n *)
Definition ent_lad_stmt (P : Z -> Prop) : Prop :=
  forall data D regs0 m0 Sp lo B1 o n flags F fc ms (Q : machine_state -> Prop),
    P n -> ent_num Sp lo -> 0 <= flags < 256 -> 0 <= o -> 0 <= n -> o + n = Z.of_nat (length D) ->
    ent_dat data D m0 lo -> (D = [] -> n = 0) ->
    ent_s854 data regs0 m0 Sp lo B1 o n flags F fc ms ->
    (forall ms', ent_s8d4 data D regs0 m0 Sp lo B1 o n flags F fc ms' -> evt rsegs Q ms') ->
    evt rsegs Q ms.

Lemma lad_sub1 : forall (D : list byte) k, (k < length D)%nat -> firstn 1 (skipn k D) = [nth k D (b8 0)].
Proof.
  induction D as [|d D IH]; intros k Hk; cbn in Hk; [lia|].
  destruct k as [|k]; cbn; [reflexivity|]. apply IH. lia.
Qed.

(* the byte o + k of the input, as the machine loads it: from bytes_at of the current memory *)
Ltac lad_ld HDm o k :=
  let mm := ent_mem_of in
  let H := fresh "HR" in
  lazymatch type of HDm with bytes_at rsegs _ ?dat ?DD =>
    pose proof (bytes_at_read rsegs mm dat DD (o + k) 1 HDm ltac:(lia) ltac:(lia)) as H;
    rewrite lad_sub1 in H by lia
  end.

(* before the step at each lbu of the cursor: the byte's read *)
Ltac lad_pre HDm o :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    lazymatch pc with
    | 0x13868 => lad_ld HDm o 0
    | 0x14634 => lad_ld HDm o 1
    | 0x14660 => lad_ld HDm o 2
    | 0x1467c => lad_ld HDm o 3
    | 0x146a8 => lad_ld HDm o 4
    | 0x146cc => lad_ld HDm o 5
    | 0x146e8 => lad_ld HDm o 6
    | 0x14714 => lad_ld HDm o 7
    | 0x1472c => lad_ld HDm o 8
    | 0x14758 => lad_ld HDm o 9
    | 0x14770 => lad_ld HDm o 10
    | 0x14798 => lad_ld HDm o 11
    | 0x147d0 => lad_ld HDm o 12
    | 0x14810 => lad_ld HDm o 13
    | _ => idtac
    end
  end.

(* a branch condition on values in range: unfold the comparison and decide it by lia *)
Ltac lad_cond :=
  unfold bv_eqb, bv_ltu, bv_leu; rewrite ?unsigned_lit by lia; fold_lit_ux; solve_cond_rec.
Ltac lad_dec :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      first [ replace c with true by (symmetry; lad_cond); cbv iota
            | replace c with false by (symmetry; lad_cond); cbv iota ]
  end.

(* step to the join 0x138d4, deciding every branch by the facts on n *)
Ltac lad_run HDm o :=
  repeat (lazymatch goal with
          | |- evt _ _ (MS _ _ (Z_to_bv 64 0x138d4) _ _ _ _) => fail
          | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => lad_dec
          | |- _ => lad_pre HDm o; zstep
          end).

(* cbyte D o n k by the facts on n: the byte or 0 *)
Ltac lad_cb :=
  try unfold cbyte;
  repeat match goal with
         | |- context [?k <? ?n] =>
             first [ rewrite (proj2 (Z.ltb_lt k n)) by lia | rewrite (proj2 (Z.ltb_ge k n)) by lia ]
         end;
  cbv iota; try unfold at8, bz.

(* a register value at the join *)
Ltac lad_eqv := lad_cb; unfold cur; cbn [fi_off fi_n]; lia.

Ltac lad_bsd :=
  first [ apply e_brange | lia | match goal with |- context [bv_unsigned ?b] => pose proof (e_brange b); lia end ].

(* the input bytes as numbers with their range *)
Ltac lad_gen :=
  repeat match goal with |- context [bv_unsigned (nth ?i ?DD ?d)] =>
    let b := fresh "b" in let Hb := fresh "Hb" in
    pose proof (e_brange (nth i DD d)) as Hb; set (b := bv_unsigned (nth i DD d)) in *; clearbody b
  end.

(* a stored value against the model's, modulo 2^32 *)
Ltac lad_v :=
  lad_cb;
  rewrite ?Zmod_0_l, ?Z.shiftl_0_l, ?Z.lor_0_l, ?Z.lor_0_r;
  rewrite ?e_mc by lad_bsd; rewrite ?e_lor1 by lad_bsd; rewrite ?e_lor2 by lad_bsd; rewrite ?e_lor16 by lad_bsd;
  rewrite ?e_land7 by lad_bsd;
  rewrite ?Z.mod_mod by lia;
  lad_gen;
  first [ e_refl | f_equal; lia | Z.div_mod_to_equations; lia ].

(* the join: the state of ent_s8d4 *)
Ltac lad_fin K :=
  apply K; eapply ent_s8d4_intro;
  [ reflexivity | lad_eqv | lad_eqv | lad_eqv | lad_eqv
  | lazymatch goal with H : stk rsegs _ _ _ |- _ => exact H end
  | lazymatch goal with H : mem_inv rsegs _ |- _ => exact H end
  | lazymatch goal with H : rw_cells rsegs _ W_BASE_UBSAN _ |- _ => exact H end
  | apply ent_W14_eq; lad_v
  | lazymatch goal with H : munch _ _ _ |- _ => exact H end
  | lazymatch goal with H : wmono rsegs _ _ |- _ => exact H end
  | lazymatch goal with H : rw_cells rsegs _ _ (CB 64 _ :: _) |- _ => exact H end ].

(* a cursor length n >= 1: the bytes are read; HP names the fact on n *)
Ltac lad_case :=
  let data := fresh "data" in let D := fresh "D" in let regs0 := fresh "regs0" in let m0 := fresh "m0" in
  let Sp := fresh "Sp" in let lo := fresh "lo" in let B1 := fresh "B1" in let o := fresh "o" in
  let n := fresh "n" in let flags := fresh "flags" in let F := fresh "F" in let fc := fresh "fc" in
  let ms := fresh "ms" in let Q := fresh "Q" in
  intros data D regs0 m0 Sp lo B1 o n flags F fc ms Q HP HNUM HFL Ho Hn Hon HDAT HD0 HS K;
  cbv beta in HP;
  destruct HS as (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s4 & s5 & s6 & s8 & s10 & s11 &
                  t3 & t4 & t5 & t6 & m & -> & HM);
  destruct HM as (j0 & j60 & ST & MI & WM & MU0 & WMO0 & FR);
  unfold ent_frame, llvm_saved in FR; cbn [app] in FR;
  destruct HNUM as (H16 & Hlo & HK & H63 & HWL); unfold LH_K, LH_FRAME in *;
  pose proof (wm_len _ _ _ _ WM) as LB;
  wk_facts; wk_eq_fact OFF_g_fail_next; wk_eq_fact OFF_g_cfg;
  destruct HDAT as [HDe | (Hd0 & Hdl & How & HD)]; [exfalso; specialize (HD0 HDe); lia |];
  unfold off_world in How;
  assert (HDm : bytes_at rsegs m data D)
    by (eapply bytes_at_transport; [exact HD | exact MU0 | cbn [disjoint_from]; unfold W_BASE_UBSAN, W_LEN in *;
                                     split; [lia | split; [lia | exact I]]]);
  assert (Us0 : bv_unsigned (Z_to_bv 64 (data + o)) = data + o) by (apply unsigned_lit; lia);
  assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia);
  lad_run HDm o;
  lad_fin K.
