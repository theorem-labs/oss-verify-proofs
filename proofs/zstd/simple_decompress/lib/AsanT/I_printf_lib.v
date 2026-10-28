(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun Stdio_pure.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ShadowTac F_irt F_rip.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.

Section CANSEC1. Context {rc : runConstT}.
Definition printf_common_entry := 0x46ac0%Z.

(* [comment removed for export] *)
End CANSEC1.
Ltac norm_sub :=
  repeat match goal with
  | |- context [Z.sub (bv_unsigned ?x) ?c] => is_Zlit c; let v := eval vm_compute in (- c)%Z in
        replace (Z.sub (bv_unsigned x) c) with (Z.add (bv_unsigned x) v) by lia
  end.
Ltac zs := zstep; norm_sub.

Section CANSEC2. Context {rc : runConstT}.
Lemma le1_unsigned8 : forall b : byte, le1 (Z_to_bv 64 (bv_unsigned b)) = [b].
Proof. intros b. exact (le1_zxb b). Qed.

Lemma unsigned_lit8 : forall z, (0 <= z < 256)%Z -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bytes_eq_of_unsigned : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|b1 l1 IH]; intros [|b2 l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

Lemma rw_cells_recell_mid : forall segs m A pre mid post mid',
  rw_cells segs m A (pre ++ mid ++ post) -> cells_wf mid' ->
  map bv_unsigned (cells_bytes mid') = map bv_unsigned (cells_bytes mid) ->
  rw_cells segs m A (pre ++ mid' ++ post).
Proof.
  intros segs m A pre mid post mid' RW WF E.
  apply bytes_eq_of_unsigned in E.
  destruct RW as [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W23]. apply cells_wf_app in W23. destruct W23 as [W2 W3].
  assert (SZ : cells_size mid' = cells_size mid).
  { rewrite <- (cells_bytes_length mid' WF), <- (cells_bytes_length mid W2), E. reflexivity. }
  split; [split|].
  - apply cells_wf_app. split; [exact W1|]. apply cells_wf_app. split; assumption.
  - rewrite !cells_bytes_app in *. rewrite E. exact Hb.
  - rewrite !cells_size_app in *. rewrite SZ. exact Hw.
Qed.

(* [comment removed for export] *)
End CANSEC2.
Ltac recell H k len mid' :=
  lazymatch type of H with rw_cells ?segs ?m ?A ?cs =>
    let pre := eval cbn [firstn] in (firstn k cs) in
    let mid := eval cbn [firstn skipn] in (firstn len (skipn k cs)) in
    let post := eval cbn [skipn Nat.add] in (skipn (k + len) cs) in
    change (rw_cells segs m A cs) with (rw_cells segs m A (pre ++ mid ++ post)) in H;
    apply (rw_cells_recell_mid segs m A pre mid post mid') in H;
    [ cbn [app] in H | cbv; repeat split; reflexivity | vm_compute; reflexivity ]
  end.

Section CANSEC3. Context {rc : runConstT}.
Lemma rw_cells_join : forall segs m A B cs1 cs2,
  rw_cells segs m A cs1 -> rw_cells segs m B cs2 -> B = (A + Z.of_nat (cells_size cs1))%Z -> rw_cells segs m A (cs1 ++ cs2).
Proof. intros segs m A B cs1 cs2 H1 H2 ->. apply (proj2 (rw_cells_app segs m A cs1 cs2)). split; assumption. Qed.

(* [comment removed for export] *)
End CANSEC3.
Ltac chunk_split H k H2 :=
  lazymatch type of H with rw_cells ?segs ?m ?A ?cs =>
    let cs1 := eval cbn [firstn] in (firstn k cs) in
    let cs2 := eval cbn [skipn] in (skipn k cs) in
    change (rw_cells segs m A cs) with (rw_cells segs m A (cs1 ++ cs2)) in H;
    apply (proj1 (rw_cells_app segs m A cs1 cs2)) in H; destruct H as [H H2];
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in H2;
    lazymatch type of H2 with rw_cells _ _ (Z.add (Z.add ?b ?c) ?d) _ =>
      let v := eval vm_compute in (Z.add c d) in
      replace (Z.add (Z.add b c) d) with (Z.add b v) in H2 by lia
    | _ => idtac end
  end.
(* [comment removed for export] *)
Ltac chunk_join H H2 :=
  lazymatch type of H with rw_cells ?segs ?m ?A ?cs1 => lazymatch type of H2 with rw_cells _ _ ?B ?cs2 =>
    pose proof (rw_cells_join segs m A B cs1 cs2 H H2 ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; lia)) as Hj;
    clear H H2; cbn [app] in Hj; rename Hj into H
  end end.

Section CANSEC4. Context {rc : runConstT}.
Lemma u8arr_of_chunk : forall segs m A cs, rw_cells segs m A cs ->
  exists bs, u8arr segs m A bs /\ length bs = cells_size cs.
Proof.
  intros segs m A cs H. destruct (rw_cells_forget segs m A cs H) as [junk Hj].
  exists junk. split; [eapply u8arr_of_rw_cells; exact Hj|].
  destruct Hj as [[Hwf _] _]. cbn in Hwf. destruct Hwf as [Hl _]. exact Hl.
Qed.

End CANSEC4.
Notation zcells0 :=
  ([C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3)]) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC5. Context {rc : runConstT}.
Definition S_FLAGS : Z := 0x15307.  Definition B_FLAGS : list byte := [Z_to_bv 8 39; Z_to_bv 8 45; Z_to_bv 8 43; Z_to_bv 8 32; Z_to_bv 8 35; Z_to_bv 8 48].  (* [comment removed for export] *)
Definition S_JZT : Z := 0x1b4fd.    Definition B_JZT : list byte := [Z_to_bv 8 106; Z_to_bv 8 122; Z_to_bv 8 116; Z_to_bv 8 76; Z_to_bv 8 113].  (* [comment removed for export] *)
Definition S_CCSS : Z := 0x140fe.   Definition B_CCSS : list byte := [Z_to_bv 8 99; Z_to_bv 8 67; Z_to_bv 8 115; Z_to_bv 8 83].  (* [comment removed for export] *)
Definition S_AEFG : Z := 0x16370.   Definition B_AEFG : list byte := [Z_to_bv 8 97; Z_to_bv 8 65; Z_to_bv 8 101; Z_to_bv 8 69; Z_to_bv 8 102; Z_to_bv 8 70; Z_to_bv 8 103; Z_to_bv 8 71].  (* [comment removed for export] *)
Definition S_DIOUX : Z := 0x1c5c2.  Definition B_DIOUX : list byte := [Z_to_bv 8 100; Z_to_bv 8 105; Z_to_bv 8 111; Z_to_bv 8 117; Z_to_bv 8 120; Z_to_bv 8 88; Z_to_bv 8 110].  (* [comment removed for export] *)

Definition S_CS : Z := 0x19bee.     Definition B_CS : list byte := [Z_to_bv 8 67; Z_to_bv 8 83].  (* [comment removed for export] *)
Definition S_CSB : Z := 0x1081e.    Definition B_CSB : list byte := [Z_to_bv 8 99; Z_to_bv 8 115; Z_to_bv 8 91].  (* [comment removed for export] *)
Definition S_SS : Z := 0x13a1f.     Definition B_SS : list byte := [Z_to_bv 8 115; Z_to_bv 8 83].  (* [comment removed for export] *)
End CANSEC5.
Ltac img_str A B :=
  intros m MI; apply ro_bytes_at; [exact MI| unfold A; lia| unfold A, B; cbn [length app]; lia|];
  apply ro_bytes_b_sound; vm_compute; reflexivity.
Section CANSEC6. Context {rc : runConstT}.
Lemma flags_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m S_FLAGS (B_FLAGS ++ Z_to_bv 8 0 :: []). Proof. img_str S_FLAGS B_FLAGS. Qed.
Lemma jzt_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m S_JZT (B_JZT ++ Z_to_bv 8 0 :: []). Proof. img_str S_JZT B_JZT. Qed.
Lemma ccss_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m S_CCSS (B_CCSS ++ Z_to_bv 8 0 :: []). Proof. img_str S_CCSS B_CCSS. Qed.
Lemma aefg_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m S_AEFG (B_AEFG ++ Z_to_bv 8 0 :: []). Proof. img_str S_AEFG B_AEFG. Qed.
Lemma dioux_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m S_DIOUX (B_DIOUX ++ Z_to_bv 8 0 :: []). Proof. img_str S_DIOUX B_DIOUX. Qed.
Lemma cs_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m S_CS (B_CS ++ Z_to_bv 8 0 :: []). Proof. img_str S_CS B_CS. Qed.
Lemma csb_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m S_CSB (B_CSB ++ Z_to_bv 8 0 :: []). Proof. img_str S_CSB B_CSB. Qed.
Lemma ss_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m S_SS (B_SS ++ Z_to_bv 8 0 :: []). Proof. img_str S_SS B_SS. Qed.
End CANSEC6.
Ltac noz_tac :=
  apply Forall_forall; let b := fresh "b" in let Hb := fresh "Hb" in intros b Hb;
  repeat (destruct Hb as [<-|Hb]; [cbv; discriminate|]); destruct Hb.
Section CANSEC7. Context {rc : runConstT}.
Lemma flags_noz : Forall (fun b : byte => bv_unsigned b <> 0%Z) B_FLAGS. Proof. noz_tac. Qed.
Lemma jzt_noz : Forall (fun b : byte => bv_unsigned b <> 0%Z) B_JZT. Proof. noz_tac. Qed.
Lemma ccss_noz : Forall (fun b : byte => bv_unsigned b <> 0%Z) B_CCSS. Proof. noz_tac. Qed.
Lemma aefg_noz : Forall (fun b : byte => bv_unsigned b <> 0%Z) B_AEFG. Proof. noz_tac. Qed.
Lemma cs_noz : Forall (fun b : byte => bv_unsigned b <> 0%Z) B_CS. Proof. noz_tac. Qed.
Lemma csb_noz : Forall (fun b : byte => bv_unsigned b <> 0%Z) B_CSB. Proof. noz_tac. Qed.
Lemma ss_noz : Forall (fun b : byte => bv_unsigned b <> 0%Z) B_SS. Proof. noz_tac. Qed.
Lemma dioux_noz : Forall (fun b : byte => bv_unsigned b <> 0%Z) B_DIOUX. Proof. noz_tac. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fgvs_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 4) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).

Lemma fgvs_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (c : Z) (idx : nat) (LM : Z),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 32)%Z ->
  find_byte c B_DIOUX = Some idx -> (0 < c < 256)%Z ->
  rw_cells bsegs m LM [C1 (Z_to_bv 8 0)] -> (bv_unsigned sp <= LM)%Z -> (LM < 2^64)%Z ->
  rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng RNG LM 1 ->
  evtF bsegs RNG (fgvs_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 LM) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x49c84) fc None m (seg_rom bsegs)).
Proof.
  intros until LM. intros MI ST LO HF CR LMC SEP LMH RSTK RI RLM.
  pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (RSTK' : rng RNG (bv_unsigned sp + -32) 32) by (eapply rng_sub'; [exact RSTK| lia]).
  carve_frame 32%nat ST.
  do 11 zstep. zstep.
  call istrchr_spec; [ eassumption | apply dioux_bytes; assumption | exact dioux_noz | reflexivity | exact CR
                     | rewrite unsigned_lit by lia; eapply rng_sub'; [exact RI | cbn; lia] | ].
  unfold istrchr_res. rewrite HF. rewrite unsigned_lit by (unfold S_DIOUX; lia).
  zstep. if_cases K1; zify_cond K1.
  { exfalso. apply find_byte_Some in HF. destruct HF as [HF _]. cbn in HF.
    change 18446744073709551615%Z with (Z.ones 64) in K1. rewrite Z.land_ones in K1 by lia. rewrite Z.mod_small in K1 by lia. lia. }
  clear K1. zstep. cbv beta. rewrite unsigned_lit8 by lia. zstep. zstep. zstep. if_cases K2; zify_cond K2. 2:{ exfalso. clear -K2. lia. }
  clear K2. zstep. if_cases K3; zify_cond K3. 2:{ exfalso. clear -K3. lia. }
  do 7 zstep.
  release_frame FR ST (bv_unsigned sp). finish.
Qed.


(* [comment removed for export] *)
Definition printf_common_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 2320, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).

End CANSEC7.
