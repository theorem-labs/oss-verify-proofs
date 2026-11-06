(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_pure.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ZBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg RtCells ShadowTac.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_m2s_b__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_rip.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module I_printf_lib.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import Stdio_pure.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ZBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg RtCells ShadowTac. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_m2s_b__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_rip. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_irt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_rip.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
Definition printf_common_entry := 0x4729c%Z.

(* [comment removed for export] *)
End CANSEC1.
Ltac norm_sub :=
  repeat match goal with
  | |- context [Z.sub (bv_unsigned ?x) ?c] => is_Zlit c; let v := eval vm_compute in (- c)%Z in
        replace (Z.sub (bv_unsigned x) c) with (Z.add (bv_unsigned x) v) by lia
  end.
Ltac zs := zstep; norm_sub.

Section CANSEC2. Context {rc : runConstT}.
#[using="Type"] Lemma le1_unsigned8 : forall b : byte, le1 (Z_to_bv 64 (bv_unsigned b)) = [b].
Proof. intros b. exact (le1_zxb b). Qed.

#[using="Type"] Lemma unsigned_lit8 : forall z, (0 <= z < 256)%Z -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma bytes_eq_of_unsigned : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|b1 l1 IH]; intros [|b2 l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

Definition rw_cells_recell_mid__stmt : Prop := forall segs m A pre mid post mid',
  rw_cells segs m A (pre ++ mid ++ post) -> cells_wf mid' ->
  map bv_unsigned (cells_bytes mid') = map bv_unsigned (cells_bytes mid) ->
  rw_cells segs m A (pre ++ mid' ++ post).
Section Sz4.
Variables segs m A pre mid post mid' : ltac2:(SecDiet.SzSec.tyM 'rw_cells_recell_mid__stmt "vvvvvvv" @segs).
#[using="Type"] Lemma rw_cells_recell_mid__body : ltac2:(SecDiet.SzSec.bodyP 'rw_cells_recell_mid__stmt "vvvvvvv").
Proof.
  intros RW WF E.
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
End Sz4.
#[using="Type"] Lemma rw_cells_recell_mid : ltac:(let t := eval cbv delta [rw_cells_recell_mid__stmt] in rw_cells_recell_mid__stmt in exact t).
Proof. intros segs m A pre mid post mid'. ltac2:(SecDiet.SzSec.closeP 'rw_cells_recell_mid__body "vvvvvvv"). Qed.

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
#[using="Type"] Lemma rw_cells_join : forall segs m A B cs1 cs2,
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
#[using="Type"] Lemma u8arr_of_chunk : forall segs m A cs, rw_cells segs m A cs ->
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
Definition S_FLAGS : Z := 0x15358.  Definition B_FLAGS : list byte := [Z_to_bv 8 39; Z_to_bv 8 45; Z_to_bv 8 43; Z_to_bv 8 32; Z_to_bv 8 35; Z_to_bv 8 48].  (* [comment removed for export] *)
Definition S_JZT : Z := 0x1b3dd.    Definition B_JZT : list byte := [Z_to_bv 8 106; Z_to_bv 8 122; Z_to_bv 8 116; Z_to_bv 8 76; Z_to_bv 8 113].  (* [comment removed for export] *)
Definition S_CCSS : Z := 0x14146.   Definition B_CCSS : list byte := [Z_to_bv 8 99; Z_to_bv 8 67; Z_to_bv 8 115; Z_to_bv 8 83].  (* [comment removed for export] *)
Definition S_FLTCV : Z := 0x163d3.   Definition B_FLTCV : list byte := [Z_to_bv 8 97; Z_to_bv 8 65; Z_to_bv 8 101; Z_to_bv 8 69; Z_to_bv 8 102; Z_to_bv 8 70; Z_to_bv 8 103; Z_to_bv 8 71].  (* [comment removed for export] *)
Definition S_DIOUX : Z := 0x1c578.  Definition B_DIOUX : list byte := [Z_to_bv 8 100; Z_to_bv 8 105; Z_to_bv 8 111; Z_to_bv 8 117; Z_to_bv 8 120; Z_to_bv 8 88; Z_to_bv 8 110].  (* [comment removed for export] *)

Definition S_CS : Z := 0x19af6.     Definition B_CS : list byte := [Z_to_bv 8 67; Z_to_bv 8 83].  (* [comment removed for export] *)
Definition S_CSB : Z := 0x107e6.    Definition B_CSB : list byte := [Z_to_bv 8 99; Z_to_bv 8 115; Z_to_bv 8 91].  (* [comment removed for export] *)
Definition S_SS : Z := 0x13a66.     Definition B_SS : list byte := [Z_to_bv 8 115; Z_to_bv 8 83].  (* [comment removed for export] *)
End CANSEC5.
Ltac img_str A B :=
  intros m MI; apply ro_bytes_at; [exact MI| unfold A; lia| unfold A, B; cbn [length app]; lia|];
  apply ro_bytes_b_sound; vm_compute; reflexivity.
Section CANSEC6. Context {rc : runConstT}.
#[using="Type"] Lemma flags_bytes : forall m, mem_inv asegs m -> bytes_at asegs m S_FLAGS (B_FLAGS ++ Z_to_bv 8 0 :: []). Proof. img_str S_FLAGS B_FLAGS. Qed.
#[using="Type"] Lemma jzt_bytes : forall m, mem_inv asegs m -> bytes_at asegs m S_JZT (B_JZT ++ Z_to_bv 8 0 :: []). Proof. img_str S_JZT B_JZT. Qed.
#[using="Type"] Lemma ccss_bytes : forall m, mem_inv asegs m -> bytes_at asegs m S_CCSS (B_CCSS ++ Z_to_bv 8 0 :: []). Proof. img_str S_CCSS B_CCSS. Qed.
#[using="Type"] Lemma fltcv_bytes : forall m, mem_inv asegs m -> bytes_at asegs m S_FLTCV (B_FLTCV ++ Z_to_bv 8 0 :: []). Proof. img_str S_FLTCV B_FLTCV. Qed.
#[using="Type"] Lemma dioux_bytes : forall m, mem_inv asegs m -> bytes_at asegs m S_DIOUX (B_DIOUX ++ Z_to_bv 8 0 :: []). Proof. img_str S_DIOUX B_DIOUX. Qed.
#[using="Type"] Lemma cs_bytes : forall m, mem_inv asegs m -> bytes_at asegs m S_CS (B_CS ++ Z_to_bv 8 0 :: []). Proof. img_str S_CS B_CS. Qed.
#[using="Type"] Lemma csb_bytes : forall m, mem_inv asegs m -> bytes_at asegs m S_CSB (B_CSB ++ Z_to_bv 8 0 :: []). Proof. img_str S_CSB B_CSB. Qed.
#[using="Type"] Lemma ss_bytes : forall m, mem_inv asegs m -> bytes_at asegs m S_SS (B_SS ++ Z_to_bv 8 0 :: []). Proof. img_str S_SS B_SS. Qed.
End CANSEC6.
Ltac noz_tac :=
  apply Forall_forall; let b := fresh "b" in let Hb := fresh "Hb" in intros b Hb;
  repeat (destruct Hb as [<-|Hb]; [cbv; discriminate|]); destruct Hb.
Section CANSEC7. Context {rc : runConstT}.
#[using="Type"] Lemma flags_noz : Forall (fun b : byte => bv_unsigned b <> 0%Z) B_FLAGS. Proof. noz_tac. Qed.
#[using="Type"] Lemma jzt_noz : Forall (fun b : byte => bv_unsigned b <> 0%Z) B_JZT. Proof. noz_tac. Qed.
#[using="Type"] Lemma ccss_noz : Forall (fun b : byte => bv_unsigned b <> 0%Z) B_CCSS. Proof. noz_tac. Qed.
#[using="Type"] Lemma fltcv_noz : Forall (fun b : byte => bv_unsigned b <> 0%Z) B_FLTCV. Proof. noz_tac. Qed.
#[using="Type"] Lemma cs_noz : Forall (fun b : byte => bv_unsigned b <> 0%Z) B_CS. Proof. noz_tac. Qed.
#[using="Type"] Lemma csb_noz : Forall (fun b : byte => bv_unsigned b <> 0%Z) B_CSB. Proof. noz_tac. Qed.
#[using="Type"] Lemma ss_noz : Forall (fun b : byte => bv_unsigned b <> 0%Z) B_SS. Proof. noz_tac. Qed.
#[using="Type"] Lemma dioux_noz : Forall (fun b : byte => bv_unsigned b <> 0%Z) B_DIOUX. Proof. noz_tac. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fgvs_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 4) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Definition fgvs_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (c : Z) (idx : nat) (LM : Z),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 32)%Z ->
  find_byte c B_DIOUX = Some idx -> (0 < c < 256)%Z ->
  rw_cells asegs m LM [C1 (Z_to_bv 8 0)] -> (bv_unsigned sp <= LM)%Z -> (LM < 2^64)%Z ->
  rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng RNG LM 1 ->
  evtF asegs RNG (fgvs_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 LM) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4ade0) fc None m (seg_rom asegs)).
Section Sz23.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo c idx LM : ltac2:(SecDiet.SzSec.tyM 'fgvs_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma fgvs_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fgvs_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros MI ST LO HF CR LMC SEP LMH RSTK RI RLM.
  pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
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
End Sz23.
#[using="Type"] Lemma fgvs_spec : ltac:(let t := eval cbv delta [fgvs_spec__stmt] in fgvs_spec__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo c idx LM. ltac2:(SecDiet.SzSec.closeP 'fgvs_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.


(* [comment removed for export] *)
Definition printf_common_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2320, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

End CANSEC7.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_pure.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_irt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_rip.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
Definition printf_common_entry := 0x47304%Z.

(* [comment removed for export] *)
End CANSEC1.
Ltac norm_sub :=
  repeat match goal with
  | |- context [Z.sub (bv_unsigned ?x) ?c] => is_Zlit c; let v := eval vm_compute in (- c)%Z in
        replace (Z.sub (bv_unsigned x) c) with (Z.add (bv_unsigned x) v) by lia
  end.
Ltac zs := zstep; norm_sub.

Section CANSEC2. Context {rc : runConstT}.
#[using="Type"] Lemma le1_unsigned8 : forall b : byte, le1 (Z_to_bv 64 (bv_unsigned b)) = [b].
Proof. intros b. exact (le1_zxb b). Qed.

#[using="Type"] Lemma unsigned_lit8 : forall z, (0 <= z < 256)%Z -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma bytes_eq_of_unsigned : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|b1 l1 IH]; intros [|b2 l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

Definition rw_cells_recell_mid__stmt : Prop := forall segs m A pre mid post mid',
  rw_cells segs m A (pre ++ mid ++ post) -> cells_wf mid' ->
  map bv_unsigned (cells_bytes mid') = map bv_unsigned (cells_bytes mid) ->
  rw_cells segs m A (pre ++ mid' ++ post).
Section Sz4.
Variables segs m A pre mid post mid' : ltac2:(SecDiet.SzSec.tyM 'rw_cells_recell_mid__stmt "vvvvvvv" @segs).
#[using="Type"] Lemma rw_cells_recell_mid__body : ltac2:(SecDiet.SzSec.bodyP 'rw_cells_recell_mid__stmt "vvvvvvv").
Proof.
  intros RW WF E.
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
End Sz4.
#[using="Type"] Lemma rw_cells_recell_mid : ltac:(let t := eval cbv delta [rw_cells_recell_mid__stmt] in rw_cells_recell_mid__stmt in exact t).
Proof. intros segs m A pre mid post mid'. ltac2:(SecDiet.SzSec.closeP 'rw_cells_recell_mid__body "vvvvvvv"). Qed.

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
#[using="Type"] Lemma rw_cells_join : forall segs m A B cs1 cs2,
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
#[using="Type"] Lemma u8arr_of_chunk : forall segs m A cs, rw_cells segs m A cs ->
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
Definition S_FLAGS : Z := 0x15358.  Definition B_FLAGS : list byte := [Z_to_bv 8 39; Z_to_bv 8 45; Z_to_bv 8 43; Z_to_bv 8 32; Z_to_bv 8 35; Z_to_bv 8 48].  (* [comment removed for export] *)
Definition S_JZT : Z := 0x1b3d5.    Definition B_JZT : list byte := [Z_to_bv 8 106; Z_to_bv 8 122; Z_to_bv 8 116; Z_to_bv 8 76; Z_to_bv 8 113].  (* [comment removed for export] *)
Definition S_CCSS : Z := 0x14146.   Definition B_CCSS : list byte := [Z_to_bv 8 99; Z_to_bv 8 67; Z_to_bv 8 115; Z_to_bv 8 83].  (* [comment removed for export] *)
Definition S_FLTCV : Z := 0x163d3.   Definition B_FLTCV : list byte := [Z_to_bv 8 97; Z_to_bv 8 65; Z_to_bv 8 101; Z_to_bv 8 69; Z_to_bv 8 102; Z_to_bv 8 70; Z_to_bv 8 103; Z_to_bv 8 71].  (* [comment removed for export] *)
Definition S_DIOUX : Z := 0x1c570.  Definition B_DIOUX : list byte := [Z_to_bv 8 100; Z_to_bv 8 105; Z_to_bv 8 111; Z_to_bv 8 117; Z_to_bv 8 120; Z_to_bv 8 88; Z_to_bv 8 110].  (* [comment removed for export] *)

Definition S_CS : Z := 0x19aee.     Definition B_CS : list byte := [Z_to_bv 8 67; Z_to_bv 8 83].  (* [comment removed for export] *)
Definition S_CSB : Z := 0x107e6.    Definition B_CSB : list byte := [Z_to_bv 8 99; Z_to_bv 8 115; Z_to_bv 8 91].  (* [comment removed for export] *)
Definition S_SS : Z := 0x13a66.     Definition B_SS : list byte := [Z_to_bv 8 115; Z_to_bv 8 83].  (* [comment removed for export] *)
End CANSEC5.
Ltac img_str A B :=
  intros m MI; apply ro_bytes_at; [exact MI| unfold A; lia| unfold A, B; cbn [length app]; lia|];
  apply ro_bytes_b_sound; vm_compute; reflexivity.
Section CANSEC6. Context {rc : runConstT}.
#[using="Type"] Lemma flags_bytes : forall m, mem_inv asegs m -> bytes_at asegs m S_FLAGS (B_FLAGS ++ Z_to_bv 8 0 :: []). Proof. img_str S_FLAGS B_FLAGS. Qed.
#[using="Type"] Lemma jzt_bytes : forall m, mem_inv asegs m -> bytes_at asegs m S_JZT (B_JZT ++ Z_to_bv 8 0 :: []). Proof. img_str S_JZT B_JZT. Qed.
#[using="Type"] Lemma ccss_bytes : forall m, mem_inv asegs m -> bytes_at asegs m S_CCSS (B_CCSS ++ Z_to_bv 8 0 :: []). Proof. img_str S_CCSS B_CCSS. Qed.
#[using="Type"] Lemma fltcv_bytes : forall m, mem_inv asegs m -> bytes_at asegs m S_FLTCV (B_FLTCV ++ Z_to_bv 8 0 :: []). Proof. img_str S_FLTCV B_FLTCV. Qed.
#[using="Type"] Lemma dioux_bytes : forall m, mem_inv asegs m -> bytes_at asegs m S_DIOUX (B_DIOUX ++ Z_to_bv 8 0 :: []). Proof. img_str S_DIOUX B_DIOUX. Qed.
#[using="Type"] Lemma cs_bytes : forall m, mem_inv asegs m -> bytes_at asegs m S_CS (B_CS ++ Z_to_bv 8 0 :: []). Proof. img_str S_CS B_CS. Qed.
#[using="Type"] Lemma csb_bytes : forall m, mem_inv asegs m -> bytes_at asegs m S_CSB (B_CSB ++ Z_to_bv 8 0 :: []). Proof. img_str S_CSB B_CSB. Qed.
#[using="Type"] Lemma ss_bytes : forall m, mem_inv asegs m -> bytes_at asegs m S_SS (B_SS ++ Z_to_bv 8 0 :: []). Proof. img_str S_SS B_SS. Qed.
End CANSEC6.
Ltac noz_tac :=
  apply Forall_forall; let b := fresh "b" in let Hb := fresh "Hb" in intros b Hb;
  repeat (destruct Hb as [<-|Hb]; [cbv; discriminate|]); destruct Hb.
Section CANSEC7. Context {rc : runConstT}.
#[using="Type"] Lemma flags_noz : Forall (fun b : byte => bv_unsigned b <> 0%Z) B_FLAGS. Proof. noz_tac. Qed.
#[using="Type"] Lemma jzt_noz : Forall (fun b : byte => bv_unsigned b <> 0%Z) B_JZT. Proof. noz_tac. Qed.
#[using="Type"] Lemma ccss_noz : Forall (fun b : byte => bv_unsigned b <> 0%Z) B_CCSS. Proof. noz_tac. Qed.
#[using="Type"] Lemma fltcv_noz : Forall (fun b : byte => bv_unsigned b <> 0%Z) B_FLTCV. Proof. noz_tac. Qed.
#[using="Type"] Lemma cs_noz : Forall (fun b : byte => bv_unsigned b <> 0%Z) B_CS. Proof. noz_tac. Qed.
#[using="Type"] Lemma csb_noz : Forall (fun b : byte => bv_unsigned b <> 0%Z) B_CSB. Proof. noz_tac. Qed.
#[using="Type"] Lemma ss_noz : Forall (fun b : byte => bv_unsigned b <> 0%Z) B_SS. Proof. noz_tac. Qed.
#[using="Type"] Lemma dioux_noz : Forall (fun b : byte => bv_unsigned b <> 0%Z) B_DIOUX. Proof. noz_tac. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fgvs_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 4) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Definition fgvs_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (c : Z) (idx : nat) (LM : Z),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 32)%Z ->
  find_byte c B_DIOUX = Some idx -> (0 < c < 256)%Z ->
  rw_cells asegs m LM [C1 (Z_to_bv 8 0)] -> (bv_unsigned sp <= LM)%Z -> (LM < 2^64)%Z ->
  rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng RNG LM 1 ->
  evtF asegs RNG (fgvs_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 LM) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4ae48) fc None m (seg_rom asegs)).
Section Sz23.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo c idx LM : ltac2:(SecDiet.SzSec.tyM 'fgvs_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma fgvs_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fgvs_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros MI ST LO HF CR LMC SEP LMH RSTK RI RLM.
  pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
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
End Sz23.
#[using="Type"] Lemma fgvs_spec : ltac:(let t := eval cbv delta [fgvs_spec__stmt] in fgvs_spec__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo c idx LM. ltac2:(SecDiet.SzSec.closeP 'fgvs_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.


(* [comment removed for export] *)
Definition printf_common_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2320, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

End CANSEC7.
End TwB.
End I_printf_lib.

(* [comment removed for export] *)
Module I_fwrite.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import Stdio_pure.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ZBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg RtCells ShadowTac F_rip. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_m2s_b__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_rip OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_tryinit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.

Ltac iprem :=
  lazymatch goal with
  | |- evtF _ _ _ _ => idtac
  | |- mem_inv _ _ => first [assumption | eassumption]
  | |- context [bv_unsigned (Z_to_bv 64 _)] => rewrite !unsigned_lit by lia; iprem
  | |- stk _ _ _ _ => first [assumption | eassumption]
  | |- rw_cells _ _ _ _ => rewrite ?Z_to_bv_bv_unsigned; first [assumption | eassumption]
  | |- shadow_bytes _ _ _ _ => first [assumption | eassumption]
  | |- bytes_at _ _ _ _ => first [assumption | eassumption]
  | |- unpoisoned _ _ _ => first [assumption | eassumption]
  | |- wr_at _ _ _ _ => first [assumption | eassumption]
  | |- app_blk _ _ => first [assumption | eassumption]
  | |- Forall _ _ => first [assumption | eassumption]
  | |- _ = Z_to_bv 64 _ => first [reflexivity | assumption | symmetry; assumption]
  | |- rng _ _ _ => first [ assumption | match goal with H : rng _ _ _ |- _ => eapply rng_sub'; [exact H | unfold KHIGH, sf_hide in *; lia] end ]
  | |- _ => unfold KHIGH, sf_hide in *; first [assumption | lia]
  end.

(* [comment removed for export] *)
Notation rt_real_fwrite m := (rw_cells asegs m 0xa7220 [C8 (Z_to_bv 64 0x9abc8)]).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition fwrite_i_mid (ra sp gp tp s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 x14 x15 x16 x17 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x46904) (Z_to_bv 64 (bv_unsigned sp - 2128)) gp tp t0 t1 t2
                  sp a1 a0 a1 a2 a3 x14 x15 x16 x17
                  a0 a3 a2 (Z_to_bv 64 1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x9abc8) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2144, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp - 2128) /\ stk asegs m' (bv_unsigned sp - 2128) (bv_unsigned sp - 56)
    /\ rw_cells asegs m' (bv_unsigned sp - 56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rt_inited m'.

Section FWRITE_PRE.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 2144)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis INI : rt_inited m.
  Hypothesis RFW : rt_real_fwrite m.
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).

  #[using="MI ST LO KLO INI RFW RI RSTK"] Lemma fwrite_i_pre :
    evtF asegs RNG (fwrite_i_mid ra sp gp tp s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x468a8) fc None m (seg_rom asegs)).
  Proof.
    pose proof (munch_refl [(bv_unsigned sp + -2144, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption). unfold KHIGH in KLO.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2144) 2144) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof MI as MIc. pose proof ST as ST0. pose proof INI as INIc. pose proof RFW as RFWc.
    change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in INI; change (?P) with (sf_hide P) in RFW.
    carve_frame 56%nat ST0.
    destruct (stk_split _ _ lo (bv_unsigned sp + -2128) _ ST0 ltac:(lia)) as [ST1 STM]. clear ST0.
    do 14 zstep. zstep.
    call_sp tryinit_spec. all: iprem.
    do 7 zstep. zstep.
    apply evtF_done. unfold fwrite_i_mid.
    replace (bv_unsigned sp - 2128)%Z with (bv_unsigned sp + -2128)%Z by lia.
    replace (bv_unsigned sp - 56)%Z with (bv_unsigned sp + -56)%Z by lia.
    replace (bv_unsigned sp - 2144)%Z with (bv_unsigned sp + -2144)%Z by lia.
    do 12 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption.
  Qed.
End FWRITE_PRE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fwrite_i_post_post (sp gp tp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (rav s0v s1v s2v s3v s4v s5v : word) (res lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 res) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc rav) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2208, bv_unsigned sp - 2128)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Section FWRITE_POST.
  Variables (RNG : footprint)
            (x1 sp gp tp t0 t1 t2 x9 a1 a2 a3 a4 a5 a6 a7 p x19 x20 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (rav s0v s1v s2v s3v s4v s5v : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo res size N : Z) (RLO RHI : Z).
  Notation P := (bv_unsigned p).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp - 2128).
  Hypothesis STM : stk asegs m (bv_unsigned sp - 2128) (bv_unsigned sp - 56).
  Hypothesis FR : rw_cells asegs m (bv_unsigned sp - 56) [C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].
  Hypothesis LO : (lo <= bv_unsigned sp - 2208)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis LAY : rt_layout m.
  Hypothesis X9 : x9 = Z_to_bv 64 size.
  Hypothesis HN : (res * size)%Z = N.
  Hypothesis RES : (0 <= res < 2^64 /\ 1 <= size /\ 0 <= N <= 2^40)%Z.
  Hypothesis APP : app_blk P (P + N).
  Hypothesis UNP : unpoisoned m P (P + N).
  Hypothesis R1 : (RLO <= P /\ P + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z.
  Hypothesis WR1 : wr_at asegs m (shad RLO) (shad RHI - shad RLO).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RSH1 : rng RNG (shad RLO) (shad RHI - shad RLO).

  Notation POST := (fwrite_i_post_post sp gp tp s6 s7 s8 s9 s10 s11 F fc rav s0v s1v s2v s3v s4v s5v res lo m).

  Definition INV (mc : word -> option byte) : Prop :=
    rw_cells asegs mc (bv_unsigned sp + -56) [C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]
    /\ stk asegs mc lo (bv_unsigned sp + -2128) /\ stk asegs mc (bv_unsigned sp + -2128) (bv_unsigned sp + -56)
    /\ munch [(bv_unsigned sp + -2208, bv_unsigned sp + -2128)]%Z m mc /\ wmono asegs m mc /\ mem_inv asegs mc
    /\ rt_got mc /\ rt_shbase mc /\ rt_layout mc
    /\ unpoisoned mc P (P + N) /\ wr_at asegs mc (shad RLO) (shad RHI - shad RLO).

  Definition BND : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2208 /\ KHIGH <= lo /\ bv_unsigned sp < 2^64 /\ 0 <= N /\ N <= 2^40 /\ 0 <= res < 2^64
     /\ 0 <= P /\ P + N + 8 <= KEND
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad P /\ shad (P + N - 1) + 1 <= shad RHI /\ shad RHI <= KHIGH
     /\ 0 <= Z.shiftr P 3 < 2^44 /\ -1 <= Z.shiftr (P + N + -1) 3 < 2^44
     /\ shad RLO mod 8 = 0 /\ shad RHI mod 8 = 0
     /\ RLO <= P /\ P + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0)%Z.
  #[using="m size ST LO KLO HN RES APP R1"] Lemma BND_ok : BND.
  Proof.
    unfold BND. destruct ST as (L0 & _). destruct APP as [LES AS]. unfold KLOW, KHIGH, KEND in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    pose proof (bv_unsigned_in_range 64 p) as PR. unfold bv_modulus in PR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in PR.
    rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF.
    Z.div_mod_to_equations. lia.
  Qed.
  Ltac acc_facts B ::= pose proof BND_ok as B; unfold BND, KHIGH, KEND in B.

  Definition BL : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2208 /\ 17594333495296 <= lo /\ bv_unsigned sp < 2^64 /\ 0 <= N /\ N <= 2^40 /\ 0 <= res < 2^64
     /\ 0 <= P /\ P + N + 8 <= 2^47
     /\ 0 <= Z.shiftr P 3 < 2^44 /\ -1 <= Z.shiftr (P + N + -1) 3 < 2^44
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad P /\ shad (P + N - 1) + 1 <= shad RHI /\ shad RHI <= 17594333495296)%Z.
  #[using="m size ST LO KLO HN RES APP R1"] Lemma BL_ok : BL. Proof. pose proof BND_ok as B. unfold BND, KHIGH, KEND in B. unfold BL. lia. Qed.

  Ltac inv_open H := destruct H as (FR1 & ST1 & STM1 & MU1 & WM1 & MI1 & GOT1 & SHB1 & LAY1 & UNP1 & WR11).
  Ltac prep IV :=
    pose proof IV as IV0; inv_open IV;
    let B := fresh "BL" in pose proof BL_ok as B; unfold BL in B;
    assert (RSTK' : rng RNG (bv_unsigned sp + -2208) 2208) by (eapply rng_sub'; [exact RSTK| lia]);
    change (?P) with (sf_hide P) in R1; change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO;
    change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in STM;
    change (?P) with (sf_hide P) in FR; change (?P) with (sf_hide P) in GOT; change (?P) with (sf_hide P) in SHB;
    change (?P) with (sf_hide P) in LAY; change (?P) with (sf_hide P) in UNP; change (?P) with (sf_hide P) in WR1.

  #[using="res size ST LO KLO HN RES APP UNP R1 WR1"] Lemma inv_of : forall mc,
    rw_cells asegs mc (bv_unsigned sp + -56) [C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
    stk asegs mc lo (bv_unsigned sp + -2128) -> stk asegs mc (bv_unsigned sp + -2128) (bv_unsigned sp + -56) ->
    munch [(bv_unsigned sp + -2208, bv_unsigned sp + -2128)]%Z m mc -> wmono asegs m mc -> mem_inv asegs mc ->
    rt_got mc -> rt_shbase mc -> rt_layout mc -> INV mc.
  Proof.
    intros mc FR1 ST1 STM1 MU1 WM1 MI1 G1 G2 G3. pose proof BND_ok as B. unfold BND, KHIGH, KEND in B.
    repeat (split; [assumption|]).
    assert (SS : (shad (P + N - 1) + 1 <= 17594333495296)%Z) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
    split. { eapply unpoisoned_munch; [exact UNP | exact MU1 |]. cbn [disjoint_from]. lia. }
    eapply wr_at_transport; eassumption.
  Qed.

  Notation FWR pc x10 x11 x12 x13 x14 x15 mc :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2 sp (Z_to_bv 64 N) x10 x11 x12 x13 x14 x15 a6 a7
             p x19 (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mc (seg_rom asegs)) (only parsing).

  (* [comment removed for export] *)
  #[using="size ST LO KLO HN RES APP R1 RSTK"] Lemma LX : forall mc x1' x5 x6 x7 x9' x11 x12 x13 x14 x15 x16 x17 x20' x21' x28 x29 x30 x31, INV mc ->
    evtF asegs RNG POST
      (MS (mkR x1' (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp x9' (Z_to_bv 64 res) x11 x12 x13 x14 x15 x16 x17
               p x19 x20' x21' s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x46968) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. prep IV.
    do 10 zstep.
    pose proof (stk_merge _ _ _ _ _ ST1 STM1 ltac:(lia)) as SK.
    pose proof (stk_release _ _ _ _ _ SK FR1 ltac:(lia)) as SK2. cbn [cells_size csize Nat.add] in SK2.
    replace (bv_unsigned sp + -56 + Z.of_nat 56)%Z with (bv_unsigned sp) in SK2 by lia.
    apply evtF_done. unfold fwrite_i_post_post.
    replace (bv_unsigned sp - 2208)%Z with (bv_unsigned sp + -2208)%Z by lia.
    replace (bv_unsigned sp - 2128)%Z with (bv_unsigned sp + -2128)%Z by lia.
    do 15 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="size ST LO KLO HN RES APP R1 RSTK RSH1"] Lemma LL : forall mc (k : nat) (c : Z) x14 x15,
    INV mc -> (1 <= N <= 64)%Z -> Z.to_nat (shad (P + N - 1) - c) = k -> (shad P <= c < shad (P + N - 1))%Z ->
    evtF asegs RNG POST (FWR 0x46a2c (Z_to_bv 64 res) (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (P + N + -1) 3)) (Z_to_bv 64 0) x14 x15 mc).
  Proof.
    intros mc k c x14 x15 IV N1 Hk Hc. prep IV.
    revert c x14 Hk Hc. induction k as [|k IH]; intros c x14 Hk Hc; [exfalso; lia|].
    assert (SL : (shad (P + N - 1) = 2147450880 + Z.shiftr (P + N + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd asegs mc P (P + N) c UNP1 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K1; zify_cond K1.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LX; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="size ST LO KLO HN RES APP R1 RSTK RSH1"] Lemma LE : forall mc x14 x15, INV mc -> (1 <= N <= 64)%Z ->
    evtF asegs RNG POST (FWR 0x46a10 (Z_to_bv 64 res) (Z_to_bv 64 (2147450880 + Z.shiftr P 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (P + N + -1) 3))
                             (Z_to_bv 64 (P + N + -1)) x14 x15 mc).
  Proof.
    intros mc x14 x15 IV N1. prep IV.
    destruct (unpoisoned_check_rd asegs mc P (P + N) (P + N + -1) 1 UNP1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((P + N + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LX; eassumption.
    - eapply (LL mc); [exact IV0 | exact N1 | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      Z.div_mod_to_equations; lia.
  Qed.

  #[using="size N RLO RHI MI ST STM FR LO KLO GOT SHB LAY X9 HN RES APP UNP R1 WR1 RI RSTK RSH1"] Lemma fwrite_i_post :
    evtF asegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2 sp x9 (Z_to_bv 64 res) a1 a2 a3 a4 a5 a6 a7
               p x19 x20 (Z_to_bv 64 1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x46904) fc None m (seg_rom asegs)).
  Proof.
    assert (IV : INV m).
    { pose proof ST as ST'. pose proof STM as STM'. pose proof FR as FR'.
      replace (bv_unsigned sp - 2128)%Z with (bv_unsigned sp + -2128)%Z in ST', STM' by lia.
      replace (bv_unsigned sp - 56)%Z with (bv_unsigned sp + -56)%Z in STM', FR' by lia.
      repeat (split; [assumption|]); try assumption. all: try apply munch_refl; try apply wmono_refl.
      split; [apply munch_refl|]. split; [apply wmono_refl|]. repeat (split; [assumption|]). assumption. }
    prep IV. subst x9.
    zstep. if_cases K0; zify_cond K0. { exfalso. clear -K0. cbv in K0. lia. } clear K0.
    zstep. if_cases KR; zify_cond KR.
    { (* [comment removed for export] *) eapply LX; eassumption. }
    assert (NPOS : (1 <= N)%Z) by (clear -KR RES HN BL0; nia).
    zstep. rewrite HN.
    zstep. rewrite zb_lxor_ones by lia. zstep. zstep. zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1 BL0. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      assert (N1 : (64 < N)%Z).
      { change 18446744073709551615%Z with (Z.ones 64) in K2. rewrite ?Z.land_ones in K2 by lia. change (2 ^ 64)%Z with 18446744073709551616%Z in K2.
        clear - K2 BL0 NPOS. Z.div_mod_to_equations. lia. }
      zstep. if_cases K3; zify_cond K3. 2:{ exfalso. clear -K3 BL0 N1. lia. }
      zstep. zstep. zstep. zstep.
      unfold sf_hide in LO.
      call_sp rip_spec;
        [ exact MI1 | exact ST1 | lia | unfold KHIGH; lia | exact GOT1 | exact SHB1 | exact LAY1
        | zsimp; exact APP | zsimp; exact UNP1
        | zsimp; pose proof BND_ok as B9; unfold BND in B9; lia
        | eapply rng_sub'; [exact RSTK | lia] | ].
      zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
      zstep. zstep.
      eapply LX. eapply inv_of; eassumption.
    - (* [comment removed for export] *)
      assert (N1 : (1 <= N <= 64)%Z).
      { change 18446744073709551615%Z with (Z.ones 64) in K2. rewrite ?Z.land_ones in K2 by lia. change (2 ^ 64)%Z with 18446744073709551616%Z in K2.
        clear - K2 BL0 NPOS. Z.div_mod_to_equations. lia. }
      do 11 zstep.
      change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
      unfold sf_hide in R1.
      destruct (shadow_probe8 asegs m RLO RHI P WR11 ltac:(apply no_image_asan; pose proof BND_ok as B9; unfold BND in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w1 P1].
      destruct (shadow_probe8 asegs m RLO RHI (P + N + -1) WR11 ltac:(apply no_image_asan; pose proof BND_ok as B9; unfold BND in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w2 P2].
      unfold ASHOFF in P1, P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply LE; eassumption.
      + eapply LX; eassumption.
  Qed.
End FWRITE_POST.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_pure.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_rip.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_tryinit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.

Ltac iprem :=
  lazymatch goal with
  | |- evtF _ _ _ _ => idtac
  | |- mem_inv _ _ => first [assumption | eassumption]
  | |- context [bv_unsigned (Z_to_bv 64 _)] => rewrite !unsigned_lit by lia; iprem
  | |- stk _ _ _ _ => first [assumption | eassumption]
  | |- rw_cells _ _ _ _ => rewrite ?Z_to_bv_bv_unsigned; first [assumption | eassumption]
  | |- shadow_bytes _ _ _ _ => first [assumption | eassumption]
  | |- bytes_at _ _ _ _ => first [assumption | eassumption]
  | |- unpoisoned _ _ _ => first [assumption | eassumption]
  | |- wr_at _ _ _ _ => first [assumption | eassumption]
  | |- app_blk _ _ => first [assumption | eassumption]
  | |- Forall _ _ => first [assumption | eassumption]
  | |- _ = Z_to_bv 64 _ => first [reflexivity | assumption | symmetry; assumption]
  | |- rng _ _ _ => first [ assumption | match goal with H : rng _ _ _ |- _ => eapply rng_sub'; [exact H | unfold KHIGH, sf_hide in *; lia] end ]
  | |- _ => unfold KHIGH, sf_hide in *; first [assumption | lia]
  end.

(* [comment removed for export] *)
Notation rt_real_fwrite m := (rw_cells asegs m 0xa7600 [C8 (Z_to_bv 64 0x9afac)]).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition fwrite_i_mid (ra sp gp tp s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 x14 x15 x16 x17 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x4696c) (Z_to_bv 64 (bv_unsigned sp - 2128)) gp tp t0 t1 t2
                  sp a1 a0 a1 a2 a3 x14 x15 x16 x17
                  a0 a3 a2 (Z_to_bv 64 1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x9afac) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2144, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp - 2128) /\ stk asegs m' (bv_unsigned sp - 2128) (bv_unsigned sp - 56)
    /\ rw_cells asegs m' (bv_unsigned sp - 56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rt_inited m'.

Section FWRITE_PRE.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 2144)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis INI : rt_inited m.
  Hypothesis RFW : rt_real_fwrite m.
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).

  #[using="MI ST LO KLO INI RFW RI RSTK"] Lemma fwrite_i_pre :
    evtF asegs RNG (fwrite_i_mid ra sp gp tp s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x46910) fc None m (seg_rom asegs)).
  Proof.
    pose proof (munch_refl [(bv_unsigned sp + -2144, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption). unfold KHIGH in KLO.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2144) 2144) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof MI as MIc. pose proof ST as ST0. pose proof INI as INIc. pose proof RFW as RFWc.
    change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in INI; change (?P) with (sf_hide P) in RFW.
    carve_frame 56%nat ST0.
    destruct (stk_split _ _ lo (bv_unsigned sp + -2128) _ ST0 ltac:(lia)) as [ST1 STM]. clear ST0.
    do 14 zstep. zstep.
    call_sp tryinit_spec. all: iprem.
    do 7 zstep. zstep.
    apply evtF_done. unfold fwrite_i_mid.
    replace (bv_unsigned sp - 2128)%Z with (bv_unsigned sp + -2128)%Z by lia.
    replace (bv_unsigned sp - 56)%Z with (bv_unsigned sp + -56)%Z by lia.
    replace (bv_unsigned sp - 2144)%Z with (bv_unsigned sp + -2144)%Z by lia.
    do 12 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption.
  Qed.
End FWRITE_PRE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fwrite_i_post_post (sp gp tp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (rav s0v s1v s2v s3v s4v s5v : word) (res lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 res) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc rav) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2208, bv_unsigned sp - 2128)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Section FWRITE_POST.
  Variables (RNG : footprint)
            (x1 sp gp tp t0 t1 t2 x9 a1 a2 a3 a4 a5 a6 a7 p x19 x20 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (rav s0v s1v s2v s3v s4v s5v : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo res size N : Z) (RLO RHI : Z).
  Notation P := (bv_unsigned p).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp - 2128).
  Hypothesis STM : stk asegs m (bv_unsigned sp - 2128) (bv_unsigned sp - 56).
  Hypothesis FR : rw_cells asegs m (bv_unsigned sp - 56) [C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].
  Hypothesis LO : (lo <= bv_unsigned sp - 2208)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis LAY : rt_layout m.
  Hypothesis X9 : x9 = Z_to_bv 64 size.
  Hypothesis HN : (res * size)%Z = N.
  Hypothesis RES : (0 <= res < 2^64 /\ 1 <= size /\ 0 <= N <= 2^40)%Z.
  Hypothesis APP : app_blk P (P + N).
  Hypothesis UNP : unpoisoned m P (P + N).
  Hypothesis R1 : (RLO <= P /\ P + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z.
  Hypothesis WR1 : wr_at asegs m (shad RLO) (shad RHI - shad RLO).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RSH1 : rng RNG (shad RLO) (shad RHI - shad RLO).

  Notation POST := (fwrite_i_post_post sp gp tp s6 s7 s8 s9 s10 s11 F fc rav s0v s1v s2v s3v s4v s5v res lo m).

  Definition INV (mc : word -> option byte) : Prop :=
    rw_cells asegs mc (bv_unsigned sp + -56) [C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]
    /\ stk asegs mc lo (bv_unsigned sp + -2128) /\ stk asegs mc (bv_unsigned sp + -2128) (bv_unsigned sp + -56)
    /\ munch [(bv_unsigned sp + -2208, bv_unsigned sp + -2128)]%Z m mc /\ wmono asegs m mc /\ mem_inv asegs mc
    /\ rt_got mc /\ rt_shbase mc /\ rt_layout mc
    /\ unpoisoned mc P (P + N) /\ wr_at asegs mc (shad RLO) (shad RHI - shad RLO).

  Definition BND : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2208 /\ KHIGH <= lo /\ bv_unsigned sp < 2^64 /\ 0 <= N /\ N <= 2^40 /\ 0 <= res < 2^64
     /\ 0 <= P /\ P + N + 8 <= KEND
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad P /\ shad (P + N - 1) + 1 <= shad RHI /\ shad RHI <= KHIGH
     /\ 0 <= Z.shiftr P 3 < 2^44 /\ -1 <= Z.shiftr (P + N + -1) 3 < 2^44
     /\ shad RLO mod 8 = 0 /\ shad RHI mod 8 = 0
     /\ RLO <= P /\ P + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0)%Z.
  #[using="m size ST LO KLO HN RES APP R1"] Lemma BND_ok : BND.
  Proof.
    unfold BND. destruct ST as (L0 & _). destruct APP as [LES AS]. unfold KLOW, KHIGH, KEND in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    pose proof (bv_unsigned_in_range 64 p) as PR. unfold bv_modulus in PR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in PR.
    rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF.
    Z.div_mod_to_equations. lia.
  Qed.
  Ltac acc_facts B ::= pose proof BND_ok as B; unfold BND, KHIGH, KEND in B.

  Definition BL : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2208 /\ 17594333495296 <= lo /\ bv_unsigned sp < 2^64 /\ 0 <= N /\ N <= 2^40 /\ 0 <= res < 2^64
     /\ 0 <= P /\ P + N + 8 <= 2^47
     /\ 0 <= Z.shiftr P 3 < 2^44 /\ -1 <= Z.shiftr (P + N + -1) 3 < 2^44
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad P /\ shad (P + N - 1) + 1 <= shad RHI /\ shad RHI <= 17594333495296)%Z.
  #[using="m size ST LO KLO HN RES APP R1"] Lemma BL_ok : BL. Proof. pose proof BND_ok as B. unfold BND, KHIGH, KEND in B. unfold BL. lia. Qed.

  Ltac inv_open H := destruct H as (FR1 & ST1 & STM1 & MU1 & WM1 & MI1 & GOT1 & SHB1 & LAY1 & UNP1 & WR11).
  Ltac prep IV :=
    pose proof IV as IV0; inv_open IV;
    let B := fresh "BL" in pose proof BL_ok as B; unfold BL in B;
    assert (RSTK' : rng RNG (bv_unsigned sp + -2208) 2208) by (eapply rng_sub'; [exact RSTK| lia]);
    change (?P) with (sf_hide P) in R1; change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO;
    change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in STM;
    change (?P) with (sf_hide P) in FR; change (?P) with (sf_hide P) in GOT; change (?P) with (sf_hide P) in SHB;
    change (?P) with (sf_hide P) in LAY; change (?P) with (sf_hide P) in UNP; change (?P) with (sf_hide P) in WR1.

  #[using="res size ST LO KLO HN RES APP UNP R1 WR1"] Lemma inv_of : forall mc,
    rw_cells asegs mc (bv_unsigned sp + -56) [C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
    stk asegs mc lo (bv_unsigned sp + -2128) -> stk asegs mc (bv_unsigned sp + -2128) (bv_unsigned sp + -56) ->
    munch [(bv_unsigned sp + -2208, bv_unsigned sp + -2128)]%Z m mc -> wmono asegs m mc -> mem_inv asegs mc ->
    rt_got mc -> rt_shbase mc -> rt_layout mc -> INV mc.
  Proof.
    intros mc FR1 ST1 STM1 MU1 WM1 MI1 G1 G2 G3. pose proof BND_ok as B. unfold BND, KHIGH, KEND in B.
    repeat (split; [assumption|]).
    assert (SS : (shad (P + N - 1) + 1 <= 17594333495296)%Z) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
    split. { eapply unpoisoned_munch; [exact UNP | exact MU1 |]. cbn [disjoint_from]. lia. }
    eapply wr_at_transport; eassumption.
  Qed.

  Notation FWR pc x10 x11 x12 x13 x14 x15 mc :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2 sp (Z_to_bv 64 N) x10 x11 x12 x13 x14 x15 a6 a7
             p x19 (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mc (seg_rom asegs)) (only parsing).

  (* [comment removed for export] *)
  #[using="size ST LO KLO HN RES APP R1 RSTK"] Lemma LX : forall mc x1' x5 x6 x7 x9' x11 x12 x13 x14 x15 x16 x17 x20' x21' x28 x29 x30 x31, INV mc ->
    evtF asegs RNG POST
      (MS (mkR x1' (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp x9' (Z_to_bv 64 res) x11 x12 x13 x14 x15 x16 x17
               p x19 x20' x21' s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x469d0) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. prep IV.
    do 10 zstep.
    pose proof (stk_merge _ _ _ _ _ ST1 STM1 ltac:(lia)) as SK.
    pose proof (stk_release _ _ _ _ _ SK FR1 ltac:(lia)) as SK2. cbn [cells_size csize Nat.add] in SK2.
    replace (bv_unsigned sp + -56 + Z.of_nat 56)%Z with (bv_unsigned sp) in SK2 by lia.
    apply evtF_done. unfold fwrite_i_post_post.
    replace (bv_unsigned sp - 2208)%Z with (bv_unsigned sp + -2208)%Z by lia.
    replace (bv_unsigned sp - 2128)%Z with (bv_unsigned sp + -2128)%Z by lia.
    do 15 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="size ST LO KLO HN RES APP R1 RSTK RSH1"] Lemma LL : forall mc (k : nat) (c : Z) x14 x15,
    INV mc -> (1 <= N <= 64)%Z -> Z.to_nat (shad (P + N - 1) - c) = k -> (shad P <= c < shad (P + N - 1))%Z ->
    evtF asegs RNG POST (FWR 0x46a94 (Z_to_bv 64 res) (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (P + N + -1) 3)) (Z_to_bv 64 0) x14 x15 mc).
  Proof.
    intros mc k c x14 x15 IV N1 Hk Hc. prep IV.
    revert c x14 Hk Hc. induction k as [|k IH]; intros c x14 Hk Hc; [exfalso; lia|].
    assert (SL : (shad (P + N - 1) = 2147450880 + Z.shiftr (P + N + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd asegs mc P (P + N) c UNP1 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K1; zify_cond K1.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LX; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="size ST LO KLO HN RES APP R1 RSTK RSH1"] Lemma LE : forall mc x14 x15, INV mc -> (1 <= N <= 64)%Z ->
    evtF asegs RNG POST (FWR 0x46a78 (Z_to_bv 64 res) (Z_to_bv 64 (2147450880 + Z.shiftr P 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (P + N + -1) 3))
                             (Z_to_bv 64 (P + N + -1)) x14 x15 mc).
  Proof.
    intros mc x14 x15 IV N1. prep IV.
    destruct (unpoisoned_check_rd asegs mc P (P + N) (P + N + -1) 1 UNP1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((P + N + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LX; eassumption.
    - eapply (LL mc); [exact IV0 | exact N1 | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      Z.div_mod_to_equations; lia.
  Qed.

  #[using="size N RLO RHI MI ST STM FR LO KLO GOT SHB LAY X9 HN RES APP UNP R1 WR1 RI RSTK RSH1"] Lemma fwrite_i_post :
    evtF asegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2 sp x9 (Z_to_bv 64 res) a1 a2 a3 a4 a5 a6 a7
               p x19 x20 (Z_to_bv 64 1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x4696c) fc None m (seg_rom asegs)).
  Proof.
    assert (IV : INV m).
    { pose proof ST as ST'. pose proof STM as STM'. pose proof FR as FR'.
      replace (bv_unsigned sp - 2128)%Z with (bv_unsigned sp + -2128)%Z in ST', STM' by lia.
      replace (bv_unsigned sp - 56)%Z with (bv_unsigned sp + -56)%Z in STM', FR' by lia.
      repeat (split; [assumption|]); try assumption. all: try apply munch_refl; try apply wmono_refl.
      split; [apply munch_refl|]. split; [apply wmono_refl|]. repeat (split; [assumption|]). assumption. }
    prep IV. subst x9.
    zstep. if_cases K0; zify_cond K0. { exfalso. clear -K0. cbv in K0. lia. } clear K0.
    zstep. if_cases KR; zify_cond KR.
    { (* [comment removed for export] *) eapply LX; eassumption. }
    assert (NPOS : (1 <= N)%Z) by (clear -KR RES HN BL0; nia).
    zstep. rewrite HN.
    zstep. rewrite zb_lxor_ones by lia. zstep. zstep. zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1 BL0. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      assert (N1 : (64 < N)%Z).
      { change 18446744073709551615%Z with (Z.ones 64) in K2. rewrite ?Z.land_ones in K2 by lia. change (2 ^ 64)%Z with 18446744073709551616%Z in K2.
        clear - K2 BL0 NPOS. Z.div_mod_to_equations. lia. }
      zstep. if_cases K3; zify_cond K3. 2:{ exfalso. clear -K3 BL0 N1. lia. }
      zstep. zstep. zstep. zstep.
      unfold sf_hide in LO.
      call_sp rip_spec;
        [ exact MI1 | exact ST1 | lia | unfold KHIGH; lia | exact GOT1 | exact SHB1 | exact LAY1
        | zsimp; exact APP | zsimp; exact UNP1
        | zsimp; pose proof BND_ok as B9; unfold BND in B9; lia
        | eapply rng_sub'; [exact RSTK | lia] | ].
      zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
      zstep. zstep.
      eapply LX. eapply inv_of; eassumption.
    - (* [comment removed for export] *)
      assert (N1 : (1 <= N <= 64)%Z).
      { change 18446744073709551615%Z with (Z.ones 64) in K2. rewrite ?Z.land_ones in K2 by lia. change (2 ^ 64)%Z with 18446744073709551616%Z in K2.
        clear - K2 BL0 NPOS. Z.div_mod_to_equations. lia. }
      do 11 zstep.
      change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
      unfold sf_hide in R1.
      destruct (shadow_probe8 asegs m RLO RHI P WR11 ltac:(apply no_image_asan; pose proof BND_ok as B9; unfold BND in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w1 P1].
      destruct (shadow_probe8 asegs m RLO RHI (P + N + -1) WR11 ltac:(apply no_image_asan; pose proof BND_ok as B9; unfold BND in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w2 P2].
      unfold ASHOFF in P1, P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply LE; eassumption.
      + eapply LX; eassumption.
  Qed.
End FWRITE_POST.
End CANSEC1.
End TwB.
End I_fwrite.
