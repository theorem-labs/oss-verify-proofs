(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import StrFun Stdio_pure.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ZBridge.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg RtCells ShadowTac F_irt F_rip.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

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
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. Local Ltac2 Set LiaHints.tbl := fun () => "0010<9530091496.3000004S2Hz".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma bytes_eq_of_unsigned : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
induction l1 as [|b1 l1 IH]; intros [|b2 l2] H; cbn in H; try discriminate; [reflexivity|].
injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.
#[using="Type"] Lemma rw_cells_recell_mid : forall segs m A pre mid post mid',
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
Section CANSEC5. Context {rc : runConstT}.
Definition S_FLAGS : Z := 0x152a7. Definition B_FLAGS : list byte := [Z_to_bv 8 39; Z_to_bv 8 45; Z_to_bv 8 43; Z_to_bv 8 32; Z_to_bv 8 35; Z_to_bv 8 48].
Definition S_JZT : Z := 0x1b2ff. Definition B_JZT : list byte := [Z_to_bv 8 106; Z_to_bv 8 122; Z_to_bv 8 116; Z_to_bv 8 76; Z_to_bv 8 113].
Definition S_CCSS : Z := 0x140b3. Definition B_CCSS : list byte := [Z_to_bv 8 99; Z_to_bv 8 67; Z_to_bv 8 115; Z_to_bv 8 83].
Definition S_AEFG : Z := 0x1635f. Definition B_AEFG : list byte := [Z_to_bv 8 97; Z_to_bv 8 65; Z_to_bv 8 101; Z_to_bv 8 69; Z_to_bv 8 102; Z_to_bv 8 70; Z_to_bv 8 103; Z_to_bv 8 71].
Definition S_DIOUX : Z := 0x1c3cf. Definition B_DIOUX : list byte := [Z_to_bv 8 100; Z_to_bv 8 105; Z_to_bv 8 111; Z_to_bv 8 117; Z_to_bv 8 120; Z_to_bv 8 88; Z_to_bv 8 110].
Definition S_CS : Z := 0x19a4b. Definition B_CS : list byte := [Z_to_bv 8 67; Z_to_bv 8 83].
Definition S_CSB : Z := 0x107de. Definition B_CSB : list byte := [Z_to_bv 8 99; Z_to_bv 8 115; Z_to_bv 8 91].
Definition S_SS : Z := 0x139f1. Definition B_SS : list byte := [Z_to_bv 8 115; Z_to_bv 8 83].
End CANSEC5.
Ltac img_str A B :=
intros m MI; apply ro_bytes_at; [exact MI| unfold A; lia| unfold A, B; cbn [length app]; lia|];
apply ro_bytes_b_sound; vm_compute; reflexivity.
Section CANSEC6. Context {rc : runConstT}.
#[using="Type"] Lemma flags_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m S_FLAGS (B_FLAGS ++ Z_to_bv 8 0 :: []). Proof. img_str S_FLAGS B_FLAGS. Qed.
#[using="Type"] Lemma jzt_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m S_JZT (B_JZT ++ Z_to_bv 8 0 :: []). Proof. img_str S_JZT B_JZT. Qed.
#[using="Type"] Lemma ccss_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m S_CCSS (B_CCSS ++ Z_to_bv 8 0 :: []). Proof. img_str S_CCSS B_CCSS. Qed.
#[using="Type"] Lemma aefg_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m S_AEFG (B_AEFG ++ Z_to_bv 8 0 :: []). Proof. img_str S_AEFG B_AEFG. Qed.
#[using="Type"] Lemma dioux_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m S_DIOUX (B_DIOUX ++ Z_to_bv 8 0 :: []). Proof. img_str S_DIOUX B_DIOUX. Qed.
#[using="Type"] Lemma cs_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m S_CS (B_CS ++ Z_to_bv 8 0 :: []). Proof. img_str S_CS B_CS. Qed.
#[using="Type"] Lemma csb_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m S_CSB (B_CSB ++ Z_to_bv 8 0 :: []). Proof. img_str S_CSB B_CSB. Qed.
#[using="Type"] Lemma ss_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m S_SS (B_SS ++ Z_to_bv 8 0 :: []). Proof. img_str S_SS B_SS. Qed.
End CANSEC6.
Ltac noz_tac :=
apply Forall_forall; let b := fresh "b" in let Hb := fresh "Hb" in intros b Hb;
repeat (destruct Hb as [<-|Hb]; [cbv; discriminate|]); destruct Hb.
Section CANSEC7. Context {rc : runConstT}.
#[using="Type"] Lemma flags_noz : Forall (fun b : byte => bv_unsigned b <> 0%Z) B_FLAGS. Proof. noz_tac. Qed.
#[using="Type"] Lemma jzt_noz : Forall (fun b : byte => bv_unsigned b <> 0%Z) B_JZT. Proof. noz_tac. Qed.
#[using="Type"] Lemma ccss_noz : Forall (fun b : byte => bv_unsigned b <> 0%Z) B_CCSS. Proof. noz_tac. Qed.
#[using="Type"] Lemma aefg_noz : Forall (fun b : byte => bv_unsigned b <> 0%Z) B_AEFG. Proof. noz_tac. Qed.
#[using="Type"] Lemma cs_noz : Forall (fun b : byte => bv_unsigned b <> 0%Z) B_CS. Proof. noz_tac. Qed.
#[using="Type"] Lemma csb_noz : Forall (fun b : byte => bv_unsigned b <> 0%Z) B_CSB. Proof. noz_tac. Qed.
#[using="Type"] Lemma ss_noz : Forall (fun b : byte => bv_unsigned b <> 0%Z) B_SS. Proof. noz_tac. Qed.
#[using="Type"] Lemma dioux_noz : Forall (fun b : byte => bv_unsigned b <> 0%Z) B_DIOUX. Proof. noz_tac. Qed.
Definition fgvs_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 4) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo (bv_unsigned sp).
#[using="Type"] Lemma fgvs_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (c : Z) (idx : nat) (LM : Z),
mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 32)%Z ->
find_byte c B_DIOUX = Some idx -> (0 < c < 256)%Z ->
rw_cells bsegs m LM [C1 (Z_to_bv 8 0)] -> (bv_unsigned sp <= LM)%Z -> (LM < 2^64)%Z ->
rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng RNG LM 1 ->
evtF bsegs RNG (fgvs_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 LM) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x482ec) fc None m (seg_rom bsegs)).
Proof.
intros until LM. intros MI ST LO HF CR LMC SEP LMH RSTK RI RLM.
pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
Local Ltac2 Set LiaHints.tbl := fun () => "00U0>15417378609.5915418079120.5617357017925.5621746761136.6521910425884.6221910425884.6923871115581.6025178090980.6325178090987.7027764935472.6433490928028.6433490928028.7134290115814.5534878709672.5235497698861.6039939624357.6040334400613.6440334400619.7041564619544.5943057221392.5345399972529.5945841261573.7054730400711.6457019737480.5959308628304.6059308628433.1 59308628566.1 66094432284.6566094432284.716641875813.68 6641875815.61 7036877028.63 7036877035.70 9701819056.62 9942992759.64 9942992759.71 9955694253.69 00000100200300400500600:00;00<00=00>00?00@00D00H00L00M00N00O00S00T00U00V00W00^00b00f00g00h00i00j00k00l00m00n00o010SSSSSSS2HFSSSSSSS2LOS2HFS2LOSSSS2LOSSSSS2HF2K1S2K2S2K3SSSSSSSSSS".
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
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition printf_common_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [(bv_unsigned sp - 2320, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo (bv_unsigned sp).
End CANSEC7.
