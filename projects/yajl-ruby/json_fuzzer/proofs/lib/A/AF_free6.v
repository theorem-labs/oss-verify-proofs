(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AF_place AF_kit AF_kit2 AF_qkit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require ZBridge Arr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac lia ::=
  first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTuning.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac slia ::= first [ exact I | dlia | split; [dlia | exact I] ].
Local Ltac flia ::= first [ assumption | lia ].
Local Definition carry_skip (P : Prop) := P.
Local Ltac skipH H := lazymatch type of H with ?TS => change TS with (carry_skip TS) in H end.

Local Ltac dlia1 := dlia.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac incl_leaves xq Hq :=
  repeat match type of Hq with _ /\ _ => let Q := fresh "Q" in destruct Hq as [Q Hq] end;
  repeat match goal with |- _ /\ _ => split end; try exact I;
  let C := fresh "C" in intros C;
  first [ match goal with Q : ~ (_ <= xq < _) |- _ => apply Q; LiaA.lia_probe end
        | match goal with D : _ \/ _ |- _ => destruct D as [XD|XD]; match goal with Q : ~ (_ <= xq < _) |- _ => apply Q; LiaA.lia_probe end end ].
(* [comment removed for export] *)
Local Ltac solve_covers ::=
  let lo := fresh "lo" in let hi := fresh "hi" in let Hin := fresh "Hin" in
  intros lo hi Hin; cbn [In app] in Hin;
  repeat match type of Hin with
  | _ \/ _ => destruct Hin as [Hin|Hin]; [injection Hin as <- <-; do 2 eexists; split; [cover_member| cbn [fst snd b_addr]; LiaA.lia_probe] |]
  | _ = _ => injection Hin as <- <-; do 2 eexists; split; [cover_member| cbn [fst snd b_addr]; LiaA.lia_probe]
  | False => contradiction
  end.
Local Ltac carry_rw H MU WM ::= eapply rw_cells_transport in H; [| exact MU| exact WM| cbn; repeat match goal with |- _ /\ _ => split end; first [exact I | dlia1]].
Local Ltac carry_all mc m' MUc WMc ::=
  repeat match goal with
  | H : rw_cells asegs mc _ _ |- _ => first [ carry_rw H MUc WMc | skipH H ]
  | H : bytes_at asegs mc _ _ |- _ => first [ eapply bytes_at_transport in H; [| exact MUc| cbn [disjoint_from length]; rewrite ?repeat_length, ?length_le8, ?length_le4; lia] | skipH H ]
  | H : stk asegs mc _ _ |- _ => first [ eapply stk_transport in H; [| exact MUc| exact WMc| intros; left; cbn; lia] | skipH H ]
  | H : wr_at asegs mc _ _ |- _ => first [ eapply wr_at_transport in H; [| exact WMc] | skipH H ]
  | H : u8arr asegs mc _ _ |- _ => first [ eapply u8arr_transport in H; [| exact MUc| exact WMc| cbn [disjoint_from length]; rewrite ?repeat_length; lia] | skipH H ]
  | H : u64arr asegs mc _ _ |- _ => first [ eapply u64arr_transport in H; [| exact MUc| exact WMc| cbn [disjoint_from length]; lia] | skipH H ]
  | H : u32arr asegs mc _ _ |- _ => first [ eapply u32arr_transport in H; [| exact MUc| exact WMc| cbn [disjoint_from length]; lia] | skipH H ]
  | H : munch ?W ?ma mc |- _ =>
      let H2 := fresh in
      first [ assert (H2 : munch W ma m')
          by (eapply munch_trans; [exact H| eapply munch_weaken; [| exact MUc];
              first [ sub_fp_fast | let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *; decompose [and] Hq; clear Hq; repeat match goal with |- _ /\ _ => split end; try exact I; match goal with O : ~ (_ <= xq < _)%Z |- _ => clear -O; let R := fresh in intros R; apply O; lia end ]]);
        clear H; rename H2 into H | skipH H ]
  | H : wmono asegs ?ma mc |- _ =>
      let H2 := fresh in
      assert (H2 : wmono asegs ma m') by (eapply wmono_trans; [exact H| exact WMc]);
      clear H; rename H2 into H
  end;
  repeat match goal with H : carry_skip _ |- _ => unfold carry_skip in H end.
Local Ltac solve_dj ::=
  cbn [disjoint_from cells_size csize length Nat.add Nat.mul app];
  rewrite ?repeat_length, ?length_le8, ?length_le4, ?upd_length;
  repeat first [ exact I
               | split; [dlia1|]
               | (eapply disjoint_from_down; [eassumption| solve_sep1])
               | dlia1 ].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma shiftr1_double : forall h, 0 <= h -> Z.shiftr (2 * h) 1 = h.
Proof. aceil. intros h Hh. rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity. Qed.
Lemma shl32_shr32_small : forall x, 0 <= x < 2^32 -> Z.shiftr (Z.shiftl x 32 mod 2^64) 32 = x.
Proof. aceil.
  intros x Hx. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. rewrite Z.mod_small by lia.
  rewrite Z.div_mul by lia. reflexivity.
Qed.
Lemma shl32_shr30_small : forall x, 0 <= x < 2^32 -> Z.shiftr (Z.shiftl x 32 mod 2^64) 30 = 4 * x.
Proof. aceil.
  intros x Hx. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. rewrite Z.mod_small by lia.
  change (2^32) with (4 * 2^30). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.

Section LDC.
Variable P : acc -> Prop.
Variables (gp tp s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (usp lo : Z) (CA SB c p : Z).
Notation INST := 0xaa518.
Definition PCB : Z := CA + 80 * c.                     (* [comment removed for export] *)
Definition xc : Z := (p - SB - c * 2^32) / 16.         (* [comment removed for export] *)

Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO : lo <= usp - 48.
Hypothesis SPH : usp <= 2^47.
Hypothesis SPA : usp mod 16 = 0.
Hypothesis HSB : 0x603000 <= SB /\ SB mod 4096 = 0 /\ SB + kSpaceSize + 4096 <= alloc_ceiling.
Hypothesis HC : 1 <= c <= kLargestClassID.
Hypothesis HCA : (0x1000 <= CA /\ (CA + 2584 <= 0x10000 \/ 0x603000 <= CA)) /\ CA + 2584 <= alloc_ceiling /\ CA mod 8 = 0.   (* [comment removed for export] *)
Hypothesis HCASB : CA + 2584 <= SB \/ SB + kSpaceSize + 4096 <= CA.
Hypothesis HP : SB + c * 2^32 <= p /\ p + 16 <= SB + c * 2^32 + 0xE0000000.
Hypothesis PSTK : forall a k, lo <= a -> a + Z.of_nat k <= usp -> P (Z_to_bv 64 a, k).
Hypothesis PDAT : forall a k, 0xa4000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PCA : forall a k, CA <= a -> a + Z.of_nat k <= CA + 2584 -> P (Z_to_bv 64 a, k).

(* [comment removed for export] *)
Lemma ldc_tail : forall mx (rav s0v s1v s2v s3v s4v : word) (rax s1x s2x s3x s4x t0x t1x t2x a5x a6x a7x : word)
    (cnt alloc : Z) (maxc csz : word) (ws : list word) (Q : machine_state -> Prop),
  mem_inv asegs mx -> stk asegs mx lo (usp - 48) ->
  rw_cells asegs mx (usp - 48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rw_cells asegs mx 0xaa538 [C8 (Z_to_bv 64 SB)] ->
  rw_cells asegs mx PCB [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr asegs mx (PCB + 16) ws -> length ws = 16%nat -> 0 <= cnt < 16 ->
  rw_cells asegs mx (CA + 2576) [C8 (Z_to_bv 64 alloc)] ->
  (forall m' (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' : word),
     mem_inv asegs m' -> stk asegs m' lo usp ->
     munch [(usp - 48, usp); (PCB, PCB + 4); (PCB + 16 + 4 * cnt, PCB + 16 + 4 * cnt + 4); (CA + 2576, CA + 2584)] mx m' -> wmono asegs mx m' ->
     rw_cells asegs m' 0xaa538 [C8 (Z_to_bv 64 SB)] ->
     rw_cells asegs m' PCB [C4 (Z_to_bv 64 (cnt + 1)); C4 maxc; C8 csz] ->
     u32arr asegs m' (PCB + 16) (upd ws (Z.to_nat cnt) (Z_to_bv 64 xc)) ->
     rw_cells asegs m' (CA + 2576) [C8 (Z_to_bv 64 (alloc - bv_unsigned csz))] ->
     evtA asegs P Q (MS (mkR rav (Z_to_bv 64 usp) gp tp t0' t1' t2' s0v s1v a0' a1' a2' a3' a4' a5' a6' a7'
                             s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc rav) fc None m' (seg_rom asegs))) ->
  evtA asegs P Q (MS (mkR rax (Z_to_bv 64 (usp + -48)) gp tp t0x t1x t2x (Z_to_bv 64 PCB) s1x (Z_to_bv 64 CA) (Z_to_bv 64 INST) (Z_to_bv 64 c) (Z_to_bv 64 p) (Z_to_bv 64 cnt) a5x a6x a7x
                          s2x s3x s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x352a0) fc None mx (seg_rom asegs)).
Proof. aceil.
  intros until Q. intros MI SK FR ISB PC ARR LEN CNT CST CONT.
  pose proof LOC as LOC0. pose proof HSB as HSB0. pose proof HCA as HCA0. pose proof HCASB as HCASBpin. aceil.
  unfold kSpaceSize in HSB, HCASB. unfold kLargestClassID in HC.
  pose proof (class_size_mod c ltac:(lia)) as [_ CSZ].
  assert (HX : 0 <= xc < 2^32) by (unfold xc; clear -CEILB HP; Z.div_mod_to_equations; lia).
  assert (MU : munch [(usp - 48, usp); (PCB, PCB + 4); (PCB + 16 + 4 * cnt, PCB + 16 + 4 * cnt + 4); (CA + 2576, CA + 2584)] mx mx) by apply munch_refl.
  assert (WM : wmono asegs mx mx) by apply wmono_refl.
  unfold PCB in *. set (PCBv := CA + 80 * c) in *.
  assert (HPCB : PCBv = CA + 80 * c) by reflexivity. clearbody PCBv.
  replace (usp - 48) with (usp + -48) in FR, SK by lia.
  pose proof (bv_unsigned_in_range _ csz) as CSR. change (bv_modulus 64) with (2^64) in CSR.
  zstepA.                         (* [comment removed for export] *)
  do 2 zstepA.                    (* [comment removed for export] *)
  do 2 zstepA.                    (* [comment removed for export] *)
  zstepA.                         (* [comment removed for export] *)
  zstepA.                         (* [comment removed for export] *)
  do 3 zstepA.                    (* [comment removed for export] *)
  replace ((cnt ≪ 32 mod 18446744073709551616) ≫ 30) with (4 * cnt)
    by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by (clear -CEILB CNT; lia); clear -CEILB CNT; Z.div_mod_to_equations; lia).
  zstepA.                         (* [comment removed for export] *)
  zstepA.                         (* [comment removed for export] *)
  match goal with |- context [Z.shiftr ?e 4] => replace (Z.shiftr e 4) with xc
      by (unfold xc; rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia; rewrite ?Z.mod_small by (clear -CEILB HP HSB HC; lia); clear -CEILB HP HSB HC; Z.div_mod_to_equations; lia) end.
  cstep.                          (* [comment removed for export] *)
  match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?m0 _) =>
    pose proof (Arr.u32arr_store_ok asegs m0 (PCBv + 16) ws cnt (Z_to_bv 64 (PCBv + 4 * cnt + 16)) ARR ltac:(rewrite LEN; clear -CEILB CNT; lia)
                  ltac:(unfold wa; f_equal; clear; lia)) as SOK;
    pose proof (Arr.u32arr_write asegs m0 (PCBv + 16) ws cnt (Z_to_bv 64 xc) ARR ltac:(rewrite LEN; clear -CEILB CNT; lia)) as ARR';
    replace (PCBv + 16 + 4 * cnt) with (PCBv + 4 * cnt + 16) in ARR' by (clear; lia) end.
  stepA.                          (* [comment removed for export] *)
  all: lazymatch goal with |- P _ => apply PCA; clear -CEILB HC CNT; lia | _ => idtac end.
  clear ARR. store_done. rename ARR' into ARR.
  zstepA.                         (* [comment removed for export] *)
  assert (AL8 : (CA + 2576) mod 8 = 0) by (clear -CEILB HCA; Z.div_mod_to_equations; lia).
  zstepA.                         (* [comment removed for export] *)
  do 7 cstep.                     (* [comment removed for export] *)
  release_frame FR SK usp.
  cstep.                          (* [comment removed for export] *)
  eapply CONT; try eassumption.
  all: try (replace (usp - 48) with (usp + -48) by lia; assumption).
  all: change 18446744073709551616 with (2^64) in *; rewrite ?ZBridge.Z_to_bv_mod64 in *; try assumption.
Qed.

(* [comment removed for export] *)
Lemma ldc_push : forall mx (ra s0 s1 s2 s3 s4 t0 t1 t2 a4 a5 a6 a7 : word) (cnt maxc alloc : Z) (csz : word) (ws : list word)
    (Q : machine_state -> Prop),
  mem_inv asegs mx -> stk asegs mx lo usp ->
  rw_cells asegs mx 0xaa538 [C8 (Z_to_bv 64 SB)] ->
  rw_cells asegs mx PCB [C4 (Z_to_bv 64 cnt); C4 (Z_to_bv 64 maxc); C8 csz] ->
  1 <= maxc <= 16 -> 0 <= cnt < maxc ->
  u32arr asegs mx (PCB + 16) ws -> length ws = 16%nat ->
  rw_cells asegs mx (CA + 2576) [C8 (Z_to_bv 64 alloc)] ->
  (forall m' (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' : word),
     mem_inv asegs m' -> stk asegs m' lo usp ->
     munch [(usp - 48, usp); (PCB, PCB + 4); (PCB + 16 + 4 * cnt, PCB + 16 + 4 * cnt + 4); (CA + 2576, CA + 2584)] mx m' -> wmono asegs mx m' ->
     rw_cells asegs m' 0xaa538 [C8 (Z_to_bv 64 SB)] ->
     rw_cells asegs m' PCB [C4 (Z_to_bv 64 (cnt + 1)); C4 (Z_to_bv 64 maxc); C8 csz] ->
     u32arr asegs m' (PCB + 16) (upd ws (Z.to_nat cnt) (Z_to_bv 64 xc)) ->
     rw_cells asegs m' (CA + 2576) [C8 (Z_to_bv 64 (alloc - bv_unsigned csz))] ->
     evtA asegs P Q (MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  evtA asegs P Q (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 CA) (Z_to_bv 64 INST) (Z_to_bv 64 c) (Z_to_bv 64 p) a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x3525c) fc None mx (seg_rom asegs)).
Proof. aceil.
  intros until Q. intros MI SK ISB PC MAXC CNT ARR LEN CST CONT.
  pose proof LOC as LOC0. pose proof HSB as HSB0. pose proof HCA as HCA0. aceil.
  unfold kSpaceSize in HSB, HCASB. pose proof HC as HC0. unfold kLargestClassID in HC.
  assert (MU : munch [(usp - 48, usp); (PCB, PCB + 4); (PCB + 16 + 4 * cnt, PCB + 16 + 4 * cnt + 4); (CA + 2576, CA + 2584)] mx mx) by apply munch_refl.
  assert (WM : wmono asegs mx mx) by apply wmono_refl.
  pose proof (unsigned_lit usp ltac:(lia)) as USP.
  unfold PCB in *. set (PCBv := CA + 80 * c) in *. assert (HPCB : PCBv = CA + 80 * c) by reflexivity. clearbody PCBv.
  carve_frame 48%nat SK.
  do 7 cstep.                     (* [comment removed for export] *)
  zstepA. if_cases K0; zify_cond K0; [exfalso; revert K0; rewrite ?unsigned_lit by lia; clear -CEILB HC; intros K0; lia|].   (* [comment removed for export] *)
  zstepA. zstepA. if_cases K1; zify_cond K1; [exfalso; revert K1; rewrite ?unsigned_lit by lia; clear -CEILB HC; intros K1; lia|]. (* [comment removed for export] *)
  do 3 zstepA.                    (* [comment removed for export] *)
  rewrite ?(Z.mod_small (c * 80)) by (clear -CEILB HC; lia).
  replace (CA + c * 80) with PCBv by (clear -CEILB HPCB; lia).
  zstepA. rewrite (fsx32_small' maxc) by (clear -CEILB MAXC; lia).       (* [comment removed for export] *)
  zstepA. if_cases K2; zify_cond K2; [exfalso; revert K2; rewrite ?unsigned_lit by lia; clear -CEILB MAXC; intros K2; lia|].  (* [comment removed for export] *)
  zstepA. rewrite (fsx32_small' cnt) by (clear -CEILB CNT MAXC; lia).    (* [comment removed for export] *)
  zstepA. if_cases K3; zify_cond K3; [exfalso; revert K3; rewrite ?unsigned_lit by lia; clear -CEILB CNT MAXC; intros K3; lia|].  (* [comment removed for export] *)
  subst PCBv.
  eapply ldc_tail; [exact MI| | | exact ISB| exact PC| exact ARR| exact LEN| clear -CEILB CNT MAXC; lia| exact CST|].
  - replace (usp - 48) with (usp + -48) by lia. exact SK.
  - replace (usp - 48) with (usp + -48) by lia. exact FR.
  - intros m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' MI' SK' MU' WM' ISB' PC' ARR' CST'. unfold PCB in *.
    eapply CONT; [exact MI'| exact SK'| | | exact ISB'| exact PC'| exact ARR'| exact CST'].
    + eapply munch_trans; [eapply munch_cover; [exact MU| solve_covers]| exact MU'].
    + eapply wmono_trans; [exact WM| exact WM'].
Qed.

(* [comment removed for export] *)
Definition ri_cells (mtx nf mfa au mu na nfr : Z) : list cell :=
  [C8 (Z_to_bv 64 mtx); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0);
   C4 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 3 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0];
   C8 (Z_to_bv 64 na); C8 (Z_to_bv 64 nfr);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

Variable RI : Z.
Hypothesis HRI : RI = SB + kSpaceSize.
Definition RIc : Z := RI + 128 * c.
Hypothesis PRIR : forall a k, RIc <= a -> a + Z.of_nat k <= RIc + 128 -> P (Z_to_bv 64 a, k).
Hypothesis LO2 : lo <= usp - 688.

(* [comment removed for export] *)
Definition drain_frames (m : mem) (ra s0 s1 s2 s3 s4 : word) (j1 j2 : list byte) : Prop :=
  rw_cells asegs m (usp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
  /\ rw_cells asegs m (usp + -112) [CB 8 j1; C8 (Z_to_bv 64 INST); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x3540c)]
  /\ rw_cells asegs m (usp + -240) [CB 16 j2; C8 (Z_to_bv 64 (RIc + 8)); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 (Z_to_bv 64 p);
                                    C8 (Z_to_bv 64 c); C8 (Z_to_bv 64 INST); C8 (Z_to_bv 64 CA); C8 (Z_to_bv 64 PCB); C8 (Z_to_bv 64 0x35654)].

(* [comment removed for export] *)
Definition rta_regs (ra t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 : word) (h nf : Z) : _ :=
  mkR ra (Z_to_bv 64 (usp + -240)) gp tp t0 t1 t2 (Z_to_bv 64 RIc) s1 a0 a1 (Z_to_bv 64 (SB + c * 4294967296)) a3 a4 a5 a6 a7
      (Z_to_bv 64 c) (Z_to_bv 64 (usp + -104)) (Z_to_bv 64 INST) (Z_to_bv 64 h) (Z_to_bv 64 (PCB + 4 * h + 16)) (Z_to_bv 64 (nf + h))
      (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 (SB + c * 4294967296 + 3758096384)) (Z_to_bv 64 1152921504607895551) (Z_to_bv 64 1152921504606846976) t3 t4 t5 t6.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ldc_drain_head : forall mx (ra s0 s1 s2 s3 s4 t0 t1 t2 a4 a5 a6 a7 : word) (h alloc nf mfa au mu na nfr : Z) (csz : word) (ws : list word)
    (Q : machine_state -> Prop),
  mem_inv asegs mx -> stk asegs mx lo usp ->
  rw_cells asegs mx 0xaa538 [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 RI)] ->
  rw_cells asegs mx PCB [C4 (Z_to_bv 64 (2 * h)); C4 (Z_to_bv 64 (2 * h)); C8 csz] ->
  1 <= h <= 8 ->
  u32arr asegs mx (PCB + 16) ws -> length ws = 16%nat ->
  rw_cells asegs mx (CA + 2576) [C8 (Z_to_bv 64 alloc)] ->
  rw_cells asegs mx RIc (ri_cells 0 nf mfa au mu na nfr) -> 0 <= nf < 2^40 ->
  (forall m' j1 j2,
     mem_inv asegs m' -> stk asegs m' lo (usp + -240) ->
     munch [(usp - 688, usp); (PCB, PCB + 4); (RIc, RIc + 8)] mx m' -> wmono asegs mx m' ->
     drain_frames m' ra s0 s1 s2 s3 s4 j1 j2 ->
     rw_cells asegs m' 0xaa538 [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 RI)] ->
     rw_cells asegs m' PCB [C4 (Z_to_bv 64 h); C4 (Z_to_bv 64 (2 * h)); C8 csz] ->
     u32arr asegs m' (PCB + 16) ws ->
     rw_cells asegs m' (CA + 2576) [C8 (Z_to_bv 64 alloc)] ->
     rw_cells asegs m' RIc (ri_cells 1152921504606846976 nf mfa au mu na nfr) ->
     evtA asegs P Q (MS (rta_regs (Z_to_bv 64 0x358f8) t0 t1 t2 (Z_to_bv 64 nf) (Z_to_bv 64 INST) (Z_to_bv 64 RIc) (Z_to_bv 64 (nf + h))
                               (Z_to_bv 64 0) (Z_to_bv 64 1152921504606846976) (Z_to_bv 64 0) (Z_to_bv 64 1500) h nf)
                        F (Z_to_bv 64 0x35abc) fc None m' (seg_rom asegs))) ->
  evtA asegs P Q (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 CA) (Z_to_bv 64 INST) (Z_to_bv 64 c) (Z_to_bv 64 p) a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x3525c) fc None mx (seg_rom asegs)).
Proof. aceil.
  intros until Q. intros MI SK INS PC HH ARR LEN CST RIC NF CONT. unfold ri_cells in RIC.
  pose proof LOC as LOC0. pose proof HSB as HSB0. pose proof HCA as HCA0. pose proof HCASB as HCASBpin. pose proof HRI as HRI0. aceil.
  unfold kSpaceSize in HSB, HCASB, HRI0. pose proof HC as HC0. unfold kLargestClassID in HC.
  assert (MU : munch [(usp - 688, usp); (PCB, PCB + 4); (RIc, RIc + 8)] mx mx) by apply munch_refl.
  assert (WM : wmono asegs mx mx) by apply wmono_refl.
  pose proof (unsigned_lit usp ltac:(lia)) as USP.
  unfold rta_regs, drain_frames in CONT. unfold PCB in *. set (PCBv := CA + 80 * c) in *. assert (HPCB : PCBv = CA + 80 * c) by reflexivity. clearbody PCBv.
  unfold RIc in *. set (RIv := RI + 128 * c) in *. assert (HRIv : RIv = RI + 128 * c) by reflexivity. clearbody RIv.
  carve_frame 48%nat SK.
  do 7 cstep.                     (* [comment removed for export] *)
  zstepA. if_cases K0; zify_cond K0; [exfalso; revert K0; rewrite ?unsigned_lit by lia; clear -CEILB HC; intros K0; lia|].   (* [comment removed for export] *)
  zstepA. zstepA. if_cases K1; zify_cond K1; [exfalso; revert K1; rewrite ?unsigned_lit by lia; clear -CEILB HC; intros K1; lia|]. (* [comment removed for export] *)
  do 3 zstepA.                    (* [comment removed for export] *)
  rewrite ?(Z.mod_small (c * 80)) by (clear -CEILB HC; lia).
  replace (CA + c * 80) with PCBv by (clear -CEILB HPCB; lia).
  zstepA. rewrite (fsx32_small' (2 * h)) by (clear -CEILB HH; lia).       (* [comment removed for export] *)
  zstepA. if_cases K2; zify_cond K2; [exfalso; revert K2; rewrite ?unsigned_lit by lia; clear -CEILB HH; intros K2; lia|].  (* [comment removed for export] *)
  zstepA. rewrite (fsx32_small' (2 * h)) by (clear -CEILB HH; lia).       (* [comment removed for export] *)
  zstepA. if_cases K3; zify_cond K3; [| exfalso; revert K3; rewrite ?unsigned_lit by lia; clear -CEILB HH; intros K3; lia].  (* [comment removed for export] *)
  do 7 cstep.                     (* [comment removed for export] *)
  cstep.                          (* [comment removed for export] *)
  (* [comment removed for export] *)
  carve_frame 64%nat SK.
  do 4 cstep.                     (* [comment removed for export] *)
  zstepA. rewrite (fsx32_small' (2 * h)) by (clear -CEILB HH; lia).       (* [comment removed for export] *)
  zstepA. rewrite ?fzx32_small' by (clear -CEILB HH; lia).                 (* [comment removed for export] *)
  do 4 cstep.                     (* [comment removed for export] *)
  do 3 zstepA.                    (* [comment removed for export] *)
  rewrite (shiftr1_double h) by (clear -CEILB HH; lia).
  rewrite (Z.mod_small (2 * h) 4294967296) by (clear -CEILB HH; lia).
  zstepA. if_cases K4; zify_cond K4; [exfalso; revert K4; rewrite ?unsigned_lit by lia; clear -CEILB HH; intros K4; lia|].  (* [comment removed for export] *)
  zstepA.                         (* [comment removed for export] *)
  replace (2 * h - h) with h by (clear; lia).
  zstepA.                         (* [comment removed for export] *)
  cstep.                          (* [comment removed for export] *)
  do 7 zstepA.                    (* [comment removed for export] *)
  replace (h ≪ 2) with (4 * h) by (rewrite Z.shiftl_mul_pow2 by lia; change (2^2) with 4; clear; lia).
  cstep.                          (* [comment removed for export] *)
  (* [comment removed for export] *)
  carve_frame 128%nat SK.
  do 14 cstep.                    (* [comment removed for export] *)
  do 7 zstepA.                    (* [comment removed for export] *)
  zstepA. zstepA.                 (* [comment removed for export] *)
  do 9 zstepA.                    (* [comment removed for export] *)
  do 4 zstepA.                    (* [comment removed for export] *)
  rewrite ?(Z.mod_small (c ≪ 7)) by (rewrite Z.shiftl_mul_pow2 by lia; clear -CEILB HC; lia).
  replace (RI + c ≪ 7) with RIv by (rewrite Z.shiftl_mul_pow2 by lia; clear -CEILB HRIv; lia).
  replace (c ≪ 32) with (c * 4294967296) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
  zstepA.                         (* [comment removed for export] *)
  do 6 zstepA.                    (* [comment removed for export] *)
  do 2 zstepA.                    (* [comment removed for export] *)
  try if_false.
  do 2 zstepA.                    (* [comment removed for export] *)
  assert (AL8 : RIv mod 8 = 0) by (rewrite HRIv, HRI0; clear -CEILB HSB; Z.div_mod_to_equations; lia).
  stepA.                          (* [comment removed for export] *)
  cstep.                          (* [comment removed for export] *)
  stepA.                          (* [comment removed for export] *)
  cstep.                          (* [comment removed for export] *)
  cstep.                          (* [comment removed for export] *)
  zstepA.                         (* [comment removed for export] *)
  do 5 zstepA.                    (* [comment removed for export] *)
  eapply CONT; [exact MI| exact SK| exact MU| exact WM| | exact INS| exact PC| exact ARR| exact CST| exact RIC].
  unfold drain_frames. split; [exact FR| split; [eexact FR0| eexact FR1]].
Qed.
End LDC.
End RC__1.
(* [comment removed for export] *)
