(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BF_place BF_kit BF_kit2 BF_qkit BF_free6.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require ZBridge Arr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)

(* [comment removed for export] *)
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
  | H : rw_cells bsegs mc _ _ |- _ => first [ carry_rw H MUc WMc | skipH H ]
  | H : bytes_at bsegs mc _ _ |- _ => first [ eapply bytes_at_transport in H; [| exact MUc| cbn [disjoint_from length]; rewrite ?repeat_length, ?length_le8, ?length_le4; lia] | skipH H ]
  | H : stk bsegs mc _ _ |- _ => first [ eapply stk_transport in H; [| exact MUc| exact WMc| intros; left; cbn; lia] | skipH H ]
  | H : wr_at bsegs mc _ _ |- _ => first [ eapply wr_at_transport in H; [| exact WMc] | skipH H ]
  | H : u8arr bsegs mc _ _ |- _ => first [ eapply u8arr_transport in H; [| exact MUc| exact WMc| cbn [disjoint_from length]; rewrite ?repeat_length; lia] | skipH H ]
  | H : u64arr bsegs mc _ _ |- _ => first [ eapply u64arr_transport in H; [| exact MUc| exact WMc| cbn [disjoint_from length]; lia] | skipH H ]
  | H : u32arr bsegs mc _ _ |- _ => first [ eapply u32arr_transport in H; [| exact MUc| exact WMc| cbn [disjoint_from length]; lia] | skipH H ]
  | H : munch ?W ?ma mc |- _ =>
      let H2 := fresh in
      first [ assert (H2 : munch W ma m')
          by (eapply munch_trans; [exact H| eapply munch_weaken; [| exact MUc];
              first [ sub_fp_fast | let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *; decompose [and] Hq; clear Hq; repeat match goal with |- _ /\ _ => split end; try exact I; match goal with O : ~ (_ <= xq < _)%Z |- _ => clear -O; let R := fresh in intros R; apply O; lia end ]]);
        clear H; rename H2 into H | skipH H ]
  | H : wmono bsegs ?ma mc |- _ =>
      let H2 := fresh in
      assert (H2 : wmono bsegs ma m') by (eapply wmono_trans; [exact H| exact WMc]);
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
Fixpoint cpn (n : nat) (src dst : list word) (a b : nat) : list word :=
  match n with
  | O => dst
  | S n' => cpn n' src (upd dst b (match nth_error src a with Some w => w | None => Z_to_bv 64 0 end)) (S a) (S b)
  end.
Lemma cpn_length : forall n src dst a b, length (cpn n src dst a b) = length dst.
Proof. aceil. induction n; intros; cbn; [reflexivity|]. rewrite IHn, upd_length. reflexivity. Qed.

End RC__1.
Ltac at_pc p tac := lazymatch goal with |- evtA _ _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => tryif constr_eq q p then tac else idtac | |- _ => idtac end.

Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section MRTO.
Variable P : acc -> Prop.
Variables (gp tp t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (lo : Z) (SB c RI : Z).
Notation INST := 0xaaf58.
Notation RIc := (BF_free6.RIc c RI).

Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis HSB : 0x603000 <= SB /\ SB mod 4096 = 0 /\ SB + kSpaceSize + 4096 <= alloc_ceiling.
Hypothesis HC : 1 <= c <= kLargestClassID.
Hypothesis HRI : RI = SB + kSpaceSize.
Hypothesis PDAT : forall a k, 0xa5000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PRIR : forall a k, RIc <= a -> a + Z.of_nat k <= RIc + 128 -> P (Z_to_bv 64 a, k).

(* [comment removed for export] *)
Lemma mrto_walk : forall mx (ra t0 t1 t2 s0 s1 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (sp : Z)
    (mtx n mfa au mu na nfr : Z) (Q : machine_state -> Prop),
  mem_inv bsegs mx -> stk bsegs mx lo sp -> lo <= sp - 80 -> sp <= 2^47 -> sp mod 16 = 0 ->
  rw_cells bsegs mx 0xaaf78 [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 RI)] ->
  rw_cells bsegs mx RIc (ri_cells mtx n mfa au mu na nfr) -> 0 <= n < 2^64 -> 0 <= nfr < 2^64 ->
  rw_cells bsegs mx 0xa5580 [C8 (Z_to_bv 64 0x13e060)] -> rw_cells bsegs mx 0x13e060 [C8 (Z_to_bv 64 4096)] ->
  (forall a k, lo <= a -> a + Z.of_nat k <= sp -> P (Z_to_bv 64 a, k)) ->
  (forall m' (a0' a1' a2' a3' : word),
     mem_inv bsegs m' -> stk bsegs m' lo sp -> munch [(sp + -80, sp)] mx m' -> wmono bsegs mx m' ->
     evtA bsegs P Q (MS (mkR ra (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  evtA bsegs P Q (MS (mkR ra (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 INST) a1 (Z_to_bv 64 c) (Z_to_bv 64 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x35a48) fc None mx (seg_rom bsegs)).
Proof. aceil.
  intros until Q. intros MI SK LO SPH SPA INS RIC HN HNFR G1 V1 PSTK CONT. unfold ri_cells in RIC.
  pose proof LOC as LOC0. pose proof HSB as HSB0. pose proof HRI as HRI0. aceil.
  unfold kSpaceSize in HSB, HRI0. pose proof HC as HC0. unfold kLargestClassID in HC.
  assert (MU : munch [(sp + -80, sp)] mx mx) by apply munch_refl.
  assert (WM : wmono bsegs mx mx) by apply wmono_refl.
  unfold BF_free6.RIc in *. set (RIv := RI + 128 * c) in *. assert (HRIv : RIv = RI + 128 * c) by reflexivity. clearbody RIv.
  carve_frame 80%nat SK.
  do 10 cstep.                    (* [comment removed for export] *)
  do 4 cstep.                     (* [comment removed for export] *)
  zstepA.                         (* [comment removed for export] *)
  do 2 zstepA.                    (* [comment removed for export] *)
  zstepA. if_cases K0; zify_cond K0; [exfalso; revert K0; rewrite ?unsigned_lit by lia; clear -CEILB HC; intros K0; lia|].   (* [comment removed for export] *)
  zstepA.                         (* [comment removed for export] *)
  zstepA. if_cases K1; zify_cond K1.                                (* [comment removed for export] *)
  1: do 9 zstepA.                 (* [comment removed for export] *)
  2: zstepA; cstep.               (* [comment removed for export] *)
  all: do 2 zstepA.               (* [comment removed for export] *)
  all: zstepA.                    (* [comment removed for export] *)
  all: zstepA.                    (* [comment removed for export] *)
  all: rewrite ?(Z.mod_small (c ≪ 7)) by (rewrite Z.shiftl_mul_pow2 by lia; clear -CEILB HC; lia).
  all: replace (RI + c ≪ 7) with RIv by (rewrite Z.shiftl_mul_pow2 by lia; clear -CEILB HRIv; lia).
  all: cstep.                     (* [comment removed for export] *)
  all: zstepA.                    (* [comment removed for export] *)
  all: zstepA.                    (* [comment removed for export] *)
  all: zstepA; (let K := fresh "K" in if_cases K; clear K).        (* [comment removed for export] *)
  all: at_pc 0x35ae4 ltac:(cstep).                                  (* [comment removed for export] *)
  all: at_pc 0x35afc ltac:(zstepA; zstepA; zstepA; zstepA;          (* [comment removed for export] *)
                            zstepA; (let K := fresh "K" in if_cases K; clear K)).   (* [comment removed for export] *)
  all: at_pc 0x35b10 ltac:(cstep; zstepA;                           (* [comment removed for export] *)
                            replace (sx32 (Z_to_bv 64 4294967295)) with (Z_to_bv 64 18446744073709551615) by (apply bv_eq; vm_compute; reflexivity);
                            cstep).                                 (* [comment removed for export] *)
  all: do 10 cstep.               (* [comment removed for export] *)
  all: release_frame FR SK sp.
  all: cstep.                     (* [comment removed for export] *)
  all: eapply CONT; [exact MI| exact SK| exact MU| exact WM].
Qed.
End MRTO.


Section LDC2.
Variable P : acc -> Prop.
Variables (gp tp s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (usp lo : Z) (CA SB c p RI : Z).
Notation INST := 0xaaf58.
Notation PCB := (BF_free6.PCB CA c).
Notation RIc := (BF_free6.RIc c RI).
Notation FA := (SB + c * 4294967296 + 3758096384).
Notation rta_regs := (BF_free6.rta_regs gp tp t3 t4 t5 t6 usp CA SB c RI).
Notation drain_frames := (BF_free6.drain_frames s5 s6 s7 s8 s9 s10 s11 usp CA c p RI).

Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO2 : lo <= usp - 688.
Hypothesis SPH : usp <= 2^47.
Hypothesis SPA : usp mod 16 = 0.
Hypothesis HSB : 0x603000 <= SB /\ SB mod 4096 = 0 /\ SB + kSpaceSize + 4096 <= alloc_ceiling.
Hypothesis HC : 1 <= c <= kLargestClassID.
Hypothesis HCA : (0x1000 <= CA /\ (CA + 2584 <= 0x10000 \/ 0x603000 <= CA)) /\ CA + 2584 <= alloc_ceiling /\ CA mod 8 = 0.   (* [comment removed for export] *)
Hypothesis HCASB : CA + 2584 <= SB \/ SB + kSpaceSize + 4096 <= CA.
Hypothesis HP : SB + c * 2^32 <= p /\ p + 16 <= SB + c * 2^32 + 0xE0000000.
Hypothesis HRI : RI = SB + kSpaceSize.
Hypothesis PSTK : forall a k, lo <= a -> a + Z.of_nat k <= usp -> P (Z_to_bv 64 a, k).
Hypothesis PDAT : forall a k, 0xa5000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PRO : forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x31000 -> P (Z_to_bv 64 a, k).
Hypothesis PCA : forall a k, CA <= a -> a + Z.of_nat k <= CA + 2584 -> P (Z_to_bv 64 a, k).
Hypothesis PRIR : forall a k, RIc <= a -> a + Z.of_nat k <= RIc + 128 -> P (Z_to_bv 64 a, k).

(* [comment removed for export] *)
Definition rregs (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s6 s9 : word) (h nf : Z) : _ :=
  mkR ra (Z_to_bv 64 (usp + -240)) gp tp t0 t1 t2 (Z_to_bv 64 RIc) s1 a0 a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 c) (Z_to_bv 64 (usp + -104)) (Z_to_bv 64 INST) (Z_to_bv 64 h) s6 (Z_to_bv 64 (nf + h))
      (Z_to_bv 64 2305843009213693952) s9 (Z_to_bv 64 1152921504607895551) (Z_to_bv 64 1152921504606846976) t3 t4 t5 t6.

(* [comment removed for export] *)
Lemma efa_nogrow : forall mx (t0 t1 t2 : word) (h nf mfa au mu na nfr mtx : Z) (Q : machine_state -> Prop),
  mem_inv bsegs mx -> stk bsegs mx lo (usp + -240) ->
  rw_cells bsegs mx RIc (ri_cells mtx nf mfa au mu na nfr) ->
  1 <= h <= 8 -> 0 <= nf < 2^40 -> 4 * (nf + h) <= mfa -> 0 <= mfa <= 2^29 ->
  (forall m',
     mem_inv bsegs m' -> stk bsegs m' lo (usp + -240) ->
     munch [(usp + -288, usp + -240)] mx m' -> wmono bsegs mx m' ->
     evtA bsegs P Q (MS (rregs (Z_to_bv 64 0x35704) t0 t1 t2 (Z_to_bv 64 nf) (Z_to_bv 64 1) (Z_to_bv 64 RIc) (Z_to_bv 64 (SB + c * 4294967296)) (Z_to_bv 64 1)
                               (Z_to_bv 64 mfa) (Z_to_bv 64 (4 * (nf + h))) (Z_to_bv 64 0) (Z_to_bv 64 1500)
                               (Z_to_bv 64 (PCB + 4 * h + 16)) (Z_to_bv 64 FA) h nf)
                        F (Z_to_bv 64 0x35704) fc None m' (seg_rom bsegs))) ->
  evtA bsegs P Q (MS (rta_regs (Z_to_bv 64 0x35704) t0 t1 t2 (Z_to_bv 64 nf) (Z_to_bv 64 INST) (Z_to_bv 64 RIc) (Z_to_bv 64 (nf + h))
                            (Z_to_bv 64 0) (Z_to_bv 64 1152921504606846976) (Z_to_bv 64 0) (Z_to_bv 64 1500) h nf)
                     F (Z_to_bv 64 0x358c8) fc None mx (seg_rom bsegs)).
Proof. aceil.
  intros until Q. intros MI SK RIC HH NF MFA MFR CONT. unfold ri_cells in RIC. unfold BF_free6.rta_regs, rregs in *.
  pose proof LOC as LOC0. pose proof HSB as HSB0. pose proof HRI as HRI0. aceil.
  unfold kSpaceSize in HSB, HCASB, HRI0. pose proof HC as HC0. unfold kLargestClassID in HC.
  assert (MU : munch [(usp + -288, usp + -240)] mx mx) by apply munch_refl.
  assert (WM : wmono bsegs mx mx) by apply wmono_refl.
  unfold BF_free6.PCB in *. set (PCBv := CA + 80 * c) in *. assert (HPCB : PCBv = CA + 80 * c) by reflexivity. clearbody PCBv.
  unfold BF_free6.RIc in *. set (RIv := RI + 128 * c) in *. assert (HRIv : RIv = RI + 128 * c) by reflexivity. clearbody RIv.
  carve_frame 48%nat SK.
  do 6 cstep.                     (* [comment removed for export] *)
  zstepA.                         (* [comment removed for export] *)
  do 2 zstepA.                    (* [comment removed for export] *)
  replace ((nf + h) ≪ 2) with (4 * (nf + h)) by (rewrite Z.shiftl_mul_pow2 by lia; change (2^2) with 4; clear; lia).
  rewrite ?(Z.mod_small (4 * (nf + h))) by (clear -CEILB HH NF; lia).
  zstepA. if_cases K0; zify_cond K0; [| exfalso; revert K0; rewrite ?unsigned_lit by lia; clear -CEILB HH NF MFA MFR; intros K0; lia].  (* [comment removed for export] *)
  cstep.                          (* [comment removed for export] *)
  do 6 cstep.                     (* [comment removed for export] *)
  release_frame FR SK (usp + -240).
  cstep.                          (* [comment removed for export] *)
  eapply CONT; [exact MI| exact SK| exact MU| exact WM].
Qed.

(* [comment removed for export] *)
Lemma fa_copy_loop : forall (k : nat) (i : Z) mx (ws fws : list word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 : word) (h nf mfa : Z) (Q : machine_state -> Prop),
  Z.of_nat k = h - i -> 0 <= i < h -> 1 <= h <= 8 -> 0 <= nf -> 4 * (nf + h) <= mfa -> mfa <= 2^29 ->
  mem_inv bsegs mx ->
  u32arr bsegs mx (PCB + 16) ws -> length ws = 16%nat ->
  (forall j, (Z.to_nat h <= j < Z.to_nat (2 * h))%nat -> exists x, nth_error ws j = Some (Z_to_bv 64 x) /\ 0 <= x < 2^31) ->
  u32arr bsegs mx FA fws -> 4 * Z.of_nat (length fws) = mfa ->
  (forall a k, FA <= a -> a + Z.of_nat k <= FA + mfa -> P (Z_to_bv 64 a, k)) ->      (* [comment removed for export] *)
  (forall m' (a1' : word),
     mem_inv bsegs m' -> munch [(FA + 4 * nf, FA + 4 * (nf + h))] mx m' -> wmono bsegs mx m' ->
     u32arr bsegs m' (PCB + 16) ws ->
     u32arr bsegs m' FA (cpn k ws fws (Z.to_nat (h + i)) (Z.to_nat (nf + i))) ->
     evtA bsegs P Q (MS (rregs (Z_to_bv 64 0x35704) t0 t1 t2 (Z_to_bv 64 (4 * nf)) (Z_to_bv 64 (PCB + 16 + 4 * (2 * h))) a1' a2 a3 a4 a5 a6 a7
                               (Z_to_bv 64 (PCB + 16 + 4 * (2 * h))) (Z_to_bv 64 (FA + 4 * (nf + h))) h nf)
                        F (Z_to_bv 64 0x35730) fc None m' (seg_rom bsegs))) ->
  evtA bsegs P Q (MS (rregs (Z_to_bv 64 0x35704) t0 t1 t2 (Z_to_bv 64 (4 * nf)) (Z_to_bv 64 (PCB + 16 + 4 * (2 * h))) a1 a2 a3 a4 a5 a6 a7
                            (Z_to_bv 64 (PCB + 16 + 4 * (h + i))) (Z_to_bv 64 (FA + 4 * (nf + i))) h nf)
                     F (Z_to_bv 64 0x3571c) fc None mx (seg_rom bsegs)).
Proof. aceil.
  induction k as [|k IH]; intros i mx ws fws t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 h nf mfa Q Hk Hi HH NF MFA MFR MI ARR LEN SMALL FAR FLEN PFA CONT; [lia|].
  unfold rregs in *.
  pose proof LOC as LOC0. pose proof HSB as HSB0. pose proof HRI as HRI0. pose proof HCA as HCA0. pose proof HCASB as HCASBpin. aceil.
  unfold kSpaceSize in HSB, HCASB, HRI0. pose proof HC as HC0. unfold kLargestClassID in HC.
  unfold BF_free6.PCB in *. set (PCBv := CA + 80 * c) in *. assert (HPCB : PCBv = CA + 80 * c) by reflexivity. clearbody PCBv.
  set (FAv := SB + c * 4294967296 + 3758096384) in *. assert (HFAv : FAv = SB + c * 4294967296 + 3758096384) by reflexivity. clearbody FAv.
  assert (MU : munch [(FAv + 4 * nf, FAv + 4 * (nf + h))] mx mx) by apply munch_refl.
  assert (WM : wmono bsegs mx mx) by apply wmono_refl.
  destruct (SMALL (Z.to_nat (h + i)) ltac:(clear -CEILB Hi HH; lia)) as (x & NTH & HX).
  pose proof (Arr.u32arr_read bsegs mx (PCBv + 16) ws (h + i) (Z_to_bv 64 x) (Z_to_bv 64 (PCBv + 16 + 4 * (h + i))) ARR NTH ltac:(clear -CEILB Hi HH; lia)
                ltac:(reflexivity)) as RD.
  zstepA. clear RD.               (* [comment removed for export] *)
  rewrite (fsx32_small' x) by (clear -CEILB HX; lia).
  zstepA.                         (* [comment removed for export] *)
  match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?m0 _) =>
    pose proof (Arr.u32arr_store_ok bsegs m0 FAv fws (nf + i) (Z_to_bv 64 (FAv + 4 * (nf + i))) FAR ltac:(clear -CEILB Hi HH NF MFA FLEN; lia) ltac:(reflexivity)) as SOK;
    pose proof (Arr.u32arr_write bsegs m0 FAv fws (nf + i) (Z_to_bv 64 x) FAR ltac:(clear -CEILB Hi HH NF MFA FLEN; lia)) as FAR' end.
  stepA.                          (* [comment removed for export] *)
  all: lazymatch goal with |- P _ => apply PFA; clear -CEILB Hi HH NF MFA HFAv; lia | _ => idtac end.
  clear FAR. store_done. rename FAR' into FAR.
  zstepA.                         (* [comment removed for export] *)
  zstepA. if_cases KL; zify_cond KL.
  - (* [comment removed for export] *)
    replace (PCBv + 16 + 4 * (h + i) + 4) with (PCBv + 16 + 4 * (h + (i + 1))) by (clear; lia).
    replace (FAv + 4 * (nf + i) + 4) with (FAv + 4 * (nf + (i + 1))) by (clear; lia).
    eapply (IH (i + 1)); [clear -CEILB Hk Hi KL HH HPCB; lia| | exact HH| exact NF| exact MFA| exact MFR| exact MI| exact ARR| exact LEN| exact SMALL| exact FAR| rewrite upd_length; exact FLEN| exact PFA|].
    { revert KL. rewrite ?unsigned_lit by lia. clear -CEILB Hi HH Hk. intros KL. lia. }
    intros m' a1' MI' MU' WM' ARR' FAR'. eapply CONT; [exact MI'| eapply munch_trans; [exact MU| exact MU']| eapply wmono_trans; [exact WM| exact WM']| exact ARR'|].
    cbn [cpn]. rewrite NTH. replace (S (Z.to_nat (h + i))) with (Z.to_nat (h + (i + 1))) by (clear -CEILB Hi HH; lia).
    replace (S (Z.to_nat (nf + i))) with (Z.to_nat (nf + (i + 1))) by (clear -CEILB Hi NF; lia). exact FAR'.
  - (* [comment removed for export] *)
    assert (Ei : h = i + 1) by (revert KL; rewrite ?unsigned_lit by lia; clear -CEILB Hi HH Hk; intros KL; lia).
    replace (PCBv + 16 + 4 * (h + i) + 4) with (PCBv + 16 + 4 * (2 * h)) by (clear -CEILB Ei; lia).
    replace (FAv + 4 * (nf + i) + 4) with (FAv + 4 * (nf + h)) by (clear -CEILB Ei; lia).
    eapply CONT; [exact MI| exact MU| exact WM| exact ARR|].
    replace k with O by (clear -CEILB Hk Ei; lia). cbn [cpn]. rewrite NTH. exact FAR.
Qed.
(* [comment removed for export] *)
Lemma rta_tail : forall mx (ra s0 s1 s2 s3 s4 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6' : word) (h alloc nf mfa au mu na nfr : Z) (csz : word)
    (ws fws : list word) (j1 j2 : list byte) (Q : machine_state -> Prop),
  mem_inv bsegs mx -> stk bsegs mx lo (usp + -240) ->
  drain_frames mx ra s0 s1 s2 s3 s4 j1 j2 ->
  rw_cells bsegs mx 0xaaf78 [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 RI)] ->
  rw_cells bsegs mx PCB [C4 (Z_to_bv 64 h); C4 (Z_to_bv 64 (2 * h)); C8 csz] ->
  1 <= h <= 8 ->
  u32arr bsegs mx (PCB + 16) ws -> length ws = 16%nat ->
  rw_cells bsegs mx (CA + 2576) [C8 (Z_to_bv 64 alloc)] ->
  rw_cells bsegs mx RIc (ri_cells 1152921504606846976 nf mfa au mu na nfr) -> 0 <= nf < 2^40 -> 0 <= nfr < 2^64 ->   (* [comment removed for export] *)
  u32arr bsegs mx FA fws -> 4 * Z.of_nat (length fws) = mfa -> mfa <= 2^29 ->
  rw_cells bsegs mx 0xa5580 [C8 (Z_to_bv 64 0x13e060)] -> rw_cells bsegs mx 0x13e060 [C8 (Z_to_bv 64 4096)] ->
  (forall m' (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' : word),
     mem_inv bsegs m' -> stk bsegs m' lo usp ->
     munch [(usp - 688, usp); (RIc, RIc + 8); (RIc + 16, RIc + 24); (RIc + 80, RIc + 88); (PCB, PCB + 4);
            (PCB + 16 + 4 * h, PCB + 16 + 4 * h + 4); (CA + 2576, CA + 2584)] mx m' -> wmono bsegs mx m' ->
     rw_cells bsegs m' 0xaaf78 [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 RI)] ->
     rw_cells bsegs m' PCB [C4 (Z_to_bv 64 (h + 1)); C4 (Z_to_bv 64 (2 * h)); C8 csz] ->
     u32arr bsegs m' (PCB + 16) (upd ws (Z.to_nat h) (Z_to_bv 64 (BF_free6.xc SB c p))) ->
     rw_cells bsegs m' (CA + 2576) [C8 (Z_to_bv 64 (alloc - bv_unsigned csz))] ->
     rw_cells bsegs m' RIc (ri_cells 0 (nf + h) mfa au mu na (nfr + h)) ->
     u32arr bsegs m' FA fws ->
     rw_cells bsegs m' 0xa5580 [C8 (Z_to_bv 64 0x13e060)] -> rw_cells bsegs m' 0x13e060 [C8 (Z_to_bv 64 4096)] ->
     evtA bsegs P Q (MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  evtA bsegs P Q (MS (rregs (Z_to_bv 64 0x35704) t0 t1 t2 (Z_to_bv 64 (4 * nf)) a0 a1 a2 a3 a4 a5 a6 a7 s6' (Z_to_bv 64 (FA + 4 * (nf + h))) h nf)
                     F (Z_to_bv 64 0x35730) fc None mx (seg_rom bsegs)).
Proof. aceil.
  intros until Q. intros MI SK DF INS PC HH ARR LEN CST RIC NF NFR FAR FLEN MFR G1 V1 CONT.
  unfold ri_cells in RIC, CONT. unfold rregs. unfold BF_free6.drain_frames in DF. destruct DF as (FRa & FRb & FRc).
  pose proof LOC as LOC0. pose proof HSB as HSB0. pose proof HRI as HRI0. pose proof HCA as HCA0. pose proof HCASB as HCASBpin. aceil.
  unfold kSpaceSize in HSB, HCASB, HRI0. pose proof HC as HC0. unfold kLargestClassID in HC.
  unfold BF_free6.PCB in *. set (PCBv := CA + 80 * c) in *. assert (HPCB : PCBv = CA + 80 * c) by reflexivity. clearbody PCBv.
  unfold BF_free6.RIc in *. set (RIv := RI + 128 * c) in *. assert (HRIv : RIv = RI + 128 * c) by reflexivity. clearbody RIv.
  set (FAv := SB + c * 4294967296 + 3758096384) in *. assert (HFAv : FAv = SB + c * 4294967296 + 3758096384) by reflexivity. clearbody FAv.
  assert (MU : munch [(usp - 688, usp + -48); (RIv, RIv + 8); (RIv + 16, RIv + 24); (RIv + 80, RIv + 88)] mx mx) by apply munch_refl.
  assert (WM : wmono bsegs mx mx) by apply wmono_refl.
  pose proof (unsigned_lit usp ltac:(lia)) as USP.
  zstepA.                         (* [comment removed for export] *)
  cstep.                          (* [comment removed for export] *)
  zstepA.                         (* [comment removed for export] *)
  cstep.                          (* [comment removed for export] *)
  do 4 zstepA.                    (* [comment removed for export] *)
  cstep.                          (* [comment removed for export] *)
  rewrite <- (ZBridge.Z_to_bv_mod64 (nfr + h)) in RIC.   (* [comment removed for export] *)
  eapply (mrto_walk P gp tp t3 t4 t5 t6 F fc lo SB c RI LOC0 HSB0 HC0 HRI PDAT);
    [ unfold BF_free6.RIc; rewrite <- HRIv; exact PRIR | exact MI| exact SK| clear -CEILB LO2; lia| clear -CEILB SPH; lia| clear -CEILB SPA; Z.div_mod_to_equations; lia
    | exact INS| unfold BF_free6.RIc, ri_cells; rewrite <- HRIv; eexact RIC | clear -CEILB NF HH; lia| first [apply Z.mod_pos_bound; clear; lia| clear -CEILB NFR HH; lia]| exact G1| exact V1
    | intros; apply PSTK; lia|].
  clear MI SK. intros m2 a0' a1' a2' a3' MI SK MU2 WM2.
  lazymatch type of RIC with rw_cells _ ?mc _ _ => after_call mc m2 MU2 WM2 end.
  ret_pc_lit.
  zstepA.                         (* [comment removed for export] *)
  do 14 zstepA.                   (* [comment removed for export] *)
  do 3 zstepA. try if_false.      (* [comment removed for export] *)
  do 2 zstepA. try if_true.       (* [comment removed for export] *)
  do 7 zstepA.                    (* [comment removed for export] *)
  zstepA. try if_true.            (* [comment removed for export] *)
  assert (AL8 : RIv mod 8 = 0) by (rewrite HRIv, HRI0; clear -CEILB HSB; Z.div_mod_to_equations; lia).
  stepA.                          (* [comment removed for export] *)
  cstep.                          (* [comment removed for export] *)
  stepA.                          (* [comment removed for export] *)
  cstep.                          (* [comment removed for export] *)
  cstep.                          (* [comment removed for export] *)
  cstep.                          (* [comment removed for export] *)
  do 14 cstep.                    (* [comment removed for export] *)
  release_frame FRc SK (usp + -112).
  cstep.                          (* [comment removed for export] *)
  ret_pc_lit.
  do 3 zstepA.                    (* [comment removed for export] *)
  cstep.                          (* [comment removed for export] *)
  carve_frame 48%nat SK.
  do 5 cstep.                     (* [comment removed for export] *)
  cstep.                          (* [comment removed for export] *)
  do 5 cstep.                     (* [comment removed for export] *)
  release_frame FR SK (usp + -112).
  cstep. ret_pc_lit.              (* [comment removed for export] *)
  do 2 cstep.                     (* [comment removed for export] *)
  release_frame FRb SK (usp + -48).
  cstep. ret_pc_lit.              (* [comment removed for export] *)
  do 4 zstepA.                    (* [comment removed for export] *)
  zstepA. rewrite (fsx32_small' h) by (clear -CEILB HH; lia).             (* [comment removed for export] *)
  cstep.                          (* [comment removed for export] *)
  subst PCBv RIv FAv.
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?m _) =>
    destruct (rwc_split bsegs m 0xaaf78 [C8 (Z_to_bv 64 SB)] [C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 RI)] INS) as [ISB _] end.
  eapply (ldc_tail P gp tp s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc usp lo CA SB c p LOC0 ltac:(clear -CEILB LO2; lia) HSB0 HC0 HCA0 HCASB HP PSTK PDAT PCA);
    [ exact MI | replace (usp - 48) with (usp + -48) by lia; exact SK | replace (usp - 48) with (usp + -48) by lia; exact FRa
    | exact ISB | exact PC | exact ARR | exact LEN | clear -CEILB HH; lia | exact CST |].
  clear MI SK ISB. intros m3 t0' t1' t2' a0x a1x a2x a3x a4x a5x a6x a7x MI SK MU3 WM3 _ PC3 ARR3 CST3.
  unfold BF_free6.PCB in *.
  lazymatch type of RIC with rw_cells _ ?mc _ _ => carry_all mc m3 MU3 WM3 end.
  change 18446744073709551616 with (2^64) in RIC. rewrite ?ZBridge.Z_to_bv_mod64 in RIC.
  eapply CONT; [exact MI| exact SK| | exact WM| exact INS| exact PC3| exact ARR3| exact CST3| exact RIC| exact FAR| exact G1| exact V1].
  eapply munch_trans; [eapply munch_cover; [exact MU| solve_covers] | eapply munch_cover; [exact MU3| solve_covers]].
Qed.
End LDC2.
End RC__2.
(* [comment removed for export] *)
