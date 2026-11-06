(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages AImageFacts NodesA ImplRzA NodesA_mm.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA.examples Require Import X_mmap_fixed.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AF_place AF_kit AF_kit2 AF_poison AF_qkit AF_mmfix1 AF_free6 AF_free7 AF_free9 AF_free10.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require ZBridge Arr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
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
Lemma wr_at_join : forall segs m a n1 n2, wr_at segs m a n1 -> wr_at segs m (a + n1) n2 -> 0 <= n1 -> 0 <= n2 -> wr_at segs m a (n1 + n2).
Proof. aceil.
  intros segs m a n1 n2 (A1 & B1 & W1) (A2 & B2 & W2) H1 H2. split; [lia|]. split; [lia|].
  intros i Hi. destruct (Z_lt_le_dec i n1); [apply W1; lia|].
  replace (a + i) with (a + n1 + (i - n1)) by lia. apply W2. lia.
Qed.
Lemma u32arr_app : forall m A ws1 ws2,
  Arr.u32arr asegs m A ws1 -> Arr.u32arr asegs m (A + 4 * Z.of_nat (length ws1)) ws2 -> Arr.u32arr asegs m A (ws1 ++ ws2).
Proof. aceil.
  intros m A ws1 ws2 [B1 W1] [B2 W2]. split.
  - rewrite Arr.u32s_app. apply bytes_at_app. split; [exact B1|]. rewrite Arr.u32s_length.
    replace (A + Z.of_nat (4 * length ws1)) with (A + 4 * Z.of_nat (length ws1)) by lia. exact B2.
  - rewrite length_app. replace (4 * Z.of_nat (length ws1 + length ws2)) with (4 * Z.of_nat (length ws1) + 4 * Z.of_nat (length ws2)) by lia.
    apply wr_at_join; [exact W1| exact W2| lia| lia].
Qed.
Lemma u32s_zeros : forall n, Arr.u32s (repeat (Z_to_bv 64 0) n) = repeat (Z_to_bv 8 0) (4 * n)%nat.
Proof. aceil. induction n as [|n IH]; [reflexivity|]. cbn [repeat Arr.u32s]. rewrite IH. replace (4 * Datatypes.S n)%nat with (4 + 4 * n)%nat by lia. rewrite repeat_app. reflexivity. Qed.
Lemma u32arr_of_zeros_nat : forall m A n,
  rw_cells asegs m A [CB (4 * n)%nat (repeat (Z_to_bv 8 0) (4 * n)%nat)] -> Arr.u32arr asegs m A (repeat (Z_to_bv 64 0) n).
Proof. aceil.
  intros m A n [[WF B] W]. split.
  - rewrite u32s_zeros. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
  - rewrite repeat_length. cbn [cells_size csize Nat.add] in W. replace (4 * Z.of_nat n) with (Z.of_nat (4 * n + 0)) by lia. exact W.
Qed.
(* [comment removed for export] *)
Lemma u32arr_of_zeros : forall m A L K,
  rw_cells asegs m A [CB (Z.to_nat L) (repeat (Z_to_bv 8 0) (Z.to_nat L))] -> L = 4 * K -> 0 <= K ->
  Arr.u32arr asegs m A (repeat (Z_to_bv 64 0) (Z.to_nat K)).
Proof. aceil.
  intros m A L K H HL HK. subst L. rewrite Z2Nat.inj_mul in H by lia. change (Z.to_nat 4) with 4%nat in H.
  apply u32arr_of_zeros_nat. exact H.
Qed.

Section LDG.
Variable P : acc -> Prop.
Variables (gp tp s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (usp lo : Z) (CA SB c p RI : Z).
Notation INST := 0xaa518.
Notation PCB := (AF_free6.PCB CA c).
Notation RIc := (AF_free6.RIc c RI).
Notation FA := (SB + c * 4294967296 + 3758096384).
Notation rregs := (AF_free7.rregs gp tp t3 t4 t5 t6 usp c RI).
Notation gregs := (AF_free9.gregs gp tp t3 t4 t5 t6 CA SB c RI).

Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO2 : lo <= usp - 688.
Hypothesis SPH : usp <= 2^47.
Hypothesis SPA : usp mod 16 = 0.
Hypothesis HSB : 0x603000 <= SB /\ SB mod 4096 = 0 /\ SB + kSpaceSize + 4096 <= alloc_ceiling.
Hypothesis HSBH : kHighMemBeg <= SB.
Hypothesis HC : 1 <= c <= kLargestClassID.
Hypothesis HCA : (0x1000 <= CA /\ (CA + 2584 <= 0x10000 \/ 0x603000 <= CA)) /\ CA + 2584 <= alloc_ceiling /\ CA mod 8 = 0.   (* [comment removed for export] *)
Hypothesis HCASB : CA + 2584 <= SB \/ SB + kSpaceSize + 4096 <= CA.
Hypothesis HP : SB + c * 2^32 <= p /\ p + 16 <= SB + c * 2^32 + 0xE0000000.
Hypothesis HRI : RI = SB + kSpaceSize.
Hypothesis PSTK : forall a k, lo <= a -> a + Z.of_nat k <= usp -> P (Z_to_bv 64 a, k).
Hypothesis PDAT : forall a k, 0xa4000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PRO : forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x31000 -> P (Z_to_bv 64 a, k).
Hypothesis PCA : forall a k, CA <= a -> a + Z.of_nat k <= CA + 2584 -> P (Z_to_bv 64 a, k).
Hypothesis PRIR : forall a k, RIc <= a -> a + Z.of_nat k <= RIc + 128 -> P (Z_to_bv 64 a, k).

(* [comment removed for export] *)
Definition ldg_post {X} (R : X -> word -> bool -> Prop) (mx : mem) (ra s0 s1 s2 s3 s4 : word)
    (h alloc nf mfa au mu na nfr : Z) (csz : word) (ws fws : list word) (TSD CTX T nmaps nmapped : Z)
    (a : X) : machine_state -> Prop :=
  fun ms' => exists (r : word) (u : bool) (m' : mem),
       R a r u /\ mem_inv asegs m' /\ statics m'
    /\ munch [(usp - 688, usp); (RIc, RIc + 8); (RIc + 16, RIc + 32); (RIc + 80, RIc + 88); (PCB, PCB + 4);
              (PCB + 16 + 4 * h, PCB + 16 + 4 * h + 4); (CA + 2576, CA + 2584); (FA + 4 * nf, FA + 4 * (nf + h));
              (FA + mfa, FA + mfa + 262144); (kShadowBase + (FA + mfa) / 8, kShadowBase + (FA + mfa) / 8 + 32768); (T + 2872, T + 2888)] mx m'
    /\ wmono asegs mx m'
    /\ (   (* [comment removed for export] *)
           (is_err r = false /\ exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
              ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                       F (ret_pc ra) fc None m' (seg_rom asegs)
              /\ stk asegs m' lo usp
              /\ rw_cells asegs m' 0xaa538 [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 RI); C1 (Z_to_bv 8 0)]
              /\ rw_cells asegs m' PCB [C4 (Z_to_bv 64 (h + 1)); C4 (Z_to_bv 64 (2 * h)); C8 csz]
              /\ Arr.u32arr asegs m' (PCB + 16) (upd ws (Z.to_nat h) (Z_to_bv 64 (AF_free6.xc SB c p)))
              /\ rw_cells asegs m' (CA + 2576) [C8 (Z_to_bv 64 (alloc - bv_unsigned csz))]
              /\ rw_cells asegs m' RIc (ri_cells 0 (nf + h) (mfa + 262144) au mu na (nfr + h))
              /\ Arr.u32arr asegs m' FA (cpn (Z.to_nat h) ws (fws ++ repeat (Z_to_bv 64 0) (Z.to_nat 65536)) (Z.to_nat h) (Z.to_nat nf))
              /\ rw_cells asegs m' (kShadowBase + (FA + mfa) / 8) [CB (Z.to_nat 32768) (repeat (Z_to_bv 8 250) (Z.to_nat 32768))]
              /\ poison_globals m' /\ thread_cells m' tp TSD CTX T
              /\ rw_cells asegs m' (T + 2872) [C8 (Z_to_bv 64 (nmaps + 1)); C8 (Z_to_bv 64 (nmapped + 262144))])
        \/ (* [comment removed for export] *)
           (is_err r = true /\ bv_unsigned r = ENOMEMw /\ exists R', ms' = MS R' F (Z_to_bv 64 0x35c28) fc None m' (seg_rom asegs))
        \/ (* [comment removed for export] *)
           (is_err r = true /\ bv_unsigned r <> ENOMEMw /\ exists (ra' sp' s4' e4 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (junk : list byte),
              ms' = MS (mkR ra' sp' gp tp t0' t1' t2' (Z_to_bv 64 262144) (Z_to_bv 64 1) a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (FA + mfa)) r s4'
                            (Z_to_bv 64 h) (Z_to_bv 64 (PCB + 4 * h + 16)) (Z_to_bv 64 (nf + h)) (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 FA)
                            (Z_to_bv 64 1152921504607895551) (Z_to_bv 64 1152921504606846976) t3' t4' t5' t6')
                       F (Z_to_bv 64 a_mmap_fixed_die) fc None m' (seg_rom asegs)
              /\ bv_unsigned sp' = usp - 384 /\ sx32 e4 = Z_to_bv 64 (2^64 - bv_unsigned r) /\ stk asegs m' lo (usp - 384)
              /\ rw_cells asegs m' (usp - 384) [C4 (Z_to_bv 64 50); CB 40 junk; C4 e4; C8 (Z_to_bv 64 INST); C8 (Z_to_bv 64 RIc); C8 (Z_to_bv 64 262144);
                                               C8 (Z_to_bv 64 (FA + mfa)); C8 (Z_to_bv 64 (mfa + 262144)); C8 (Z_to_bv 64 0x35b5c)])).

(* [comment removed for export] *)
(* [comment removed for export] *)

End LDG.
End RC__1.
(* [comment removed for export] *)
