(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require Import SumWalkTac Frame.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc Require Import RelocKit RCode_1c000_1d000.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Musl Require Import MuslTac MemcpyBase Memcpy.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require Import PFLib.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc Require Import RelocKit .
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Musl Require Import MuslTac PFBase.
Import ListNotations.
Open Scope bv_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation W8 v := (word_to_le_bytes 8 (Z_to_bv 64 v)).
Abbreviation X8 w := (word_to_le_bytes 8 w).

(* [comment removed for export] *)
Section GD_1.
  Context {RL : Reloc}.
Definition snw_regions (sp0 sp : Z) : list (word * Z) :=
  [(Z_to_bv 64 (sp - 64), 64%Z); (Z_to_bv 64 (sp0 - 2080), 2000%Z);
   (Z_to_bv 64 (sp0 - 2360), 8%Z); (Z_to_bv 64 (sp0 - 2344), 8%Z); (Z_to_bv 64 (sp0 - 2168), 16%Z)].
End GD_1.

Section SNW.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLD : RelocData RL} {RLI : RelocImg RL} {RLW : RelocRW RL RLD} {RLP : RelocPF RL}.
  Variables (sp0 : Z) (mem0 : word -> option byte) (cv : Z) (rom : word -> option byte).
  Hypothesis CTX : ctxH sp0 mem0 cv.
  Variables (m : word -> option byte) (sp u j s l : Z) (bs : list byte).
  Hypothesis F : FRM sp0 mem0 m.
  Hypothesis Hsp : (sp0 - FR + 64 <= sp /\ sp <= sp0 - 2768)%Z.
  Hypothesis Hck : rdn SEGS m (Z_to_bv 64 (sp0 - 2248)) 8 = Some (W8 (sp0 - 2168)).
  Hypothesis Hwpos : rdn SEGS m (Z_to_bv 64 (sp0 - 2360)) 8 = Some (W8 (sp0 - 2752 + u)).
  Hypothesis Hwbase : rdn SEGS m (Z_to_bv 64 (sp0 - 2344)) 8 = Some (W8 (sp0 - 2752)).
  Hypothesis Hbuf : rdn SEGS m (Z_to_bv 64 (sp0 - 2312)) 8 = Some (W8 (sp0 - 2752)).
  Hypothesis HCK : CKst m sp0 j.
  Hypothesis Hu : (0 <= u <= 80)%Z.
  Hypothesis Hdef : defined m (sp0 - 2752) u.
  Hypothesis Hl : (0 <= l < 2 ^ 32)%Z.
  Hypothesis Hs : rdn SEGS m (Z_to_bv 64 s) (Z.to_nat l) = Some bs.
  Hypothesis Hsrng : (0 <= s /\ (s + l <= sp0 - FR \/ (sp <= s /\ s + l <= sp0 - 2768)))%Z.

  Let Hcsp : (IMG_TOP + FR <= sp0 <= 0x800000000000)%Z := Csp _ _ _ CTX.

  Ltac sok := soks CTX.

  (* [comment removed for export] *)
  Record snwI (regs : bvmap 5 word) (ret : word) (r : bvmap 5 word) (m' : word -> option byte) (j' : Z) : Prop := SNWI {
    Ir_sp : getr r 2 = Z_to_bv 64 (sp - 64);
    Ir_s0 : getr r 8 = Z_to_bv 64 l;
    Ir_s1 : getr r 9 = Z_to_bv 64 (sp0 - 2400);
    Ir_s2 : getr r 18 = Z_to_bv 64 s;
    Ir_s3 : getr r 19 = Z_to_bv 64 (1999 - j');
    Ir_s5 : getr r 21 = Z_to_bv 64 (sp0 - 2168);
    Ir_a0 : getr r 10 = Z_to_bv 64 (sp0 - 2080 + j');
    Ir_cs : agree_but [1; 2; 8; 9; 18; 19; 20; 21] regs r;
    Im_fr : frame_mod m m' (snw_regions sp0 sp);
    Im_ra : rdn SEGS m' (Z_to_bv 64 (sp - 8)) 8 = Some (X8 ret);
    Im_s0 : rdn SEGS m' (Z_to_bv 64 (sp - 16)) 8 = Some (X8 (getr regs 8));
    Im_s1 : rdn SEGS m' (Z_to_bv 64 (sp - 24)) 8 = Some (X8 (getr regs 9));
    Im_s2 : rdn SEGS m' (Z_to_bv 64 (sp - 32)) 8 = Some (X8 (getr regs 18));
    Im_s3 : rdn SEGS m' (Z_to_bv 64 (sp - 40)) 8 = Some (X8 (getr regs 19));
    Im_s4 : rdn SEGS m' (Z_to_bv 64 (sp - 48)) 8 = Some (X8 (getr regs 20));
    Im_s5 : rdn SEGS m' (Z_to_bv 64 (sp - 56)) 8 = Some (X8 (getr regs 21));
    Im_buf : rdn SEGS m' (Z_to_bv 64 (sp0 - 2312)) 8 = Some (W8 (sp0 - 2752));
    Im_ck : CKst m' sp0 j';
    Im_src : rdn SEGS m' (Z_to_bv 64 s) (Z.to_nat l) = Some bs;
    Ij : (j <= j')%Z }.

  (* [comment removed for export] *)
  Ltac prefixA regs ret :=
        stepiv constr:(F_1c80c) constr:(D_1c80c) (Z_to_bv 64 (sp - 64)) ltac:(zval);  (* [comment removed for export] *)
        stepST constr:(F_1c810) constr:(D_1c810) (Z_to_bv 64 (sp - 8)) ret ltac:(sok);                (* [comment removed for export] *)
        stepST constr:(F_1c814) constr:(D_1c814) (Z_to_bv 64 (sp - 16)) (getr regs 8) ltac:(sok);     (* [comment removed for export] *)
        stepST constr:(F_1c818) constr:(D_1c818) (Z_to_bv 64 (sp - 24)) (getr regs 9) ltac:(sok);     (* [comment removed for export] *)
        stepST constr:(F_1c81c) constr:(D_1c81c) (Z_to_bv 64 (sp - 32)) (getr regs 18) ltac:(sok);    (* [comment removed for export] *)
        stepST constr:(F_1c820) constr:(D_1c820) (Z_to_bv 64 (sp - 40)) (getr regs 19) ltac:(sok);    (* [comment removed for export] *)
        stepST constr:(F_1c824) constr:(D_1c824) (Z_to_bv 64 (sp - 48)) (getr regs 20) ltac:(sok);    (* [comment removed for export] *)
        stepST constr:(F_1c828) constr:(D_1c828) (Z_to_bv 64 (sp - 56)) (getr regs 21) ltac:(sok);    (* [comment removed for export] *)
        stepn constr:(F_1c82c) constr:(D_1c82c);                                                      (* [comment removed for export] *)
        stepn constr:(F_1c830) constr:(D_1c830);                                                      (* [comment removed for export] *)
        stepn constr:(F_1c834) constr:(D_1c834);                                                      (* [comment removed for export] *)
        stepLD8 constr:(F_1c838) constr:(D_1c838) (Z_to_bv 64 (sp0 - 2168));                          (* [comment removed for export] *)
        stepLD8 constr:(F_1c83c) constr:(D_1c83c) (Z_to_bv 64 (sp0 - 2752 + u));                      (* [comment removed for export] *)
        stepLD8 constr:(F_1c840) constr:(D_1c840) (Z_to_bv 64 (sp0 - 2752));                          (* [comment removed for export] *)
        stepLD8 constr:(F_1c844) constr:(D_1c844) (Z_to_bv 64 (1999 - j));                            (* [comment removed for export] *)
        stepiv constr:(F_1c848) constr:(D_1c848) (Z_to_bv 64 u) ltac:(zval);  (* [comment removed for export] *)
        stepn constr:(F_1c84c) constr:(D_1c84c).                                                      (* [comment removed for export] *)
  (* [comment removed for export] *)
  Record snwJ (regs : bvmap 5 word) (ret : word) (r : bvmap 5 word) (m' : word -> option byte) (j' : Z) : Prop := SNWJ {
    Jr_sp : getr r 2 = Z_to_bv 64 (sp - 64);
    Jr_s0 : getr r 8 = Z_to_bv 64 l;
    Jr_s1 : getr r 9 = Z_to_bv 64 (sp0 - 2400);
    Jr_a0 : getr r 10 = Z_to_bv 64 (sp0 - 2080 + j');
    Jr_cs : agree_but [1; 2; 8; 9; 18; 19; 20; 21] regs r;
    Jm_fr : frame_mod m m' (snw_regions sp0 sp);
    Jm_ra : rdn SEGS m' (Z_to_bv 64 (sp - 8)) 8 = Some (X8 ret);
    Jm_s0 : rdn SEGS m' (Z_to_bv 64 (sp - 16)) 8 = Some (X8 (getr regs 8));
    Jm_s1 : rdn SEGS m' (Z_to_bv 64 (sp - 24)) 8 = Some (X8 (getr regs 9));
    Jm_s2 : rdn SEGS m' (Z_to_bv 64 (sp - 32)) 8 = Some (X8 (getr regs 18));
    Jm_s3 : rdn SEGS m' (Z_to_bv 64 (sp - 40)) 8 = Some (X8 (getr regs 19));
    Jm_s4 : rdn SEGS m' (Z_to_bv 64 (sp - 48)) 8 = Some (X8 (getr regs 20));
    Jm_s5 : rdn SEGS m' (Z_to_bv 64 (sp - 56)) 8 = Some (X8 (getr regs 21));
    Jm_buf : rdn SEGS m' (Z_to_bv 64 (sp0 - 2312)) 8 = Some (W8 (sp0 - 2752));
    Jm_ck : CKst m' sp0 j';
    Jj : (j <= j')%Z }.

  (* [comment removed for export] *)
  Lemma snw_regions_sub : forall a, outside a [(Z_to_bv 64 (sp0 - FR), FR)] -> outside a (snw_regions sp0 sp).
  Proof.
    pose proof Hcsp as Hsp0.
    intros a Ho. unfold snw_regions. cbn [outside] in Ho |- *. unfold in_rng in *. lay.
    revert Ho. unorm. intros Ho. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma snw_A : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret -> getr regs 2 = Z_to_bv 64 sp ->
    getr regs 10 = Z_to_bv 64 (sp0 - 2400) -> getr regs 11 = Z_to_bv 64 s -> getr regs 12 = Z_to_bv 64 l ->
    exists r m',
      msteps SEGS (mkst regs (rl dF_1c80c 0x1c80c) m rom) (mkst r (rl dF_1c80c 0x1c880) m' rom)
      /\ (exists j', snwI regs ret r m' j').
  Proof.
    intros regs ret Hret H1 H2 H10 H11 H12.
    pose proof Hcsp as Hsp0. lay. destruct HCK as (Hcs & Hcn & Hj).
    set (M1 := wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
               (Z_to_bv 64 (sp - 8)) (X8 ret))
               (Z_to_bv 64 (sp - 16)) (X8 (getr regs 8)))
               (Z_to_bv 64 (sp - 24)) (X8 (getr regs 9)))
               (Z_to_bv 64 (sp - 32)) (X8 (getr regs 18)))
               (Z_to_bv 64 (sp - 40)) (X8 (getr regs 19)))
               (Z_to_bv 64 (sp - 48)) (X8 (getr regs 20)))
               (Z_to_bv 64 (sp - 56)) (X8 (getr regs 21))).
    (* [comment removed for export] *)
    eapply (runs_trans1m SEGS _ (fun r => mkst r (rl dF_1c80c 0x1c858) M1 rom)
      (fun r => getr r 2 = Z_to_bv 64 (sp - 64) /\ getr r 8 = Z_to_bv 64 l /\ getr r 9 = Z_to_bv 64 (sp0 - 2400)
                /\ getr r 18 = Z_to_bv 64 s /\ getr r 19 = Z_to_bv 64 (1999 - j) /\ getr r 21 = Z_to_bv 64 (sp0 - 2168)
                /\ getr r 20 = Z_to_bv 64 (Z.min (1999 - j) u) /\ getr r 1 = ret /\ getr r 11 = Z_to_bv 64 (sp0 - 2752)
                /\ agree_but [1; 2; 8; 9; 18; 19; 20; 21] regs r)).
    { 
      destruct (Z_lt_le_dec (1999 - j) u) as [Hlt|Hge].
      + eexists. split.
        * prefixA regs ret.
          stepb_tk F_1c850 D_1c850 ltac:(cond_lia).                                 (* [comment removed for export] *)
          apply mst_refl.
        * rewrite Z.min_l by lia. postR.
      + eexists. split.
        * prefixA regs ret.
          stepb_ft F_1c850 D_1c850 ltac:(cond_lia).                                 (* [comment removed for export] *)
          stepn F_1c854 D_1c854.                                                    (* [comment removed for export] *)
          apply mst_refl.
        * rewrite Z.min_r by lia. postR. }
    cbv beta. intros r1 (R2 & R8 & R9 & R18 & R19 & R21 & R20 & R1 & R11 & RCS).
    (* [comment removed for export] *)
    assert (GM1 : mem_grows m M1) by (unfold M1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
    assert (FM1 : frame_mod m M1 (snw_regions sp0 sp)).
    { unfold M1, snw_regions.
      repeat (eapply frame_mod_wb; [ | intros x Hx Ho; cbn [outside] in Ho; unfold in_rng in *; revert Hx Ho; zlen; unorm; intros Hx Ho; lia
                                   | zlen; unorm; lia ]).
      apply frame_mod_refl. }
    assert (F1 : FRM sp0 mem0 M1).
    { eapply FRM_sub; [exact F | exact FM1 |].
      intros a Ho. unfold snw_regions. cbn [outside] in Ho |- *. unfold in_rng in *. lay. revert Ho. unorm. intros Ho. repeat split; lia. }
    assert (M1cs : rdn SEGS M1 (Z_to_bv 64 (sp0 - 2168)) 8 = Some (W8 (sp0 - 2080 + j))) by (unfold M1; rdn_solve).
    assert (M1cn : rdn SEGS M1 (Z_to_bv 64 (sp0 - 2160)) 8 = Some (W8 (1999 - j))) by (unfold M1; rdn_solve).
    assert (M1ra : rdn SEGS M1 (Z_to_bv 64 (sp - 8)) 8 = Some (X8 ret)) by (unfold M1; rdn_solve).
    assert (M1s0 : rdn SEGS M1 (Z_to_bv 64 (sp - 16)) 8 = Some (X8 (getr regs 8))) by (unfold M1; rdn_solve).
    assert (M1s1 : rdn SEGS M1 (Z_to_bv 64 (sp - 24)) 8 = Some (X8 (getr regs 9))) by (unfold M1; rdn_solve).
    assert (M1s2 : rdn SEGS M1 (Z_to_bv 64 (sp - 32)) 8 = Some (X8 (getr regs 18))) by (unfold M1; rdn_solve).
    assert (M1s3 : rdn SEGS M1 (Z_to_bv 64 (sp - 40)) 8 = Some (X8 (getr regs 19))) by (unfold M1; rdn_solve).
    assert (M1s4 : rdn SEGS M1 (Z_to_bv 64 (sp - 48)) 8 = Some (X8 (getr regs 20))) by (unfold M1; rdn_solve).
    assert (M1s5 : rdn SEGS M1 (Z_to_bv 64 (sp - 56)) 8 = Some (X8 (getr regs 21))) by (unfold M1; rdn_solve).
    assert (M1buf : rdn SEGS M1 (Z_to_bv 64 (sp0 - 2312)) 8 = Some (W8 (sp0 - 2752))) by (unfold M1; rdn_solve).
    assert (M1src : rdn SEGS M1 (Z_to_bv 64 s) (Z.to_nat l) = Some bs) by (unfold M1; rdn_solve).
    clearbody M1.
    set (k := Z.min (1999 - j) u) in *.
    assert (Hk : (0 <= k <= u /\ k <= 1999 - j)%Z) by (subst k; lia).
    destruct (Z.eq_dec k 0) as [Hk0|Hk0].
    - (* [comment removed for export] *)
      eexists. exists M1. split.
      + stepLD8 F_1c858 D_1c858 (Z_to_bv 64 (sp0 - 2080 + j)).                    (* [comment removed for export] *)
        stepb_tk F_1c85c D_1c85c ltac:(cond_lia).                                   (* [comment removed for export] *)
        apply mst_refl.
      + exists j. split; try assumption; gres; rwH; try reflexivity; try (f_equal; lia); try solve_ab.
        split; [exact M1cs | split; [exact M1cn | lia]].
    - (* [comment removed for export] *)
      destruct (rdn_defined SEGS M1 (sp0 - 2752) (Z.to_nat u) ltac:(lia) ltac:(lia)) as (bsU & HbsU & LbsU).
      { intros i Hi. apply GM1. apply Hdef. lia. }
      set (bs1 := firstn (Z.to_nat k) bsU).
      assert (Lbs1 : length bs1 = Z.to_nat k) by (subst bs1; rewrite length_firstn; lia).
      assert (Hbs1 : rdn SEGS M1 (Z_to_bv 64 (sp0 - 2752)) (length bs1) = Some bs1).
      { rewrite Lbs1. subst bs1. eapply rdn_firstn; [exact HbsU | lia]. }
      assert (MC : mcH M1 (Z_to_bv 64 (sp0 - 2080 + j)) (Z_to_bv 64 (sp0 - 2752)) k bs1).
      { split.
        - lia.
        - exact Lbs1.
        - exact Hbs1.
        - rewrite Lbs1. eapply (FRM_sok sp0 mem0 cv CTX); [exact F1 | lay; lia | lay; lia].
        - unorm. lia.
        - unorm. lia.
        - unorm. lia. }
      set (M2 := wbytes (wbytes (wbytes M1 (Z_to_bv 64 (sp0 - 2080 + j)) bs1)
                   (Z_to_bv 64 (sp0 - 2168)) (W8 (sp0 - 2080 + j + k)))
                   (Z_to_bv 64 (sp0 - 2160)) (W8 (1999 - j - k))).
      (* [comment removed for export] *)
      eapply (runs_trans1m SEGS _ (fun r => mkst r (rl dF_1c9b4 0x1c9b4) M1 rom)
        (fun r => getr r 1 = (rl dF_1c80c 0x1c868) /\ getr r 10 = Z_to_bv 64 (sp0 - 2080 + j)
                  /\ getr r 11 = Z_to_bv 64 (sp0 - 2752) /\ getr r 12 = Z_to_bv 64 k
                  /\ getr r 2 = Z_to_bv 64 (sp - 64) /\ getr r 8 = Z_to_bv 64 l /\ getr r 9 = Z_to_bv 64 (sp0 - 2400)
                  /\ getr r 18 = Z_to_bv 64 s /\ getr r 19 = Z_to_bv 64 (1999 - j) /\ getr r 21 = Z_to_bv 64 (sp0 - 2168)
                  /\ getr r 20 = Z_to_bv 64 k /\ agree_but [1; 2; 8; 9; 18; 19; 20; 21] regs r)).
      { eexists. split.
        - stepLD8 F_1c858 D_1c858 (Z_to_bv 64 (sp0 - 2080 + j)).                  (* [comment removed for export] *)
          stepb_ft F_1c85c D_1c85c ltac:(cond_lia).                                 (* [comment removed for export] *)
          stepn F_1c860 D_1c860.                                                    (* [comment removed for export] *)
          stepn F_1c864 D_1c864.                                                    (* [comment removed for export] *)
          apply mst_refl.
        - cbv beta. repeat split; gres; rwH; try reflexivity; try bveq. all: solve_ab. }
      cbv beta. intros r2 (Q1 & Q10 & Q11 & Q12 & Q2 & Q8 & Q9 & Q18 & Q19 & Q21 & Q20 & QCS).
      (* [comment removed for export] *)
      eapply (runs_trans1m SEGS _ (fun r => mkst r (rl dF_1c80c 0x1c868) (wbytes M1 (Z_to_bv 64 (sp0 - 2080 + j)) bs1) rom)
        (fun r => keeps r2 r)).
      { destruct (ref_memcpy M1 (Z_to_bv 64 (sp0 - 2080 + j)) (Z_to_bv 64 (sp0 - 2752)) k bs1 rom MC r2 (rl dF_1c80c 0x1c868)
                  ltac:(rl_ret_ok) Q1 Q10 Q11 Q12) as (r3 & RUN & K3).
        exists r3. split; [exact RUN | exact K3]. }
      cbv beta. intros r3 K3.
      assert (T2 : getr r3 2 = Z_to_bv 64 (sp - 64)) by (rewrite (K3 2%bv) by kept_reg; exact Q2).
      assert (T19 : getr r3 19 = Z_to_bv 64 (1999 - j)) by (rewrite (K3 19%bv) by kept_reg; exact Q19).
      assert (T20 : getr r3 20 = Z_to_bv 64 k) by (rewrite (K3 20%bv) by kept_reg; exact Q20).
      assert (T21 : getr r3 21 = Z_to_bv 64 (sp0 - 2168)) by (rewrite (K3 21%bv) by kept_reg; exact Q21).
      eexists. exists M2. split.
      + stepLD8 F_1c868 D_1c868 (Z_to_bv 64 (sp0 - 2080 + j)).                    (* [comment removed for export] *)
        stepLD8 F_1c86c D_1c86c (Z_to_bv 64 (1999 - j)).                          (* [comment removed for export] *)
        stepiv F_1c870 D_1c870 (Z_to_bv 64 (sp0 - 2080 + j + k)) ltac:(zval).  (* [comment removed for export] *)
        stepiv F_1c874 D_1c874 (Z_to_bv 64 (1999 - j - k)) ltac:(zval).      (* [comment removed for export] *)
        stepST F_1c878 D_1c878 (Z_to_bv 64 (sp0 - 2168)) (Z_to_bv 64 (sp0 - 2080 + j + k)) ltac:(sok).   (* [comment removed for export] *)
        stepST F_1c87c D_1c87c (Z_to_bv 64 (sp0 - 2160)) (Z_to_bv 64 (1999 - j - k)) ltac:(sok).       (* [comment removed for export] *)
        unfold M2. apply mst_refl.
      + assert (T8 : getr r3 8 = Z_to_bv 64 l) by (rewrite (K3 8%bv) by kept_reg; exact Q8).
        assert (T9 : getr r3 9 = Z_to_bv 64 (sp0 - 2400)) by (rewrite (K3 9%bv) by kept_reg; exact Q9).
        assert (T18 : getr r3 18 = Z_to_bv 64 s) by (rewrite (K3 18%bv) by kept_reg; exact Q18).
        exists (j + k)%Z.
        split; try assumption; gres; rwH; try reflexivity; try (f_equal; lia); try solve_ab; try (unfold M2; rdn_solve).
        all: match goal with
             | |- frame_mod _ _ _ =>
                 unfold M2, snw_regions;
                 repeat (eapply frame_mod_wb; [ | intros x Hx Ho; cbn [outside] in Ho; unfold in_rng in *; revert Hx Ho; zlen; rewrite ?Lbs1; unorm; intros Hx Ho; lia
                                              | zlen; rewrite ?Lbs1; unorm; lia ]);
                 exact FM1
             | |- CKst _ _ _ =>
                 unfold CKst;
                 replace (sp0 - 2080 + (j + k))%Z with (sp0 - 2080 + j + k)%Z by lia;
                 replace (1999 - (j + k))%Z with (1999 - j - k)%Z by lia;
                 split; [|split; [|lia]]; unfold M2; rdn_solve
             | |- _ => lia
             end.
  Qed.

  (* [comment removed for export] *)
  Lemma snw_B : forall regs (ret : word) r1 m1 j1,
    snwI regs ret r1 m1 j1 ->
    exists r m',
      msteps SEGS (mkst r1 (rl dF_1c80c 0x1c880) m1 rom) (mkst r (rl dF_1c80c 0x1c8b0) m' rom)
      /\ (exists j', snwJ regs ret r m' j').
  Proof.
    intros regs ret r1 m1 j1 INV.
    pose proof Hcsp as Hsp0. lay.
    destruct INV as [R2 R8 R9 R18 R19 R21 R10 RCS FM1 M1ra M1s0 M1s1 M1s2 M1s3 M1s4 M1s5 M1buf [M1cs [M1cn Hj1]] M1src Hjj].
    assert (F1 : FRM sp0 mem0 m1) by (eapply FRM_sub; [exact F | exact FM1 | apply snw_regions_sub]).
    set (k2 := Z.min (1999 - j1) l).
    assert (Hk2 : (0 <= k2 <= l /\ k2 <= 1999 - j1)%Z) by (subst k2; lia).
    (* [comment removed for export] *)
    eapply (runs_trans1m SEGS _ (fun r => mkst r (rl dF_1c80c 0x1c888) m1 rom)
      (fun r => getr r 2 = Z_to_bv 64 (sp - 64) /\ getr r 8 = Z_to_bv 64 l /\ getr r 9 = Z_to_bv 64 (sp0 - 2400)
                /\ getr r 18 = Z_to_bv 64 s /\ getr r 19 = Z_to_bv 64 k2 /\ getr r 21 = Z_to_bv 64 (sp0 - 2168)
                /\ getr r 10 = Z_to_bv 64 (sp0 - 2080 + j1)
                /\ agree_but [1; 2; 8; 9; 18; 19; 20; 21] regs r)).
    { destruct (Z_lt_le_dec (1999 - j1) l) as [Hlt|Hge].
      + eexists. split.
        * stepb_tk F_1c880 D_1c880 ltac:(cond_lia).                                 (* [comment removed for export] *)
          apply mst_refl.
        * replace k2 with (1999 - j1)%Z by (unfold k2; rewrite Z.min_l; lia). postR.
      + eexists. split.
        * stepb_ft F_1c880 D_1c880 ltac:(cond_lia).                                 (* [comment removed for export] *)
          stepn F_1c884 D_1c884.                                                    (* [comment removed for export] *)
          apply mst_refl.
        * replace k2 with l by (unfold k2; rewrite Z.min_r; lia). postR. }
    cbv beta. intros r2 (Q2 & Q8 & Q9 & Q18 & Q19 & Q21 & Q10 & QCS).
    destruct (Z.eq_dec k2 0) as [Hk0|Hk0].
    - (* [comment removed for export] *)
      eexists. exists m1. split.
      + stepb_tk F_1c888 D_1c888 ltac:(cond_lia).                                   (* [comment removed for export] *)
        apply mst_refl.
      + exists j1. split; try assumption; gres; rwH; try reflexivity; try (f_equal; lia); try solve_ab.
        split; [exact M1cs | split; [exact M1cn | lia]].
    - (* [comment removed for export] *)
      set (bs2 := firstn (Z.to_nat k2) bs).
      pose proof (rdn_length _ _ _ _ _ Hs) as Lbs.
      assert (Lbs2 : length bs2 = Z.to_nat k2) by (subst bs2; rewrite length_firstn; lia).
      assert (Hbs2 : rdn SEGS m1 (Z_to_bv 64 s) (length bs2) = Some bs2).
      { rewrite Lbs2. subst bs2. eapply rdn_firstn; [exact M1src | lia]. }
      assert (MC : mcH m1 (Z_to_bv 64 (sp0 - 2080 + j1)) (Z_to_bv 64 s) k2 bs2).
      { split.
        - lia.
        - exact Lbs2.
        - exact Hbs2.
        - rewrite Lbs2. eapply (FRM_sok sp0 mem0 cv CTX); [exact F1 | lay; lia | lay; lia].
        - unorm. lia.
        - unorm. lia.
        - unorm. lia. }
      set (M2 := wbytes (wbytes (wbytes m1 (Z_to_bv 64 (sp0 - 2080 + j1)) bs2)
                   (Z_to_bv 64 (sp0 - 2168)) (W8 (sp0 - 2080 + j1 + k2)))
                   (Z_to_bv 64 (sp0 - 2160)) (W8 (1999 - j1 - k2))).
      eapply (runs_trans1m SEGS _ (fun r => mkst r (rl dF_1c9b4 0x1c9b4) m1 rom)
        (fun r => getr r 1 = (rl dF_1c80c 0x1c898) /\ getr r 10 = Z_to_bv 64 (sp0 - 2080 + j1)
                  /\ getr r 11 = Z_to_bv 64 s /\ getr r 12 = Z_to_bv 64 k2
                  /\ getr r 2 = Z_to_bv 64 (sp - 64) /\ getr r 8 = Z_to_bv 64 l /\ getr r 9 = Z_to_bv 64 (sp0 - 2400)
                  /\ getr r 19 = Z_to_bv 64 k2 /\ getr r 21 = Z_to_bv 64 (sp0 - 2168)
                  /\ agree_but [1; 2; 8; 9; 18; 19; 20; 21] regs r)).
      { eexists. split.
        - stepb_ft F_1c888 D_1c888 ltac:(cond_lia).                                 (* [comment removed for export] *)
          stepn F_1c88c D_1c88c.                                                    (* [comment removed for export] *)
          stepn F_1c890 D_1c890.                                                    (* [comment removed for export] *)
          stepn F_1c894 D_1c894.                                                    (* [comment removed for export] *)
          apply mst_refl.
        - cbv beta. repeat split; gres; rwH; try reflexivity; try bveq. all: solve_ab. }
      cbv beta. intros r3 (T1 & T10 & T11 & T12 & T2 & T8 & T9 & T19 & T21 & TCS).
      eapply (runs_trans1m SEGS _ (fun r => mkst r (rl dF_1c80c 0x1c898) (wbytes m1 (Z_to_bv 64 (sp0 - 2080 + j1)) bs2) rom)
        (fun r => keeps r3 r)).
      { destruct (ref_memcpy m1 (Z_to_bv 64 (sp0 - 2080 + j1)) (Z_to_bv 64 s) k2 bs2 rom MC r3 (rl dF_1c80c 0x1c898)
                  ltac:(rl_ret_ok) T1 T10 T11 T12) as (r4 & RUN & K4).
        exists r4. split; [exact RUN | exact K4]. }
      cbv beta. intros r4 K4.
      assert (U2 : getr r4 2 = Z_to_bv 64 (sp - 64)) by (rewrite (K4 2%bv) by kept_reg; exact T2).
      assert (U8 : getr r4 8 = Z_to_bv 64 l) by (rewrite (K4 8%bv) by kept_reg; exact T8).
      assert (U9 : getr r4 9 = Z_to_bv 64 (sp0 - 2400)) by (rewrite (K4 9%bv) by kept_reg; exact T9).
      assert (U19 : getr r4 19 = Z_to_bv 64 k2) by (rewrite (K4 19%bv) by kept_reg; exact T19).
      assert (U21 : getr r4 21 = Z_to_bv 64 (sp0 - 2168)) by (rewrite (K4 21%bv) by kept_reg; exact T21).
      eexists. exists M2. split.
      + stepLD8 F_1c898 D_1c898 (Z_to_bv 64 (sp0 - 2080 + j1)).                   (* [comment removed for export] *)
        stepLD8 F_1c89c D_1c89c (Z_to_bv 64 (1999 - j1)).                         (* [comment removed for export] *)
        stepiv F_1c8a0 D_1c8a0 (Z_to_bv 64 (sp0 - 2080 + j1 + k2)) ltac:(zval).  (* [comment removed for export] *)
        stepiv F_1c8a4 D_1c8a4 (Z_to_bv 64 (1999 - j1 - k2)) ltac:(zval).      (* [comment removed for export] *)
        stepST F_1c8a8 D_1c8a8 (Z_to_bv 64 (sp0 - 2168)) (Z_to_bv 64 (sp0 - 2080 + j1 + k2)) ltac:(sok).   (* [comment removed for export] *)
        stepST F_1c8ac D_1c8ac (Z_to_bv 64 (sp0 - 2160)) (Z_to_bv 64 (1999 - j1 - k2)) ltac:(sok).       (* [comment removed for export] *)
        unfold M2. apply mst_refl.
      + exists (j1 + k2)%Z.
        split; try assumption; gres; rwH; try reflexivity; try (f_equal; lia); try solve_ab; try (unfold M2; rdn_solve).
        all: match goal with
             | |- frame_mod _ _ _ => unfold M2, snw_regions; frame_tac Lbs2; exact FM1
             | |- CKst _ _ _ =>
                 unfold CKst;
                 replace (sp0 - 2080 + (j1 + k2))%Z with (sp0 - 2080 + j1 + k2)%Z by lia;
                 replace (1999 - (j1 + k2))%Z with (1999 - j1 - k2)%Z by lia;
                 split; [|split; [|lia]]; unfold M2; rdn_solve
             | |- _ => lia
             end.
  Qed.

  (* [comment removed for export] *)
  Lemma snw_C : forall regs (ret : word) r1 m1 j1,
    ret_ok ret -> getr regs 1 = ret -> getr regs 2 = Z_to_bv 64 sp ->
    snwJ regs ret r1 m1 j1 ->
    exists r m',
      msteps SEGS (mkst r1 (rl dF_1c80c 0x1c8b0) m1 rom) (mkst r ret m' rom)
      /\ (keeps_cs regs r /\ getr r 10 = Z_to_bv 64 l
          /\ rdn SEGS m' (Z_to_bv 64 (sp0 - 2360)) 8 = Some (W8 (sp0 - 2752))
          /\ rdn SEGS m' (Z_to_bv 64 (sp0 - 2344)) 8 = Some (W8 (sp0 - 2752))
          /\ CKst m' sp0 j1
          /\ frame_mod m m' (snw_regions sp0 sp)).
  Proof.
    intros regs ret r1 m1 j1 Hret H1 H2 INV.
    pose proof Hcsp as Hsp0. lay.
    destruct INV as [R2 R8 R9 R10 RCS FM1 M1ra M1s0 M1s1 M1s2 M1s3 M1s4 M1s5 M1buf [M1cs [M1cn Hj1]] Hjj].
    assert (F1 : FRM sp0 mem0 m1) by (eapply FRM_sub; [exact F | exact FM1 | apply snw_regions_sub]).
    eexists. eexists. split.
    - stepST F_1c8b0 D_1c8b0 (Z_to_bv 64 (sp0 - 2080 + j1)) (Z_to_bv 64 0) ltac:(sok).   (* [comment removed for export] *)
      stepLD8 F_1c8b4 D_1c8b4 (Z_to_bv 64 (sp0 - 2752)).                           (* [comment removed for export] *)
      stepST F_1c8b8 D_1c8b8 (Z_to_bv 64 (sp0 - 2360)) (Z_to_bv 64 (sp0 - 2752)) ltac:(sok).   (* [comment removed for export] *)
      stepST F_1c8bc D_1c8bc (Z_to_bv 64 (sp0 - 2344)) (Z_to_bv 64 (sp0 - 2752)) ltac:(sok).   (* [comment removed for export] *)
      stepn F_1c8c0 D_1c8c0.                                                       (* [comment removed for export] *)
      stepLD8 F_1c8c4 D_1c8c4 ret.                                                 (* [comment removed for export] *)
      stepLD8 F_1c8c8 D_1c8c8 (getr regs 8).                                       (* [comment removed for export] *)
      stepLD8 F_1c8cc D_1c8cc (getr regs 9).                                       (* [comment removed for export] *)
      stepLD8 F_1c8d0 D_1c8d0 (getr regs 18).                                      (* [comment removed for export] *)
      stepLD8 F_1c8d4 D_1c8d4 (getr regs 19).                                      (* [comment removed for export] *)
      stepLD8 F_1c8d8 D_1c8d8 (getr regs 20).                                      (* [comment removed for export] *)
      stepLD8 F_1c8dc D_1c8dc (getr regs 21).                                      (* [comment removed for export] *)
      stepiv F_1c8e0 D_1c8e0 (Z_to_bv 64 sp) ltac:(zval).  (* [comment removed for export] *)
      stepret F_1c8e4 D_1c8e4 ret ltac:(reflexivity).
      apply mst_refl.
    - split; [|split; [|split; [|split; [|split]]]].
      + keeps_cs_fin RCS.
      + gres. exact R8.
      + rdn_solve.
      + rdn_solve.
      + split; [|split; [|lia]]; rdn_solve.
      + unfold snw_regions. frame_tac Hjj. exact FM1.
  Qed.

  (* [comment removed for export] *)
  Theorem sn_write_run : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret -> getr regs 2 = Z_to_bv 64 sp ->
    getr regs 10 = Z_to_bv 64 (sp0 - 2400) -> getr regs 11 = Z_to_bv 64 s -> getr regs 12 = Z_to_bv 64 l ->
    exists r m',
      msteps SEGS (mkst regs (rl dF_1c80c 0x1c80c) m rom) (mkst r ret m' rom)
      /\ (keeps_cs regs r /\ getr r 10 = Z_to_bv 64 l
          /\ rdn SEGS m' (Z_to_bv 64 (sp0 - 2360)) 8 = Some (W8 (sp0 - 2752))
          /\ rdn SEGS m' (Z_to_bv 64 (sp0 - 2344)) 8 = Some (W8 (sp0 - 2752))
          /\ (exists j', (j <= j')%Z /\ CKst m' sp0 j')
          /\ frame_mod m m' (snw_regions sp0 sp)).
  Proof.
    intros regs ret Hret H1 H2 H10 H11 H12.
    eapply runs_trans2; [exact (snw_A regs ret Hret H1 H2 H10 H11 H12)|].
    cbv beta. intros r1 m1 [j1 I1].
    eapply runs_trans2; [exact (snw_B regs ret r1 m1 j1 I1)|].
    cbv beta. intros r2 m2 [j2 I2].
    pose proof (Jj _ _ _ _ _ I2) as Hj2.
    destruct (snw_C regs ret r2 m2 j2 Hret H1 H2 I2) as (r3 & m3 & RUN & K & A10 & W1 & W2 & CK & FRm).
    exists r3, m3. split; [exact RUN|].
    split; [exact K|]. split; [exact A10|]. split; [exact W1|]. split; [exact W2|]. split; [|exact FRm].
    exists j2. split; [exact Hj2 | exact CK].
  Qed.
End SNW.
