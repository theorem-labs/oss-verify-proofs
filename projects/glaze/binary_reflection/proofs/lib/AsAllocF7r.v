(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRc4a OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM1. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRc4a.AsAllocFBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM1.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

Section FPGen.
Context {fx : FPState}.

Ltac regneq := apply reg_neq_of_eqb; reflexivity.
Ltac pc4 := apply bv_eq; reflexivity.

(* [comment removed for export] *)
Ltac fsb F D aa bb :=
  chain_step; [reflexivity
    | eapply MmapSim.step_sb_at with (a := aa) (b := bb);
      [exact F | reflexivity | exact D
      | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; first [reflexivity | f_equal; lia | apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_addi, at_ in G in change_no_check G' end); wd_ulia]
      | gres; rwH; reflexivity
      | first [reflexivity | apply bv_eq; unorm; reflexivity]
      | first [stk_ok | hyp_ok] ]
    | step_simpl]; vn.

(* [comment removed for export] *)
Ltac fldx F D vv :=
  chain_step; [reflexivity
    | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
      [exact F | reflexivity | exact D
      | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; try ((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; fold_at_vars); autounfold with asfr;
        repeat (wd_rdstep rd8_side)
      | apply bytes_le_to_Z_8 ]
    | step_simpl]; vn.

Section DRAINRC.
  Variables (mem rom : word -> option byte) (S ra0 s0v s1v s2v s3v a2v a3v : word).
  Variables (T len first lastq qb glen glast gqb : Z) (b1 b2 b3 : byte).
  Variable regs : bvmap 5 word.
  Variable minsz : Z.                    (* [comment removed for export] *)
  Hypothesis H1 : getr regs 1 = ra0.
  Hypothesis Hret : ret_ok ra0.
  Hypothesis H2 : getr regs 2 = at_ S (-2208).
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 (0x103f18 + 728).
  Hypothesis H11 : getr regs 11 = at_ (Z_to_bv 64 T) 80.
  Hypothesis H12 : getr regs 12 = a2v.
  Hypothesis H13 : getr regs 13 = a3v.
  Hypothesis H8 : getr regs 8 = s0v.
  Hypothesis H9 : getr regs 9 = s1v.
  Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis HT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= bv_unsigned S - 3584))%Z.
  Hypothesis Hlen : (1 <= len < 2 ^ 40)%Z.
  Hypothesis Hqb : (0 <= qb < 2 ^ 40)%Z.
  Hypothesis Hglen : (0 <= glen < 2 ^ 40)%Z.
  Hypothesis Hgqb : (0 <= gqb < 2 ^ 40)%Z.
  Hypothesis Hfirst : (0 <= first < 2 ^ 64)%Z.
  Hypothesis Hlastq : (0 <= lastq < 2 ^ 64)%Z.
  Hypothesis Hstk : store_ok ASEGS mem (at_ S (-2256)) 48 = true.     (* [comment removed for export] *)
  Hypothesis HokT : store_ok ASEGS mem (Z_to_bv 64 (T + 80)) 32 = true.
  (* [comment removed for export] *)
  Hypothesis Rlen : rdn ASEGS mem (Z_to_bv 64 (T + 80)) 8 = Some (LE8 (Z_to_bv 64 len)).
  Hypothesis Rfirst : rdn ASEGS mem (Z_to_bv 64 (T + 88)) 8 = Some (LE8 (Z_to_bv 64 first)).
  Hypothesis Rlastq : rdn ASEGS mem (Z_to_bv 64 (T + 96)) 8 = Some (LE8 (Z_to_bv 64 lastq)).
  Hypothesis Rqb : rdn ASEGS mem (Z_to_bv 64 (T + 104)) 8 = Some (LE8 (Z_to_bv 64 qb)).
  Hypothesis Rglen : rdn ASEGS mem (Z_to_bv 64 (0x103f18 + 888)) 8 = Some (LE8 (Z_to_bv 64 glen)).
  Hypothesis Rgqb : rdn ASEGS mem (Z_to_bv 64 (0x103f18 + 912)) 8 = Some (LE8 (Z_to_bv 64 gqb)).
  Hypothesis Rmax : rdn ASEGS mem (Z_to_bv 64 (0x103f18 + 792)) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 28))).
  Hypothesis Rlock : rdn ASEGS mem (Z_to_bv 64 0x104288) 4 = Some [Z_to_bv 8 0; b1; b2; b3].


  (* [comment removed for export] *)
  Ltac d7_prefix HV :=
      an F_4d7e8 D_4d7e8;                              (* [comment removed for export] *)
      fsd F_4d7ec D_4d7ec (at_ S (-2216));             (* [comment removed for export] *)
      fsd F_4d7f0 D_4d7f0 (at_ S (-2224));             (* [comment removed for export] *)
      fsd F_4d7f4 D_4d7f4 (at_ S (-2232));             (* [comment removed for export] *)
      fsd F_4d7f8 D_4d7f8 (at_ S (-2240));             (* [comment removed for export] *)
      fsd F_4d7fc D_4d7fc (at_ S (-2248));             (* [comment removed for export] *)
      an F_4d800 D_4d800;                              (* [comment removed for export] *)
      an F_4d804 D_4d804;                              (* [comment removed for export] *)
      an F_4d808 D_4d808;                              (* [comment removed for export] *)
      an F_4d80c D_4d80c;                              (* [comment removed for export] *)
      eapply msteps_trans;
      [ eapply (drain_lock_6908c _ _ rom _ (Z_to_bv 8 0) b1 b2 b3);
          [ gres; rwH; first [reflexivity | apply bv_eq; reflexivity]
          | gres; rwH; first [reflexivity | apply bv_eq; reflexivity]
          | gres; rwH; first [reflexivity | apply bv_eq; reflexivity]
          | rd_addr Rlock
          | exact HV ]
      | ];
      av F_4d82c D_4d82c (Z_to_bv 64 0) ltac:(rewrite (lock_byte0 (Z_to_bv 8 0) b1 b2 b3 _ HV); unorm; reflexivity);   (* [comment removed for export] *)
      ab_ft F_4d830 D_4d830 ltac:(condz);              (* [comment removed for export] *)
      an F_4d834 D_4d834;                              (* [comment removed for export] *)
      ab_ft F_4d838 D_4d838 ltac:(condz);              (* [comment removed for export] *)
      cld8 F_4d83c D_4d83c (Z_to_bv 64 len) Rlen;      (* [comment removed for export] *)
      ab_ft F_4d840 D_4d840 ltac:(condz);              (* [comment removed for export] *)
      cld8 F_4d844 D_4d844 (Z_to_bv 64 glen) Rglen.    (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac d7_tail_rc RL2 HV2 minsz Rmin :=
      fsd F_4d884 D_4d884 (Z_to_bv 64 (T + 80));       (* [comment removed for export] *)
      fsd F_4d888 D_4d888 (Z_to_bv 64 (T + 88));       (* [comment removed for export] *)
      fsd F_4d88c D_4d88c (Z_to_bv 64 (T + 96));       (* [comment removed for export] *)
      cld8 F_4d890 D_4d890 (Z_to_bv 64 qb) Rqb;        (* [comment removed for export] *)
      cld8 F_4d894 D_4d894 (Z_to_bv 64 gqb) Rgqb;      (* [comment removed for export] *)
      av F_4d898 D_4d898 (Z_to_bv 64 (gqb + qb)) ltac:(valz);   (* [comment removed for export] *)
      fsd F_4d89c D_4d89c (Z_to_bv 64 (0x103f18 + 912));        (* [comment removed for export] *)
      fsd F_4d8a0 D_4d8a0 (Z_to_bv 64 (T + 104));      (* [comment removed for export] *)
      afence F_4d8a4 D_4d8a4;                          (* [comment removed for export] *)
      fsb F_4d8a8 D_4d8a8 (Z_to_bv 64 0x104288) (Z_to_bv 8 0);  (* [comment removed for export] *)
      fldx F_4d8ac D_4d8ac (Z_to_bv 64 (gqb + qb));    (* [comment removed for export] *)
      cld8 F_4d8b0 D_4d8b0 (Z_to_bv 64 (2 ^ 28)) Rmax; (* [comment removed for export] *)
      ab_ft F_4d8b4 D_4d8b4 ltac:(condz);              (* [comment removed for export] *)
      an F_4d8b8 D_4d8b8;                              (* [comment removed for export] *)
      an F_4d8bc D_4d8bc;                              (* [comment removed for export] *)
      an F_4d8c0 D_4d8c0;                              (* [comment removed for export] *)
      av F_4d8c4 D_4d8c4 (Z_to_bv 64 0x104288) ltac:(valz);   (* [comment removed for export] *)
      av F_4d8c8 D_4d8c8 (Z_to_bv 64 1) ltac:(valz);          (* [comment removed for export] *)
      av F_4d8cc D_4d8cc (Z_to_bv 64 8) ltac:(valz);          (* [comment removed for export] *)
      an F_4d8d0 D_4d8d0;                              (* [comment removed for export] *)
      an F_4d8d4 D_4d8d4;                              (* [comment removed for export] *)
      eapply msteps_trans;
      [ eapply (drain_trylock_4d8d8 _ _ rom _ (Z_to_bv 8 0) b1 b2 b3);
          [ gres; rwH; first [reflexivity | apply bv_eq; reflexivity]
          | gres; rwH; first [reflexivity | apply bv_eq; vm_compute; reflexivity]
          | gres; rwH; first [reflexivity | apply bv_eq; vm_compute; reflexivity]
          | exact RL2
          | exact HV2 ]
      | ];
      an F_4d8f4 D_4d8f4;                              (* [comment removed for export] *)
      av F_4d8f8 D_4d8f8 (Z_to_bv 64 (bv_unsigned b1)) ltac:(first [apply (lock_byte1 (Z_to_bv 8 0) b1 b2 b3 _ HV2) | rewrite <- (lock_byte1 (Z_to_bv 8 0) b1 b2 b3 _ HV2); reflexivity]);  (* [comment removed for export] *)
      ab_tk F_4d8fc D_4d8fc ltac:(condz);              (* [comment removed for export] *)
      cld8 F_4d91c D_4d91c (Z_to_bv 64 minsz) Rmin;   (* [comment removed for export] *)
      fld F_4d920 D_4d920 ra0;                         (* [comment removed for export] *)
      fld F_4d924 D_4d924 s0v;                         (* [comment removed for export] *)
      fld F_4d928 D_4d928 s1v;                         (* [comment removed for export] *)
      fld F_4d92c D_4d92c s2v;                         (* [comment removed for export] *)
      fld F_4d930 D_4d930 s3v;                         (* [comment removed for export] *)
      an F_4d934 D_4d934;                              (* [comment removed for export] *)
      an F_4d938 D_4d938.                              (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[local] Definition rc_regs (r : bvmap 5 word) : Prop :=
      getr r 1 = ra0 /\ getr r 2 = at_ S (-2208) /\ getr r 10 = Z_to_bv 64 (0x103f18 + 728) /\ getr r 11 = Z_to_bv 64 minsz
      /\ getr r 12 = a2v /\ getr r 13 = a3v
      /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22
      /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25
      /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.

  (* [comment removed for export] *)
  Lemma lockword_d7n : (2 ^ 44 <= glast /\ glast + 8192 <= bv_unsigned S - 3584)%Z ->
    rdn ASEGS (fr_d7n mem S ra0 s0v s1v s2v s3v T len first lastq qb glen glast gqb b1 b2 b3) (Z_to_bv 64 0x104288) 4
      = Some [Z_to_bv 8 0; b1; b2; b3].
  Proof using HT HS.
    intros Hglast. pose proof (u64_range S) as HSr. destruct HT as (HT1 & HT2). unfold hideW in HT2. unfold hideW in HT2.
    change [Z_to_bv 8 0; b1; b2; b3] with ([Z_to_bv 8 0] ++ [b1; b2; b3]). change 4%nat with (1 + 3)%nat.
    apply rdn_cat; [| | wd_ulia].
    - (lazymatch goal with |- ?G => let G' := eval unfold fr_d7n in G in change_no_check G' end). apply rdn1_top. (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end). unorm. lia.
    - (lazymatch goal with |- ?G => let G' := eval unfold fr_d7n in G in change_no_check G' end). rewrite rdn_wbytes_out; [| rd8_side | rd8_side | rd8_side].
      repeat (rewrite rdn_wbytes_out; [| rd8_side | rd8_side | rd8_side]).
      replace (at_ (Z_to_bv 64 0x104288) (Z.of_nat 1) : word) with (at_ (Z_to_bv 64 0x104288 : word) (Z.of_nat 1)) by reflexivity.
      rewrite (rdn_wbytes_sub ASEGS _ (Z_to_bv 64 0x104288) [Z_to_bv 8 1; b1; b2; b3] 1 3); [reflexivity | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | wd_ulia_c].
  Qed.

  Lemma lockword_d7e :
    rdn ASEGS (fr_d7e mem S ra0 s0v s1v s2v s3v T len first lastq qb gqb b1 b2 b3) (Z_to_bv 64 0x104288) 4
      = Some [Z_to_bv 8 0; b1; b2; b3].
  Proof using HT HS.
    pose proof (u64_range S) as HSr. destruct HT as (HT1 & HT2). unfold hideW in HT2. unfold hideW in HT2.
    change [Z_to_bv 8 0; b1; b2; b3] with ([Z_to_bv 8 0] ++ [b1; b2; b3]). change 4%nat with (1 + 3)%nat.
    apply rdn_cat; [| | wd_ulia].
    - (lazymatch goal with |- ?G => let G' := eval unfold fr_d7e in G in change_no_check G' end). apply rdn1_top. (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end). unorm. lia.
    - (lazymatch goal with |- ?G => let G' := eval unfold fr_d7e in G in change_no_check G' end). repeat (rewrite rdn_wbytes_out; [| rd8_side | rd8_side | rd8_side]).
      replace (at_ (Z_to_bv 64 0x104288) (Z.of_nat 1) : word) with (at_ (Z_to_bv 64 0x104288 : word) (Z.of_nat 1)) by reflexivity.
      rewrite (rdn_wbytes_sub ASEGS _ (Z_to_bv 64 0x104288) [Z_to_bv 8 1; b1; b2; b3] 1 3); [reflexivity | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | wd_ulia_c].
  Qed.

  (* [comment removed for export] *)
  Lemma drain_rc_n :
    (1 <= glen)%Z -> (2 ^ 28 < gqb + qb)%Z ->
    (2 ^ 44 <= glast /\ glast + 8192 <= bv_unsigned S - 3584)%Z -> (glast + 8192 <= T \/ T + 4096 <= glast)%Z ->
    store_ok ASEGS mem (Z_to_bv 64 glast) 8 = true ->
    rdn ASEGS mem (Z_to_bv 64 (0x103f18 + 904)) 8 = Some (LE8 (Z_to_bv 64 glast)) ->
    bv_unsigned b1 = 0%Z ->
    rdn ASEGS mem (Z_to_bv 64 (0x103f18 + 800)) 8 = Some (LE8 (Z_to_bv 64 minsz)) ->
    exists r,
      msteps ASEGS (mkst regs (0x4d7f0 : word) mem rom)
                   (mkst r (0x4d994 : word)
                         (wbytes (fr_d7n mem S ra0 s0v s1v s2v s3v T len first lastq qb glen glast gqb b1 b2 b3)
                                 (Z_to_bv 64 0x104288) [Z_to_bv 8 0; Z_to_bv 8 1; b2; b3]) rom)
      /\ rc_regs r.
  Proof using Rlock Rmax Rgqb Rglen Rqb Rlastq Rfirst Rlen HokT Hstk Hgqb Hglen Hqb Hlen HT HS H19 H18 H9 H8 H13 H12 H11 H10 H2 H1.
    intros Hglen1 Hsum Hglast HglastT Hokgl Rglast Hb1 Rmin. (lazymatch goal with |- ?G => let G' := eval unfold rc_regs in G in change_no_check G' end).
    pose proof (lockword_d7n Hglast) as RL2.
    pose proof (u64_range S) as HSr. destruct HT as (HT1 & HT2). unfold hideW in HT2. unfold hideW in HT2.
    pose proof (sok_lockword mem) as Hoklk. pose proof (sok_glist mem) as Hokgq.
    assert (HV : bytes_le_to_Z [Z_to_bv 8 0; b1; b2; b3] = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z [Z_to_bv 8 0; b1; b2; b3]))).
    { pose proof (lez4_range [Z_to_bv 8 0; b1; b2; b3] eq_refl) as B. rewrite u_Z2bv by lia. reflexivity. }
    wd_eexists. split.
    - d7_prefix HV.
      ab_ft F_4d848 D_4d848 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_4d84c D_4d84c (Z_to_bv 64 glast) Rglast.  (* [comment removed for export] *)
      cld8 F_4d850 D_4d850 (Z_to_bv 64 first) Rfirst.  (* [comment removed for export] *)
      cld8 F_4d854 D_4d854 (Z_to_bv 64 lastq) Rlastq.  (* [comment removed for export] *)
      av F_4d858 D_4d858 (Z_to_bv 64 (glen + len)) ltac:(valz).   (* [comment removed for export] *)
      fsd F_4d85c D_4d85c (Z_to_bv 64 glast);          (* [comment removed for export] *)
      fsd F_4d860 D_4d860 (Z_to_bv 64 (0x103f18 + 888)).          (* [comment removed for export] *)
      fsd F_4d864 D_4d864 (Z_to_bv 64 (0x103f18 + 904)).          (* [comment removed for export] *)
      an F_4d868 D_4d868.                              (* [comment removed for export] *)
      d7_tail_rc RL2 HV minsz Rmin.
      change (wbytes (wbytes _ _ _) (Z_to_bv 64 0x104288) [Z_to_bv 8 0; Z_to_bv 8 1; b2; b3])
        with (wbytes (fr_d7n mem S ra0 s0v s1v s2v s3v T len first lastq qb glen glast gqb b1 b2 b3) (Z_to_bv 64 0x104288) [Z_to_bv 8 0; Z_to_bv 8 1; b2; b3]).
      rewrite ?at_0. wd_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  Lemma drain_rc_e :
    glen = 0%Z -> (2 ^ 28 < gqb + qb)%Z ->
    bv_unsigned b1 = 0%Z ->
    rdn ASEGS mem (Z_to_bv 64 (0x103f18 + 800)) 8 = Some (LE8 (Z_to_bv 64 minsz)) ->
    exists r,
      msteps ASEGS (mkst regs (0x4d7f0 : word) mem rom)
                   (mkst r (0x4d994 : word)
                         (wbytes (fr_d7e mem S ra0 s0v s1v s2v s3v T len first lastq qb gqb b1 b2 b3)
                                 (Z_to_bv 64 0x104288) [Z_to_bv 8 0; Z_to_bv 8 1; b2; b3]) rom)
      /\ rc_regs r.
  Proof using Rlock Rmax Rgqb Rglen Rqb Rlastq Rfirst Rlen HokT Hstk Hgqb Hglen Hqb Hlen HT HS H19 H18 H9 H8 H13 H12 H11 H10 H2 H1.
    intros Hglen0 Hsum Hb1 Rmin. (lazymatch goal with |- ?G => let G' := eval unfold rc_regs in G in change_no_check G' end).
    pose proof lockword_d7e as RL2.
    pose proof (u64_range S) as HSr. destruct HT as (HT1 & HT2). unfold hideW in HT2. unfold hideW in HT2.
    pose proof (sok_lockword mem) as Hoklk. pose proof (sok_glist mem) as Hokgq.
    assert (HV : bytes_le_to_Z [Z_to_bv 8 0; b1; b2; b3] = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z [Z_to_bv 8 0; b1; b2; b3]))).
    { pose proof (lez4_range [Z_to_bv 8 0; b1; b2; b3] eq_refl) as B. rewrite u_Z2bv by lia. reflexivity. }
    wd_eexists. split.
    - d7_prefix HV.
      subst glen.
      ab_tk F_4d848 D_4d848 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_4d86c D_4d86c (Z_to_bv 64 lastq) Rlastq.  (* [comment removed for export] *)
      fsd F_4d870 D_4d870 (Z_to_bv 64 (0x103f18 + 904)).          (* [comment removed for export] *)
      cld8 F_4d874 D_4d874 (Z_to_bv 64 first) Rfirst.  (* [comment removed for export] *)
      fsd F_4d878 D_4d878 (Z_to_bv 64 (0x103f18 + 896)).          (* [comment removed for export] *)
      cld8 F_4d87c D_4d87c (Z_to_bv 64 len) Rlen.      (* [comment removed for export] *)
      fsd F_4d880 D_4d880 (Z_to_bv 64 (0x103f18 + 888)).          (* [comment removed for export] *)
      d7_tail_rc RL2 HV minsz Rmin.
      change (wbytes (wbytes _ _ _) (Z_to_bv 64 0x104288) [Z_to_bv 8 0; Z_to_bv 8 1; b2; b3])
        with (wbytes (fr_d7e mem S ra0 s0v s1v s2v s3v T len first lastq qb gqb b1 b2 b3) (Z_to_bv 64 0x104288) [Z_to_bv 8 0; Z_to_bv 8 1; b2; b3]).
      rewrite ?at_0. wd_refl.
    - post.
  Qed.
End DRAINRC.
End FPGen.
