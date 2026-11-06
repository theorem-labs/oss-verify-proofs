(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.


(* [comment removed for export] *)
Section FPGen1.
Context {fx : FPState}.

Definition mmemset_words : list (bv 32) :=
  [W_f56e8; W_f56ec; W_f56f0; W_f56f4; W_f56f8; W_f56fc; W_f5700; W_f5704; W_f5708; W_f570c; W_f5710; W_f5714; W_f5718; W_f571c; W_f5720; W_f5724; W_f5728; W_f572c; W_f5730; W_f5734; W_f5738; W_f573c; W_f5740; W_f5744; W_f5748; W_f574c; W_f5750; W_f5754; W_f5758; W_f575c; W_f5760; W_f5764; W_f5768; W_f576c; W_f5770; W_f5774; W_f5778; W_f577c; W_f5780; W_f5784; W_f5788; W_f578c; W_f5790; W_f5794; W_f5798; W_f579c; W_f57a0; W_f57a4; W_f57a8; W_f57ac; W_f57b0; W_f57b4; W_f57b8; W_f57bc; W_f57c0; W_f57c4; W_f57c8; W_f57cc; W_f57d0; W_f57d4; W_f57d8; W_f57dc]%list.

(* [comment removed for export] *)
End FPGen1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Section FPGen2.
Context {fx : FPState}.


Section MMEMSET.
  Variable segs : list Segment.
  Variable base : word.
  Hypothesis HCODE : code_at segs base 0 mmemset_words.

  (* [comment removed for export] *)
  Lemma Fo_000 : fetch_word segs (at_ base 0) = Some W_f56e8.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 0 _ HCODE eq_refl). Qed.
  Lemma Fo_004 : fetch_word segs (at_ base 4) = Some W_f56ec.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 1 _ HCODE eq_refl). Qed.
  Lemma Fo_008 : fetch_word segs (at_ base 8) = Some W_f56f0.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 2 _ HCODE eq_refl). Qed.
  Lemma Fo_00c : fetch_word segs (at_ base 12) = Some W_f56f4.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 3 _ HCODE eq_refl). Qed.
  Lemma Fo_010 : fetch_word segs (at_ base 16) = Some W_f56f8.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 4 _ HCODE eq_refl). Qed.
  Lemma Fo_014 : fetch_word segs (at_ base 20) = Some W_f56fc.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 5 _ HCODE eq_refl). Qed.
  Lemma Fo_018 : fetch_word segs (at_ base 24) = Some W_f5700.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 6 _ HCODE eq_refl). Qed.
  Lemma Fo_01c : fetch_word segs (at_ base 28) = Some W_f5704.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 7 _ HCODE eq_refl). Qed.
  Lemma Fo_020 : fetch_word segs (at_ base 32) = Some W_f5708.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 8 _ HCODE eq_refl). Qed.
  Lemma Fo_024 : fetch_word segs (at_ base 36) = Some W_f570c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 9 _ HCODE eq_refl). Qed.
  Lemma Fo_028 : fetch_word segs (at_ base 40) = Some W_f5710.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 10 _ HCODE eq_refl). Qed.
  Lemma Fo_02c : fetch_word segs (at_ base 44) = Some W_f5714.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 11 _ HCODE eq_refl). Qed.
  Lemma Fo_030 : fetch_word segs (at_ base 48) = Some W_f5718.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 12 _ HCODE eq_refl). Qed.
  Lemma Fo_034 : fetch_word segs (at_ base 52) = Some W_f571c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 13 _ HCODE eq_refl). Qed.
  Lemma Fo_038 : fetch_word segs (at_ base 56) = Some W_f5720.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 14 _ HCODE eq_refl). Qed.
  Lemma Fo_03c : fetch_word segs (at_ base 60) = Some W_f5724.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 15 _ HCODE eq_refl). Qed.
  Lemma Fo_040 : fetch_word segs (at_ base 64) = Some W_f5728.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 16 _ HCODE eq_refl). Qed.
  Lemma Fo_044 : fetch_word segs (at_ base 68) = Some W_f572c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 17 _ HCODE eq_refl). Qed.
  Lemma Fo_048 : fetch_word segs (at_ base 72) = Some W_f5730.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 18 _ HCODE eq_refl). Qed.
  Lemma Fo_04c : fetch_word segs (at_ base 76) = Some W_f5734.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 19 _ HCODE eq_refl). Qed.
  Lemma Fo_050 : fetch_word segs (at_ base 80) = Some W_f5738.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 20 _ HCODE eq_refl). Qed.
  Lemma Fo_054 : fetch_word segs (at_ base 84) = Some W_f573c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 21 _ HCODE eq_refl). Qed.
  Lemma Fo_058 : fetch_word segs (at_ base 88) = Some W_f5740.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 22 _ HCODE eq_refl). Qed.
  Lemma Fo_05c : fetch_word segs (at_ base 92) = Some W_f5744.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 23 _ HCODE eq_refl). Qed.
  Lemma Fo_060 : fetch_word segs (at_ base 96) = Some W_f5748.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 24 _ HCODE eq_refl). Qed.
  Lemma Fo_064 : fetch_word segs (at_ base 100) = Some W_f574c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 25 _ HCODE eq_refl). Qed.
  Lemma Fo_068 : fetch_word segs (at_ base 104) = Some W_f5750.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 26 _ HCODE eq_refl). Qed.
  Lemma Fo_06c : fetch_word segs (at_ base 108) = Some W_f5754.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 27 _ HCODE eq_refl). Qed.
  Lemma Fo_070 : fetch_word segs (at_ base 112) = Some W_f5758.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 28 _ HCODE eq_refl). Qed.
  Lemma Fo_074 : fetch_word segs (at_ base 116) = Some W_f575c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 29 _ HCODE eq_refl). Qed.
  Lemma Fo_078 : fetch_word segs (at_ base 120) = Some W_f5760.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 30 _ HCODE eq_refl). Qed.
  Lemma Fo_07c : fetch_word segs (at_ base 124) = Some W_f5764.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 31 _ HCODE eq_refl). Qed.
  Lemma Fo_080 : fetch_word segs (at_ base 128) = Some W_f5768.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 32 _ HCODE eq_refl). Qed.
  Lemma Fo_084 : fetch_word segs (at_ base 132) = Some W_f576c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 33 _ HCODE eq_refl). Qed.
  Lemma Fo_088 : fetch_word segs (at_ base 136) = Some W_f5770.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 34 _ HCODE eq_refl). Qed.
  Lemma Fo_08c : fetch_word segs (at_ base 140) = Some W_f5774.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 35 _ HCODE eq_refl). Qed.
  Lemma Fo_090 : fetch_word segs (at_ base 144) = Some W_f5778.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 36 _ HCODE eq_refl). Qed.
  Lemma Fo_094 : fetch_word segs (at_ base 148) = Some W_f577c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 37 _ HCODE eq_refl). Qed.
  Lemma Fo_098 : fetch_word segs (at_ base 152) = Some W_f5780.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 38 _ HCODE eq_refl). Qed.
  Lemma Fo_09c : fetch_word segs (at_ base 156) = Some W_f5784.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 39 _ HCODE eq_refl). Qed.
  Lemma Fo_0a0 : fetch_word segs (at_ base 160) = Some W_f5788.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 40 _ HCODE eq_refl). Qed.
  Lemma Fo_0a4 : fetch_word segs (at_ base 164) = Some W_f578c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 41 _ HCODE eq_refl). Qed.
  Lemma Fo_0a8 : fetch_word segs (at_ base 168) = Some W_f5790.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 42 _ HCODE eq_refl). Qed.
  Lemma Fo_0ac : fetch_word segs (at_ base 172) = Some W_f5794.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 43 _ HCODE eq_refl). Qed.
  Lemma Fo_0b0 : fetch_word segs (at_ base 176) = Some W_f5798.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 44 _ HCODE eq_refl). Qed.
  Lemma Fo_0b4 : fetch_word segs (at_ base 180) = Some W_f579c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 45 _ HCODE eq_refl). Qed.
  Lemma Fo_0b8 : fetch_word segs (at_ base 184) = Some W_f57a0.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 46 _ HCODE eq_refl). Qed.
  Lemma Fo_0bc : fetch_word segs (at_ base 188) = Some W_f57a4.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 47 _ HCODE eq_refl). Qed.
  Lemma Fo_0c0 : fetch_word segs (at_ base 192) = Some W_f57a8.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 48 _ HCODE eq_refl). Qed.
  Lemma Fo_0c4 : fetch_word segs (at_ base 196) = Some W_f57ac.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 49 _ HCODE eq_refl). Qed.
  Lemma Fo_0c8 : fetch_word segs (at_ base 200) = Some W_f57b0.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 50 _ HCODE eq_refl). Qed.
  Lemma Fo_0cc : fetch_word segs (at_ base 204) = Some W_f57b4.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 51 _ HCODE eq_refl). Qed.
  Lemma Fo_0d0 : fetch_word segs (at_ base 208) = Some W_f57b8.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 52 _ HCODE eq_refl). Qed.
  Lemma Fo_0d4 : fetch_word segs (at_ base 212) = Some W_f57bc.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 53 _ HCODE eq_refl). Qed.
  Lemma Fo_0d8 : fetch_word segs (at_ base 216) = Some W_f57c0.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 54 _ HCODE eq_refl). Qed.
  Lemma Fo_0dc : fetch_word segs (at_ base 220) = Some W_f57c4.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 55 _ HCODE eq_refl). Qed.
  Lemma Fo_0e0 : fetch_word segs (at_ base 224) = Some W_f57c8.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 56 _ HCODE eq_refl). Qed.
  Lemma Fo_0e4 : fetch_word segs (at_ base 228) = Some W_f57cc.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 57 _ HCODE eq_refl). Qed.
  Lemma Fo_0e8 : fetch_word segs (at_ base 232) = Some W_f57d0.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 58 _ HCODE eq_refl). Qed.
  Lemma Fo_0ec : fetch_word segs (at_ base 236) = Some W_f57d4.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 59 _ HCODE eq_refl). Qed.
  Lemma Fo_0f0 : fetch_word segs (at_ base 240) = Some W_f57d8.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 60 _ HCODE eq_refl). Qed.
  Lemma Fo_0f4 : fetch_word segs (at_ base 244) = Some W_f57dc.
  Proof using HCODE. exact (code_at_get segs base 0 mmemset_words 61 _ HCODE eq_refl). Qed.

(* [comment removed for export] *)
#[local] Ltac stepat L F D vv tac :=
  chain_step; [reflexivity | eapply L with (v := vv); [exact F | reflexivity | exact D | reflexivity | tac] | step_simpl]; vn.
(* [comment removed for export] *)
#[local] Ltac siv F D v tac := stepiv F D v tac; vn.

Section Walk.
  Variable mem0 : word -> option byte.
  Variables d cv ret : word.
  Variable n : Z.
  Variable rom : word -> option byte.
  Hypothesis Hn : (0 <= n)%Z.
  Hypothesis Hnw : (bv_unsigned d + n < 2 ^ 64)%Z.
  Hypothesis Hok : store_ok segs mem0 d (Z.to_nat n) = true.
  Hypothesis Hret : ret_ok ret.

  #[local] Abbreviation CF := (cfill mem0 d n (cbyte cv)).
  #[local] Abbreviation PC o := (at_ base o).

  (* [comment removed for export] *)
  #[local] Ltac msb F D oo :=
    chain_step; [reflexivity
      | eapply (cf_sb segs mem0 d n cv Hnw Hok) with (o := oo);
        [exact F | reflexivity | exact D
        | gres; rwH; rewrite ?at_addi; reflexivity
        | imm_norm; lia
        | gres; rwH; reflexivity
        | lia | lia]
      | step_simpl]; vn.
  #[local] Ltac msw F D oo :=
    chain_step; [reflexivity
      | eapply (cf_sw segs mem0 d n cv Hnw Hok) with (o := oo);
        [exact F | reflexivity | exact D
        | gres; rwH; rewrite ?at_addi; reflexivity
        | imm_norm; lia
        | gres; rwH; reflexivity
        | apply wleb4_c32
        | lia | lia]
      | step_simpl]; vn.
  #[local] Ltac msd F D oo :=
    chain_step; [reflexivity
      | eapply (cf_sd segs mem0 d n cv Hnw Hok) with (o := oo);
        [exact F | reflexivity | exact D
        | gres; rwH; rewrite ?at_addi; reflexivity
        | imm_norm; lia
        | gres; rwH; reflexivity
        | apply wleb8_c64
        | lia | lia]
      | step_simpl]; vn.
  (* [comment removed for export] *)
  #[local] Ltac mret := aret Fo_0f4 D_f57dc ret.
  (* [comment removed for export] *)
  #[local] Ltac post := repeat split; gres; rwH; try reflexivity; solve_ms_agree.

  (* [comment removed for export] *)
  Definition L2 : list (Z * Z) := [(n-1,1); (0,1)]%Z.
  Definition L6 : list (Z * Z) := [(n-2,1); (n-3,1); (2,1); (1,1); (n-1,1); (0,1)]%Z.
  Definition L8 : list (Z * Z) := [(n-4,1); (3,1); (n-2,1); (n-3,1); (2,1); (1,1); (n-1,1); (0,1)]%Z.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma A_exit0 : forall regs,
    getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
    (n = 0)%Z ->
    exists regs',
      msteps segs (mkst regs (PC 0) (CF []) rom) (mkst regs' ret (CF []) rom)
      /\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
  Proof using Hret Hn HCODE.
    intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd.
    wd_eexists. split.
    - ab_tk Fo_000 D_f56e8 ltac:(condz).          (* [comment removed for export] *)
      mret.
      wd_refl.
    - post.
  Qed.

  Lemma A_exit2 : forall regs,
    getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
    (1 <= n <= 2)%Z ->
    exists regs',
      msteps segs (mkst regs (PC 0) (CF []) rom) (mkst regs' ret (CF L2) rom)
      /\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
  Proof using Hret Hok Hnw Hn HCODE.
    intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd.
    wd_eexists. split.
    - ab_ft Fo_000 D_f56e8 ltac:(condz).          (* [comment removed for export] *)
      msb Fo_004 D_f56ec 0%Z.                         (* [comment removed for export] *)
      siv Fo_008 D_f56f0 (at_ d n) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).  (* [comment removed for export] *)
      an Fo_00c D_f56f4.                           (* [comment removed for export] *)
      msb Fo_010 D_f56f8 (n-1)%Z.                     (* [comment removed for export] *)
      ab_tk Fo_014 D_f56fc ltac:(condz).          (* [comment removed for export] *)
      mret.
      wd_refl.
    - post.
  Qed.

  Lemma A_exit6 : forall regs,
    getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
    (3 <= n <= 6)%Z ->
    exists regs',
      msteps segs (mkst regs (PC 0) (CF []) rom) (mkst regs' ret (CF L6) rom)
      /\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
  Proof using Hret Hok Hnw Hn HCODE.
    intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd.
    wd_eexists. split.
    - ab_ft Fo_000 D_f56e8 ltac:(condz).
      msb Fo_004 D_f56ec 0%Z.
      siv Fo_008 D_f56f0 (at_ d n) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).
      an Fo_00c D_f56f4.
      msb Fo_010 D_f56f8 (n-1)%Z.
      ab_ft Fo_014 D_f56fc ltac:(condz).
      msb Fo_018 D_f5700 1%Z.                         (* [comment removed for export] *)
      msb Fo_01c D_f5704 2%Z.                         (* [comment removed for export] *)
      an Fo_020 D_f5708.                           (* [comment removed for export] *)
      msb Fo_024 D_f570c (n-3)%Z.                     (* [comment removed for export] *)
      msb Fo_028 D_f5710 (n-2)%Z.                     (* [comment removed for export] *)
      ab_tk Fo_02c D_f5714 ltac:(condz).          (* [comment removed for export] *)
      mret.
      wd_refl.
    - post.
  Qed.

  Lemma A_exit8 : forall regs,
    getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
    (7 <= n <= 8)%Z ->
    exists regs',
      msteps segs (mkst regs (PC 0) (CF []) rom) (mkst regs' ret (CF L8) rom)
      /\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
  Proof using Hret Hok Hnw Hn HCODE.
    intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd.
    wd_eexists. split.
    - ab_ft Fo_000 D_f56e8 ltac:(condz).
      msb Fo_004 D_f56ec 0%Z.
      siv Fo_008 D_f56f0 (at_ d n) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).
      an Fo_00c D_f56f4.
      msb Fo_010 D_f56f8 (n-1)%Z.
      ab_ft Fo_014 D_f56fc ltac:(condz).
      msb Fo_018 D_f5700 1%Z.
      msb Fo_01c D_f5704 2%Z.
      an Fo_020 D_f5708.
      msb Fo_024 D_f570c (n-3)%Z.
      msb Fo_028 D_f5710 (n-2)%Z.
      ab_ft Fo_02c D_f5714 ltac:(condz).
      msb Fo_030 D_f5718 3%Z.                         (* [comment removed for export] *)
      an Fo_034 D_f571c.                           (* [comment removed for export] *)
      msb Fo_038 D_f5720 (n-4)%Z.                     (* [comment removed for export] *)
      ab_tk Fo_03c D_f5724 ltac:(condz).          (* [comment removed for export] *)
      mret.
      wd_refl.
    - post.
  Qed.

  Lemma A_cont : forall regs,
    getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
    (9 <= n)%Z ->
    exists regs',
      msteps segs (mkst regs (PC 0) (CF []) rom) (mkst regs' (PC 0x40) (CF L8) rom)
      /\ getr regs' 10 = at_ d 0 /\ getr regs' 11 = cv /\ getr regs' 12 = Z_to_bv 64 n
      /\ getr regs' 13 = at_ d n /\ getr regs' 15 = Z_to_bv 64 9 /\ getr regs' 1 = ret
      /\ ms_agree regs regs'.
  Proof using Hok Hnw Hn HCODE.
    intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd.
    wd_eexists. split.
    - ab_ft Fo_000 D_f56e8 ltac:(condz).
      msb Fo_004 D_f56ec 0%Z.
      siv Fo_008 D_f56f0 (at_ d n) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).
      an Fo_00c D_f56f4.
      msb Fo_010 D_f56f8 (n-1)%Z.
      ab_ft Fo_014 D_f56fc ltac:(condz).
      msb Fo_018 D_f5700 1%Z.
      msb Fo_01c D_f5704 2%Z.
      an Fo_020 D_f5708.
      msb Fo_024 D_f570c (n-3)%Z.
      msb Fo_028 D_f5710 (n-2)%Z.
      ab_ft Fo_02c D_f5714 ltac:(condz).
      msb Fo_030 D_f5718 3%Z.
      an Fo_034 D_f571c.
      msb Fo_038 D_f5720 (n-4)%Z.
      ab_ft Fo_03c D_f5724 ltac:(condz).          (* [comment removed for export] *)
      wd_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Section Aligned.
    Variables k n1 : Z.
    Hypothesis Hk : (0 <= k <= 3)%Z.
    Hypothesis Hn1 : (n - k - 3 <= n1 <= n - k)%Z.
    Hypothesis Hkv : v_andi (v_subw (Z_to_bv 64 0) d) 3 = Z_to_bv 64 k.
    Hypothesis Hn1v : v_andi (Z_to_bv 64 (n - k)) (-4) = Z_to_bv 64 n1.

    Definition LB : list (Z * Z) := ((k+n1-4,4) :: (k,4) :: L8)%Z.
    Definition LC : list (Z * Z) := ((k+n1-8,4) :: (k+n1-12,4) :: (k+8,4) :: (k+4,4) :: LB)%Z.
    Definition LD (s4 : Z) : list (Z * Z) :=
      ((k+n1-16,4) :: (k+n1-20,4) :: (k+n1-24,4) :: (k+n1-28,4)
        :: (k+24,4) :: (k+20,4) :: (k+16,4) :: (k+12,4) :: LC)%Z.

    #[local] Ltac blockB :=
      an Fo_040 D_f5728;                           (* [comment removed for export] *)
      an Fo_044 D_f572c;                           (* [comment removed for export] *)
      an Fo_048 D_f5730;                           (* [comment removed for export] *)
      siv Fo_04c D_f5734 (Z_to_bv 64 k) ltac:(gres; rwH; imm_norm; rewrite ?at_0; exact Hkv);   (* [comment removed for export] *)
      an Fo_050 D_f5738;                           (* [comment removed for export] *)
      siv Fo_054 D_f573c (Z_to_bv 64 (n - k)) ltac:(gres; rwH; apply ms_v_sub_ZZ; lia);          (* [comment removed for export] *)
      siv Fo_058 D_f5740 (at_ d k) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia);  (* [comment removed for export] *)
      an Fo_05c D_f5744;                           (* [comment removed for export] *)
      siv Fo_060 D_f5748 (Z_to_bv 64 n1) ltac:(gres; rwH; imm_norm; exact Hn1v);              (* [comment removed for export] *)
      stepat ms_step_mulhu_at Fo_064 D_f574c (c32 cv) ltac:(gres; rwH; apply mulhu_c32; unorm; reflexivity);  (* [comment removed for export] *)
      msw Fo_068 D_f5750 k;                           (* [comment removed for export] *)
      siv Fo_06c D_f5754 (at_ d (k + n1)) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; reflexivity);  (* [comment removed for export] *)
      msw Fo_070 D_f5758 (k + n1 - 4)%Z.              (* [comment removed for export] *)

    Lemma B_exit : forall regs,
      getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n ->
      getr regs 13 = at_ d n -> getr regs 15 = Z_to_bv 64 9 -> getr regs 1 = ret ->
      (9 <= n)%Z -> (n1 < 9)%Z ->
      exists regs',
        msteps segs (mkst regs (PC 0x40) (CF L8) rom) (mkst regs' ret (CF LB) rom)
        /\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
    Proof using Hn1v Hkv Hn1 Hk Hret Hok Hnw HCODE.
      intros regs H10 H11 H12 H13 H15 H1 Hn9 Hc. pose proof (u64_range d) as Hd.
      wd_eexists. split.
      - blockB.
        ab_tk Fo_074 D_f575c ltac:(condz).        (* [comment removed for export] *)
        mret.
        wd_refl.
      - post.
    Qed.

    Lemma B_cont : forall regs,
      getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n ->
      getr regs 13 = at_ d n -> getr regs 15 = Z_to_bv 64 9 -> getr regs 1 = ret ->
      (9 <= n)%Z -> (9 <= n1)%Z ->
      exists regs',
        msteps segs (mkst regs (PC 0x40) (CF L8) rom) (mkst regs' (PC 0x78) (CF LB) rom)
        /\ getr regs' 10 = at_ d 0 /\ getr regs' 11 = at_ d k /\ getr regs' 12 = c32 cv
        /\ getr regs' 13 = at_ d (k + n1) /\ getr regs' 14 = Z_to_bv 64 n1 /\ getr regs' 1 = ret
        /\ ms_agree regs regs'.
    Proof using Hn1v Hkv Hn1 Hk Hok Hnw HCODE.
      intros regs H10 H11 H12 H13 H15 H1 Hn9 Hc. pose proof (u64_range d) as Hd.
      wd_eexists. split.
      - blockB.
        ab_ft Fo_074 D_f575c ltac:(condz).        (* [comment removed for export] *)
        wd_refl.
      - post.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)

    #[local] Ltac blockC :=
      msw Fo_078 D_f5760 (k + 4)%Z;                   (* [comment removed for export] *)
      msw Fo_07c D_f5764 (k + 8)%Z;                   (* [comment removed for export] *)
      an Fo_080 D_f5768;                           (* [comment removed for export] *)
      msw Fo_084 D_f576c (k + n1 - 12)%Z;             (* [comment removed for export] *)
      msw Fo_088 D_f5770 (k + n1 - 8)%Z.              (* [comment removed for export] *)

    Lemma C_exit : forall regs,
      getr regs 10 = at_ d 0 -> getr regs 11 = at_ d k -> getr regs 12 = c32 cv ->
      getr regs 13 = at_ d (k + n1) -> getr regs 14 = Z_to_bv 64 n1 -> getr regs 1 = ret ->
      (9 <= n)%Z -> (12 <= n1)%Z -> (n1 < 25)%Z ->
      exists regs',
        msteps segs (mkst regs (PC 0x78) (CF LB) rom) (mkst regs' ret (CF LC) rom)
        /\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
    Proof using Hn1 Hk Hret Hok Hnw HCODE.
      intros regs H10 H11 H12 H13 H14 H1 Hn9 Hn1' Hc. pose proof (u64_range d) as Hd.
      wd_eexists. split.
      - blockC.
        ab_tk Fo_08c D_f5774 ltac:(condz).        (* [comment removed for export] *)
        mret.
        wd_refl.
      - post.
    Qed.

    Lemma C_cont : forall regs,
      getr regs 10 = at_ d 0 -> getr regs 11 = at_ d k -> getr regs 12 = c32 cv ->
      getr regs 13 = at_ d (k + n1) -> getr regs 14 = Z_to_bv 64 n1 -> getr regs 1 = ret ->
      (9 <= n)%Z -> (25 <= n1)%Z ->
      exists regs',
        msteps segs (mkst regs (PC 0x78) (CF LB) rom) (mkst regs' (PC 0x90) (CF LC) rom)
        /\ getr regs' 10 = at_ d 0 /\ getr regs' 11 = at_ d k /\ getr regs' 12 = c32 cv
        /\ getr regs' 13 = at_ d (k + n1) /\ getr regs' 14 = Z_to_bv 64 n1 /\ getr regs' 1 = ret
        /\ ms_agree regs regs'.
    Proof using Hn1 Hk Hok Hnw HCODE.
      intros regs H10 H11 H12 H13 H14 H1 Hn9 Hc. pose proof (u64_range d) as Hd.
      wd_eexists. split.
      - blockC.
        ab_ft Fo_08c D_f5774 ltac:(condz).        (* [comment removed for export] *)
        wd_refl.
      - post.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)

    Section D.
      Variable s4 : Z.
      Hypothesis Hs4 : (s4 = 0 \/ s4 = 4)%Z.
      Hypothesis Hs4v : v_andi (at_ d k) 4 = Z_to_bv 64 s4.

      #[local] Ltac blockD :=
        msw Fo_090 D_f5778 (k + 12)%Z;                (* [comment removed for export] *)
        msw Fo_094 D_f577c (k + 16)%Z;                (* [comment removed for export] *)
        msw Fo_098 D_f5780 (k + 20)%Z;                (* [comment removed for export] *)
        msw Fo_09c D_f5784 (k + 24)%Z;                (* [comment removed for export] *)
        siv Fo_0a0 D_f5788 (Z_to_bv 64 s4) ltac:(gres; rwH; imm_norm; exact Hs4v);          (* [comment removed for export] *)
        an Fo_0a4 D_f578c;                         (* [comment removed for export] *)
        siv Fo_0a8 D_f5790 (Z_to_bv 64 (s4 + 24)) ltac:(gres; rwH; imm_norm; apply ms_v_addi_Z; lia);  (* [comment removed for export] *)
        siv Fo_0ac D_f5794 (Z_to_bv 64 (n1 - s4 - 24)) ltac:(gres; rwH; rewrite ms_v_sub_ZZ by lia; f_equal; lia);  (* [comment removed for export] *)
        msw Fo_0b0 D_f5798 (k + n1 - 28)%Z;           (* [comment removed for export] *)
        msw Fo_0b4 D_f579c (k + n1 - 24)%Z;           (* [comment removed for export] *)
        msw Fo_0b8 D_f57a0 (k + n1 - 20)%Z;           (* [comment removed for export] *)
        msw Fo_0bc D_f57a4 (k + n1 - 16)%Z.           (* [comment removed for export] *)

      Lemma D_exit : forall regs,
        getr regs 10 = at_ d 0 -> getr regs 11 = at_ d k -> getr regs 12 = c32 cv ->
        getr regs 13 = at_ d (k + n1) -> getr regs 14 = Z_to_bv 64 n1 -> getr regs 1 = ret ->
        (9 <= n)%Z -> (28 <= n1)%Z -> (n1 - s4 - 24 < 32)%Z ->
        exists regs',
          msteps segs (mkst regs (PC 0x90) (CF LC) rom) (mkst regs' ret (CF (LD s4)) rom)
          /\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
      Proof using Hs4v Hs4 Hn1 Hk Hret Hok Hnw HCODE.
        intros regs H10 H11 H12 H13 H14 H1 Hn9 Hn1' Hc. pose proof (u64_range d) as Hd.
        wd_eexists. split.
        - blockD.
          ab_tk Fo_0c0 D_f57a8 ltac:(condz).      (* [comment removed for export] *)
          mret.
          wd_refl.
        - post.
      Qed.

      Lemma D_cont : forall regs,
        getr regs 10 = at_ d 0 -> getr regs 11 = at_ d k -> getr regs 12 = c32 cv ->
        getr regs 13 = at_ d (k + n1) -> getr regs 14 = Z_to_bv 64 n1 -> getr regs 1 = ret ->
        (9 <= n)%Z -> (28 <= n1)%Z -> (32 <= n1 - s4 - 24)%Z ->
        exists regs',
          msteps segs (mkst regs (PC 0x90) (CF LC) rom) (mkst regs' (PC 0xc4) (CF (LD s4)) rom)
          /\ getr regs' 10 = at_ d 0 /\ getr regs' 11 = at_ d k /\ getr regs' 12 = c32 cv
          /\ getr regs' 14 = Z_to_bv 64 (n1 - s4 - 24) /\ getr regs' 15 = Z_to_bv 64 (s4 + 24)
          /\ getr regs' 1 = ret /\ ms_agree regs regs'.
      Proof using Hs4v Hs4 Hn1 Hk Hok Hnw HCODE.
        intros regs H10 H11 H12 H13 H14 H1 Hn9 Hn1' Hc. pose proof (u64_range d) as Hd.
        wd_eexists. split.
        - blockD.
          ab_ft Fo_0c0 D_f57a8 ltac:(condz).      (* [comment removed for export] *)
          wd_refl.
        - post.
      Qed.

      (* [comment removed for export] *)
      (* [comment removed for export] *)
      (* [comment removed for export] *)

      Lemma E_run : forall regs L,
        getr regs 10 = at_ d 0 -> getr regs 11 = at_ d k -> getr regs 12 = c32 cv ->
        getr regs 14 = Z_to_bv 64 (n1 - s4 - 24) -> getr regs 15 = Z_to_bv 64 (s4 + 24) -> getr regs 1 = ret ->
        (9 <= n)%Z -> (28 <= n1)%Z ->
        exists regs',
          msteps segs (mkst regs (PC 0xc4) (CF L) rom) (mkst regs' (PC 0xd8) (CF L) rom)
          /\ getr regs' 10 = at_ d 0 /\ getr regs' 11 = at_ d (k + s4 + 24) /\ getr regs' 12 = c64 cv
          /\ getr regs' 13 = Z_to_bv 64 31 /\ getr regs' 14 = Z_to_bv 64 (n1 - s4 - 24)
          /\ getr regs' 1 = ret /\ ms_agree regs regs'.
      Proof using Hs4 HCODE.
        intros regs L H10 H11 H12 H14 H15 H1 Hn9 Hn1'. pose proof (u64_range d) as Hd.
        wd_eexists. split.
        - siv Fo_0c4 D_f57ac (c32h cv) ltac:(gres; rwH; imm_norm; apply slli32_c32).             (* [comment removed for export] *)
          siv Fo_0c8 D_f57b0 (at_ d (k + s4 + 24)) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).  (* [comment removed for export] *)
          siv Fo_0cc D_f57b4 (c32 cv) ltac:(gres; rwH; imm_norm; apply srli32_c32h);             (* [comment removed for export] *)
          stepat ms_step_or_at Fo_0d0 D_f57b8 (c64 cv) ltac:(gres; rwH; apply or_c64).                 (* [comment removed for export] *)
          an Fo_0d4 D_f57bc.                       (* [comment removed for export] *)
          wd_refl.
        - post.
      Qed.
    End D.
  End Aligned.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[local] Ltac ms_cov_eq :=
    intros i Hi; rewrite !ms_cov_cons;
    match goal with |- _ = ?rhs => match rhs with context [ms_cov ?L i] => destruct (ms_cov L i) end end;
    rewrite ?orb_true_r, ?orb_false_r; [reflexivity|];
    apply eq_true_iff_eq; rewrite !orb_true_iff, !ms_inb_true; lia.

  (* [comment removed for export] *)
  Lemma loop_run : forall (q : nat) regs L a r,
    getr regs 10 = at_ d 0 -> getr regs 11 = at_ d a -> getr regs 12 = c64 cv ->
    getr regs 13 = Z_to_bv 64 31 -> getr regs 14 = Z_to_bv 64 r -> getr regs 1 = ret ->
    (0 <= a)%Z -> (a + r <= n)%Z ->
    (32 * (Z.of_nat q + 1) <= r < 32 * (Z.of_nat q + 1) + 32)%Z ->
    exists regs',
      msteps segs (mkst regs (PC 0xd8) (CF L) rom)
                   (mkst regs' (PC 0xf4) (CF ((a, 32 * (Z.of_nat q + 1))%Z :: L)) rom)
      /\ getr regs' 10 = at_ d 0 /\ getr regs' 1 = ret /\ ms_agree regs regs'.
  Proof using Hok Hnw HCODE.
    induction q as [|q IH]; intros regs L a r H10 H11 H12 H13 H14 H1 Ha Har Hq;
      pose proof (u64_range d) as Hd.
    - (* [comment removed for export] *)
      wd_eexists. split.
      + msd Fo_0d8 D_f57c0 a.                         (* [comment removed for export] *)
        msd Fo_0dc D_f57c4 (a + 8)%Z.                 (* [comment removed for export] *)
        msd Fo_0e0 D_f57c8 (a + 16)%Z.                (* [comment removed for export] *)
        msd Fo_0e4 D_f57cc (a + 24)%Z.                (* [comment removed for export] *)
        siv Fo_0e8 D_f57d0 (Z_to_bv 64 (r - 32)) ltac:(gres; rwH; imm_norm; rewrite ms_v_addi_Z by lia; f_equal; lia).  (* [comment removed for export] *)
        siv Fo_0ec D_f57d4 (at_ d (a + 32)) ltac:(gres; rwH; imm_norm; rewrite at_addi; reflexivity).               (* [comment removed for export] *)
        ab_ft Fo_0f0 D_f57d8 ltac:(condz).        (* [comment removed for export] *)
        replace (CF ((a + 24, 8) :: (a + 16, 8) :: (a + 8, 8) :: (a, 8) :: L))%Z
          with (CF ((a, 32 * (Z.of_nat 0 + 1))%Z :: L)) by (apply cfill_ext; ms_cov_eq).
        wd_refl.
      + post.
    - eapply (runs_trans segs _
                (fun rg => mkst rg (PC 0xd8) (CF ((a + 24, 8) :: (a + 16, 8) :: (a + 8, 8) :: (a, 8) :: L))%Z rom)
                (fun rg => getr rg 10 = at_ d 0 /\ getr rg 11 = at_ d (a + 32) /\ getr rg 12 = c64 cv
                           /\ getr rg 13 = Z_to_bv 64 31 /\ getr rg 14 = Z_to_bv 64 (r - 32) /\ getr rg 1 = ret
                           /\ ms_agree regs rg)).
      + cbv beta. wd_eexists. split.
        * msd Fo_0d8 D_f57c0 a.
          msd Fo_0dc D_f57c4 (a + 8)%Z.
          msd Fo_0e0 D_f57c8 (a + 16)%Z.
          msd Fo_0e4 D_f57cc (a + 24)%Z.
          siv Fo_0e8 D_f57d0 (Z_to_bv 64 (r - 32)) ltac:(gres; rwH; imm_norm; rewrite ms_v_addi_Z by lia; f_equal; lia).
          siv Fo_0ec D_f57d4 (at_ d (a + 32)) ltac:(gres; rwH; imm_norm; rewrite at_addi; reflexivity).
          ab_tk Fo_0f0 D_f57d8 ltac:(condz).      (* [comment removed for export] *)
          wd_refl.
        * post.
      + cbv beta. intros r1 (R10 & R11 & R12 & R13 & R14 & R1 & AG).
        destruct (IH r1 ((a + 24, 8) :: (a + 16, 8) :: (a + 8, 8) :: (a, 8) :: L)%Z (a + 32)%Z (r - 32)%Z
                    R10 R11 R12 R13 R14 R1 ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P10 & P1 & AG2).
        exists r2. split.
        * replace (CF ((a, 32 * (Z.of_nat (S q) + 1))%Z :: L))
            with (CF ((a + 32, 32 * (Z.of_nat q + 1))%Z :: ((a + 24, 8) :: (a + 16, 8) :: (a + 8, 8) :: (a, 8) :: L)%Z))
            by (apply cfill_ext; ms_cov_eq).
          exact RUN.
        * repeat split; try assumption. eapply ms_agree_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma ret_run : forall regs (M : word -> option byte),
    getr regs 1 = ret ->
    exists regs',
      msteps segs (mkst regs (PC 0xf4) M rom) (mkst regs' ret M rom)
      /\ regs' = regs.
  Proof using Hret HCODE.
    intros regs M H1. wd_eexists. split.
    - mret. wd_refl.
    - reflexivity.
  Qed.

End Walk.

(* [comment removed for export] *)
#[local] Ltac solve_incl :=
  let x := fresh "x" in let H := fresh "H" in
  intros x H; cbn [In] in H;
  repeat (destruct H as [<-|H]; [(lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat first [left; reflexivity | right] |]);
  destruct H.


Section Summary.
  Variable mem0 : word -> option byte.
  Variables d cv ret : word.
  Variable n : Z.
  Variable rom : word -> option byte.
  Hypothesis Hn : (0 <= n)%Z.
  Hypothesis Hnw : (bv_unsigned d + n < 2 ^ 64)%Z.
  Hypothesis Hok : store_ok segs mem0 d (Z.to_nat n) = true.
  Hypothesis Hret : ret_ok ret.

  #[local] Abbreviation CF := (cfill mem0 d n (cbyte cv)).
  #[local] Abbreviation PC o := (at_ base o).

  (* [comment removed for export] *)
  #[local] Ltac cover L' :=
    apply (cfill_full_chain mem0 d n (cbyte cv) Hn Hnw _ L');
    [ (lazymatch goal with |- ?G => let G' := eval unfold L2, L6, L8, LB, LC, LD in G in change_no_check G' end); solve_incl
    | (lazymatch goal with |- ?G => let G' := eval cbn [ms_chain] in G in change_no_check G' end); lia ].

  Theorem memset_summary : forall regs,
    getr regs 10 = d -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
    exists regs',
      msteps segs (mkst regs (at_ base 0) mem0 rom)
                   (mkst regs' ret (wbytes mem0 d (repeat (cbyte cv) (Z.to_nat n))) rom)
      /\ getr regs' 10 = d /\ ms_agree regs regs'.
  Proof using Hret Hok Hnw Hn HCODE.
    intros regs H10 H11 H12 H1.
    pose proof (u64_range d) as Hd.
    rewrite <- (at_0 d) in H10.
    replace (mkst regs (PC 0) mem0 rom) with (mkst regs (PC 0) (CF []) rom) by (rewrite cfill_nil; reflexivity).
    (* [comment removed for export] *)
    assert (FIN : forall regs' (M : word -> option byte),
              M = wbytes mem0 d (repeat (cbyte cv) (Z.to_nat n)) ->
              msteps segs (mkst regs (PC 0) (CF []) rom) (mkst regs' ret M rom) ->
              getr regs' 10 = at_ d 0 -> ms_agree regs regs' ->
              exists regs'',
                msteps segs (mkst regs (PC 0) (CF []) rom)
                       (mkst regs'' ret (wbytes mem0 d (repeat (cbyte cv) (Z.to_nat n))) rom)
                /\ getr regs'' 10 = d /\ ms_agree regs regs'').
    { intros regs' M -> RUN P10 AG. exists regs'. rewrite at_0 in P10. auto. }
    destruct (Z.lt_ge_cases n 9) as [Hsmall|Hn9].
    { (* [comment removed for export] *)
      destruct (Z.eq_dec n 0) as [Hz|Hnz].
      { destruct (A_exit0 mem0 d cv ret n rom Hn Hret regs H10 H11 H12 H1 Hz) as (r1 & RUN & P10 & AG).
        eapply (FIN r1); try eassumption.
        rewrite cfill_nil. rewrite Hz. reflexivity. }
      destruct (Z.lt_ge_cases n 3) as [H3|H3].
      { destruct (A_exit2 mem0 d cv ret n rom Hn Hnw Hok Hret regs H10 H11 H12 H1 ltac:(lia)) as (r1 & RUN & P10 & AG).
        eapply (FIN r1); try eassumption. cover ([(0,1); (n-1,1)]%Z). }
      destruct (Z.lt_ge_cases n 7) as [H7|H7].
      { destruct (A_exit6 mem0 d cv ret n rom Hn Hnw Hok Hret regs H10 H11 H12 H1 ltac:(lia)) as (r1 & RUN & P10 & AG).
        eapply (FIN r1); try eassumption. cover ([(0,1); (1,1); (2,1); (n-3,1); (n-2,1); (n-1,1)]%Z). }
      destruct (A_exit8 mem0 d cv ret n rom Hn Hnw Hok Hret regs H10 H11 H12 H1 ltac:(lia)) as (r1 & RUN & P10 & AG).
      eapply (FIN r1); try eassumption.
      cover ([(0,1); (1,1); (2,1); (3,1); (n-4,1); (n-3,1); (n-2,1); (n-1,1)]%Z). }
    (* [comment removed for export] *)
    destruct (A_cont mem0 d cv ret n rom Hn Hnw Hok regs H10 H11 H12 H1 Hn9)
      as (r1 & RUN1 & Q10 & Q11 & Q12 & Q13 & Q15 & Q1 & AG1).
    (* [comment removed for export] *)
    set (k := ((- bv_unsigned d) mod 4)%Z).
    pose proof (neg_mod4_range (bv_unsigned d)) as Hk. fold k in Hk.
    pose proof (negw_and3 d) as Hkv. fold k in Hkv.
    set (n1 := (n - k - (n - k) mod 4)%Z).
    set (m1 := ((n - k) / 4)%Z).
    pose proof (Z.div_mod (n - k) 4 ltac:(lia)) as Hdm.
    pose proof (Z.mod_pos_bound (n - k) 4 ltac:(lia)) as Hmb.
    assert (Hm1 : (4 * m1 = n1)%Z) by (subst n1 m1; lia).
    assert (Hn1 : (n - k - 3 <= n1 <= n - k)%Z) by (subst n1; lia).
    pose proof (andi_m4 (n - k) ltac:(lia)) as Hn1v. fold n1 in Hn1v.
    clearbody n1 m1. clear Hdm Hmb.
    destruct (Z.lt_ge_cases n1 9) as [HB|HB].
    { (* [comment removed for export] *)
      destruct (B_exit mem0 d cv ret n rom Hnw Hok Hret k n1 Hk Hn1 Hkv Hn1v r1 Q10 Q11 Q12 Q13 Q15 Q1 Hn9 HB)
        as (r2 & RUN2 & P10 & AG2).
      eapply (FIN r2); [| eapply msteps_trans; [exact RUN1 | exact RUN2] | exact P10 | eapply ms_agree_trans; eassumption].
      cover ([(0,1); (1,1); (2,1); (3,1); (k,4); (k+n1-4,4); (n-4,1); (n-3,1); (n-2,1); (n-1,1)]%Z). }
    destruct (B_cont mem0 d cv ret n rom Hnw Hok k n1 Hk Hn1 Hkv Hn1v r1 Q10 Q11 Q12 Q13 Q15 Q1 Hn9 HB)
      as (r2 & RUN2 & S10 & S11 & S12 & S13 & S14 & S1 & AG2).
    destruct (Z.lt_ge_cases n1 25) as [HC|HC].
    { destruct (C_exit mem0 d cv ret n rom Hnw Hok Hret k n1 Hk Hn1 r2 S10 S11 S12 S13 S14 S1 Hn9 ltac:(lia) HC)
        as (r3 & RUN3 & P10 & AG3).
      eapply (FIN r3); [| eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]]
                       | exact P10 | repeat (eapply ms_agree_trans; [eassumption|]); first [assumption | apply ms_agree_refl]].
      cover ([(0,1); (1,1); (2,1); (3,1); (k,4); (k+4,4); (k+8,4); (k+n1-12,4); (k+n1-8,4); (k+n1-4,4);
              (n-4,1); (n-3,1); (n-2,1); (n-1,1)]%Z). }
    destruct (C_cont mem0 d cv ret n rom Hnw Hok k n1 Hk Hn1 r2 S10 S11 S12 S13 S14 S1 Hn9 HC)
      as (r3 & RUN3 & T10 & T11 & T12 & T13 & T14 & T1 & AG3).
    destruct (andi_4_cases (at_ d k)) as (s4 & Hs4v & Hs4).
    destruct (Z.lt_ge_cases (n1 - s4 - 24) 32) as [HD|HD].
    { destruct (D_exit mem0 d cv ret n rom Hnw Hok Hret k n1 Hk Hn1 s4 Hs4 Hs4v r3 T10 T11 T12 T13 T14 T1 Hn9 ltac:(lia) HD)
        as (r4 & RUN4 & P10 & AG4).
      eapply (FIN r4); [| eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 |
                            eapply msteps_trans; [exact RUN3 | exact RUN4]]]
                       | exact P10 | repeat (eapply ms_agree_trans; [eassumption|]); first [assumption | apply ms_agree_refl]].
      cover ([(0,1); (1,1); (2,1); (3,1); (k,4); (k+4,4); (k+8,4); (k+12,4); (k+16,4); (k+20,4); (k+24,4);
              (k+n1-28,4); (k+n1-24,4); (k+n1-20,4); (k+n1-16,4); (k+n1-12,4); (k+n1-8,4); (k+n1-4,4);
              (n-4,1); (n-3,1); (n-2,1); (n-1,1)]%Z). }
    destruct (D_cont mem0 d cv ret n rom Hnw Hok k n1 Hk Hn1 s4 Hs4 Hs4v r3 T10 T11 T12 T13 T14 T1 Hn9 ltac:(lia) HD)
      as (r4 & RUN4 & U10 & U11 & U12 & U14 & U15 & U1 & AG4).
    destruct (E_run mem0 d cv ret n rom k n1 s4 Hs4 r4 (LD n k n1 s4) U10 U11 U12 U14 U15 U1 Hn9 ltac:(lia))
      as (r5 & RUN5 & V10 & V11 & V12 & V13 & V14 & V1 & AG5).
    (* [comment removed for export] *)
    set (r := (n1 - s4 - 24)%Z) in *.
    set (q := Z.to_nat (r / 32 - 1)).
    assert (Hq : (32 * (Z.of_nat q + 1) <= r < 32 * (Z.of_nat q + 1) + 32)%Z).
    { subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
      pose proof (Z.div_mod r 32 ltac:(lia)). pose proof (Z.mod_pos_bound r 32 ltac:(lia)). lia. }
    destruct (loop_run mem0 d cv ret n rom Hnw Hok q r5 (LD n k n1 s4) (k + s4 + 24)%Z r
                V10 V11 V12 V13 V14 V1 ltac:(lia) ltac:(lia) Hq)
      as (r6 & RUN6 & W10 & W1 & AG6).
    destruct (ret_run ret rom Hret r6 (CF (((k + s4 + 24)%Z, (32 * (Z.of_nat q + 1))%Z) :: LD n k n1 s4)) W1)
      as (r7 & RUN7 & ->).
    eapply (FIN r6); [| eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 |
                          eapply msteps_trans; [exact RUN3 | eapply msteps_trans; [exact RUN4 |
                          eapply msteps_trans; [exact RUN5 | eapply msteps_trans; [exact RUN6 | exact RUN7]]]]]]
                     | exact W10 | repeat (eapply ms_agree_trans; [eassumption|]); first [assumption | apply ms_agree_refl]].
    cover ([(0,1); (1,1); (2,1); (3,1); (k,4); (k+4,4); (k+8,4); (k+12,4); (k+16,4); (k+20,4); (k+24,4);
            (k+s4+24, 32 * (Z.of_nat q + 1));
            (k+n1-28,4); (k+n1-24,4); (k+n1-20,4); (k+n1-16,4); (k+n1-12,4); (k+n1-8,4); (k+n1-4,4);
            (n-4,1); (n-3,1); (n-2,1); (n-1,1)]%Z).
  Qed.

End Summary.

End MMEMSET.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End FPGen2.


From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Section FPGen3.
Context {fx : FPState}.


Definition asan_memset_entry : word := 0xf56e4.

Lemma asan_memset_code :
  code_at Asan.M.loaded_segments asan_memset_entry 0 mmemset_words.
Proof using. (lazymatch goal with |- ?G => let G' := eval unfold mmemset_words in G in change_no_check G' end). code_at_vm. Qed.

Theorem asan_memset : forall (mem0 : word -> option byte) (d cv ret : word) (n : Z) (rom : word -> option byte) regs,
  (0 <= n)%Z -> (bv_unsigned d + n < 2 ^ 64)%Z ->
  store_ok Asan.M.loaded_segments mem0 d (Z.to_nat n) = true -> ret_ok ret ->
  getr regs 10 = d -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
  exists regs',
    msteps Asan.M.loaded_segments
           (mkst regs asan_memset_entry mem0 rom)
           (mkst regs' ret (wbytes mem0 d (repeat (cbyte cv) (Z.to_nat n))) rom)
    /\ getr regs' 10 = d /\ ms_agree regs regs'.
Proof using.
  intros mem0 d cv ret n rom regs Hn Hnw Hok Hret.
  rewrite <- (at_0 asan_memset_entry).
  apply (memset_summary _ _ asan_memset_code mem0 d cv ret n rom Hn Hnw Hok Hret).
Qed.

End FPGen3.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
