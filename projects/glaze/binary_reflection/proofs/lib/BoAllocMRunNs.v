(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.glaze.binary_reflection.images.AsanUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.InstrEnc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module Bo_code_88dc0_89a68.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- @eq (option (bv 32)) (fetch_word ?s ?a) ?r =>
      apply (@bool_decide_eq_true_1 _ (@decide_rel (option (bv 32)) (option (bv 32)) (@eq (option (bv 32))) (@option_eq_dec (bv 32) (bv_eq_dec 32)) (fetch_word s a) r));
      vm_cast_no_check (@eq_refl bool true)
  | |- @eq (option (prod instr Z)) (decode_any ?w) ?r =>
      (* [comment removed for export] *)
      apply (@InstrEnc.enc_opt_inj (decode_any w) r);
      vm_cast_no_check (@eq_refl (list Z) (InstrEnc.enc_opt r))
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_89288 : bv 32 := @BV 32 0xff010113%Z I.
Lemma F_89288 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x89288%Z I : word) = Some W_89288.
Proof. vm_refl. Qed.
Lemma D_89288 : decode_any W_89288 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4080%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8928c : bv 32 := @BV 32 0x00113423%Z I.
Lemma F_8928c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8928c%Z I : word) = Some W_8928c.
Proof. vm_refl. Qed.
Lemma D_8928c : decode_any W_8928c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89290 : bv 32 := @BV 32 0x728640ef%Z I.
Lemma F_89290 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x89290%Z I : word) = Some W_89290.
Proof. vm_refl. Qed.
Lemma D_89290 : decode_any W_89290 = Some (Jal (@BV 5 1%Z I) (@BV 21 411432%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89294 : bv 32 := @BV 32 0x00c00593%Z I.
Lemma F_89294 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x89294%Z I : word) = Some W_89294.
Proof. vm_refl. Qed.
Lemma D_89294 : decode_any W_89294 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89298 : bv 32 := @BV 32 0x00b52023%Z I.
Lemma F_89298 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x89298%Z I : word) = Some W_89298.
Proof. vm_refl. Qed.
Lemma D_89298 : decode_any W_89298 = Some (Store SZ4 (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8929c : bv 32 := @BV 32 0x00813083%Z I.
Lemma F_8929c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8929c%Z I : word) = Some W_8929c.
Proof. vm_refl. Qed.
Lemma D_8929c : decode_any W_8929c = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_892a0 : bv 32 := @BV 32 0x01010113%Z I.
Lemma F_892a0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x892a0%Z I : word) = Some W_892a0.
Proof. vm_refl. Qed.
Lemma D_892a0 : decode_any W_892a0 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_892a4 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_892a4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x892a4%Z I : word) = Some W_892a4.
Proof. vm_refl. Qed.
Lemma D_892a4 : decode_any W_892a4 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.
End Bo_code_88dc0_89a68.
Require Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_ed07c_ed9d0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Module BoAllocM8n.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c.BoAllocM8q OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT.Bo_code_7ab0c_7b3f4 Bo_code_88dc0_89a68 OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_ed07c_ed9d0.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section RF0.
  Variables (M rom : word -> option byte) (sp ra s0v s1v : word).          (* [comment removed for export] *)
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ sp (-32).
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis S_ra : rdn BSEGS M (at_ sp (-8)) 8 = Some (LE8 ra).
  Hypothesis S_s0 : rdn BSEGS M (at_ sp (-16)) 8 = Some (LE8 s0v).
  Hypothesis S_s1 : rdn BSEGS M (at_ sp (-24)) 8 = Some (LE8 s1v).
  Lemma rf_ret0 :
    exists r, msteps BSEGS (mkst regs (0x5147c : word) M rom) (mkst r ra M rom)
      /\ getr r 10 = Z_to_bv 64 0 /\ getr r 2 = sp /\ getr r 1 = ra /\ getr r 8 = s0v /\ getr r 9 = s1v
      /\ regs_agree (fun i : reg => In i [1; 2; 8; 9]) regs r.
  Proof using S_s1 S_s0 S_ra Hret H10 H2.
    pose proof (u64_range sp) as Hspr.
    wd_eexists. split.
    - ab_tk F_5147c D_5147c ltac:(condz).              (* [comment removed for export] *)
      cld8 F_51484 D_51484 ra S_ra.                    (* [comment removed for export] *)
      cld8 F_51488 D_51488 s0v S_s0.                   (* [comment removed for export] *)
      cld8 F_5148c D_5148c s1v S_s1.                   (* [comment removed for export] *)
      an F_51490 D_51490.                              (* [comment removed for export] *)
      aret F_51494 D_51494 ra.                         (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.
End RF0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CB0.
  Variables (M rom : word -> option byte) (sp ra s0v s1v s2v s3v s4v : word).   (* [comment removed for export] *)
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ sp (-48).
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0.
  Hypothesis H18 : getr regs 18 = Z_to_bv 64 8.                            (* [comment removed for export] *)
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis S_ra : rdn BSEGS M (at_ sp (-8)) 8 = Some (LE8 ra).
  Hypothesis S_s0 : rdn BSEGS M (at_ sp (-16)) 8 = Some (LE8 s0v).
  Hypothesis S_s1 : rdn BSEGS M (at_ sp (-24)) 8 = Some (LE8 s1v).
  Hypothesis S_s2 : rdn BSEGS M (at_ sp (-32)) 8 = Some (LE8 s2v).
  Hypothesis S_s3 : rdn BSEGS M (at_ sp (-40)) 8 = Some (LE8 s3v).
  Hypothesis S_s4 : rdn BSEGS M (at_ sp (-48)) 8 = Some (LE8 s4v).
  Lemma cb_ret0 :
    exists r, msteps BSEGS (mkst regs (0x50f9c : word) M rom) (mkst r ra M rom)
      /\ getr r 10 = Z_to_bv 64 0 /\ getr r 2 = sp /\ getr r 1 = ra
      /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v
      /\ regs_agree (fun i : reg => In i [1; 2; 8; 9; 11; 13; 18; 19; 20]) regs r.
  Proof using S_s4 S_s3 S_s2 S_s1 S_s0 S_ra Hret H18 H10 H2.
    pose proof (u64_range sp) as Hspr.
    wd_eexists. split.
    - ab_tk F_50f9c D_50f9c ltac:(condz).              (* [comment removed for export] *)
      an F_50fb4 D_50fb4.                              (* [comment removed for export] *)
      an F_50fb8 D_50fb8.                              (* [comment removed for export] *)
      ab_ft F_50fbc D_50fbc ltac:(condz).              (* [comment removed for export] *)
      an F_50fc0 D_50fc0.                              (* [comment removed for export] *)
      cld8 F_50ef0 D_50ef0 ra S_ra.                    (* [comment removed for export] *)
      cld8 F_50ef4 D_50ef4 s0v S_s0.                   (* [comment removed for export] *)
      cld8 F_50ef8 D_50ef8 s1v S_s1.                   (* [comment removed for export] *)
      cld8 F_50efc D_50efc s2v S_s2.                   (* [comment removed for export] *)
      cld8 F_50f00 D_50f00 s3v S_s3.                   (* [comment removed for export] *)
      cld8 F_50f04 D_50f04 s4v S_s4.                   (* [comment removed for export] *)
      an F_50f08 D_50f08.                              (* [comment removed for export] *)
      aret F_50f0c D_50f0c ra.                         (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.
End CB0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition am_null_mem (M : word -> option byte) (sp tp : word) : word -> option byte :=
  wbytes (wbytes (wbytes M (Z_to_bv 64 0x190420) [Z_to_bv 8 1]) (at_ sp 120) (LE8 (Z_to_bv 64 0x4c580))) (at_ tp (-164)) (LE4 12).

Section AMNULL.
  Variables (M rom : word -> option byte) (sp tp rai s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v s0' : word).
  (* [comment removed for export] *)
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H4 : getr regs 4 = tp.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 160 <= 2 ^ 47)%Z.
  Hypothesis Htp : (AIMGLO + 164 <= U tp /\ U tp <= AIMGHI)%Z.
  Hypothesis Hret : ret_ok rai.
  Hypothesis C_mrn : rdn BSEGS M (Z_to_bv 64 0x190421) 1 = Some [Z_to_bv 8 1].
  Hypothesis SOK_oom : store_ok BSEGS M (Z_to_bv 64 0x190420) 1 = true.
  Hypothesis SOK_err : store_ok BSEGS M (at_ tp (-164)) 4 = true.
  Hypothesis SOK_stk : store_ok BSEGS M (at_ sp 120) 8 = true.
  Hypothesis SL : forall (k : Z) (v : word),
    In (k, v) [(120, Z_to_bv 64 0x4c564); (112, s0v); (104, s1v); (96, s2v); (88, s3v); (80, s4v); (72, s5v); (64, s6v); (56, s7v); (48, s8v);
               (40, s9v); (32, s10v); (24, s11v); (136, rai); (128, s0')]%Z -> rdn BSEGS M (at_ sp k) 8 = Some (LE8 v).

  Ltac sld F D vv k :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := LE8 vv) (v := vv);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi, ?at_at; fold_at_vars; rewrite ?at_addi, ?at_at; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold am_null_mem in G in change_no_check G' end);
          repeat (rewrite wc_rdn_wbytes_out3; [ | rd8_side ]);
          first [apply (SL k vv) | replace (at_ sp _) with (at_ sp k) by (f_equal; lia); apply (SL k vv)]; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto
        | apply bytes_le_to_Z_8]
      | step_simpl]; vn.

  Lemma am_null :
    exists r, msteps BSEGS (mkst regs (0x4c834 : word) M rom) (mkst r rai (am_null_mem M sp tp) rom)
      /\ getr r 10 = Z_to_bv 64 0 /\ getr r 2 = at_ sp 144 /\ getr r 1 = rai
      /\ getr r 8 = s0' /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v /\ getr r 21 = s5v
      /\ getr r 22 = s6v /\ getr r 23 = s7v /\ getr r 24 = s8v /\ getr r 25 = s9v /\ getr r 26 = s10v /\ getr r 27 = s11v
      /\ regs_agree (fun i : reg => In i [1; 2; 8; 9; 10; 11; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]) regs r.
  Proof using SL SOK_stk SOK_err SOK_oom C_mrn Hret Htp Hsp H10 H4 H2 s0v.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range tp) as Htpr. destruct Htp as [TP1 TP2].
    wd_eexists. split.
    - an F_4c834 D_4c834.                              (* [comment removed for export] *)
      ab_tk F_4c838 D_4c838 ltac:(condz).              (* [comment removed for export] *)
      an F_4c904 D_4c904.                              (* [comment removed for export] *)
      an F_7b3ac D_7b3ac.                              (* [comment removed for export] *)
      an F_7b3b0 D_7b3b0.                              (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply MmapSim.step_sb_at with (a := Z_to_bv 64 0x190420) (b := Z_to_bv 8 1);
          [exact F_7b3b4 | reflexivity | exact D_7b3b4
          | gres; rwH; apply bv_eq; vm_compute; reflexivity
          | gres; rwH; reflexivity
          | apply bv_eq; vm_compute; reflexivity
          | exact SOK_oom ]
        | step_simpl]; vn.                             (* [comment removed for export] *)
      rt F_7b3b8 D_7b3b8.                              (* [comment removed for export] *)
      an F_4c908 D_4c908.                              (* [comment removed for export] *)
      an F_7b3bc D_7b3bc.                              (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 1);
          [exact F_7b3c0 | reflexivity | exact D_7b3c0
          | gres; rwH;
            lazymatch goal with |- rdn _ _ ?a _ = _ => replace a with (Z_to_bv 64 0x190421 : word) by (apply bv_eq; vm_compute; reflexivity) end;
            rewrite rdn_wbytes_out; [exact C_mrn | rd8_side | rd8_side | rd8_side ] ]
        | step_simpl]; vn.                             (* [comment removed for export] *)
      an F_7b3c4 D_7b3c4.                              (* [comment removed for export] *)
      rt F_7b3c8 D_7b3c8.                              (* [comment removed for export] *)
      ab_tk F_4c90c D_4c90c ltac:(first [condz | vm_compute; reflexivity]).   (* [comment removed for export] *)
      an F_4cde4 D_4cde4.                              (* [comment removed for export] *)
      an F_4cde8 D_4cde8.                              (* [comment removed for export] *)
      an F_4ccc8 D_4ccc8.                              (* [comment removed for export] *)
      sld F_4cccc D_4cccc (Z_to_bv 64 0x4c564) 120%Z.  (* [comment removed for export] *)
      sld F_4ccd0 D_4ccd0 s0v 112%Z. sld F_4ccd4 D_4ccd4 s1v 104%Z. sld F_4ccd8 D_4ccd8 s2v 96%Z. sld F_4ccdc D_4ccdc s3v 88%Z.
      sld F_4cce0 D_4cce0 s4v 80%Z. sld F_4cce4 D_4cce4 s5v 72%Z. sld F_4cce8 D_4cce8 s6v 64%Z. sld F_4ccec D_4ccec s7v 56%Z.
      sld F_4ccf0 D_4ccf0 s8v 48%Z. sld F_4ccf4 D_4ccf4 s9v 40%Z. sld F_4ccf8 D_4ccf8 s10v 32%Z. sld F_4ccfc D_4ccfc s11v 24%Z.
      an F_4cd00 D_4cd00.                              (* [comment removed for export] *)
      rt F_4cd04 D_4cd04.                              (* [comment removed for export] *)
      ab_tk F_4c564 D_4c564 ltac:(condz).              (* [comment removed for export] *)
      an F_4c578 D_4c578.                              (* [comment removed for export] *)
      an F_4c57c D_4c57c.                              (* [comment removed for export] *)
      an F_89288 D_89288.                              (* [comment removed for export] *)
      fsd F_8928c D_8928c (at_ sp 120).                (* [comment removed for export] *)
      an F_89290 D_89290.                              (* [comment removed for export] *)
      an F_ed9c4 D_ed9c4.                              (* [comment removed for export] *)
      an F_ed9c8 D_ed9c8.                              (* [comment removed for export] *)
      rt F_ed9cc D_ed9cc.                              (* [comment removed for export] *)
      an F_89294 D_89294.                              (* [comment removed for export] *)
      fsw F_89298 D_89298 (at_ tp (-164)).             (* [comment removed for export] *)
      fld F_8929c D_8929c (Z_to_bv 64 0x4c580).        (* [comment removed for export] *)
      an F_892a0 D_892a0.                              (* [comment removed for export] *)
      rt F_892a4 D_892a4.                              (* [comment removed for export] *)
      an F_4c580 D_4c580.                              (* [comment removed for export] *)
      change (wbytes (wbytes (wbytes M _ _) _ _) _ _) with (am_null_mem M sp tp).
      sld F_4c584 D_4c584 rai 136%Z.                   (* [comment removed for export] *)
      sld F_4c588 D_4c588 s0' 128%Z.                   (* [comment removed for export] *)
      an F_4c58c D_4c58c.                              (* [comment removed for export] *)
      aret F_4c590 D_4c590 rai.                        (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.
End AMNULL.
End FPGen.
End BoAllocM8n.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocMRunN.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA.BoAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA BoAllocM8n.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Section FPGen.
Context {fx : FPState}.

Lemma at0_litN : forall c : Z, (0 <= c < 2 ^ 64)%Z -> at_ (Z_to_bv 64 0) c = Z_to_bv 64 c.
Proof using. intros c Hc. apply bv_eq. rewrite at_u by (first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]). rewrite !u_Z2bv by lia. reflexivity. Qed.
Lemma ARB_litN : forall c : Z, (0 <= c < 2 ^ 64)%Z -> at_ ARB c = Z_to_bv 64 c.
Proof using. intros c Hc. (lazymatch goal with |- ?G => let G' := eval unfold ARB in G in change_no_check G' end). apply at0_litN. exact Hc. Qed.

Section RUNN.
  Variables (M4 rom : word -> option byte) (r0 R : bvmap 5 word).
  Variables (S tp : word) (T n : Z) (x18 x19 : word).
  #[local] Abbreviation sp2 := (at_ S (-2272)).
  #[local] Abbreviation thr := (Z_to_bv 64 T).
  (* [comment removed for export] *)
  Hypothesis H2 : getr r0 2 = at_ sp2 (-48).
  Hypothesis H4 : getr r0 4 = tp.
  Hypothesis H3 : getr r0 3 = getr R 3.
  Hypothesis H10 : getr r0 10 = Z_to_bv 64 0.
  Hypothesis H18 : getr r0 18 = Z_to_bv 64 8.
  Hypothesis Hret : ret_ok (getr R 1).
  (* [comment removed for export] *)
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 /\ U S mod 16 = 0)%Z.
  Hypothesis Gn : (1 <= n <= 64512)%Z.
  Hypothesis GT : ((4096 <= T /\ TSIDE T) /\ T + 4096 <= U S - 3584)%Z.
  Hypothesis Gtp : (AIMGLO + 164 <= U tp /\ U tp <= AIMGHI)%Z.
  (* [comment removed for export] *)
  Hypothesis Hstk : store_ok BSEGS M4 (at_ S (-3584)) 3584 = true.
  Hypothesis C_inited : rdn BSEGS M4 (Z_to_bv 64 0x10ee98) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_gcf : rdn BSEGS M4 (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 0x19fce8)).
  Hypothesis C_fum : rdn BSEGS M4 (Z_to_bv 64 0x19fd0a) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_mcs : rdn BSEGS M4 (Z_to_bv 64 0x10eebc) 4 = Some (LE4 30).
  Hypothesis C_mrn : rdn BSEGS M4 (Z_to_bv 64 0x190421) 1 = Some [Z_to_bv 8 1].           (* [comment removed for export] *)
  Hypothesis SOK_oom : store_ok BSEGS M4 (Z_to_bv 64 0x190420) 1 = true.
  Hypothesis SOK_err : store_ok BSEGS M4 (at_ tp (-164)) 4 = true.
  (* [comment removed for export] *)
  Hypothesis FC : forall (o : Z) (v : word),
    In (o, v) [(-8, at_ ARB 0x4c834); (-16, Z_to_bv 64 1); (-24, Z_to_bv 64 n); (-32, Z_to_bv 64 8); (-40, Z_to_bv 64 (needed n)); (-48, Z_to_bv 64 (rz n))]%Z ->
    rdn BSEGS M4 (at_ sp2 o) 8 = Some (LE8 v).
  Hypothesis FA : forall (k : Z) (v : word),
    In (k, v) (ma_slotsA S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27)) ->
    rdn BSEGS M4 (at_ S k) 8 = Some (LE8 v).
  Hypothesis FI : forall (k : Z) (v : word),
    In (k, v) [(-8, getr R 1); (-16, getr R 8); (-24, getr R 9); (-32, getr R 18); (-40, getr R 19); (-48, getr R 20); (-56, getr R 21)]%Z ->
    rdn BSEGS M4 (at_ S k) 8 = Some (LE8 v).

  Definition mn_mem : word -> option byte := am_null_mem M4 sp2 tp.

  Lemma mn_mem_outside : forall x : word,
    (U x <> 0x190420)%Z -> (U x < U S - 2152 \/ U S - 2144 <= U x)%Z -> (U x < U tp - 164 \/ U tp - 160 <= U x)%Z -> mn_mem x = M4 x.
  Proof using Gtp GS.
    intros x X1 X2 X3. pose proof (u64_range S). pose proof (u64_range tp). destruct GS as (G1 & G2 & _). destruct Gtp as [P1 P2].
    (lazymatch goal with |- ?G => let G' := eval unfold mn_mem, am_null_mem in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_at, ?at_u by lia; rewrite ?u_Z2bv by lia;
      (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat Z.add Z.opp Pos.add Z.pos_sub] in G in change_no_check G' end); try lia. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma mn_mem_errno : forall x : word, (U tp - 164 <= U x < U tp - 160)%Z -> mn_mem x <> None.
  Proof using Gtp.
    intros x Hx. pose proof (u64_range tp). destruct Gtp as [P1 P2]. (lazymatch goal with |- ?G => let G' := eval unfold mn_mem, am_null_mem in G in change_no_check G' end).
    rewrite wbytes_inside; [discriminate | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
  Qed.
  Lemma mn_mem_grows : mem_grows M4 mn_mem.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold mn_mem, am_null_mem in G in change_no_check G' end). do 3 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.

  Theorem run_mA_null :
    exists (r : bvmap 5 word),
      msteps BSEGS (mkst r0 (Z_to_bv 64 0x50f9c) M4 rom) (mkst r (getr R 1) mn_mem rom)
      /\ getr r 10 = Z_to_bv 64 0 /\ getr r 1 = getr R 1 /\ getr r 2 = S /\ getr r 3 = getr R 3 /\ getr r 4 = tp
      /\ getr r 8 = getr R 8 /\ getr r 9 = getr R 9 /\ getr r 18 = getr R 18 /\ getr r 19 = getr R 19
      /\ getr r 20 = getr R 20 /\ getr r 21 = getr R 21 /\ getr r 22 = getr R 22 /\ getr r 23 = getr R 23
      /\ getr r 24 = getr R 24 /\ getr r 25 = getr R 25 /\ getr r 26 = getr R 26 /\ getr r 27 = getr R 27.
  Proof using FI FA FC SOK_err SOK_oom C_mrn C_mcs C_fum C_gcf C_inited Hstk Gtp GT Gn GS Hret H18 H10 H3 H4 H2 x19 x18 n T.
    pose proof (u64_range S) as HSr. pose proof (u64_range tp) as Htpr.
    destruct GS as (GS1 & GS2 & GS3). destruct GT as (GT1 & GT2). destruct Gtp as [Gtp1 Gtp2].
    assert (Uthr : U thr = T) by (unorm; reflexivity).
    assert (Usp2 : U sp2 = (U S - 2272)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (RETC : ret_ok (at_ ARB 0x4c834)) by (rewrite (ARB_litN 0x4c834) by lia; apply ret_ok_lit; [lia | reflexivity]).
    assert (RETI : ret_ok (at_ ARB 0x6f070)) by (rewrite (ARB_litN 0x6f070) by lia; apply ret_ok_lit; [lia | reflexivity]).
    (* [comment removed for export] *)
    destruct (cb_ret0 M4 rom sp2 (at_ ARB 0x4c834) (Z_to_bv 64 1) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 (needed n)) (Z_to_bv 64 (rz n)) r0
                H2 H10 H18 RETC
                (FC (-8)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)) (FC (-16)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)) (FC (-24)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto))
                (FC (-32)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)) (FC (-40)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)) (FC (-48)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)))
      as (r1 & RUN1 & A10 & A2 & A1 & A8 & A9 & A18 & A19 & A20 & AG1).
    replace (0x50f9c : word) with (Z_to_bv 64 0x50f9c : word) in RUN1 by (apply bv_eq; reflexivity).
    rewrite (ARB_litN 0x4c834) in RUN1 by lia.
    (* [comment removed for export] *)
    assert (SLs : forall (k : Z) (v : word),
              In (k, v) [(120, Z_to_bv 64 0x4c564); (112, S); (104, Z_to_bv 64 n); (96, x18); (88, x19); (80, at_ S (-2128)); (72, at_ S (-81));
                         (64, getr R 22); (56, getr R 23); (48, getr R 24); (40, getr R 25); (32, getr R 26); (24, getr R 27);
                         (136, at_ ARB 0x6f070); (128, S)]%Z -> rdn BSEGS M4 (at_ sp2 k) 8 = Some (LE8 v)).
    { intros k v Hin. rewrite at_at.
      assert (EK : In ((-2272 + k)%Z, v) (ma_slotsA S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27))).
      { (lazymatch goal with |- ?G => let G' := eval unfold ma_slotsA in G in change_no_check G' end). rewrite (ARB_litN 0x4c564) by lia. cbn [In] in Hin |- *.
        repeat (destruct Hin as [E|Hin]; [injection E as <- <-; (lazymatch goal with |- ?G => let G' := eval cbn [Z.add Z.opp Pos.add Z.pos_sub] in G in change_no_check G' end); tauto|]). destruct Hin. }
      exact (FA _ _ EK). }
    destruct (am_null M4 rom sp2 tp (at_ ARB 0x6f070) S (Z_to_bv 64 n) x18 x19 (at_ S (-2128)) (at_ S (-81))
                (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) S r1
                A2 ltac:(rewrite (AG1 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi); exact H4)
                A10 ltac:(rewrite Usp2; lia) ltac:(split; lia) RETI C_mrn SOK_oom SOK_err
                ltac:(eapply (store_ok_sub BSEGS M4 (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_at, !at_u by lia; lia | rewrite !at_at, !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia])
                SLs)
      as (r2 & RUN2 & B10 & B2 & B1 & B8 & B9 & B18 & B19 & B20 & B21 & B22 & B23 & B24 & B25 & B26 & B27 & AG2).
    replace (0x4c834 : word) with (Z_to_bv 64 0x4c834 : word) in RUN2 by (apply bv_eq; reflexivity).
    fold mn_mem in RUN2.
    rewrite at_at in B2. cbn [Z.add Z.opp Pos.add Z.pos_sub] in B2.
    (* [comment removed for export] *)
    assert (MH : mpH BSEGS both_mp_tab M4 S (Z_to_bv 64 0x19fce8) thr (Z_to_bv 8 1)).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [mt_rb mt_ui mt_g_cf mt_a_inited mt_g_mcs both_mp_tab] in G in change_no_check G' end).
      - exact C_inited.
      - exact C_gcf.
      - replace (at_ (Z_to_bv 64 0x19fce8) 34) with (Z_to_bv 64 0x19fd0a : word) by (apply bv_eq; reflexivity). exact C_fum.
      - vm_compute. discriminate.
      - exact C_mcs.
      - eapply (store_ok_sub BSEGS M4 (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia.
      - lia.
      - rewrite Uthr. lia. }
    assert (FIn : forall (k : Z) (v : word),
              In (k, v) [(-8, getr R 1); (-16, getr R 8); (-24, getr R 9); (-32, getr R 18); (-40, getr R 19); (-48, getr R 20); (-56, getr R 21)]%Z ->
              rdn BSEGS mn_mem (at_ S k) 8 = Some (LE8 v)).
    { intros k v Hin. rewrite <- (FI k v Hin).
      assert (Hk : (-56 <= k /\ k + 8 <= 0)%Z) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply mn_mem_outside; lia. }
    destruct (mp_epi BSEGS both_mp_tab both_mp_tab_ok R M4 rom (getr R 1) S (Z_to_bv 64 0x19fce8) thr (Z_to_bv 64 4096) (Z_to_bv 8 1)
                Hret MH ltac:(wd_ulia) mn_mem r2 B2 FIn)
      as (r3 & RUN3 & C10 & C1 & C2 & C8 & C9 & C18 & C19 & C20 & C21 & CK).
    cbn [mt_rb both_mp_tab] in RUN3. rewrite (ARB_litN 0x6f070) in RUN3 by lia. rewrite (ARB_litN 0x6f070) in RUN2 by lia.
    exists r3. split.
    { eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2 | exact RUN3]. }
    assert (NI : forall i : reg, In i [3; 4; 22; 23; 24; 25; 26; 27] -> ~ In i [1; 2; 8; 9; 18; 19; 20; 21]).
    { intros i Hi Hx. cbn [In] in Hi, Hx. repeat (destruct Hi as [<-|Hi]; [repeat (destruct Hx as [Hx|Hx]; [discriminate Hx|]); exact Hx|]). exact Hi. }
    split; [rewrite C10; exact B10|]. split; [exact C1|]. split; [exact C2|].
    split. { rewrite (CK 3%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto). rewrite (AG2 3%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi).
             rewrite (AG1 3%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi). exact H3. }
    split. { rewrite (CK 4%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto). rewrite (AG2 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi).
             rewrite (AG1 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi). exact H4. }
    split; [exact C8|]. split; [exact C9|]. split; [exact C18|]. split; [exact C19|]. split; [exact C20|]. split; [exact C21|].
    split; [rewrite (CK 22%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact B22|]. split; [rewrite (CK 23%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact B23|].
    split; [rewrite (CK 24%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact B24|]. split; [rewrite (CK 25%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact B25|].
    split; [rewrite (CK 26%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact B26|]. rewrite (CK 27%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto). exact B27.
  Qed.
End RUNN.
End FPGen.
End BoAllocMRunN.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA.BoAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA BoAllocM8n OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c.BoAllocM9a OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c.BoAllocM9d.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Section FPGen.
Context {fx : FPState}.

Lemma at0_litNs : forall c : Z, (0 <= c < 2 ^ 64)%Z -> at_ (Z_to_bv 64 0) c = Z_to_bv 64 c.
Proof using. intros c Hc. apply bv_eq. rewrite at_u by (first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]). rewrite !u_Z2bv by lia. reflexivity. Qed.
Lemma ARB_litNs : forall c : Z, (0 <= c < 2 ^ 64)%Z -> at_ ARB c = Z_to_bv 64 c.
Proof using. intros c Hc. (lazymatch goal with |- ?G => let G' := eval unfold ARB in G in change_no_check G' end). apply at0_litNs. exact Hc. Qed.

Section RUNNS.
  Variables (M4 rom : word -> option byte) (r0 R : bvmap 5 word).
  Variables (S tp : word) (T n : Z) (x18 x19 : word).
  #[local] Abbreviation sp2 := (at_ S (-2272)).
  #[local] Abbreviation thr := (Z_to_bv 64 T).
  (* [comment removed for export] *)
  Hypothesis HL : la_regs (at_ S (-2320)) (Z_to_bv 64 0x10ae08) (sec_needed n) r0.
  Hypothesis H4 : getr r0 4 = tp.
  Hypothesis H3 : getr r0 3 = getr R 3.
  Hypothesis H10 : getr r0 10 = Z_to_bv 64 0.
  Hypothesis Hret : ret_ok (getr R 1).
  (* [comment removed for export] *)
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 /\ U S mod 16 = 0)%Z.
  Hypothesis Gn : (64513 <= n <= 2 ^ 34)%Z.
  Hypothesis GT : ((4096 <= T /\ TSIDE T) /\ T + 4096 <= U S - 3584)%Z.
  Hypothesis Gtp : (AIMGLO + 164 <= U tp /\ U tp <= AIMGHI)%Z.
  (* [comment removed for export] *)
  Hypothesis Hstk : store_ok BSEGS M4 (at_ S (-3584)) 3584 = true.
  Hypothesis C_inited : rdn BSEGS M4 (Z_to_bv 64 0x10ee98) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_gcf : rdn BSEGS M4 (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 0x19fce8)).
  Hypothesis C_fum : rdn BSEGS M4 (Z_to_bv 64 0x19fd0a) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_mcs : rdn BSEGS M4 (Z_to_bv 64 0x10eebc) 4 = Some (LE4 30).
  Hypothesis C_mrn : rdn BSEGS M4 (Z_to_bv 64 0x190421) 1 = Some [Z_to_bv 8 1].           (* [comment removed for export] *)
  Hypothesis SOK_oom : store_ok BSEGS M4 (Z_to_bv 64 0x190420) 1 = true.
  Hypothesis SOK_err : store_ok BSEGS M4 (at_ tp (-164)) 4 = true.
  (* [comment removed for export] *)
  Hypothesis FC : forall (o : Z) (v : word),
    In (o, v) [(-8, at_ ARB 0x4c834); (-16, Z_to_bv 64 0); (-24, Z_to_bv 64 n); (-32, Z_to_bv 64 8); (-40, Z_to_bv 64 (sec_needed n)); (-48, Z_to_bv 64 2048)]%Z ->
    rdn BSEGS M4 (at_ sp2 o) 8 = Some (LE8 v).
  (* [comment removed for export] *)
  Hypothesis FLA : forall (o : Z) (v : word),
    In (o, v) [(-8, Z_to_bv 64 0x50d94); (-16, Z_to_bv 64 8); (-24, Z_to_bv 64 n); (-32, Z_to_bv 64 8); (-40, Z_to_bv 64 (sec_needed n)); (-48, Z_to_bv 64 2048);
               (-56, Z_to_bv 64 n); (-64, Z_to_bv 64 0x10ab58); (-72, at_ S (-2128)); (-80, Z_to_bv 64 18446744073709551608); (-88, Z_to_bv 64 7)]%Z ->
    rdn BSEGS M4 (at_ (at_ S (-2320)) o) 8 = Some (LE8 v).
  Hypothesis FA : forall (k : Z) (v : word),
    In (k, v) (ma_slotsA S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27)) ->
    rdn BSEGS M4 (at_ S k) 8 = Some (LE8 v).
  Hypothesis FI : forall (k : Z) (v : word),
    In (k, v) [(-8, getr R 1); (-16, getr R 8); (-24, getr R 9); (-32, getr R 18); (-40, getr R 19); (-48, getr R 20); (-56, getr R 21)]%Z ->
    rdn BSEGS M4 (at_ S k) 8 = Some (LE8 v).

  Definition mn_mem : word -> option byte := am_null_mem M4 sp2 tp.

  Lemma mn_mem_outside : forall x : word,
    (U x <> 0x190420)%Z -> (U x < U S - 2152 \/ U S - 2144 <= U x)%Z -> (U x < U tp - 164 \/ U tp - 160 <= U x)%Z -> mn_mem x = M4 x.
  Proof using Gtp GS.
    intros x X1 X2 X3. pose proof (u64_range S). pose proof (u64_range tp). destruct GS as (G1 & G2 & _). destruct Gtp as [P1 P2].
    (lazymatch goal with |- ?G => let G' := eval unfold mn_mem, am_null_mem in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_at, ?at_u by lia; rewrite ?u_Z2bv by lia;
      (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat Z.add Z.opp Pos.add Z.pos_sub] in G in change_no_check G' end); try lia. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma mn_mem_errno : forall x : word, (U tp - 164 <= U x < U tp - 160)%Z -> mn_mem x <> None.
  Proof using Gtp.
    intros x Hx. pose proof (u64_range tp). destruct Gtp as [P1 P2]. (lazymatch goal with |- ?G => let G' := eval unfold mn_mem, am_null_mem in G in change_no_check G' end).
    rewrite wbytes_inside; [discriminate | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
  Qed.
  Lemma mn_mem_grows : mem_grows M4 mn_mem.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold mn_mem, am_null_mem in G in change_no_check G' end). do 3 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.

  Theorem run_mS_null :
    exists (r : bvmap 5 word),
      msteps BSEGS (mkst r0 (Z_to_bv 64 0x51080) M4 rom) (mkst r (getr R 1) mn_mem rom)
      /\ getr r 10 = Z_to_bv 64 0 /\ getr r 1 = getr R 1 /\ getr r 2 = S /\ getr r 3 = getr R 3 /\ getr r 4 = tp
      /\ getr r 8 = getr R 8 /\ getr r 9 = getr R 9 /\ getr r 18 = getr R 18 /\ getr r 19 = getr R 19
      /\ getr r 20 = getr R 20 /\ getr r 21 = getr R 21 /\ getr r 22 = getr R 22 /\ getr r 23 = getr R 23
      /\ getr r 24 = getr R 24 /\ getr r 25 = getr R 25 /\ getr r 26 = getr R 26 /\ getr r 27 = getr R 27.
  Proof using FI FA FLA FC SOK_err SOK_oom C_mrn C_mcs C_fum C_gcf C_inited Hstk Gtp GT Gn GS Hret H10 H3 H4 HL x19 x18 n T.
    pose proof (u64_range S) as HSr. pose proof (u64_range tp) as Htpr.
    destruct GS as (GS1 & GS2 & GS3). destruct GT as (GT1 & GT2). destruct Gtp as [Gtp1 Gtp2].
    assert (Uthr : U thr = T) by (unorm; reflexivity).
    assert (Usp2 : U sp2 = (U S - 2272)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (RETC : ret_ok (at_ ARB 0x4c834)) by (rewrite (ARB_litNs 0x4c834) by lia; apply ret_ok_lit; [lia | reflexivity]).
    assert (RETI : ret_ok (at_ ARB 0x6f070)) by (rewrite (ARB_litNs 0x6f070) by lia; apply ret_ok_lit; [lia | reflexivity]).
    (* [comment removed for export] *)
    assert (RETL : ret_ok (Z_to_bv 64 0x50d94)) by (apply ret_ok_lit; [lia | reflexivity]).
    destruct (la_fail M4 rom (at_ S (-2320)) (Z_to_bv 64 0x50d94) (Z_to_bv 64 8) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 (sec_needed n)) (Z_to_bv 64 2048)
                (Z_to_bv 64 n) (Z_to_bv 64 0x10ab58) (at_ S (-2128)) (Z_to_bv 64 18446744073709551608) (Z_to_bv 64 7) (Z_to_bv 64 0x10ae08) (sec_needed n) r0
                HL RETL H10
                (FLA (-8)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20)) (FLA (-16)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20)) (FLA (-24)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20))
                (FLA (-32)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20)) (FLA (-40)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20)) (FLA (-48)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20))
                (FLA (-56)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20)) (FLA (-64)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20)) (FLA (-72)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20))
                (FLA (-80)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20)) (FLA (-88)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20)))
      as (r0' & RUN0 & (L10 & L2 & L1 & L8 & L9 & L18 & L19 & L20 & L21 & L22 & L23 & L24 & L25 & AG0)).
    replace (0x51080 : word) with (Z_to_bv 64 0x51080 : word) in RUN0 by (apply bv_eq; reflexivity).
    assert (K0 : forall i : reg, In i [3; 4; 26; 27] -> getr r0' i = getr r0 i).
    { intros i Hi. apply AG0. cbn [In] in Hi |- *. intros Hx. repeat (destruct Hi as [<-|Hi]; [repeat (destruct Hx as [Hx|Hx]; [discriminate Hx|]); exact Hx|]). exact Hi. }
    (* [comment removed for export] *)
    destruct (cbs_ret M4 rom sp2 (at_ ARB 0x4c834) (Z_to_bv 64 0) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 (sec_needed n)) (Z_to_bv 64 2048) (Z_to_bv 64 0) r0'
                ltac:(rewrite L2; rewrite !at_at; reflexivity) L8 L10 RETC
                (FC (-8)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20)) (FC (-16)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20)) (FC (-24)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20))
                (FC (-32)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20)) (FC (-40)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20)) (FC (-48)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20)))
      as (r1 & RUN1 & A10 & A2 & A1 & A8 & A9 & A18 & A19 & A20 & AG1).
    replace (0x50d94 : word) with (Z_to_bv 64 0x50d94 : word) in RUN1 by (apply bv_eq; reflexivity).
    rewrite (ARB_litNs 0x4c834) in RUN1 by lia.
    assert (H4' : getr r0' 4 = tp) by (rewrite K0 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20); exact H4).
    assert (H3' : getr r0' 3 = getr R 3) by (rewrite K0 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20); exact H3).
    (* [comment removed for export] *)
    assert (SLs : forall (k : Z) (v : word),
              In (k, v) [(120, Z_to_bv 64 0x4c564); (112, S); (104, Z_to_bv 64 n); (96, x18); (88, x19); (80, at_ S (-2128)); (72, at_ S (-81));
                         (64, getr R 22); (56, getr R 23); (48, getr R 24); (40, getr R 25); (32, getr R 26); (24, getr R 27);
                         (136, at_ ARB 0x6f070); (128, S)]%Z -> rdn BSEGS M4 (at_ sp2 k) 8 = Some (LE8 v)).
    { intros k v Hin. rewrite at_at.
      assert (EK : In ((-2272 + k)%Z, v) (ma_slotsA S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27))).
      { (lazymatch goal with |- ?G => let G' := eval unfold ma_slotsA in G in change_no_check G' end). rewrite (ARB_litNs 0x4c564) by lia. cbn [In] in Hin |- *.
        repeat (destruct Hin as [E|Hin]; [injection E as <- <-; (lazymatch goal with |- ?G => let G' := eval cbn [Z.add Z.opp Pos.add Z.pos_sub] in G in change_no_check G' end); tauto|]). destruct Hin. }
      exact (FA _ _ EK). }
    destruct (am_null M4 rom sp2 tp (at_ ARB 0x6f070) S (Z_to_bv 64 n) x18 x19 (at_ S (-2128)) (at_ S (-81))
                (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) S r1
                A2 ltac:(rewrite (AG1 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi); exact H4')
                A10 ltac:(rewrite Usp2; lia) ltac:(split; lia) RETI C_mrn SOK_oom SOK_err
                ltac:(eapply (store_ok_sub BSEGS M4 (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_at, !at_u by lia; lia | rewrite !at_at, !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia])
                SLs)
      as (r2 & RUN2 & B10 & B2 & B1 & B8 & B9 & B18 & B19 & B20 & B21 & B22 & B23 & B24 & B25 & B26 & B27 & AG2).
    replace (0x4c834 : word) with (Z_to_bv 64 0x4c834 : word) in RUN2 by (apply bv_eq; reflexivity).
    fold mn_mem in RUN2.
    rewrite at_at in B2. cbn [Z.add Z.opp Pos.add Z.pos_sub] in B2.
    (* [comment removed for export] *)
    assert (MH : mpH BSEGS both_mp_tab M4 S (Z_to_bv 64 0x19fce8) thr (Z_to_bv 8 1)).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [mt_rb mt_ui mt_g_cf mt_a_inited mt_g_mcs both_mp_tab] in G in change_no_check G' end).
      - exact C_inited.
      - exact C_gcf.
      - replace (at_ (Z_to_bv 64 0x19fce8) 34) with (Z_to_bv 64 0x19fd0a : word) by (apply bv_eq; reflexivity). exact C_fum.
      - vm_compute. discriminate.
      - exact C_mcs.
      - eapply (store_ok_sub BSEGS M4 (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia.
      - lia.
      - rewrite Uthr. lia. }
    assert (FIn : forall (k : Z) (v : word),
              In (k, v) [(-8, getr R 1); (-16, getr R 8); (-24, getr R 9); (-32, getr R 18); (-40, getr R 19); (-48, getr R 20); (-56, getr R 21)]%Z ->
              rdn BSEGS mn_mem (at_ S k) 8 = Some (LE8 v)).
    { intros k v Hin. rewrite <- (FI k v Hin).
      assert (Hk : (-56 <= k /\ k + 8 <= 0)%Z) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply mn_mem_outside; lia. }
    destruct (mp_epi BSEGS both_mp_tab both_mp_tab_ok R M4 rom (getr R 1) S (Z_to_bv 64 0x19fce8) thr (Z_to_bv 64 4096) (Z_to_bv 8 1)
                Hret MH ltac:(wd_ulia) mn_mem r2 B2 FIn)
      as (r3 & RUN3 & C10 & C1 & C2 & C8 & C9 & C18 & C19 & C20 & C21 & CK).
    cbn [mt_rb both_mp_tab] in RUN3. rewrite (ARB_litNs 0x6f070) in RUN3 by lia. rewrite (ARB_litNs 0x6f070) in RUN2 by lia.
    exists r3. split.
    { eapply msteps_trans; [exact RUN0|]. eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2 | exact RUN3]. }
    assert (NI : forall i : reg, In i [3; 4; 22; 23; 24; 25; 26; 27] -> ~ In i [1; 2; 8; 9; 18; 19; 20; 21]).
    { intros i Hi Hx. cbn [In] in Hi, Hx. repeat (destruct Hi as [<-|Hi]; [repeat (destruct Hx as [Hx|Hx]; [discriminate Hx|]); exact Hx|]). exact Hi. }
    split; [rewrite C10; exact B10|]. split; [exact C1|]. split; [exact C2|].
    split. { rewrite (CK 3%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto). rewrite (AG2 3%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi).
             rewrite (AG1 3%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi). exact H3'. }
    split. { rewrite (CK 4%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto). rewrite (AG2 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi).
             rewrite (AG1 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi). exact H4'. }
    split; [exact C8|]. split; [exact C9|]. split; [exact C18|]. split; [exact C19|]. split; [exact C20|]. split; [exact C21|].
    split; [rewrite (CK 22%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact B22|]. split; [rewrite (CK 23%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact B23|].
    split; [rewrite (CK 24%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact B24|]. split; [rewrite (CK 25%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact B25|].
    split; [rewrite (CK 26%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact B26|]. rewrite (CK 27%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto). exact B27.
  Qed.
End RUNNS.
End FPGen.
