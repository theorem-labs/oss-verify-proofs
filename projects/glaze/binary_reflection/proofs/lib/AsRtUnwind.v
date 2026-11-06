(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen1.
Context {fx : FPState}.

Definition uf_words : list (option (bv 32)) :=
  [
   Some W_8f404; Some W_8f408; Some W_8f40c; Some W_8f410; Some W_8f414; Some W_8f418; Some W_8f41c;
   Some W_8f420; Some W_8f424; Some W_8f428; Some W_8f42c; Some W_8f430; Some W_8f434; Some W_8f438;
   None; None; Some W_8f444; Some W_8f448; Some W_8f44c; Some W_8f450; Some W_8f454; Some W_8f458;
   Some W_8f45c; Some W_8f460; Some W_8f464; Some W_8f468; Some W_8f46c; Some W_8f470; Some W_8f474;
   Some W_8f478; Some W_8f47c; Some W_8f480; Some W_8f484; Some W_8f488; Some W_8f48c; Some W_8f490;
   Some W_8f494; Some W_8f498; Some W_8f49c; Some W_8f4a0; Some W_8f4a4; Some W_8f4a8; Some W_8f4ac;
   Some W_8f4b0; Some W_8f4b4; Some W_8f4b8; Some W_8f4bc; Some W_8f4c0; Some W_8f4c4; Some W_8f4c8;
   Some W_8f4cc; Some W_8f4d0; Some W_8f4d4; Some W_8f4d8; Some W_8f4dc; Some W_8f4e0; Some W_8f4e4;
   Some W_8f4e8; Some W_8f4ec; Some W_8f4f0; Some W_8f4f4; Some W_8f4f8; Some W_8f4fc; Some W_8f500;
   Some W_8f504; Some W_8f508; Some W_8f50c; Some W_8f510; Some W_8f514; Some W_8f518; Some W_8f51c;
   Some W_8f520; Some W_8f524
  ]%list.

(* [comment removed for export] *)
Definition uf_clob : list reg := [12; 13; 14; 15; 16; 17].
(* [comment removed for export] *)
Definition uf_clobx : list reg := [2; 8; 9; 18; 19; 20; 21; 22; 12; 13; 14; 15; 16; 17].

(* [comment removed for export] *)
Record uf_tab := UFT { uf_base : word; uf_g_pgsz : Z }.
Record uf_tab_ok (segs : list Segment) (t : uf_tab) : Prop := UFTOK {
  ufo_code : code_ato segs (uf_base t) 0 uf_words;
  ufo_g56 : gload2 segs (uf_base t) 56 13 18 (uf_g_pgsz t) }.

Section UF.
  Variable segs : list Segment.
  Variable base : word.
  Variable g_pgsz : Z.
  Hypothesis HCODE : code_ato segs base 0 uf_words.
  Hypothesis G56 : gload2 segs base 56 13 18 g_pgsz.

  Lemma Fo0 : fetch_word segs (at_ base 0) = Some W_8f404.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 0 _ HCODE eq_refl). Qed.
  Lemma Fo4 : fetch_word segs (at_ base 4) = Some W_8f408.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 1 _ HCODE eq_refl). Qed.
  Lemma Fo8 : fetch_word segs (at_ base 8) = Some W_8f40c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 2 _ HCODE eq_refl). Qed.
  Lemma Fo12 : fetch_word segs (at_ base 12) = Some W_8f410.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 3 _ HCODE eq_refl). Qed.
  Lemma Fo16 : fetch_word segs (at_ base 16) = Some W_8f414.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 4 _ HCODE eq_refl). Qed.
  Lemma Fo20 : fetch_word segs (at_ base 20) = Some W_8f418.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 5 _ HCODE eq_refl). Qed.
  Lemma Fo24 : fetch_word segs (at_ base 24) = Some W_8f41c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 6 _ HCODE eq_refl). Qed.
  Lemma Fo28 : fetch_word segs (at_ base 28) = Some W_8f420.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 7 _ HCODE eq_refl). Qed.
  Lemma Fo32 : fetch_word segs (at_ base 32) = Some W_8f424.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 8 _ HCODE eq_refl). Qed.
  Lemma Fo36 : fetch_word segs (at_ base 36) = Some W_8f428.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 9 _ HCODE eq_refl). Qed.
  Lemma Fo40 : fetch_word segs (at_ base 40) = Some W_8f42c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 10 _ HCODE eq_refl). Qed.
  Lemma Fo44 : fetch_word segs (at_ base 44) = Some W_8f430.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 11 _ HCODE eq_refl). Qed.
  Lemma Fo48 : fetch_word segs (at_ base 48) = Some W_8f434.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 12 _ HCODE eq_refl). Qed.
  Lemma Fo52 : fetch_word segs (at_ base 52) = Some W_8f438.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 13 _ HCODE eq_refl). Qed.
  Lemma Fo64 : fetch_word segs (at_ base 64) = Some W_8f444.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 16 _ HCODE eq_refl). Qed.
  Lemma Fo68 : fetch_word segs (at_ base 68) = Some W_8f448.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 17 _ HCODE eq_refl). Qed.
  Lemma Fo72 : fetch_word segs (at_ base 72) = Some W_8f44c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 18 _ HCODE eq_refl). Qed.
  Lemma Fo76 : fetch_word segs (at_ base 76) = Some W_8f450.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 19 _ HCODE eq_refl). Qed.
  Lemma Fo80 : fetch_word segs (at_ base 80) = Some W_8f454.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 20 _ HCODE eq_refl). Qed.
  Lemma Fo84 : fetch_word segs (at_ base 84) = Some W_8f458.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 21 _ HCODE eq_refl). Qed.
  Lemma Fo88 : fetch_word segs (at_ base 88) = Some W_8f45c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 22 _ HCODE eq_refl). Qed.
  Lemma Fo160 : fetch_word segs (at_ base 160) = Some W_8f4a4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 40 _ HCODE eq_refl). Qed.
  Lemma Fo164 : fetch_word segs (at_ base 164) = Some W_8f4a8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 41 _ HCODE eq_refl). Qed.
  Lemma Fo168 : fetch_word segs (at_ base 168) = Some W_8f4ac.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 42 _ HCODE eq_refl). Qed.
  Lemma Fo172 : fetch_word segs (at_ base 172) = Some W_8f4b0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 43 _ HCODE eq_refl). Qed.
  Lemma Fo176 : fetch_word segs (at_ base 176) = Some W_8f4b4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 44 _ HCODE eq_refl). Qed.
  Lemma Fo180 : fetch_word segs (at_ base 180) = Some W_8f4b8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 45 _ HCODE eq_refl). Qed.
  Lemma Fo184 : fetch_word segs (at_ base 184) = Some W_8f4bc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 46 _ HCODE eq_refl). Qed.
  Lemma Fo188 : fetch_word segs (at_ base 188) = Some W_8f4c0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 47 _ HCODE eq_refl). Qed.
  Lemma Fo192 : fetch_word segs (at_ base 192) = Some W_8f4c4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 48 _ HCODE eq_refl). Qed.
  Lemma Fo196 : fetch_word segs (at_ base 196) = Some W_8f4c8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 49 _ HCODE eq_refl). Qed.
  Lemma Fo200 : fetch_word segs (at_ base 200) = Some W_8f4cc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 50 _ HCODE eq_refl). Qed.
  Lemma Fo204 : fetch_word segs (at_ base 204) = Some W_8f4d0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 51 _ HCODE eq_refl). Qed.
  Lemma Fo208 : fetch_word segs (at_ base 208) = Some W_8f4d4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 52 _ HCODE eq_refl). Qed.
  Lemma Fo212 : fetch_word segs (at_ base 212) = Some W_8f4d8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 53 _ HCODE eq_refl). Qed.
  Lemma Fo216 : fetch_word segs (at_ base 216) = Some W_8f4dc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 54 _ HCODE eq_refl). Qed.
  Lemma Fo220 : fetch_word segs (at_ base 220) = Some W_8f4e0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 55 _ HCODE eq_refl). Qed.
  Lemma Fo224 : fetch_word segs (at_ base 224) = Some W_8f4e4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 56 _ HCODE eq_refl). Qed.
  Lemma Fo228 : fetch_word segs (at_ base 228) = Some W_8f4e8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 57 _ HCODE eq_refl). Qed.
  Lemma Fo232 : fetch_word segs (at_ base 232) = Some W_8f4ec.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 58 _ HCODE eq_refl). Qed.
  Lemma Fo236 : fetch_word segs (at_ base 236) = Some W_8f4f0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 59 _ HCODE eq_refl). Qed.
  Lemma Fo240 : fetch_word segs (at_ base 240) = Some W_8f4f4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 60 _ HCODE eq_refl). Qed.
  Lemma Fo244 : fetch_word segs (at_ base 244) = Some W_8f4f8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 61 _ HCODE eq_refl). Qed.
  Lemma Fo248 : fetch_word segs (at_ base 248) = Some W_8f4fc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 62 _ HCODE eq_refl). Qed.
  Lemma Fo252 : fetch_word segs (at_ base 252) = Some W_8f500.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 63 _ HCODE eq_refl). Qed.
  Lemma Fo256 : fetch_word segs (at_ base 256) = Some W_8f504.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 64 _ HCODE eq_refl). Qed.
  Lemma Fo260 : fetch_word segs (at_ base 260) = Some W_8f508.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 65 _ HCODE eq_refl). Qed.
  Lemma Fo264 : fetch_word segs (at_ base 264) = Some W_8f50c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 66 _ HCODE eq_refl). Qed.
  Lemma Fo268 : fetch_word segs (at_ base 268) = Some W_8f510.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 67 _ HCODE eq_refl). Qed.
  Lemma Fo272 : fetch_word segs (at_ base 272) = Some W_8f514.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 68 _ HCODE eq_refl). Qed.
  Lemma Fo276 : fetch_word segs (at_ base 276) = Some W_8f518.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 69 _ HCODE eq_refl). Qed.
  Lemma Fo280 : fetch_word segs (at_ base 280) = Some W_8f51c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 70 _ HCODE eq_refl). Qed.
  Lemma Fo284 : fetch_word segs (at_ base 284) = Some W_8f520.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 71 _ HCODE eq_refl). Qed.
  Lemma Fo288 : fetch_word segs (at_ base 288) = Some W_8f524.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 72 _ HCODE eq_refl). Qed.

  (* [comment removed for export] *)
  Variables (regs : bvmap 5 word) (rom : word -> option byte).
  Variables (ra sp this pc0 bp top bot : word).
  Hypothesis Hret : ret_ok ra.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H10 : getr regs 10 = this.
  Hypothesis H11 : getr regs 11 = pc0.
  Hypothesis H12 : getr regs 12 = bp.
  Hypothesis H13 : getr regs 13 = top.
  Hypothesis H14 : getr regs 14 = bot.
  Hypothesis H15 : getr regs 15 = Z_to_bv 64 30.
  (* [comment removed for export] *)
  Hypothesis Gsp : (2 ^ 32 + 64 <= U sp)%Z.
  Hypothesis Gframe : (U sp <= U this)%Z.
  Hypothesis Gobj : (U this + 256 <= U bp - 16)%Z.
  Hypothesis GS : (U bp + 16 <= 2 ^ 47)%Z.
  Hypothesis GS8 : (U bp mod 16 = 0)%Z.
  Hypothesis Gtop : (4096 <= U top <= 2 ^ 47)%Z.
  Hypothesis Gbot : (U bot < U top)%Z.

  #[local] Abbreviation CL := (fun r => In r uf_clob).
  #[local] Abbreviation CLX := (fun r => In r uf_clobx).

  (* [comment removed for export] *)
  Lemma uf_epi : forall (M : word -> option byte) r0,
    getr r0 2 = at_ sp (-64) -> getr r0 10 = this -> getr r0 11 = pc0 ->
    (forall (k : Z) (v : word),
       In (k, v) [(-8, ra); (-16, getr regs 8); (-24, getr regs 9); (-32, getr regs 18); (-40, getr regs 19);
                  (-48, getr regs 20); (-56, getr regs 21); (-64, getr regs 22)]%Z ->
       rdn segs M (at_ sp k) 8 = Some (LE8 v)) ->
    regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ base 252) M rom) (mkst r ra M rom)
      /\ getr r 10 = this /\ getr r 11 = pc0
      /\ regs_agree CL regs r.
  Proof using H15 H14 H13 H12 H2 H1 Hret bot top bp HCODE.
    intros M r0 R2 R10 R11 RD AG0. pose proof (u64_range sp) as Hspr.
    Ltac fldM F D vv RD :=
      chain_step; [reflexivity
        | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
          [exact F | reflexivity | exact D
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; apply RD; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto
          | apply bytes_le_to_Z_8]
        | step_simpl]; vn.
    wd_eexists. split; [|split; [|split]].
    - fldM Fo252 D_8f500 ra RD.
      fldM Fo256 D_8f504 (getr regs 8) RD.
      fldM Fo260 D_8f508 (getr regs 9) RD.
      fldM Fo264 D_8f50c (getr regs 18) RD.
      fldM Fo268 D_8f510 (getr regs 19) RD.
      fldM Fo272 D_8f514 (getr regs 20) RD.
      fldM Fo276 D_8f518 (getr regs 21) RD.
      fldM Fo280 D_8f51c (getr regs 22) RD.
      an Fo284 D_8f520.                                  (* [comment removed for export] *)
      aret Fo288 D_8f524 ra.                             (* [comment removed for export] *)
      wd_refl.
    - gres. exact R10.
    - gres. exact R11.
    - apply (regs_agree_strengthen uf_clob uf_clobx regs).
      + (lazymatch goal with |- ?G => let G' := eval unfold uf_clobx in G in change_no_check G' end). ra_solve.
      + intros i Hi Hni. cbn [uf_clobx In] in Hi.
        repeat (destruct Hi as [<-|Hi]; [gres; rwH; rewrite ?at_addi, ?at_0; first [reflexivity | symmetry; assumption | f_equal; lia | exfalso; apply Hni; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto] |]).
        destruct Hi.
  Qed.

  (* [comment removed for export] *)
  Definition uf_frame (mem : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
      (at_ sp (-8)) (LE8 ra)) (at_ sp (-16)) (LE8 (getr regs 8))) (at_ sp (-24)) (LE8 (getr regs 9)))
      (at_ sp (-32)) (LE8 (getr regs 18))) (at_ sp (-40)) (LE8 (getr regs 19))) (at_ sp (-48)) (LE8 (getr regs 20)))
      (at_ sp (-56)) (LE8 (getr regs 21))) (at_ sp (-64)) (LE8 (getr regs 22)).
  (* [comment removed for export] *)
  Definition uf_mem2 (mem : word -> option byte) : word -> option byte :=
    wbytes (wbytes (uf_frame mem) (at_ this 8) (LE4 1)) (at_ this 16) (LE8 pc0).

  Lemma uf_frame_outside : forall mem (x : word),
    (U x < U sp - 64 \/ U sp <= U x)%Z -> uf_frame mem x = mem x.
  Proof using Gsp bp.
    intros mem x Hx. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold uf_frame in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; try reflexivity; rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia.
  Qed.
  Lemma uf_mem2_outside : forall mem (x : word),
    (U x < U sp - 64)%Z \/ (U sp <= U x < U this + 8)%Z \/ (U this + 12 <= U x < U this + 16)%Z \/ (U this + 24 <= U x)%Z ->
    uf_mem2 mem x = mem x.
  Proof using GS Gobj Gframe Gsp bp.
    intros mem x Hx. pose proof (u64_range sp). pose proof (u64_range this). (lazymatch goal with |- ?G => let G' := eval unfold uf_mem2 in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia.
    apply uf_frame_outside. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma uf_mem2_slots : forall mem (k : Z) (v : word),
    In (k, v) [(-8, ra); (-16, getr regs 8); (-24, getr regs 9); (-32, getr regs 18); (-40, getr regs 19);
               (-48, getr regs 20); (-56, getr regs 21); (-64, getr regs 22)]%Z ->
    rdn segs (uf_mem2 mem) (at_ sp k) 8 = Some (LE8 v).
  Proof using GS Gobj Gframe Gsp bp.
    intros mem k v Hin. pose proof (u64_range sp). pose proof (u64_range this). (lazymatch goal with |- ?G => let G' := eval unfold uf_mem2, uf_frame in G in change_no_check G' end).
    cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin.
  Qed.

  (* [comment removed for export] *)
  Lemma rd_same : forall (M mem : word -> option byte) (a : word) k bs0,
    (forall x : word, (U a <= U x < U a + Z.of_nat k)%Z -> M x = mem x) -> (U a + Z.of_nat k <= 2 ^ 64)%Z ->
    rdn segs mem a k = Some bs0 -> rdn segs M a k = Some bs0.
  Proof using. intros M mem a k bs0 HM Hnw Hr. rewrite <- Hr. apply rdn_ext; [exact Hnw | exact HM]. Qed.
  Lemma rd_sameZ : forall (M mem : word -> option byte) (c : Z) k bs0,
    (0 <= c < 2 ^ 64)%Z -> (c + Z.of_nat k <= 2 ^ 64)%Z ->
    (forall x : word, (c <= U x < c + Z.of_nat k)%Z -> M x = mem x) ->
    rdn segs mem (Z_to_bv 64 c) k = Some bs0 -> rdn segs M (Z_to_bv 64 c) k = Some bs0.
  Proof using bp.
    intros M mem c k bs0 Hc Hk HM Hr. apply (rd_same M mem); [| wd_ulia | exact Hr].
    intros x Hx. apply HM. revert Hx. unorm. intros Hx. exact Hx.
  Qed.

  Section Run.
    Variable mem : word -> option byte.
    Variables (P : word).
    (* [comment removed for export] *)
    Hypothesis Rg : rdn segs mem (Z_to_bv 64 g_pgsz) 8 = Some (LE8 P).
    Hypothesis RP : rdn segs mem P 8 = Some (LE8 (Z_to_bv 64 4096)).
    Hypothesis Gg : (0 <= g_pgsz /\ g_pgsz + 8 <= 2 ^ 32)%Z.
    Hypothesis GP : (U P + 8 <= 2 ^ 32)%Z.
    (* [comment removed for export] *)
    Hypothesis Hstk : store_ok segs mem (at_ sp (-64)) 64 = true.
    Hypothesis Hobj : store_ok segs mem (at_ this 8) 248 = true.

    Ltac sok8 Hs lo N :=
      repeat (eapply store_ok_mono; [apply wbytes_grows|]);
      eapply (store_ok_sub segs mem lo _ N); [rewrite at_u; lia | exact Hs | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia].
    (* [comment removed for export] *)
    Ltac sok8G GR Hs lo N :=
      repeat (eapply store_ok_mono; [apply wbytes_grows|]);
      eapply store_ok_mono; [exact GR|];
      eapply (store_ok_sub segs mem lo _ N); [rewrite at_u; lia | exact Hs | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia].
    Ltac fsd_g F D aa oktac :=
      chain_step; [reflexivity
        | eapply step_sd_at with (a := aa);
          [exact F | reflexivity | exact D
          | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
          | gres; rwH; reflexivity
          | oktac ]
        | step_simpl]; vn.
    Ltac fsw_g F D aa oktac :=
      chain_step; [reflexivity
        | eapply step_sw_at with (a := aa);
          [exact F | reflexivity | exact D
          | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
          | gres; rwH; reflexivity
          | oktac ]
        | step_simpl]; vn.
    Ltac fsd F D aa := fsd_g F D aa ltac:(first [sok8 Hstk (at_ sp (-64)) 64%nat | sok8 Hobj (at_ this 8) 248%nat]).
    Ltac fsw F D aa := fsw_g F D aa ltac:(first [sok8 Hstk (at_ sp (-64)) 64%nat | sok8 Hobj (at_ this 8) 248%nat]).
    Ltac cld F D vv Hr :=
      chain_step; [reflexivity
        | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
          [exact F | reflexivity | exact D | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi; zlit_at; Hr | apply bytes_le_to_Z_8]
        | step_simpl]; vn.

    (* [comment removed for export] *)
    Lemma uf_pro :
      exists r,
        msteps segs (mkst regs (at_ base 0) mem rom) (mkst r (at_ base 164) (uf_mem2 mem) rom)
        /\ getr r 2 = at_ sp (-64) /\ getr r 10 = this /\ getr r 11 = pc0 /\ getr r 12 = bp
        /\ getr r 13 = Z_to_bv 64 4096 /\ getr r 14 = bot /\ getr r 15 = Z_to_bv 64 1
        /\ getr r 8 = Z_to_bv 64 30 /\ getr r 9 = top
        /\ regs_agree CLX regs r.
    Proof using Hobj Hstk GP Gg RP Rg P Gbot Gtop GS Gobj Gframe Gsp H15 H14 H13 H12 H11 H10 H2 H1 G56 HCODE g_pgsz.
      pose proof (u64_range sp) as Hspr. pose proof (u64_range this) as Hth. pose proof (u64_range top) as Htop.
      destruct G56 as [gx G56'].
      wd_eexists. split.
      - an Fo0 D_8f404.                                   (* [comment removed for export] *)
        fsd Fo4 D_8f408 (at_ sp (-8)).                    (* [comment removed for export] *)
        fsd Fo8 D_8f40c (at_ sp (-16)).                   (* [comment removed for export] *)
        fsd Fo12 D_8f410 (at_ sp (-24)).                  (* [comment removed for export] *)
        fsd Fo16 D_8f414 (at_ sp (-32)).                  (* [comment removed for export] *)
        fsd Fo20 D_8f418 (at_ sp (-40)).                  (* [comment removed for export] *)
        fsd Fo24 D_8f41c (at_ sp (-48)).                  (* [comment removed for export] *)
        fsd Fo28 D_8f420 (at_ sp (-56)).                  (* [comment removed for export] *)
        fsd Fo32 D_8f424 (at_ sp (-64)).                  (* [comment removed for export] *)
        change (wbytes _ _ _) with (uf_frame mem).
        an Fo36 D_8f428.                                  (* [comment removed for export] *)
        an Fo40 D_8f42c.                                  (* [comment removed for export] *)
        an Fo44 D_8f430.                                  (* [comment removed for export] *)
        an Fo48 D_8f434.                                  (* [comment removed for export] *)
        ab_ft Fo52 D_8f438 ltac:(condz).                 (* [comment removed for export] *)
        eapply msteps_trans; [ eapply G56'; apply (rd_sameZ _ mem); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros x Hx; apply uf_frame_outside; cbn in Hx; lia | exact Rg] | ]; zlit_at.
        cld Fo64 D_8f444 (Z_to_bv 64 4096) ltac:(apply (rd_same _ mem); [intros x Hx; apply uf_frame_outside; cbn in Hx; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact RP]).   (* [comment removed for export] *)
        ab_ft Fo68 D_8f448 ltac:(condz).                 (* [comment removed for export] *)
        an Fo72 D_8f44c.                                  (* [comment removed for export] *)
        av Fo76 D_8f450 (Z_to_bv 64 (U top / 4096)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; reflexivity).  (* [comment removed for export] *)
        fsw Fo80 D_8f454 (at_ this 8).                    (* [comment removed for export] *)
        fsd Fo84 D_8f458 (at_ this 16).                   (* [comment removed for export] *)
        change (wbytes _ _ _) with (uf_mem2 mem).
        assert (Hd : (1 <= U top / 4096 /\ U top / 4096 < 2 ^ 62)%Z) by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia]).
        ab_tk Fo88 D_8f45c ltac:(condz).                 (* [comment removed for export] *)
        ab_ft Fo160 D_8f4a4 ltac:(condz).                (* [comment removed for export] *)
        wd_refl.
      - post. (lazymatch goal with |- ?G => let G' := eval unfold uf_clobx in G in change_no_check G' end). ra_solve.
    Qed.

    (* [comment removed for export] *)
    Definition uf_upd (M : word -> option byte) (k : Z) (r : word) : word -> option byte :=
      wbytes (wbytes M (at_ this 8) (LE4 (k + 1))) (at_ this (16 + 8 * k)) (LE8 r).

    Lemma uf_upd_outside : forall M k r (x : word), (1 <= k < 30)%Z ->
      (U x < U this + 8 \/ (U this + 12 <= U x < U this + 16 + 8 * k) \/ U this + 24 + 8 * k <= U x)%Z ->
      uf_upd M k r x = M x.
    Proof using GS Gobj Gframe Gsp bp sp.
      intros M k r x Hk Hx. pose proof (u64_range this). (lazymatch goal with |- ?G => let G' := eval unfold uf_upd in G in change_no_check G' end).
      rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia. reflexivity.
    Qed.

    (* [comment removed for export] *)
    Lemma rdn_some_of_defined : forall (M : word -> option byte) n (a : word),
      (forall i, (U a <= i < U a + Z.of_nat n)%Z -> M (Z_to_bv 64 i) <> None) -> (U a + Z.of_nat n <= 2 ^ 64)%Z ->
      exists bs, rdn segs M a n = Some bs /\ length bs = n.
    Proof using Gobj Gframe Gsp bp this sp.
      intros M n. induction n as [|n IH]; intros a HD Hnw.
      - exists []. split; reflexivity.
      - (lazymatch goal with |- ?G => let G' := eval cbn [rdn] in G in change_no_check G' end). pose proof (u64_range a) as Ha.
        assert (Hb : exists b, M a = Some b).
        { destruct (M a) as [b|] eqn:E; [exists b; reflexivity|]. exfalso. apply (HD (U a)); [lia|].
          rewrite Z_to_bv_bv_unsigned. exact E. }
        destruct Hb as [b ->].
        destruct n as [|n'].
        + exists [b]. split; reflexivity.
        + assert (Hu1 : U (a + 1) = (U a + 1)%Z) by (apply u_add1; lia).
          destruct (IH (a + 1)) as (bs & -> & L); [intros i Hi; apply HD; lia | lia |].
          exists (b :: bs). split; [reflexivity | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); rewrite L; reflexivity].
    Qed.

    (* [comment removed for export] *)
    Lemma rdn_of_m64 : forall (M : word -> option byte) (a : word) (w : Z),
      m64 M (U a) w -> (U a + 8 <= 2 ^ 64)%Z ->
      exists bs, rdn segs M a 8 = Some bs /\ length bs = 8%nat /\ bytes_le_to_Z bs = w.
    Proof using Gobj Gframe Gsp bp this sp.
      intros M a w (bs & B1 & B2 & B3) Hnw. exists bs. split; [| split; assumption].
      pose proof (u64_range a) as Ha.
      destruct bs as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|x t]]]]]]]]]; cbn in B2; try lia.
      assert (E : forall i : nat, (i < 8)%nat -> M (Z_to_bv 64 (U a + Z.of_nat i)) = Some (nth i [b0; b1; b2; b3; b4; b5; b6; b7] (Z_to_bv 8 0))) by exact B1.
      rewrite <- (rdn_wbytes_hit segs [b0; b1; b2; b3; b4; b5; b6; b7] M a) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia).
      apply rdn_ext; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. cbn [length] in Hx.
      rewrite wbytes_inside by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia). cbn [length Z.of_nat] in *.
      pose proof (u64_range x).
      assert (Ex : x = Z_to_bv 64 (U a + Z.of_nat (Z.to_nat (U x - U a)))) by (apply bv_eq; wd_ulia).
      rewrite Ex at 1. rewrite (E (Z.to_nat (U x - U a))) by lia. reflexivity.
    Qed.

    #[local] Abbreviation lez := bytes_le_to_Z.
    (* [comment removed for export] *)
    Definition uf_foot (x : word) : Prop := (U this + 8 <= U x < U this + 12)%Z \/ (U this + 24 <= U x < U this + 256)%Z.
    Definition uf_slots (M : word -> option byte) : Prop :=
      forall (c : Z) (x : word),
        In (c, x) [(-8, ra); (-16, getr regs 8); (-24, getr regs 9); (-32, getr regs 18); (-40, getr regs 19);
                   (-48, getr regs 20); (-56, getr regs 21); (-64, getr regs 22)]%Z ->
        rdn segs M (at_ sp c) 8 = Some (LE8 x).

    Lemma uf_slots_keep : forall M M' : word -> option byte,
      uf_slots M -> (forall x : word, (U x < U sp)%Z -> M' x = M x) -> uf_slots M'.
    Proof using GS Gobj Gframe Gsp bp this.
      intros M M' RD HM c x Hin. pose proof (u64_range sp).
      assert (Hc : (-64 <= c <= -8)%Z) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E; intros; lia|]); destruct Hin).
      apply (rd_same M' M); [intros y Hy; apply HM; rewrite at_u in Hy; lia | rewrite at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (RD c x Hin)].
    Qed.

    Ltac cldb F D bs0 Hr :=
      chain_step; [reflexivity
        | eapply step_ld with (bs := bs0) (v := Z_to_bv 64 (bytes_le_to_Z bs0));
          [exact F | reflexivity | exact D | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi; zlit_at; Hr | unorm; reflexivity]
        | step_simpl]; vn.

    (* [comment removed for export] *)
    Lemma uf_exit : forall (M M1 : word -> option byte) r1 (k s : Z) (bnd : Z),
      getr r1 2 = at_ sp (-64) -> getr r1 10 = this -> getr r1 11 = pc0 -> regs_agree CLX regs r1 ->
      uf_slots M1 -> (k <= s <= 30)%Z -> (s <= k + 1)%Z -> (0 <= bnd)%Z -> rdn segs M1 (at_ this 8) 4 = Some (LE4 s) ->
      (forall x : word, M1 x <> M x -> uf_foot x) -> mem_grows M M1 ->
      exists r' M' (s' : Z),
        msteps segs (mkst r1 (at_ base 252) M1 rom) (mkst r' ra M' rom)
        /\ getr r' 10 = this /\ getr r' 11 = pc0 /\ regs_agree CL regs r'
        /\ (k <= s' <= 30)%Z /\ (s' <= k + 1 + bnd)%Z
        /\ rdn segs M' (at_ this 8) 4 = Some (LE4 s')
        /\ (forall x : word, M' x <> M x -> uf_foot x)
        /\ mem_grows M M'.
    Proof using Gobj Gframe Gsp H15 H14 H13 H12 H2 H1 Hret bot top bp HCODE.
      intros M M1 r1 k s bnd Q2 Q10 Q11 QAG QRD Hs1 Hs2 Hb QSZ QF QG.
      destruct (uf_epi M1 r1 Q2 Q10 Q11 QRD QAG) as (r' & RUN & P10 & P11 & PAG).
      exists r', M1, s. repeat (split; [first [exact RUN | exact P10 | exact P11 | exact PAG | exact QSZ | exact QF | lia] |]). exact QG.
    Qed.

    (* [comment removed for export] *)
    Definition uf_step (M : word -> option byte) (k k1 : Z) (r : word) : word -> option byte :=
      if Z.eqb k1 k then M else uf_upd M k r.

    Lemma uf_head : forall (M : word -> option byte) r0 (v : word) (k : Z) (bsr : list byte),
      getr r0 2 = at_ sp (-64) -> getr r0 10 = this -> getr r0 11 = pc0 -> getr r0 12 = v ->
      getr r0 13 = Z_to_bv 64 4096 -> getr r0 14 = at_ this 16 -> getr r0 15 = Z_to_bv 64 k ->
      getr r0 8 = Z_to_bv 64 30 -> getr r0 9 = at_ top (-16) -> regs_agree CLX regs r0 ->
      (1 <= k < 30)%Z -> (U bp <= U v)%Z -> (U v + 16 < 2 ^ 47)%Z ->
      rdn segs M (at_ v (-8)) 8 = Some bsr -> length bsr = 8%nat -> (4096 <= lez bsr)%Z ->
      mem_grows mem M ->
      exists r1 (k1 : Z),
        msteps segs (mkst r0 (at_ base 192) M rom) (mkst r1 (at_ base 228) (uf_step M k k1 (Z_to_bv 64 (lez bsr))) rom)
        /\ getr r1 2 = at_ sp (-64) /\ getr r1 10 = this /\ getr r1 11 = pc0 /\ getr r1 12 = v
        /\ getr r1 13 = Z_to_bv 64 4096 /\ getr r1 14 = at_ this 16 /\ getr r1 15 = Z_to_bv 64 k1
        /\ getr r1 8 = Z_to_bv 64 30 /\ getr r1 9 = at_ top (-16) /\ regs_agree CLX regs r1
        /\ (k1 = k \/ k1 = k + 1)%Z.
    Proof using Hobj Gobj Gframe Gsp HCODE.
      intros M r0 v k bsr R2 R10 R11 R12 R13 R14 R15 R8 R9 AG0 Hk HSv Hv Rr Lr Hr4 GR.
      pose proof (u64_range sp) as Hspr. pose proof (u64_range this) as Hth. pose proof (u64_range top) as Htop.
      pose proof (u64_range bp) as HS. pose proof (u64_range v) as Hvr. pose proof (u64_range pc0) as Hpc0.
      pose proof (bytes_le_to_Z_bound bsr) as Br. rewrite Lr in Br. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in Br.
      pose proof (bytes_le_to_Z_nonneg bsr) as Br0.
      destruct (Z.eq_dec (lez bsr) (U pc0)) as [Epc|Npc].
      - (* [comment removed for export] *)
        eexists _, k. split.
        + ab_ft Fo192 D_8f4c4 ltac:(condz).                (* [comment removed for export] *)
          cldb Fo196 D_8f4c8 bsr ltac:(exact Rr).           (* [comment removed for export] *)
          ab_ft Fo200 D_8f4cc ltac:(condz).                (* [comment removed for export] *)
          ab_tk Fo204 D_8f4d0 ltac:(rwH; (lazymatch goal with |- ?G => let G' := eval unfold c_eq, bv_eqb in G in change_no_check G' end); unorm; apply Z.eqb_eq; exact Epc).   (* [comment removed for export] *)
          (lazymatch goal with |- ?G => let G' := eval unfold uf_step in G in change_no_check G' end). rewrite Z.eqb_refl. wd_refl.
        + post. (lazymatch goal with |- ?G => let G' := eval unfold uf_clobx in G in change_no_check G' end). ra_chain.
      - (* [comment removed for export] *)
        eexists _, (k + 1)%Z. split.
        + ab_ft Fo192 D_8f4c4 ltac:(condz).
          cldb Fo196 D_8f4c8 bsr ltac:(exact Rr).
          ab_ft Fo200 D_8f4cc ltac:(condz).
          ab_ft Fo204 D_8f4d0 ltac:(rwH; (lazymatch goal with |- ?G => let G' := eval unfold c_eq, bv_eqb in G in change_no_check G' end); unorm; apply Z.eqb_neq; exact Npc).   (* [comment removed for export] *)
          av Fo208 D_8f4d4 (Z_to_bv 64 (8 * k)) ltac:(rewrite v_slli_mul by lia; unorm; f_equal; lia).   (* [comment removed for export] *)
          av Fo212 D_8f4d8 (Z_to_bv 64 (k + 1)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; reflexivity).              (* [comment removed for export] *)
          av Fo216 D_8f4dc (at_ this (16 + 8 * k)) ltac:(rewrite v_add_at by lia; rewrite at_at; reflexivity).   (* [comment removed for export] *)
          fsw_g Fo220 D_8f4e0 (at_ this 8) ltac:(sok8G GR Hobj (at_ this 8) 248%nat).                   (* [comment removed for export] *)
          fsd_g Fo224 D_8f4e4 (at_ this (16 + 8 * k)) ltac:(sok8G GR Hobj (at_ this 8) 248%nat).        (* [comment removed for export] *)
          (lazymatch goal with |- ?G => let G' := eval unfold uf_step in G in change_no_check G' end). replace (Z.eqb (k + 1) k) with false by (symmetry; apply Z.eqb_neq; lia).
          (lazymatch goal with |- ?G => let G' := eval unfold uf_upd in G in change_no_check G' end). wd_refl.
        + post. (lazymatch goal with |- ?G => let G' := eval unfold uf_clobx in G in change_no_check G' end). ra_chain.
    Qed.

    (* [comment removed for export] *)
    Lemma uf_tail : forall (d : nat) (M1 : word -> option byte) r1 (v : word) (k1 : Z) (bsw : list byte),
      getr r1 2 = at_ sp (-64) -> getr r1 10 = this -> getr r1 11 = pc0 -> getr r1 12 = v ->
      getr r1 13 = Z_to_bv 64 4096 -> getr r1 14 = at_ this 16 -> getr r1 15 = Z_to_bv 64 k1 ->
      getr r1 8 = Z_to_bv 64 30 -> getr r1 9 = at_ top (-16) -> regs_agree CLX regs r1 ->
      (U bp <= U v)%Z -> (U v + 16 < 2 ^ 47)%Z ->
      rdn segs mem (at_ v (-16)) 8 = Some bsw -> length bsw = 8%nat ->
      fpc mem (lez bsw) (U v) d ->
      (forall x : word, (U bp - 16 <= U x)%Z -> M1 x = mem x) ->
      (exists r2, msteps segs (mkst r1 (at_ base 228) M1 rom) (mkst r2 (at_ base 252) M1 rom)
                  /\ getr r2 2 = at_ sp (-64) /\ getr r2 10 = this /\ getr r2 11 = pc0 /\ regs_agree CLX regs r2)
      \/ (exists r2 d' (bsr' bsw' : list byte), d = S d'
            /\ msteps segs (mkst r1 (at_ base 228) M1 rom) (mkst r2 (at_ base 192) M1 rom)
            /\ getr r2 2 = at_ sp (-64) /\ getr r2 10 = this /\ getr r2 11 = pc0 /\ getr r2 12 = Z_to_bv 64 (lez bsw)
            /\ getr r2 13 = Z_to_bv 64 4096 /\ getr r2 14 = at_ this 16 /\ getr r2 15 = Z_to_bv 64 k1
            /\ getr r2 8 = Z_to_bv 64 30 /\ getr r2 9 = at_ top (-16) /\ regs_agree CLX regs r2
            /\ (U bp <= lez bsw)%Z /\ (lez bsw + 16 < 2 ^ 47)%Z
            /\ rdn segs mem (at_ (Z_to_bv 64 (lez bsw)) (-8)) 8 = Some bsr' /\ length bsr' = 8%nat
            /\ rdn segs mem (at_ (Z_to_bv 64 (lez bsw)) (-16)) 8 = Some bsw' /\ length bsw' = 8%nat
            /\ fpc mem (lez bsw') (lez bsw) d').
    Proof using Gtop Gobj Gframe Gsp HCODE.
      intros d M1 r1 v k1 bsw R2 R10 R11 R12 R13 R14 R15 R8 R9 AG0 HSv Hv Rw Lw FPC HM1.
      pose proof (u64_range sp) as Hspr. pose proof (u64_range this) as Hth. pose proof (u64_range top) as Htop.
      pose proof (u64_range bp) as HS. pose proof (u64_range v) as Hvr.
      pose proof (bytes_le_to_Z_bound bsw) as Bw. rewrite Lw in Bw. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in Bw.
      pose proof (bytes_le_to_Z_nonneg bsw) as Bw0.
      assert (Rw1 : rdn segs M1 (at_ v (-16)) 8 = Some bsw).
      { apply (rd_same M1 mem); [intros x Hx; apply HM1; rewrite at_u in Hx by lia; lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Rw]. }
      destruct (Z.lt_ge_cases (U v) (lez bsw)) as [C1|C1].
      2:{ left. wd_eexists. split.
          - cldb Fo228 D_8f4e8 bsw ltac:(exact Rw1).        (* [comment removed for export] *)
            ab_tk Fo232 D_8f4ec ltac:(condz).              (* [comment removed for export] *)
            wd_refl.
          - post. (lazymatch goal with |- ?G => let G' := eval unfold uf_clobx in G in change_no_check G' end). ra_chain. }
      destruct (Z.lt_ge_cases (lez bsw) (U top - 16)) as [C2|C2].
      2:{ left. wd_eexists. split.
          - cldb Fo228 D_8f4e8 bsw ltac:(exact Rw1).
            ab_ft Fo232 D_8f4ec ltac:(condz).
            ab_tk Fo236 D_8f4f0 ltac:(condz).              (* [comment removed for export] *)
            wd_refl.
          - post. (lazymatch goal with |- ?G => let G' := eval unfold uf_clobx in G in change_no_check G' end). ra_chain. }
      destruct (Z.eq_dec (lez bsw mod 8) 0) as [C3|C3].
      2:{ left. wd_eexists. split.
          - cldb Fo228 D_8f4e8 bsw ltac:(exact Rw1).
            ab_ft Fo232 D_8f4ec ltac:(condz).
            ab_ft Fo236 D_8f4f0 ltac:(condz).
            av Fo240 D_8f4f4 (Z_to_bv 64 (lez bsw mod 8)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_andi in G in change_no_check G' end); change (bv_wrap 64 7) with 7%Z; unorm; rewrite land_7 by lia; reflexivity).  (* [comment removed for export] *)
            an Fo244 D_8f4f8.                                (* [comment removed for export] *)
            pose proof (Z.mod_pos_bound (lez bsw) 8 ltac:(lia)).
            ab_ft Fo248 D_8f4fc ltac:(condz).              (* [comment removed for export] *)
            wd_refl.
          - post. (lazymatch goal with |- ?G => let G' := eval unfold uf_clobx in G in change_no_check G' end). ra_chain. }
      (* [comment removed for export] *)
      right.
      inversion FPC as [v0 lo0 d0 ST E1 E2 E3 | v0 lo0 d' w2 H16 H8 HP DEF RD64 CH E1 E2 E3]; subst v0 lo0.
      { exfalso. unfold PTRHI in ST. lia. }
      subst d.
      assert (Uw : U (Z_to_bv 64 (lez bsw)) = lez bsw) by (unorm; reflexivity).
      destruct (rdn_of_m64 mem (at_ (Z_to_bv 64 (lez bsw)) (-16)) w2) as (bsw' & Rw' & Lw' & Ew').
      { rewrite at_u by (rewrite Uw; lia). rewrite Uw. exact RD64. }
      { rewrite at_u by (rewrite Uw; lia). rewrite Uw. lia. }
      destruct (rdn_some_of_defined mem 8 (at_ (Z_to_bv 64 (lez bsw)) (-8))) as (bsr' & Rr' & Lr').
      { intros i Hi. rewrite at_u in Hi by (rewrite Uw; lia). rewrite Uw in Hi. apply DEF. cbn in Hi. lia. }
      { rewrite at_u by (rewrite Uw; lia). rewrite Uw. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
      eexists _, d', bsr', bsw'. split; [reflexivity|]. split.
      - cldb Fo228 D_8f4e8 bsw ltac:(exact Rw1).
        ab_ft Fo232 D_8f4ec ltac:(condz).
        ab_ft Fo236 D_8f4f0 ltac:(condz).
        av Fo240 D_8f4f4 (Z_to_bv 64 0) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_andi in G in change_no_check G' end); change (bv_wrap 64 7) with 7%Z; unorm; rewrite land_7 by lia; rewrite C3; reflexivity).
        an Fo244 D_8f4f8.
        ab_tk Fo248 D_8f4fc ltac:(condz).                  (* [comment removed for export] *)
        wd_refl.
      - post. 1: ((lazymatch goal with |- ?G => let G' := eval unfold uf_clobx in G in change_no_check G' end); ra_chain). all: try lia. all: try assumption. rewrite Ew'. exact CH.
    Qed.

    Lemma uf_step_outside : forall M k k1 r (x : word), (1 <= k < 30)%Z ->
      (U x < U this + 8 \/ U this + 256 <= U x)%Z -> uf_step M k k1 r x = M x.
    Proof using GS Gobj Gframe Gsp bp sp.
      intros M k k1 r x Hk Hx. (lazymatch goal with |- ?G => let G' := eval unfold uf_step in G in change_no_check G' end). destruct (Z.eqb k1 k); [reflexivity|]. apply uf_upd_outside; lia.
    Qed.
    Lemma uf_step_grows : forall M k k1 r, mem_grows M (uf_step M k k1 r).
    Proof using.
      intros M k k1 r. (lazymatch goal with |- ?G => let G' := eval unfold uf_step, uf_upd in G in change_no_check G' end). destruct (Z.eqb k1 k); [apply mem_grows_refl|].
      eapply mem_grows_trans; apply wbytes_grows.
    Qed.
    Lemma uf_step_frame : forall M k k1 r (x : word), (1 <= k < 30)%Z ->
      uf_step M k k1 r x <> M x -> uf_foot x.
    Proof using GS Gobj Gframe Gsp bp sp.
      intros M k k1 r x Hk Hx. pose proof (u64_range x). pose proof (u64_range this). (lazymatch goal with |- ?G => let G' := eval unfold uf_foot in G in change_no_check G' end).
      unfold uf_step in Hx. destruct (Z.eqb k1 k); [exfalso; exact (Hx eq_refl)|].
      destruct (Z.lt_ge_cases (U x) (U this + 8)); [exfalso; apply Hx; apply uf_upd_outside; lia|].
      destruct (Z.lt_ge_cases (U x) (U this + 12)); [left; lia|].
      destruct (Z.lt_ge_cases (U x) (U this + 16 + 8 * k)); [exfalso; apply Hx; apply uf_upd_outside; lia|].
      destruct (Z.lt_ge_cases (U x) (U this + 24 + 8 * k)); [right; lia|].
      exfalso; apply Hx; apply uf_upd_outside; lia.
    Qed.
    Lemma uf_step_sz : forall M k k1 r, (1 <= k < 30)%Z -> (k1 = k \/ k1 = k + 1)%Z ->
      rdn segs M (at_ this 8) 4 = Some (LE4 k) -> rdn segs (uf_step M k k1 r) (at_ this 8) 4 = Some (LE4 k1).
    Proof using GS Gobj Gframe Gsp bp sp.
      intros M k k1 r Hk [-> | ->] R; (lazymatch goal with |- ?G => let G' := eval unfold uf_step in G in change_no_check G' end).
      - rewrite Z.eqb_refl. exact R.
      - replace (Z.eqb (k + 1) k) with false by (symmetry; apply Z.eqb_neq; lia). (lazymatch goal with |- ?G => let G' := eval unfold uf_upd in G in change_no_check G' end).
        pose proof (u64_range this).
        rewrite rdn_wbytes_out; [ | rewrite length_N_to_le_bytes, !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ].
        pose proof (rdn_wbytes_hit segs (LE4 (k + 1)) M (at_ this 8)) as X. rewrite length_N_to_le_bytes in X.
        apply X. rewrite at_u by lia. lia.
    Qed.

    (* [comment removed for export] *)
    Record uf_inv (d : nat) (M : word -> option byte) (r0 : bvmap 5 word) (v : word) (k : Z) (bsr bsw : list byte) : Prop := UFI {
      ui_r2 : getr r0 2 = at_ sp (-64); ui_r10 : getr r0 10 = this; ui_r11 : getr r0 11 = pc0; ui_r12 : getr r0 12 = v;
      ui_r13 : getr r0 13 = Z_to_bv 64 4096; ui_r14 : getr r0 14 = at_ this 16; ui_r15 : getr r0 15 = Z_to_bv 64 k;
      ui_r8 : getr r0 8 = Z_to_bv 64 30; ui_r9 : getr r0 9 = at_ top (-16); ui_ag : regs_agree CLX regs r0;
      ui_k : (1 <= k <= 30)%Z; ui_bpv : (U bp <= U v)%Z; ui_v : (U v + 16 < 2 ^ 47)%Z;
      ui_rr : rdn segs mem (at_ v (-8)) 8 = Some bsr; ui_lr : length bsr = 8%nat;
      ui_rw : rdn segs mem (at_ v (-16)) 8 = Some bsw; ui_lw : length bsw = 8%nat;
      ui_fpc : fpc mem (lez bsw) (U v) d;
      ui_hm : forall x : word, (U bp - 16 <= U x)%Z -> M x = mem x;
      ui_gr : mem_grows mem M; ui_slots : uf_slots M;
      ui_sz : rdn segs M (at_ this 8) 4 = Some (LE4 k) }.
  (* [comment removed for export] *)

    (* [comment removed for export] *)
    Lemma uf_round : forall (d : nat) (M : word -> option byte) r0 (v : word) (k : Z) (bsr bsw : list byte),
      uf_inv d M r0 v k bsr bsw ->
      (exists r' M' (s : Z),
        msteps segs (mkst r0 (at_ base 192) M rom) (mkst r' ra M' rom)
        /\ getr r' 10 = this /\ getr r' 11 = pc0 /\ regs_agree CL regs r'
        /\ (k <= s <= 30)%Z /\ (s <= k + 1)%Z
        /\ rdn segs M' (at_ this 8) 4 = Some (LE4 s)
        /\ (forall x : word, M' x <> M x -> uf_foot x)
        /\ mem_grows M M')
      \/ (exists d' M1 r1 v1 k1 bsr' bsw', d = S d' /\ uf_inv d' M1 r1 v1 k1 bsr' bsw'
        /\ msteps segs (mkst r0 (at_ base 192) M rom) (mkst r1 (at_ base 192) M1 rom)
        /\ (k <= k1 <= k + 1)%Z
        /\ (forall x : word, M1 x <> M x -> uf_foot x)
        /\ mem_grows M M1).
    Proof using Hobj Gtop GS Gobj Gframe Gsp H15 H14 H13 H12 H2 H1 Hret bot HCODE.
      intros d M r0 v k bsr bsw [R2 R10 R11 R12 R13 R14 R15 R8 R9 AG0 Hk HSv Hv Rr Lr Rw Lw FPC HM GR RD RSZ].
      pose proof (u64_range sp) as Hspr. pose proof (u64_range this) as Hth. pose proof (u64_range top) as Htop.
      pose proof (u64_range bp) as Hbp. pose proof (u64_range v) as Hvr.
      pose proof (bytes_le_to_Z_bound bsr) as Br. rewrite Lr in Br. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in Br.
      pose proof (bytes_le_to_Z_nonneg bsr) as Br0.
      assert (Rr1 : rdn segs M (at_ v (-8)) 8 = Some bsr)
        by (apply (rd_same M mem); [intros x Hx; apply HM; rewrite at_u in Hx by lia; lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Rr]).
      destruct (Z.lt_ge_cases k 30) as [Hk30|Hk30].
      2:{ (* [comment removed for export] *)
          left.
          assert (W : exists r1, msteps segs (mkst r0 (at_ base 192) M rom) (mkst r1 (at_ base 252) M rom)
                       /\ getr r1 2 = at_ sp (-64) /\ getr r1 10 = this /\ getr r1 11 = pc0 /\ regs_agree CLX regs r1).
          { wd_eexists. split.
            { ab_tk Fo192 D_8f4c4 ltac:(condz).              (* [comment removed for export] *)
              wd_refl. }
            post; (lazymatch goal with |- ?G => let G' := eval unfold uf_clobx in G in change_no_check G' end); ra_chain. }
          destruct W as (r1 & W & Q2 & Q10 & Q11 & QAG).
          destruct (uf_exit M M r1 k k 0 Q2 Q10 Q11 QAG RD ltac:(lia) ltac:(lia) ltac:(lia) RSZ ltac:(intros x Hx; exfalso; exact (Hx eq_refl)) (mem_grows_refl M))
            as (r' & M' & s' & RUN & X).
          exists r', M', s'. split; [eapply msteps_trans; [exact W | exact RUN] | ].
          destruct X as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). repeat (split; [first [eassumption | lia]|]). exact A8. }
      destruct (Z.lt_ge_cases (lez bsr) 4096) as [Hr4|Hr4].
      { (* [comment removed for export] *)
        left.
        assert (W : exists r1, msteps segs (mkst r0 (at_ base 192) M rom) (mkst r1 (at_ base 252) M rom)
                     /\ getr r1 2 = at_ sp (-64) /\ getr r1 10 = this /\ getr r1 11 = pc0 /\ regs_agree CLX regs r1).
        { wd_eexists. split.
          { ab_ft Fo192 D_8f4c4 ltac:(condz).
            cldb Fo196 D_8f4c8 bsr ltac:(exact Rr1).         (* [comment removed for export] *)
            ab_tk Fo200 D_8f4cc ltac:(condz).                (* [comment removed for export] *)
            wd_refl. }
          post; (lazymatch goal with |- ?G => let G' := eval unfold uf_clobx in G in change_no_check G' end); ra_chain. }
        destruct W as (r1 & W & Q2 & Q10 & Q11 & QAG).
        destruct (uf_exit M M r1 k k 0 Q2 Q10 Q11 QAG RD ltac:(lia) ltac:(lia) ltac:(lia) RSZ ltac:(intros x Hx; exfalso; exact (Hx eq_refl)) (mem_grows_refl M))
          as (r' & M' & s' & RUN & X).
        exists r', M', s'. split; [eapply msteps_trans; [exact W | exact RUN] | ].
        destruct X as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). repeat (split; [first [eassumption | lia]|]). exact A8. }
      destruct (uf_head M r0 v k bsr R2 R10 R11 R12 R13 R14 R15 R8 R9 AG0 ltac:(lia) HSv Hv Rr1 Lr Hr4 GR)
        as (r1 & k1 & RUN1 & Q2 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q8 & Q9 & QAG & Hk1).
      set (M1 := uf_step M k k1 (Z_to_bv 64 (lez bsr))) in *.
      assert (HM1 : forall x : word, (U bp - 16 <= U x)%Z -> M1 x = mem x).
      { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). rewrite uf_step_outside by lia. apply HM. exact Hx. }
      assert (FR1 : forall x : word, M1 x <> M x -> uf_foot x) by (intros x; (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end); apply uf_step_frame; lia).
      assert (GR1 : mem_grows M M1) by ((lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end); apply uf_step_grows).
      assert (SZ1 : rdn segs M1 (at_ this 8) 4 = Some (LE4 k1)) by ((lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end); apply uf_step_sz; [lia | exact Hk1 | exact RSZ]).
      assert (SL1 : uf_slots M1) by (apply (uf_slots_keep M M1 RD); intros x Hx; (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end); apply uf_step_outside; lia).
      destruct (uf_tail d M1 r1 v k1 bsw Q2 Q10 Q11 Q12 Q13 Q14 Q15 Q8 Q9 QAG HSv Hv Rw Lw FPC HM1)
        as [(r2 & RUN2 & P2 & P10 & P11 & PAG) | (r2 & d' & bsr' & bsw' & Ed & RUN2 & P2 & P10 & P11 & P12 & P13 & P14 & P15 & P8 & P9 & PAG & B1 & B2 & Rr' & Lr' & Rw' & Lw' & FPC')].
      - left.
        destruct (uf_exit M M1 r2 k k1 0 P2 P10 P11 PAG SL1 ltac:(lia) ltac:(lia) ltac:(lia) SZ1 FR1 GR1) as (r' & M' & s' & RUN & X).
        exists r', M', s'. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2|]; exact RUN |].
        destruct X as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). repeat (split; [first [eassumption | lia]|]). exact A8.
      - right. exists d', M1, r2, (Z_to_bv 64 (lez bsw)), k1, bsr', bsw'. split; [exact Ed|]. split.
        + pose proof (bytes_le_to_Z_bound bsw) as Bw. rewrite Lw in Bw. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in Bw.
          pose proof (bytes_le_to_Z_nonneg bsw) as Bw0.
          assert (Uw : U (Z_to_bv 64 (lez bsw)) = lez bsw) by (unorm; reflexivity).
          constructor; try assumption; try (rewrite Uw; assumption); try lia.
          eapply mem_grows_trans; [exact GR | exact GR1].
        + split; [| split; [lia | split; [exact FR1 | exact GR1]]].
          eapply msteps_trans; [exact RUN1 | exact RUN2].
    Qed.

    (* [comment removed for export] *)
    Lemma uf_loop : forall (d : nat) (M : word -> option byte) r0 (v : word) (k : Z) (bsr bsw : list byte),
      uf_inv d M r0 v k bsr bsw ->
      exists r' M' (s : Z),
        msteps segs (mkst r0 (at_ base 192) M rom) (mkst r' ra M' rom)
        /\ getr r' 10 = this /\ getr r' 11 = pc0 /\ regs_agree CL regs r'
        /\ (k <= s <= 30)%Z /\ (s <= k + 1 + Z.of_nat d)%Z
        /\ rdn segs M' (at_ this 8) 4 = Some (LE4 s)
        /\ (forall x : word, M' x <> M x -> uf_foot x)
        /\ mem_grows M M'.
    Proof using Hobj Gtop GS Gobj Gframe Gsp H15 H14 H13 H12 H2 H1 Hret bot HCODE.
      induction d as [|d IH]; intros M r0 v k bsr bsw INV.
      - destruct (uf_round 0%nat M r0 v k bsr bsw INV) as [(r' & M' & s & X) | (d' & M1 & r1 & v1 & k1 & bsr' & bsw' & Ed & _)]; [|discriminate Ed].
        exists r', M', s. destruct X as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9). repeat (split; [first [eassumption | lia]|]). exact A9.
      - destruct (uf_round (S d) M r0 v k bsr bsw INV) as [(r' & M' & s & X) | (d' & M1 & r1 & v1 & k1 & bsr' & bsw' & Ed & INV1 & RUN1 & Hk1 & FR1 & GR1)].
        + exists r', M', s. destruct X as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9). repeat (split; [first [eassumption | lia]|]). exact A9.
        + injection Ed as <-.
          destruct (IH M1 r1 v1 k1 bsr' bsw' INV1) as (r' & M' & s & RUN & P10 & P11 & PAG & S1 & S2 & SZ & FR & GR).
          exists r', M', s. split; [eapply msteps_trans; [exact RUN1 | exact RUN]|].
          repeat (split; [first [eassumption | lia]|]).
          split; [| eapply mem_grows_trans; [exact GR1 | exact GR]].
          intros x Hx. destruct (decide (M1 x = M x)) as [E|NE]; [apply FR; rewrite E; exact Hx | apply FR1; exact NE].
    Qed.

    (* [comment removed for export] *)
    Theorem uf_run : forall (D : nat) (bsr0 bsw0 : list byte),
      rdn segs mem (at_ bp (-8)) 8 = Some bsr0 -> length bsr0 = 8%nat ->
      rdn segs mem (at_ bp (-16)) 8 = Some bsw0 -> length bsw0 = 8%nat ->
      fpc mem (lez bsw0) (U bp) D ->
      exists r' M' (s : Z),
        msteps segs (mkst regs (at_ base 0) mem rom) (mkst r' ra M' rom)
        /\ getr r' 10 = this /\ getr r' 11 = pc0 /\ regs_agree CL regs r'
        /\ (1 <= s <= 30)%Z /\ (s <= 2 + Z.of_nat D)%Z
        /\ rdn segs M' (at_ this 8) 4 = Some (LE4 s)
        /\ rdn segs M' (at_ this 16) 8 = Some (LE8 pc0)
        /\ (forall x : word, M' x <> mem x -> (U sp - 64 <= U x < U sp)%Z \/ ((U this + 8 <= U x < U this + 12)%Z \/ (U this + 16 <= U x < U this + 256)%Z))
        /\ mem_grows mem M'.
    Proof using Hobj Hstk GP Gg RP Rg P Gbot Gtop GS8 GS Gobj Gframe Gsp H15 H14 H13 H12 H11 H10 H2 H1 Hret bot top G56 HCODE g_pgsz.
      intros D bsr0 bsw0 Rr Lr Rw Lw FPC.
      pose proof (u64_range sp) as Hspr. pose proof (u64_range this) as Hth. pose proof (u64_range top) as Htop. pose proof (u64_range bp) as Hbp.
      destruct uf_pro as (r0 & RUN0 & R2 & R10 & R11 & R12 & R13 & R14 & R15 & R8 & R9 & AG0).
      assert (GR2 : mem_grows mem (uf_mem2 mem)) by ((lazymatch goal with |- ?G => let G' := eval unfold uf_mem2, uf_frame in G in change_no_check G' end); repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
      assert (HM2 : forall x : word, (U bp - 16 <= U x)%Z -> uf_mem2 mem x = mem x) by (intros x Hx; apply uf_mem2_outside; lia).
      assert (SZ2 : rdn segs (uf_mem2 mem) (at_ this 8) 4 = Some (LE4 1)).
      { (lazymatch goal with |- ?G => let G' := eval unfold uf_mem2 in G in change_no_check G' end). rewrite rdn_wbytes_out; [ | rewrite length_N_to_le_bytes, !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ].
        pose proof (rdn_wbytes_hit segs (LE4 1) (uf_frame mem) (at_ this 8)) as X. rewrite length_N_to_le_bytes in X. apply X. rewrite at_u by lia. lia. }
      assert (PC2 : rdn segs (uf_mem2 mem) (at_ this 16) 8 = Some (LE8 pc0)).
      { (lazymatch goal with |- ?G => let G' := eval unfold uf_mem2 in G in change_no_check G' end). apply rdn_wbytes_hit8. rewrite at_u by lia. lia. }
      assert (FR2 : forall x : word, uf_mem2 mem x <> mem x -> (U sp - 64 <= U x < U sp)%Z \/ ((U this + 8 <= U x < U this + 12)%Z \/ (U this + 16 <= U x < U this + 256)%Z)).
      { intros x Hx. pose proof (u64_range x).
        destruct (Z.lt_ge_cases (U x) (U sp - 64)); [exfalso; apply Hx; apply uf_mem2_outside; lia|].
        destruct (Z.lt_ge_cases (U x) (U sp)); [left; lia|].
        destruct (Z.lt_ge_cases (U x) (U this + 8)); [exfalso; apply Hx; apply uf_mem2_outside; lia|].
        destruct (Z.lt_ge_cases (U x) (U this + 12)); [right; left; lia|].
        destruct (Z.lt_ge_cases (U x) (U this + 16)); [exfalso; apply Hx; apply uf_mem2_outside; lia|].
        destruct (Z.lt_ge_cases (U x) (U this + 24)); [right; right; lia|].
        exfalso; apply Hx; apply uf_mem2_outside; lia. }
      (* [comment removed for export] *)
      assert (EARLY : forall r1, msteps segs (mkst r0 (at_ base 164) (uf_mem2 mem) rom) (mkst r1 (at_ base 252) (uf_mem2 mem) rom) ->
                getr r1 2 = at_ sp (-64) -> getr r1 10 = this -> getr r1 11 = pc0 -> regs_agree CLX regs r1 ->
                exists r' M' (s : Z),
                  msteps segs (mkst regs (at_ base 0) mem rom) (mkst r' ra M' rom)
                  /\ getr r' 10 = this /\ getr r' 11 = pc0 /\ regs_agree CL regs r'
                  /\ (1 <= s <= 30)%Z /\ (s <= 2 + Z.of_nat D)%Z
                  /\ rdn segs M' (at_ this 8) 4 = Some (LE4 s)
                  /\ rdn segs M' (at_ this 16) 8 = Some (LE8 pc0)
                  /\ (forall x : word, M' x <> mem x -> (U sp - 64 <= U x < U sp)%Z \/ ((U this + 8 <= U x < U this + 12)%Z \/ (U this + 16 <= U x < U this + 256)%Z))
                  /\ mem_grows mem M').
      { intros r1 W Q2 Q10 Q11 QAG.
        destruct (uf_epi (uf_mem2 mem) r1 Q2 Q10 Q11 (uf_mem2_slots mem) QAG) as (r' & RUN & P10 & P11 & PAG).
        exists r', (uf_mem2 mem), 1%Z.
        split; [eapply msteps_trans; [exact RUN0|]; eapply msteps_trans; [exact W | exact RUN] |].
        repeat (split; [first [eassumption | lia] |]). exact GR2. }
      destruct (Z.lt_ge_cases (U bot) (U bp)) as [C1|C1].
      2:{ eapply EARLY. { ab_tk Fo164 D_8f4a8 ltac:(condz). wd_refl. } all: gres; try assumption; (lazymatch goal with |- ?G => let G' := eval unfold uf_clobx in G in change_no_check G' end); ra_chain. }
      destruct (Z.lt_ge_cases (U bp) (U top - 16)) as [C2|C2].
      2:{ eapply EARLY.
          { ab_ft Fo164 D_8f4a8 ltac:(condz).                (* [comment removed for export] *)
            av Fo168 D_8f4ac (at_ top (-16)) ltac:(reflexivity).   (* [comment removed for export] *)
            ab_tk Fo172 D_8f4b0 ltac:(condz).                (* [comment removed for export] *)
            wd_refl. }
          all: gres; try assumption; (lazymatch goal with |- ?G => let G' := eval unfold uf_clobx in G in change_no_check G' end); ra_chain. }
      (* [comment removed for export] *)
      assert (G8 : (U bp mod 8 = 0)%Z).
      { rewrite (Z_div_mod_eq_full (U bp) 16). rewrite GS8, Z.add_0_r.
        replace (16 * (U bp / 16))%Z with ((2 * (U bp / 16)) * 8)%Z by lia. apply Z_mod_mult. }
      assert (W : exists r1, msteps segs (mkst r0 (at_ base 164) (uf_mem2 mem) rom) (mkst r1 (at_ base 192) (uf_mem2 mem) rom)
                   /\ uf_inv D (uf_mem2 mem) r1 bp 1 bsr0 bsw0).
      { wd_eexists. split.
        { ab_ft Fo164 D_8f4a8 ltac:(condz).
          av Fo168 D_8f4ac (at_ top (-16)) ltac:(reflexivity).
          ab_ft Fo172 D_8f4b0 ltac:(condz).
          av Fo176 D_8f4b4 (Z_to_bv 64 0) ltac:(apply v_andi_7_aligned; exact G8).   (* [comment removed for export] *)
          ab_ft Fo180 D_8f4b8 ltac:(condz).                (* [comment removed for export] *)
          av Fo184 D_8f4bc (at_ this 16) ltac:(reflexivity).   (* [comment removed for export] *)
          an Fo188 D_8f4c0.                                  (* [comment removed for export] *)
          wd_refl. }
        constructor; gres; rewrite ?at_0; try assumption; try reflexivity; try lia.
        - (lazymatch goal with |- ?G => let G' := eval unfold uf_clobx in G in change_no_check G' end). ra_chain.
        - exact (uf_mem2_slots mem). }
      destruct W as (r1 & W & INV).
      destruct (uf_loop D (uf_mem2 mem) r1 bp 1 bsr0 bsw0 INV) as (r' & M' & s & RUN & P10 & P11 & PAG & S1 & S2 & SZ & FR & GR).
      exists r', M', s.
      split; [eapply msteps_trans; [exact RUN0|]; eapply msteps_trans; [exact W | exact RUN] |].
      repeat (split; [first [eassumption | lia] |]).
      split.
      { (* [comment removed for export] *)
        rewrite <- PC2. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx.
        destruct (decide (M' x = uf_mem2 mem x)) as [E|NE]; [exact E|]. exfalso. pose proof (FR x NE) as F. unfold uf_foot in F. lia. }
      split; [| eapply mem_grows_trans; [exact GR2 | exact GR]].
      intros x Hx. destruct (decide (M' x = uf_mem2 mem x)) as [E|NE].
      - apply FR2. rewrite <- E. exact Hx.
      - pose proof (FR x NE) as F. unfold uf_foot in F. right. lia.
    Qed.
  End Run.
End UF.
End FPGen1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPGen1b.
Context {fx : FPState}.

Definition gct_words : list (option (bv 32)) :=
  [Some W_783b4; Some W_783b8; Some W_783bc; Some W_783c0; Some W_783c4; Some W_783c8; Some W_783cc; Some W_783d0]%list.
Definition tsd_words : list (option (bv 32)) :=
  [None; None; Some W_70a3c; Some W_70a40; Some W_70a44; None]%list.
Definition pgs_words : list (option (bv 32)) :=
  [Some W_f7074; Some W_f7078; Some W_f707c; Some W_f7080; Some W_f7084; Some W_f7088; Some W_f708c]%list.
Definition gct_clob : list reg := [10; 11].

(* [comment removed for export] *)
Record gct_tab := GCT { gt_rb : word; gt_tsd : word; gt_pgs : word }.
Record gct_tab_ok (segs : list Segment) (t : gct_tab) : Prop := GCTOK {
  gto_gct : code_ato segs (gt_rb t) 0x783bc gct_words;
  gto_tsd : code_ato segs (gt_rb t) 0x70a3c tsd_words;
  gto_gaddr : gaddr2 segs (gt_rb t) 0x70a3c 10 10 (gt_tsd t);
  gto_jmp : gjump segs (gt_rb t) (0x70a3c + 20) (gt_pgs t);
  gto_pgs : code_ato segs (gt_pgs t) 0 pgs_words;
  gto_rb : (U (gt_rb t) mod 2 = 0)%Z /\ (U (gt_rb t) + 2 ^ 24 < 2 ^ 64)%Z }.

(* [comment removed for export] *)
Record gctH (segs : list Segment) (t : gct_tab) (mem : word -> option byte) (sp tp tsdp tctx thr : word) : Prop := GCTH {
  gh_flag : rdn segs mem (gt_tsd t) 1 = Some [Z_to_bv 8 1];
  gh_key : rdn segs mem (at_ (gt_tsd t) 4) 4 = Some (LE4 0);
  gh_tsdp : rdn segs mem (at_ tp (-88)) 8 = Some (LE8 tsdp);
  gh_tctx : rdn segs mem tsdp 8 = Some (LE8 tctx);
  gh_thr : rdn segs mem (at_ tctx 152) 8 = Some (LE8 thr);
  gh_tctx_nz : U tctx <> 0%Z;
  gh_stk : store_ok segs mem (at_ sp (-8)) 8 = true;
  (* [comment removed for export] *)
  gh_sp : (16 <= U sp)%Z /\ (U sp + 8 <= 2 ^ 64)%Z;
  gh_g1 : (U (gt_tsd t) + 8 <= U sp - 16)%Z;
  gh_g2 : (88 <= U tp)%Z /\ (U tp - 80 <= U sp - 16)%Z;
  gh_g3 : (U tsdp + 8 <= U sp - 16)%Z;
  gh_g4 : (U tctx + 160 <= U sp - 16)%Z }.

(* [comment removed for export] *)
Lemma gctH_keep : forall segs t (mem M' : word -> option byte) (sp tp tsdp tctx thr : word),
  gctH segs t mem sp tp tsdp tctx thr ->
  (forall x : word, (U x < U sp - 16)%Z -> M' x = mem x) -> mem_grows mem M' ->
  gctH segs t M' sp tp tsdp tctx thr.
Proof using.
  intros segs t mem M' sp tp tsdp tctx thr [Rf Rk Rt Rc Rth NZ SOK Gsp G1 G2 G3 G4] HM GR.
  pose proof (u64_range tp). pose proof (u64_range tsdp). pose proof (u64_range tctx). pose proof (u64_range (gt_tsd t)). pose proof (u64_range sp).
  split; try assumption.
  - rewrite <- Rf. apply rdn_ext; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros x Hx; apply HM; cbn in Hx; lia].
  - rewrite <- Rk. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply HM; rewrite at_u in Hx by lia; cbn in Hx; lia].
  - rewrite <- Rt. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply HM; rewrite at_u in Hx by lia; cbn in Hx; lia].
  - rewrite <- Rc. apply rdn_ext; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros x Hx; apply HM; cbn in Hx; lia].
  - rewrite <- Rth. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply HM; rewrite at_u in Hx by lia; cbn in Hx; lia].
  - eapply store_ok_mono; [exact GR | exact SOK].
Qed.

Section GCT.
  Variable segs : list Segment.
  Variable t : gct_tab.
  Hypothesis TOK : gct_tab_ok segs t.
  #[local] Abbreviation rb := (gt_rb t).

  Let HG : code_ato segs rb 0x783bc gct_words := gto_gct _ _ TOK.
  Let HT : code_ato segs rb 0x70a3c tsd_words := gto_tsd _ _ TOK.
  Let HP : code_ato segs (gt_pgs t) 0 pgs_words := gto_pgs _ _ TOK.

  Lemma Go0 : fetch_word segs (at_ rb 0x783bc) = Some W_783b4.  Proof using HG TOK fx. exact (code_ato_get segs rb 0x783bc gct_words 0 _ HG eq_refl). Qed.
  Lemma Go4 : fetch_word segs (at_ rb 0x783c0) = Some W_783b8.  Proof using HG TOK fx. exact (code_ato_get segs rb 0x783bc gct_words 1 _ HG eq_refl). Qed.
  Lemma Go8 : fetch_word segs (at_ rb 0x783c4) = Some W_783bc.  Proof using HG TOK fx. exact (code_ato_get segs rb 0x783bc gct_words 2 _ HG eq_refl). Qed.
  Lemma Go12 : fetch_word segs (at_ rb 0x783c8) = Some W_783c0.  Proof using HG TOK fx. exact (code_ato_get segs rb 0x783bc gct_words 3 _ HG eq_refl). Qed.
  Lemma Go16 : fetch_word segs (at_ rb 0x783cc) = Some W_783c4.  Proof using HG TOK fx. exact (code_ato_get segs rb 0x783bc gct_words 4 _ HG eq_refl). Qed.
  Lemma Go20 : fetch_word segs (at_ rb 0x783d0) = Some W_783c8.  Proof using HG TOK fx. exact (code_ato_get segs rb 0x783bc gct_words 5 _ HG eq_refl). Qed.
  Lemma Go24 : fetch_word segs (at_ rb 0x783d4) = Some W_783cc.  Proof using HG TOK fx. exact (code_ato_get segs rb 0x783bc gct_words 6 _ HG eq_refl). Qed.
  Lemma Go28 : fetch_word segs (at_ rb 0x783d8) = Some W_783d0.  Proof using HG TOK fx. exact (code_ato_get segs rb 0x783bc gct_words 7 _ HG eq_refl). Qed.
  Lemma To8 : fetch_word segs (at_ rb 0x70a44) = Some W_70a3c.  Proof using HT TOK fx. exact (code_ato_get segs rb 0x70a3c tsd_words 2 _ HT eq_refl). Qed.
  Lemma To12 : fetch_word segs (at_ rb 0x70a48) = Some W_70a40.  Proof using HT TOK fx. exact (code_ato_get segs rb 0x70a3c tsd_words 3 _ HT eq_refl). Qed.
  Lemma To16 : fetch_word segs (at_ rb 0x70a4c) = Some W_70a44.  Proof using HT TOK fx. exact (code_ato_get segs rb 0x70a3c tsd_words 4 _ HT eq_refl). Qed.
  Lemma Po0 : fetch_word segs (at_ (gt_pgs t) 0) = Some W_f7074.  Proof using HP TOK fx. exact (code_ato_get segs _ 0 pgs_words 0 _ HP eq_refl). Qed.
  Lemma Po4 : fetch_word segs (at_ (gt_pgs t) 4) = Some W_f7078.  Proof using HP TOK fx. exact (code_ato_get segs _ 0 pgs_words 1 _ HP eq_refl). Qed.
  Lemma Po8 : fetch_word segs (at_ (gt_pgs t) 8) = Some W_f707c.  Proof using HP TOK fx. exact (code_ato_get segs _ 0 pgs_words 2 _ HP eq_refl). Qed.
  Lemma Po12 : fetch_word segs (at_ (gt_pgs t) 12) = Some W_f7080.  Proof using HP TOK fx. exact (code_ato_get segs _ 0 pgs_words 3 _ HP eq_refl). Qed.
  Lemma Po16 : fetch_word segs (at_ (gt_pgs t) 16) = Some W_f7084.  Proof using HP TOK fx. exact (code_ato_get segs _ 0 pgs_words 4 _ HP eq_refl). Qed.
  Lemma Po20 : fetch_word segs (at_ (gt_pgs t) 20) = Some W_f7088.  Proof using HP TOK fx. exact (code_ato_get segs _ 0 pgs_words 5 _ HP eq_refl). Qed.
  Lemma Po24 : fetch_word segs (at_ (gt_pgs t) 24) = Some W_f708c.  Proof using HP TOK fx. exact (code_ato_get segs _ 0 pgs_words 6 _ HP eq_refl). Qed.

  Theorem gct_run : forall mem rom regs (ra sp tp tsdp tctx thr : word),
    gctH segs t mem sp tp tsdp tctx thr ->
    ret_ok ra -> getr regs 1 = ra -> getr regs 2 = sp -> getr regs 4 = tp ->
    exists r,
      msteps segs (mkst regs (at_ rb 0x783bc) mem rom) (mkst r ra (wbytes mem (at_ sp (-8)) (LE8 ra)) rom)
      /\ getr r 10 = thr /\ getr r 11 = tsdp
      /\ regs_agree (fun x => In x gct_clob) regs r.
  Proof using HP HT HG TOK.
    intros mem rom regs ra sp tp tsdp tctx thr [Rf Rk Rt Rc Rth NZ SOK Gsp G1 G2 G3 G4] Hret H1 H2 H4.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range tp) as Htp. pose proof (u64_range tsdp) as Htsdp.
    pose proof (u64_range tctx) as Htc. pose proof (u64_range (gt_tsd t)) as Htsd.
    destruct (gto_gaddr _ _ TOK) as [gx GA]. pose proof (gto_jmp _ _ TOK) as GJ.
    set (M1 := wbytes mem (at_ sp (-8)) (LE8 ra)).
    assert (HM1 : forall x : word, (U x < U sp - 8 \/ U sp <= U x)%Z -> M1 x = mem x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). rewrite wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia. reflexivity. }
    Ltac rdM1 HM1 Hr := apply (rd_same _ _ _ _ _ _ ) || idtac.
    wd_eexists. split; [|split; [|split]].
    - an Go0 D_783b4.                                   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sd_at with (a := at_ sp (-8));
          [exact Go4 | reflexivity | exact D_783b8 | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia] | gres; rwH; reflexivity | exact SOK ]
        | step_simpl]; vn.                                (* [comment removed for export] *)
      change (wbytes _ _ _) with M1.
      an Go8 D_783bc.                                   (* [comment removed for export] *)
      eapply msteps_trans; [apply GA|]. zlit_at.          (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lbu with (b := Z_to_bv 8 1);
          [exact To8 | reflexivity | exact D_70a3c
          | gres; rwH; imm_norm; rewrite ?v_addi_0; rewrite <- Rf; apply rdn_ext; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros x Hx; apply HM1; cbn in Hx; lia] ]
        | step_simpl]; vn.                                (* [comment removed for export] *)
      ab_ft To12 D_70a40 ltac:(condz).                  (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lw with (bs := LE4 0) (v := Z_to_bv 64 0);
          [exact To16 | reflexivity | exact D_70a44
          | gres; rwH; imm_norm; rewrite ?at_addi; change (v_addi (gt_tsd t) 4) with (at_ (gt_tsd t) 4); rewrite <- Rk; apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply HM1; rewrite at_u in Hx by lia; cbn in Hx; lia]
          | apply bytes4_small; lia ]
        | step_simpl]; vn.                                (* [comment removed for export] *)
      eapply msteps_trans; [apply GJ|].                   (* [comment removed for export] *)
      rewrite <- (at_0 (gt_pgs t)).
      an Po0 D_f7074.                                    (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 tsdp) (v := tsdp);
          [exact Po4 | reflexivity | exact D_f7078
          | gres; rwH; imm_norm; change (v_addi tp (-88)) with (at_ tp (-88)); rewrite <- Rt; apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply HM1; rewrite at_u in Hx by lia; cbn in Hx; lia]
          | apply bytes_le_to_Z_8 ]
        | step_simpl]; vn.                                (* [comment removed for export] *)
      an Po8 D_f707c.                                    (* [comment removed for export] *)
      an Po12 D_f7080.                                   (* [comment removed for export] *)
      av Po16 D_f7084 tsdp ltac:(rewrite v_add_0_r; reflexivity).   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 tctx) (v := tctx);
          [exact Po20 | reflexivity | exact D_f7088
          | gres; rwH; imm_norm; rewrite ?v_addi_0; rewrite <- Rc; apply rdn_ext; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros x Hx; apply HM1; cbn in Hx; lia]
          | apply bytes_le_to_Z_8 ]
        | step_simpl]; vn.                                (* [comment removed for export] *)
      assert (RA1 : ret_ok (at_ rb 0x783c8)) by (destruct (gto_rb _ _ TOK) as [E1 E2]; apply ret_ok_at; [exact E1 | reflexivity | pose proof (u64_range rb); lia]).
      aret Po24 D_f708c (at_ rb 0x783c8).                (* [comment removed for export] *)
      ab_ft Go12 D_783c0 ltac:(rwH; (lazymatch goal with |- ?G => let G' := eval unfold c_eq, bv_eqb in G in change_no_check G' end); apply Z.eqb_neq; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); exact NZ || (unorm; exact NZ)).   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 thr) (v := thr);
          [exact Go16 | reflexivity | exact D_783c4
          | gres; rwH; imm_norm; change (v_addi tctx 152) with (at_ tctx 152); rewrite <- Rth; apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply HM1; rewrite at_u in Hx by lia; cbn in Hx; lia]
          | apply bytes_le_to_Z_8 ]
        | step_simpl]; vn.                                (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 ra) (v := ra);
          [exact Go20 | reflexivity | exact D_783c8
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end); apply rdn_wbytes_hit8; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]
          | apply bytes_le_to_Z_8 ]
        | step_simpl]; vn.                                (* [comment removed for export] *)
      an Go24 D_783cc.                                    (* [comment removed for export] *)
      aret Go28 D_783d0 ra.                               (* [comment removed for export] *)
      wd_refl.
    - gres. reflexivity.
    - gres. reflexivity.
    - apply (regs_agree_strengthen gct_clob [1; 2; 10; 11] regs).
      + ra_solve.
      + intros i Hi Hni. cbn [In] in Hi.
        repeat (destruct Hi as [<-|Hi]; [gres; rwH; rewrite ?at_addi, ?at_0; first [reflexivity | symmetry; assumption | f_equal; lia | exfalso; apply Hni; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto] |]).
        destruct Hi.
  Qed.
End GCT.
End FPGen1b.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPGen1c.
Context {fx : FPState}.

Definition stt_words : list (option (bv 32)) :=
  [Some W_78578; Some W_7857c; Some W_78580; None; None; None; None; None; None; None; None; None; None; None; None; None;
   Some W_785b8; Some W_785bc; Some W_785c0; Some W_785c4; Some W_785c8; Some W_785cc]%list.
Definition stb_words : list (option (bv 32)) :=
  [Some W_785d0; Some W_785d4; Some W_785d8; None; None; None; None; None; None; None; None; None; None; None; None; None;
   Some W_78610; Some W_78614; Some W_78618; Some W_7861c; Some W_78620; Some W_78624]%list.
Definition ain_words : list (option (bv 32)) := [None; None; Some W_74cac; Some W_74cb0; Some W_74cb4; Some W_74cb8]%list.

Lemma v_and_m1_l : forall x : word, v_and (Z_to_bv 64 (-1)) x = x.
Proof using.
  intros x. (lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end). change (bv_unsigned (Z_to_bv 64 (-1))) with (Z.ones 64).
  pose proof (u64_range x). rewrite Z.land_comm, Z.land_ones_low.
  - apply Z_to_bv_bv_unsigned.
  - lia.
  - destruct (Z.eq_dec (bv_unsigned x) 0) as [E|NE]; [rewrite E; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. apply Z.log2_lt_pow2; lia.
Qed.

Section STK.
  Variable segs : list Segment.
  Variable rb : word.
  Hypothesis HT : code_ato segs rb 0x78580 stt_words.
  Hypothesis HB : code_ato segs rb 0x785d8 stb_words.

  Lemma So0 : fetch_word segs (at_ rb 0x78580) = Some W_78578.  Proof using HT. exact (code_ato_get segs rb 0x78580 stt_words 0 _ HT eq_refl). Qed.
  Lemma So4 : fetch_word segs (at_ rb 0x78584) = Some W_7857c.  Proof using HT. exact (code_ato_get segs rb 0x78580 stt_words 1 _ HT eq_refl). Qed.
  Lemma So8 : fetch_word segs (at_ rb 0x78588) = Some W_78580.  Proof using HT. exact (code_ato_get segs rb 0x78580 stt_words 2 _ HT eq_refl). Qed.
  Lemma So64 : fetch_word segs (at_ rb 0x785c0) = Some W_785b8.  Proof using HT. exact (code_ato_get segs rb 0x78580 stt_words 16 _ HT eq_refl). Qed.
  Lemma So68 : fetch_word segs (at_ rb 0x785c4) = Some W_785bc.  Proof using HT. exact (code_ato_get segs rb 0x78580 stt_words 17 _ HT eq_refl). Qed.
  Lemma So72 : fetch_word segs (at_ rb 0x785c8) = Some W_785c0.  Proof using HT. exact (code_ato_get segs rb 0x78580 stt_words 18 _ HT eq_refl). Qed.
  Lemma So76 : fetch_word segs (at_ rb 0x785cc) = Some W_785c4.  Proof using HT. exact (code_ato_get segs rb 0x78580 stt_words 19 _ HT eq_refl). Qed.
  Lemma So80 : fetch_word segs (at_ rb 0x785d0) = Some W_785c8.  Proof using HT. exact (code_ato_get segs rb 0x78580 stt_words 20 _ HT eq_refl). Qed.
  Lemma So84 : fetch_word segs (at_ rb 0x785d4) = Some W_785cc.  Proof using HT. exact (code_ato_get segs rb 0x78580 stt_words 21 _ HT eq_refl). Qed.
  Lemma Bo0 : fetch_word segs (at_ rb 0x785d8) = Some W_785d0.  Proof using HB. exact (code_ato_get segs rb 0x785d8 stb_words 0 _ HB eq_refl). Qed.
  Lemma Bo4 : fetch_word segs (at_ rb 0x785dc) = Some W_785d4.  Proof using HB. exact (code_ato_get segs rb 0x785d8 stb_words 1 _ HB eq_refl). Qed.
  Lemma Bo8 : fetch_word segs (at_ rb 0x785e0) = Some W_785d8.  Proof using HB. exact (code_ato_get segs rb 0x785d8 stb_words 2 _ HB eq_refl). Qed.
  Lemma Bo64 : fetch_word segs (at_ rb 0x78618) = Some W_78610.  Proof using HB. exact (code_ato_get segs rb 0x785d8 stb_words 16 _ HB eq_refl). Qed.
  Lemma Bo68 : fetch_word segs (at_ rb 0x7861c) = Some W_78614.  Proof using HB. exact (code_ato_get segs rb 0x785d8 stb_words 17 _ HB eq_refl). Qed.
  Lemma Bo72 : fetch_word segs (at_ rb 0x78620) = Some W_78618.  Proof using HB. exact (code_ato_get segs rb 0x785d8 stb_words 18 _ HB eq_refl). Qed.
  Lemma Bo76 : fetch_word segs (at_ rb 0x78624) = Some W_7861c.  Proof using HB. exact (code_ato_get segs rb 0x785d8 stb_words 19 _ HB eq_refl). Qed.
  Lemma Bo80 : fetch_word segs (at_ rb 0x78628) = Some W_78620.  Proof using HB. exact (code_ato_get segs rb 0x785d8 stb_words 20 _ HB eq_refl). Qed.
  Lemma Bo84 : fetch_word segs (at_ rb 0x7862c) = Some W_78624.  Proof using HB. exact (code_ato_get segs rb 0x785d8 stb_words 21 _ HB eq_refl). Qed.

  (* [comment removed for export] *)
  Record stkH (mem : word -> option byte) (thr top bot : word) : Prop := STKH {
    sh_sw : rdn segs mem (at_ thr 40) 1 = Some [Z_to_bv 8 0];
    sh_top : rdn segs mem (at_ thr 8) 8 = Some (LE8 top);
    sh_bot : rdn segs mem (at_ thr 16) 8 = Some (LE8 bot);
    sh_lt : (U bot < U top)%Z;
    sh_rng : (U thr + 48 <= 2 ^ 64)%Z }.

  Ltac cld8 F D vv Hr :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
        [exact F | reflexivity | exact D | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi; zlit_at; Hr | apply bytes_le_to_Z_8]
      | step_simpl]; vn.

  Theorem stt_run : forall mem rom regs (ra thr top bot : word),
    stkH mem thr top bot -> ret_ok ra -> getr regs 1 = ra -> getr regs 10 = thr ->
    exists r, msteps segs (mkst regs (at_ rb 0x78580) mem rom) (mkst r ra mem rom)
      /\ getr r 10 = top /\ getr r 11 = top /\ regs_agree (fun x => In x [10; 11]) regs r.
  Proof using HT.
    intros mem rom regs ra thr top bot [Rsw Rt Rb LT RG] Hret H1 H10. pose proof (u64_range thr). pose proof (u64_range top). pose proof (u64_range bot).
    wd_eexists. split; [|split; [|split]].
    - chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0); [exact So0 | reflexivity | exact D_78578 | gres; rwH; imm_norm; exact Rsw]
        | step_simpl]; vn.                                (* [comment removed for export] *)
      afence So4 D_7857c.                                 (* [comment removed for export] *)
      ab_tk So8 D_78580 ltac:(condz).                    (* [comment removed for export] *)
      cld8 So64 D_785b8 top ltac:(exact Rt).              (* [comment removed for export] *)
      cld8 So68 D_785bc bot ltac:(exact Rb).              (* [comment removed for export] *)
      an So72 D_785c0.                                    (* [comment removed for export] *)
      an So76 D_785c4.                                    (* [comment removed for export] *)
      an So80 D_785c8.                                    (* [comment removed for export] *)
      aret So84 D_785cc ra.
      wd_refl.
    - gres. (lazymatch goal with |- ?G => let G' := eval unfold v_sltu in G in change_no_check G' end). replace (c_ltu bot top) with true by (symmetry; (lazymatch goal with |- ?G => let G' := eval unfold c_ltu, bv_ltu in G in change_no_check G' end); apply Z.ltb_lt; exact LT).
      change (v_sub (Z_to_bv 64 0) (Z_to_bv 64 1)) with (Z_to_bv 64 (-1)). apply v_and_m1_l.
    - gres; reflexivity.
    - ra_solve.
  Qed.

  Theorem stb_run : forall mem rom regs (ra thr top bot : word),
    stkH mem thr top bot -> ret_ok ra -> getr regs 1 = ra -> getr regs 10 = thr ->
    exists r, msteps segs (mkst regs (at_ rb 0x785d8) mem rom) (mkst r ra mem rom)
      /\ getr r 10 = bot /\ getr r 11 = Z_to_bv 64 (-1) /\ regs_agree (fun x => In x [10; 11]) regs r.
  Proof using HB.
    intros mem rom regs ra thr top bot [Rsw Rt Rb LT RG] Hret H1 H10. pose proof (u64_range thr). pose proof (u64_range top). pose proof (u64_range bot).
    wd_eexists. split; [|split; [|split]].
    - chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0); [exact Bo0 | reflexivity | exact D_785d0 | gres; rwH; imm_norm; exact Rsw]
        | step_simpl]; vn.                                (* [comment removed for export] *)
      afence Bo4 D_785d4.
      ab_tk Bo8 D_785d8 ltac:(condz).                    (* [comment removed for export] *)
      cld8 Bo64 D_78610 top ltac:(exact Rt).              (* [comment removed for export] *)
      cld8 Bo68 D_78614 bot ltac:(exact Rb).              (* [comment removed for export] *)
      an Bo72 D_78618.                                    (* [comment removed for export] *)
      an Bo76 D_7861c.                                    (* [comment removed for export] *)
      an Bo80 D_78620.                                    (* [comment removed for export] *)
      aret Bo84 D_78624 ra.
      wd_refl.
    - gres. (lazymatch goal with |- ?G => let G' := eval unfold v_sltu in G in change_no_check G' end). replace (c_ltu bot top) with true by (symmetry; (lazymatch goal with |- ?G => let G' := eval unfold c_ltu, bv_ltu in G in change_no_check G' end); apply Z.ltb_lt; exact LT).
      change (v_sub (Z_to_bv 64 0) (Z_to_bv 64 1)) with (Z_to_bv 64 (-1)). apply v_and_m1_l.
    - gres. (lazymatch goal with |- ?G => let G' := eval unfold v_sltu in G in change_no_check G' end). replace (c_ltu bot top) with true by (symmetry; (lazymatch goal with |- ?G => let G' := eval unfold c_ltu, bv_ltu in G in change_no_check G' end); apply Z.ltb_lt; exact LT). reflexivity.
    - ra_solve.
  Qed.
End STK.

Lemma stkH_keep : forall segs (mem M' : word -> option byte) (thr top bot : word),
  stkH segs mem thr top bot -> (forall x : word, (U thr <= U x < U thr + 48)%Z -> M' x = mem x) -> stkH segs M' thr top bot.
Proof using.
  intros segs mem M' thr top bot [Rsw Rt Rb LT RG] HM. pose proof (u64_range thr).
  split; try assumption.
  - rewrite <- Rsw. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply HM; rewrite at_u in Hx by lia; cbn in Hx; lia].
  - rewrite <- Rt. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply HM; rewrite at_u in Hx by lia; cbn in Hx; lia].
  - rewrite <- Rb. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply HM; rewrite at_u in Hx by lia; cbn in Hx; lia].
Qed.

Section AIN.
  Variable segs : list Segment.
  Variable rb : word.
  Variable g_inited : Z.
  Hypothesis HA : code_ato segs rb 0x74cac ain_words.
  Hypothesis GA : gloadb segs rb 0x74cac 10 g_inited.
  Lemma Ao8 : fetch_word segs (at_ rb 0x74cb4) = Some W_74cac.  Proof using HA. exact (code_ato_get segs rb 0x74cac ain_words 2 _ HA eq_refl). Qed.
  Lemma Ao12 : fetch_word segs (at_ rb 0x74cb8) = Some W_74cb0.  Proof using HA. exact (code_ato_get segs rb 0x74cac ain_words 3 _ HA eq_refl). Qed.
  Lemma Ao16 : fetch_word segs (at_ rb 0x74cbc) = Some W_74cb4.  Proof using HA. exact (code_ato_get segs rb 0x74cac ain_words 4 _ HA eq_refl). Qed.
  Lemma Ao20 : fetch_word segs (at_ rb 0x74cc0) = Some W_74cb8.  Proof using HA. exact (code_ato_get segs rb 0x74cac ain_words 5 _ HA eq_refl). Qed.

  (* [comment removed for export] *)
  Theorem ain_run : forall mem rom regs (ra : word),
    rdn segs mem (Z_to_bv 64 g_inited) 1 = Some [Z_to_bv 8 1] ->
    ret_ok ra -> getr regs 1 = ra ->
    exists r, msteps segs (mkst regs (at_ rb 0x74cac) mem rom) (mkst r ra mem rom)
      /\ getr r 10 = Z_to_bv 64 1 /\ regs_agree (fun x => In x [10]) regs r.
  Proof using GA HA.
    intros mem rom regs ra Rin Hret H1.
    wd_eexists. split; [|split].
    - eapply msteps_trans; [eapply GA; exact Rin|]. zlit_at.
      afence Ao8 D_74cac.
      an Ao12 D_74cb0.                                    (* [comment removed for export] *)
      an Ao16 D_74cb4.                                    (* [comment removed for export] *)
      aret Ao20 D_74cb8 ra.
      wd_refl.
    - gres. reflexivity.
    - ra_solve.
  Qed.
End AIN.
End FPGen1c.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPGen1d.
Context {fx : FPState}.

Definition ui_words : list (option (bv 32)) :=
  [Some W_7694c; Some W_76950; Some W_76954; Some W_76958; Some W_7695c; Some W_76960; Some W_76964; Some W_76968;
   Some W_7696c; Some W_76970; Some W_76974; Some W_76978; Some W_7697c; Some W_76980; Some W_76984; Some W_76988;
   Some W_7698c; Some W_76990; Some W_76994; Some W_76998; Some W_7699c; Some W_769a0; Some W_769a4; Some W_769a8;
   Some W_769ac; Some W_769b0; Some W_769b4; Some W_769b8; Some W_769bc; Some W_769c0; Some W_769c4; Some W_769c8;
   Some W_769cc; Some W_769d0; Some W_769d4; Some W_769d8; Some W_769dc; Some W_769e0; Some W_769e4; Some W_769e8;
   Some W_769ec; Some W_769f0; Some W_769f4; Some W_769f8; Some W_769fc; Some W_76a00; Some W_76a04; Some W_76a08;
   Some W_76a0c; Some W_76a10; Some W_76a14; Some W_76a18; Some W_76a1c; Some W_76a20; Some W_76a24; Some W_76a28;
   Some W_76a2c; Some W_76a30; Some W_76a34; Some W_76a38; Some W_76a3c; Some W_76a40; Some W_76a44; Some W_76a48;
   Some W_76a4c; Some W_76a50; Some W_76a54; Some W_76a58; Some W_76a5c; Some W_76a60; Some W_76a64; Some W_76a68;
   Some W_76a6c; Some W_76a70; Some W_76a74; Some W_76a78; Some W_76a7c; Some W_76a80; Some W_76a84; Some W_76a88;
   Some W_76a8c; Some W_76a90; Some W_76a94; Some W_76a98]%list.
Definition uw_words : list (option (bv 32)) :=
  [Some W_8fa60; Some W_8fa64; Some W_8fa68; Some W_8fa6c; Some W_8fa70; Some W_8fa74; Some W_8fa78;
   Some W_8fa7c; Some W_8fa80; Some W_8fa84; Some W_8fa88; Some W_8fa8c; Some W_8fa90; Some W_8fa94;
   Some W_8fa98; Some W_8fa9c; Some W_8faa0; Some W_8faa4; Some W_8faa8; Some W_8faac; Some W_8fab0;
   Some W_8fab4; Some W_8fab8; Some W_8fabc; Some W_8fac0; Some W_8fac4; Some W_8fac8; Some W_8facc;
   Some W_8fad0; Some W_8fad4; Some W_8fad8; Some W_8fadc; Some W_8fae0; Some W_8fae4; Some W_8fae8;
   Some W_8faec; Some W_8faf0; Some W_8faf4; Some W_8faf8; Some W_8fafc; Some W_8fb00; Some W_8fb04;
   Some W_8fb08; Some W_8fb0c; Some W_8fb10; Some W_8fb14; Some W_8fb18; Some W_8fb1c; Some W_8fb20;
   Some W_8fb24; Some W_8fb28; Some W_8fb2c; Some W_8fb30; Some W_8fb34; Some W_8fb38; Some W_8fb3c;
   Some W_8fb40; Some W_8fb44; Some W_8fb48; Some W_8fb4c; Some W_8fb50; Some W_8fb54; Some W_8fb58;
   Some W_8fb5c; Some W_8fb60; Some W_8fb64; Some W_8fb68; Some W_8fb6c; Some W_8fb70; Some W_8fb74]%list.

(* [comment removed for export] *)
Definition ui_clob : list reg := [5; 6; 10; 11; 12; 13; 14; 15; 16; 17].
Definition ui_clobx : list reg := [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 5; 6; 10; 11; 12; 13; 14; 15; 16; 17].

(* [comment removed for export] *)
Record ui_tab := UIT { ut_rb : word; ut_gct : gct_tab; ut_g_inited : Z; ut_g_pgsz : Z;
                        ut_img_lo : Z; ut_img_hi : Z   (* [comment removed for export] *) }.
Record ui_tab_ok (segs : list Segment) (t : ui_tab) : Prop := UITOK {
  uto_ui : code_ato segs (ut_rb t) 0x76954 ui_words;
  uto_uw : code_ato segs (ut_rb t) 0x8fa68 uw_words;
  uto_uf : code_ato segs (at_ (ut_rb t) 0x8f40c) 0 uf_words;
  uto_uf56 : gload2 segs (at_ (ut_rb t) 0x8f40c) 56 13 18 (ut_g_pgsz t);
  uto_gct : gct_tab_ok segs (ut_gct t);
  uto_gct_rb : gt_rb (ut_gct t) = ut_rb t;
  uto_stt : code_ato segs (ut_rb t) 0x78580 stt_words;
  uto_stb : code_ato segs (ut_rb t) 0x785d8 stb_words;
  uto_ain : code_ato segs (ut_rb t) 0x74cac ain_words;
  uto_ainb : gloadb segs (ut_rb t) 0x74cac 10 (ut_g_inited t);
  uto_rb : (U (ut_rb t) mod 2 = 0)%Z /\ (U (ut_rb t) + 2 ^ 24 < 2 ^ 64)%Z }.

(* [comment removed for export] *)
Record uiH (segs : list Segment) (t : ui_tab) (mem : word -> option byte) (sp this bp thr P : word) : Prop := UIH {
  uh_inited : rdn segs mem (Z_to_bv 64 (ut_g_inited t)) 1 = Some [Z_to_bv 8 1];
  uh_unw : rdn segs mem (at_ thr 3168) 1 = Some [Z_to_bv 8 0];
  uh_unw_ok : store_ok segs mem (at_ thr 3168) 1 = true;
  uh_pg : rdn segs mem (Z_to_bv 64 (ut_g_pgsz t)) 8 = Some (LE8 P);
  uh_P : rdn segs mem P 8 = Some (LE8 (Z_to_bv 64 4096));
  uh_stk : store_ok segs mem (at_ sp (-144)) 144 = true;
  uh_obj : store_ok segs mem (at_ this 8) 2056 = true;
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  uh_g0 : ((ut_img_lo t <= ut_g_inited t /\ ut_g_inited t + 1 <= ut_img_hi t)
           /\ (ut_img_lo t <= ut_g_pgsz t /\ ut_g_pgsz t + 8 <= ut_img_hi t)
           /\ (ut_img_lo t <= U P /\ U P + 8 <= ut_img_hi t)
           /\ (0 <= ut_img_lo t /\ ut_img_hi t <= 4294967296))%Z;
  uh_g1 : (2 ^ 32 + 144 <= U sp)%Z /\ (U sp <= U this)%Z /\ (U this + 2064 <= U bp - 16)%Z /\ (U bp + 16 <= 2 ^ 47)%Z /\ (U bp mod 16 = 0)%Z;
  uh_g2 : ((U thr + 4096 <= ut_img_lo t \/ ut_img_hi t <= U thr) /\ 4096 <= U thr /\ U thr + 4096 <= U sp - 144)%Z }.

Section UI.
  Variable segs : list Segment.
  Variable t : ui_tab.
  Hypothesis TOK : ui_tab_ok segs t.
  #[local] Abbreviation rb := (ut_rb t).
  Let HUI : code_ato segs rb 0x76954 ui_words := uto_ui _ _ TOK.
  Let HUW : code_ato segs rb 0x8fa68 uw_words := uto_uw _ _ TOK.

  Lemma If0ff8 : fetch_word segs (at_ rb 0x76954) = Some W_7694c.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 0 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If0ffc : fetch_word segs (at_ rb 0x76958) = Some W_76950.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 1 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1000 : fetch_word segs (at_ rb 0x7695c) = Some W_76954.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 2 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1004 : fetch_word segs (at_ rb 0x76960) = Some W_76958.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 3 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1008 : fetch_word segs (at_ rb 0x76964) = Some W_7695c.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 4 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If100c : fetch_word segs (at_ rb 0x76968) = Some W_76960.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 5 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1010 : fetch_word segs (at_ rb 0x7696c) = Some W_76964.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 6 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1014 : fetch_word segs (at_ rb 0x76970) = Some W_76968.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 7 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1018 : fetch_word segs (at_ rb 0x76974) = Some W_7696c.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 8 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If101c : fetch_word segs (at_ rb 0x76978) = Some W_76970.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 9 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1020 : fetch_word segs (at_ rb 0x7697c) = Some W_76974.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 10 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1024 : fetch_word segs (at_ rb 0x76980) = Some W_76978.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 11 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1028 : fetch_word segs (at_ rb 0x76984) = Some W_7697c.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 12 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If102c : fetch_word segs (at_ rb 0x76988) = Some W_76980.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 13 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1030 : fetch_word segs (at_ rb 0x7698c) = Some W_76984.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 14 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1034 : fetch_word segs (at_ rb 0x76990) = Some W_76988.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 15 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1038 : fetch_word segs (at_ rb 0x76994) = Some W_7698c.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 16 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If103c : fetch_word segs (at_ rb 0x76998) = Some W_76990.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 17 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1040 : fetch_word segs (at_ rb 0x7699c) = Some W_76994.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 18 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1044 : fetch_word segs (at_ rb 0x769a0) = Some W_76998.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 19 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1048 : fetch_word segs (at_ rb 0x769a4) = Some W_7699c.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 20 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If104c : fetch_word segs (at_ rb 0x769a8) = Some W_769a0.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 21 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1050 : fetch_word segs (at_ rb 0x769ac) = Some W_769a4.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 22 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1054 : fetch_word segs (at_ rb 0x769b0) = Some W_769a8.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 23 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1058 : fetch_word segs (at_ rb 0x769b4) = Some W_769ac.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 24 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If105c : fetch_word segs (at_ rb 0x769b8) = Some W_769b0.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 25 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1060 : fetch_word segs (at_ rb 0x769bc) = Some W_769b4.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 26 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1064 : fetch_word segs (at_ rb 0x769c0) = Some W_769b8.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 27 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1068 : fetch_word segs (at_ rb 0x769c4) = Some W_769bc.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 28 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If106c : fetch_word segs (at_ rb 0x769c8) = Some W_769c0.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 29 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1070 : fetch_word segs (at_ rb 0x769cc) = Some W_769c4.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 30 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1074 : fetch_word segs (at_ rb 0x769d0) = Some W_769c8.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 31 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1078 : fetch_word segs (at_ rb 0x769d4) = Some W_769cc.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 32 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If107c : fetch_word segs (at_ rb 0x769d8) = Some W_769d0.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 33 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1080 : fetch_word segs (at_ rb 0x769dc) = Some W_769d4.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 34 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1084 : fetch_word segs (at_ rb 0x769e0) = Some W_769d8.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 35 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1088 : fetch_word segs (at_ rb 0x769e4) = Some W_769dc.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 36 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If108c : fetch_word segs (at_ rb 0x769e8) = Some W_769e0.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 37 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1090 : fetch_word segs (at_ rb 0x769ec) = Some W_769e4.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 38 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1094 : fetch_word segs (at_ rb 0x769f0) = Some W_769e8.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 39 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1098 : fetch_word segs (at_ rb 0x769f4) = Some W_769ec.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 40 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If109c : fetch_word segs (at_ rb 0x769f8) = Some W_769f0.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 41 _ HUI eq_refl). Qed.



























   (* [comment removed for export] *)
  Lemma If1110 : fetch_word segs (at_ rb 0x76a6c) = Some W_76a64.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 70 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1114 : fetch_word segs (at_ rb 0x76a70) = Some W_76a68.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 71 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1118 : fetch_word segs (at_ rb 0x76a74) = Some W_76a6c.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 72 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If111c : fetch_word segs (at_ rb 0x76a78) = Some W_76a70.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 73 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1120 : fetch_word segs (at_ rb 0x76a7c) = Some W_76a74.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 74 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1124 : fetch_word segs (at_ rb 0x76a80) = Some W_76a78.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 75 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1128 : fetch_word segs (at_ rb 0x76a84) = Some W_76a7c.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 76 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If112c : fetch_word segs (at_ rb 0x76a88) = Some W_76a80.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 77 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1130 : fetch_word segs (at_ rb 0x76a8c) = Some W_76a84.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 78 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1134 : fetch_word segs (at_ rb 0x76a90) = Some W_76a88.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 79 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1138 : fetch_word segs (at_ rb 0x76a94) = Some W_76a8c.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 80 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If113c : fetch_word segs (at_ rb 0x76a98) = Some W_76a90.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 81 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1140 : fetch_word segs (at_ rb 0x76a9c) = Some W_76a94.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 82 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1144 : fetch_word segs (at_ rb 0x76aa0) = Some W_76a98.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x76954 ui_words 83 _ HUI eq_refl). Qed.   (* [comment removed for export] *)

  Lemma I10d804 : fetch_word segs (at_ rb 0x8fa68) = Some W_8fa60.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x8fa68 uw_words 0 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I10d808 : fetch_word segs (at_ rb 0x8fa6c) = Some W_8fa64.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x8fa68 uw_words 1 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I10d80c : fetch_word segs (at_ rb 0x8fa70) = Some W_8fa68.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x8fa68 uw_words 2 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I10d810 : fetch_word segs (at_ rb 0x8fa74) = Some W_8fa6c.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x8fa68 uw_words 3 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I10d814 : fetch_word segs (at_ rb 0x8fa78) = Some W_8fa70.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x8fa68 uw_words 4 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I10d818 : fetch_word segs (at_ rb 0x8fa7c) = Some W_8fa74.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x8fa68 uw_words 5 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I10d81c : fetch_word segs (at_ rb 0x8fa80) = Some W_8fa78.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x8fa68 uw_words 6 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I10d820 : fetch_word segs (at_ rb 0x8fa84) = Some W_8fa7c.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x8fa68 uw_words 7 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I10d824 : fetch_word segs (at_ rb 0x8fa88) = Some W_8fa80.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x8fa68 uw_words 8 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I10d828 : fetch_word segs (at_ rb 0x8fa8c) = Some W_8fa84.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x8fa68 uw_words 9 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I10d82c : fetch_word segs (at_ rb 0x8fa90) = Some W_8fa88.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x8fa68 uw_words 10 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I10d830 : fetch_word segs (at_ rb 0x8fa94) = Some W_8fa8c.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x8fa68 uw_words 11 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I10d834 : fetch_word segs (at_ rb 0x8fa98) = Some W_8fa90.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x8fa68 uw_words 12 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I10d838 : fetch_word segs (at_ rb 0x8fa9c) = Some W_8fa94.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x8fa68 uw_words 13 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I10d83c : fetch_word segs (at_ rb 0x8faa0) = Some W_8fa98.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x8fa68 uw_words 14 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I10d840 : fetch_word segs (at_ rb 0x8faa4) = Some W_8fa9c.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x8fa68 uw_words 15 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I10d844 : fetch_word segs (at_ rb 0x8faa8) = Some W_8faa0.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x8fa68 uw_words 16 _ HUW eq_refl). Qed.












   (* [comment removed for export] *)
  Lemma I10d87c : fetch_word segs (at_ rb 0x8fae0) = Some W_8fad8.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x8fa68 uw_words 30 _ HUW eq_refl). Qed.
























   (* [comment removed for export] *)
  Lemma I10d8e4 : fetch_word segs (at_ rb 0x8fb48) = Some W_8fb40.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x8fa68 uw_words 56 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I10d8e8 : fetch_word segs (at_ rb 0x8fb4c) = Some W_8fb44.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x8fa68 uw_words 57 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I10d8ec : fetch_word segs (at_ rb 0x8fb50) = Some W_8fb48.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x8fa68 uw_words 58 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I10d8f0 : fetch_word segs (at_ rb 0x8fb54) = Some W_8fb4c.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x8fa68 uw_words 59 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I10d8f4 : fetch_word segs (at_ rb 0x8fb58) = Some W_8fb50.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x8fa68 uw_words 60 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I10d8f8 : fetch_word segs (at_ rb 0x8fb5c) = Some W_8fb54.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x8fa68 uw_words 61 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I10d8fc : fetch_word segs (at_ rb 0x8fb60) = Some W_8fb58.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x8fa68 uw_words 62 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I10d900 : fetch_word segs (at_ rb 0x8fb64) = Some W_8fb5c.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x8fa68 uw_words 63 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I10d904 : fetch_word segs (at_ rb 0x8fb68) = Some W_8fb60.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x8fa68 uw_words 64 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I10d908 : fetch_word segs (at_ rb 0x8fb6c) = Some W_8fb64.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x8fa68 uw_words 65 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I10d90c : fetch_word segs (at_ rb 0x8fb70) = Some W_8fb68.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x8fa68 uw_words 66 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I10d910 : fetch_word segs (at_ rb 0x8fb74) = Some W_8fb6c.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x8fa68 uw_words 67 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I10d914 : fetch_word segs (at_ rb 0x8fb78) = Some W_8fb70.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x8fa68 uw_words 68 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I10d918 : fetch_word segs (at_ rb 0x8fb7c) = Some W_8fb74.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x8fa68 uw_words 69 _ HUW eq_refl). Qed.   (* [comment removed for export] *)


  Variables (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ra sp tp this pc0 bp fast thr top bot tsdp tctx P : word).
  Hypothesis Hret : ret_ok ra.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H4 : getr regs 4 = tp.
  Hypothesis H10 : getr regs 10 = this.
  Hypothesis H11 : getr regs 11 = pc0.
  Hypothesis H12 : getr regs 12 = bp.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 0.
  Hypothesis H14 : getr regs 14 = fast.
  Hypothesis H15 : getr regs 15 = Z_to_bv 64 30.
  Hypothesis Hfast : U fast <> 0%Z.
  Hypothesis UH : uiH segs t mem sp this bp thr P.
  Hypothesis GH : gctH segs (ut_gct t) mem (at_ sp (-80)) tp tsdp tctx thr.
  Hypothesis SH : stkH segs mem thr top bot.
  Hypothesis Gtop : (4096 <= U top <= 2 ^ 47)%Z.

  #[local] Abbreviation CL := (fun r => In r ui_clob).
  #[local] Abbreviation CLX := (fun r => In r ui_clobx).

  (* [comment removed for export] *)
  Definition ui_m1 : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
      (at_ sp (-8)) (LE8 ra)) (at_ sp (-16)) (LE8 (getr regs 8))) (at_ sp (-24)) (LE8 (getr regs 9)))
      (at_ sp (-32)) (LE8 (getr regs 18))) (at_ sp (-40)) (LE8 (getr regs 19))) (at_ sp (-48)) (LE8 (getr regs 20)))
      (at_ sp (-56)) (LE8 (getr regs 21))) (at_ sp (-64)) (LE8 (getr regs 22))) (at_ sp (-72)) (LE8 (getr regs 23)))
      (at_ sp (-80)) (LE8 (getr regs 24))) (at_ this 8) (LE4 0).

  Lemma ui_m1_outside : forall x : word,
    (U x < U sp - 80)%Z \/ (U sp <= U x < U this + 8)%Z \/ (U this + 12 <= U x)%Z -> ui_m1 x = mem x.
  Proof using UH P thr bp t segs.
    intros x Hx. destruct UH as [_ _ _ _ _ _ _ G0 G1 G2]. pose proof (u64_range sp). pose proof (u64_range this). (lazymatch goal with |- ?G => let G' := eval unfold ui_m1 in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia. reflexivity.
  Qed.
  Lemma ui_m1_slots : forall (k : Z) (v : word),
    In (k, v) [(-8, ra); (-16, getr regs 8); (-24, getr regs 9); (-32, getr regs 18); (-40, getr regs 19);
               (-48, getr regs 20); (-56, getr regs 21); (-64, getr regs 22); (-72, getr regs 23); (-80, getr regs 24)]%Z ->
    rdn segs ui_m1 (at_ sp k) 8 = Some (LE8 v).
  Proof using UH P thr bp t.
    intros k v Hin. destruct UH as [_ _ _ _ _ _ _ G0 G1 G2]. pose proof (u64_range sp). pose proof (u64_range this). (lazymatch goal with |- ?G => let G' := eval unfold ui_m1 in G in change_no_check G' end).
    cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin.
  Qed.

  Ltac sokS Hs lo N :=
    repeat (eapply store_ok_mono; [apply wbytes_grows|]);
    eapply (store_ok_sub segs mem lo _ N); [rewrite at_u; lia | exact Hs | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia].
  Ltac fsd8 F D aa Hs lo N :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := aa);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | sokS Hs lo N ]
      | step_simpl]; vn.

  (* [comment removed for export] *)
  Lemma uiA :
    exists r,
      msteps segs (mkst regs (at_ rb 0x76954) mem rom) (mkst r (at_ rb 0x74cac) ui_m1 rom)
      /\ getr r 1 = at_ rb 0x769a0 /\ getr r 2 = at_ sp (-80) /\ getr r 4 = tp
      /\ getr r 9 = Z_to_bv 64 30 /\ getr r 21 = fast /\ getr r 20 = Z_to_bv 64 0 /\ getr r 8 = bp /\ getr r 18 = pc0 /\ getr r 19 = this
      /\ regs_agree CLX regs r.
  Proof using UH H15 H14 H13 H12 H11 H10 H4 H2 H1 P thr HUI TOK.
    destruct UH as [_ _ _ _ _ Hstk Hobj G0 G1 G2]. pose proof (u64_range sp) as Hspr. pose proof (u64_range this) as Hth.
    wd_eexists. split.
    - an If0ff8 D_7694c.                                   (* [comment removed for export] *)
      fsd8 If0ffc D_76950 (at_ sp (-8)) Hstk (at_ sp (-144)) 144%nat.
      fsd8 If1000 D_76954 (at_ sp (-16)) Hstk (at_ sp (-144)) 144%nat.
      fsd8 If1004 D_76958 (at_ sp (-24)) Hstk (at_ sp (-144)) 144%nat.
      fsd8 If1008 D_7695c (at_ sp (-32)) Hstk (at_ sp (-144)) 144%nat.
      fsd8 If100c D_76960 (at_ sp (-40)) Hstk (at_ sp (-144)) 144%nat.
      fsd8 If1010 D_76964 (at_ sp (-48)) Hstk (at_ sp (-144)) 144%nat.
      fsd8 If1014 D_76968 (at_ sp (-56)) Hstk (at_ sp (-144)) 144%nat.
      fsd8 If1018 D_7696c (at_ sp (-64)) Hstk (at_ sp (-144)) 144%nat.
      fsd8 If101c D_76970 (at_ sp (-72)) Hstk (at_ sp (-144)) 144%nat.
      fsd8 If1020 D_76974 (at_ sp (-80)) Hstk (at_ sp (-144)) 144%nat.
      an If1024 D_76978. an If1028 D_7697c. an If102c D_76980. an If1030 D_76984. an If1034 D_76988. an If1038 D_7698c.   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sw_at with (a := at_ this 8);
          [exact If103c | reflexivity | exact D_76990
          | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
          | gres; rwH; reflexivity
          | sokS Hobj (at_ this 8) 2056%nat ]
        | step_simpl]; vn.                                  (* [comment removed for export] *)
      change (wbytes _ _ _) with ui_m1.
      an If1040 D_76994.                                    (* [comment removed for export] *)
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold ui_clobx in G in change_no_check G' end). ra_solve.
  Qed.

  Ltac cldg F D bs0 vv Hr :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := bs0) (v := vv);
        [exact F | reflexivity | exact D | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi; zlit_at; Hr | first [apply bytes_le_to_Z_8 | unorm; reflexivity] ]
      | step_simpl]; vn.

  (* [comment removed for export] *)
  Lemma uiB : forall (M : word -> option byte) r0,
    getr r0 10 = Z_to_bv 64 1 -> regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ rb 0x769a0) M rom) (mkst r (at_ rb 0x783bc) M rom)
      /\ getr r 1 = at_ rb 0x769a8
      /\ (forall i : reg, In i [2; 4; 8; 9; 18; 19; 20; 21] -> getr r i = getr r0 i)
      /\ regs_agree CLX regs r.
  Proof using HUI TOK.
    intros M r0 R10 AG0.
    wd_eexists. split.
    - ab_ft If1044 D_76998 ltac:(condz).                  (* [comment removed for export] *)
      an If1048 D_7699c.                                   (* [comment removed for export] *)
      wd_refl.
    - post. 2: ((lazymatch goal with |- ?G => let G' := eval unfold ui_clobx in G in change_no_check G' end); ra_chain).
      intros i Hi; cbn [In] in Hi; repeat (destruct Hi as [<-|Hi]; [gres; reflexivity|]); destruct Hi.
  Qed.

  (* [comment removed for export] *)
  Lemma uiC : forall (M : word -> option byte) r0,
    getr r0 10 = thr -> rdn segs M (at_ thr 3168) 1 = Some [Z_to_bv 8 0] -> store_ok segs M (at_ thr 3168) 1 = true ->
    regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ rb 0x769a8) M rom) (mkst r (at_ rb 0x78580) (wbytes M (at_ thr 3168) [Z_to_bv 8 1]) rom)
      /\ getr r 1 = at_ rb 0x769c8 /\ getr r 10 = thr /\ getr r 23 = thr /\ getr r 24 = at_ thr 2047
      /\ (forall i : reg, In i [2; 4; 8; 9; 18; 19; 20; 21] -> getr r i = getr r0 i)
      /\ regs_agree CLX regs r.
  Proof using UH P bp this sp mem HUI TOK.
    intros M r0 R10 Ru SOK AG0. destruct UH as [_ _ _ _ _ _ _ G0 G1 G2]. pose proof (u64_range thr).
    wd_eexists. split.
    - ab_ft If104c D_769a0 ltac:(condz).                  (* [comment removed for export] *)
      an If1050 D_769a4.                                   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lbu with (b := Z_to_bv 8 0); [exact If1054 | reflexivity | exact D_769a8 | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; exact Ru]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      an If1058 D_769ac.                                   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sb_at with (a := at_ thr 3168) (b := Z_to_bv 8 1);
          [exact If105c | reflexivity | exact D_769b0 | gres; rwH; imm_norm; rewrite ?at_addi; reflexivity | gres; rwH; reflexivity | reflexivity | exact SOK]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      ab_ft If1060 D_769b4 ltac:(condz).                  (* [comment removed for export] *)
      an If1064 D_769b8.                                   (* [comment removed for export] *)
      an If1068 D_769bc.                                   (* [comment removed for export] *)
      wd_refl.
    - post. 2: ((lazymatch goal with |- ?G => let G' := eval unfold ui_clobx in G in change_no_check G' end); ra_chain).
      intros i Hi; cbn [In] in Hi; repeat (destruct Hi as [<-|Hi]; [gres; reflexivity|]); destruct Hi.
  Qed.

  (* [comment removed for export] *)
  Lemma uiD : forall (M : word -> option byte) r0,
    getr r0 10 = top -> getr r0 23 = thr -> regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ rb 0x769c8) M rom) (mkst r (at_ rb 0x785d8) M rom)
      /\ getr r 1 = at_ rb 0x769d4 /\ getr r 10 = thr /\ getr r 22 = top
      /\ (forall i : reg, In i [2; 4; 8; 9; 18; 19; 20; 21; 23; 24] -> getr r i = getr r0 i)
      /\ regs_agree CLX regs r.
  Proof using HUI TOK.
    intros M r0 R10 R23 AG0.
    wd_eexists. split.
    - an If106c D_769c0.                                   (* [comment removed for export] *)
      an If1070 D_769c4.                                   (* [comment removed for export] *)
      an If1074 D_769c8.                                   (* [comment removed for export] *)
      wd_refl.
    - post. 2: ((lazymatch goal with |- ?G => let G' := eval unfold ui_clobx in G in change_no_check G' end); ra_chain).
      intros i Hi; cbn [In] in Hi; repeat (destruct Hi as [<-|Hi]; [gres; reflexivity|]); destruct Hi.
  Qed.

  (* [comment removed for export] *)
  Definition uw_mem (M : word -> option byte) (s1v s4v : word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M
      (at_ sp (-88)) (LE8 (at_ rb 0x76a70))) (at_ sp (-96)) (LE8 bp)) (at_ sp (-104)) (LE8 s1v))
      (at_ sp (-112)) (LE8 pc0)) (at_ sp (-120)) (LE8 this)) (at_ sp (-128)) (LE8 s4v))
      (at_ sp (-136)) (LE8 fast)) (at_ this 2056) (LE8 bp).

  Lemma uw_mem_outside : forall M s1v s4v (x : word),
    (U x < U sp - 136)%Z \/ (U sp - 80 <= U x < U this + 2056)%Z \/ (U this + 2064 <= U x)%Z -> uw_mem M s1v s4v x = M x.
  Proof using UH P thr mem segs.
    intros M s1v s4v x Hx. destruct UH as [_ _ _ _ _ _ _ G0 G1 G2]. pose proof (u64_range sp). pose proof (u64_range this). (lazymatch goal with |- ?G => let G' := eval unfold uw_mem in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma uiE : forall (M : word -> option byte) r0,
    mem_grows mem M ->
    getr r0 10 = bot -> getr r0 22 = top -> getr r0 23 = thr -> getr r0 24 = at_ thr 2047 ->
    getr r0 2 = at_ sp (-80) -> getr r0 4 = tp -> getr r0 8 = bp -> getr r0 9 = Z_to_bv 64 30 -> getr r0 18 = pc0 -> getr r0 19 = this ->
    getr r0 20 = Z_to_bv 64 0 -> getr r0 21 = fast ->
    regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ rb 0x769d4) M rom) (mkst r (at_ (at_ rb 0x8f40c) 0) (uw_mem M (Z_to_bv 64 30) (Z_to_bv 64 0)) rom)
      /\ getr r 1 = at_ rb 0x76a70 /\ getr r 2 = at_ sp (-80) /\ getr r 10 = this /\ getr r 11 = pc0 /\ getr r 12 = bp
      /\ getr r 13 = top /\ getr r 14 = bot /\ getr r 15 = Z_to_bv 64 30
      /\ getr r 4 = tp /\ getr r 8 = bp /\ getr r 9 = Z_to_bv 64 30 /\ getr r 18 = pc0 /\ getr r 19 = this
      /\ getr r 20 = Z_to_bv 64 0 /\ getr r 21 = fast /\ getr r 22 = top /\ getr r 23 = thr /\ getr r 24 = at_ thr 2047
      /\ regs_agree CLX regs r.
  Proof using UH Hfast P HUW HUI TOK.
    intros M r0 GR R10 R22 R23 R24 R2 R4 R8 R9 R18 R19 R20 R21 AG0.
    destruct UH as [_ _ _ _ _ Hstk Hobj G0 G1 G2]. pose proof (u64_range sp) as Hspr. pose proof (u64_range this) as Hth. pose proof (u64_range bp) as Hbp.
    Ltac sokG GR Hs lo N :=
      repeat (eapply store_ok_mono; [apply wbytes_grows|]); eapply store_ok_mono; [exact GR|];
      eapply (store_ok_sub segs mem lo _ N); [rewrite at_u; lia | exact Hs | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia].
    Ltac fsdG F D aa GR Hs lo N :=
      chain_step; [reflexivity
        | eapply step_sd_at with (a := aa);
          [exact F | reflexivity | exact D
          | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
          | gres; rwH; reflexivity
          | sokG GR Hs lo N ]
        | step_simpl]; vn.
    assert (RDW : forall (k : Z) (v : word),
      In (k, v) [(-88, at_ rb 0x76a70); (-96, bp); (-104, Z_to_bv 64 30); (-112, pc0); (-120, this); (-128, Z_to_bv 64 0); (-136, fast)]%Z ->
      rdn segs (uw_mem M (Z_to_bv 64 30) (Z_to_bv 64 0)) (at_ sp k) 8 = Some (LE8 v)).
    { intros k v Hin. (lazymatch goal with |- ?G => let G' := eval unfold uw_mem in G in change_no_check G' end).
      assert (Hk : (-136 <= k <= -88)%Z) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E; intros; lia|]); destruct Hin).
      rewrite rdn_wbytes_out; [ | rewrite length_N_to_le_bytes, !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ].
      cbn [In] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin. }
    wd_eexists. split.
    - an If1078 D_769cc.                                   (* [comment removed for export] *)
      ab_ft If107c D_769d0 ltac:(rwH; (lazymatch goal with |- ?G => let G' := eval unfold c_eq, bv_eqb in G in change_no_check G' end); apply Z.eqb_neq; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); exact Hfast || (unorm; exact Hfast)).   (* [comment removed for export] *)
      an If1080 D_769d4. an If1084 D_769d8. an If1088 D_769dc. an If108c D_769e0. an If1090 D_769e4. an If1094 D_769e8. an If1098 D_769ec.
      an If109c D_769f0.                                   (* [comment removed for export] *)
      an If1110 D_76a64.                                   (* [comment removed for export] *)
      an I10d804 D_8fa60.                                 (* [comment removed for export] *)
      fsdG I10d808 D_8fa64 (at_ sp (-88)) GR Hstk (at_ sp (-144)) 144%nat.     (* [comment removed for export] *)
      fsdG I10d80c D_8fa68 (at_ sp (-96)) GR Hstk (at_ sp (-144)) 144%nat.     (* [comment removed for export] *)
      fsdG I10d810 D_8fa6c (at_ sp (-104)) GR Hstk (at_ sp (-144)) 144%nat.    (* [comment removed for export] *)
      fsdG I10d814 D_8fa70 (at_ sp (-112)) GR Hstk (at_ sp (-144)) 144%nat.    (* [comment removed for export] *)
      fsdG I10d818 D_8fa74 (at_ sp (-120)) GR Hstk (at_ sp (-144)) 144%nat.    (* [comment removed for export] *)
      fsdG I10d81c D_8fa78 (at_ sp (-128)) GR Hstk (at_ sp (-144)) 144%nat.    (* [comment removed for export] *)
      fsdG I10d820 D_8fa7c (at_ sp (-136)) GR Hstk (at_ sp (-144)) 144%nat.    (* [comment removed for export] *)
      an I10d824 D_8fa80.                                 (* [comment removed for export] *)
      an I10d828 D_8fa84.                                 (* [comment removed for export] *)
      an I10d82c D_8fa88.                                 (* [comment removed for export] *)
      an I10d830 D_8fa8c.                                 (* [comment removed for export] *)
      an I10d834 D_8fa90.                                 (* [comment removed for export] *)
      match goal with |- context [v_and ?m bp] => replace (v_and m bp) with bp by (symmetry; etransitivity; [|apply v_and_m1_l]; f_equal; apply bv_eq; reflexivity) end.
      an I10d838 D_8fa94.                                 (* [comment removed for export] *)
      fsdG I10d83c D_8fa98 (at_ this 2056) GR Hobj (at_ this 8) 2056%nat.      (* [comment removed for export] *)
      change (wbytes _ _ _) with (uw_mem M (Z_to_bv 64 30) (Z_to_bv 64 0)).
      ab_ft I10d840 D_8fa9c ltac:(condz).                (* [comment removed for export] *)
      ab_tk I10d844 D_8faa0 ltac:(condz).                (* [comment removed for export] *)
      ab_tk I10d87c D_8fad8 ltac:(condz).                (* [comment removed for export] *)
      an I10d8e4 D_8fb40. an I10d8e8 D_8fb44. an I10d8ec D_8fb48. an I10d8f0 D_8fb4c. an I10d8f4 D_8fb50.   (* [comment removed for export] *)
      cldg I10d8f8 D_8fb54 (LE8 (at_ rb 0x76a70)) (at_ rb 0x76a70) ltac:(apply RDW; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).    (* [comment removed for export] *)
      cldg I10d8fc D_8fb58 (LE8 bp) bp ltac:(apply RDW; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).                                (* [comment removed for export] *)
      cldg I10d900 D_8fb5c (LE8 (Z_to_bv 64 30)) (Z_to_bv 64 30) ltac:(apply RDW; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).    (* [comment removed for export] *)
      cldg I10d904 D_8fb60 (LE8 pc0) pc0 ltac:(apply RDW; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).                              (* [comment removed for export] *)
      cldg I10d908 D_8fb64 (LE8 this) this ltac:(apply RDW; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).                            (* [comment removed for export] *)
      cldg I10d90c D_8fb68 (LE8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(apply RDW; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).      (* [comment removed for export] *)
      cldg I10d910 D_8fb6c (LE8 fast) fast ltac:(apply RDW; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).                            (* [comment removed for export] *)
      an I10d914 D_8fb70.                                 (* [comment removed for export] *)
      an I10d918 D_8fb74.                                 (* [comment removed for export] *)
      rewrite ?at_at. wd_refl.
    - rewrite ?at_at. post. (lazymatch goal with |- ?G => let G' := eval unfold ui_clobx in G in change_no_check G' end). ra_chain.
  Qed.

  (* [comment removed for export] *)
  Lemma uiF : forall (M : word -> option byte) r0,
    getr r0 2 = at_ sp (-80) -> getr r0 24 = at_ thr 2047 -> store_ok segs M (at_ thr 3168) 1 = true ->
    (forall (k : Z) (v : word),
       In (k, v) [(-8, ra); (-16, getr regs 8); (-24, getr regs 9); (-32, getr regs 18); (-40, getr regs 19);
                  (-48, getr regs 20); (-56, getr regs 21); (-64, getr regs 22); (-72, getr regs 23); (-80, getr regs 24)]%Z ->
       rdn segs M (at_ sp k) 8 = Some (LE8 v)) ->
    regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ rb 0x76a70) M rom) (mkst r ra (wbytes M (at_ thr 3168) [Z_to_bv 8 0]) rom)
      /\ regs_agree CL regs r.
  Proof using UH H15 H14 H13 H12 H11 H10 H2 H1 Hret P fast bp pc0 this mem HUI TOK.
    intros M r0 R2 R24 SOK RD AG0. destruct UH as [_ _ _ _ _ _ _ G0 G1 G2]. pose proof (u64_range sp) as Hspr. pose proof (u64_range thr).
    assert (RD' : forall (k : Z) (v : word),
       In (k, v) [(-8, ra); (-16, getr regs 8); (-24, getr regs 9); (-32, getr regs 18); (-40, getr regs 19);
                  (-48, getr regs 20); (-56, getr regs 21); (-64, getr regs 22); (-72, getr regs 23); (-80, getr regs 24)]%Z ->
       rdn segs (wbytes M (at_ thr 3168) [Z_to_bv 8 0]) (at_ sp k) 8 = Some (LE8 v)).
    { intros k v Hin. assert (Hk : (-80 <= k <= -8)%Z) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E; intros; lia|]); destruct Hin).
      rewrite rdn_wbytes_out; [exact (RD k v Hin) | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]]. }
    wd_eexists. split.
    - chain_step; [reflexivity
        | eapply step_sb_at with (a := at_ thr 3168) (b := Z_to_bv 8 0);
          [exact If1114 | reflexivity | exact D_76a68 | gres; rwH; imm_norm; rewrite ?at_addi; reflexivity | gres; rwH; reflexivity | reflexivity | exact SOK]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      cldg If1118 D_76a6c (LE8 ra) ra ltac:(apply RD'; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).
      cldg If111c D_76a70 (LE8 (getr regs 8)) (getr regs 8) ltac:(apply RD'; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).
      cldg If1120 D_76a74 (LE8 (getr regs 9)) (getr regs 9) ltac:(apply RD'; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).
      cldg If1124 D_76a78 (LE8 (getr regs 18)) (getr regs 18) ltac:(apply RD'; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).
      cldg If1128 D_76a7c (LE8 (getr regs 19)) (getr regs 19) ltac:(apply RD'; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).
      cldg If112c D_76a80 (LE8 (getr regs 20)) (getr regs 20) ltac:(apply RD'; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).
      cldg If1130 D_76a84 (LE8 (getr regs 21)) (getr regs 21) ltac:(apply RD'; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).
      cldg If1134 D_76a88 (LE8 (getr regs 22)) (getr regs 22) ltac:(apply RD'; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).
      cldg If1138 D_76a8c (LE8 (getr regs 23)) (getr regs 23) ltac:(apply RD'; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).
      cldg If113c D_76a90 (LE8 (getr regs 24)) (getr regs 24) ltac:(apply RD'; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).
      an If1140 D_76a94.                                   (* [comment removed for export] *)
      aret If1144 D_76a98 ra.                              (* [comment removed for export] *)
      wd_refl.
    - apply (regs_agree_strengthen ui_clob ui_clobx regs).
      + (lazymatch goal with |- ?G => let G' := eval unfold ui_clobx in G in change_no_check G' end). ra_solve.
      + intros i Hi Hni. cbn [ui_clobx In] in Hi.
        repeat (destruct Hi as [<-|Hi]; [gres; rwH; rewrite ?at_addi, ?at_0; first [reflexivity | symmetry; assumption | f_equal; lia | exfalso; apply Hni; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto] |]).
        destruct Hi.
  Qed.

  (* [comment removed for export] *)
  Ltac via AG r H :=
    let T := fresh in pose proof (AG r ltac:(notin_list)) as T; rewrite H in T; exact T.

  (* [comment removed for export] *)
  Theorem ui_run_s : forall (D : nat) (bsr0 bsw0 : list byte),
    rdn segs mem (at_ bp (-8)) 8 = Some bsr0 -> length bsr0 = 8%nat ->
    rdn segs mem (at_ bp (-16)) 8 = Some bsw0 -> length bsw0 = 8%nat ->
    fpc mem (bytes_le_to_Z bsw0) (U bp) D ->
    exists r' M' (s : Z),
      msteps segs (mkst regs (at_ rb 0x76954) mem rom) (mkst r' ra M' rom)
      /\ regs_agree CL regs r'
      /\ (1 <= s <= 30)%Z /\ (s <= 2 + Z.of_nat D)%Z
      /\ rdn segs M' (at_ this 8) 4 = Some (LE4 s)
      /\ rdn segs M' (at_ this 16) 8 = Some (LE8 pc0)
      /\ rdn segs M' (at_ thr 3168) 1 = Some [Z_to_bv 8 0]
      /\ (forall x : word, M' x <> mem x ->
            (U sp - 144 <= U x < U sp)%Z \/ (U this + 8 <= U x < U this + 12)%Z \/ (U this + 16 <= U x < U this + 256)%Z
            \/ (U this + 2056 <= U x < U this + 2064)%Z \/ U x = (U thr + 3168)%Z)
      /\ mem_grows mem M'.
  Proof using Gtop SH GH UH Hfast H15 H14 H13 H12 H11 H10 H4 H2 H1 Hret P tctx tsdp bot top fast tp HUW HUI TOK.
    intros D bsr0 bsw0 Rr Lr Rw Lw FPC.
    pose proof TOK as TOK'. destruct TOK' as [_ _ UFC UF56 GTOK GRB STT STB AIN AINB RB].
    pose proof UH as UH'. destruct UH' as [Rin Ru SOKu Rg RP Hstk Hobj G0 G1 G2].
    pose proof (u64_range sp) as Hspr. pose proof (u64_range this) as Hth. pose proof (u64_range bp) as Hbp. pose proof (u64_range thr) as Hthr.
    pose proof (u64_range rb) as Hrb. pose proof (u64_range P) as HP.
    assert (RET : forall d, (d mod 2 = 0)%Z -> (0 <= d < 2 ^ 24)%Z -> ret_ok (at_ rb d)).
    { intros d Hd Hdr. apply ret_ok_at; [exact (proj1 RB) | exact Hd | lia]. }
    (* [comment removed for export] *)
    destruct uiA as (r1 & RUN1 & A1 & A2 & A4 & A9 & A21 & A20 & A8 & A18 & A19 & AG1).
    assert (GR1 : mem_grows mem ui_m1) by ((lazymatch goal with |- ?G => let G' := eval unfold ui_m1 in G in change_no_check G' end); repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
    (* [comment removed for export] *)
    destruct (ain_run segs rb (ut_g_inited t) AIN AINB ui_m1 rom r1 (at_ rb 0x769a0)) as (r2 & RUN2 & B10 & AG2).
    { rewrite <- Rin. apply rdn_ext; [wd_ulia_c|]. intros x Hx. apply ui_m1_outside. revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx. lia. }
    { apply RET; [reflexivity | lia]. }
    { exact A1. }
    (* [comment removed for export] *)
    destruct (uiB ui_m1 r2 B10 ltac:(eapply regs_agree_trans; [exact AG1 | regs_agree_weaken AG2])) as (r3 & RUN3 & C1 & CK & AG3).
    (* [comment removed for export] *)
    assert (GH1 : gctH segs (ut_gct t) ui_m1 (at_ sp (-80)) tp tsdp tctx thr).
    { apply (gctH_keep segs (ut_gct t) mem ui_m1); [exact GH | | exact GR1]. intros x Hx. rewrite at_u in Hx by lia. apply ui_m1_outside. lia. }
    destruct (gct_run segs (ut_gct t) GTOK ui_m1 rom r3 (at_ rb 0x769a8) (at_ sp (-80)) tp tsdp tctx thr GH1) as (r4 & RUN4 & D10 & D11 & AG4).
    { apply RET; [reflexivity | lia]. }
    { exact C1. }
    { rewrite (CK 2) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto). via AG2 (2 : reg) A2. }
    { rewrite (CK 4) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto). via AG2 (4 : reg) A4. }
    rewrite GRB in RUN4. rewrite at_at in RUN4. cbn [Z.add] in RUN4.
    set (M2 := wbytes ui_m1 (at_ sp (-88)) (LE8 (at_ rb 0x769a8))) in RUN4.
    assert (HM2 : forall x : word, (U x < U sp - 88)%Z \/ (U sp <= U x < U this + 8)%Z \/ (U this + 12 <= U x)%Z -> M2 x = mem x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold M2 in G in change_no_check G' end). rewrite wbytes_outside; [apply ui_m1_outside; lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    assert (GR2 : mem_grows mem M2) by ((lazymatch goal with |- ?G => let G' := eval unfold M2 in G in change_no_check G' end); eapply mem_grows_trans; [exact GR1 | apply wbytes_grows]).
    (* [comment removed for export] *)
    destruct (uiC M2 r4 D10) as (r5 & RUN5 & E1 & E10 & E23 & E24 & EK & AG5).
    { rewrite <- Ru. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. apply HM2. cbn in Hx. lia. }
    { eapply store_ok_mono; [exact GR2 | exact SOKu]. }
    { eapply regs_agree_trans; [exact AG3 | regs_agree_weaken AG4]. }
    set (M3 := wbytes M2 (at_ thr 3168) [Z_to_bv 8 1]) in RUN5.
    assert (HM3 : forall x : word, U x <> (U thr + 3168)%Z ->
              (U x < U sp - 88)%Z \/ (U sp <= U x < U this + 8)%Z \/ (U this + 12 <= U x)%Z -> M3 x = mem x).
    { intros x Hx1 Hx2. (lazymatch goal with |- ?G => let G' := eval unfold M3 in G in change_no_check G' end). rewrite wbytes_outside; [apply HM2; exact Hx2 | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]]. }
    assert (GR3 : mem_grows mem M3) by ((lazymatch goal with |- ?G => let G' := eval unfold M3 in G in change_no_check G' end); eapply mem_grows_trans; [exact GR2 | apply wbytes_grows]).
    assert (SH3 : stkH segs M3 thr top bot).
    { apply (stkH_keep segs mem M3 _ _ _ SH). intros x Hx. apply HM3; lia. }
    (* [comment removed for export] *)
    destruct (stt_run segs rb STT M3 rom r5 (at_ rb 0x769c8) thr top bot SH3 ltac:(apply RET; [reflexivity | lia]) E1 E10) as (r6 & RUN6 & F10 & F11 & AG6).
    (* [comment removed for export] *)
    destruct (uiD M3 r6 F10 ltac:(via AG6 (23 : reg) E23) ltac:(eapply regs_agree_trans; [exact AG5 | regs_agree_weaken AG6])) as (r7 & RUN7 & G1' & G10 & G22 & GK & AG7).
    (* [comment removed for export] *)
    destruct (stb_run segs rb STB M3 rom r7 (at_ rb 0x769d4) thr top bot SH3 ltac:(apply RET; [reflexivity | lia]) G1' G10) as (r8 & RUN8 & I10 & I11 & AG8).
    (* [comment removed for export] *)
    assert (K2 : getr r8 2 = at_ sp (-80)).
    { rewrite (AG8 2) by notin_list. rewrite (GK 2) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto). rewrite (AG6 2) by notin_list. rewrite (EK 2) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto).
      rewrite (AG4 2) by notin_list. rewrite (CK 2) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto). via AG2 (2 : reg) A2. }
    Ltac thread8 AG8 GK AG6 EK AG4 CK AG2 r A :=
      rewrite (AG8 r) by notin_list; rewrite (GK r) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto); rewrite (AG6 r) by notin_list; rewrite (EK r) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto);
      rewrite (AG4 r) by notin_list; rewrite (CK r) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto); via AG2 r A.
    assert (K4 : getr r8 4 = tp) by (thread8 AG8 GK AG6 EK AG4 CK AG2 (4 : reg) A4).
    assert (K8 : getr r8 8 = bp) by (thread8 AG8 GK AG6 EK AG4 CK AG2 (8 : reg) A8).
    assert (K9 : getr r8 9 = Z_to_bv 64 30) by (thread8 AG8 GK AG6 EK AG4 CK AG2 (9 : reg) A9).
    assert (K18 : getr r8 18 = pc0) by (thread8 AG8 GK AG6 EK AG4 CK AG2 (18 : reg) A18).
    assert (K19 : getr r8 19 = this) by (thread8 AG8 GK AG6 EK AG4 CK AG2 (19 : reg) A19).
    assert (K20 : getr r8 20 = Z_to_bv 64 0) by (thread8 AG8 GK AG6 EK AG4 CK AG2 (20 : reg) A20).
    assert (K21 : getr r8 21 = fast) by (thread8 AG8 GK AG6 EK AG4 CK AG2 (21 : reg) A21).
    assert (K22 : getr r8 22 = top) by (rewrite (AG8 22) by notin_list; exact G22).
    assert (K23 : getr r8 23 = thr) by (rewrite (AG8 23) by notin_list; rewrite (GK 23) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto); via AG6 (23 : reg) E23).
    assert (K24 : getr r8 24 = at_ thr 2047) by (rewrite (AG8 24) by notin_list; rewrite (GK 24) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto); via AG6 (24 : reg) E24).
    destruct (uiE M3 r8 GR3 I10 K22 K23 K24 K2 K4 K8 K9 K18 K19 K20 K21 ltac:(eapply regs_agree_trans; [exact AG7 | regs_agree_weaken AG8]))
      as (r9 & RUN9 & J1 & J2 & J10 & J11 & J12 & J13 & J14 & J15 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J23 & J24 & AG9).
    set (M4 := uw_mem M3 (Z_to_bv 64 30) (Z_to_bv 64 0)) in RUN9.
    assert (HM4 : forall x : word, U x <> (U thr + 3168)%Z ->
              (U x < U sp - 144)%Z \/ (U sp <= U x < U this + 8)%Z \/ (U this + 12 <= U x < U this + 2056)%Z \/ (U this + 2064 <= U x)%Z -> M4 x = mem x).
    { intros x Hx1 Hx2. (lazymatch goal with |- ?G => let G' := eval unfold M4 in G in change_no_check G' end). rewrite uw_mem_outside by lia. apply HM3; lia. }
    assert (GR4 : mem_grows mem M4).
    { (lazymatch goal with |- ?G => let G' := eval unfold M4, uw_mem in G in change_no_check G' end). eapply mem_grows_trans; [exact GR3|]. do 8 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. }
    (* [comment removed for export] *)
    destruct (uf_run segs (at_ rb 0x8f40c) (ut_g_pgsz t) UFC UF56 r9 rom (at_ rb 0x76a70) (at_ sp (-80)) this pc0 bp top bot
                ltac:(apply RET; [reflexivity | lia]) J1 J2 J10 J11 J12 J13 J14 J15
                ltac:(first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]) ltac:(first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]) ltac:(lia) ltac:(lia) ltac:(lia) Gtop (sh_lt _ _ _ _ _ SH)
                M4 P) with (D := D) (bsr0 := bsr0) (bsw0 := bsw0)
      as (r10 & M5 & s & RUN10 & L10 & L11 & AG10 & S1 & S2 & SZ & PC & FR5 & GR5).
    { rewrite <- Rg. apply rdn_ext; [wd_ulia_c|]. intros x Hx. apply HM4; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia. }
    { rewrite <- RP. apply rdn_ext; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. apply HM4; cbn in Hx; lia. }
    { lia. }
    { lia. }
    { eapply store_ok_mono; [exact GR4|]. rewrite at_at. (lazymatch goal with |- ?G => let G' := eval cbn [Z.add] in G in change_no_check G' end).
      eapply (store_ok_sub segs mem (at_ sp (-144)) _ 144); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { eapply store_ok_mono; [exact GR4|].
      eapply (store_ok_sub segs mem (at_ this 8) _ 2056); [rewrite at_u; lia | exact Hobj | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { rewrite <- Rr. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. apply HM4; cbn in Hx; lia. }
    { exact Lr. }
    { rewrite <- Rw. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. apply HM4; cbn in Hx; lia. }
    { exact Lw. }
    { pose proof (bytes_le_to_Z_bound bsw0) as Bw. rewrite Lw in Bw. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in Bw.
      apply (fpc_kept_gen mem _ _ _ FPC M4).
      destruct (fpc_shape _ _ _ _ FPC) as [ST | FRM]; [left; exact ST | right].
      intros a Ha. pose proof (u64_range (Z_to_bv 64 a)).
      apply HM4; rewrite u_Z2bv by (unfold PTRHI in Ha; lia); lia. }
    (* [comment removed for export] *)
    assert (HM5 : forall x : word, (U sp - 80 <= U x < U sp)%Z -> M5 x = ui_m1 x).
    { intros x Hx. destruct (decide (M5 x = M4 x)) as [E5|NE5].
      2:{ exfalso. destruct (FR5 x NE5) as [F|F]; rewrite ?at_u in F by lia; lia. }
      rewrite E5. (lazymatch goal with |- ?G => let G' := eval unfold M4 in G in change_no_check G' end). rewrite uw_mem_outside by lia. (lazymatch goal with |- ?G => let G' := eval unfold M3 in G in change_no_check G' end). rewrite wbytes_outside by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
      (lazymatch goal with |- ?G => let G' := eval unfold M2 in G in change_no_check G' end). rewrite wbytes_outside by (rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia). reflexivity. }
    destruct (uiF M5 r10) as (r11 & RUN11 & AG11).
    { rewrite (AG10 2) by notin_list. exact J2. }
    { rewrite (AG10 24) by notin_list. exact J24. }
    { eapply store_ok_mono; [| exact SOKu]. eapply mem_grows_trans; [exact GR4 | exact GR5]. }
    { intros k v Hin. assert (Hk : (-80 <= k <= -8)%Z) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E; intros; lia|]); destruct Hin).
      rewrite <- (ui_m1_slots k v Hin). apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. apply HM5. cbn in Hx. lia. }
    { eapply regs_agree_trans; [exact AG9 | regs_agree_weaken AG10]. }
    (* [comment removed for export] *)
    exists r11, (wbytes M5 (at_ thr 3168) [Z_to_bv 8 0]), s.
    split.
    { eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|].
      eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|]. eapply msteps_trans; [exact RUN6|].
      eapply msteps_trans; [exact RUN7|]. eapply msteps_trans; [exact RUN8|]. eapply msteps_trans; [exact RUN9|].
      eapply msteps_trans; [exact RUN10|]. exact RUN11. }
    split; [exact AG11|]. split; [exact S1|]. split; [exact S2|].
    split. { rewrite rdn_wbytes_out; [exact SZ | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]]. }
    split. { rewrite rdn_wbytes_out; [exact PC | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]]. }
    split. { pose proof (rdn_wbytes_hit segs [Z_to_bv 8 0] M5 (at_ thr 3168)) as X. cbn [length] in X. apply X. rewrite at_u by lia. lia. }
    split.
    { intros x Hx. pose proof (u64_range x).
      destruct (Z.eq_dec (U x) (U thr + 3168)) as [E|NE]; [right; right; right; right; exact E|].
      rewrite wbytes_outside in Hx by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
      destruct (decide (M5 x = M4 x)) as [E5|NE5].
      2:{ destruct (FR5 x NE5) as [F|[F|F]]; rewrite ?at_u in F by lia; [left; lia | right; left; lia | right; right; left; lia]. }
      rewrite E5 in Hx.
      destruct (Z.lt_ge_cases (U x) (U sp - 144)); [exfalso; apply Hx; apply HM4; lia|].
      destruct (Z.lt_ge_cases (U x) (U sp)); [left; lia|].
      destruct (Z.lt_ge_cases (U x) (U this + 8)); [exfalso; apply Hx; apply HM4; lia|].
      destruct (Z.lt_ge_cases (U x) (U this + 12)); [right; left; lia|].
      destruct (Z.lt_ge_cases (U x) (U this + 2056)); [exfalso; apply Hx; apply HM4; lia|].
      destruct (Z.lt_ge_cases (U x) (U this + 2064)); [right; right; right; left; lia|].
      exfalso; apply Hx; apply HM4; lia. }
    eapply mem_grows_trans; [exact GR4|]. eapply mem_grows_trans; [exact GR5 | apply wbytes_grows].
  Qed.

  (* [comment removed for export] *)
  Theorem ui_run : forall (D : nat) (bsr0 bsw0 : list byte),
    rdn segs mem (at_ bp (-8)) 8 = Some bsr0 -> length bsr0 = 8%nat ->
    rdn segs mem (at_ bp (-16)) 8 = Some bsw0 -> length bsw0 = 8%nat ->
    fpc mem (bytes_le_to_Z bsw0) (U bp) D ->
    exists r' M' (s : Z),
      msteps segs (mkst regs (at_ rb 0x76954) mem rom) (mkst r' ra M' rom)
      /\ regs_agree CL regs r'
      /\ (1 <= s <= 30)%Z /\ (s <= 2 + Z.of_nat D)%Z
      /\ rdn segs M' (at_ this 8) 4 = Some (LE4 s)
      /\ rdn segs M' (at_ this 16) 8 = Some (LE8 pc0)
      /\ rdn segs M' (at_ thr 3168) 1 = Some [Z_to_bv 8 0]
      /\ (forall x : word, M' x <> mem x ->
            (U sp - 144 <= U x < U sp)%Z \/ (U this + 8 <= U x < U this + 256)%Z \/ (U this + 2056 <= U x < U this + 2064)%Z \/ U x = (U thr + 3168)%Z)
      /\ mem_grows mem M'.
  Proof using Gtop SH GH UH Hfast H15 H14 H13 H12 H11 H10 H4 H2 H1 Hret P tctx tsdp bot top fast tp HUW HUI TOK.
    intros D bsr0 bsw0 Rr Lr Rw Lw FPC.
    destruct (ui_run_s D bsr0 bsw0 Rr Lr Rw Lw FPC) as (r' & M' & s & RUN & AG & S1 & S2 & SZ & PC & UN & FR & GR).
    exists r', M', s. repeat (split; [assumption|]). split; [|exact GR].
    intros x Hx. destruct (FR x Hx) as [F|[F|[F|[F|F]]]]; [left | right; left | right; left | right; right; left | right; right; right]; try lia; try exact F.
  Qed.
End UI.
End FPGen1d.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.glaze.binary_reflection.images Require Import Asan.

Section FPGen2.
Context {fx : FPState}.
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

Definition asan_gct_tab : gct_tab := GCT (Z_to_bv 64 0) (Z_to_bv 64 0x106de0) (Z_to_bv 64 0xf7070).
Definition asan_ui_tab : ui_tab := UIT (Z_to_bv 64 0) asan_gct_tab 0x108258 0xff250 0x10000 0x65d000.

Lemma asan_gct_tab_ok : gct_tab_ok ASEGS asan_gct_tab.
Proof using.
  split; (lazymatch goal with |- ?G => let G' := eval cbn [gt_rb gt_tsd gt_pgs asan_gct_tab] in G in change_no_check G' end).
  - (lazymatch goal with |- ?G => let G' := eval unfold gct_words in G in change_no_check G' end). code_ato_vm.
  - (lazymatch goal with |- ?G => let G' := eval unfold tsd_words in G in change_no_check G' end). code_ato_vm.
  - gaddr2_tac F_70a34 D_70a34 F_70a38 D_70a38.
  - gjump_tac F_70a48 D_70a48.
  - (lazymatch goal with |- ?G => let G' := eval unfold pgs_words in G in change_no_check G' end). code_ato_vm.
  - split; vm_compute; [reflexivity | exact eq_refl].
Qed.

Lemma asan_ui_tab_ok : ui_tab_ok ASEGS asan_ui_tab.
Proof using.
  split; (lazymatch goal with |- ?G => let G' := eval cbn [ut_rb ut_gct ut_g_inited ut_g_pgsz ut_img_lo ut_img_hi asan_ui_tab] in G in change_no_check G' end).
  - (lazymatch goal with |- ?G => let G' := eval unfold ui_words in G in change_no_check G' end). code_ato_vm.
  - (lazymatch goal with |- ?G => let G' := eval unfold uw_words in G in change_no_check G' end). code_ato_vm.
  - (lazymatch goal with |- ?G => let G' := eval unfold uf_words in G in change_no_check G' end). code_ato_vm.
  - gload_tac F_8f43c D_8f43c F_8f440 D_8f440.
  - exact asan_gct_tab_ok.
  - reflexivity.
  - (lazymatch goal with |- ?G => let G' := eval unfold stt_words in G in change_no_check G' end). code_ato_vm.
  - (lazymatch goal with |- ?G => let G' := eval unfold stb_words in G in change_no_check G' end). code_ato_vm.
  - (lazymatch goal with |- ?G => let G' := eval unfold ain_words in G in change_no_check G' end). code_ato_vm.
  - gload_tac F_74ca4 D_74ca4 F_74ca8 D_74ca8.
  - split; vm_compute; [reflexivity | exact eq_refl].
Qed.

(* [comment removed for export] *)
Definition asan_ui_run := ui_run ASEGS asan_ui_tab asan_ui_tab_ok.
Definition asan_ui_run_s := ui_run_s ASEGS asan_ui_tab asan_ui_tab_ok.
End FPGen2.
