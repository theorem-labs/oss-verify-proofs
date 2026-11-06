(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "iff"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sprop"; "sstate"; "holds"; "rw"; "ss_next"; "eval"; "rm"; "sobj"; "rl"; "sprop_eqb"; "SVar"; "sprop_below"; "SLit"; "SPUle"; "agree_below"; "ss_facts"; "ss_lenient"; "swf"; "ext_low"; "obj_range"; "ranges_disjoint"; "soff"; "@Corelib.Init.Datatypes"; "list"; "prod"; "bool"; "true"; "option"; "andb"; "Some"; "nat"; "nil"; "fst"; "snd"; "negb"; "pair"; "false"; "None"; "length"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "jpred"; "stableJ"; "ok_frameJ"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "VmMaps"; "m_vmmaps"; "m_vm_materialized"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "MInv"; "ma_L"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "pow"; "leb"; "lt"; "mul"; "modulo"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLoop.WithSegs.Bracket"; "tv_eval_eq"; "snapJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLoop.WithSegs.Tracked"; "tv_geo"; "robjs_missT"; "has_top_facts"; "F_top_hi"; "F_top_lo"; "robjs_missT_statics"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "lf_state"; "sym_run"; "@Stdlib.Lists.List"; "forallb"; "In"; "existsb"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "JGi"; "tvv"; "tnz"; "tv_below"; "T_ok"; "aceil"; "inited"; "robj_stack"; "robj_tracked"; "tvd"; "tvin"; "tvz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "sv_has_rl"; "rho_set_rl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "V_TOP"; "rd_of"; "wok_of"; "tp_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLoop"; "CAP"; "ALIGNED"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "diffs_ok"; "state_diff"; "set_rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "mc_img_hi"; "mc_img_lo"; "topL"; "wz"; "@Corelib.Init.Peano"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.BvBase"; "len_word"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvPristine"; "robj_img_misses"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvStatics"; "a_got"; "a_guard"; "a_nl"; "statics_disjoint"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "IB"; "UNIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Pristine"; "reads"; "@Stdlib.PArith.BinPos.Pos"; "le"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws Contract Pristine.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymCall Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue CursorGlue ListObj TobjJV DrvStatics DrvPristine.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

Section JFrame.
Variable C : mconsts.
Variable NP : positive.
Variables Kc Kc' : list event -> Model -> Prop.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.

Lemma JGi_sys : ltac2:(tb__ "0|4|
S2fS1eS1fS6S6A2A1S3cS7S7S1eS38A1M0G0S37S37S83VNP;R9A2S0S20S5fRaR9A2S21A3S2fS84R1RcA2S0S30Q40A1M1SbR9R2A2SbRaR2A2A3F_;Fi;S2fS0S1eS30Q8A1M2A1S10R9R1A2S10RaR1A2A3Fl;S0G1S22G2A1F_;SeR9A1SeRaA1A3S0S39S3aR6A1S3aR7A1A3VKc;RaR8A2VKc';RaR8A2F_;S5cVsegs;VC;VNP;VKc;Vrho0;VP0f;S26S1fS2eS2eA2A1M3RfReRdRbR9AcS5cVsegs;VC;VNP;VKc';Vrho0;VP0f;G3R10RfRdRbR9AcF_;F_;F_;F_;F_;F_;F_;F_;Fmd';Fmd;Ftr';Ftr;Frho';Frho;FAi;Ftv;Fn;").
Proof using .
  intros n tv Ai rho rho' tr tr' md md' Hle Hb Hw Hl Hm Hvm HK (Hav & Hk & [HM Hi] & HP & (HN & HD & HZ) & HKF & HP0).
  assert (Hag : agree_below n rho rho').
  { split; [intros i Hi'; symmetry; exact (Hw i Hi')|]. split; [intros l; symmetry; exact (Hl l) | intros a; rewrite Hm; reflexivity]. }
  pose proof (agree_below_vals _ _ _ Hag) as Hav'.
  split; [|split; [exact (HK Hk)|split; [split; [|exact Hi]|split; [exact HP|split; [split; [|split]|split; [|exact HP0]]]]]].
  - eapply agree_vals_trans; [exact Hav|]. eapply agree_vals_le; [exact Hle | exact Hav'].
  - unfold MInvR in *. rewrite Hm, Hvm. exact HM.
  - eapply tvin_agree; [exact Hav' | exact Hb | exact HN].
  - eapply tvd_agree; [exact Hav' | exact Hb | exact HD].
  - eapply tvz_agree; [exact Hav' | exact Hb | exact HZ].
  - intros a Ha Hp. rewrite Hm. exact (HKF a Ha Hp).
Qed.
End JFrame.

Section Helpers.
Variable ok : world -> Prop.

Lemma run_trJ : ltac2:(tb__ "0|1|
S25S1eS2eA1S9S1eS55A1M0S34S7S4cS0S22G0A1S57Vsegs;R7R6R5S21A5S24G0R4A2A3S0S20S18R6A1S2bA3S36Vsegs;Vok;R5A3S35ScR8A1R6A2S55S7S59S55R2RaA3S16ScRcA1R9R2A3S4aVsegs;Vok;S33Vsegs;RbS56R4A1R3A4R9A4F_;F_;Frho';FLf;S4aVsegs;Vok;S33Vsegs;R8RaR7A4R6A4F_;F_;F_;F_;F_;FQ;Frho;FJ;Fleaves;FS;Fcuts;Ffuel;").
Proof using .
  intros fuel cuts S leaves J rho Q Hrun Hstrict Hok Hst H.
  eapply triple_seq; [apply triple1_triple; eapply sym_run_soundJ; [exact Hrun | exact Hok | rewrite Hstrict; discriminate | exact Hst]|].
  clear Hrun. revert H. generalize (ss_next S) as n. induction leaves as [|Lf rest IH]; intros n H.
  - apply triple_leavesJ_nil.
  - apply triple_leavesJ_cons; [intros rho' Hag; apply H; [left; reflexivity | exact Hag]|].
    apply IH. intros Lf' rho' Hin Hag. apply H; [right; exact Hin | exact Hag].
Qed.

Lemma erun_trJ : ltac2:(tb__ "0|1|
S25S1eS2eA1S9S1eS55A1M0S34S7S4bOF_;S0S22G0A1S57Vsegs;R7R6R5S21A5S24G0R4A2A3S0S20S18R6A1S2bA3S35ScR7A1R5A2S55S7S59S55R2R9A3S16ScRbA1R8R2A3S49Vsegs;S33Vsegs;RaS56R4A1R3A4R8A3F_;F_;Frho';FLf;S49Vsegs;S33Vsegs;R7R9R6A4R5A3F_;F_;F_;F_;FQ;Frho;FJ;Fleaves;FS;Fcuts;Ffuel;").
Proof using .
  intros fuel cuts S leaves J rho Q Hrun Hstrict Hst H w Hsp.
  destruct (sym_run_completeJ segs fuel cuts S leaves J rho w Hstrict Hst Hrun Hsp) as (Lf & rho' & w' & Hin & Hst' & Hag & Hsp').
  destruct (H Lf rho' Hin Hag w' Hsp') as (w'' & Hst'' & HQ).
  exists w''. split; [eapply wsteps_trans; eauto | exact HQ].
Qed.

Lemma SPJ_add_facts : ltac2:(tb__ "0|0|
S34S7S1eS8A1S9S4bS33Vsegs;R5R2R4R1A5S3fS8SaR5A1R4A3S0S20S58S8S13ScR4A1A1R5A3S21A3S33Vsegs;R8S6eR6R5A2R7R4A5F_;F_;F_;Fw;FS;FFs;Frho;FJ;").
Proof using . intros J rho Fs S w [Hsm HJ] HF Hb. split; [apply smatch_add_facts; assumption | exact HJ]. Qed.

Lemma triple_add_facts : ltac2:(tb__ "0|0|
S34S7S1eS8A1S9S9S4cS0S9S6eR4R3A2R2A3S0S20S58S8S13ScR4A1A1R5A3S21A3S3fS8SaR7A1R6A3S4aVsegs;Vok;S33Vsegs;R9R5R8A4R4A4S4aVsegs;Vok;S33Vsegs;RaR7R9A4R5A4F_;F_;F_;F_;FQ;FS';FS;FFs;Frho;FJ;").
Proof using .
  intros J rho Fs S S' Q <- Hb HF HT. eapply triple_conseq; [| intros w Hw; exact Hw | exact HT].
  intros w Hw. apply SPJ_add_facts; assumption.
Qed.
Lemma etriple_add_facts : ltac2:(tb__ "0|0|
S34S7S1eS8A1S9S9S4bOF_;S0S9S6eR4R3A2R2A3S0S20S58S8S13ScR4A1A1R5A3S21A3S3fS8SaR7A1R6A3S49Vsegs;S33Vsegs;R9R5R8A4R4A3S49Vsegs;S33Vsegs;RaR7R9A4R5A3F_;F_;F_;F_;FQ;FS';FS;FFs;Frho;FJ;").
Proof using .
  intros J rho Fs S S' Q <- Hb HF HT. eapply etriple_conseq; [| intros w Hw; exact Hw | exact HT].
  intros w Hw. apply SPJ_add_facts; assumption.
Qed.

Lemma triple_restate : ltac2:(tb__ "0|3|
S34S7S9S9S1eS1fS6S6A2A1M0S4cS0S20S19R3A1S21A3S0S22S1fG0S1eS8A1M1A2M2A1S72R5R4A2S24G2S2aG0G1R3S26S8A1A4A2A3S71R7R4A2S4aVsegs;Vok;S33Vsegs;R9R6R8A4R4A4S4aVsegs;Vok;S33Vsegs;RaR8R9A4R5A4F_;F_;F_;F_;FQ;Fd;FS';FS;Frho;FJ;").
Proof using .
  intros J rho S S' d Q Hwf Hd Hok HT. eapply triple_conseq; [| intros w Hw; exact Hw | exact HT].
  intros w Hw. eapply SPJ_restate; eauto.
Qed.
Lemma etriple_restate : ltac2:(tb__ "0|3|
S34S7S9S9S1eS1fS6S6A2A1M0S4bOF_;S0S20S19R3A1S21A3S0S22S1fG0S1eS8A1M1A2M2A1S72R5R4A2S24G2S2aG0G1R3S26S8A1A4A2A3S71R7R4A2S49Vsegs;S33Vsegs;R9R6R8A4R4A3S49Vsegs;S33Vsegs;RaR8R9A4R5A3F_;F_;F_;F_;FQ;Fd;FS';FS;Frho;FJ;").
Proof using .
  intros J rho S S' d Q Hwf Hd Hok HT. eapply etriple_conseq; [| intros w Hw; exact Hw | exact HT].
  intros w Hw. eapply SPJ_restate; eauto.
Qed.

Lemma triple_absurd1 : ltac2:(tb__ "0|0|
S34S9S7S4cS8S0S22S8A1S5bS8S17R4A1U0A3S24S8R1A2A3S3SaR4R2A2A1S4aVsegs;Vok;S33Vsegs;R7R6R5A4R4A4F_;F_;Fp;FQ;Frho;FS;FJ;").
Proof using .
  intros J S rho Q p Hp Hn. apply triple_leafJ_absurd. intros HF. apply Hn.
  destruct (ss_facts S) as [|q fs']; [discriminate|]. injection Hp as ->. exact (Forall_inv HF).
Qed.
Lemma etriple_absurd1 : ltac2:(tb__ "0|0|
S34S9S7S4bOF_;S8S0S22S8A1S5bS8S17R4A1U0A3S24S8R1A2A3S3SaR4R2A2A1S49Vsegs;S33Vsegs;R7R6R5A4R4A3F_;F_;Fp;FQ;Frho;FS;FJ;").
Proof using .
  intros J S rho Q p Hp Hn. apply etriple_leafJ_absurd. intros HF. apply Hn.
  destruct (ss_facts S) as [|q fs']; [discriminate|]. injection Hp as ->. exact (Forall_inv HF).
Qed.
End Helpers.

Section Pure.
Variable ok : world -> Prop.
Lemma triple_Jpure : ltac2:(tb__ "0|1|
OS34S9S7S4cS1eS38A1S37R6R4R2R1A3R8F_;Fmd;Ftr;R6S4aVsegs;Vok;S33Vsegs;R6R5R4A4R3A4M0F_;G0F_;F_;FQ;Frho;FS;FJ;FX;").
Proof using . intros X J S rho Q HX HT n Hg w [Hsm HJ]. exact (HT (HX _ _ HJ) n Hg w (conj Hsm HJ)). Qed.

Lemma etriple_Jpure : ltac2:(tb__ "0|1|
OS34S9S7S4bOF_;S1eS38A1S37R6R4R2R1A3R8F_;Fmd;Ftr;R6S49Vsegs;S33Vsegs;R6R5R4A4R3A3M0F_;G0F_;F_;FQ;Frho;FS;FJ;FX;").
Proof using . intros X J S rho Q HX HT w [Hsm HJ]. exact (HT (HX _ _ HJ) w (conj Hsm HJ)). Qed.
End Pure.

Lemma soff_var : ltac2:(tb__ "0|1|
S7S2fS45S31Q40M0SbR2R1A2A2S43Z2Z3fA2A2S0S2eS1dR3S12R2A1A2S31G0SbR3R2A2A2A3F_;Fi;Frho;").
Proof using .
  intros rho i Hi. unfold soff. cbn [eval]. rewrite bv_signed_U.
  destruct (Zsigned_spec (bv_unsigned (rw rho i))) as [[_ X]|[Y X]]; [exact X|]. pose proof (bv_urange (rw rho i)). lia.
Qed.

Lemma len_word_zero : ltac2:(tb__ "0|2|
S1eS30Q8A1M0A1S0S25S2dG0R1A2U0A3S0S30Q40M1A1S79G0R2A2S32G1Z0A2A3F_;Fbs;").
Proof using . intros bs H. unfold len_word. rewrite H. reflexivity. Qed.

Lemma holds_of_existsb : ltac2:(tb__ "0|0|
S7S1eS8A1S8S3fS8SaR3A1R2A3S0S20S5aS8S11R2A1R3A3S21A3SaR5R3A2F_;F_;Ff;Ffacts;Frho;").
Proof using .
  intros rho facts f HFa He. apply existsb_exists in He as (g & Hg & Hge). apply sprop_eqb_sound in Hge. subst g.
  exact (proj1 (Forall_forall _ _) HFa _ Hg).
Qed.

Lemma reads8_of_bytes : ltac2:(tb__ "0|3|
S30Q40A1S22S30Q8A1M0A1M1F_;S2eS25S78R1U8M2A2S2G0G0S0G1S6bVsegs;R5S77S42R4S48R3A1A2A1A3S24G0R1A2A3Lb;A2F_;Fk;S2S2eS2eS1S82Vsegs;R4R3G2R1A5S1S41Z0R1A2S45R1S43Z2Z40A2A2A2A2Lgd;A2F_;Fa;Fm;").
Proof using .
  intros m a H.
  destruct (H 0%nat ltac:(lia)) as [b0 E0]. destruct (H 1%nat ltac:(lia)) as [b1 E1].
  destruct (H 2%nat ltac:(lia)) as [b2 E2]. destruct (H 3%nat ltac:(lia)) as [b3 E3].
  destruct (H 4%nat ltac:(lia)) as [b4 E4]. destruct (H 5%nat ltac:(lia)) as [b5 E5].
  destruct (H 6%nat ltac:(lia)) as [b6 E6]. destruct (H 7%nat ltac:(lia)) as [b7 E7].
  pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1. pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
  pose proof (bv_unsigned_in_range 8 b4) as R4. pose proof (bv_unsigned_in_range 8 b5) as R5. pose proof (bv_unsigned_in_range 8 b6) as R6. pose proof (bv_unsigned_in_range 8 b7) as R7.
  change (bv_modulus 8) with 256 in *.
  set (gd := bv_unsigned b0 + 2^8 * bv_unsigned b1 + 2^16 * bv_unsigned b2 + 2^24 * bv_unsigned b3
             + 2^32 * bv_unsigned b4 + 2^40 * bv_unsigned b5 + 2^48 * bv_unsigned b6 + 2^56 * bv_unsigned b7).
  exists gd. split; [|lia].
  intros k Hk. unfold le_byte. rewrite Z.shiftr_div_pow2 by lia. rewrite (Z.mod_small gd) by (change (2 ^ (8 * Z.of_nat 8)) with (2^64); lia).
  assert (B : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b) by (intros b; apply Z_to_bv_bv_unsigned).
  destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; [| | | | | | | |lia];
    [rewrite E0, <- (B b0) at 1 | rewrite E1, <- (B b1) at 1 | rewrite E2, <- (B b2) at 1 | rewrite E3, <- (B b3) at 1
    | rewrite E4, <- (B b4) at 1 | rewrite E5, <- (B b5) at 1 | rewrite E6, <- (B b6) at 1 | rewrite E7, <- (B b7) at 1];
    f_equal; f_equal; cbn [Z.of_nat Z.mul Pos.mul Pos.of_succ_nat]; subst gd.
  all: first [rewrite Z.pow_0_r, Z.div_1_r | idtac].
  all: symmetry; Z.to_euclidean_division_equations; nia || lia.
Qed.

Lemma ext_low32_mod : ltac2:(tb__ "0|2|
S30Q40M0A1S0S2eS47S31G0S1aS21Q20R1A3A2S43Z2Z20A2M1A2S47S31G0R1A2G1A2A3Fv;").
Proof using .
  intros v. unfold ext_low. rewrite sext64_32_mod by lia.
  rewrite bv_extract_unsigned. change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
  apply Z.mod_mod. lia.
Qed.

Section Tracked.
Variable C : mconsts.
Variable NP : positive.
Variable Kc : ltac2:(tb__ "0|0|
S1eS38A1S37OF_;F_;").
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Hypothesis ML : malloc_laws segs C.

Definition F_top_lo : sprop := ltac2:(tb__ "0|0|
S15S14Z7fff7f800000A1S12S6aA1A2").
Definition F_top_hi : sprop := ltac2:(tb__ "0|0|
S15S12S6aA1S14Z7fffff800000A1A2").
Definition has_top_facts (facts : list sprop) : bool := ltac2:(tb__ "0|0|
S23S5aS8S11S53A1Vfacts;A3S5aS8S11S52A1Vfacts;A3A2").

Lemma holds_of_existsb0 : ltac2:(tb__ "0|0|
S7S1eS8A1S8S3fS8SaR3A1R2A3S0S20S5aS8S11R2A1R3A3S21A3SaR5R3A2F_;F_;Ff;Ffacts;Frho;").
Proof using .
  intros rho facts f HFa He. apply existsb_exists in He as (g & Hg & Hge). apply sprop_eqb_sound in Hge. subst g.
  exact (proj1 (Forall_forall _ _) HFa _ Hg).
Qed.

Lemma top_facts_T_ok : ltac2:(tb__ "0|1|
S7S1eS8A1S3fS8SaR2A1R1A3S0S20S51R2A1S21A3S1S60R4S31Q40SbR4S6aA2A2M0A2S1S41Z7fff7f800000G0A2S41G0Z7fffff800000A2A2A2F_;F_;Ffacts;Frho;").
Proof using .
  intros rho facts HF H. apply andb_prop in H as [H1 H2].
  pose proof (holds_of_existsb0 rho facts _ HF H1) as L. pose proof (holds_of_existsb0 rho facts _ HF H2) as U.
  cbn [holds eval F_top_lo F_top_hi] in L, U. rewrite Z_to_bv_small in L by (rewrite two64; lia). rewrite Z_to_bv_small in U by (rewrite two64; lia).
  split; [|lia]. split; [reflexivity | lia].
Qed.

Definition robjs_missT (facts : list sprop) (tv : list (sv * sv)) (lo hi : Z) (objs : list sobj) : bool := ltac2:(tb__ "0|1|
S23S23S23S23S23S44S75VC;A1Vlo;A2S44Vhi;S74VC;A1A2A2S44Z0Vlo;A2A2S44Vhi;S61A2A2S51Vfacts;A1A2S58SfSfS20S20L_;M0S63Vfacts;R1A2S21G0S7bVlo;Vhi;R1A3S21S64Vtv;S2cS25A1R1A3X20x2X20x2Lo;Vobjs;A3A2").

Definition tv_geo (rho : valuation) (tv : list (sv * sv)) : Prop := ltac2:(tb__ "0|6|
S1fS6S6A2M0S59G0R1Vtv;A3S1S0S2eS31Q40M1SdVrho;S27S6S6R2A3A2A2Z0M2A3M3S0S2eS31G1SdVrho;S28S6S6R3A3A2A2G2A3F_;S3G3A1S5S41S42S42S27S2eS2eS5dVrho;R3A2M4A3M5S28S2eS2eG4A3A2S80A2S75VC;A1A2S41S42S74VC;A1S81A2G5A2A2F_;A2F_;Ft;").

Lemma tv_geo_of_JGi : ltac2:(tb__ "0|0|
S1eS1fS6S6A2A1S3cS7S1eS38A1S37S5cVsegs;VC;VNP;VKc;Vrho0;VP0f;S26S1fS2eS2eA2A1R5R4R3R2R1AcS4fR4R6A2F_;Fmd;Ftr;Frho;FAi;Ftv;").
Proof using .
  intros tv Ai rho tr md (Hav & Hk & [HM _] & HP & (HN & HD & HZ) & HKF & HP0) t Ht. split.
  - intros Hz. exact (proj1 (Forall_forall _ _) HZ t Ht (fun H => H Hz)).
  - intros Hnz. destruct (proj1 (Forall_forall _ _) HN t Ht Hnz) as (Tpos & Tin & _).
    unfold MInvR in HM. rewrite (surjective_pairing (tvv rho t)) in Tin.
    pose proof (minv_block_geom C Ai _ _ _ _ _ HM Tin) as (G0 & _ & G2 & G3 & G4). exact G4.
Qed.

Lemma tv_geo_set_rl : ltac2:(tb__ "0|1|
S7S1eS1fS6S6A2M0A1S2fS1eS30Q8A1A1S0S20S58G0G0S23S29S68R3S27S6S6R1A3A2A1S29S68R3S28S6S6R1A3A2A1A2Lt;R3A3S21A3S4fR5R4A2S4fS69R6R4R3A3R5A2F_;F_;Fbs;Fl;Ftv;Frho;").
Proof using .
  intros rho tv l bs Hb HG t Ht. pose proof (proj1 (forallb_forall _ _) Hb t Ht) as Hbt. apply andb_prop in Hbt as [H1 H2].
  apply Bool.negb_true_iff in H1. apply Bool.negb_true_iff in H2.
  unfold tvv. rewrite !eval_set_rl by assumption. exact (HG t Ht).
Qed.
Lemma tv_geo_rw : ltac2:(tb__ "0|0|
S7S7S1eS1fS6S6A2A1S2fS0S30Q40A1SbR3R1A2SbR4R1A2A3Fi;S2fS0S1eS30Q8A1A1S10R4R1A2S10R5R1A2A3Fl;S4fR5R3A2S4fR5R4A2F_;F_;F_;Ftv;Frho';Frho;").
Proof using .
  intros rho rho' tv Hw Hl HG t Ht. unfold tvv.
  assert (E : forall e, eval rho' e = eval rho e).
  { intros e. symmetry. apply (eval_agree_vars (fun _ => true)); [intros v _; symmetry; apply Hw | intros l'; symmetry; apply Hl |].
    induction e; cbn; rewrite ?IHe1, ?IHe2, ?IHe; reflexivity. }
  rewrite !E. exact (HG t Ht).
Qed.

Lemma robjs_missT_sound : ltac2:(tb__ "0|0|
S1eS8A1S1eS1fS6S6A2A1S2eS2eS1eSfA1S7S4fR1R5A2S3fS8SaR2A1R7A3S0S20S50R8R7R6R5R4A5S21A3S3fSfSfS1cS1bR5R1A2S2aS2eS2eR8R7A4A2Lo;R5A3F_;F_;F_;Frho;Fobjs;Fhi;Flo;Ftv;Ffacts;").
Proof using P0f.
  intros facts tv lo hi objs rho HG HF H.
  unfold robjs_missT in H. apply andb_prop in H as [H Hall]. apply andb_prop in H as [H Htf]. apply andb_prop in H as [H Hhi]. apply andb_prop in H as [H Hlo0]. apply andb_prop in H as [Hlo Hhi'].
  apply Z.leb_le in Hlo. apply Z.leb_le in Hhi'. apply Z.leb_le in Hlo0. apply Z.leb_le in Hhi. unfold aceil in Hhi.
  destruct (top_facts_T_ok rho facts HF Htf) as [HT HTr].
  apply Forall_forall. intros o Ho. pose proof (proj1 (forallb_forall _ _) Hall o Ho) as Hc. cbn beta in Hc.
  apply lazy_orb_prop in Hc as [Hc|Hc].
  -
    unfold ranges_disjoint. cbn [fst snd].
    destruct (Z_lt_le_dec (fst (obj_range rho o)) (snd (obj_range rho o))) as [Hne|Hem]; [|lia].
    pose proof (robj_stack_sound facts rho _ o (fst (obj_range rho o)) HF HT Hc ltac:(lia)). lia.
  - apply lazy_orb_prop in Hc as [Hc|Hc].
    +
      unfold DrvPristine.robj_img_misses in Hc.
      destruct (ob_base o) as [b| | | | | | |] eqn:Eb; try discriminate.
      destruct (ob_lo o) as [olo| | | | | | |] eqn:El; try discriminate.
      destruct (ob_hi o) as [ohi| | | | | | |] eqn:Eh; try discriminate.
      apply andb_prop in Hc as [Hc Q6]. apply andb_prop in Hc as [Hc Q5]. apply andb_prop in Hc as [Hc Q4].
      apply andb_prop in Hc as [Hc Q3]. apply andb_prop in Hc as [Q1 Q2].
      apply Z.leb_le in Q1. apply Z.ltb_lt in Q2. apply Z.leb_le in Q3. apply Z.leb_le in Q4. apply Z.ltb_lt in Q5.
      unfold obj_range, obj_lo_of, obj_hi_of. rewrite Eb, El, Eh. cbn [fst snd eval].
      rewrite (Z_to_bv_small 64 b) by (rewrite two64; lia).
      unfold ranges_disjoint. cbn [fst snd].
      rewrite !soff_lit_small by lia. rewrite !Bool.orb_true_iff in Q6. rewrite !Z.leb_le in Q6. lia.
    +
      destruct (robj_tracked_sound tv None o Hc) as (j & t & Hj & _ & Hb & Hl & Hh).
      rewrite (surjective_pairing (obj_range rho o)). apply ranges_disjoint_by_points. intros a Ha1 Ha2.
      destruct (tracked_range rho o t a Hb Hl Hh Ha1) as [Hr Hpos].
      destruct (HG t (nth_error_In _ _ Hj)) as [Gz Gnz].
      assert (Hnz : bv_unsigned (eval rho (fst t)) <> 0).
      { intros Hz. unfold tvv in Hpos. cbn [snd] in Hpos. pose proof (Gz Hz). lia. }
      pose proof (Gnz Hnz) as G4. unfold IB, UNIT in *. lia.
Qed.

Definition robjs_missT_statics (facts : list sprop) (tv : list (sv * sv)) (objs : list sobj) : bool := ltac2:(tb__ "0|4|
S23S23S50Vfacts;Vtv;S7cVC;A1M0S42G0Z8M1A2Vobjs;A5S50Vfacts;Vtv;S7dVC;A1M2S42G2G1A2Vobjs;A5A2S50Vfacts;Vtv;S7eVC;A1M3S42G3Z1A2Vobjs;A5A2").

Lemma robjs_missT_statics_sound : ltac2:(tb__ "0|0|
S1eS8A1S1eS1fS6S6A2A1S1eSfA1S7S4fR1R3A2S3fS8SaR2A1R5A3S0S20S54R6R5R4A3S21A3S7fVC;R4R5A3F_;F_;F_;Frho;Fobjs;Ftv;Ffacts;").
Proof using P0f.
  intros facts tv objs rho HG HF H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  split; [|split]; eapply robjs_missT_sound; eauto.
Qed.
End Tracked.

Section Bracket.
Variable C : mconsts.
Variable NP : positive.
Variable P0f : valuation -> Prop.
Hypothesis ML : malloc_laws segs C.

Definition tv_eval_eq (rho rho' : valuation) (tv : list (sv * sv)) : Prop := ltac2:(tb__ "0|4|
S1fS6S6A2M0S59G0R1Vtv;A3S1S0S30Q40A1M1SdVrho';S27S6S6R2A3M2A2SdVrho;G2A2A3S0G1SdVrho';S28S6S6R2A3M3A2SdVrho;G3A2A3A2F_;Ft;").

Lemma tv_eval_eq_agree : ltac2:(tb__ "0|0|
S2fS7S7S1eS1fS6S6A2A1S7aR4R3R2A3S0S20S5fR5R2A2S21A3S4dR5R4R3A3F_;F_;Ftv;Frho';Frho;Fn;").
Proof using .
  intros n rho rho' tv Hav Hb t Ht. pose proof (proj1 (forallb_forall _ _) Hb t Ht) as Hbt. apply andb_prop in Hbt as [H1 H2].
  split; symmetry; eapply eval_agree_vals; eauto.
Qed.
Lemma tv_eval_eq_set_rl : ltac2:(tb__ "0|1|
S7S1eS1fS6S6A2M0A1S2fS1eS30Q8A1A1S0S20S58G0G0S23S29S68R3S27S6S6R1A3A2A1S29S68R3S28S6S6R1A3A2A1A2Lt;R3A3S21A3S4dR5S69R5R3R2A3R4A3F_;Fbs;Fl;Ftv;Frho;").
Proof using .
  intros rho tv l bs Hb t Ht. pose proof (proj1 (forallb_forall _ _) Hb t Ht) as Hbt. apply andb_prop in Hbt as [H1 H2].
  apply Bool.negb_true_iff in H1. apply Bool.negb_true_iff in H2. split; apply eval_set_rl; assumption.
Qed.
Lemma tv_eval_eq_set_rm : ltac2:(tb__ "0|0|
S7S1eS1fS6S6A2A1S30Q40A1S22S30Q8A1A1F_;S4dR3S73R3R1A2R2A3Fm;Ftv;Frho;").
Proof using . intros rho tv m t Ht. split; apply eval_set_rm. Qed.
Lemma tv_eval_eq_trans : ltac2:(tb__ "0|0|
S7S7S7S1eS1fS6S6A2A1S4dR4R3R1A3S4dR4R3R2A3S4dR6R4R3A3F_;F_;Ftv;Fr3;Fr2;Fr1;").
Proof using . intros r1 r2 r3 tv A B t Ht. destruct (A t Ht) as [A1 A2]. destruct (B t Ht) as [B1 B2]. split; congruence. Qed.

Lemma tv_eval_eq_facts : ltac2:(tb__ "0|4|
S7S7S1eS1fS6S6A2M0A1S4dR3R2R1A3S1S0S1eS1fS2eS2eA2M1A1S40G0G1S5dR3A1R2A4S40G0G1S5dR4A1R2A4A3S25G0G0S0S22G0A1M2S5bG0R5R3A3S24G0R2A2M3A3S0G2S5bG0R6R4A3G3A3S4S5eR8R3A2S5eR9R4A2A2F_;F_;Ft';Ft;Fk;A2F_;Ftv;Frho';Frho;").
Proof using P0f.
  intros rho rho' tv HE. split.
  - apply map_ext_in. intros t Ht. destruct (HE t Ht) as [E1 E2]. unfold tvv. rewrite E1, E2. reflexivity.
  - intros k t t' H1 H2. rewrite H1 in H2. injection H2 as <-. destruct (HE t (nth_error_In _ _ H1)) as [E1 _]. unfold tnz. rewrite E1. tauto.
Qed.

Variable wtop : word.
Hypothesis P0f_top : ltac2:(tb__ "0|0|
S7VP0f;R1A1S0S30Q40A1SbR2S6aA2Vwtop;A3F_;Fr;").

Definition snapJ (tv : list (sv * sv)) (D : MA -> Model -> Prop) (rho : valuation) (vm : VmMaps) (mat : list word) : Prop := ltac2:(tb__ "0|2|
S2S3cS3cS2S37S37S1S3dVC;R2S6bVsegs;SeVrho;A1M0A2S6cVsegs;G0A2Vvm;A5S1S1S62R2A1S0S2eS76S3eR2A1A1S31Q40M1Vwtop;A2A3A2S1S1S66S26S1fS2eS2eA2A1R2Vrho;Vtv;A4S1S65Vrho;Vtv;A2S67Vrho;Vtv;A2A2A2S1VP0f;Vrho;A1S1S0S39S3aR1A1Vvm;A3S1S0S1eS30G1A1A1S3bR1A1Vmat;A3VD;R2R1A2A2A2A2A2A2A2Lmd;A2LAi;A2").

Lemma deJ : ltac2:(tb__ "0|1|
S1eS38A1M0S37OF_;F_;S7S1eS1fS6S6A2A1S3cS37OFx0;Fx;S3cS7G0S37S5cVsegs;VC;VNP;R8R7VP0f;S26S1fS2eS2eA2A1R6R4R3R2R1AcR6R5R2A2VP0f;R5A1S1S4eR9R8R6S3aR4A1S3bR4A1A5RbR5R4A2A2F_;F_;F_;Fmd;Ftr;Frho;FAi;FD;Ftv;Frho0;FKc;").
Proof using P0f_top.
  intros Kc rho0 tv D Ai rho tr md (Hav & Hk & [HM [Hi HT]] & HP & HN & HKF & HP0) HD HPr.
  split; [|exact Hk]. exists Ai, md. unfold MInvR in HM. split; [exact HM|].
  split; [split; [exact Hi|]; rewrite (TPI_top _ _ _ HT); unfold T0; rewrite (P0f_top _ HP0); reflexivity|].
  split; [exact HN|]. split; [exact HPr|].
  split; [reflexivity|]. split; [reflexivity|exact HD].
Qed.

Lemma snapJ_transport : ltac2:(tb__ "0|2|
S1eS1fS6S6A2A1S3cS37OF_;F_;S7S7S39S1eS30Q40A1M0A1S4eR6R5R4R2R1A5S4dR5R4R7A3G0S0S22S30Q8A1A1S6bVsegs;SeR6A1R1A3S6bVsegs;SeR7A1M1R1A3A3Fa;G0S0S20S6cVsegs;G1R1A3S6cVsegs;SeR8A1R1A3A3Fa;VP0f;R7A1S4eRbRaR8R7R6A5F_;F_;F_;F_;F_;Fmat;Fvm;Frho';Frho;FD;Ftv;").
Proof using ML.
  intros tv D rho rho' vm mat (Ai & md & HM & [Hi HT] & (HN & HD & HZ) & HP0 & Hvm & Hmat & HDD) HE Hrd Hwok HP0'.
  destruct (tv_eval_eq_facts rho rho' tv HE) as [M1 M2].
  exists Ai, md. split.
  { eapply (ml_frame segs C ML); [exact HM| |reflexivity|reflexivity|reflexivity|reflexivity|reflexivity|reflexivity|exact Hi].
    intros a _ _. rewrite <- (Z_to_bv_bv_unsigned 64 (Z_to_bv 64 a)). split; [apply Hrd | apply Hwok]. }
  split; [split; [exact Hi | exact HT]|]. split; [split; [|split]|].
  - eapply tvin_map; eauto.
  - eapply tvd_map; eauto.
  - eapply tvz_map; eauto.
  - split; [exact HP0'|]. split; [exact Hvm|]. split; [exact Hmat | exact HDD].
Qed.

Hypothesis P0f_tp : ltac2:(tb__ "0|0|
S7VP0f;R1A1S6dVC;R2A2F_;Fr;").

Lemma reJ : ltac2:(tb__ "0|4|
S1eS38A1M0S37OFx0;Fx;S1eS1fS6S6A2A1S3cS37OF_;F_;S7S39S1eS30Q40A1A1M1G0S37S4eR7R6R5R4R3A5S0S39S3aR2A1M2R5A3S0G1S3bR3A1M3R5A3S3cS37S37S0S39S3aR1A1G2A3S0G1S3bR2A1G3A3ReR5R4A2RfR6R4A2F_;F_;F_;Fm';Fm;FA;RcR6R5A2S2S3cS3cS1S5cVsegs;VC;VNP;ReRbVP0f;S26S1fS2eS2eA2A1RdR1RbR8R7AcRcR1R7A2A2LAi;A2F_;F_;F_;F_;F_;Fmd;Ftr;Fmat;Fvm;Frho;FD;Ftv;FKc';").
Proof using P0f_tp P0f_top.
  intros Kc' tv D rho vm mat tr md (Ai & md0 & HM & [Hi HT] & HN & HP0 & Hvm & Hmat & HDD) Hvm' Hmat' HDf Hk.
  exists Ai. split; [|apply (HDf Ai md0 md); [congruence|congruence|exact HDD]].
  split; [apply agree_vals_refl|]. split; [exact Hk|].
  split; [split; [|split; [exact Hi | split; [exact (P0f_tp _ HP0) | unfold T0; rewrite (P0f_top _ HP0); exact HT]]]|].
  - unfold MInvR. rewrite Hvm'. exact HM.
  - split; [intros b Hb; destruct Hb|]. split; [exact HN|]. split; [intros a _ _; reflexivity | exact HP0].
Qed.
End Bracket.

End WithSegs.

Definition CAP (cap : Z) : Prop := ltac2:(tb__ "0|1|
S1S2S25S25S0S2eVcap;S46Z10000S43Z2M0S48R1A1A2A2A3Lg;A2S41Vcap;S43G0Z1aA2A2A2").

Definition ALIGNED (x : Z) : Prop := x mod 65536 = 0.
Lemma CAP_facts : ltac2:(tb__ "0|2|
S2eS6fR1A1S1S1S41Z10000R2A2S41R2S43Z2M0Z1aA2M1A2A2S1S70R2A1S45R2G1A2S41S46G0R3A2G1A2F_;A2A2F_;Fcap;").
Proof.
  intros cap [[g ->] Hle]. pose proof (Z.pow_pos_nonneg 2 (Z.of_nat g) ltac:(lia) ltac:(lia)) as P.
  split; [lia|]. split; [unfold ALIGNED; rewrite Z.mul_comm, Z.mod_mul; lia|].
  intros Hlt. change (2 ^ 26) with (65536 * 2 ^ 10) in *.
  assert (2 ^ Z.of_nat g < 2 ^ 10) by nia.
  apply Z.pow_lt_mono_r_iff in H; [|lia|lia].
  assert (2 * 2 ^ Z.of_nat g = 2 ^ (Z.of_nat g + 1)) by (rewrite Z.pow_add_r by lia; lia).
  assert (2 ^ (Z.of_nat g + 1) <= 2 ^ 10) by (apply Z.pow_le_mono_r; lia). nia.
Qed.
Lemma CAP_double : ltac2:(tb__ "0|1|
S2eS6fR1A1S45R2S43Z2M0Z1aA2A2S6fS46G0R3A2A1F_;F_;Fcap;").
Proof.
  intros cap HC Hlt. pose proof (CAP_facts cap HC) as (A & B & Cc). destruct HC as [[g ->] _].
  split; [|lia]. exists (S g). rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.
Lemma CAP_init : CAP 65536.
Proof. split; [exists 0%nat; reflexivity | lia]. Qed.

