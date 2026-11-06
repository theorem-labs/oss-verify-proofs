(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "SLit"; "ob_dflt"; "ob_hi"; "ob_lo"; "smatch"; "ss_objs"; "sstate"; "sv"; "DList"; "cell"; "dflt_writable"; "is_arr"; "mkObj"; "ob_base"; "ob_cells"; "valuation"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "option"; "bool"; "Some"; "false"; "list"; "S"; "app"; "cons"; "nat"; "nil"; "prod"; "true"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes"; "bexp"; "beval"; "cells_bytes"; "@Stdlib.Lists.List"; "nth_error"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "opp"; "pow"; "sub"; "to_nat"; "@Corelib.Lists.ListDef"; "firstn"; "map"; "skipn"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rl"; "state_has_rl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj"; "obj_to_list"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR SymObj SymCall SymBytes Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition obj_to_list (S : sstate) (i : nat) (l : positive) : sstate := ltac2:(tb__ "0|1|
S13S0A1S7Lx;S24S0S6VS;A1M0Vi;A3S0S32VS;S19S0S2bS0Vi;G0A3S1aS0SdSeR1A1S4R1A1S3R1A1S1cSaA1S9Vl;A1A5S2dS0S18Vi;A1G0A3A3A3A2Lo;VS;X13x2").

Section L.
Variable segs : list Segment.

Lemma Forall_nth_error : forall {A} (P : A -> Prop) l i x, Forall P l -> nth_error l i = Some x -> P x.
Proof using . intros A P l i x H Hn. exact (proj1 (Forall_forall _ _) H x (nth_error_In _ _ Hn)). Qed.

Theorem smatch_obj_to_list : ltac2:(tb__ "0|3|
S10S7S1dS17S2fA1S2eA2S1bS20S0S1fS1fS17S21A1M0S5Vsegs;R9R8R7A4S11S13S0A1S24S0S6R9A1R7A3S15S0R5A2A3S11S8S4R6A1S1R5A1M1A3S11S8S3R7A1G1A3S25S27S28Z2Z3eA2M2A1R7A2S12S25R8R7A2S26R7G2A2A2S11S14SbS2RaA1A1S1eA3S11S14ScS2RbA1A1S16A3S11S13G0A1S23SfRcA1S1RbA1Z0S2aS29RaRbA2A1A4S15G0R9A2A3S11S14S31ReR11A2S16A3S5Vsegs;S30R13RfS2cS21S34Q8A1S22R13A1RbA4A3S33R12R10RfA3R11A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fbl;Fhi;Flo;Fo;Fl;Fi;Fw;FS;Frho;").
Proof using .
  intros rho S [tr [ms md]] i l o lo hi bl Hsm Hn Hlo Hhi Hb0 Hb Hwr Harr Hcb Hrl.
  set (rho' := rho_set_rl rho l (map (beval rho) bl)).
  assert (Hsm' : smatch segs rho' S (tr, mkCfg ms md)) by (apply smatch_set_rl; assumption).
  pose proof (smatch_swf segs _ _ _ Hsm) as Hwf.
  pose proof Hsm' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmm & _). cbn [fst snd cfg_ms cfg_model] in Hmm.
  destruct Hmm as (Hall & Hpd & Hfr).
  pose proof (Forall_nth_error _ _ _ _ Hall Hn) as Ho.
  pose proof (swf_obj_nth S i o Hwf Hn) as Howf.
  unfold obj_to_list. rewrite Hn.
  pose proof (nth_error_split3 (ss_objs S) i o Hn) as Esplit.
  set (o' := mkObj (ob_base o) (ob_lo o) (ob_hi o) [] (DList l)).
  assert (Hrange : obj_range rho' o' = obj_range rho' o) by reflexivity.
  assert (Ho' : obj_holds segs rho' ms o').
  { pose proof Ho as (Hbnd & Hw & Hc & Hd & Hinv). unfold obj_holds. subst o'. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt].
    unfold obj_lo_of, obj_hi_of in *. cbn [ob_lo ob_hi]. rewrite Hlo, Hhi in *. rewrite !soff_lit_small in * by lia.
    split; [exact Hbnd|]. split; [intros off Hoff _; apply Hw; [exact Hoff | exact Hwr]|]. split; [constructor|]. split.
    - intros off Hoff _. cbn [dflt_holds]. subst rho'. cbn [rl rho_set_rl]. rewrite Pos.eqb_refl.

      destruct (smatch_mm segs rho S tr ms md Hsm) as (Hall0 & _ & _).
      pose proof (Forall_nth_error _ _ _ _ Hall0 Hn) as Ho0.
      pose proof Ho0 as (Hbnd0 & _). unfold obj_lo_of, obj_hi_of in Hbnd0. rewrite Hlo, Hhi in Hbnd0. rewrite !soff_lit_small in Hbnd0 by lia.
      pose proof (cells_bytes_sound segs rho ms o (ss_next S) (SLit lo) 0 (Z.to_nat (hi - lo)) bl Ho0 Howf) as X.
      unfold obj_lo_of, obj_hi_of in X. rewrite Hlo, Hhi in X. rewrite !soff_lit_small in X by lia.
      specialize (X ltac:(lia) Hcb).
      assert (Eb : eval (rho_set_rl rho l (map (beval rho) bl)) (ob_base o) = eval rho (ob_base o)).
      { apply eval_set_rl. unfold state_has_rl in Hrl. repeat (apply Bool.orb_false_iff in Hrl as [Hrl ?]).
        pose proof (existsb_false_forall (obj_has_rl l) (ss_objs S) o H0 (nth_error_In _ _ Hn)) as Hor.
        unfold obj_has_rl in Hor. repeat (apply Bool.orb_false_iff in Hor as [Hor ?]). exact Hor. }
      rewrite Eb.
      pose proof (rd_bytes_nth ms (Z.to_nat (hi - lo)) (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o)) + lo + 0)) _ (Z.to_nat (off - lo)) X ltac:(lia)) as Y.
      rewrite Z_to_bv_small in Y by (change (bv_modulus 64%N) with (2 ^ 64); lia).
      specialize (Y ltac:(lia)).
      replace (bv_unsigned (eval rho (ob_base o)) + lo + 0 + Z.of_nat (Z.to_nat (off - lo))) with (bv_unsigned (eval rho (ob_base o)) + off) in Y by lia.
      exact Y.
    - cbn [dflt_inv]. subst rho'. cbn [rl rho_set_rl]. rewrite Pos.eqb_refl, length_map, (cells_bytes_length _ _ _ _ _ Hcb). lia. }
  unfold set_objs.
  apply (smatch_set_objs_next segs rho' S (tr, mkCfg ms md) _ (ss_next S) (ss_lenient S) Hsm').
  - cbn [snd cfg_ms]. rewrite Esplit in Hall, Hpd, Hfr. split; [|split].
    + apply Forall_app in Hall as [H1 H2]. apply Forall_cons_iff in H2 as [_ H3]. apply Forall_app. split; [exact H1|]. constructor; assumption.
    + eapply pairwise_disjoint_pdr. apply pairwise_disjoint_pdr in Hpd. rewrite map_app in *. cbn [map] in *. rewrite Hrange. exact Hpd.
    + intros a Ha. apply Hfr. unfold outside_all in *. rewrite Forall_app in *. destruct Ha as [Ha1 Ha2]. apply Forall_cons_iff in Ha2 as [Ha2 Ha3].
      split; [exact Ha1|]. constructor; [rewrite <- Hrange; exact Ha2 | exact Ha3].
  - pose proof (smatch_swf segs _ _ _ Hsm') as W. unfold swf in W |- *. cbn [ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next].
    repeat (apply andb_prop in W; destruct W as [W ?]). repeat (apply andb_true_intro; split); try assumption.
    rewrite Esplit in H0. rewrite forallb_app in H0 |- *. apply andb_prop in H0 as [F1 F2]. cbn [forallb] in F2 |- *. apply andb_prop in F2 as [F2 F3].
    rewrite F1, F3. cbn [andb]. rewrite Bool.andb_true_r.
    unfold obj_wf in Howf |- *. subst o'. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt].
    repeat (apply andb_prop in Howf; destruct Howf as [Howf ?]). rewrite Hlo, Hhi in *.
    repeat (apply andb_true_intro; split); try assumption; try reflexivity.
Qed.
End L.
