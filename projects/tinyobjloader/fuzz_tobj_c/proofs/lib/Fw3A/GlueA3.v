(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "pow"; "opp"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "SLit"; "ss_objs"; "DUnknown"; "cell"; "eval"; "image_byte"; "mkObj"; "obj_range"; "ranges_disjoint"; "ss_next"; "sv"; "sv_below"; "valuation"; "@Corelib.Init.Datatypes"; "pair"; "list"; "nil"; "None"; "app"; "bool"; "cons"; "option"; "true"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "axst"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "xword"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "wview"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA3.G3"; "unknown_obj"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundW SymSoundF SymSoundR SymFrame SymEntail SymCFG SymCall Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA LedgerA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.

Section G3.
Variable segs : list Segment.

Definition unknown_obj (eb : sv) (lo hi : Z) : sobj := ltac2:(tb__ "0|0|
SdVeb;S7Vlo;A1S7Vhi;A1S16SaA1S9A5").

Lemma SPA_carve_unknown_w : ltac2:(tb__ "0|b|
S26S13S22S11S5S5S15S28Q40M0A1M1A1S15S2fA1M2S2cS2eS25Vsegs;RaR8R9R4S14G2S23R3S24R2R1A2A4A6S29G0SbRaR8A2A2S5S1eS19S12S10S20RaA1A1R9A2S1cA3S1S4S3Z2M3Z3eA2M4A1R9A2S1RaR9A2S2RaG4A2S1Z0S0R5RcA2A2S1S0R6RcA2S3G3Z40A2A2S5S1dS1RfR1A2S2R1ReA2A2S1dS1fS1eS1bS28Q8A1M5A1M6S2dVsegs;G1S17G5A1M7L_;S2aG0S0R9R2A2A2M8A3G7A3A1S1fS1eG6ScVsegs;G8A2G7A3A1A2F_;Foff;S2bS6S6SfSeR13R1A2S14S5S5S0R9R10A2S0R9RfA2A4A2Lo;S8S20R11A1A1A3G1S27R14R13R1A3S1fS1dS1S0RbR12A2S29G0R2A2M9A2S2G9S0RbR11A2A2A2A1F_;Fx;S25Vsegs;R15S21R13S30S20R13A1MaS18S6S8GaA1S1aS6S31R12R11R10A3S16S6A1A3A3A2A2R14RfS14G2S23ReS24RdRcA2A4A6F_;F_;F_;F_;F_;F_;F_;F_;F_;Tb;F_;Fmd;Fms;Ftr;Ftp;Fhi;Flo;Feb;FA;Frho;FJ;").
Proof using .
  intros J rho A eb lo hi tp tr ms md [(Hsm & HMI & Hwf & Hsh & Hhz) Hk] b Hbel Hlo Hlh Hhi Hb0 Hb64 Himg Hdisj Hxw.
  pose proof (urange (eval rho eb)) as Rb. fold b in Rb.
  unfold virt in Hsm. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm.
  destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & (Hall & Hpd & Hfr) & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in Hswf, Hpc, Hpend, Hhalt, Hrom, Hroc, Hregs, Hfregs, Hfcsr, Hresv, Hall, Hpd, Hfr, Hfacts.
  assert (Hslo : soff rho (SLit lo) = lo) by (apply soff_lit_small; lia).
  assert (Hshi : soff rho (SLit hi) = hi) by (apply soff_lit_small; lia).
  assert (Hzr : obj_range rho (unknown_obj eb lo hi) = (b + lo, b + hi)).
  { unfold obj_range, obj_lo_of, obj_hi_of, unknown_obj. cbn [ob_base ob_lo ob_hi]. rewrite Hslo, Hshi. reflexivity. }
  split; [|exact Hk]. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in HMI, Hhz |- *.
  unfold smatchA. cbn [ax_S ax_setS fst snd cfg_ms cfg_model w_tr w_cfg].
  split; [|split; [exact HMI | split; [unfold axwf in Hwf |- *; cbn [ax_S ax_X ax_base ax_setS ss_next set_objs] in Hwf |- *; exact Hwf | split]]].
  - unfold virt, smatch. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ss_pc ss_regs ss_fregs ss_next ss_fcsr ss_resv ss_objs ss_facts set_objs].
    split.
    { unfold swf in Hswf |- *. cbn [ss_regs ss_fregs ss_next ss_fcsr ss_resv ss_objs ss_facts set_objs].
      rewrite forallb_app. cbn [forallb].
      assert (Ho : obj_wf (ss_next (ax_S A)) (unknown_obj eb lo hi) = true).
      { unfold obj_wf, unknown_obj. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt forallb]. rewrite Hbel. reflexivity. }
      rewrite Ho, andb_true_r. exact Hswf. }
    split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hroc|].
    split; [exact Hregs|]. split; [exact Hfregs|]. split; [exact Hfcsr|]. split; [exact Hresv|].
    split; [|exact Hfacts].
    split; [|split].
    + cbn [ss_objs set_objs]. apply Forall_app. split; [exact Hall|].
      constructor; [|constructor]. unfold obj_holds. unfold obj_lo_of, obj_hi_of, unknown_obj.
      cbn [ob_base ob_lo ob_hi ob_cells ob_dflt dflt_writable]. rewrite Hslo, Hshi. fold b.
      split; [lia|]. split.
      { intros off Hoff _. destruct (Himg off Hoff) as [Hw _].
        eapply wview_mono; [|exact Hw]. intros y Hy. exfalso. apply Hy. reflexivity. }
      split; [constructor|]. split; [|exact I].
      intros off Hoff _. unfold dflt_holds, rd, ms_read_byte. destruct (Himg off Hoff) as [_ Hi].
      destruct (ms_mem (vms md tp ms) (Z_to_bv 64 (b + off))) as [v|]; [exists v; reflexivity|].
      rewrite (Hrom (Z_to_bv 64 (b + off))). destruct (image_byte segs (Z_to_bv 64 (b + off))) as [v|]; [exists v; reflexivity | exfalso; apply Hi; reflexivity].
    + cbn [ss_objs set_objs]. apply pairwise_disjoint_app1; [exact Hpd|].
      apply Forall_forall. intros o Ho. rewrite Hzr. exact (proj1 (Forall_forall _ _) Hdisj o Ho).
    + cbn [ss_objs set_objs]. intros a Hout. apply outside_all_app_iff in Hout as [Hout1 _]. exact (Hfr a Hout1).
  -
    apply shadow_ok_transport_objs; [|exact Hsh]. cbn [ax_X ax_base ax_S ax_setS ss_objs set_objs]. intros x Hx Hout _.
    apply outside_all_app_iff. split; [exact Hout|].
    constructor; [|constructor]. cbn zeta. rewrite Hzr. cbn [fst snd]. exact (Hxw x Hx).
  - exact Hhz.
Qed.

End G3.
