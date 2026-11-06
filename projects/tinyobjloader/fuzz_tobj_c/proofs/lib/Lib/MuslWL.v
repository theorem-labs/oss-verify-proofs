(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "bv_add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "eval"; "sstate"; "rw"; "sv"; "sprop"; "SLit"; "ss_next"; "SVar"; "holds"; "SPUle"; "reg_sv"; "cell"; "sobj"; "SAlu"; "agree_below"; "ss_facts"; "rl"; "sprop_below"; "obj_lo_of"; "ss_objs"; "sv_below"; "ob_cells"; "obj_holds"; "odefault"; "ob_base"; "ob_dflt"; "obj_hi_of"; "ss_lenient"; "mkCell"; "mkObj"; "rd_bytes"; "sv_eqb"; "tfact"; "@"; "segs"; "wl_fd"; "D"; "Pre_wl1"; "Pre_wl2"; "CB1"; "CB2"; "@Corelib.Init.Datatypes"; "list"; "nat"; "length"; "bool"; "true"; "Some"; "option"; "nil"; "pair"; "app"; "cons"; "prod"; "false"; "None"; "negb"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "of_nat"; "pow"; "lt"; "sub"; "to_nat"; "opp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "LQ"; "ok_frame"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "FdEntry"; "WriteEv"; "FdChannel"; "fd_lookup"; "m_fds"; "read_bytes_map"; "MAX_RW_COUNT"; "read_u64"; "@Corelib.Init.Peano"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL.WLProof.WL"; "Kw"; "G"; "MSG"; "chw"; "P_of"; "Posts_wl"; "QD"; "TRk"; "eQD"; "Q_wr"; "eQ_wr"; "@Corelib.Init.Nat"; "add"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "triple"; "etriple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "lf_state"; "add_fact"; "sym_run"; "RsCut"; "mkLeaf"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_read_byte"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "map"; "Forall"; "nth"; "seq"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "smatch_pending"; "ok_pframe"; "@Stdlib.PArith.BinPos.Pos"; "le"; "lt"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "rho_sub"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "S_after_write"; "obj_rng"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails"; "cell_eqb"; "dummy_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL"; "ob"; "sub_idb"; "site1"; "site2"; "dlist_of"; "@LinuxProcessSemantics.Riscv.Sem"; "alu64"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL.Generic"; "dlist_of"; "ob"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.SpecConsts"; "max_write_total"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj SymCall SymBytes SymExit Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue SysExtra.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec Require Import SpecConsts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section Generic.
Variable segs : list Segment.
Variable ok : world -> Prop.

Lemma LQ_elim : ltac2:(tb__ "0|0|
S33S4dA1S4eOF_;F_;S5SaS33S6aA1S69S6aSaS70S6aR2R4A3S19R7R6R2A3S67Vsegs;Vok;S4aVsegs;R9S6bR4A1R3A4R5A4F_;F_;Frho';FL;S67Vsegs;Vok;S4bVsegs;R6R5R4R3A5R2A4F_;FQ;Fleaves;Frho;Fn;FK;").
Proof using .
  intros K n rho leaves Q H. unfold LQ, LQJ.
  apply triple_ex; intros L. apply triple_ex; intros rho'.
  apply triple_pure; intros Hin. apply triple_pure; intros Hag.
  eapply triple_conseq; [| intros w Hw; exact Hw | exact (H L rho' Hin Hag)].
  intros w [Hsm Hk]. split; assumption.
Qed.

Lemma run_tr : ltac2:(tb__ "0|1|
S34S33S4A1ScS33S6aA1M0S33S4dA1S4eOF_;F_;SaS69S0S39G0A1S6dVsegs;R7R6R5S37A5S38G0R4A2A3S0S36S26R6A1S3fA3S4cVsegs;Vok;R5A3S6aSaS70S6aR2R9A3S19S11RbA1R8R2A3S67Vsegs;Vok;S4aVsegs;RaS6bR4A1R3A4R8A4F_;F_;Frho';FL;S67Vsegs;Vok;S4aVsegs;R7R9R6A4R5A4F_;F_;F_;F_;FQ;Frho;FK;Fleaves;FS;Fcuts;Ffuel;").
Proof using .
  intros fuel cuts S leaves K rho Q Hrun Hstrict Hok H.
  eapply triple_seq; [apply triple1_triple; eapply sym_run_sound; [exact Hrun | exact Hok | rewrite Hstrict; discriminate]|].
  apply LQ_elim. exact H.
Qed.

Lemma erun_tr : ltac2:(tb__ "0|1|
S34S33S4A1ScS33S6aA1M0S33S4dA1S4eOF_;F_;SaS66OF_;S0S39G0A1S6dVsegs;R7R6R5S37A5S38G0R4A2A3S0S36S26R6A1S3fA3S6aSaS70S6aR2R8A3S19S11RaA1R7R2A3S68Vsegs;S4aVsegs;R9S6bR4A1R3A4R7A3F_;F_;Frho';FL;S68Vsegs;S4aVsegs;R6R8R5A4R4A3F_;F_;F_;FQ;Frho;FK;Fleaves;FS;Fcuts;Ffuel;").
Proof using .
  intros fuel cuts S leaves K rho Q Hrun Hstrict H w Hsp.
  destruct (sym_run_complete segs fuel cuts S leaves K rho w Hstrict Hrun Hsp) as (L & rho' & w' & Hin & Hst & Hag & Hsp').
  destruct (H L rho' Hin Hag w' Hsp') as (w'' & Hst' & HQ).
  exists w''. split; [eapply wsteps_trans; eauto | exact HQ].
Qed.

Lemma SP_entails : ltac2:(tb__ "0|0|
S33S4dA1S4eOF_;F_;ScScS84SaS66S0S36S89R5R4R3A3S37A3S4aVsegs;R7R6R3R2A5S4aVsegs;R8R6S85R4R5A2R3A5F_;F_;Fw;Frho;Fs;FT;FL;FK;").
Proof using . intros K L T s rho w He [Hsm Hk]. split; [eapply entails_sound; eauto | exact Hk]. Qed.

Lemma SP_fact : ltac2:(tb__ "0|0|
S33S4dA1S4eOF_;F_;ScSaS66SfS4aVsegs;R5R4R3R2A5S70SfR2S1aR5A1A3S13R5R3A2F_;F_;Fp;Fw;Frho;FS;FK;").
Proof using . intros K S rho w p Hsp Hin. exact (proj1 (Forall_forall _ _) (SP_facts_hold segs K rho S w Hsp) p Hin). Qed.

Lemma SPp_fact : ltac2:(tb__ "0|1|
SaScS33S4dA1M0S73S4eSfS7fVsegs;R6R5S3bG0S7dR4S7eR3R2A2A4A4S70SfR2S1aR6A1A3S13R8R3A2F_;F_;Fp;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md p Hsp Hin. pose proof Hsp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF).
  exact (proj1 (Forall_forall _ _) HF p Hin).
Qed.

Lemma SPp_facts : ltac2:(tb__ "0|1|
SaScS33S4dA1M0S73S4eS7fVsegs;R5R4S3bG0S7dR3S7eR2R1A2A4A4S7aSfS13R6A1S1aR5A1A3F_;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md Hsp. pose proof Hsp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF). exact HF.
Qed.

Lemma hd_fact : ltac2:(tb__ "0|1|
SaScSfS33SfA1M0S66S33S4dA1S4eOF_;F_;S0G0S1aR5A1S3dSfR4R3A3A3S4aVsegs;R2R6R7R3A5S13R8R6A2F_;F_;FK;Fw;FF;Ff;FS;Frho;").
Proof using . intros rho S f F w K E Hsp. eapply SP_fact; [exact Hsp|]. rewrite E. left. reflexivity. Qed.

Lemma SP_add1 : ltac2:(tb__ "0|0|
S33S4dA1S4eOF_;F_;ScSaS66SfS4aVsegs;R5R4R3R2A5S13R4R2A2S0S36S1cS11R6A1R3A2S37A3S4aVsegs;R8S6cR7R4A2R6R5A5F_;F_;F_;Ff;Fw;Frho;FS;FK;").
Proof using .
  intros K S rho w f [Hsm Hk] Hf Hb. split; [|exact Hk]. apply smatch_add_fact; [exact Hsm | exact Hb | exact Hf].
Qed.

Lemma SP_addn : ltac2:(tb__ "0|0|
S33S4dA1S4eOF_;F_;ScSaS66S33SfA1S4aVsegs;R5R4R3R2A5S7aSfS13R4A1R2A3S0S36S71SfS1cS11R6A1A1R3A3S37A3S4aVsegs;R8S94R4R7A2R6R5A5F_;F_;F_;FF;Fw;Frho;FS;FK;").
Proof using .
  intros K S rho w F [Hsm Hk] Hf Hb. split; [|exact Hk]. apply smatch_add_facts; [exact Hsm | exact Hf | exact Hb].
Qed.

Definition ob (S : sstate) (i : nat) : sobj := ltac2:(tb__ "0|0|
S7bS17Vi;S1eVS;A1S8bA4").

Definition dlist_of (d : odefault) : option positive := ltac2:(tb__ "0|2|
S22S39S5A1Ld;Vd;S40S5A1M0G0G0S5S38S5R1A2Ll;M1G1S4SeS33S3eS4S4A2A1S33S2bA1G0Ltmpl;Lflds;Lcnt;Lesz;X22x6").

Lemma listish_obj_rd_bytes : ltac2:(tb__ "0|3|
SaS73S17S5S34S4S21Vsegs;R6R5R4A4S0S39S5A1S92S24R5A1A1S38S5R4A2A3S0S33S16A1S20R6A1S3aS16A1A3S42S1dR9R7A2R4A2S42S43R5S44R6A1A2S25RaR8A2A2S0S39S33S7Q8A1M0A1M1A1S29RaS8Q40M2S43S6G2SbRbS23R9A1A2A2R6A2A2R7A3S38G1S77G0R7S78G0S48S47R6S1dRbR9A2A2A1S1bRbR8A2A3A3A2A3F_;F_;F_;F_;F_;Foff;Fn;Fl;Fo;Fms;Frho;").
Proof using .
  intros rho ms o l n. induction n as [|n IH]; intros off Ho Hd Hc Hlo Hhi.
  - reflexivity.
  - cbn [rd_bytes]. pose proof Ho as (Hbnd & _ & _ & Hdf & Hinv).
    assert (Hnc : forall q, ~ covered rho (ob_cells o) q) by (intros q HC; rewrite Hc in HC; inversion HC).
    assert (Hdf' : rd ms (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o)) + off))
                   = Some (nth (Z.to_nat (off - obj_lo_of rho o)) (rl rho l) (Z_to_bv 8 0))
            /\ Z.of_nat (length (rl rho l)) = obj_hi_of rho o - obj_lo_of rho o).
    { destruct (ob_dflt o); cbn [dlist_of] in Hd; try discriminate; injection Hd as ->;
        cbn [dflt_holds dflt_inv] in Hdf, Hinv; (split; [exact (Hdf off ltac:(lia) (Hnc off)) | exact Hinv]). }
    destruct Hdf' as [R Hlen]. rewrite R.
    replace (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o)) + off) + 1)%bv
      with (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o)) + (off + 1))).
    2:{ apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
        change (bv_unsigned (1%bv : bv 64)) with 1. rewrite Zplus_mod_idemp_l. f_equal. lia. }
    rewrite (IH (off + 1) Ho Hd Hc ltac:(lia) ltac:(lia)).
    f_equal.
    replace (Z.to_nat (off + 1 - obj_lo_of rho o)) with (S (Z.to_nat (off - obj_lo_of rho o))) by lia.
    rewrite <- (firstn_cons n). f_equal.
    destruct (Nat.lt_ge_cases (Z.to_nat (off - obj_lo_of rho o)) (length (rl rho l))) as [Hlt|Hge].
    + apply nth_skipn_cons. exact Hlt.
    + exfalso. lia.
Qed.

Lemma listish_obj_read_bytes_map : ltac2:(tb__ "0|5|
SaS73S17S5S34S4S7Q40M0A1M1G1S21Vsegs;R8R7R6A4S0S39S5A1S92S24R7A1A1S38S5R6A2A3S0S33S16A1S20R8A1S3aS16A1A3S42S1dRbR9A2R6A2S42S43R7S44R8A1A2S25RcRaA2A2S0S4S6G0R7A2M2S43S6G0SbRdS23RbA1A2A2R8A2A3S0S4G2S44RaA1A3S0S39S33S7Q8A1M3A1M4A1S54S74ReA1R9R8A3S38G4S77G3RbS78G3S48S47RaS1dRfRdA2A2A1S1bRfRcA2A3A3A2A3F_;F_;F_;F_;F_;F_;F_;Flen;Fa;Foff;Fn;Fl;Fo;Fms;Frho;").
Proof using .
  intros rho ms o l n off a len Ho Hd Hc Hlo Hhi Ha Hlen.
  rewrite read_bytes_map_eq; unfold word_to_nat. rewrite rd_bytes_read_aux, Hlen, Nat2Z.id.
  replace a with (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o)) + off)) by (rewrite <- Ha; apply Z_to_bv_bv_unsigned).
  apply listish_obj_rd_bytes; auto.
Qed.

Lemma objs_hold : ltac2:(tb__ "0|1|
SaScS33S4dA1M0S73S4eS34S7fVsegs;R6R5S3bG0S7dR4S7eR3R2A2A4A4S58R2S35S17S1eR6A1A2A2S21Vsegs;R8R5S93R7R3A2A4F_;F_;Fi;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md i Hsp Hi. destruct (smatch_pending_mem segs _ _ _ _ _ Hsp) as (Hall & _ & _).
  unfold ob. exact (proj1 (Forall_forall _ _) Hall _ (nth_In _ dummy_obj Hi)).
Qed.
End Generic.

Lemma U_lit64 : ltac2:(tb__ "0|0|
SaS4S1S42Z0R1A2S46R1S45Z2Z40A2A2A2S0S4S6Q40SbR3S10R2A1A2A2R2A3F_;Fz;Frho;").
Proof. intros rho z Hz. cbn. apply Z_to_bv_small. rewrite two64. exact Hz. Qed.

Lemma U_addc : ltac2:(tb__ "0|3|
SaSeS4S4S0S4S6Q40M0SbR4R3A2A2R1A3S1S42Z0S43R2R3A2M1A2S46G1S45Z2Z40A2M2A2A2S1S46S49G2A1R4A2S46R4G2A2A2S0S4S6G0SbR7S18S75R6S10R5A1A3A2A2S43R4R5A2A3F_;F_;F_;Fx;Fc;Fe;Frho;").
Proof.
  intros rho e c x Hx Hb Hc. cbn [eval]. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned, Hx.
  unfold bv_wrap. rewrite two64. rewrite Zplus_mod_idemp_r. apply Z.mod_small. lia.
Qed.
Lemma U_add2 : ltac2:(tb__ "0|2|
SaSeSeS4S4S0S4S6Q40M0SbR5R4A2A2R2A3S0S4S6G0SbR6R4A2A2R2A3S1S42Z0S43R4R3A2M1A2S46G1S45Z2Z40A2A2A2S0S4S6G0SbR8S18S75R7R6A3A2A2S43R5R4A2A3F_;F_;F_;Fy;Fx;Fb;Fa;Frho;").
Proof.
  intros rho a b x y Hx Hy Hb. cbn [eval]. unfold alu64, alu. rewrite bv_add_unsigned, Hx, Hy.
  unfold bv_wrap. rewrite two64. apply Z.mod_small. pose proof (urange (eval rho a)). pose proof (urange (eval rho b)). lia.
Qed.
Lemma U_sub2 : ltac2:(tb__ "0|1|
SaSeSeS4S4S0S4S6Q40M0SbR5R4A2A2R2A3S0S4S6G0SbR6R4A2A2R2A3S42Z0S47R4R3A2A2S0S4S6G0SbR8S18S76R7R6A3A2A2S47R5R4A2A3F_;F_;F_;Fy;Fx;Fb;Fa;Frho;").
Proof.
  intros rho a b x y Hx Hy Hb. cbn [eval]. unfold alu64, alu. rewrite bv_sub_unsigned, Hx, Hy.
  unfold bv_wrap. rewrite two64. apply Z.mod_small. pose proof (urange (eval rho a)). pose proof (urange (eval rho b)). lia.
Qed.
Lemma U_bvadd : ltac2:(tb__ "0|4|
S7Q40M0A1M1G1S4S4S0S4S6G0R4A2R2A3M2G2S1S42Z0S43R4R3A2M3A2S46G3S45Z2Z40A2A2A2S0S4S6G0S9G0R7R6A3A2S43R5R4A2A3F_;F_;F_;Fy;Fx;Fb;Fa;").
Proof. intros a b x y <- <- H. rewrite bv_add_unsigned. unfold bv_wrap. rewrite two64. apply Z.mod_small. lia. Qed.
Lemma alu_add2 : ltac2:(tb__ "0|4|
S7Q40M0A1M1G1S4S4S0S4S6G0R4A2R2A3M2G2S1S42Z0S43R4R3A2M3A2S46G3S45Z2Z40A2A2A2S0S4S6G0S91S75R7R6A3A2S43R5R4A2A3F_;F_;F_;Fy;Fx;Fb;Fa;").
Proof. intros a b x y <- <- H. unfold alu64, alu. rewrite bv_add_unsigned. unfold bv_wrap. rewrite two64. apply Z.mod_small. lia. Qed.
Lemma negb_neq_true : ltac2:(tb__ "0|0|
S36S3S0S36S41R1A1S37A3A1S0S36R2S37A3F_;Fb;").
Proof. intros [|] H; [reflexivity | exfalso; apply H; reflexivity]. Qed.
Lemma u8 : bv_unsigned (8%bv : bv 64) = 8. Proof. reflexivity. Qed.
Lemma u16 : bv_unsigned (16%bv : bv 64) = 16. Proof. reflexivity. Qed.

Lemma In_cellb : ltac2:(tb__ "0|0|
S16S33S16A1S0S36S72S16S8aR2A1R1A3S37A3S70S16R3R2A3F_;Fcells;Fc;").
Proof.
  intros c cells H. apply existsb_exists in H as (c' & Hin & E). apply cell_eqb_sound in E. subst c'. exact Hin.
Qed.

Definition sub_idb (s : wsub) : bool := ltac2:(tb__ "0|0|
S71S5S5S2aS86Vs;R1A2S12R1A1A2Li;S79S34S5S83S7cU1U5bA2A4A3").

Record site2 (segs : list Segment) (wl_fd : Z) (S : sstate) (e0 l0 : sv) : Prop := mkSite2 {
  s2_len : (4 <= length (ss_objs S))%nat;
  s2_stk : obj_rng (ob S 0) = (SVar 10, SLit 8, SLit 40);
  s2_b1 : ob S 1 = mkObj (SVar 12) (SLit 0) (SVar 13) [] (DList 5);
  s2_b2 : ob S 2 = mkObj (SVar 14) (SLit 0) (SVar 15) [] (DRom 6);
  s2_c8 : existsb (cell_eqb (mkCell (SLit 8) 8 e0)) (ob_cells (ob S 0)) = true;
  s2_c16 : existsb (cell_eqb (mkCell (SLit 16) 8 l0)) (ob_cells (ob S 0)) = true;
  s2_c24 : existsb (cell_eqb (mkCell (SLit 24) 8 (SVar 14))) (ob_cells (ob S 0)) = true;
  s2_c32 : existsb (cell_eqb (mkCell (SLit 32) 8 (SVar 15))) (ob_cells (ob S 0)) = true;
  s2_a1 : reg_sv S 11 = SAlu ALU_ADD (SVar 10) (SLit 8);
  s2_pc : instr_at segs (ss_pc S) = Some Ecall;
  s2_a7 : reg_sv S 17 = SLit 66;
  s2_a0 : reg_sv S 10 = SLit wl_fd;
  s2_a2 : reg_sv S 12 = SLit 2;
  s2_f10a : In (SPUle (SLit 0x7fff7ff00000) (SVar 10)) (ss_facts S);
  s2_f10b : In (SPUle (SVar 10) (SLit (2 ^ 47))) (ss_facts S);
  s2_f12 : In (SPUle (SVar 12) (SLit (2 ^ 62))) (ss_facts S);
  s2_f14 : In (SPUle (SVar 14) (SLit (2 ^ 62))) (ss_facts S);

  s2_urng : forall rho, Forall (holds rho) (ss_facts S) ->
      bv_unsigned (rw rho 10) + 40 <= 2 ^ 47
      /\ bv_unsigned (rw rho 12) + bv_unsigned (rw rho 13) <= 2 ^ 47
      /\ bv_unsigned (rw rho 14) + bv_unsigned (rw rho 15) <= 2 ^ 47
}.

Record site1 (segs : list Segment) (wl_fd : Z) (S : sstate) (e1 l1 : sv) : Prop := mkSite1 {
  s1_len : (4 <= length (ss_objs S))%nat;
  s1_stk : obj_rng (ob S 0) = (SVar 10, SLit 8, SLit 40);
  s1_b2 : ob S 2 = mkObj (SVar 14) (SLit 0) (SVar 15) [] (DRom 6);
  s1_c24 : existsb (cell_eqb (mkCell (SLit 24) 8 e1)) (ob_cells (ob S 0)) = true;
  s1_c32 : existsb (cell_eqb (mkCell (SLit 32) 8 l1)) (ob_cells (ob S 0)) = true;
  s1_a1 : reg_sv S 11 = SAlu ALU_ADD (SVar 10) (SLit 24);
  s1_pc : instr_at segs (ss_pc S) = Some Ecall;
  s1_a7 : reg_sv S 17 = SLit 66;
  s1_a0 : reg_sv S 10 = SLit wl_fd;
  s1_a2 : reg_sv S 12 = SLit 1;
  s1_f10a : In (SPUle (SLit 0x7fff7ff00000) (SVar 10)) (ss_facts S);
  s1_f10b : In (SPUle (SVar 10) (SLit (2 ^ 47))) (ss_facts S);
  s1_f14 : In (SPUle (SVar 14) (SLit (2 ^ 62))) (ss_facts S);

  s1_urng : forall rho, Forall (holds rho) (ss_facts S) ->
      bv_unsigned (rw rho 10) + 40 <= 2 ^ 47
      /\ bv_unsigned (rw rho 14) + bv_unsigned (rw rho 15) <= 2 ^ 47
}.

Lemma fact_of : forall rho (F : list sprop) p, Forall (holds rho) F -> In p F -> holds rho p.
Proof. intros rho F p HF Hin. exact (proj1 (Forall_forall _ _) HF p Hin). Qed.

Ltac in_facts := cbn; repeat (first [left; reflexivity | right]).

Lemma urng_add_nowrap : ltac2:(tb__ "0|6|
S7Q40M0A1M1G1S4S4S4S42S6G0R5A2R3A2M2G2S42Z0M3R5A2M4G4S46S43R7R6A2S45Z2Z40A2M5A2S42S6G0S91S75RaR9A3A2S6G0S8G0R6A2A2A2S1S42G3R7A2S46R7G5A2A2S42S43S6G0RcA2S6G0RbA2A2R8A2F_;F_;F_;F_;F_;F_;F_;FC;Fcb;Fca;Fb;Fa;").
Proof.
  intros a b ca cb C Ha Hb Hca Hcb Hs H HC.
  pose proof (urange a). pose proof (urange b).
  rewrite (alu_add2 a b (bv_unsigned a) (bv_unsigned b) eq_refl eq_refl) in H by lia.
  rewrite u64_lit in H by lia. exact H.
Qed.

Lemma urng2_of_facts : ltac2:(tb__ "0|11|
SaS4S4S4S13R4S14S12PaM0A1S10R3A1A2A2S42Z0M1R4A2S42S43R5Z28M2A2S45Z2M3Z2fA2M4A2S13R7S14S12PcM5A1M6S10S45G3Z3eA2A1M7A2A2S13R8S14S12PdM8A1M9S10R6A1A2A2S1S42G1R7A2S42R7S45G3Z3dA2MaA2A2S13RaS14S18S75G6G9A3S10G4A1MbA2A2S13RbS14S12PeMcA1MdG7A2A2S13RcS14S12PfMeA1MfS10R9A1A2A2S1S42G1RaA2S42RaGaA2A2S13ReS14S18S75GdGfA3GbA2A2S1S42S43S6Q40M10SdRfG0A2A2G2A2G4A2S1S42S43S6G10SdRfG5A2A2S6G10SdRfG8A2A2A2G4A2S42S43S6G10SdRfGcA2A2S6G10SdRfGeA2A2A2G4A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fn15;Fn13;Fc10;Frho;").
Proof.
  intros rho c10 n13 n15 H10 Hc10 Hc40 H12 H13 Hn13 H1213 H14 H15 Hn15 H1415.
  cbn [holds eval] in H10, H12, H13, H14, H15, H1213, H1415.
  rewrite u64_lit in H10, H12, H13, H14, H15 by lia.
  split; [lia|]. split.
  - eapply (urng_add_nowrap _ _ (2 ^ 62) n13); try eassumption; lia.
  - eapply (urng_add_nowrap _ _ (2 ^ 62) n15); try eassumption; lia.
Qed.

Lemma urng1_of_facts : ltac2:(tb__ "0|a|
SaS4S4S13R3S14S12PaM0A1S10R2A1A2A2S42Z0M1R3A2S42S43R4Z28M2A2S45Z2M3Z2fA2M4A2S13R6S14S12PeM5A1M6S10S45G3Z3eA2A1A2A2S13R7S14S12PfM7A1M8S10R5A1A2A2S1S42G1R6A2S42R6S45G3Z3dA2A2A2S13R9S14S18S75G6G8A3S10G4A1A2A2S1S42S43S6Q40M9SdRaG0A2A2G2A2G4A2S42S43S6G9SdRaG5A2A2S6G9SdRaG7A2A2A2G4A2A2F_;F_;F_;F_;F_;F_;F_;Fn15;Fc10;Frho;").
Proof.
  intros rho c10 n15 H10 Hc10 Hc40 H14 H15 Hn15 H1415.
  cbn [holds eval] in H10, H14, H15, H1415.
  rewrite u64_lit in H10, H14, H15 by lia.
  split; [lia|].
  eapply (urng_add_nowrap _ _ (2 ^ 62) n15); try eassumption; lia.
Qed.

Module WLProof.

Section WL.
  Variable segs : list Segment.

  Variable wl_fd : Z.
  Hypothesis wl_fd_rng : 0 < wl_fd < 2 ^ 32.

  Variables Pre_wl2 PA2 PA2a PA2b CB2 PB2 PB2a PB2b CB1 PB1 D Pre_wl1 PA1 : sstate.

  Variables L_PA2a_e L_PA2a_d L_PA2b_e L_PA2b_d L_PB2a_d L_PB2a_e
             L_PB2b_d L_PB2b_e L_PB1_d L_PB1_e L_PA1_e L_PA1_d : sstate.
  Variable FUEL : nat.
  Variable cuts_run : list Z.

  Hypothesis PA2_eq : add_facts [SPUle (SVar 92) (SLit (2^28))] (S_after_write Pre_wl2 (reg_sv Pre_wl2 22)) = PA2.
  Hypothesis PA2a_eq : add_fact PA2 (SPNot (SPBranch BC_LTU (SVar 13) (SVar 92))) = PA2a.
  Hypothesis PA2b_eq : add_fact PA2 (SPBranch BC_LTU (SVar 13) (SVar 92)) = PA2b.
  Hypothesis PB2_eq : add_facts [SPUle (SVar 98) (SLit (2^28))] (S_after_write CB2 (reg_sv CB2 22)) = PB2.
  Hypothesis PB2a_eq : add_fact PB2 (SPNot (SPBranch BC_LTU (SVar 93) (SVar 98))) = PB2a.
  Hypothesis PB2b_eq : add_fact PB2 (SPBranch BC_LTU (SVar 93) (SVar 98)) = PB2b.
  Hypothesis PB1_eq : add_facts [SPUle (SVar 100) (SLit (2^28))] (S_after_write CB1 (reg_sv CB1 22)) = PB1.
  Hypothesis PA1_eq : add_facts [SPUle (SVar 92) (SLit (2^28))] (S_after_write Pre_wl1 (reg_sv Pre_wl1 22)) = PA1.

  Hypothesis run_PA2a : sym_run segs FUEL cuts_run PA2a true = Some [mkLeaf L_PA2a_e RsCut; mkLeaf L_PA2a_d RsCut].
  Hypothesis run_PA2b : sym_run segs FUEL cuts_run PA2b true = Some [mkLeaf L_PA2b_e RsCut; mkLeaf L_PA2b_d RsCut].
  Hypothesis run_PB2a : sym_run segs FUEL cuts_run PB2a true = Some [mkLeaf L_PB2a_d RsCut; mkLeaf L_PB2a_e RsCut].
  Hypothesis run_PB2b : sym_run segs FUEL cuts_run PB2b true = Some [mkLeaf L_PB2b_d RsCut; mkLeaf L_PB2b_e RsCut].
  Hypothesis run_PB1 : sym_run segs FUEL cuts_run PB1 true = Some [mkLeaf L_PB1_d RsCut; mkLeaf L_PB1_e RsCut].
  Hypothesis run_PA1 : sym_run segs FUEL cuts_run PA1 true = Some [mkLeaf L_PA1_e RsCut; mkLeaf L_PA1_d RsCut].

  Variables s_PA2a_CB2 s_PB2a_CB2 s_PA2b_CB1 s_PB2b_CB1 s_PB1_CB1 s_PA1_CB1
             s_PA2a_D s_PA2b_D s_PB2a_D s_PB2b_D s_PB1_D s_PA1_D : wsub.
  Hypothesis ent_PA2a_CB2 : entails L_PA2a_e CB2 s_PA2a_CB2 = true.
  Hypothesis ent_PB2a_CB2 : entails L_PB2a_e CB2 s_PB2a_CB2 = true.
  Hypothesis ent_PA2b_CB1 : entails L_PA2b_e CB1 s_PA2b_CB1 = true.
  Hypothesis ent_PB2b_CB1 : entails L_PB2b_e CB1 s_PB2b_CB1 = true.
  Hypothesis ent_PB1_CB1 : entails L_PB1_e CB1 s_PB1_CB1 = true.
  Hypothesis ent_PA1_CB1 : entails L_PA1_e CB1 s_PA1_CB1 = true.
  Hypothesis ent_PA2a_D : entails L_PA2a_d D s_PA2a_D = true.
  Hypothesis ent_PA2b_D : entails L_PA2b_d D s_PA2b_D = true.
  Hypothesis ent_PB2a_D : entails L_PB2a_d D s_PB2a_D = true.
  Hypothesis ent_PB2b_D : entails L_PB2b_d D s_PB2b_D = true.
  Hypothesis ent_PB1_D : entails L_PB1_d D s_PB1_D = true.
  Hypothesis ent_PA1_D : entails L_PA1_d D s_PA1_D = true.

  Hypothesis sv93 :
    wsub_get s_PA2a_CB2 93 = SAlu ALU_SUB (SVar 13) (SVar 92)
    /\ wsub_get s_PB2a_CB2 93 = SAlu ALU_SUB (SVar 93) (SVar 98)
    /\ wsub_get s_PA2b_CB1 93 = SAlu ALU_SUB (SVar 15) (SAlu ALU_SUB (SVar 92) (SVar 13))
    /\ wsub_get s_PB2b_CB1 93 = SAlu ALU_SUB (SVar 15) (SAlu ALU_SUB (SVar 98) (SVar 93))
    /\ wsub_get s_PB1_CB1 93 = SAlu ALU_SUB (SVar 93) (SVar 100)
    /\ wsub_get s_PA1_CB1 93 = SAlu ALU_SUB (SVar 15) (SVar 92).

  Hypothesis subs_id :
    forallb sub_idb
      [s_PA2a_CB2; s_PB2a_CB2; s_PA2b_CB1; s_PB2b_CB1; s_PB1_CB1; s_PA1_CB1;
       s_PA2a_D; s_PA2b_D; s_PB2a_D; s_PB2b_D; s_PB1_D; s_PA1_D] = true.

  Hypothesis cert_misc :
    ss_next CB2 = 98%positive /\ reg_sv CB2 22 = SAlu ALU_ADD (SVar 93) (SVar 15)
    /\ ss_next CB1 = 100%positive /\ reg_sv CB1 22 = SVar 93
    /\ ss_next Pre_wl2 = 92%positive /\ reg_sv Pre_wl2 22 = SAlu ALU_ADD (SVar 13) (SVar 15)
    /\ ss_next Pre_wl1 = 92%positive /\ reg_sv Pre_wl1 22 = SVar 15
    /\ ss_facts L_PB2a_d = SPBranch BC_EQ (SVar 98) (SAlu ALU_ADD (SVar 93) (SVar 15)) :: ss_facts PB2a
    /\ ss_facts L_PB2a_e = SPNot (SPBranch BC_EQ (SVar 98) (SAlu ALU_ADD (SVar 93) (SVar 15))) :: ss_facts PB2a
    /\ ss_facts L_PB2b_d = SPBranch BC_EQ (SVar 98) (SAlu ALU_ADD (SVar 93) (SVar 15)) :: ss_facts PB2b
    /\ ss_facts L_PB2b_e = SPNot (SPBranch BC_EQ (SVar 98) (SAlu ALU_ADD (SVar 93) (SVar 15))) :: ss_facts PB2b
    /\ ss_facts L_PB1_d = SPBranch BC_EQ (SVar 100) (SVar 93) :: ss_facts PB1
    /\ ss_facts L_PB1_e = SPNot (SPBranch BC_EQ (SVar 100) (SVar 93)) :: ss_facts PB1
    /\ ss_facts L_PA2a_d = SPNot (SPBranch BC_NE (SVar 92) (SAlu ALU_ADD (SVar 13) (SVar 15))) :: ss_facts PA2a
    /\ ss_facts L_PA2a_e = SPBranch BC_NE (SVar 92) (SAlu ALU_ADD (SVar 13) (SVar 15)) :: ss_facts PA2a
    /\ ss_facts L_PA2b_d = SPNot (SPBranch BC_NE (SVar 92) (SAlu ALU_ADD (SVar 13) (SVar 15))) :: ss_facts PA2b
    /\ ss_facts L_PA2b_e = SPBranch BC_NE (SVar 92) (SAlu ALU_ADD (SVar 13) (SVar 15)) :: ss_facts PA2b
    /\ ss_facts L_PA1_d = SPNot (SPBranch BC_NE (SVar 92) (SVar 15)) :: ss_facts PA1
    /\ ss_facts L_PA1_e = SPBranch BC_NE (SVar 92) (SVar 15) :: ss_facts PA1.

  Hypothesis cert_runs :
    ss_next PA2a = 93%positive /\ ss_next PA2b = 93%positive /\ ss_next PB2a = 99%positive
    /\ ss_next PB2b = 99%positive /\ ss_next PB1 = 101%positive /\ ss_next PA1 = 93%positive
    /\ ss_lenient PA2a = false /\ ss_lenient PA2b = false /\ ss_lenient PB2a = false
    /\ ss_lenient PB2b = false /\ ss_lenient PB1 = false /\ ss_lenient PA1 = false.
  Hypothesis cert_pre :
    sv_below 92 (reg_sv Pre_wl2 22) = true /\ sv_below 92 (reg_sv Pre_wl1 22) = true
    /\ sv_below 98 (reg_sv CB2 22) = true /\ sv_below 100 (reg_sv CB1 22) = true
    /\ In (SPUle (SVar 12) (SLit (2 ^ 62))) (ss_facts Pre_wl2) /\ In (SPUle (SVar 14) (SLit (2 ^ 62))) (ss_facts Pre_wl1).
  Hypothesis site_Pre_wl2 : site2 segs wl_fd Pre_wl2 (SVar 12) (SVar 13).
  Hypothesis site_CB2 : site2 segs wl_fd CB2 (SAlu ALU_SUB (SAlu ALU_ADD (SVar 12) (SVar 13)) (SVar 93)) (SVar 93).
  Hypothesis site_Pre_wl1 : site1 segs wl_fd Pre_wl1 (SVar 14) (SVar 15).
  Hypothesis site_CB1 : site1 segs wl_fd CB1 (SAlu ALU_SUB (SAlu ALU_ADD (SVar 14) (SVar 15)) (SVar 93)) (SVar 93).

Variable ok : world -> Prop.
Variable K : ltac2:(tb__ "0|0|
S33S4dA1S4eOF_;F_;").
Variable rho0 : valuation.
Variables bs1 bs2 : list byte.

Definition MSG : list byte := bs1 ++ bs2.
Definition chw : word := Z_to_bv 64 wl_fd.
Definition TRk (k : nat) : list event := ltac2:(tb__ "0|1|
S79S7Q8A1M0S4dS50S5cA1S77G0Vk;S5bA3A4").

Definition Kw (k : nat) : list event -> Model -> Prop := ltac2:(tb__ "0|1|
S33S4dA1M0S4eS2G0G0S1VK;R1R2A2S0G0R3S3cS4dR1S60Vk;A1A3A3A2Ltr0;A2Lmd;Ltr;").
Definition Posts_wl : list leaf := ltac2:(tb__ "0|0|
S3dS6aS6fS2eS6eA2S3aS6aA1A3").

Hypothesis Hrl5 : rl rho0 5 = bs1.
Hypothesis Hrl6 : rl rho0 6 = bs2.
Hypothesis HU13 : ltac2:(tb__ "0|0|
S0S4S6Q40SdVrho0;PdA2A2S44S35S7Q8A1Vbs1;A2A1A3").
Hypothesis HU15 : ltac2:(tb__ "0|0|
S0S4S6Q40SdVrho0;PfA2A2S44S35S7Q8A1Vbs2;A2A1A3").
Hypothesis Hmax : ltac2:(tb__ "0|0|
S42S44S35S7Q8A1S5bA2A1S95A2").
Hypothesis HokK : ltac2:(tb__ "0|0|
S34S4cS2cVok;S59R1A1A3Fk;").
Hypothesis HokP : ltac2:(tb__ "0|0|
S34S80S2cVok;S59R1A1A3Fk;").
Hypothesis Hfd : ltac2:(tb__ "0|0|
S33S4dA1S4eVK;R2R1A2S0S39S4fA1S52S53R2A1S5cA2S38S4fS51S5cA1A2A3F_;Fmd;Ftr;").

Lemma MSG_len : ltac2:(tb__ "0|1|
S0S34S35S7Q8A1M0S5bA2S64S35G0Vbs1;A2S35G0Vbs2;A2A2A3").
Proof using . unfold MSG. rewrite length_app. reflexivity. Qed.

Lemma rwmax : ltac2:(tb__ "0|1|
S1S42S44S35S7Q8A1S5bA2A1M0S55A2S42G0S45Z2Z12A2A2A2").
Proof using Hmax cert_misc cert_runs. pose proof max_write_total_le_rw_count_clamp. pose proof max_write_total_eq_2_18. lia. Qed.

Definition G (rho : valuation) : Prop := agree_below 92 rho0 rho.
Lemma G_agree : ltac2:(tb__ "0|1|
S5SaSaS19R3R2R1A3S81P5cR4A2S5aR4A1M0G0F_;F_;F_;Frho';Frho;Fn;").
Proof using .
  intros n rho rho' Hag Hn HG. eapply agree_below_trans; [exact HG|].
  eapply agree_below_le; [exact Hn|exact Hag].
Qed.
Lemma G_sub : ltac2:(tb__ "0|0|
S84SaS0S36S8dR2A1S37A3S5aR2A1S5aS85R3R4A2A1F_;F_;Frho;Fs;").
Proof using bs1 bs2 cert_misc cert_runs.
  intros s rho Hs (Hw & Hl & Hm). split; [|split; [intros l; rewrite Hl; reflexivity | intros a; rewrite Hm; reflexivity]].
  intros i Hi. rewrite (Hw i Hi). cbn [rho_sub rw].
  pose proof (proj1 (forallb_forall _ _) Hs i) as X. cbn beta in X.
  assert (In i (map Pos.of_nat (seq 1 91))) as Hin.
  { apply in_map_iff. exists (Pos.to_nat i). split; [apply Pos2Nat.id|]. apply in_seq. lia. }
  rewrite (sv_eqb_sound _ _ (X Hin)). reflexivity.
Qed.
Lemma G_rw : ltac2:(tb__ "0|0|
SaS5S5aR2A1S82R2P5cA2S0S7Q40A1SdR4R3A2SdVrho0;R3A2A3F_;F_;Fi;Frho;").
Proof using . intros rho i (Hw & _ & _) Hi. symmetry. apply Hw. exact Hi. Qed.
Lemma G_rl : ltac2:(tb__ "0|0|
SaS5S5aR2A1S0S33S7Q8A1A1S1bR3R2A2S1bVrho0;R2A2A3F_;Fl;Frho;").
Proof using . intros rho l (_ & Hl & _). symmetry. apply Hl. Qed.
Lemma G13 : ltac2:(tb__ "0|0|
SaS5aR1A1S0S4S6Q40SbR2S12PdA1A2A2S44S35S7Q8A1Vbs1;A2A1A3F_;Frho;").
Proof using HU13 bs2 cert_misc cert_runs. intros rho HG. cbn [eval]. rewrite (G_rw rho 13 HG) by lia. exact HU13. Qed.
Lemma G15 : ltac2:(tb__ "0|0|
SaS5aR1A1S0S4S6Q40SbR2S12PfA1A2A2S44S35S7Q8A1Vbs2;A2A1A3F_;Frho;").
Proof using HU15 bs1 cert_misc cert_runs. intros rho HG. cbn [eval]. rewrite (G_rw rho 15 HG) by lia. exact HU15. Qed.

Lemma Kw_fd : ltac2:(tb__ "0|0|
S34S33S4dA1S4eS59R3R2R1A3S0S39S4fA1S52S53R2A1S5cA2S38S4fS51S5cA1A2A3F_;Fmd;Ftr;Fk;").
Proof using Hfd. intros k tr md (tr0 & Hk & _). exact (Hfd tr0 md Hk). Qed.

Lemma firstn_add_skipn : forall {A} (l : list A) n k, firstn n l ++ firstn k (skipn n l) = firstn (n + k) l.
Proof using .
  intros A l n k. revert l. induction n as [|n IH]; intros l; [reflexivity|].
  destruct l as [|x l]; cbn; [rewrite firstn_nil; reflexivity|]. rewrite IH. reflexivity.
Qed.
Lemma TRk_app : ltac2:(tb__ "0|1|
S34S34S0S33S4dA1S3cS4dS60R2A1S79S7Q8A1M0S4dS50S5cA1S77G0R1S78G0R2S5bA3A3A4A3S60S64R2R1A2A1A3Fk;Fn;").
Proof using . intros n k. unfold TRk. rewrite <- map_app, firstn_add_skipn. reflexivity. Qed.
Lemma Kw_step : ltac2:(tb__ "0|1|
S34S34S33S4dA1S4eS59R4R2R1A3S59S64R5R4A2S3cS4dR3S79S7Q8A1M0S4dS50S5cA1S77G0R4S78G0R5S5bA3A3A4A3R2A3F_;Fmd;Ftr;Fk;Fn;").
Proof using . intros n k tr md (tr0 & Hk & ->). exists tr0. split; [exact Hk|]. rewrite <- app_assoc, TRk_app. reflexivity. Qed.

Lemma wl_fd_u : 0 <= wl_fd < 2 ^ 64.
Proof using bs1 bs2 cert_misc cert_runs wl_fd_rng. pose proof wl_fd_rng. lia. Qed.

Lemma iov_field : ltac2:(tb__ "0|7|
SaScS33S4dA1M0S73S4eS4SeS7Q40M1A1M2S7fS2cR8R7S3bG0S7dR6S7eR5R4A2A4A4S57U4S35S17S1eR8A1A2A2S0S3eS3eSeSeA2M3SeA2S88S8cR9U0M4A2A1S3bG3SeS3bSeSeS12PaM5A1S10Z8M6A1A4S10Z28A1A4A3S0S36S72S16S8aS27S10R6A1G6R5A3A1S20S8cRaG4A2A1A3S37A3S1S42Z0R7A2S46R7Z40A2A2S0S4S6G1R6A2S43S6G1SdRdG5A2A2R8A2A3S0S39G2A1S56S74RbA1R7A2S38G2SbReR8A2A2A3F_;F_;F_;F_;F_;F_;Fa;Fv;Foff;Fmd;Fms;Ftr;FS;Frho;").
Proof using bs1 bs2 cert_misc cert_runs.
  intros rho S tr ms md off v a Hsp Hlen Hrng Hc Hoff Ha.
  pose proof (objs_hold segs rho S tr ms md 0 Hsp ltac:(lia)) as H0.
  unfold obj_rng in Hrng. injection Hrng as Hb Hlo Hhi.
  apply (cell_read_u64 segs rho ms (ob S 0) (SLit off) v a H0 (In_cellb _ _ Hc)).
  rewrite Hb. change (eval rho (SVar 10)) with (rw rho 10). rewrite soff_lit_small by lia. lia.
Qed.

Lemma list_read : ltac2:(tb__ "0|7|
S22SaScS33S4dA1M0S73S4eS34S5S5S5S4S34S7Q40M1A1M2G2S7fS2cRdRcS3bG0S7dRbS7eRaR9A2A4A4S58R9S35S17S1eRdA1A2A2S0S17S8cReRaA2S28S12R9A1S10Z0M3A1S12R8A1S3aS16A1R10A5A3S0S39S5A1S90R11A1S38S5R8A2A3S42G3R8A2S42S43R9S44R8A1A2S6G1SdR12RbA2A2A2S46S6G1SdR13RcA2A2S45Z2Z3eA2A2S0S4S6G1R9A2M4S43S6G1SdR14ReA2A2RbA2A3S0S4G4S44RbA1A3S0S39S33S7Q8A1M5A1M6A1S54S74R13A1RbRaA3S38G6S77G5RcS78G5S48RdA1S1bR16ReA2A3A3A2A3F_;F_;F_;F_;F_;F_;F_;F_;F_;Flen;Fa;Fn;Foff;Fl;Fhi;Fb;Fi;Fmd;Fms;Ftr;FS;Frho;Fd;").
Proof using bs1 bs2 cert_misc cert_runs.
  intros d rho S tr ms md i b hi l off n a len Hsp Hi Hob Hd Hoff Hn Hhi Ha Hl.
  pose proof (objs_hold segs rho S tr ms md i Hsp Hi) as H. rewrite Hob in H.
  rewrite (listish_obj_read_bytes_map segs rho ms _ l n off a len H Hd eq_refl).
  - unfold obj_lo_of. cbn [ob_lo]. rewrite soff_lit_small by lia. rewrite Z.sub_0_r. reflexivity.
  - unfold obj_lo_of. cbn [ob_lo]. rewrite soff_lit_small by lia. lia.
  - unfold obj_hi_of. cbn [ob_hi]. rewrite soff_snorm. unfold U. change (eval rho (SVar hi)) with (rw rho hi).
    rewrite snorm_id; [lia|]. unfold smin, smax. pose proof (urange (rw rho hi)). lia.
  - cbn [ob_base]. change (eval rho (SVar b)) with (rw rho b). lia.
  - exact Hl.
Qed.

Definition Q_wr (S : sstate) (e : sv) (n len : nat) (rho : valuation) : assn := ltac2:(tb__ "0|2|
S66S2SaSaS2S34S34S1S5aR2A1S1S19S11VS;A1M0Vrho;R2A3S1S0S7Q40M1A1SdR2G0A2S8G1S44R1A1A2A3S1S1S57U1R1A2S57R1Vlen;A2A2S4aS2cS59S64Vn;R1A2A1S87VS;Ve;A2R2R3A5A2A2A2A2Lk;A2Lrho';A2Lw;").

Lemma writev2 : ltac2:(tb__ "0|6|
ScSeSeSaS34S8fS2cS2dR5R4R3A5S5aR3A1S81P5cS11R7A1A2S0S36S1fS11R8A1S15R8Z16M0A2A2S37A3S57R5S35S7Q8A1M1Vbs1;A2M2A2S57U1S64R6S35G1Vbs2;A2M3A2A2S0S4S6Q40M4SbR8R9A2A2S44R7A1A3S0S4S6G4SbR9RbA2A2S43S6G4SdR9PcA2A2S44S65G2R8A2A1A2A3S0S4S6G4SbRaS15RdG0A2A2A2S44S64R9G3A2A1A3S67S2cVok;S4aS2cS59S65G2RaA2M5A1ReRbA4S62ReS15ReG0A2G5S64RaG3A2RbA5A4F_;F_;F_;F_;F_;F_;F_;F_;F_;FL0;Frho;Fl0;Fe0;FS;").
Proof using HU13 HU15 Hfd Hmax HokK HokP Hrl5 Hrl6 cert_misc cert_runs wl_fd_rng.
  intros S e0 l0 rho L0 HS HG Hn He HL0 H1 Hl0 He0 H22.
  destruct HS as [Hlen Hrng Hb1 Hb2 C8 C16 C24 C32 R11 Hi H17 H10 H12 F10a F10b F12 F14 UR].
  pose proof wl_fd_u as FD.
  set (n := (length bs1 - L0)%nat).
  set (J' := fun (r : valuation) (tr : list event) (md : Model) =>
               exists k, rw r (ss_next S) = Z_to_bv 64 (Z.of_nat k) /\ (1 <= k <= L0 + length bs2)%nat /\ Kw (n + k) tr md).
  assert (Hbs : length (skipn n bs1 ++ bs2) = (L0 + length bs2)%nat) by (rewrite length_app, length_skipn; lia).
  apply triple1_triple.
  eapply triple1_conseq; [intros w Hw; exact Hw | |
    eapply (triple1_writev2J segs ok (liftK (Kw n)) J' S rho wl_fd (skipn n bs1) bs2 (reg_sv S 22));
      [ apply ok_frame_liftK; apply HokK
      | intros r tr ms md x8 Hk; exact (HokP n tr ms md x8 Hk)
      | exact Hi | exact H17 | exact H10 | exact H12 | exact wl_fd_rng | rewrite Hbs; pose proof rwmax as RWM; rewrite MSG_len in RWM; lia | exact He | | ]].
  - intros w (rho' & Hag & Hsm & (k & Hk & Hkb & HK)). exists rho', k.
    split; [exact (G_agree _ _ _ Hag Hn HG)|]. split; [exact Hag|]. split; [exact Hk|]. split; [exact Hkb|].
    split; [exact Hsm | exact HK].
  - intros rho' tr md k Hag Hk HK Hkb. split; [exact (Kw_fd _ _ _ HK)|]. exists k. split; [exact Hk|].
    split; [rewrite Hbs in Hkb; exact Hkb|].
    replace (skipn n bs1 ++ bs2) with (skipn n MSG) by (unfold MSG; rewrite skipn_app; replace (n - length bs1)%nat with 0%nat by lia; reflexivity).
    apply Kw_step. exact HK.
  - intros tr ms md Hsp HK.
    pose proof (SPp_fact segs _ _ _ _ _ _ Hsp F10a) as A1. pose proof (SPp_fact segs _ _ _ _ _ _ Hsp F10b) as A2.
    pose proof (SPp_fact segs _ _ _ _ _ _ Hsp F12) as A3. pose proof (SPp_fact segs _ _ _ _ _ _ Hsp F14) as A4.
    cbn [holds eval] in A1, A2, A3, A4. rewrite !u64_lit in A1, A2, A3, A4 by lia.
    change (eval rho (SVar 10)) with (rw rho 10) in *. change (eval rho (SVar 12)) with (rw rho 12) in *. change (eval rho (SVar 14)) with (rw rho 14) in *.
    pose proof (G13 rho HG) as V13. pose proof (G15 rho HG) as V15. cbn [eval] in V13, V15.
    assert (A0 : bv_unsigned (eval rho (reg_sv S 11)) = bv_unsigned (rw rho 10) + 8).
    { rewrite R11. apply (U_addc rho (SVar 10) 8 (bv_unsigned (rw rho 10))); [reflexivity | lia | lia]. }
    assert (A16 : bv_unsigned (eval rho (reg_sv S 11) + 16)%bv = bv_unsigned (rw rho 10) + 24) by (rewrite (U_bvadd _ _ _ _ A0 u16) by lia; lia).
    exists (eval rho e0), (eval rho l0), (eval rho (SVar 14)), (eval rho (SVar 15)).
    split; [eapply (iov_field rho S tr ms md 8); [exact Hsp | exact Hlen | exact Hrng | exact C8 | lia | lia]|].
    split; [eapply (iov_field rho S tr ms md 16); [exact Hsp | exact Hlen | exact Hrng | exact C16 | lia | rewrite (U_bvadd _ _ _ _ A0 u8) by lia; lia]|].
    split; [eapply (iov_field rho S tr ms md 24); [exact Hsp | exact Hlen | exact Hrng | exact C24 | lia | lia]|].
    split; [eapply (iov_field rho S tr ms md 32); [exact Hsp | exact Hlen | exact Hrng | exact C32 | lia | rewrite (U_bvadd _ _ _ _ A16 u8) by lia; lia]|].
    split.
    { pose proof rwmax as HM. rewrite MSG_len in HM.
      rewrite (list_read (DList 5) rho S tr ms md 1 12 13 5 (Z.of_nat n) L0 (eval rho e0) (eval rho l0) Hsp ltac:(lia) Hb1 eq_refl ltac:(lia) ltac:(rewrite V13; lia) ltac:(rewrite V13; lia) He0 Hl0).
      f_equal. rewrite Nat2Z.id, (G_rl rho 5 HG), Hrl5. apply firstn_all2. rewrite length_skipn. lia. }
    split.
    { pose proof rwmax as HM. rewrite MSG_len in HM.
      rewrite (list_read (DRom 6) rho S tr ms md 2 14 15 6 0 (length bs2) (eval rho (SVar 14)) (eval rho (SVar 15)) Hsp ltac:(lia) Hb2 eq_refl ltac:(lia) ltac:(rewrite V15; lia) ltac:(rewrite V15; lia) ltac:(cbn [eval]; lia) V15).
      f_equal. cbn [Z.to_nat skipn]. rewrite (G_rl rho 6 HG), Hrl6. apply firstn_all. }
    destruct (UR rho (SPp_facts segs _ _ _ _ _ Hsp)) as (U10 & U12 & U14).
    change (eval rho (SVar 14)) with (rw rho 14). change (eval rho (SVar 15)) with (rw rho 15).
    rewrite task_size_val. split; [rewrite H22, Hbs; reflexivity|]. split; [lia|]. split; [|exact U14].
    rewrite He0, Hl0. rewrite V13 in U12. lia.
Qed.

Lemma writev1 : ltac2:(tb__ "0|4|
ScSeSeSaS34S34S8eS2cS2dR6R5R4A5S5aR4A1S81P5cS11R8A1A2S0S36S1fS11R9A1S15R9Z16M0A2A2S37A3S1S57U1R6A2S57R6S35S7Q8A1M1Vbs2;A2M2A2A2S0S34R6S64S35G1Vbs1;A2S65G2R7A2A2A3S0S4S6Q40M3SbR9RaA2A2S44R8A1A3S0S4S6G3SbRaRcA2A2S43S6G3SdRaPeA2A2S44S65G2R9A2A1A2A3S0S4S6G3SbRbS15ReG0A2A2A2S44RaA1A3S67S2cVok;S4aS2cS59RaA1RfRcA4S62RfS15RfG0A2RaRbRcA5A4F_;F_;F_;F_;F_;F_;F_;F_;F_;Fn0;FR;Frho;Fl1;Fe1;FS;").
Proof using HU15 Hfd Hmax HokK HokP Hrl6 cert_misc cert_runs wl_fd_rng.
  intros S e1 l1 rho R n0 HS HG Hn He HR Hn0 Hl1 He1 H22.
  destruct HS as [Hlen Hrng Hb2 C24 C32 R11 Hi H17 H10 H12 F10a F10b F14 UR].
  pose proof wl_fd_u as FD.
  set (J' := fun (r : valuation) (tr : list event) (md : Model) =>
               exists k, rw r (ss_next S) = Z_to_bv 64 (Z.of_nat k) /\ (1 <= k <= R)%nat /\ Kw (n0 + k) tr md).
  assert (Hbs : length (skipn (length bs2 - R) bs2) = R) by (rewrite length_skipn; lia).
  apply triple1_triple.
  eapply triple1_conseq; [intros w Hw; exact Hw | |
    eapply (triple1_writev1J segs ok (liftK (Kw n0)) J' S rho wl_fd (skipn (length bs2 - R) bs2) (reg_sv S 22));
      [ apply ok_frame_liftK; apply HokK
      | intros r tr ms md x8 Hk; exact (HokP n0 tr ms md x8 Hk)
      | exact Hi | exact H17 | exact H10 | exact H12 | exact wl_fd_rng | rewrite Hbs; pose proof rwmax as RWM; rewrite MSG_len in RWM; lia | exact He | | ]].
  - intros w (rho' & Hag & Hsm & (k & Hk & Hkb & HK)). exists rho', k.
    split; [exact (G_agree _ _ _ Hag Hn HG)|]. split; [exact Hag|]. split; [exact Hk|]. split; [exact Hkb|].
    split; [exact Hsm | exact HK].
  - intros rho' tr md k Hag Hk HK Hkb. split; [exact (Kw_fd _ _ _ HK)|]. exists k. split; [exact Hk|].
    split; [rewrite Hbs in Hkb; exact Hkb|].
    replace (skipn (length bs2 - R) bs2) with (skipn n0 MSG) by (unfold MSG; rewrite skipn_app, skipn_all2 by lia; cbn [app]; f_equal; lia).
    apply Kw_step. exact HK.
  - intros tr ms md Hsp HK.
    pose proof (SPp_fact segs _ _ _ _ _ _ Hsp F10a) as A1. pose proof (SPp_fact segs _ _ _ _ _ _ Hsp F10b) as A2.
    pose proof (SPp_fact segs _ _ _ _ _ _ Hsp F14) as A4.
    cbn [holds eval] in A1, A2, A4. rewrite !u64_lit in A1, A2, A4 by lia.
    change (eval rho (SVar 10)) with (rw rho 10) in *. change (eval rho (SVar 14)) with (rw rho 14) in *.
    pose proof (G15 rho HG) as V15. cbn [eval] in V15.
    assert (A0 : bv_unsigned (eval rho (reg_sv S 11)) = bv_unsigned (rw rho 10) + 24).
    { rewrite R11. apply (U_addc rho (SVar 10) 24 (bv_unsigned (rw rho 10))); [reflexivity | lia | lia]. }
    exists (eval rho e1), (eval rho l1).
    split; [eapply (iov_field rho S tr ms md 24); [exact Hsp | exact Hlen | exact Hrng | exact C24 | lia | lia]|].
    split; [eapply (iov_field rho S tr ms md 32); [exact Hsp | exact Hlen | exact Hrng | exact C32 | lia | rewrite (U_bvadd _ _ _ _ A0 u8) by lia; lia]|].
    split.
    { pose proof rwmax as HM. rewrite MSG_len in HM.
      rewrite (list_read (DRom 6) rho S tr ms md 2 14 15 6 (Z.of_nat (length bs2 - R)) R (eval rho e1) (eval rho l1) Hsp ltac:(lia) Hb2 eq_refl ltac:(lia) ltac:(rewrite V15; lia) ltac:(rewrite V15; lia) He1 Hl1).
      f_equal. rewrite Nat2Z.id, (G_rl rho 6 HG), Hrl6. apply firstn_all2. rewrite length_skipn. lia. }
    destruct (UR rho (SPp_facts segs _ _ _ _ _ Hsp)) as (U10 & U14).
    rewrite task_size_val. split; [rewrite H22, Hbs; reflexivity|]. split; [lia|].
    rewrite He1, Hl1. rewrite V15 in U14. lia.
Qed.

Definition P_of (rho : valuation) : nat := Z.to_nat (bv_unsigned (rw rho 93)).
Definition QD : assn := ltac2:(tb__ "0|0|
S4bS2cS59S35S7Q8A1S5bA2A1P5cVrho0;S5eA5").

Lemma facts_12 : ltac2:(tb__ "0|2|
ScSaS66S33S4dA1S4eOF_;F_;S4aS2cR1R4R3R2A5S70SfS14S12PcM0A1S10S45Z2Z3eA2M1A1A2S1aR5A1A3S42S6Q40SdR5G0A2A2G1A2F_;F_;FKx;Fw;Frho;FS;").
Proof using bs1 bs2 cert_misc cert_runs. intros S rho w Kx Hsp Hin. pose proof (SP_fact segs _ _ _ _ _ Hsp Hin) as X. cbn [holds eval] in X. rewrite u64_lit in X by lia. exact X. Qed.
Lemma facts_14 : ltac2:(tb__ "0|2|
ScSaS66S33S4dA1S4eOF_;F_;S4aS2cR1R4R3R2A5S70SfS14S12PeM0A1S10S45Z2Z3eA2M1A1A2S1aR5A1A3S42S6Q40SdR5G0A2A2G1A2F_;F_;FKx;Fw;Frho;FS;").
Proof using bs1 bs2 cert_misc cert_runs. intros S rho w Kx Hsp Hin. pose proof (SP_fact segs _ _ _ _ _ Hsp Hin) as X. cbn [holds eval] in X. rewrite u64_lit in X by lia. exact X. Qed.

Lemma to_D : ltac2:(tb__ "0|0|
ScS84SaS34S66S0S36S89R5S2eR4A3S37A3S0S36S8dR5A1S37A3S5aR5A1S0S34R5S35S7Q8A1S5bA2A3S4aS2cS59R6A1R9R7R5A5S5fR6A1F_;F_;F_;F_;F_;Fw;Fn;Frho;FsD;FL;").
Proof using cert_misc cert_runs.
  intros L sD rho n w He Hs HG -> Hsp. exists (mkLeaf D RsCut), (rho_sub rho sD).
  split; [left; reflexivity|]. split; [apply G_sub; [exact Hs | exact HG]|].
  eapply SP_entails; [exact He | exact Hsp].
Qed.

Lemma after_write_below : ltac2:(tb__ "0|0|
ScS5S4S0S5S11R3A1R2A3S0S36S71SfS1cS11S87R4S15R4Z16A2A2A1A1S3dSfS14S12R3A1S10R2A1A2S3aSfA1A3A3S37A3F_;Fz;Fv;FS;").
Proof using bs1 bs2 cert_misc cert_runs.
  intros S v z Hv. unfold S_after_write. rewrite !ss_next_add_fact, ss_next_S_after, Hv.
  cbn. rewrite !andb_true_r. apply Pos.ltb_lt. lia.
Qed.

Lemma below_of_eq : ltac2:(tb__ "0|0|
ScScSfS5SfS0ScS6cR5R3A2R4A3S0S5S11R5A1R3A3S0S36S1cR4R3A2S37A3S0S36S1cS11R8A1R4A2S37A3F_;F_;F_;Ff;Fv;Fp;FS';FS;").
Proof using . intros S S' p v f <- Hv Hf. exact (eq_trans (f_equal (fun n => sprop_below n f) Hv) Hf). Qed.

Lemma loop : ltac2:(tb__ "0|8|
S34S1SaS5aR1A1M0S57S5dR2A1M1S35S7Q8A1M2Vbs1;A2M3A2S57U1M4S64S5dR3A1M5S35G2Vbs2;A2M6A2A2S57S64S5dR4A1M7G6A2R5A2S67S2cVok;S4aS2cS59S65G3S5dR5A1A2A1S32R5A4S5fA4F_;F_;F_;F_;Frho;SaG0S1S57G4G1A2S57G1G6A2A2S57G5R4A2S67S2cVok;S4aS2cS59S64G3S65G6G7A2A2A1S31R4A4S5fA4F_;F_;F_;Frho;A2Fm;").
Proof using HU13 HU15 Hfd Hmax HokK HokP Hrl5 Hrl6 PB1_eq PB2_eq PB2a_eq PB2b_eq cert_misc cert_runs ent_PB1_CB1 ent_PB1_D ent_PB2a_CB2 ent_PB2a_D ent_PB2b_CB1 ent_PB2b_D run_PB1 run_PB2a run_PB2b site_CB1 site_CB2 subs_id sv93 wl_fd_rng.
  pose proof rwmax as RWM. rewrite MSG_len in RWM.
  pose proof subs_id as SI. cbn [forallb] in SI.
  apply andb_prop in SI as [S1 SI]. apply andb_prop in SI as [S2 SI]. apply andb_prop in SI as [S3 SI].
  apply andb_prop in SI as [S4 SI]. apply andb_prop in SI as [S5 SI]. apply andb_prop in SI as [S6 SI].
  apply andb_prop in SI as [S7 SI]. apply andb_prop in SI as [S8 SI]. apply andb_prop in SI as [S9 SI].
  apply andb_prop in SI as [S10 SI]. apply andb_prop in SI as [S11 SI]. apply andb_prop in SI as [S12 _].
  destruct cert_misc as (Nx2 & R22b & Nx1 & R22c & _ & _ & _ & _ & FPB2ad & FPB2ae & FPB2bd & FPB2be & FPB1d & FPB1e & _).
  destruct cert_runs as (_ & _ & NxPB2a & NxPB2b & NxPB1 & _ & _ & _ & StPB2a & StPB2b & StPB1 & _).
  destruct sv93 as (_ & CV2a & _ & CV2b & CV1 & _).
  pose proof (s2_f12 _ _ _ _ _ site_CB2) as F12. pose proof (s1_f14 _ _ _ _ _ site_CB1) as F14.
  induction m as [|m IH].
  { split; intros; exfalso; lia. }
  destruct IH as [IH2 IH1].
  split.
  -
    intros rho HG HL0 H1 Hm. set (L0 := P_of rho) in *.
    assert (U93 : bv_unsigned (rw rho 93) = Z.of_nat L0) by (subst L0; unfold P_of; pose proof (urange (rw rho 93)); lia).
    clearbody L0.
    apply triple_facts. intros HF.
    eapply triple_seq.
    { apply (writev2 CB2 _ _ rho L0 site_CB2 HG); [rewrite Nx2; lia | rewrite R22b, Nx2; reflexivity | lia | lia | cbn [eval]; exact U93 | |].
      + pose proof (G13 rho HG) as V13. cbn [eval] in V13.
        assert (B12 : bv_unsigned (rw rho 12) <= 2 ^ 62).
        { pose proof (proj1 (Forall_forall _ _) HF (SPUle (SVar 12) (SLit (2 ^ 62))) F12) as X.
          cbn [holds eval] in X. rewrite u64_lit in X by lia. exact X. }
        pose proof (urange (rw rho 12)) as UR12.
        rewrite (U_sub2 rho _ _ (bv_unsigned (rw rho 12) + Z.of_nat (length bs1)) (Z.of_nat L0)); [lia | | cbn [eval]; exact U93 | lia].
        apply (U_add2 rho (SVar 12) (SVar 13) (bv_unsigned (rw rho 12)) (Z.of_nat (length bs1))); [reflexivity | exact V13 | lia].
      + rewrite R22b. pose proof (G15 rho HG) as V15. cbn [eval] in V15.
        rewrite (U_add2 rho (SVar 93) (SVar 15) (Z.of_nat L0) (Z.of_nat (length bs2))); [lia | cbn [eval]; exact U93 | exact V15 | lia]. }
    apply triple_ex; intros rho1. apply triple_ex; intros k.
    apply triple_pure; intros HG1. apply triple_pure; intros Hag1. apply triple_pure; intros Hk. apply triple_pure; intros Hkb.
    rewrite Nx2 in Hk, Hag1.
    assert (E93 : rw rho1 93 = rw rho 93) by (symmetry; apply (proj1 Hag1); lia).
    assert (U98 : bv_unsigned (rw rho1 98) = Z.of_nat k) by (rewrite Hk; apply Z_to_bv_small; rewrite two64; lia).
    pose proof (G15 rho1 HG1) as V15. cbn [eval] in V15.

    eapply triple_conseq with (P := SP segs (Kw (length bs1 - L0 + k)) PB2 rho1); [| intros w Hw; exact Hw |].
    { intros w Hw. rewrite <- PB2_eq. apply SP_addn; [exact Hw | | apply after_write_below; exact Nx2]. constructor; [|constructor].
      cbn [holds eval]. rewrite U98, u64_lit by lia. lia. }
    destruct (Nat.le_gt_cases k L0) as [Hle|Hgt].
    +
      eapply triple_conseq with (P := SP segs (Kw (length bs1 - L0 + k)) PB2a rho1); [| intros w Hw; exact Hw |].
      { intros w Hw. rewrite <- PB2a_eq. apply SP_add1; [exact Hw | | apply (below_of_eq _ _ _ _ _ PB2a_eq NxPB2a); reflexivity]. cbn [holds eval branch_taken]. unfold bv_ltu.
        rewrite E93, U93, U98. destruct (Z.ltb_spec (Z.of_nat L0) (Z.of_nat k)); [lia | discriminate]. }
      eapply run_tr; [exact run_PB2a | exact StPB2a | apply HokK |].
      intros L rho2 [<-|[<-|[]]] Hag2; cbn [lf_state]; rewrite NxPB2a in Hag2.
      *
        eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
        intros w Hw. pose proof (hd_fact segs rho2 L_PB2a_d _ _ w _ FPB2ad Hw) as Hf.
        cbn [holds branch_taken eval] in Hf. unfold bv_eqb in Hf. apply Z.eqb_eq in Hf.
        rewrite <- (proj1 Hag2 98%positive ltac:(cbn; lia)), U98 in Hf.
        rewrite (alu_add2 (rw rho2 93) (rw rho2 15) (Z.of_nat L0) (Z.of_nat (length bs2))) in Hf;
          [| rewrite <- (proj1 Hag2 93%positive ltac:(cbn; lia)), E93; exact U93
           | rewrite <- (proj1 Hag2 15%positive ltac:(cbn; lia)); exact V15 | lia].
        apply (to_D _ _ rho2 (length bs1 - L0 + k)%nat w ent_PB2a_D S9 ltac:(eapply G_agree; [exact Hag2 | cbn; lia | exact HG1]) ltac:(clear -HL0 Hle Hf; rewrite MSG_len; lia) Hw).
      *
        apply triple_facts. intros HF2. rewrite FPB2ae in HF2.
        apply Forall_inv in HF2. cbn [holds branch_taken eval] in HF2. unfold bv_eqb in HF2. rewrite Z.eqb_eq in HF2.
        rewrite <- (proj1 Hag2 98%positive ltac:(cbn; lia)), U98 in HF2.
        rewrite (alu_add2 (rw rho2 93) (rw rho2 15) (Z.of_nat L0) (Z.of_nat (length bs2))) in HF2;
          [| rewrite <- (proj1 Hag2 93%positive ltac:(cbn; lia)), E93; exact U93
           | rewrite <- (proj1 Hag2 15%positive ltac:(cbn; lia)); exact V15 | lia].
        assert (EL : P_of (rho_sub rho2 s_PB2a_CB2) = (L0 - k)%nat).
        { unfold P_of. cbn [rho_sub rw]. rewrite CV2a.
          rewrite (U_sub2 rho2 (SVar 93) (SVar 98) (Z.of_nat L0) (Z.of_nat k)); [lia | | | lia];
            cbn [eval]; rewrite <- ?(proj1 Hag2 93%positive ltac:(cbn; lia)), <- ?(proj1 Hag2 98%positive ltac:(cbn; lia)), ?E93; [exact U93 | exact U98]. }
        eapply triple_conseq; [| intros w Hw; exact Hw | apply (IH2 (rho_sub rho2 s_PB2a_CB2))].
        -- intros w Hw. eapply SP_entails in Hw; [|exact ent_PB2a_CB2]. rewrite EL.
           replace (length bs1 - (L0 - k))%nat with (length bs1 - L0 + k)%nat by lia. exact Hw.
        -- apply G_sub; [exact S2|]. eapply G_agree; [exact Hag2 | cbn; lia | exact HG1].
        -- rewrite EL. lia.
        -- rewrite EL. lia.
        -- rewrite EL. lia.
    +
      eapply triple_conseq with (P := SP segs (Kw (length bs1 - L0 + k)) PB2b rho1); [| intros w Hw; exact Hw |].
      { intros w Hw. rewrite <- PB2b_eq. apply SP_add1; [exact Hw | | apply (below_of_eq _ _ _ _ _ PB2b_eq NxPB2b); reflexivity]. cbn [holds eval branch_taken]. unfold bv_ltu.
        rewrite E93, U93, U98. destruct (Z.ltb_spec (Z.of_nat L0) (Z.of_nat k)); [reflexivity | lia]. }
      eapply run_tr; [exact run_PB2b | exact StPB2b | apply HokK |].
      intros L rho2 [<-|[<-|[]]] Hag2; cbn [lf_state]; rewrite NxPB2b in Hag2.
      *
        eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
        intros w Hw. pose proof (hd_fact segs rho2 L_PB2b_d _ _ w _ FPB2bd Hw) as Hf.
        cbn [holds branch_taken eval] in Hf. unfold bv_eqb in Hf. apply Z.eqb_eq in Hf.
        rewrite <- (proj1 Hag2 98%positive ltac:(cbn; lia)), U98 in Hf.
        rewrite (alu_add2 (rw rho2 93) (rw rho2 15) (Z.of_nat L0) (Z.of_nat (length bs2))) in Hf;
          [| rewrite <- (proj1 Hag2 93%positive ltac:(cbn; lia)), E93; exact U93
           | rewrite <- (proj1 Hag2 15%positive ltac:(cbn; lia)); exact V15 | lia].
        apply (to_D _ _ rho2 (length bs1 - L0 + k)%nat w ent_PB2b_D S10 ltac:(eapply G_agree; [exact Hag2 | cbn; lia | exact HG1]) ltac:(clear -HL0 Hgt Hf Hkb; rewrite MSG_len; lia) Hw).
      *
        apply triple_facts. intros HF2. rewrite FPB2be in HF2.
        apply Forall_inv in HF2. cbn [holds branch_taken eval] in HF2. unfold bv_eqb in HF2. rewrite Z.eqb_eq in HF2.
        rewrite <- (proj1 Hag2 98%positive ltac:(cbn; lia)), U98 in HF2.
        rewrite (alu_add2 (rw rho2 93) (rw rho2 15) (Z.of_nat L0) (Z.of_nat (length bs2))) in HF2;
          [| rewrite <- (proj1 Hag2 93%positive ltac:(cbn; lia)), E93; exact U93
           | rewrite <- (proj1 Hag2 15%positive ltac:(cbn; lia)); exact V15 | lia].
        assert (ER : P_of (rho_sub rho2 s_PB2b_CB1) = (L0 + length bs2 - k)%nat).
        { unfold P_of. cbn [rho_sub rw]. rewrite CV2b.
          rewrite (U_sub2 rho2 (SVar 15) _ (Z.of_nat (length bs2)) (Z.of_nat k - Z.of_nat L0)); [lia | | | lia].
          - cbn [eval]. rewrite <- (proj1 Hag2 15%positive ltac:(cbn; lia)). exact V15.
          - apply (U_sub2 rho2 (SVar 98) (SVar 93)); [| | lia]; cbn [eval];
              rewrite <- ?(proj1 Hag2 93%positive ltac:(cbn; lia)), <- ?(proj1 Hag2 98%positive ltac:(cbn; lia)), ?E93; [exact U98 | exact U93]. }
        eapply triple_conseq; [| intros w Hw; exact Hw | apply (IH1 (rho_sub rho2 s_PB2b_CB1))].
        -- intros w Hw. eapply SP_entails in Hw; [|exact ent_PB2b_CB1]. rewrite ER.
           replace (length bs1 + (length bs2 - (L0 + length bs2 - k)))%nat with (length bs1 - L0 + k)%nat by lia. exact Hw.
        -- apply G_sub; [exact S4|]. eapply G_agree; [exact Hag2 | cbn; lia | exact HG1].
        -- rewrite ER. lia.
        -- rewrite ER. lia.
  -
    intros rho HG HR Hm. set (R := P_of rho) in *.
    assert (U93 : bv_unsigned (rw rho 93) = Z.of_nat R) by (subst R; unfold P_of; pose proof (urange (rw rho 93)); lia).
    clearbody R.
    apply triple_facts. intros HF.
    eapply triple_seq.
    { apply (writev1 CB1 _ _ rho R (length bs1 + (length bs2 - R)) site_CB1 HG); [rewrite Nx1; lia | rewrite R22c, Nx1; reflexivity | lia | lia | cbn [eval]; exact U93 | | rewrite R22c; cbn [eval]; exact U93].
      pose proof (G15 rho HG) as V15. cbn [eval] in V15.
      assert (B14 : bv_unsigned (rw rho 14) <= 2 ^ 62).
      { pose proof (proj1 (Forall_forall _ _) HF (SPUle (SVar 14) (SLit (2 ^ 62))) F14) as X.
        cbn [holds eval] in X. rewrite u64_lit in X by lia. exact X. }
      pose proof (urange (rw rho 14)) as UR14.
      rewrite (U_sub2 rho _ _ (bv_unsigned (rw rho 14) + Z.of_nat (length bs2)) (Z.of_nat R)); [lia | | cbn [eval]; exact U93 | lia].
      apply (U_add2 rho (SVar 14) (SVar 15) (bv_unsigned (rw rho 14)) (Z.of_nat (length bs2))); [reflexivity | exact V15 | lia]. }
    apply triple_ex; intros rho1. apply triple_ex; intros k.
    apply triple_pure; intros HG1. apply triple_pure; intros Hag1. apply triple_pure; intros Hk. apply triple_pure; intros Hkb.
    rewrite Nx1 in Hk, Hag1.
    assert (E93 : rw rho1 93 = rw rho 93) by (symmetry; apply (proj1 Hag1); lia).
    assert (U100 : bv_unsigned (rw rho1 100) = Z.of_nat k) by (rewrite Hk; apply Z_to_bv_small; rewrite two64; lia).
    eapply triple_conseq with (P := SP segs (Kw (length bs1 + (length bs2 - R) + k)) PB1 rho1); [| intros w Hw; exact Hw |].
    { intros w Hw. rewrite <- PB1_eq. apply SP_addn; [exact Hw | | apply after_write_below; exact Nx1]. constructor; [|constructor].
      cbn [holds eval]. rewrite U100, u64_lit by lia. lia. }
    eapply run_tr; [exact run_PB1 | exact StPB1 | apply HokK |].
    intros L rho2 [<-|[<-|[]]] Hag2; cbn [lf_state]; rewrite NxPB1 in Hag2.
    +
      eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
      intros w Hw. pose proof (hd_fact segs rho2 L_PB1_d _ _ w _ FPB1d Hw) as Hf.
      cbn [holds branch_taken eval] in Hf. unfold bv_eqb in Hf. apply Z.eqb_eq in Hf.
      rewrite <- (proj1 Hag2 100%positive ltac:(cbn; lia)), <- (proj1 Hag2 93%positive ltac:(cbn; lia)), U100, E93, U93 in Hf.
      apply (to_D _ _ rho2 (length bs1 + (length bs2 - R) + k)%nat w ent_PB1_D S11 ltac:(eapply G_agree; [exact Hag2 | cbn; lia | exact HG1]) ltac:(clear -HR Hf Hkb; rewrite MSG_len; lia) Hw).
    +
      apply triple_facts. intros HF2. rewrite FPB1e in HF2.
      apply Forall_inv in HF2. cbn [holds branch_taken eval] in HF2. unfold bv_eqb in HF2. rewrite Z.eqb_eq in HF2.
      rewrite <- (proj1 Hag2 100%positive ltac:(cbn; lia)), <- (proj1 Hag2 93%positive ltac:(cbn; lia)), U100, E93, U93 in HF2.
      assert (ER : P_of (rho_sub rho2 s_PB1_CB1) = (R - k)%nat).
      { unfold P_of. cbn [rho_sub rw]. rewrite CV1.
        rewrite (U_sub2 rho2 (SVar 93) (SVar 100) (Z.of_nat R) (Z.of_nat k)); [lia | | | lia]; cbn [eval];
          rewrite <- ?(proj1 Hag2 93%positive ltac:(cbn; lia)), <- ?(proj1 Hag2 100%positive ltac:(cbn; lia)), ?E93; [exact U93 | exact U100]. }
      eapply triple_conseq; [| intros w Hw; exact Hw | apply (IH1 (rho_sub rho2 s_PB1_CB1))].
      * intros w Hw. eapply SP_entails in Hw; [|exact ent_PB1_CB1]. rewrite ER.
        replace (length bs1 + (length bs2 - (R - k)))%nat with (length bs1 + (length bs2 - R) + k)%nat by lia. exact Hw.
      * apply G_sub; [exact S5|]. eapply G_agree; [exact Hag2 | cbn; lia | exact HG1].
      * rewrite ER. lia.
      * rewrite ER. lia.
Qed.

Definition eQ_wr (S : sstate) (e : sv) (n len : nat) (rho : valuation) : world -> Prop := ltac2:(tb__ "0|4|
S66S2SaSaS2S34S34S1S5aR2A1S1S19S11VS;A1M0Vrho;R2A3S1S0S7Q40M1A1M2SdR2G0A2M3S8G1S44R1A1A2A3S1S1S57U1R1A2S57R1Vlen;A2A2S1S0G2G3S8G1S44Vlen;A1A2A3S4aS2cS59S64Vn;R1A2A1S87VS;Ve;A2R2R3A5A2A2A2A2A2Lk;A2Lrho';A2Lw;").

Lemma ewritev2 : ltac2:(tb__ "0|6|
ScSeSeSaS34S8fS2cS2dR5R4R3A5S5aR3A1S81P5cS11R7A1A2S0S36S1fS11R8A1S15R8Z16M0A2A2S37A3S57R5S35S7Q8A1M1Vbs1;A2M2A2S57U1S64R6S35G1Vbs2;A2M3A2A2S0S4S6Q40M4SbR8R9A2A2S44R7A1A3S0S4S6G4SbR9RbA2A2S43S6G4SdR9PcA2A2S44S65G2R8A2A1A2A3S0S4S6G4SbRaS15RdG0A2A2A2S44S64R9G3A2A1A3S68S2cS4aS2cS59S65G2RaA2M5A1ReRbA4S63ReS15ReG0A2G5S64RaG3A2RbA5A3F_;F_;F_;F_;F_;F_;F_;F_;F_;FL0;Frho;Fl0;Fe0;FS;").
Proof using HU13 HU15 Hfd Hmax Hrl5 Hrl6 cert_misc cert_runs wl_fd_rng.
  intros S e0 l0 rho L0 HS HG Hn He HL0 H1 Hl0 He0 H22.
  destruct HS as [Hlen Hrng Hb1 Hb2 C8 C16 C24 C32 R11 Hi H17 H10 H12 F10a F10b F12 F14 UR].
  pose proof wl_fd_u as FD.
  set (n := (length bs1 - L0)%nat).
  set (J' := fun (r : valuation) (tr : list event) (md : Model) =>
               exists k, rw r (ss_next S) = Z_to_bv 64 (Z.of_nat k) /\ (1 <= k <= L0 + length bs2)%nat /\ Kw (n + k) tr md).
  assert (Hbs : length (skipn n bs1 ++ bs2) = (L0 + length bs2)%nat) by (rewrite length_app, length_skipn; lia).
  eapply etriple_conseq; [intros w Hw; exact Hw | |
    eapply (etriple_writev2J segs (liftK (Kw n)) J' S rho wl_fd (skipn n bs1) bs2 (reg_sv S 22));
      [ exact Hi | exact H17 | exact H10 | exact H12 | exact wl_fd_rng | rewrite Hbs; pose proof rwmax as RWM; rewrite MSG_len in RWM; lia | exact He | | ]].
  - intros w (rho' & Hag & Hfull & Hsm & (k & Hk & Hkb & HK)). exists rho', k.
    split; [exact (G_agree _ _ _ Hag Hn HG)|]. split; [exact Hag|]. split; [exact Hk|]. split; [exact Hkb|].
    split; [rewrite Hbs in Hfull; exact Hfull|]. split; [exact Hsm | exact HK].
  - intros rho' tr md k Hag Hk HK Hkb. split; [exact (Kw_fd _ _ _ HK)|]. exists k. split; [exact Hk|].
    split; [rewrite Hbs in Hkb; exact Hkb|].
    replace (skipn n bs1 ++ bs2) with (skipn n MSG) by (unfold MSG; rewrite skipn_app; replace (n - length bs1)%nat with 0%nat by lia; reflexivity).
    apply Kw_step. exact HK.
  - intros tr ms md Hsp HK.
    pose proof (SPp_fact segs _ _ _ _ _ _ Hsp F10a) as A1. pose proof (SPp_fact segs _ _ _ _ _ _ Hsp F10b) as A2.
    pose proof (SPp_fact segs _ _ _ _ _ _ Hsp F12) as A3. pose proof (SPp_fact segs _ _ _ _ _ _ Hsp F14) as A4.
    cbn [holds eval] in A1, A2, A3, A4. rewrite !u64_lit in A1, A2, A3, A4 by lia.
    pose proof (G13 rho HG) as V13. pose proof (G15 rho HG) as V15. cbn [eval] in V13, V15.
    assert (A0 : bv_unsigned (eval rho (reg_sv S 11)) = bv_unsigned (rw rho 10) + 8).
    { rewrite R11. apply (U_addc rho (SVar 10) 8 (bv_unsigned (rw rho 10))); [reflexivity | lia | lia]. }
    assert (A16 : bv_unsigned (eval rho (reg_sv S 11) + 16)%bv = bv_unsigned (rw rho 10) + 24) by (rewrite (U_bvadd _ _ _ _ A0 u16) by lia; lia).
    exists (eval rho e0), (eval rho l0), (eval rho (SVar 14)), (eval rho (SVar 15)).
    split; [eapply (iov_field rho S tr ms md 8); [exact Hsp | exact Hlen | exact Hrng | exact C8 | lia | lia]|].
    split; [eapply (iov_field rho S tr ms md 16); [exact Hsp | exact Hlen | exact Hrng | exact C16 | lia | rewrite (U_bvadd _ _ _ _ A0 u8) by lia; lia]|].
    split; [eapply (iov_field rho S tr ms md 24); [exact Hsp | exact Hlen | exact Hrng | exact C24 | lia | lia]|].
    split; [eapply (iov_field rho S tr ms md 32); [exact Hsp | exact Hlen | exact Hrng | exact C32 | lia | rewrite (U_bvadd _ _ _ _ A16 u8) by lia; lia]|].
    split.
    { pose proof rwmax as HM. rewrite MSG_len in HM.
      rewrite (list_read (DList 5) rho S tr ms md 1 12 13 5 (Z.of_nat n) L0 (eval rho e0) (eval rho l0) Hsp ltac:(lia) Hb1 eq_refl ltac:(lia) ltac:(rewrite V13; lia) ltac:(rewrite V13; lia) He0 Hl0).
      f_equal. rewrite Nat2Z.id, (G_rl rho 5 HG), Hrl5. apply firstn_all2. rewrite length_skipn. lia. }
    split.
    { pose proof rwmax as HM. rewrite MSG_len in HM.
      rewrite (list_read (DRom 6) rho S tr ms md 2 14 15 6 0 (length bs2) (eval rho (SVar 14)) (eval rho (SVar 15)) Hsp ltac:(lia) Hb2 eq_refl ltac:(lia) ltac:(rewrite V15; lia) ltac:(rewrite V15; lia) ltac:(cbn [eval]; lia) V15).
      f_equal. cbn [Z.to_nat skipn]. rewrite (G_rl rho 6 HG), Hrl6. apply firstn_all. }
    destruct (UR rho (SPp_facts segs _ _ _ _ _ Hsp)) as (U10 & U12 & U14).
    change (eval rho (SVar 14)) with (rw rho 14). change (eval rho (SVar 15)) with (rw rho 15).
    rewrite task_size_val. split; [rewrite H22, Hbs; reflexivity|]. split; [lia|]. split; [|exact U14].
    rewrite He0, Hl0. rewrite V13 in U12. lia.
Qed.

Lemma ewritev1 : ltac2:(tb__ "0|4|
ScSeSeSaS34S34S8eS2cS2dR6R5R4A5S5aR4A1S81P5cS11R8A1A2S0S36S1fS11R9A1S15R9Z16M0A2A2S37A3S1S57U1R6A2S57R6S35S7Q8A1M1Vbs2;A2M2A2A2S0S34R6S64S35G1Vbs1;A2S65G2R7A2A2A3S0S4S6Q40M3SbR9RaA2A2S44R8A1A3S0S4S6G3SbRaRcA2A2S43S6G3SdRaPeA2A2S44S65G2R9A2A1A2A3S0S4S6G3SbRbS15ReG0A2A2A2S44RaA1A3S68S2cS4aS2cS59RaA1RfRcA4S63RfS15RfG0A2RaRbRcA5A3F_;F_;F_;F_;F_;F_;F_;F_;F_;Fn0;FR;Frho;Fl1;Fe1;FS;").
Proof using HU15 Hfd Hmax Hrl6 cert_misc cert_runs wl_fd_rng.
  intros S e1 l1 rho R n0 HS HG Hn He HR Hn0 Hl1 He1 H22.
  destruct HS as [Hlen Hrng Hb2 C24 C32 R11 Hi H17 H10 H12 F10a F10b F14 UR].
  pose proof wl_fd_u as FD.
  set (J' := fun (r : valuation) (tr : list event) (md : Model) =>
               exists k, rw r (ss_next S) = Z_to_bv 64 (Z.of_nat k) /\ (1 <= k <= R)%nat /\ Kw (n0 + k) tr md).
  assert (Hbs : length (skipn (length bs2 - R) bs2) = R) by (rewrite length_skipn; lia).
  eapply etriple_conseq; [intros w Hw; exact Hw | |
    eapply (etriple_writev1J segs (liftK (Kw n0)) J' S rho wl_fd (skipn (length bs2 - R) bs2) (reg_sv S 22));
      [ exact Hi | exact H17 | exact H10 | exact H12 | exact wl_fd_rng | rewrite Hbs; pose proof rwmax as RWM; rewrite MSG_len in RWM; lia | exact He | | ]].
  - intros w (rho' & Hag & Hfull & Hsm & (k & Hk & Hkb & HK)). exists rho', k.
    split; [exact (G_agree _ _ _ Hag Hn HG)|]. split; [exact Hag|]. split; [exact Hk|]. split; [exact Hkb|].
    split; [rewrite Hbs in Hfull; exact Hfull|]. split; [exact Hsm | exact HK].
  - intros rho' tr md k Hag Hk HK Hkb. split; [exact (Kw_fd _ _ _ HK)|]. exists k. split; [exact Hk|].
    split; [rewrite Hbs in Hkb; exact Hkb|].
    replace (skipn (length bs2 - R) bs2) with (skipn n0 MSG) by (unfold MSG; rewrite skipn_app, skipn_all2 by lia; cbn [app]; f_equal; lia).
    apply Kw_step. exact HK.
  - intros tr ms md Hsp HK.
    pose proof (SPp_fact segs _ _ _ _ _ _ Hsp F10a) as A1. pose proof (SPp_fact segs _ _ _ _ _ _ Hsp F10b) as A2.
    pose proof (SPp_fact segs _ _ _ _ _ _ Hsp F14) as A4.
    cbn [holds eval] in A1, A2, A4. rewrite !u64_lit in A1, A2, A4 by lia.
    pose proof (G15 rho HG) as V15. cbn [eval] in V15.
    assert (A0 : bv_unsigned (eval rho (reg_sv S 11)) = bv_unsigned (rw rho 10) + 24).
    { rewrite R11. apply (U_addc rho (SVar 10) 24 (bv_unsigned (rw rho 10))); [reflexivity | lia | lia]. }
    exists (eval rho e1), (eval rho l1).
    split; [eapply (iov_field rho S tr ms md 24); [exact Hsp | exact Hlen | exact Hrng | exact C24 | lia | lia]|].
    split; [eapply (iov_field rho S tr ms md 32); [exact Hsp | exact Hlen | exact Hrng | exact C32 | lia | rewrite (U_bvadd _ _ _ _ A0 u8) by lia; lia]|].
    split.
    { pose proof rwmax as HM. rewrite MSG_len in HM.
      rewrite (list_read (DRom 6) rho S tr ms md 2 14 15 6 (Z.of_nat (length bs2 - R)) R (eval rho e1) (eval rho l1) Hsp ltac:(lia) Hb2 eq_refl ltac:(lia) ltac:(rewrite V15; lia) ltac:(rewrite V15; lia) He1 Hl1).
      f_equal. rewrite Nat2Z.id, (G_rl rho 6 HG), Hrl6. apply firstn_all2. rewrite length_skipn. lia. }
    destruct (UR rho (SPp_facts segs _ _ _ _ _ Hsp)) as (U10 & U14).
    rewrite task_size_val. split; [rewrite H22, Hbs; reflexivity|]. split; [lia|].
    rewrite He1, Hl1. rewrite V15 in U14. lia.
Qed.

Lemma G0 : G rho0. Proof using . apply agree_below_refl. Qed.

Lemma SP_Kw0 : ltac2:(tb__ "0|0|
ScSaS66S4aS2cVK;R3R2R1A5S4aS2cS59U0A1R4R3R2A5F_;Fw;Frho;FS;").
Proof using . intros S rho w [Hsm Hk]. split; [exact Hsm|]. exists (w_tr w). split; [exact Hk|]. unfold TRk. cbn. rewrite app_nil_r. reflexivity. Qed.

Theorem wl2_sum : ltac2:(tb__ "0|1|
S57U1S35S7Q8A1M0Vbs1;A2A2S67S2cVok;S4aS2cVK;S30Vrho0;A4S4bS2cS59S35G0S5bA2A1P5cVrho0;S5eA5A4F_;").
Proof using HU13 HU15 Hfd Hmax HokK HokP Hrl5 Hrl6 PA2_eq PA2a_eq PA2b_eq PB1_eq PB2_eq PB2a_eq PB2b_eq cert_misc cert_pre cert_runs ent_PA2a_CB2 ent_PA2a_D ent_PA2b_CB1 ent_PA2b_D ent_PB1_CB1 ent_PB1_D ent_PB2a_CB2 ent_PB2a_D ent_PB2b_CB1 ent_PB2b_D run_PA2a run_PA2b run_PB1 run_PB2a run_PB2b site_CB1 site_CB2 site_Pre_wl2 subs_id sv93 wl_fd_rng.
  intros Hbs1. pose proof rwmax as RWM. rewrite MSG_len in RWM.
  pose proof subs_id as SI. cbn [forallb] in SI.
  apply andb_prop in SI as [S1 SI]. apply andb_prop in SI as [S2 SI]. apply andb_prop in SI as [S3 SI].
  apply andb_prop in SI as [S4 SI]. apply andb_prop in SI as [S5 SI]. apply andb_prop in SI as [S6 SI].
  apply andb_prop in SI as [S7 SI]. apply andb_prop in SI as [S8 SI]. apply andb_prop in SI as [S9 SI].
  apply andb_prop in SI as [S10 SI]. apply andb_prop in SI as [S11 SI]. apply andb_prop in SI as [S12 _].
  destruct cert_misc as (Nx2 & R22b & Nx1 & R22c & Nx0 & R22a & _ & _ & _ & _ & _ & _ & _ & _ & FPA2ad & FPA2ae & FPA2bd & FPA2be & _ & _).
  destruct cert_runs as (NxPA2a & NxPA2b & _ & _ & _ & _ & StPA2a & StPA2b & _ & _ & _ & _).
  destruct sv93 as (CVa & _ & CVb & _ & _ & _).
  destruct cert_pre as (B22 & _ & _ & _ & F12 & _).
  eapply triple_conseq; [intros w Hw; exact (SP_Kw0 _ _ _ Hw) | intros w Hw; exact Hw |].
  apply triple_facts. intros HF.
  assert (B12 : bv_unsigned (rw rho0 12) <= 2 ^ 62).
  { pose proof (proj1 (Forall_forall _ _) HF _ F12) as X. cbn [holds eval] in X. rewrite u64_lit in X by lia. exact X. }
  pose proof (urange (rw rho0 12)) as UR12.
  eapply triple_seq.
  { replace 0%nat with (length bs1 - length bs1)%nat by lia.
    apply (writev2 Pre_wl2 (SVar 12) (SVar 13) rho0 (length bs1) site_Pre_wl2 G0); [rewrite Nx0; lia | rewrite Nx0; exact B22 | lia | lia | cbn [eval]; exact HU13 | cbn [eval]; lia |].
    rewrite R22a, Nat2Z.inj_add. apply (U_add2 rho0 (SVar 13) (SVar 15)); [cbn [eval]; exact HU13 | cbn [eval]; exact HU15 | lia]. }
  apply triple_ex; intros rho1. apply triple_ex; intros k.
  apply triple_pure; intros HG1. apply triple_pure; intros Hag1. apply triple_pure; intros Hk. apply triple_pure; intros Hkb.
  rewrite Nx0 in Hk, Hag1. replace (length bs1 - length bs1 + k)%nat with k by lia.
  assert (U92 : bv_unsigned (rw rho1 92) = Z.of_nat k) by (rewrite Hk; apply Z_to_bv_small; rewrite two64; lia).
  pose proof (G13 rho1 HG1) as V13. pose proof (G15 rho1 HG1) as V15. cbn [eval] in V13, V15.
  eapply triple_conseq with (P := SP segs (Kw k) PA2 rho1); [| intros w Hw; exact Hw |].
  { intros w Hw. rewrite <- PA2_eq. apply SP_addn; [exact Hw | | apply after_write_below; exact Nx0]. constructor; [|constructor].
    cbn [holds eval]. rewrite U92, u64_lit by lia. lia. }
  destruct (Nat.le_gt_cases k (length bs1)) as [Hle|Hgt].
  - eapply triple_conseq with (P := SP segs (Kw k) PA2a rho1); [| intros w Hw; exact Hw |].
    { intros w Hw. rewrite <- PA2a_eq. apply SP_add1; [exact Hw | | apply (below_of_eq _ _ _ _ _ PA2a_eq NxPA2a); reflexivity]. cbn [holds eval branch_taken]. unfold bv_ltu.
      rewrite V13, U92. destruct (Z.ltb_spec (Z.of_nat (length bs1)) (Z.of_nat k)); [lia | discriminate]. }
    eapply run_tr; [exact run_PA2a | exact StPA2a | apply HokK |].
    intros L rho2 [<-|[<-|[]]] Hag2; cbn [lf_state]; rewrite NxPA2a in Hag2.
    +
      apply triple_facts. intros HF2. rewrite FPA2ae in HF2.
      apply Forall_inv in HF2. cbn [holds branch_taken eval] in HF2. unfold bv_eqb in HF2. apply negb_true_iff in HF2. rewrite Z.eqb_neq in HF2.
      rewrite <- (proj1 Hag2 92%positive ltac:(cbn; lia)), U92 in HF2.
      rewrite (alu_add2 (rw rho2 13) (rw rho2 15) (Z.of_nat (length bs1)) (Z.of_nat (length bs2))) in HF2;
        [| rewrite <- (proj1 Hag2 13%positive ltac:(cbn; lia)); exact V13
         | rewrite <- (proj1 Hag2 15%positive ltac:(cbn; lia)); exact V15 | lia].
      assert (EL : P_of (rho_sub rho2 s_PA2a_CB2) = (length bs1 - k)%nat).
      { unfold P_of. cbn [rho_sub rw]. rewrite CVa.
        rewrite (U_sub2 rho2 (SVar 13) (SVar 92) (Z.of_nat (length bs1)) (Z.of_nat k)); [lia | | | lia]; cbn [eval];
          rewrite <- ?(proj1 Hag2 13%positive ltac:(cbn; lia)), <- ?(proj1 Hag2 92%positive ltac:(cbn; lia)); [exact V13 | exact U92]. }
      eapply triple_conseq; [| intros w Hw; exact Hw | apply (proj1 (loop (length bs1 - k + length bs2)) (rho_sub rho2 s_PA2a_CB2))].
      * intros w Hw. eapply SP_entails in Hw; [|exact ent_PA2a_CB2]. rewrite EL.
        replace (length bs1 - (length bs1 - k))%nat with k by lia. exact Hw.
      * apply G_sub; [exact S1|]. eapply G_agree; [exact Hag2 | cbn; lia | exact HG1].
      * rewrite EL. lia.
      * rewrite EL. clear -Hle Hkb HF2 Hbs1. lia.
      * rewrite EL. lia.
    +
      eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
      intros w Hw. pose proof (hd_fact segs rho2 L_PA2a_d _ _ w _ FPA2ad Hw) as Hf.
      cbn [holds branch_taken eval] in Hf. unfold bv_eqb in Hf. apply negb_neq_true in Hf. apply Z.eqb_eq in Hf.
      rewrite <- (proj1 Hag2 92%positive ltac:(cbn; lia)), U92 in Hf.
      rewrite (alu_add2 (rw rho2 13) (rw rho2 15) (Z.of_nat (length bs1)) (Z.of_nat (length bs2))) in Hf;
        [| rewrite <- (proj1 Hag2 13%positive ltac:(cbn; lia)); exact V13
         | rewrite <- (proj1 Hag2 15%positive ltac:(cbn; lia)); exact V15 | lia].
      apply (to_D _ _ rho2 k w ent_PA2a_D S7 ltac:(eapply G_agree; [exact Hag2 | cbn; lia | exact HG1]) ltac:(clear -Hf; rewrite MSG_len; lia) Hw).
  - eapply triple_conseq with (P := SP segs (Kw k) PA2b rho1); [| intros w Hw; exact Hw |].
    { intros w Hw. rewrite <- PA2b_eq. apply SP_add1; [exact Hw | | apply (below_of_eq _ _ _ _ _ PA2b_eq NxPA2b); reflexivity]. cbn [holds eval branch_taken]. unfold bv_ltu.
      rewrite V13, U92. destruct (Z.ltb_spec (Z.of_nat (length bs1)) (Z.of_nat k)); [reflexivity | lia]. }
    eapply run_tr; [exact run_PA2b | exact StPA2b | apply HokK |].
    intros L rho2 [<-|[<-|[]]] Hag2; cbn [lf_state]; rewrite NxPA2b in Hag2.
    +
      apply triple_facts. intros HF2. rewrite FPA2be in HF2.
      apply Forall_inv in HF2. cbn [holds branch_taken eval] in HF2. unfold bv_eqb in HF2. apply negb_true_iff in HF2. rewrite Z.eqb_neq in HF2.
      rewrite <- (proj1 Hag2 92%positive ltac:(cbn; lia)), U92 in HF2.
      rewrite (alu_add2 (rw rho2 13) (rw rho2 15) (Z.of_nat (length bs1)) (Z.of_nat (length bs2))) in HF2;
        [| rewrite <- (proj1 Hag2 13%positive ltac:(cbn; lia)); exact V13
         | rewrite <- (proj1 Hag2 15%positive ltac:(cbn; lia)); exact V15 | lia].
      assert (ER : P_of (rho_sub rho2 s_PA2b_CB1) = (length bs1 + length bs2 - k)%nat).
      { unfold P_of. cbn [rho_sub rw]. rewrite CVb.
        rewrite (U_sub2 rho2 (SVar 15) _ (Z.of_nat (length bs2)) (Z.of_nat k - Z.of_nat (length bs1))); [lia | | | lia].
        - cbn [eval]. rewrite <- (proj1 Hag2 15%positive ltac:(cbn; lia)). exact V15.
        - apply (U_sub2 rho2 (SVar 92) (SVar 13)); [| | lia]; cbn [eval];
            rewrite <- ?(proj1 Hag2 13%positive ltac:(cbn; lia)), <- ?(proj1 Hag2 92%positive ltac:(cbn; lia)); [exact U92 | exact V13]. }
      eapply triple_conseq; [| intros w Hw; exact Hw | apply (proj2 (loop (length bs1 + length bs2 - k)) (rho_sub rho2 s_PA2b_CB1))].
      * intros w Hw. eapply SP_entails in Hw; [|exact ent_PA2b_CB1]. rewrite ER.
        replace (length bs1 + (length bs2 - (length bs1 + length bs2 - k)))%nat with k by lia. exact Hw.
      * apply G_sub; [exact S3|]. eapply G_agree; [exact Hag2 | cbn; lia | exact HG1].
      * rewrite ER. clear -Hgt Hkb HF2. lia.
      * rewrite ER. lia.
    +
      eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
      intros w Hw. pose proof (hd_fact segs rho2 L_PA2b_d _ _ w _ FPA2bd Hw) as Hf.
      cbn [holds branch_taken eval] in Hf. unfold bv_eqb in Hf. apply negb_neq_true in Hf. apply Z.eqb_eq in Hf.
      rewrite <- (proj1 Hag2 92%positive ltac:(cbn; lia)), U92 in Hf.
      rewrite (alu_add2 (rw rho2 13) (rw rho2 15) (Z.of_nat (length bs1)) (Z.of_nat (length bs2))) in Hf;
        [| rewrite <- (proj1 Hag2 13%positive ltac:(cbn; lia)); exact V13
         | rewrite <- (proj1 Hag2 15%positive ltac:(cbn; lia)); exact V15 | lia].
      apply (to_D _ _ rho2 k w ent_PA2b_D S8 ltac:(eapply G_agree; [exact Hag2 | cbn; lia | exact HG1]) ltac:(clear -Hf; rewrite MSG_len; lia) Hw).
Qed.

Theorem wl1_sum : ltac2:(tb__ "0|1|
S0S33S7Q8A1M0A1Vbs1;S3aG0A1A3S57U1S35G0Vbs2;A2A2S67S2cVok;S4aS2cVK;S2fVrho0;A4S4bS2cS59S35G0S5bA2A1P5cVrho0;S5eA5A4F_;F_;").
Proof using HU13 HU15 Hfd Hmax HokK HokP Hrl5 Hrl6 PA1_eq PB1_eq PB2_eq PB2a_eq PB2b_eq cert_misc cert_pre cert_runs ent_PA1_CB1 ent_PA1_D ent_PB1_CB1 ent_PB1_D ent_PB2a_CB2 ent_PB2a_D ent_PB2b_CB1 ent_PB2b_D run_PA1 run_PB1 run_PB2a run_PB2b site_CB1 site_CB2 site_Pre_wl1 subs_id sv93 wl_fd_rng.
  intros Hnil Hbs2. pose proof rwmax as RWM. rewrite MSG_len in RWM.
  assert (L1z : length bs1 = 0%nat) by (rewrite Hnil; reflexivity).
  pose proof subs_id as SI. cbn [forallb] in SI.
  apply andb_prop in SI as [S1 SI]. apply andb_prop in SI as [S2 SI]. apply andb_prop in SI as [S3 SI].
  apply andb_prop in SI as [S4 SI]. apply andb_prop in SI as [S5 SI]. apply andb_prop in SI as [S6 SI].
  apply andb_prop in SI as [S7 SI]. apply andb_prop in SI as [S8 SI]. apply andb_prop in SI as [S9 SI].
  apply andb_prop in SI as [S10 SI]. apply andb_prop in SI as [S11 SI]. apply andb_prop in SI as [S12 _].
  destruct cert_misc as (Nx2 & R22b & Nx1 & R22c & Nx0 & R22a & Nx0' & R22a' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FPA1d & FPA1e).
  destruct cert_runs as (_ & _ & _ & _ & _ & NxPA1 & _ & _ & _ & _ & _ & StPA1).
  destruct sv93 as (_ & _ & _ & _ & _ & CVc).
  destruct cert_pre as (_ & B22 & _ & _ & _ & F14).
  eapply triple_conseq; [intros w Hw; exact (SP_Kw0 _ _ _ Hw) | intros w Hw; exact Hw |].
  apply triple_facts. intros HF.
  assert (B14 : bv_unsigned (rw rho0 14) <= 2 ^ 62).
  { pose proof (proj1 (Forall_forall _ _) HF _ F14) as X. cbn [holds eval] in X. rewrite u64_lit in X by lia. exact X. }
  pose proof (urange (rw rho0 14)) as UR14.
  eapply triple_seq.
  { apply (writev1 Pre_wl1 (SVar 14) (SVar 15) rho0 (length bs2) 0%nat site_Pre_wl1 G0); [rewrite Nx0'; lia | rewrite Nx0'; exact B22 | lia | lia | cbn [eval]; exact HU15 | cbn [eval]; lia |].
    rewrite R22a'. cbn [eval]. exact HU15. }
  apply triple_ex; intros rho1. apply triple_ex; intros k.
  apply triple_pure; intros HG1. apply triple_pure; intros Hag1. apply triple_pure; intros Hk. apply triple_pure; intros Hkb.
  rewrite Nx0' in Hk, Hag1. cbn [Nat.add].
  assert (U92 : bv_unsigned (rw rho1 92) = Z.of_nat k) by (rewrite Hk; apply Z_to_bv_small; rewrite two64; lia).
  pose proof (G15 rho1 HG1) as V15. cbn [eval] in V15.
  eapply triple_conseq with (P := SP segs (Kw k) PA1 rho1); [| intros w Hw; exact Hw |].
  { intros w Hw. rewrite <- PA1_eq. apply SP_addn; [exact Hw | | apply after_write_below; exact Nx0']. constructor; [|constructor].
    cbn [holds eval]. rewrite U92, u64_lit by lia. lia. }
  eapply run_tr; [exact run_PA1 | exact StPA1 | apply HokK |].
  intros L rho2 [<-|[<-|[]]] Hag2; cbn [lf_state]; rewrite NxPA1 in Hag2.
  -
    apply triple_facts. intros HF2. rewrite FPA1e in HF2.
    apply Forall_inv in HF2. cbn [holds branch_taken eval] in HF2. unfold bv_eqb in HF2. apply negb_true_iff in HF2. rewrite Z.eqb_neq in HF2.
    rewrite <- (proj1 Hag2 92%positive ltac:(cbn; lia)), <- (proj1 Hag2 15%positive ltac:(cbn; lia)), U92, V15 in HF2.
    assert (ER : P_of (rho_sub rho2 s_PA1_CB1) = (length bs2 - k)%nat).
    { unfold P_of. cbn [rho_sub rw]. rewrite CVc.
      rewrite (U_sub2 rho2 (SVar 15) (SVar 92) (Z.of_nat (length bs2)) (Z.of_nat k)); [lia | | | lia]; cbn [eval];
        rewrite <- ?(proj1 Hag2 15%positive ltac:(cbn; lia)), <- ?(proj1 Hag2 92%positive ltac:(cbn; lia)); [exact V15 | exact U92]. }
    eapply triple_conseq; [| intros w Hw; exact Hw | apply (proj2 (loop (length bs2 - k)) (rho_sub rho2 s_PA1_CB1))].
    + intros w Hw. eapply SP_entails in Hw; [|exact ent_PA1_CB1]. rewrite ER, L1z.
      replace (0 + (length bs2 - (length bs2 - k)))%nat with k by lia. exact Hw.
    + apply G_sub; [exact S6|]. eapply G_agree; [exact Hag2 | cbn; lia | exact HG1].
    + rewrite ER. clear -Hkb HF2. lia.
    + rewrite ER. lia.
  -
    eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
    intros w Hw. pose proof (hd_fact segs rho2 L_PA1_d _ _ w _ FPA1d Hw) as Hf.
    cbn [holds branch_taken eval] in Hf. unfold bv_eqb in Hf. apply negb_neq_true in Hf. apply Z.eqb_eq in Hf.
    rewrite <- (proj1 Hag2 92%positive ltac:(cbn; lia)), <- (proj1 Hag2 15%positive ltac:(cbn; lia)), U92, V15 in Hf.
    apply (to_D _ _ rho2 k w ent_PA1_D S12 ltac:(eapply G_agree; [exact Hag2 | cbn; lia | exact HG1]) ltac:(clear -Hf L1z; rewrite MSG_len; lia) Hw).
Qed.

Definition eQD : world -> Prop := ltac2:(tb__ "0|0|
S4bS2cS59S35S7Q8A1S5bA2A1P5cVrho0;S5eA5").

Lemma eto_D : ltac2:(tb__ "0|0|
ScS84SaS34S66S0S36S89R5S2eR4A3S37A3S0S36S8dR5A1S37A3S5aR5A1S0S34R5S35S7Q8A1S5bA2A3S4aS2cS59R6A1R9R7R5A5S61R6A1F_;F_;F_;F_;F_;Fw;Fn;Frho;FsD;FL;").
Proof using cert_misc cert_runs. intros. eapply to_D; eauto. Qed.

Lemma k_full : ltac2:(tb__ "0|4|
S7Q40M0A1M1S34S34S0G1R3S8G0S44R2A1A2M2A3S0G1R4G2A3S46S44R4A1S45Z2Z40A2A2M3G3S0S34R6R5A3F_;F_;F_;F_;Flen;Fk;Fr;").
Proof using bs1 bs2 cert_misc cert_runs.
  intros r k len H1 H2 Hk Hl. rewrite H1 in H2. apply (f_equal bv_unsigned) in H2.
  rewrite !Z_to_bv_small in H2 by (rewrite two64; lia). lia.
Qed.

Theorem wl2_sum_ex : ltac2:(tb__ "0|0|
S57U1S35S7Q8A1Vbs1;A2A2S68S2cS4aS2cVK;S30Vrho0;A4S61A3F_;").
Proof using HU13 HU15 Hfd Hmax Hrl5 Hrl6 PA2_eq PA2a_eq PA2b_eq cert_misc cert_pre cert_runs ent_PA2a_D ent_PA2b_D run_PA2a run_PA2b site_Pre_wl2 subs_id wl_fd_rng.
  intros Hbs1. pose proof rwmax as RWM. rewrite MSG_len in RWM.
  pose proof subs_id as SI. cbn [forallb] in SI.
  apply andb_prop in SI as [S1 SI]. apply andb_prop in SI as [S2 SI]. apply andb_prop in SI as [S3 SI].
  apply andb_prop in SI as [S4 SI]. apply andb_prop in SI as [S5 SI]. apply andb_prop in SI as [S6 SI].
  apply andb_prop in SI as [S7 SI]. apply andb_prop in SI as [S8 SI]. apply andb_prop in SI as [S9 SI].
  apply andb_prop in SI as [S10 SI]. apply andb_prop in SI as [S11 SI]. apply andb_prop in SI as [S12 _].
  destruct cert_misc as (Nx2 & R22b & Nx1 & R22c & Nx0 & R22a & _ & _ & _ & _ & _ & _ & _ & _ & FPA2ad & FPA2ae & FPA2bd & FPA2be & _ & _).
  destruct cert_runs as (NxPA2a & NxPA2b & _ & _ & _ & _ & StPA2a & StPA2b & _ & _ & _ & _).
  destruct cert_pre as (B22 & _ & _ & _ & F12 & _).
  intros w0 Hw0. apply SP_Kw0 in Hw0.
  pose proof (SP_facts_hold segs _ _ _ _ Hw0) as HF.
  assert (B12 : bv_unsigned (rw rho0 12) <= 2 ^ 62).
  { pose proof (proj1 (Forall_forall _ _) HF _ F12) as X. cbn [holds eval] in X. rewrite u64_lit in X by lia. exact X. }
  pose proof (urange (rw rho0 12)) as UR12.
  revert w0 Hw0. eapply etriple_seq.
  { replace 0%nat with (length bs1 - length bs1)%nat by lia.
    apply (ewritev2 Pre_wl2 (SVar 12) (SVar 13) rho0 (length bs1) site_Pre_wl2 G0); [rewrite Nx0; lia | rewrite Nx0; exact B22 | lia | lia | cbn [eval]; exact HU13 | cbn [eval]; lia |].
    rewrite R22a, Nat2Z.inj_add. apply (U_add2 rho0 (SVar 13) (SVar 15)); [cbn [eval]; exact HU13 | cbn [eval]; exact HU15 | lia]. }
  apply etriple_ex; intros rho1. apply etriple_ex; intros k.
  apply etriple_pure; intros HG1. apply etriple_pure; intros Hag1. apply etriple_pure; intros Hk. apply etriple_pure; intros Hkb. apply etriple_pure; intros Hfull.
  rewrite Nx0 in Hk, Hag1, Hfull. replace (length bs1 - length bs1 + k)%nat with k by lia.
  pose proof (k_full _ _ _ Hk Hfull ltac:(lia) ltac:(lia)) as Ek.
  assert (U92 : bv_unsigned (rw rho1 92) = Z.of_nat k) by (rewrite Hk; apply Z_to_bv_small; rewrite two64; lia).
  pose proof (G13 rho1 HG1) as V13. pose proof (G15 rho1 HG1) as V15. cbn [eval] in V13, V15.
  eapply etriple_conseq with (P := SP segs (Kw k) PA2 rho1); [| intros w Hw; exact Hw |].
  { intros w Hw. rewrite <- PA2_eq. apply SP_addn; [exact Hw | | apply after_write_below; exact Nx0]. constructor; [|constructor].
    cbn [holds eval]. rewrite U92, u64_lit by lia. lia. }
  destruct (Nat.le_gt_cases k (length bs1)) as [Hle|Hgt].
  - eapply etriple_conseq with (P := SP segs (Kw k) PA2a rho1); [| intros w Hw; exact Hw |].
    { intros w Hw. rewrite <- PA2a_eq. apply SP_add1; [exact Hw | | apply (below_of_eq _ _ _ _ _ PA2a_eq NxPA2a); reflexivity]. cbn [holds eval branch_taken]. unfold bv_ltu.
      rewrite V13, U92. destruct (Z.ltb_spec (Z.of_nat (length bs1)) (Z.of_nat k)); [lia | discriminate]. }
    eapply erun_tr; [exact run_PA2a | exact StPA2a |].
    intros L rho2 [<-|[<-|[]]] Hag2; cbn [lf_state]; rewrite NxPA2a in Hag2; intros w Hw.
    + exfalso. pose proof (hd_fact segs rho2 L_PA2a_e _ _ w _ FPA2ae Hw) as Hf.
      cbn [holds branch_taken eval] in Hf. unfold bv_eqb in Hf. apply negb_true_iff in Hf. rewrite Z.eqb_neq in Hf.
      rewrite <- (proj1 Hag2 92%positive ltac:(cbn; lia)), U92 in Hf.
      rewrite (alu_add2 (rw rho2 13) (rw rho2 15) (Z.of_nat (length bs1)) (Z.of_nat (length bs2))) in Hf;
        [| rewrite <- (proj1 Hag2 13%positive ltac:(cbn; lia)); exact V13
         | rewrite <- (proj1 Hag2 15%positive ltac:(cbn; lia)); exact V15 | lia]. clear -Hf Ek. lia.
    + exists w. split; [apply wsteps_refl|].
      apply (eto_D _ _ rho2 k w ent_PA2a_D S7 ltac:(eapply G_agree; [exact Hag2 | cbn; lia | exact HG1]) ltac:(clear -Ek; rewrite MSG_len; lia) Hw).
  - eapply etriple_conseq with (P := SP segs (Kw k) PA2b rho1); [| intros w Hw; exact Hw |].
    { intros w Hw. rewrite <- PA2b_eq. apply SP_add1; [exact Hw | | apply (below_of_eq _ _ _ _ _ PA2b_eq NxPA2b); reflexivity]. cbn [holds eval branch_taken]. unfold bv_ltu.
      rewrite V13, U92. destruct (Z.ltb_spec (Z.of_nat (length bs1)) (Z.of_nat k)); [reflexivity | lia]. }
    eapply erun_tr; [exact run_PA2b | exact StPA2b |].
    intros L rho2 [<-|[<-|[]]] Hag2; cbn [lf_state]; rewrite NxPA2b in Hag2; intros w Hw.
    + exfalso. pose proof (hd_fact segs rho2 L_PA2b_e _ _ w _ FPA2be Hw) as Hf.
      cbn [holds branch_taken eval] in Hf. unfold bv_eqb in Hf. apply negb_true_iff in Hf. rewrite Z.eqb_neq in Hf.
      rewrite <- (proj1 Hag2 92%positive ltac:(cbn; lia)), U92 in Hf.
      rewrite (alu_add2 (rw rho2 13) (rw rho2 15) (Z.of_nat (length bs1)) (Z.of_nat (length bs2))) in Hf;
        [| rewrite <- (proj1 Hag2 13%positive ltac:(cbn; lia)); exact V13
         | rewrite <- (proj1 Hag2 15%positive ltac:(cbn; lia)); exact V15 | lia]. clear -Hf Ek. lia.
    + exists w. split; [apply wsteps_refl|].
      apply (eto_D _ _ rho2 k w ent_PA2b_D S8 ltac:(eapply G_agree; [exact Hag2 | cbn; lia | exact HG1]) ltac:(clear -Ek; rewrite MSG_len; lia) Hw).
Qed.

Theorem wl1_sum_ex : ltac2:(tb__ "0|1|
S0S33S7Q8A1M0A1Vbs1;S3aG0A1A3S57U1S35G0Vbs2;A2A2S68S2cS4aS2cVK;S2fVrho0;A4S61A3F_;F_;").
Proof using HU15 Hfd Hmax Hrl6 PA1_eq cert_misc cert_pre cert_runs ent_PA1_D run_PA1 site_Pre_wl1 subs_id wl_fd_rng.
  intros Hnil Hbs2. pose proof rwmax as RWM. rewrite MSG_len in RWM.
  assert (L1z : length bs1 = 0%nat) by (rewrite Hnil; reflexivity).
  pose proof subs_id as SI. cbn [forallb] in SI.
  apply andb_prop in SI as [S1 SI]. apply andb_prop in SI as [S2 SI]. apply andb_prop in SI as [S3 SI].
  apply andb_prop in SI as [S4 SI]. apply andb_prop in SI as [S5 SI]. apply andb_prop in SI as [S6 SI].
  apply andb_prop in SI as [S7 SI]. apply andb_prop in SI as [S8 SI]. apply andb_prop in SI as [S9 SI].
  apply andb_prop in SI as [S10 SI]. apply andb_prop in SI as [S11 SI]. apply andb_prop in SI as [S12 _].
  destruct cert_misc as (Nx2 & R22b & Nx1 & R22c & Nx0 & R22a & Nx0' & R22a' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FPA1d & FPA1e).
  destruct cert_runs as (_ & _ & _ & _ & _ & NxPA1 & _ & _ & _ & _ & _ & StPA1).
  destruct cert_pre as (_ & B22 & _ & _ & _ & F14).
  intros w0 Hw0. apply SP_Kw0 in Hw0.
  pose proof (SP_facts_hold segs _ _ _ _ Hw0) as HF.
  assert (B14 : bv_unsigned (rw rho0 14) <= 2 ^ 62).
  { pose proof (proj1 (Forall_forall _ _) HF _ F14) as X. cbn [holds eval] in X. rewrite u64_lit in X by lia. exact X. }
  pose proof (urange (rw rho0 14)) as UR14.
  revert w0 Hw0. eapply etriple_seq.
  { apply (ewritev1 Pre_wl1 (SVar 14) (SVar 15) rho0 (length bs2) 0%nat site_Pre_wl1 G0); [rewrite Nx0'; lia | rewrite Nx0'; exact B22 | lia | lia | cbn [eval]; exact HU15 | cbn [eval]; lia |].
    rewrite R22a'. cbn [eval]. exact HU15. }
  apply etriple_ex; intros rho1. apply etriple_ex; intros k.
  apply etriple_pure; intros HG1. apply etriple_pure; intros Hag1. apply etriple_pure; intros Hk. apply etriple_pure; intros Hkb. apply etriple_pure; intros Hfull.
  rewrite Nx0' in Hk, Hag1, Hfull. cbn [Nat.add].
  pose proof (k_full _ _ _ Hk Hfull ltac:(lia) ltac:(lia)) as Ek.
  assert (U92 : bv_unsigned (rw rho1 92) = Z.of_nat k) by (rewrite Hk; apply Z_to_bv_small; rewrite two64; lia).
  pose proof (G15 rho1 HG1) as V15. cbn [eval] in V15.
  eapply etriple_conseq with (P := SP segs (Kw k) PA1 rho1); [| intros w Hw; exact Hw |].
  { intros w Hw. rewrite <- PA1_eq. apply SP_addn; [exact Hw | | apply after_write_below; exact Nx0']. constructor; [|constructor].
    cbn [holds eval]. rewrite U92, u64_lit by lia. lia. }
  eapply erun_tr; [exact run_PA1 | exact StPA1 |].
  intros L rho2 [<-|[<-|[]]] Hag2; cbn [lf_state]; rewrite NxPA1 in Hag2; intros w Hw.
  - exfalso. pose proof (hd_fact segs rho2 L_PA1_e _ _ w _ FPA1e Hw) as Hf.
    cbn [holds branch_taken eval] in Hf. unfold bv_eqb in Hf. apply negb_true_iff in Hf. rewrite Z.eqb_neq in Hf.
    rewrite <- (proj1 Hag2 92%positive ltac:(cbn; lia)), <- (proj1 Hag2 15%positive ltac:(cbn; lia)), U92, V15 in Hf. clear -Hf Ek. lia.
  - exists w. split; [apply wsteps_refl|].
    apply (eto_D _ _ rho2 k w ent_PA1_D S12 ltac:(eapply G_agree; [exact Hag2 | cbn; lia | exact HG1]) ltac:(clear -Ek L1z; rewrite MSG_len; lia) Hw).
Qed.
End WL.
End WLProof.
