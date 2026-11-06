(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sstate"; "valuation"; "sobj"; "sprop"; "ss_next"; "ss_facts"; "cell"; "holds"; "SLit"; "ss_objs"; "mem_match"; "obj_holds"; "ob_base"; "ob_cells"; "obj_range"; "ob_dflt"; "ob_hi"; "ob_lo"; "sv_eqb"; "odefault"; "smatch"; "sprop_eqb"; "eval"; "sv_below"; "SPBranch"; "SPNot"; "c_off"; "c_val"; "c_width"; "enc_bytes"; "mkCell"; "mkObj"; "pairwise_disjoint"; "tfact"; "agree_below"; "cell_holds"; "oaddr"; "obj_hi_of"; "obj_lo_of"; "rd_bytes"; "sprop_below"; "ss_lenient"; "swf"; "@Corelib.Init.Datatypes"; "bool"; "list"; "false"; "true"; "prod"; "option"; "app"; "fst"; "snd"; "Some"; "andb"; "nat"; "cons"; "pair"; "None"; "nil"; "orb"; "S"; "negb"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "jpred"; "LQ"; "LQJ"; "SP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA"; "amode"; "JGA"; "aedesc"; "ANone"; "ad_state"; "am_below"; "am_eqb"; "JGA_pre"; "PostsCA"; "ad_am"; "ad_tv"; "am_subst"; "XA"; "ad_rank"; "ad_var"; "ameas"; "hdr_obj"; "nodes_ok"; "AHead"; "amL_ok"; "eecheckA"; "ejcertA"; "new_objs_okA"; "pl_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "nth_error"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "eqb"; "leb"; "add"; "ltb"; "opp"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAx"; "nstep"; "run_nsteps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "rho_absorb"; "rho_sub"; "wsub_get"; "wsub_id_below"; "sv_subst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "LQP"; "jpost"; "import_post"; "call_check"; "J_ofP"; "call_checkP"; "call_link"; "call_linkP"; "import_okP"; "import_sub"; "wsub_dom_below"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "firstn"; "skipn"; "nth"; "@LinuxProcessSemantics.Riscv.Instr"; "mulop"; "aluop"; "BC_EQ"; "branch_cond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx"; "emeasZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "set_objs"; "uleq"; "lf_state"; "sym_run"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "remove_nth"; "tv_below"; "pclF"; "JG_pre"; "PostsC"; "call_checkT"; "robjs_check"; "tv_sub_eqb"; "tvz"; "FBx"; "T_after"; "tnz"; "tvd"; "tvv"; "T_afterN"; "T_ok"; "caddr"; "fbin"; "import_tv"; "malloc_contracts"; "malloc_contracts_ex"; "tvL_ok"; "tvin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy.ClientSite"; "cdesc"; "posts_check"; "post_check"; "site_check"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "with_facts"; "same_but_objs"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "entails"; "@Stdlib.Sorting.Permutation"; "Permutation";
"@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy.JA"; "null_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy.Kit"; "subsetb"; "gc_facts"; "gcS"; "renormK"; "sv_closed"; "cont_check"; "reent_check"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy.Sub"; "add_subcells"; "add_subcell"; "has_zero8_over"; "small_lit"; "subcell_ok"; "subcells_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy.ContA.TRX"; "landAs_check"; "landA_check"; "contA_check"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy.ContA"; "entA_check"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy.Emp"; "empty_obj_check"; "empty_obj_check2"; "sv_zero"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy.Join"; "has_zero4_at"; "add_cell8"; "join_ok"; "joincell_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy.NoneMode"; "PDAnone"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "ma_L"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "edge"; "infer_sub"; "add_facts"; "leaves_edges"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy.PureSite"; "pposts_check"; "ppost_check"; "pure_site_check"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy"; "cont_check"; "reent_check"; "empty_obj_check"; "empty_obj_check2"; "permb"; "small_lit"; "sv_zero"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "L_free"; "Pre_free"; "MInvR"; "ok_sideK"; "vm_insensitive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy.PerCutA"; "ejcutA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy.Permb"; "permb"; "rm_first"; "tve_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "topL"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundL SymSoundI SymSoundM SymSoundR SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue ObjUnbase ObjXform TobjJV TobjJVx TobjArena TobjJVA TobjJVAx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section Sub.
Variable segs : list Segment.

Definition small_lit (z : Z) : bool := ltac2:(tb__ "0|1|
S36S71S74S75Z2Z3eA2M0A1Vz;A2S73Vz;G0A2A2").
Definition has_zero8_over (cells : list cell) (off w : Z) : bool := ltac2:(tb__ "0|9|
S6bS7S7S0S2cLx;M0S1bR1A1S3fG0S1cR2A1S3fS3fS2cLz;R1S36S36S36S70S1dR3A1Z8M1A2SccR2A1A2S71R2Voff;A2A2S71S72Voff;Vw;A2S72R2G1A2A2A2S40S2eLp;M2G2X3fx3Lz;S40S2eLi;M3S90S0S0S2eLb;La;M4Lop;M5G5S8fG4Lop;M6G6S2cS41S0S2eLa;Lw0;Lsgn;M7S40S0S3fS2eLk;Li;Ll;M8X0x8Lo0;G3G5G5G6G6G7G8X0x8Lc;Vcells;A3").
Definition subcell_ok (o : sobj) (ow : Z * Z) : bool := ltac2:(tb__ "0|1|
S36ScbSeVo;A1S33S3fS3fVow;A3S34S3fS3fVow;A3M0A3S3cS3cS70G0Z1A2S70G0Z2A2A2S70G0Z4A2A2A2").
Definition add_subcell (o : sobj) (ow : Z * Z) : sobj := ltac2:(tb__ "0|0|
S20SdVo;A1S12Vo;A1S11Vo;A1S38S7S1fS9S33S3fS3fVow;A3A1S34S3fS3fVow;A3S9Z0A1A3SeVo;A1A3S10Vo;A1A5").
Fixpoint add_subcells (o : sobj) (l : list (Z * Z)) : option sobj :=
  match l with
  | [] => Some o
  | ow :: r => if subcell_ok o ow then add_subcells (add_subcell o ow) r else None
  end.
Definition subcells_at (S : sstate) (i : nat) (l : list (Z * Z)) : option sstate := ltac2:(tb__ "0|3|
S31S3A1S31S1A1Lx;M0S6cS3SaVS;A1M1Vi;A3S3G0Sc9R1Vl;A2S3S35S1S95VS;S32S3S8cS3Vi;G1A3S38S3R1S8dS3S3dVi;A1G1A3A3A3A2A2Lo';S3aS1A1M2X31x2Lo;G2X31x2").

Lemma enc_bytes_zero_nth : ltac2:(tb__ "0|4|
S37S37S42Sc7Q8M0A1M1S8eG1R1S1eR2Sc6Q40Z0M2A2A2Sc6G0G2A2M3A4G3A3Fj;Fk;").
Proof using .
  intros k j. unfold enc_bytes. rewrite Z_to_bv_unsigned. change (bv_wrap 64 0) with 0.
  destruct (Nat.lt_ge_cases j k) as [Hj|Hj].
  - rewrite Z_to_le_bytes_nth by exact Hj. rewrite Z.shiftr_0_l. reflexivity.
  - rewrite nth_overflow; [reflexivity|]. rewrite Z_to_le_bytes_length. exact Hj.
Qed.

Lemma eval_lit0 : ltac2:(tb__ "0|2|
S2S42Sc7Q40M0A1S17R1S9Z0M1A1A2Sc6G0G1A2A3Frho;").
Proof using . intros. reflexivity. Qed.

Lemma add_subcell_holds : ltac2:(tb__ "0|0|
S2S6dS3S30S3fS3fA2S42S2cScdR2R1A2S2fA3ScVsegs;R5R4R3A4ScVsegs;R6R5ScaR4R3A2A4F_;F_;Fow;Fo;Fms;Frho;").
Proof using .
  intros rho ms o [off w] Hok (Hb & Hw & Hc & Hd & Hi). unfold subcell_ok in Hok. cbn [fst snd] in Hok.
  apply andb_prop in Hok as [Hz Hw8]. unfold has_zero8_over in Hz. apply existsb_exists in Hz as (c & Hin & Hc0).
  destruct c as [co cw cv]. cbn [c_off c_val c_width] in Hc0.
  destruct co as [o0| | | | | | |]; try discriminate. destruct cv as [z| | | | | | |]; try discriminate.
  destruct z; try discriminate.
  apply andb_prop in Hc0 as [Hc0 H2]. apply andb_prop in Hc0 as [Hc0 H1]. apply andb_prop in Hc0 as [H0 Hs].
  apply Z.eqb_eq in H0. apply Z.leb_le in H1. apply Z.leb_le in H2. subst cw.
  unfold small_lit in Hs. apply andb_prop in Hs as [Hs1 Hs2]. apply Z.leb_le in Hs1. apply Z.ltb_lt in Hs2.
  assert (Hw' : 0 < w <= 8).
  { apply orb_prop in Hw8. destruct Hw8 as [Hw8|Hw8]; [apply orb_prop in Hw8; destruct Hw8 as [X|X]|]; apply Z.eqb_eq in Hw8 || apply Z.eqb_eq in X; lia. }
  pose proof (proj1 (Forall_forall _ _) Hc _ Hin) as CH. destruct CH as (C1 & C2 & C3). cbn [c_off c_width c_val] in C1, C2, C3.
  rewrite soff_lit_small in C1, C2, C3 by lia.
  unfold obj_holds, obj_lo_of, obj_hi_of in *. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt add_subcell fst snd] in *.
  split; [exact Hb|]. split; [exact Hw|]. split; [|split; [|exact Hi]].
  - constructor; [|exact Hc]. unfold cell_holds. cbn [c_off c_width c_val]. rewrite soff_lit_small by lia.
    split; [lia|]. split; [lia|].
    rewrite eval_lit0 in C3 |- *.
    apply rd_bytes_of_nth.
    + apply enc_bytes_length.
    + unfold oaddr. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64, Z.mod_small by lia. lia.
    + intros j Hj. rewrite enc_bytes_zero_nth.
      pose proof (rd_bytes_nth ms 8 (oaddr rho (ob_base o) o0) _ (Z.to_nat (off - o0) + j) C3 ltac:(lia)) as R.
      rewrite enc_bytes_zero_nth in R.
      unfold oaddr in R |- *. rewrite Z_to_bv_unsigned in R |- *. unfold bv_wrap in R |- *. rewrite two64 in R |- *.
      rewrite Z.mod_small in R by lia. rewrite Z.mod_small by lia.
      rewrite <- R; [|change (Z.of_nat 8) with 8; lia]. f_equal. f_equal. rewrite Nat2Z.inj_add, Z2Nat.id by lia. lia.
  - intros off' Hoff' Hncov. apply (Hd off' Hoff'). intros Hcov. apply Hncov. unfold covered in *. constructor 2. exact Hcov.
Qed.

Lemma add_subcells_holds : ltac2:(tb__ "0|0|
S2S6dS2dS30S3fS3fA2A1S3S3S42S31S3A1Sc9R2R3A2S35S3R1A2A3ScVsegs;R6R5R3A4ScVsegs;R7R6R3A4F_;F_;Fo';Fo;Fl;Fms;Frho;").
Proof using .
  intros rho ms l. induction l as [|ow r IH]; intros o o' H Ho; cbn [add_subcells] in H.
  - injection H as <-. exact Ho.
  - destruct (subcell_ok o ow) eqn:E; [|discriminate]. apply (IH _ _ H). apply add_subcell_holds; [exact E | exact Ho].
Qed.

Lemma add_subcells_shape : ltac2:(tb__ "0|1|
S2dS30S3fS3fA2A1S3S3S42S31S3A1Sc9R2R3A2S35S3R1A2A3S43S42S0SdR2A1SdR3A1A3S43S42S0S12R2A1S12R3A1A3S43S42S0S11R2A1S11R3A1A3S43S42S14S10R2A1S10R3A1A3S7S69S7R1SeR4A1M0A3S69S7R2G0A3F_;Fc;A2A2A2A2F_;Fo';Fo;Fl;").
Proof using .
  induction l as [|ow r IH]; intros o o' H; cbn [add_subcells] in H.
  - injection H as <-. repeat split; auto.
  - destruct (subcell_ok o ow); [|discriminate]. destruct (IH _ _ H) as (A & B & C & D & E).
    cbn [add_subcell ob_base ob_lo ob_hi ob_dflt ob_cells] in A, B, C, D, E. repeat split; auto.
    intros c Hc. apply E. right. exact Hc.
Qed.

Lemma mem_match_subcells : ltac2:(tb__ "0|1|
S2S6dS2dS3A1M0S3S3G0S2dS30S3fS3fA2A1S42S31S3A1Sc9R4R1A2S35S3R3A2A3SbVsegs;R8S32S3R6S38S3R5R3A3A3R7A4SbVsegs;R9S32S3R7S38S3R5R4A3A3R8A4F_;F_;Fl;FL2;Fo';Fo;FL1;Fms;Frho;").
Proof using .
  intros rho ms L1 o o' L2 l H (Hall & Hpd & Hfr).
  destruct (add_subcells_shape l o o' H) as (EB & EL & EH & ED & EC).
  assert (RNG : forall rho', obj_range rho' o' = obj_range rho' o).
  { intros rho'. unfold obj_range, obj_lo_of, obj_hi_of. rewrite EB, EL, EH. reflexivity. }
  assert (RNGS : forall rho', map (obj_range rho') (L1 ++ o' :: L2) = map (obj_range rho') (L1 ++ o :: L2)).
  { intros rho'. rewrite !map_app. cbn [map]. rewrite RNG. reflexivity. }
  split; [|split].
  - rewrite !Forall_app in Hall |- *. destruct Hall as (A & B). split; [exact A|].
    inversion B; subst. constructor; [|assumption]. eapply add_subcells_holds; eauto.
  - apply (proj2 (pairwise_disjoint_pdr rho _)). rewrite RNGS. apply (proj1 (pairwise_disjoint_pdr rho _)). exact Hpd.
  - unfold mem_frame, outside_all in *. intros a Ha. apply Hfr.
    rewrite Forall_app in Ha |- *. destruct Ha as [Ha1 Ha2]. split; [exact Ha1|]. inversion Ha2; subst. constructor; [|assumption].
    rewrite <- RNG. assumption.
Qed.

Lemma SPJ_subcells : ltac2:(tb__ "0|0|
S47S2S1S37S2dS30S3fS3fA2A1S1S63S42S31S1A1SceR5R4R3A3S35S1R2A2A3S42S2cSb7R6R3A2S2fA3S46Vsegs;R9R7R8R3A5S46Vsegs;RaR5R9R4A5F_;F_;F_;Fw;FS';Fl;Fi;FS;Frho;FJ;").
Proof using .
  intros J rho S i l S' [tr [ms md]] H Hsame Hw.
  eapply SPJ_reobj; [exact Hsame | exact Hw |].
  destruct Hw as [Hsm _]. cbn [w_cfg cfg_ms].
  destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmem & _). cbn [fst snd cfg_ms cfg_model] in Hmem.
  unfold subcells_at in H. destruct (nth_error (ss_objs S) i) as [o|] eqn:Hi; [|discriminate].
  destruct (add_subcells o l) as [o'|] eqn:Ha; [|discriminate]. injection H as <-. cbn [ss_objs set_objs].
  rewrite (split_at_nth (ss_objs S) i o Hi) in Hmem.
  eapply mem_match_subcells; [exact Ha | exact Hmem].
Qed.
End Sub.

Section Emp.
Variable segs : list Segment.

Definition sv_zero (v : sv) : bool := ltac2:(tb__ "0|f|
S0S2cLv;Vv;S3fS3fS2cLz;M0R1S2fS40S2eLp;M1G1X3fx3Lz;S40S2eLi;M2S90S0S0S2eLb;La;M3Lop;M4G4S8fS0S0S8fS2cLop;R3S0S2cLa;R2S3fG0R1S0S2cLb;M5R2S3fS3fS2cLz0;M6R1S2fS40S2fLp;M7G7X3fx3Lz0;G2S90S0S0S2eLb0;La0;M8Lop0;M9G9S8fG8Lop0;MaGaS2cS41S0S2eLa0;Lw;Lsgn;MbS40S0S3fS2eLk;Li;Ll;McX0x8S40G5R3S3fG6R1S2fS40S2eLp0;MdGdX3fx3Lz0;G2G9G9GaGaGbGcX0x8Lp;MeGeX3fx3Lz;G2G9G9GaGaGbGcX0x8S2eS2eS2eS2eS2eS2eS2eX8fx8Lb;La;Lop;S8fG3Lop;S2cS41S0S2eLa;Lw;Lsgn;GcX0x8").
Lemma sv_zero_sound : ltac2:(tb__ "0|1|
S2S0S42S2cSd5R1A1S2fA3S42Sc7Q40M0A1S17R3R2A2Sc6G0Z0A2A3F_;Fv;Frho;").
Proof using .
  intros rho v H.
  assert (CASES : v = SLit 0 \/ exists a b, v = SMd M_MUL (SLit a) (SLit b) /\ (a = 0 \/ b = 0)).
  { destruct v as [z|p|o a b|o a b|o a b|o a b|g w a|l i k]; try discriminate.
    - destruct z; try discriminate. left. reflexivity.
    - destruct o; try discriminate. right.
      destruct a as [za| | | | | | |]; try discriminate.
      destruct za.
      + destruct b as [zb| | | | | | |]; try discriminate. exists 0, zb. auto.
      + destruct b as [zb| | | | | | |]; try discriminate. destruct zb; try discriminate. eexists _, 0. auto.
      + destruct b as [zb| | | | | | |]; try discriminate. destruct zb; try discriminate. eexists _, 0. auto. }
  clear H. destruct CASES as [-> | (a & b & -> & Hab)]; [reflexivity|].
  apply bv_eq. rewrite U_mul, !U_lit, lit_unsigned.
  destruct Hab as [-> | ->].
  - rewrite (Z.mod_0_l M64v) by (unfold M64v; lia). rewrite Z.mul_0_l. reflexivity.
  - rewrite (Z.mod_0_l M64v) by (unfold M64v; lia). rewrite Z.mul_0_r. reflexivity.
Qed.

Definition empty_obj_check (o : sobj) : bool := ltac2:(tb__ "0|a|
S0S2cLx;M0SdVo;A1S3fS3fS2cLz;R1G0S12Vo;A1S3fS3fS2cLz0;R1S2dS7A1M1S2cLx;SeVo;A1S14S2cLx;S10Vo;A1Sd5S11Vo;A1A1S2eS2eS40S2eLl;M2G2S3fS0S2dS30S3fS3fA2A1S2dS22A1S2eLtmpl;Lflds;Lcnt;Lesz;X14x6S7G1S2eLl;Lc;X2dx2S40S2eLp;M3G3X3fx3Lz0;S40S2eLi;M4S90S0S0S2eLb;La;M5Lop;M6G6S8fG5Lop;M7G7S2cS41S0S2eLa;Lw;Lsgn;M8S40S0S3fS2eLk;Li;Ll;M9X0x8G3G3X3fx3Lz;G4G6G6G7G7G8G9X0x8").

Lemma empty_obj_range : ltac2:(tb__ "0|1|
S2S3S42S2cSd3R1A1S2fA3S42S30S3fS3fA2SfR3R2A2S39S3fS3fZ0M0G0A4A3F_;Fo;Frho;").
Proof using .
  intros rho [b lo hi cells d] H. unfold empty_obj_check in H. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in H.
  destruct b as [zb| | | | | | |]; try discriminate. destruct zb; try discriminate.
  destruct lo as [zl| | | | | | |]; try discriminate. destruct zl; try discriminate.
  destruct cells; try discriminate. destruct d; try discriminate.
  unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. unfold soff.
  rewrite (sv_zero_sound rho hi H). change (eval rho (SLit 0)) with (Z_to_bv 64 0). rewrite lit_unsigned. cbn. reflexivity.
Qed.

Lemma empty_obj_holds : ltac2:(tb__ "0|0|
S2S6dS3S42S2cSd3R1A1S2fA3ScVsegs;R4R3R2A4F_;Fo;Fms;Frho;").
Proof using .
  intros rho ms [b lo hi cells d] H. pose proof (empty_obj_range rho _ H) as HR.
  unfold empty_obj_check in H. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in H.
  destruct b as [zb| | | | | | |]; try discriminate. destruct zb; try discriminate.
  destruct lo as [zl| | | | | | |]; try discriminate. destruct zl; try discriminate.
  destruct cells; try discriminate. destruct d; try discriminate.
  unfold obj_range in HR. cbn [ob_base] in HR. change (eval rho (SLit 0)) with (Z_to_bv 64 0) in HR. rewrite lit_unsigned in HR. change (0 mod 2 ^ 64) with 0 in HR.
  injection HR as A. rewrite Z.add_0_l in A.
  assert (B : obj_lo_of rho (mkObj (SLit 0) (SLit 0) hi [] DUnknown) = 0) by reflexivity.
  unfold obj_holds. cbn [ob_base ob_cells ob_dflt]. change (eval rho (SLit 0)) with (Z_to_bv 64 0). rewrite lit_unsigned. change (0 mod 2 ^ 64) with 0.
  rewrite A, B.
  split; [lia|]. split; [intros; lia|]. split; [constructor|]. split; [intros; lia|]. exact I.
Qed.

Lemma mem_match_add_empties : ltac2:(tb__ "0|1|
S2S6dS2dS3A1M0G0S42S2cS6aS3Sd3R1A3S2fA3SbVsegs;R5R3R4A4SbVsegs;R6S32S3R4R3A3R5A4F_;F_;Fobjs';Fobjs;Fms;Frho;").
Proof using .
  intros rho ms objs objs' Hc (Hall & Hpd & Hfr).
  assert (HE : forall o, In o objs' -> obj_range rho o = (0, 0)).
  { intros o Ho. apply empty_obj_range. exact (proj1 (forallb_forall _ _) Hc o Ho). }
  split; [|split].
  - rewrite Forall_app. split; [exact Hall|]. apply Forall_forall. intros o Ho. apply empty_obj_holds.
    exact (proj1 (forallb_forall _ _) Hc o Ho).
  - apply (proj2 (pairwise_disjoint_pdr rho _)). rewrite map_app.
    apply pdr_app.
    + apply (proj1 (pairwise_disjoint_pdr rho _)). exact Hpd.
    + clear - HE. induction objs' as [|o r IH]; cbn; [exact I|]. split.
      * apply Forall_forall. intros r' Hr'. rewrite (HE o (or_introl eq_refl)). unfold ranges_disjoint. cbn. lia.
      * apply IH. intros o' Ho'. apply HE. right. exact Ho'.
    + intros r1 r2 _ Hr2. apply in_map_iff in Hr2 as (o & <- & Ho).
      rewrite (HE o Ho). unfold ranges_disjoint. cbn. lia.
  - unfold mem_frame, outside_all in *. intros a Ha. apply Hfr. rewrite Forall_app in Ha. exact (proj1 Ha).
Qed.

Definition empty_obj_check2 (facts : list sprop) (o : sobj) : bool := ltac2:(tb__ "0|8|
S0S2cLx;S12Vo;A1S3fS3fS2cLz;R1S2dS7A1M0S2cLx;SeVo;A1S14S2cLx;S10Vo;A1S36S96Vfacts;SdVo;A1Z0M1S9G1A1M2A4S96Vfacts;S11Vo;A1G1G2A4A2S2eS2eS40S2eLl;M3G3S3fS0S2dS30S3fS3fA2A1S2dS22A1S2eLtmpl;Lflds;Lcnt;Lesz;X14x6S7G0S2eLl;Lc;X2dx2S40S2eLp;M4G4X3fx3Lz;S40S2eLi;S90S0S0S2eLb;La;M5Lop;M6G6S8fG5Lop;M7G7S2cS41S0S2eLa;Lw;Lsgn;S40S0S3fS2eLk;Li;Ll;X0x8").

Lemma empty_obj_range2 : ltac2:(tb__ "0|1|
S2S2dS4A1S3S8aS4S8R3A1R2A3S42S2cSd4R3R2A2S2fA3S43S42S30S3fS3fA2SfR5R3A2S39S3fS3fZ0M0G0A4A3S43S42S3fS27R5R3A2G0A3S43S42S3fS26R5R3A2G0A3S42S3fSc8Q40S17R5SdR3A1A2A2G0A3A2A2A2F_;F_;Fo;Ffacts;Frho;").
Proof using .
  intros rho facts [b lo hi cells d] HF H. unfold empty_obj_check2 in H. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in H.
  destruct lo as [zl| | | | | | |]; try discriminate. destruct zl; try discriminate.
  destruct cells; try discriminate. destruct d; try discriminate.
  apply andb_prop in H as [H1 H2].
  pose proof (uleq_sound rho _ _ 0 _ HF H1) as U1. pose proof (uleq_sound rho _ _ 0 _ HF H2) as U2. unfold U in U1, U2.
  change (eval rho (SLit 0)) with (Z_to_bv 64 0) in U1, U2. rewrite lit_unsigned in U1, U2. change (0 mod 2 ^ 64) with 0 in U1, U2.
  pose proof (bv_urange (eval rho b)) as Rb. pose proof (bv_urange (eval rho hi)) as Rh.
  assert (Eh : bv_unsigned (eval rho hi) = 0) by lia. assert (Eb : bv_unsigned (eval rho b) = 0) by lia.
  assert (Sh : soff rho hi = 0). { unfold soff. rewrite bv_signed_U. rewrite Eh. reflexivity. }
  unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite Eb, Sh.
  change (soff rho (SLit 0)) with (bv_signed (Z_to_bv 64 0)). rewrite bv_signed_U, lit_unsigned. cbn. auto.
Qed.

Lemma empty_obj_holds2 : ltac2:(tb__ "0|0|
S2S2dS4A1S6dS3S8aS4S8R4A1R3A3S42S2cSd4R4R2A2S2fA3ScVsegs;R6R4R3A4F_;F_;Fo;Fms;Ffacts;Frho;").
Proof using .
  intros rho facts ms o HF H. destruct (empty_obj_range2 rho facts o HF H) as (HR & L0 & H0 & B0).
  destruct o as [b lo hi cells d]. unfold empty_obj_check2 in H. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in H, B0.
  destruct lo as [zl| | | | | | |]; try discriminate. destruct zl; try discriminate.
  destruct cells; try discriminate. destruct d; try discriminate.
  unfold obj_holds. rewrite L0, H0. cbn [ob_base ob_cells ob_dflt]. rewrite B0.
  split; [lia|]. split; [intros; lia|]. split; [constructor|]. split; [intros; lia|]. exact I.
Qed.

Lemma mem_match_add_empties2 : ltac2:(tb__ "0|1|
S2S2dS4A1S6dS2dS3A1M0G0S8aS4S8R5A1R4A3S42S2cS6aS3Sd4R5A1R2A3S2fA3SbVsegs;R7R4R5A4SbVsegs;R8S32S3R5R4A3R6A4F_;F_;F_;Fobjs';Fobjs;Fms;Ffacts;Frho;").
Proof using .
  intros rho facts ms objs objs' HF Hc (Hall & Hpd & Hfr).
  assert (HE : forall o, In o objs' -> obj_range rho o = (0, 0)).
  { intros o Ho. apply (empty_obj_range2 rho facts o HF). exact (proj1 (forallb_forall _ _) Hc o Ho). }
  split; [|split].
  - rewrite Forall_app. split; [exact Hall|]. apply Forall_forall. intros o Ho. eapply empty_obj_holds2; [exact HF|].
    exact (proj1 (forallb_forall _ _) Hc o Ho).
  - apply (proj2 (pairwise_disjoint_pdr rho _)). rewrite map_app.
    apply pdr_app.
    + apply (proj1 (pairwise_disjoint_pdr rho _)). exact Hpd.
    + clear - HE. induction objs' as [|o r IH]; cbn; [exact I|]. split.
      * apply Forall_forall. intros r' Hr'. rewrite (HE o (or_introl eq_refl)). unfold ranges_disjoint. cbn. lia.
      * apply IH. intros o' Ho'. apply HE. right. exact Ho'.
    + intros r1 r2 _ Hr2. apply in_map_iff in Hr2 as (o & <- & Ho).
      rewrite (HE o Ho). unfold ranges_disjoint. cbn. lia.
  - unfold mem_frame, outside_all in *. intros a Ha. apply Hfr. rewrite Forall_app in Ha. exact (proj1 Ha).
Qed.
End Emp.

Section SE.
Variable segs : list Segment.
Lemma SPJ_add_empties : ltac2:(tb__ "0|0|
S47S2S1S2dS3A1S63S42S2cS6aS3Se6R2A3S2fA3S42S2cSb7R4S95R4S32S3SaR4A1R3A3A2A2S2fA3S46Vsegs;R7R5R6R3A5S46Vsegs;R8S95R6S32S3SaR6A1R5A3A2R7R4A5F_;F_;F_;Fw;Fobjs';FS;Frho;FJ;").
Proof using .
  intros J rho S objs' [tr [ms md]] Hc Hsame Hw.
  eapply SPJ_reobj; [exact Hsame | exact Hw |].
  destruct Hw as [Hsm _]. cbn [w_cfg cfg_ms].
  destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmem & _). cbn [fst snd cfg_ms cfg_model] in Hmem.
  cbn [ss_objs set_objs]. apply mem_match_add_empties; [exact Hc | exact Hmem].
Qed.

Lemma SPJ_add_empties2 : ltac2:(tb__ "0|0|
S47S2S1S2dS3A1S63S42S2cS6aS3Se7S6R3A1A1R2A3S2fA3S42S2cSb7R4S95R4S32S3SaR4A1R3A3A2A2S2fA3S46Vsegs;R7R5R6R3A5S46Vsegs;R8S95R6S32S3SaR6A1R5A3A2R7R4A5F_;F_;F_;Fw;Fobjs';FS;Frho;FJ;").
Proof using .
  intros J rho S objs' [tr [ms md]] Hc Hsame Hw.
  eapply SPJ_reobj; [exact Hsame | exact Hw |].
  destruct Hw as [Hsm _]. cbn [w_cfg cfg_ms].
  pose proof (smatch_facts_hold segs _ _ _ Hsm) as HF.
  destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmem & _). cbn [fst snd cfg_ms cfg_model] in Hmem.
  cbn [ss_objs set_objs]. eapply mem_match_add_empties2; [exact HF | exact Hc | exact Hmem].
Qed.
End SE.

Section JA.
Variable segs : list Segment.
Variable C : mconsts.
Variable NP : positive.
Variable Kc : ltac2:(tb__ "0|0|
S2dS68A1S67OF_;F_;").
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Hypothesis ML : malloc_laws segs C.

Definition null_entry (t : sv * sv) : bool := ltac2:(tb__ "0|4|
S0S2cLx;S33S0S0Vt;A3S3fS3fS2cLz;R1SeaS34S0S0Vt;A3A1S40S2eLp;M0G0X3fx3Lz;S40S2eLi;S90S0S0S2eLb;La;M1Lop;M2G2S8fG1Lop;M3G3S2cS41S0S2eLa;Lw;Lsgn;S40S0S3fS2eLk;Li;Ll;X0x8").

Lemma null_entry_not_tnz : ltac2:(tb__ "0|0|
S2S30S0S0A2S42S2cSbeR1A1S2fA3S45Sa4R3R2A2A1F_;Ft;Frho;").
Proof using .
  intros rho [d sz] H Hnz. unfold null_entry in H. cbn [fst snd] in H. destruct d as [z| | | | | | |]; try discriminate.
  destruct z; try discriminate. apply Hnz. cbn [fst]. change (eval rho (SLit 0)) with (Z_to_bv 64 0). rewrite lit_unsigned. reflexivity.
Qed.
Lemma null_entry_size0 : ltac2:(tb__ "0|0|
S2S30S0S0A2S42S2cSbeR1A1S2fA3S42S3fS34S3fS3fSa6R3R2A2A3Z0A3F_;Ft;Frho;").
Proof using .
  intros rho [d sz] H. unfold null_entry in H. cbn [fst snd] in H. destruct d as [z| | | | | | |]; try discriminate.
  destruct z; try discriminate. unfold tvv. cbn [fst snd]. rewrite (sv_zero_sound rho sz H). rewrite lit_unsigned. reflexivity.
Qed.

Lemma tvd_app_nulls : ltac2:(tb__ "0|2|
S2S2dS30S0S0A2M0A1M1G1S42S2cS6aG0SbeR1A3S2fA3Sa5R4R3A2Sa5R5S32G0R4R3A3A2F_;F_;Fnl;Ftv;Frho;").
Proof using .
  intros rho tv nl Hn. induction tv as [|t r IH]; intros H.
  - cbn [app]. clear H. induction nl as [|t r IH]; [exact I|]. cbn in Hn. apply andb_prop in Hn as [H1 H2]. cbn. split.
    + intros t' _ Hnz _. exfalso. exact (null_entry_not_tnz rho t H1 Hnz).
    + exact (IH H2).
  - destruct H as [H1 H2]. cbn. split; [|exact (IH H2)].
    intros t' Hin Hnz Hnz'. apply in_app_or in Hin as [Hin|Hin]; [exact (H1 t' Hin Hnz Hnz')|].
    exfalso. exact (null_entry_not_tnz rho t' (proj1 (forallb_forall _ _) Hn t' Hin) Hnz').
Qed.

Lemma JGA_add_nulls : ltac2:(tb__ "0|2|
S2dS30S0S0A2M0A1M1G1S4bS2S2dS68A1S67S42S2cS6aG0SbeR5A3S2fA3S4cVsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;R7R5R4R3R2AcS4cVsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;S32G0R8R7A3R6R5R4R3AcF_;F_;Fmd;Ftr;Frho;Fam;Fnl;Ftv;").
Proof using .
  intros tv nl am rho tr md Hn [Ai [(Hav & Hk & HM & HP & (HN & HD & HZ) & HK & HP0) HXA]]. exists Ai. split.
  - split; [exact Hav|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HP|]. split; [|split; [exact HK | exact HP0]].
    split; [|split].
    + unfold tvin in *. rewrite Forall_app. split; [exact HN|]. apply Forall_forall. intros t Ht Hnz.
      exfalso. exact (null_entry_not_tnz rho t (proj1 (forallb_forall _ _) Hn t Ht) Hnz).
    + apply tvd_app_nulls; [exact Hn | exact HD].
    + unfold tvz in *. rewrite Forall_app. split; [exact HZ|]. apply Forall_forall. intros t Ht _.
      apply null_entry_size0. exact (proj1 (forallb_forall _ _) Hn t Ht).
  - destruct am as [|hd|hd nx cap sl|hd g]; cbn -[pl_below] in HXA |- *.
    + exact I.
    + destruct HXA as (ns & HA & [HF HDp]). exists ns. split; [exact HA|]. split; [|exact HDp].
      apply Forall_forall. intros bc Hbc. destruct (proj1 (Forall_forall _ _) HF bc Hbc) as (X1 & X2 & X3).
      split; [exact X1|]. split; [exact X2|]. intros t Ht Hnz. apply in_app_or in Ht as [Ht|Ht]; [exact (X3 t Ht Hnz)|].
      exfalso. exact (null_entry_not_tnz rho t (proj1 (forallb_forall _ _) Hn t Ht) Hnz).
    + destruct HXA as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & ns & HA & [HF HDp] & Hnin).
      split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split.
      * intros t Ht Hnz. apply in_app_or in Ht as [Ht|Ht]; [exact (X5 t Ht Hnz)|].
        exfalso. exact (null_entry_not_tnz rho t (proj1 (forallb_forall _ _) Hn t Ht) Hnz).
      * split; [exact X6|]. split; [exact X7|]. exists ns. split; [exact HA|]. split; [|exact Hnin]. split; [|exact HDp].
        apply Forall_forall. intros bc Hbc. destruct (proj1 (Forall_forall _ _) HF bc Hbc) as (Y1 & Y2 & Y3).
        split; [exact Y1|]. split; [exact Y2|]. intros t Ht Hnz. apply in_app_or in Ht as [Ht|Ht]; [exact (Y3 t Ht Hnz)|].
        exfalso. exact (null_entry_not_tnz rho t (proj1 (forallb_forall _ _) Hn t Ht) Hnz).
    + destruct HXA as (ns & HA & [HF HDp] & HG). exists ns. split; [exact HA|]. split; [|exact HG]. split; [|exact HDp].
      apply Forall_forall. intros bc Hbc. destruct (proj1 (Forall_forall _ _) HF bc Hbc) as (X1 & X2 & X3).
      split; [exact X1|]. split; [exact X2|]. intros t Ht Hnz. apply in_app_or in Ht as [Ht|Ht]; [exact (X3 t Ht Hnz)|].
      exfalso. exact (null_entry_not_tnz rho t (proj1 (forallb_forall _ _) Hn t Ht) Hnz).
Qed.

Lemma SPJ_JGA_add_nulls : ltac2:(tb__ "0|2|
S2dS30S0S0A2M0A1M1G1S4bS1S2S63S42S2cS6aG0SbeR5A3S2fA3S46Vsegs;S4cVsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;R7R5A9R4R3R2A5S46Vsegs;S4cVsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;S32G0R8R7A3R6A9R5R4R3A5F_;F_;Fw;Frho;FS;Fam;Fnl;Ftv;").
Proof using . intros tv nl am S rho w Hn [Hs HJ]. split; [exact Hs|]. apply JGA_add_nulls; [exact Hn | exact HJ]. Qed.

Lemma SPJ_JGA_head0 : ltac2:(tb__ "0|1|
S2dS30S0S0A2A1S0S1S2S63S42S2cS96S6R3A1R4Z0M0S9G0A1A4S2fA3S46Vsegs;S4cVsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;R6S4eA9R4R3R2A5S46Vsegs;S4cVsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;R7S5dR6A1A9R5R4R3A5F_;F_;Fw;Frho;FS;Fhd;Ftv;").
Proof using .
  intros tv hd S rho [tr [ms md]] Hu [Hs [Ai [HJ _]]]. split; [exact Hs|]. exists Ai. split; [exact HJ|].
  cbn. exists []. split.
  - cbn. pose proof (uleq_sound rho _ _ 0 _ (smatch_facts_hold segs _ _ _ Hs) Hu) as U1.
    unfold U in U1. change (eval rho (SLit 0)) with (Z_to_bv 64 0) in U1. rewrite lit_unsigned in U1.
    change (0 mod 2 ^ 64) with 0 in U1. pose proof (bv_urange (eval rho hd)). cbv beta. lia.
  - split; [constructor | constructor].
Qed.
End JA.

Section PerCutA.
Variable segs : list Segment. Variable NP : positive.
Variable fuel : nat. Variable cutpcs : list Z. Variable g : positive.

Definition ejcutA (nodes : list aedesc) (i : nat) (n : aedesc) : bool := ltac2:(tb__ "0|3|
S36S3eS2aS4fVn;A1M0A1A1S36Sb4Vg;S5G0A1A2S31S2dS94A1M1A1S2cLx;S98Vsegs;Vfuel;Vcutpcs;G0S2fA5G1S31S2dSddA1M2A1S2cLx;Se0Vg;Vi;R1S8bS4dS1S4fVnodes;A4A4G2S6aSddS5fVNP;Vnodes;A2R1A3Les;S2eX31x2Lleaves;S2eX31x2A2A2").

Lemma ejcertA_of_cuts : ltac2:(tb__ "0|1|
S2dS4dA1M0G0S37S4dS42S31S4dA1S6cS4dR4R2A3S35S4dR1A2A3S42S2cSf0S32S4dR5R4A3R3R2A3S2fA3F_;Fn;Fi;S42S2cS60Vsegs;VNP;Vfuel;Vcutpcs;Vg;R3R2A7S2fA3F_;FexitsE;FcutsE;").
Proof using .
  intros cutsE exitsE Hc. unfold ejcertA. apply andb_true_intro. split.
  - apply forallb_forall. intros n Hn. apply In_nth_error in Hn as [i Hi].
    pose proof (Hc i n Hi) as H. unfold ejcutA in H. apply andb_prop in H as [H _]. exact H.
  - unfold cfg_edges.
    destruct (cuts_edges_ok segs fuel cutpcs g (eecheckA NP (cutsE ++ exitsE)) (map ad_state cutsE ++ map ad_state exitsE)
                (map ad_state cutsE) 0 ) as (es & Hce & Hes).
    { intros k T Hn. rewrite nth_error_map in Hn. destruct (nth_error cutsE k) as [n|] eqn:En; [|discriminate].
      cbn in Hn. injection Hn as <-.
      pose proof (Hc k n En) as H. unfold ejcutA in H. apply andb_prop in H as [_ H]. apply andb_prop in H as [Hg H].
      split; [exact Hg|].
      destruct (sym_run segs fuel cutpcs (ad_state n) true) as [leaves|]; [|discriminate].
      cbn [Nat.add].
      destruct (leaves_edges g k leaves (map ad_state (cutsE ++ exitsE))) as [es|] eqn:Hle; [|discriminate].
      exists leaves, es. rewrite map_app in Hle. auto. }
    rewrite Hce. exact Hes.
Qed.
End PerCutA.

Section ContA.
Variable segs : list Segment.
Variable C : mconsts.
Variable NP : positive.
Variable Kc : ltac2:(tb__ "0|0|
S2dS68A1S67OF_;F_;").
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Hypothesis ML : malloc_laws segs C.

Let JGv (tv : list (sv * sv)) (am : amode) : jpred := ltac2:(tb__ "0|0|
S4cVsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;Vtv;Vam;A9").

Definition entA_check (n : positive) (X A : sstate) (tvi tvj : list (sv * sv)) (ami amj : amode) (vA : sv) (rA rE : Z) (vE : sv) : bool := ltac2:(tb__ "0|2|
SdeVNP;VX;VA;A3S78S2cS2cL_;M0SbaVX;VA;R1A3G0S7cR1VNP;A2G0Sb4VNP;S5VX;A1M1A2G0S9aG1Vtvi;A2G0Sa0R1Vtvi;Vtvj;A3G0S50G1Vami;A2G0S51S56R1Vamj;A2Vami;A2G0S18Vn;VvE;A2G0S71Z0VrA;A2G0S73VrA;VrE;A2S2fG0S70VrA;VrE;A2S96S6VX;A1S7dR1VvA;A2Z1VvE;A4S2eX2cx2X2cx2S2eX2cx2S2eX2cx2S2eX2cx2S2eX2cx2S2eX2cx2S2eX2cx2S2eX2cx2S2eX2cx2S2eX2cx2Ts;").

Lemma entA_sound : ltac2:(tb__ "0|2|
S40S1S1S2dS30S0S0A2A1M0G0S4bS4bS0S3fS3fS0S42S2cSd2RbRaR9R8R7R6R5R4R3R2R1AbS2fA3S2S2S63S46Vsegs;VJGv;RcRaA2ReR2R1A5S7eR10R4R3A3S44S2S2S43S46Vsegs;VJGv;ReRcA2R10R1R4A5S43S6eZ0S93RaRbR1A3M1A2S6fG1S93R9R8R6A3A2A2A2Lrho';A2F_;F_;Fw;Frho;FrhoX;F_;FvE;FrE;FrA;FvA;Famj;Fami;Ftvj;Ftvi;FA;FX;Fn;").
Proof using FB Kc ML P0f rho0.
  intros n X A tvi tvj ami amj vA rA rE vE H rhoX rho w Hw Hag. unfold entA_check in H. cbv zeta in H.
  apply lazy_andb_prop in H as [H1 H]. apply lazy_andb_prop in H as [H2 H]. apply lazy_andb_prop in H as [H3 H].
  apply lazy_andb_prop in H as [H4 H]. apply lazy_andb_prop in H as [H5 H]. apply lazy_andb_prop in H as [H6 H].
  apply lazy_andb_prop in H as [H7 H]. apply lazy_andb_prop in H as [Hb H].
  apply lazy_andb_prop in H as [H0 H].
  exists (rho_sub rho (infer_sub NP X A)). split.
  - eapply (SPJ_entails_JGA segs C NP Kc rho0 P0f FB ML); [exact H1 | exact H2 | exact H3 | exact H4 | exact H5 | exact H6 | exact H7 | exact Hw].
  - unfold emeasZ. rewrite <- eval_subst.
    rewrite (eval_agree_vals n rhoX rho vE Hag Hb).
    apply Z.leb_le in H0.
    pose proof (urange (eval rho (sv_subst (infer_sub NP X A) vA))) as R1. pose proof (urange (eval rho vE)) as R2.
    apply lazy_orb_prop in H as [Hlt|H].
    + apply Z.ltb_lt in Hlt. nia.
    + apply lazy_andb_prop in H as [Heq Hu]. apply Z.eqb_eq in Heq. subst rE.
      destruct Hw as [Hsm _]. destruct w as [tr [ms md]].
      pose proof (uleq_sound rho _ _ 1 _ (smatch_facts_hold segs _ _ _ Hsm) Hu) as U1. unfold U in U1. lia.
Qed.

Section TRX.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S64S64S64S63R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_exw : forall (A : Type) (P : A -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_pureh : ltac2:(tb__ "0|0|
OS64S64R3VTR;R3R2A2F_;VTR;S63S43R5R4R1A1A2Lw;R2A2F_;FQ;FP;FX;").

Lemma entA_TR : ltac2:(tb__ "0|3|
S40S1S1S2dS30S0S0A2M0A1M1G1G1S4bS4bS0S3fS3fS0S2S2S64S42S2cSd2RfReRdRcRbR9R8R7R6R5R4AbS2fA3SbbG0RcRbA3S7eR11R5R4A3S2S43S6eZ0S93RaRbR1A3M2A2S6fG2S93R9R8R7A3A2A2VTR;S46Vsegs;VJGv;RfRdA2R12R2A4R6A2F_;Frho';VTR;S46Vsegs;VJGv;R10RdA2R12R6A4R5A2F_;F_;F_;F_;FFAMb;Frho;FrhoX;FvE;FrE;FrA;FvA;Famj;Fami;Ftvj';Ftvj;Ftvi;FA;FX;Fn;").
Proof using FB Kc ML P0f TR_exw TR_pre TR_pureh rho0.
  intros n X A tvi tvj tvj' ami amj vA rA rE vE rhoX rho FAMb H HP Hag HA.
  eapply TR_pre; [ | apply (TR_exw valuation (fun rho' w => (0 <= emeasZ rA vA rho' < emeasZ rE vE rhoX) /\ SPJ segs (JGv tvj' amj) A rho' w))].
  - intros w Hw. destruct (entA_sound n X A tvi tvj ami amj vA rA rE vE H rhoX rho w Hw Hag) as (rho' & H' & Hm).
    exists rho'. split; [exact Hm|]. destruct H' as [Hs HJ]. split; [exact Hs|]. eapply JGA_tv_perm; [exact HP | exact HJ].
  - intros rho'. apply TR_pureh. intros Hm. exact (HA rho' Hm).
Qed.

Definition contA_check (ns : list nstep) (n : positive) (T A : sstate) (tvi tvj : list (sv * sv)) (ami amj : amode)
           (vA : sv) (rA rE : Z) (vE : sv) : bool := ltac2:(tb__ "0|0|
S31S1A1S2cLx;S77VT;Vns;A2S1Sd2Vn;R1VA;Vtvi;Vtvj;Vami;Vamj;VvA;VrA;VrE;VvE;AbLX;S2eX31x2").

Lemma contA_TR : ltac2:(tb__ "0|3|
S2dS76A1S40S1S1S2dS30S0S0A2M0A1M1G1G1S4bS4bS0S3fS3fS0S2S2S64S42S2cSd1R10RfReRdRcRbR9R8R7R6R5R4AcS2fA3SbbG0RcRbA3S7eR11R5R4A3S2S43S6eZ0S93RaRbR1A3M2A2S6fG2S93R9R8R7A3A2A2VTR;S46Vsegs;VJGv;RfRdA2R12R2A4R6A2F_;Frho';VTR;S46Vsegs;VJGv;R10RdA2R12R6A4R5A2F_;F_;F_;F_;FFAMb;Frho;FrhoX;FvE;FrE;FrA;FvA;Famj;Fami;Ftvj';Ftvj;Ftvi;FA;FT;Fn;Fns;").
Proof using FB Kc ML P0f TR_exw TR_pre TR_pureh rho0.
  intros ns n T A tvi tvj tvj' ami amj vA rA rE vE rhoX rho FAMb H HP Hag HA. unfold contA_check in H.
  destruct (run_nsteps T ns) as [X|] eqn:HN; [|discriminate].
  eapply TR_pre; [| apply (entA_TR n X A tvi tvj tvj' ami amj vA rA rE vE rhoX rho FAMb H HP Hag HA)].
  intros w Hw. eapply SPJ_nsteps; [exact HN | exact Hw].
Qed.

Definition landAs_check (ns : list nstep) (s0 : wsub) (T A : sstate) (tvi tvj : list (sv * sv)) (ami amj : amode) : bool := ltac2:(tb__ "0|3|
S31S1A1S2cLx;S77VT;Vns;A2S1S32S30S40S0A2M0Vs0;SdeVNP;R1VA;A3A3S2dG0A1S2cS2cL_;M1SbaR2VA;R1A3G1S7cR1VNP;A2G1Sb4VNP;S5R2A1M2A2G1S9aG2Vtvi;A2G1Sa0R1Vtvi;Vtvj;A3G1S50G2Vami;A2S51S56R1Vamj;A2Vami;A2S2eX2cx2S2eX2cx2S2eX2cx2S2eX2cx2S2eX2cx2S2eX2cx2Ts;LX;S2eX31x2").
Definition landA_check (ns : list nstep) (T A : sstate) (tvi tvj : list (sv * sv)) (ami amj : amode) : bool := ltac2:(tb__ "0|0|
ScfVns;S3bS30S40S0A2A1VT;VA;Vtvi;Vtvj;Vami;Vamj;A8").

Lemma landAs_sound : ltac2:(tb__ "0|1|
S2dS76A1S78S1S1S2dS30S0S0A2A1M0G0S4bS4bS42S2cScfR8R7R6R5R4R3R2R1A8S2fA3S2S63S46Vsegs;VJGv;R7R5A2R9R2R1A5S44S2S2S46Vsegs;VJGv;R8R6A2RaR1R3A5Lrho';A2F_;Fw;Frho;F_;Famj;Fami;Ftvj;Ftvi;FA;FT;Fs0;Fns;").
Proof using FB Kc ML P0f rho0.
  intros ns s0 T A tvi tvj ami amj H rho w Hw. unfold landAs_check in H.
  destruct (run_nsteps T ns) as [X|] eqn:HN; [|discriminate]. cbv zeta in H.
  apply lazy_andb_prop in H as [H1 H]. apply lazy_andb_prop in H as [H2 H]. apply lazy_andb_prop in H as [H3 H].
  apply lazy_andb_prop in H as [H4 H]. apply lazy_andb_prop in H as [H5 H]. apply lazy_andb_prop in H as [H6 H7].
  eexists. eapply (SPJ_entails_JGA segs C NP Kc rho0 P0f FB ML); [exact H1 | exact H2 | exact H3 | exact H4 | exact H5 | exact H6 | exact H7 |].
  eapply SPJ_nsteps; [exact HN | exact Hw].
Qed.

Lemma landA_sound : ltac2:(tb__ "0|1|
S2dS76A1S1S1S2dS30S0S0A2A1M0G0S4bS4bS42S2cSd0R7R6R5R4R3R2R1A7S2fA3S2S63S46Vsegs;VJGv;R7R5A2R9R2R1A5S44S2S2S46Vsegs;VJGv;R8R6A2RaR1R3A5Lrho';A2F_;Fw;Frho;F_;Famj;Fami;Ftvj;Ftvi;FA;FT;Fns;").
Proof using FB Kc ML P0f rho0. intros ns. exact (landAs_sound ns []). Qed.

Lemma landAs_TR : ltac2:(tb__ "0|2|
S2dS76A1S78S1S1S2dS30S0S0A2M0A1M1G1G1S4bS4bS2S64S42S2cScfRbRaR9R8R7R6R4R3A8S2fA3SbbG0R7R6A3S2VTR;S46Vsegs;VJGv;R8R6A2RbR1A4R4A2Frho';VTR;S46Vsegs;VJGv;RaR7A2RcR5A4R4A2F_;F_;F_;FFAMb;Frho;Famj;Fami;Ftvj';Ftvj;Ftvi;FA;FT;Fs0;Fns;").
Proof using FB Kc ML P0f TR_exw TR_pre rho0.
  intros ns s0 T A tvi tvj tvj' ami amj rho FAMb H HP HA.
  eapply TR_pre; [ | apply (TR_exw valuation (fun rho' w => SPJ segs (JGv tvj' amj) A rho' w)); intros a; apply HA].
  intros w Hw. destruct (landAs_sound ns s0 T A tvi tvj ami amj H rho w Hw) as (rho' & [Hs HJ]).
  exists rho'. split; [exact Hs|]. eapply JGA_tv_perm; [exact HP | exact HJ].
Qed.

Lemma landA_TR : ltac2:(tb__ "0|2|
S2dS76A1S1S1S2dS30S0S0A2M0A1M1G1G1S4bS4bS2S64S42S2cSd0RaR9R8R7R6R4R3A7S2fA3SbbG0R7R6A3S2VTR;S46Vsegs;VJGv;R8R6A2RbR1A4R4A2Frho';VTR;S46Vsegs;VJGv;RaR7A2RcR5A4R4A2F_;F_;F_;FFAMb;Frho;Famj;Fami;Ftvj';Ftvj;Ftvi;FA;FT;Fns;").
Proof using FB Kc ML P0f TR_exw TR_pre rho0. intros ns. exact (landAs_TR ns []). Qed.
End TRX.
End ContA.

Section NK.
Variable segs : list Segment.
Lemma SPJ_nsteps_keepfacts : ltac2:(tb__ "0|0|
S47S2dS76A1S2S1S2dS4A1S1S63S42S31S1A1S77Sb6R4R3A2R6A2S35S1R2A2A3S42S2cS6aS4S4S6bS4S16R1A1S6R6A1A3Lf;R4A3S2fA3S42S2cSb5S5R4A1S5R6A1A2S2fA3S46Vsegs;RaR7R8R4A5S46Vsegs;RbSb6R6S6R8A1A2R9R5A5F_;F_;F_;F_;Fw;FX;FF0;FS;Frho;Fns;FJ;").
Proof using .
  intros J ns rho S F0 X w Hrun Hsub Hnx [Hsm HJ].
  assert (HF : Forall (holds rho) (ss_facts S)).
  { destruct w as [tr [ms md]]. exact (smatch_facts_hold segs _ _ _ Hsm). }
  assert (Hwf : swf S = true) by exact (smatch_swf segs _ _ _ Hsm).
  assert (Hmin : SPJ segs J (with_facts S F0) rho w).
  { split; [|exact HJ]. apply smatch_refacts; [exact Hsm| |].
    - apply forallb_forall. intros f Hf. pose proof (proj1 (forallb_forall _ _) Hsub f Hf) as Hx.
      apply existsb_exists in Hx as (g & Hg & He). apply sprop_eqb_sound in He. subst g.
      unfold swf in Hwf. repeat (apply andb_prop in Hwf as [Hwf ?]). exact (proj1 (forallb_forall _ _) H f Hg).
    - apply Forall_forall. intros f Hf. pose proof (proj1 (forallb_forall _ _) Hsub f Hf) as Hx.
      apply existsb_exists in Hx as (g & Hg & He). apply sprop_eqb_sound in He. subst g.
      exact (proj1 (Forall_forall _ _) HF f Hg). }
  pose proof (SPJ_nsteps segs J ns rho _ _ w Hrun Hmin) as [HsmX HJX].
  split; [|exact HJX]. apply smatch_refacts; [exact HsmX| |exact HF].
  apply Pos.eqb_eq in Hnx. unfold with_facts. cbn [ss_next]. rewrite Hnx.
  unfold swf in Hwf. repeat (apply andb_prop in Hwf as [Hwf ?]). assumption.
Qed.
End NK.

Section GC.
Variable segs : list Segment.
Lemma SPJ_subfacts : ltac2:(tb__ "0|0|
S47S2S1S2dS4A1S63S42S2cS6aS4S4S6bS4S16R1A1S6R4A1A3Lf;R2A3S2fA3S46Vsegs;R6R4R5R2A5S46Vsegs;R7Sb6R5R4A2R6R3A5F_;F_;Fw;FF;FS;Frho;FJ;").
Proof using .
  intros J rho S F w Hsub [Hsm HJ]. split; [|exact HJ].
  assert (HF : Forall (holds rho) (ss_facts S)).
  { destruct w as [tr [ms md]]. exact (smatch_facts_hold segs _ _ _ Hsm). }
  pose proof (smatch_swf segs _ _ _ Hsm) as Hwf.
  apply smatch_refacts; [exact Hsm| |].
  - apply forallb_forall. intros f Hf. pose proof (proj1 (forallb_forall _ _) Hsub f Hf) as Hx.
    apply existsb_exists in Hx as (g & Hg & He). apply sprop_eqb_sound in He. subst g.
    unfold swf in Hwf. repeat (apply andb_prop in Hwf as [Hwf ?]). exact (proj1 (forallb_forall _ _) H f Hg).
  - apply Forall_forall. intros f Hf. pose proof (proj1 (forallb_forall _ _) Hsub f Hf) as Hx.
    apply existsb_exists in Hx as (g & Hg & He). apply sprop_eqb_sound in He. subst g.
    exact (proj1 (Forall_forall _ _) HF f Hg).
Qed.
End GC.

Section Join.
Variable segs : list Segment.
Definition has_zero4_at (cells : list cell) (off : Z) : bool := ltac2:(tb__ "0|8|
S6bS7S7S0S2cLx;M0S1bR1A1S3fG0S1cR2A1S3fS3fS2cLz;R1S36S36S70S1dR3A1Z4A2Se9R2A1A2S70R2Voff;A2A2S40S2eLp;M1G1X3fx3Lz;S40S2eLi;M2S90S0S0S2eLb;La;M3Lop;M4G4S8fG3Lop;M5G5S2cS41S0S2eLa;Lw;Lsgn;M6S40S0S3fS2eLk;Li;Ll;M7X0x8Lo0;G2G4G4G5G5G6G7X0x8Lc;Vcells;A3").
Definition join_ok (o : sobj) (off : Z) : bool := ltac2:(tb__ "0|1|
S36Sd6SeVo;A1M0Voff;A2Sd6G0S72Voff;Z4A2A2A2").
Definition add_cell8 (o : sobj) (off : Z) : sobj := ltac2:(tb__ "0|0|
S20SdVo;A1S12Vo;A1S11Vo;A1S38S7S1fS9Voff;A1Z8S9Z0A1A3SeVo;A1A3S10Vo;A1A5").
Definition joincell_at (S : sstate) (i : nat) (off : Z) : option sstate := ltac2:(tb__ "0|3|
S31S3A1S31S1A1M0Lx;S6cS3SaVS;A1M1Vi;A3S3S2cG0L_;Sd8R1Voff;A2S35S1S95VS;S32S3S8cS3Vi;G1A3S38S3Sd7R1Voff;A2S8dS3S3dVi;A1G1A3A3A3A2A2S3aS1A1M2X2cx2Lo;G2X31x2").

Lemma has_zero4_at_sound : ltac2:(tb__ "0|3|
S2S0S3fS3fS6dS2dS7A1S3fS8aS7S24R7R6R5R4R3A5R2A3S42S2cSd6R3R2A2S2fA3S43S6eR7R3A2S43S6eS72R3Z4A2R6A2S43S43S6eS74S75Z2Z3eA2M0A1R3A2S6fR3G0A2A2S42S31S2dSc7Q8A1A1M1A1S28R5S25R9R8R3A3U4M2A3S35G1S1eG2Sc6Q40Z0A2A2A2A3A2A2A2F_;F_;Foff;Fcells;Fms;Fhi;Flo;Fbase;Frho;").
Proof using .
  intros rho base lo hi ms cells off HC H. unfold has_zero4_at in H. apply existsb_exists in H as (c & Hin & Hc).
  destruct c as [co cw cv]. cbn [c_off c_val c_width] in Hc.
  destruct co as [o0| | | | | | |]; try discriminate. destruct cv as [z| | | | | | |]; try discriminate. destruct z; try discriminate.
  apply andb_prop in Hc as [Hc Ho]. apply andb_prop in Hc as [Hw Hs]. apply Z.eqb_eq in Hw. apply Z.eqb_eq in Ho. subst cw o0.
  unfold small_lit in Hs. apply andb_prop in Hs as [Hs1 Hs2]. apply Z.leb_le in Hs1. apply Z.ltb_lt in Hs2.
  pose proof (proj1 (Forall_forall _ _) HC _ Hin) as (C1 & C2 & C3). cbn [c_off c_width c_val] in C1, C2, C3.
  rewrite soff_lit_small in C1, C2, C3 by lia. rewrite eval_lit0 in C3. repeat split; try lia. exact C3.
Qed.

Lemma add_cell8_holds : ltac2:(tb__ "0|0|
S2S6dS3S3fS42S2cSd8R2R1A2S2fA3ScVsegs;R5R4R3A4ScVsegs;R6R5Sd7R4R3A2A4F_;F_;Foff;Fo;Fms;Frho;").
Proof using .
  intros rho ms o off Hok (Hb & Hw & Hc & Hd & Hi). unfold join_ok in Hok. apply andb_prop in Hok as [H1 H2].
  destruct (has_zero4_at_sound rho (ob_base o) _ _ ms _ _ Hc H1) as (A1 & A2 & A3 & A4).
  destruct (has_zero4_at_sound rho (ob_base o) _ _ ms _ _ Hc H2) as (B1 & B2 & B3 & B4).
  unfold obj_holds, obj_lo_of, obj_hi_of in *. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt add_cell8] in *.
  split; [exact Hb|]. split; [exact Hw|]. split; [|split; [|exact Hi]].
  - constructor; [|exact Hc]. unfold cell_holds. cbn [c_off c_width c_val]. rewrite soff_lit_small by lia.
    split; [lia|]. split; [lia|]. rewrite eval_lit0.
    change (Z.to_nat 8) with (4 + 4)%nat.
    replace (enc_bytes (4 + 4) (Z_to_bv 64 0)) with (enc_bytes 4 (Z_to_bv 64 0) ++ enc_bytes 4 (Z_to_bv 64 0)) by reflexivity.
    apply rd_bytes_app; [exact A4|].
    replace (oaddr rho (ob_base o) off + Z_to_bv 64 (Z.of_nat 4))%bv with (oaddr rho (ob_base o) (off + 4)); [exact B4|].
    unfold oaddr. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). change (Z.of_nat 4 mod 2 ^ 64) with 4. rewrite Zplus_mod_idemp_l. f_equal. lia.
  - intros off' Hoff' Hncov. apply (Hd off' Hoff'). intros Hcov. apply Hncov. unfold covered in *. constructor 2. exact Hcov.
Qed.

Lemma SPJ_joincell : ltac2:(tb__ "0|0|
S47S2S1S37S3fS1S63S42S31S1A1Sd9R5R4R3A3S35S1R2A2A3S42S2cSb7R6R3A2S2fA3S46Vsegs;R9R7R8R3A5S46Vsegs;RaR5R9R4A5F_;F_;F_;Fw;FS';Foff;Fi;FS;Frho;FJ;").
Proof using .
  intros J rho S i off S' [tr [ms md]] H Hsame Hw.
  eapply SPJ_reobj; [exact Hsame | exact Hw |].
  destruct Hw as [Hsm _]. cbn [w_cfg cfg_ms].
  destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmem & _). cbn [fst snd cfg_ms cfg_model] in Hmem.
  unfold joincell_at in H. destruct (nth_error (ss_objs S) i) as [o|] eqn:Hi; [|discriminate].
  destruct (join_ok o off) eqn:Hok; [|discriminate]. injection H as <-. cbn [ss_objs set_objs].
  rewrite (split_at_nth (ss_objs S) i o Hi) in Hmem.
  destruct Hmem as (Hall & Hpd & Hfr). split; [|split].
  - rewrite !Forall_app in Hall |- *. destruct Hall as (A & B). split; [exact A|]. inversion B; subst. constructor; [|assumption].
    apply add_cell8_holds; assumption.
  - apply (proj2 (pairwise_disjoint_pdr rho _)). rewrite map_app. cbn [map].
    replace (obj_range rho (add_cell8 o off)) with (obj_range rho o) by reflexivity.
    apply (proj1 (pairwise_disjoint_pdr rho _)) in Hpd. rewrite map_app in Hpd. exact Hpd.
  - unfold mem_frame, outside_all in *. intros a Ha. apply Hfr.
    rewrite Forall_app in Ha |- *. destruct Ha as [Ha1 Ha2]. split; [exact Ha1|]. inversion Ha2; subst. constructor; assumption.
Qed.
End Join.

Section Kit.
Variable segs : list Segment.
Fixpoint sv_closed (v : sv) : bool :=
  match v with
  | SLit _ => true | SVar _ => false
  | SAlu _ a b | SAluW _ a b | SMd _ a b | SMdW _ a b => sv_closed a && sv_closed b
  | SExt _ _ a => sv_closed a | SLBytes _ i _ => sv_closed i
  end.
Definition sprop_closed (p : sprop) : bool := ltac2:(tb__ "0|3|
S4S2cLp;Vp;S92S0S0S36Sc3R2A1Sc3R1A1A2Lb;La;M0Lc;M1S4S4S2cLq;R1G1S4S2eLp0;G0G0G0S2eS40S3fS2eLa;Li;M2X4x7Lq;G0G0G0S2fG2X4x7").
Fixpoint gc_facts (l : list sprop) : list sprop :=
  match l with [] => [] | f :: r => if sprop_closed f || existsb (sprop_eqb f) r then gc_facts r else f :: gc_facts r end.
Lemma gc_facts_sub : ltac2:(tb__ "0|0|
S2dS4A1S4S69S4R1Sc0R2A1A3S69S4R2R3A3F_;Ff;Fl;").
Proof using . induction l as [|g r IH]; intros f H; cbn in H; [exact H|]. destruct (sprop_closed g || existsb (sprop_eqb g) r); [right; exact (IH f H)|]. destruct H as [<-|H]; [left; reflexivity | right; exact (IH f H)]. Qed.
Definition gcS (S : sstate) : sstate := ltac2:(tb__ "0|0|
Sb6VS;Sc0S6VS;A1A1A2").

Definition renormK (F0 : list sprop) (prog : list nstep) (T : sstate) : option sstate := ltac2:(tb__ "0|2|
S31S1A1M0G0Lx;S77Sb6Sc1VT;A1M1VF0;A2Vprog;A2S1S35S1Sb6R1S6G1A1A2A2LX;S3aS1A1X31x2").
Definition subsetb (F G : list sprop) : bool := ltac2:(tb__ "0|0|
S6aS4S4S6bS4S16R1A1VG;A3Lf;VF;A3").
Lemma subsetb_In : ltac2:(tb__ "0|1|
S2dS4A1M0G0S4S42S2cSbfR3R2A2S2fA3S69S4R2R4A3S69S4R3R4A3F_;F_;Ff;FG;FF;").
Proof using .
  intros F G f H Hf. pose proof (proj1 (forallb_forall _ _) H f Hf) as Hx. apply existsb_exists in Hx as (g & Hg & He).
  apply sprop_eqb_sound in He. subst g. exact Hg.
Qed.

Lemma SPJ_renormK : ltac2:(tb__ "0|1|
S47S2dS4A1S2dS76A1S1S1S2S63S42S31S1A1Sc2R6R5R4A3S35S1R3A2A3S42S2cSbfSc0S6R5A1M0A1G0A2S2fA3S42S2cSbfR8S6Sc1R6A1A1A2S2fA3S42S2cSb5S5R6A1S5R7A1A2S2fA3S46Vsegs;RbR8R6R5A5S46Vsegs;RcR8R7R6A5F_;F_;F_;F_;F_;Fw;Frho;FX;FT;Fprog;FF0;FJ;").
Proof using .
  intros J F0 prog T X rho w HR Hgc Hsub Hnx Hw. unfold renormK in HR.
  destruct (run_nsteps (with_facts (gcS T) F0) prog) as [X0|] eqn:E; [|discriminate]. injection HR as <-.
  assert (Hg : SPJ segs J (gcS T) rho w) by (unfold gcS; apply SPJ_subfacts; [exact Hgc | exact Hw]).
  apply (SPJ_nsteps_keepfacts segs J prog rho (gcS T) F0 X0 w E Hsub).
  - unfold with_facts in Hnx |- *. cbn [ss_next] in Hnx |- *. exact Hnx.
  - exact Hg.
Qed.

Definition cont_check (F0 : list sprop) (prog : list nstep) (T A : sstate) : bool := ltac2:(tb__ "0|5|
S31S1A1S2cLx;Sc2VF0;Vprog;VT;A3S1S36S36S36S36SbfSc0S6VT;A1M0A1G0A2SbfVF0;S6Sc1VT;A1A1A2A2Sb5S5R1A1S5VT;A1A2A2S2bVA;A1A2S31S30S2dS30S0S0A2M1A1M2S2dS4A1M3A2M4A1S2cLx;Sb8R1VA;A2G4G4S2cLp;R1G2G3G2S2cLl;R2G3S2cLl0;R1S2fS4G3S2eLl1;Ls;X2dx2G1G2S2eLl1;Lp0;X2dx2Ll0;Ll;X30x1Lp;S2eX31x2A2LX;S2eX31x2").
Lemma cont_sound : ltac2:(tb__ "0|0|
S47S2dS4A1S2dS76A1S1S1S2S63S42S2cSc4R6R5R4R3A4S2fA3S46Vsegs;R8R5R3R2A5S46Vsegs;R9R5R4R3A5F_;F_;Fw;Frho;FA;FT;Fprog;FF0;FJ;").
Proof using .
  intros J F0 prog T A rho w H Hw. unfold cont_check in H.
  destruct (renormK F0 prog T) as [X|] eqn:HR; [|discriminate].
  apply andb_prop in H as [H Hd]. apply andb_prop in H as [H Hwf]. apply andb_prop in H as [H Hnx]. apply andb_prop in H as [Hgc Hsub].
  destruct (state_diff X A) as [[[|] [|]]|] eqn:Hsd; try discriminate.
  eapply SPJ_restate; [exact Hwf | exact Hsd | constructor | constructor |].
  eapply SPJ_renormK; eauto.
Qed.

Definition reent_check (F : list sprop) (n : positive) (vA : sv) (rA rE : Z) (vE : sv) : bool := ltac2:(tb__ "0|0|
S36S36S36S18Vn;VvA;A2S18Vn;VvE;A2A2S71Z0VrA;A2A2S3cS73VrA;VrE;A2S36S70VrA;VrE;A2S96VF;VvA;Z1VvE;A4A2A2A2").
Lemma reent_sound : ltac2:(tb__ "0|1|
S2dS4A1S40S0S3fS3fS0S2S2S42S2cSc5R8R7R6R5R4R3A6S2fA3S8aS4S8R3A1R9A3S7eR9R4R3A3S43S6eZ0S93R8R9R4A3M0A2S6fG0S93R7R6R5A3A2A2F_;F_;F_;Frho';Frho;FvE;FrE;FrA;FvA;Fn;FF;").
Proof using .
  intros F n vA rA rE vE rho rho' H HF Hag. unfold reent_check in H.
  apply andb_prop in H as [H Hdec]. apply andb_prop in H as [H H0]. apply andb_prop in H as [HbA HbE].
  apply Z.leb_le in H0. unfold emeasZ.
  rewrite <- (eval_agree_vals n rho rho' vA Hag HbA).
  pose proof (urange (eval rho vA)) as R1. pose proof (urange (eval rho vE)) as R2.
  apply orb_prop in Hdec. destruct Hdec as [Hlt|Heq].
  - apply Z.ltb_lt in Hlt. nia.
  - apply andb_prop in Heq as [Heq Hu]. apply Z.eqb_eq in Heq. subst rE.
    pose proof (uleq_sound rho _ _ 1 _ HF Hu) as U1. unfold U in U1. lia.
Qed.
End Kit.

Section Permb.
Definition tve_eqb (a b : sv * sv) : bool := ltac2:(tb__ "0|0|
S36S13S33S0S0Va;A3S33S0S0Vb;A3A2S13S34S0S0Va;A3S34S0S0Vb;A3A2A2").
Lemma tve_eqb_sound : ltac2:(tb__ "0|1|
S30S0S0A2M0G0S42S2cSf3R2R1A2S2fA3S42G0R3R2A3F_;Fb;Fa;").
Proof.
  intros [a1 a2] [b1 b2] H. unfold tve_eqb in H. cbn [fst snd] in H. apply andb_prop in H as [H1 H2].
  apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. congruence.
Qed.
Fixpoint rm_first (x : sv * sv) (l : list (sv * sv)) : option (list (sv * sv)) :=
  match l with
  | [] => None
  | y :: r => if tve_eqb x y then Some r else match rm_first x r with Some r' => Some (y :: r') | None => None end
  end.
Lemma rm_first_perm : ltac2:(tb__ "0|2|
S30S0S0A2M0S2dG0A1M1G1S42S31G1A1Sf2R3R2A2S35G1R1A2A3SbbG0R3S38G0R4R2A3A3F_;Fl';Fl;Fx;").
Proof.
  intros x l. induction l as [|y r IH]; intros l' H; cbn in H; [discriminate|].
  destruct (tve_eqb x y) eqn:E.
  - injection H as <-. apply tve_eqb_sound in E. subst y. apply Permutation_refl.
  - destruct (rm_first x r) as [r'|] eqn:E2; [|discriminate]. injection H as <-.
    apply (Permutation_trans (perm_skip y (IH r' eq_refl))). apply perm_swap.
Qed.
Fixpoint permb (l1 l2 : list (sv * sv)) : bool :=
  match l1 with
  | [] => match l2 with [] => true | _ => false end
  | x :: r => match rm_first x l2 with Some l2' => permb r l2' | None => false end
  end.
Lemma permb_sound : ltac2:(tb__ "0|2|
S2dS30S0S0A2M0A1M1G1S42S2cSf1R2R1A2S2fA3SbbG0R3R2A3F_;Fl2;Fl1;").
Proof.
  induction l1 as [|x r IH]; intros l2 H; cbn in H.
  - destruct l2; [apply Permutation_refl | discriminate].
  - destruct (rm_first x l2) as [l2'|] eqn:E; [|discriminate].
    apply (Permutation_trans (perm_skip x (IH l2' H))). apply Permutation_sym. apply rm_first_perm. exact E.
Qed.
End Permb.

Section NoneMode.
Variable segs : list Segment.
Variable C : mconsts.
Variable Kc : ltac2:(tb__ "0|0|
S2dS68A1S67OF_;F_;").
Variable P0c : ltac2:(tb__ "0|0|
S2dS30S3fS3fA2A1S2OF_;F_;").
Variable PD : ltac2:(tb__ "0|0|
S2dS30S1S2dS30S0S0A2A1A2A1").
Definition PDAnone : list (sstate * (list (sv * sv) * amode)) := ltac2:(tb__ "0|3|
S8bS30S1S2dS30S0S0A2A1M0A2M1S30S1S30G0S4bA2M2A2G1S39S1G2S33S1G0R1A3S39G0S4bS34S1G0R1A3S4eA4A4Ld;VPD;A4").

Lemma SPJ_JGA_pre_none : ltac2:(tb__ "0|0|
S2dS30S3fS3fA2A1S2dS30S0S0A2A1S1S2S63S46Vsegs;S52Vsegs;VC;VKc;VP0c;R5A1R5R4S4eA7R3R2R1A5S46Vsegs;S9cVsegs;VC;VKc;VP0c;R6A1R6R5A6R4R3R2A5F_;Fw;Frho;FS;Ftv;FFBc;").
Proof using . intros FBc tv S rho w [Hs HJ]. split; [exact Hs|]. apply (proj1 (JGA_pre_none segs C Kc (P0c FBc) FBc tv _ _ _)). exact HJ. Qed.

Lemma LQP_PostsC_none : ltac2:(tb__ "0|0|
S2dS30S3fS3fA2A1S40S2S63S7fVsegs;R3R2S9dVsegs;VC;VKc;VP0c;VPD;R4A6R1A5S7fVsegs;R4R3S53Vsegs;VC;VKc;VP0c;SdaR5A6R2A5F_;Fw;Frho1;Fn;FFBc;").
Proof using .
  intros FBc n rho1 w (L & JL & rho' & Hin & Hag & Hsm & HJL).
  unfold PostsC in Hin. apply in_map_iff in Hin as ([Ld tvL] & Heq & Hd). cbn [fst snd] in Heq. injection Heq as HL HJLe. subst L JL.
  exists Ld, (JLGA segs C Kc (P0c FBc) FBc tvL ANone), rho'.
  split; [unfold PostsCA, PDAnone; rewrite map_map; apply in_map_iff; exists (Ld, tvL); split; [reflexivity | exact Hd]|].
  split; [exact Hag|]. split; [exact Hsm|].
  destruct HJL as (Hk & Ai & HM & HP & HN & HK & HP0). exists Ai. split; [|exact I]. auto 10.
Qed.

Lemma JG_sum_none : ltac2:(tb__ "0|2|
S63OF_;S40S1S2dS30S0S0A2A1S2dS30S3fS3fA2A1M0S2S66Vsegs;R6S46Vsegs;S9cVsegs;VC;VKc;VP0c;R2A1M1R2R3A6R4R1A4S7fVsegs;R5R1S9dVsegs;VC;VKc;VP0c;VPD;R2A6A4A4Frho1;FFBc;G0S2S66Vsegs;R7S46Vsegs;S52Vsegs;VC;VKc;G1R2R4S4eA7R5R1A4S7fVsegs;R6R1S53Vsegs;VC;VKc;VP0c;SdaR2A6A4A4Frho1;FFBc;F_;FtvC;FPreC;FNPc;Fok;").
Proof using .
  intros ok NPc PreC tvC SUM FBc rho1.
  eapply triple_conseq; [intros w Hw; apply SPJ_JGA_pre_none; exact Hw | intros w Hw; apply LQP_PostsC_none; exact Hw | apply SUM].
Qed.
Lemma JG_sum_none_ex : ltac2:(tb__ "0|2|
S40S1S2dS30S0S0A2A1S2dS30S3fS3fA2A1M0S2S65Vsegs;S46Vsegs;S9cVsegs;VC;VKc;VP0c;R2A1M1R2R3A6R4R1A4S7fVsegs;R5R1S9dVsegs;VC;VKc;VP0c;VPD;R2A6A4A3Frho1;FFBc;G0S2S65Vsegs;S46Vsegs;S52Vsegs;VC;VKc;G1R2R4S4eA7R5R1A4S7fVsegs;R6R1S53Vsegs;VC;VKc;VP0c;SdaR2A6A4A3Frho1;FFBc;F_;FtvC;FPreC;FNPc;").
Proof using .
  intros NPc PreC tvC SUM FBc rho1.
  eapply etriple_conseq; [intros w Hw; apply SPJ_JGA_pre_none; exact Hw | intros w Hw; apply LQP_PostsC_none; exact Hw | apply SUM].
Qed.
End NoneMode.

Section ClientSite.
Variable segs : list Segment.
Variable C : mconsts.
Variable NP : positive.
Variable Kc : ltac2:(tb__ "0|0|
S2dS68A1S67OF_;F_;").
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Hypothesis ML : malloc_laws segs C.
Hypothesis HNP : NP_ok NP.
Variable P0c : ltac2:(tb__ "0|0|
S2dS30S3fS3fA2A1S2OF_;F_;").
Variable PreC : sstate.
Variable tvC : list (sv * sv).
Variable amC : amode.
Variable PDA : ltac2:(tb__ "0|0|
S2dS30S1S30S2dS30S0S0A2A1S4bA2A2A1").
Variable NPc : positive.
Hypothesis HnextPre : ltac2:(tb__ "0|0|
S42S40S5VPreC;A1VNPc;A3").
Variable F0 : list sprop.
Variable extra : sobj -> bool.

Let JGv (tv : list (sv * sv)) (am : amode) : jpred := ltac2:(tb__ "0|0|
S4cVsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;Vtv;Vam;A9").

Definition cdesc : Type := (list nstep * aedesc)%type.

Definition post_check (Cl : sstate) (s : wsub) (R : list sobj) (kept : list (sv * sv)) (rE : Z) (vE : sv)
           (d : sstate * (list (sv * sv) * amode)) (c : cdesc) : bool := ltac2:(tb__ "0|9|
S88Vs;VNPc;S33S1S30S2dS30S0S0A2M0A1M1S4bA2M2Vd;A3M3S5VCl;A1M4A4S78S2cS2cL_;M5Se4VF0;S33S2dS76A1M6S4dVc;A3Sa7VNPc;VCl;Vs;VR;G3A5S4fS34G6S4dVc;A3M7A1A4G5Se8S32G0Vkept;SabR1S33G1S4bS34S1G2Vd;A3M8A3A2A3S55G7A1A2G5S51S56R1S34G1S4bG8A3A2S54G7A1A2Se5S6VCl;A1G4S59G7A1S58G7A1VrE;VvE;A6S2eX2cx2S2eX2cx2S2eX2cx2Tisub;").

Fixpoint posts_check (Cl : sstate) (s : wsub) (R : list sobj) (kept : list (sv * sv)) (rE : Z) (vE : sv)
         (ds : list (sstate * (list (sv * sv) * amode))) (cs : list cdesc) : bool :=
  match ds, cs with
  | [], [] => true
  | d :: ds', c :: cs' => post_check Cl s R kept rE vE d c &&& posts_check Cl s R kept rE vE ds' cs'
  | _, _ => false
  end.

Lemma posts_check_sound : ltac2:(tb__ "0|2|
S1S78S2dS3A1S2dS30S0S0A2A1M0S3fS0S2dS30S1S30G0S4bA2A2M1A1S2dSb0A1S42S2cSb1R8R7R6R5R4R3R2R1A8S2fA3G1S69G1R1R4A3S44Sb0Sb0S43S69Sb0R1R5A3S42S2cSb2RcRbRaR9R8R7R3R1A8S2fA3A2Lc;A2F_;Fd;F_;Fcs;Fds;FvE;FrE;Fkept;FR;Fs;FCl;").
Proof using .
  intros Cl s R kept rE vE ds. induction ds as [|d0 ds IH]; intros cs H d Hd; [destruct Hd|].
  destruct cs as [|c0 cs]; [discriminate|]. cbn [posts_check] in H. apply lazy_andb_prop in H as [H0 H1].
  destruct Hd as [<-|Hd].
  - exists c0. split; [left; reflexivity | exact H0].
  - destruct (IH cs H1 d Hd) as (c & Hc & Hp). exists c. split; [right; exact Hc | exact Hp].
Qed.

Definition site_check (Cl : sstate) (s : wsub) (kept passed : list (sv * sv)) (am : amode)
           (rE : Z) (vE : sv) (conts : list cdesc) : bool := ltac2:(tb__ "0|b|
S31S2dS3A1M0A1S2cLx;Sb9VCl;VPreC;Vs;A3G0S2cS2cL_;M1S9eVC;VNP;VCl;VPreC;Vs;R1S8bS30S1S30S2dS30S0S0A2M2A1M3S4bA2M4A2M5S1S33S1G4A2VPDA;A4A7G1S89Vs;VNPc;A2G1Sb4VNP;S5VCl;A1M6A2G1S9aG6S32G2Vkept;Vpassed;A3A2G1S50G6Vam;A2G1Sa0Vs;Vpassed;VtvC;A3G1S51S56Vs;VamC;A2Vam;A2G1S6aG5G5S36S36SaeVNPc;Vs;G6S33S1G4R1A3M7S33G3S4bS34S1G4R1A3M8A3M9A5S5eVNPc;Vs;G6G7S34G3S4bG8A3MaA5A2S61VPreC;G7G9GaA4A2Ld;VPDA;A3G1S9fS6VCl;A1Vkept;S3aS37A1Vextra;R1A5Sb1VCl;Vs;R1Vkept;VrE;VvE;VPDA;Vconts;A8S2eX2cx2S2eX2cx2S2eX2cx2S2eX2cx2S2eX2cx2S2eX2cx2S2eX2cx2S2eX2cx2S2eX2cx2LR;S2eX31x2").

Section T.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S47S1S2S64S8aS4S8R2A1S6R3A1A3VTR;S46Vsegs;R5R4R3A4R2A2M0F_;G0F_;FQ;Frho;FS;FJ;").
Hypothesis TR_ex : forall (A : Type) (J : A -> jpred) S rho (Q : assn),
  (forall x, TR (SPJ segs (J x) S rho) Q) -> TR (SPJ segs (fun r t m => exists x, J x r t m) S rho) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S64S64S64S63R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|3|
S47S47S1S1S78S2dS3A1M0S2dS30S1S80A2M1A1S64S2S42S31G0A1Sb9R7R6R5A3S35G0R4A2A3S42S2cS84R8R7R6R5S8bG1S1S33S1S80A2R4A4A5S2fA3S2VTR;S46Vsegs;RbR9R1A4S7fVsegs;S5R9A1R1R6A4A2Frho1;S2dS68A1M2S6dS67S15Vsegs;R7RdS39G2SbcR3SbdR2R1A2A4A4R10R8R4R2A3R10S7aS79R9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S1S80G2S6dS67S2G2S6dS67S69G1S39S1S80R9R8A4R10A3S15Vsegs;RfR15S39G2SbcR8SbdR7R6A2A4A4R18R10R9R7A3S7eS5R16A1S7aS79R11R14R9A3R15A2R7A3S15Vsegs;R8RdS39G2SbcR7SbdR6R5A2A4A4RdS7aS79R13R16RbA3R17A2R9R8R6A4S43S87R14RcR17R18R19RfRaA7S2S86R15RdR18R19R1aR1bR10R1RbA9VTR;S46Vsegs;S83R10S7aS79R16R19ReA3R1aA2RcA3S81R1aS5R1bA1R11S5R1cA1R19A5R2A4R17A2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S46Vsegs;ReRcR6A4R7A2F_;F_;F_;F_;F_;Frho;FQ;FPosts;FR;Fs;FPre;FC0;FJp;FJ;").
Hypothesis SUMT : ltac2:(tb__ "0|0|
S2dS30S3fS3fA2A1S2VTR;S46Vsegs;S52Vsegs;VC;VKc;VP0c;R2A1R2VtvC;VamC;A7VPreC;R1A4S7fVsegs;VNPc;R1S53Vsegs;VC;VKc;VP0c;VPDA;R2A6A4A2Frho1;FFBc;").

Hypothesis Hextra : ltac2:(tb__ "0|1|
S2S2dS30S0S0A2A1S2dS3A1S3S3fVP0f;Vrho0;A1S7eVNP;Vrho0;R6A3S69S3R4R5A3S42S2cVextra;R5A1S2fA3S43S6eS33S3fS3fSfR9R6A2M0A3R5A2S6fR5S34S3fS3fG0A3A2A2S9bVsegs;VC;Vrho0;Sa2VFB;RaR9A3R6A5F_;F_;F_;F_;F_;Fa;Fo;FR;Fkept;Frho;").

Lemma tvz_app_l : ltac2:(tb__ "0|2|
S2S2dS30S0S0A2M0A1M1G1Sa1R3S32G0R2R1A3A2Sa1R4R3A2F_;Fb;Fa;Frho;").
Proof using . intros rho a b H. unfold tvz in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) H). apply in_or_app. left. exact Ht. Qed.

Theorem client_siteAT : ltac2:(tb__ "0|5|
S1S78S2dS30S0S0A2M0A1M1G1S4bS3fS0S2dSb0A1S2S64S42S2cSb3RaR9R8R7R6R5R4R3A8S2fA3S6dS2dS3A1S8aS4S8R5A1S6RdA1A3VP0f;Vrho0;A1S7eVNP;Vrho0;R7A3Sa1R8S32G0ReRdA3A2VP0c;Sa2VFB;R9RfA3S7aS79R9R5R6A3R10A2A2F_;F_;F_;F_;FR;Fms;Sb0S2S69Sb0R2R7A3S43S6eZ0S5aS34S2dS76A1M2S4dR3A3R2A2M3A2S6fG3S93RaR9R7A3A2A2VTR;S46Vsegs;VJGv;S55S34G2S4dR4A3M4A1S54G4A1A2S4fG4A1R3A4R7A2F_;F_;Frho';Fc;VTR;S46Vsegs;VJGv;S32G0RbRaA3R9A2RdR5A4R4A2F_;F_;F_;FFAMb;Frho;Fconts;FvE;FrE;Fam;Fpassed;Fkept;Fs;FCl;").
Proof using Hextra HnextPre ML HNP SUMT TR_callP TR_ex TR_facts TR_pre.
  intros Cl s kept passed am rE vE conts rho FAMb H HP0c HC. unfold site_check in H.
  destruct (entails_fr Cl PreC s) as [R|] eqn:He; [|discriminate]. cbv zeta in H.
  apply lazy_andb_prop in H as [H1 H]. apply lazy_andb_prop in H as [H2 H]. apply lazy_andb_prop in H as [H3 H].
  apply lazy_andb_prop in H as [H4 H]. apply lazy_andb_prop in H as [H5 H]. apply lazy_andb_prop in H as [H6 H].
  apply lazy_andb_prop in H as [H7 H]. apply lazy_andb_prop in H as [H8 H]. apply lazy_andb_prop in H as [H9 H10].
  apply TR_facts. intros HF.
  apply (client_callAT segs C NP Kc rho0 P0f FB ML P0c PreC tvC amC PDA NPc HnextPre TR TR_facts TR_ex TR_pre TR_callP SUMT
           Cl s R rho kept passed am FAMb He H1 H2 H3 H4 H5 H6 H7 H8).
  - intros Ai ms HF' HP0 Hav HP HN HD HZ HXA HM HT. split.
    + eapply (robjs_checkF_sound segs C rho0 FB rho (ss_facts Cl) kept extra R HF'); [exact (T_ok_T0_of NP rho0 HNP rho _ Hav HT) | exact (tvz_app_l rho _ _ HZ) | exact H9 |].
      intros o a Ho Hx Hr. eapply Hextra; eauto.
    + apply (HP0c ms R HF' HP0 Hav HZ).
  - intros d rho' Hd Hag.
    destruct (posts_check_sound Cl s R kept rE vE PDA conts H10 d Hd) as (c & Hc & Hp).
    unfold post_check in Hp. apply lazy_andb_prop in Hp as [Q1 Hp]. apply lazy_andb_prop in Hp as [Q2 Hp]. apply lazy_andb_prop in Hp as [Q3 Q4].
    apply am_eqb_sound in Q3. rewrite Q3. apply permb_sound in Q2.
    eapply TR_pre; [ | apply (HC c rho' Hc)].
    + intros w Hw. apply (cont_sound segs _ F0 (fst c) (T_afterN NPc Cl s R (fst d)) (ad_state (snd c)) rho' w Q1).
      eapply (SPJ_JGA_perm segs C NP Kc rho0 P0f FB); [exact Q2 | exact Hw].
    + unfold ameas. exact (reent_sound (ss_facts Cl) (ss_next Cl) (ad_var (snd c)) (ad_rank (snd c)) rE vE rho rho' Q4 HF Hag).
Qed.
End T.
End ClientSite.

Section PureSite.
Variable segs : list Segment.
Variable C : mconsts.
Variable NP : positive.
Variable Kc : ltac2:(tb__ "0|0|
S2dS68A1S67OF_;F_;").
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Hypothesis ML : malloc_laws segs C.
Variable PreC : sstate.
Variable PostsC : list leaf.
Variable F0 : list sprop.

Let JGv (tv : list (sv * sv)) (am : amode) : jpred := ltac2:(tb__ "0|0|
S4cVsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;Vtv;Vam;A9").

Definition ppost_check (Cl : sstate) (s : wsub) (R : list sobj) (tv : list (sv * sv)) (am : amode) (rE : Z) (vE : sv)
           (L : leaf) (c : list nstep * aedesc) : bool := ltac2:(tb__ "0|5|
S2cS2cL_;M0Se4VF0;S33S2dS76A1M1S4dVc;A3SdfS6VCl;A1M2S81Vs;S5VPreC;A1S97VL;A1S5VCl;A1M3VR;A5A2S4fS34G1S4dVc;A3M4A1A4G0S62Vtv;S55G4A1A2G0S51Vam;S54G4A1A2Se5G2G3S59G4A1S58G4A1VrE;VvE;A6S2eX2cx2S2eX2cx2S2eX2cx2").
Fixpoint pposts_check (Cl : sstate) (s : wsub) (R : list sobj) (tv : list (sv * sv)) (am : amode) (rE : Z) (vE : sv)
         (ls : list leaf) (cs : list (list nstep * aedesc)) : bool :=
  match ls, cs with
  | [], [] => true
  | L :: ls', c :: cs' => ppost_check Cl s R tv am rE vE L c &&& pposts_check Cl s R tv am rE vE ls' cs'
  | _, _ => false
  end.
Lemma pposts_check_sound : ltac2:(tb__ "0|1|
S1S78S2dS3A1S2dS30S0S0A2A1S4bS3fS0S2dS94A1S2dS30S2dS76A1S4dA2M0A1S42S2cSe1R9R8R7R6R5R4R3R2R1A9S2fA3S94S69S94R1R4A3S44G0G0S43S69G0R1R5A3S42S2cSe2RdRcRbRaR9R8R7R3R1A9S2fA3A2Lc;A2F_;FL;F_;Fcs;Fls;FvE;FrE;Fam;Ftv;FR;Fs;FCl;").
Proof using .
  intros Cl s R tv am rE vE ls. induction ls as [|L0 ls IH]; intros cs H L HL; [destruct HL|].
  destruct cs as [|c0 cs]; [discriminate|]. cbn [pposts_check] in H. apply lazy_andb_prop in H as [H0 H1].
  destruct HL as [<-|HL].
  - exists c0. split; [left; reflexivity | exact H0].
  - destruct (IH cs H1 L HL) as (c & Hc & Hp). exists c. split; [right; exact Hc | exact Hp].
Qed.

Definition pure_site_check (Cl : sstate) (s : wsub) (tv : list (sv * sv)) (am : amode) (rE : Z) (vE : sv)
           (conts : list (list nstep * aedesc)) : bool := ltac2:(tb__ "0|3|
S31S2dS3A1M0A1S2cLx;Sb9VCl;VPreC;Vs;A3G0S2cS2cL_;M1S82VCl;VPreC;Vs;R1VPostsC;A5G1Sb4VNP;S5VCl;A1M2A2G1S9aG2Vtv;A2G1S50G2Vam;A2G1S6aS4S29G2A1S6VCl;A1A3Se1VCl;Vs;R1Vtv;Vam;VrE;VvE;VPostsC;Vconts;A9S2eX2cx2S2eX2cx2S2eX2cx2S2eX2cx2S2eX2cx2LR;S2eX31x2").

Section T.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S47S1S2S64S8aS4S8R2A1S6R3A1A3VTR;S46Vsegs;R5R4R3A4R2A2M0F_;G0F_;FQ;Frho;FS;FJ;").
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S64S64S64S63R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_callJ : ltac2:(tb__ "0|3|
S47S47S47S47S1S1S78S2dS3A1M0S2dS94A1S64S2S42S31G0A1Sb9R7R6R5A3S35G0R4A2A3S42S2cS82R8R7R6R5R4A5S2fA3S2VTR;S46Vsegs;RdR9R1A4S49Vsegs;RcS5R9A1R1R6A5A2Frho1;S2dS68A1M1S6dS67S15Vsegs;R7RdS39G1SbcR3SbdR2R1A2A4A4R12R8R4R2A3R12S7aS79R9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S94S2S2G1S6dS67G1S67S69S94R8RfA3S15Vsegs;ReR14S39G1SbcR6SbdR5R4A2A4A4R19RfR7R5A3S85R10R7R13R14R15R16S97RbA1RaR9A9R19RaR6R5A3R19RcR7R6A3F_;F_;F_;F_;F_;Fmd';Ftr';Fmd;Fms;Ftr;FrhoL;Frho';FL;S94S2S69S94R2RaA3S23S5RfA1M2R9R2A3VTR;S46Vsegs;R11S81ReG2S97R4A1S5R10A1RdA5R3A4RbA2F_;F_;Frho';FL;VTR;S46Vsegs;R11RdR7A4R8A2F_;F_;F_;F_;F_;F_;Frho;FQ;FPosts;FR;Fs;FPre;FC0;FJc';FJp';FJp;FJ;").

Hypothesis SUMT : ltac2:(tb__ "0|1|
S2dS30S0S0A2A1S4bS2S2VTR;S4aVsegs;S2dS68A1S67VJGv;R6R5R4R2R1A5Lmd;Ltr;M0VPreC;R1A4S48Vsegs;G0S5VPreC;A1R1VPostsC;A5A2Frho1;Frho;Fam;Ftv;").

Theorem pure_siteAT : ltac2:(tb__ "0|4|
S1S78S2dS30S0S0A2A1S4bS3fS0S2dS30S2dS76A1M0S4dA2M1A1S2S64S42S2cSe3R9R8R7R6R5R4R3A7S2fA3G1S2S69G1R2R6A3S43S6eZ0S5aS34G0S4dR3A3R2A2M2A2S6fG2S93R9R8R6A3A2A2VTR;S46Vsegs;VJGv;S55S34G0S4dR4A3M3A1S54G3A1A2S4fG3A1R3A4R6A2F_;F_;Frho';Fc;VTR;S46Vsegs;VJGv;R9R8A2RbR4A4R3A2F_;F_;FFAMb;Frho;Fconts;FvE;FrE;Fam;Ftv;Fs;FCl;").
Proof using ML SUMT TR_callJ TR_facts TR_pre.
  intros Cl s tv am rE vE conts rho FAMb H HC. unfold pure_site_check in H.
  destruct (entails_fr Cl PreC s) as [R|] eqn:He; [|discriminate]. cbv zeta in H.
  apply lazy_andb_prop in H as [H1 H]. apply lazy_andb_prop in H as [H2 H]. apply lazy_andb_prop in H as [H3 H].
  apply lazy_andb_prop in H as [H4 H]. apply lazy_andb_prop in H as [H5 H6].
  apply TR_facts. intros HF.
  apply (pure_callAT segs C NP Kc rho0 P0f FB ML TR TR_facts TR_pre TR_callJ Cl PreC s R PostsC rho tv am FAMb (SUMT tv am rho) He H1 H2 H3 H4 H5).
  intros L rho' HL Hag.
  destruct (pposts_check_sound Cl s R tv am rE vE PostsC conts H6 L HL) as (c & Hc & Hp).
  unfold ppost_check in Hp. apply lazy_andb_prop in Hp as [Q1 Hp]. apply lazy_andb_prop in Hp as [Q2 Hp]. apply lazy_andb_prop in Hp as [Q3 Q4].
  apply pl_eqb_sound in Q2. apply am_eqb_sound in Q3.
  eapply TR_pre; [ | apply (HC c rho' Hc)].
  - intros w Hw. apply (cont_sound segs _ F0 (fst c) _ (ad_state (snd c)) rho' w Q1). rewrite <- Q2, <- Q3. exact Hw.
  - unfold ameas. exact (reent_sound (ss_facts Cl) (ss_next Cl) (ad_var (snd c)) (ad_rank (snd c)) rE vE rho rho' Q4 HF (agree_below_vals _ _ _ Hag)).
Qed.
End T.
End PureSite.

Section ToNone.
Variable segs : list Segment.
Variable C : mconsts.
Variable NP : positive.
Variable Kc : ltac2:(tb__ "0|0|
S2dS68A1S67OF_;F_;").
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Lemma SPJ_JGA_to_none : ltac2:(tb__ "0|0|
S2dS30S0S0A2A1S4bS1S2S63S46Vsegs;S4cVsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;R5R4A9R3R2R1A5S46Vsegs;S4cVsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;R6S4eA9R4R3R2A5F_;Fw;Frho;FS;Fam;Ftv;").
Proof using . intros tv am S rho w [Hs (Ai & HJ & _)]. split; [exact Hs|]. exists Ai. split; [exact HJ | exact I]. Qed.
End ToNone.

Section DropT.
Variable segs : list Segment.
Variable C : mconsts.
Variable NP : positive.
Variable Kc : ltac2:(tb__ "0|0|
S2dS68A1S67OF_;F_;").
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).

Lemma nodes_ok_remove : ltac2:(tb__ "0|1|
SdbS2S2dS30S0S0A2M0A1S2dS30S3fS3fA2A1S37S5cVFB;R5R4R3R2A5S5cVFB;R6R5S99G0R2R4A3R3A5F_;Fi;Fns;Ftv;Frho;FAi;").
Proof using .
  intros Ai rho tv ns i [HF HD]. split; [|exact HD]. apply Forall_forall. intros bc Hbc.
  destruct (proj1 (Forall_forall _ _) HF bc Hbc) as (A & B & Cc). split; [exact A|]. split; [exact B|].
  intros t Ht. apply Cc. eapply remove_nth_In. exact Ht.
Qed.

Lemma XA_remove : ltac2:(tb__ "0|1|
S4bSdbS2S2dS30S0S0A2M0A1S37S57VFB;R5R4R3R2A5S57VFB;R6R5R4S99G0R2R3A3A5F_;Fi;Ftv;Frho;FAi;Fam;").
Proof using .
  intros am Ai rho tv i HX. destruct am as [|hd|hd nx cap sl|hd g]; cbn -[HDR] in HX |- *.
  - exact I.
  - destruct HX as (ns & HA & HN). exists ns. split; [exact HA | apply nodes_ok_remove; exact HN].
  - destruct HX as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & ns & HA & HN & Hnin).
    split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|].
    split; [intros t Ht; apply X5; eapply remove_nth_In; exact Ht|]. split; [exact X6|]. split; [exact X7|].
    exists ns. split; [exact HA|]. split; [apply nodes_ok_remove; exact HN | exact Hnin].
  - destruct HX as (ns & HA & HN & HG). exists ns. split; [exact HA|]. split; [apply nodes_ok_remove; exact HN | exact HG].
Qed.

Lemma JGA_remove_nth : ltac2:(tb__ "0|1|
S2dS30S0S0A2M0A1S4bS37S2S2dS68A1S67S4cVsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;R6R5R3R2R1AcS4cVsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;S99G0R5R7A3R6R4R3R2AcF_;Fmd;Ftr;Frho;Fi;Fam;Ftv;").
Proof using .
  intros tv am i rho tr md (Ai & (Hav & Hk & HM & HP & (HN & HD & HZ) & HK & HP0) & HX).
  exists Ai. split; [|apply XA_remove; exact HX].
  split; [exact Hav|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HP|]. split; [|split; [exact HK | exact HP0]].
  split; [|split].
  - unfold tvin in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HN). eapply remove_nth_In. exact Ht.
  - apply tvd_remove. exact HD.
  - unfold tvz in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HZ). eapply remove_nth_In. exact Ht.
Qed.

Lemma SPJ_JGA_remove_nth : ltac2:(tb__ "0|1|
S2dS30S0S0A2M0A1S4bS37S1S2S63S46Vsegs;S4cVsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;R6R5A9R3R2R1A5S46Vsegs;S4cVsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;S99G0R5R7A3R6A9R4R3R2A5F_;Fw;Frho;FS;Fi;Fam;Ftv;").
Proof using . intros tv am i S rho w [Hs HJ]. split; [exact Hs | apply JGA_remove_nth; exact HJ]. Qed.
End DropT.

Section DropO.
Variable segs : list Segment.

Lemma pairwise_disjoint_remove : ltac2:(tb__ "0|1|
S2S2dS3A1M0S3G0S21R4S32S3R3S38S3R2R1A3A3A2S21R5S32S3R4R2A3A2F_;Fl2;Fo;Fl1;Frho;").
Proof using .
  intros rho l1. induction l1 as [|x l1 IH]; intros o l2 H; cbn in H |- *.
  - exact (proj2 H).
  - destruct H as [HF HP]. split; [|apply (IH o l2); exact HP].
    rewrite Forall_app in HF |- *. destruct HF as [A B]. split; [exact A|]. inversion B; subst; assumption.
Qed.

Lemma mem_match_remove_empty : ltac2:(tb__ "0|2|
S2S6dS2dS3A1M0S3G0S6eS34S3fS3fSfR5R2A2M1A3S33S3fS3fG1A3A2SbVsegs;R6S32S3R4S38S3R3R2A3A3R5A4SbVsegs;R7S32S3R5R3A3R6A4F_;F_;Fl2;Fo;Fl1;Fms;Frho;").
Proof using .
  intros rho ms l1 o l2 He (Hall & Hpd & Hfr). split; [|split].
  - rewrite Forall_app in Hall |- *. destruct Hall as [A B]. split; [exact A|]. inversion B; subst; assumption.
  - eapply pairwise_disjoint_remove. exact Hpd.
  - unfold mem_frame, outside_all in *. intros a Ha. apply Hfr. rewrite Forall_app in Ha |- *. destruct Ha as [A B].
    split; [exact A|]. constructor; [|exact B]. cbv beta. lia.
Qed.

Lemma remove_nth_split : forall {A} (l : list A) i o,
  nth_error l i = Some o -> l = firstn i l ++ o :: skipn (S i) l /\ remove_nth i l = firstn i l ++ skipn (S i) l.
Proof using .
  intros A l. induction l as [|x r IH]; intros [|i] o H; cbn in H |- *; try discriminate.
  - injection H as ->. split; reflexivity.
  - destruct (IH i o H) as [E1 E2]. split; [f_equal; exact E1 | f_equal; exact E2].
Qed.

Lemma SPJ_drop_empty : ltac2:(tb__ "0|1|
S47S2S1S37S3S63S42S31S3A1S6cS3SaR4A1R3A3S35S3R2A2A3S42S2cSb7R5S95R5S99S3R4SaR5A1A3A2A2S2fA3S2dS68A1S67RaR9R2R1A3S8aS4S8RaA1S6R9A1A3S6eS34S3fS3fSfRbR8A2M0A3S33S3fS3fG0A3A2F_;F_;Fmd;Ftr;S46Vsegs;R9R7R8R4A5S46Vsegs;RaS95R8S99S3R7SaR8A1A3A2R9R5A5F_;F_;F_;F_;Fw;Fo;Fi;FS;Frho;FJ;").
Proof using .
  intros J rho S i o [tr [ms md]] Hn Hsame He Hw.
  eapply SPJ_reobj; [exact Hsame | exact Hw |].
  destruct Hw as [Hsm HJ]. cbn [w_cfg cfg_ms].
  pose proof (smatch_facts_hold segs _ _ _ Hsm) as HF.
  destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmem & _). cbn [fst snd cfg_ms cfg_model] in Hmem, HJ.
  cbn [ss_objs set_objs]. destruct (remove_nth_split (ss_objs S) i o Hn) as [E1 E2].
  rewrite E2. rewrite E1 in Hmem. eapply mem_match_remove_empty; [| exact Hmem]. exact (He tr md HJ HF).
Qed.
End DropO.

Section FreeX.
Variable segs : list Segment.
Variable C : mconsts.
Variable E : entry_consts.
Variable NP : positive.
Variable Kc : ltac2:(tb__ "0|0|
S2dS68A1S67OF_;F_;").
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Hypothesis ML : malloc_laws segs C.

Hypothesis HNP : NP_ok NP.
Lemma pclF_caddr_free : ltac2:(tb__ "0|1|
SdbS2S2dS30S0S0A2M0A1G0S3fS2S67SedVsegs;VC;R7R2R1A5S7eVNP;Vrho0;R7A3Sa8R8Sf4SdcR9A1A1A2SaaVFB;RaA2SafVFB;RbRaR9A4S69G0R9RaA3Sa4RcRaA2S9bVsegs;VC;Vrho0;VFB;RaA5Sa9Vsegs;VC;RfS35S3fS33S3fS3fSa6ReRcA2A3A2RbA5F_;F_;F_;F_;F_;F_;F_;F_;Fmd;FrhoM;Fa;Ft;Ftv;Frho;FAi;").
Proof using Kc P0f HNP.
  intros Ai rho tv t a rhoM md HM [Hw _] [HT _] HP HN Ht Hnz [A|[A|(b & n & Hin & Hr)]]; [left; unfold T0 in A; rewrite (Hw V_TOP HNP), HT in A; exact A | right; left; exact A |].
  right; right. exists b, n. split; [exact (HP _ Hin)|]. split; [|exact Hr].
  destruct (proj1 (Forall_forall _ _) HN t Ht Hnz) as (S1 & S2 & S3).
  intros Heq. injection Heq as Heq.
  refine (blocks_bases_differ segs C Ai rhoM md (fst (tvv rho t)) (snd (tvv rho t)) b n HM _ (HP _ Hin) _ S1 ltac:(lia) _).
  - rewrite <- surjective_pairing. exact S2.
  - intros X. apply S3. rewrite (surjective_pairing (tvv rho t)), X. exact Hin.
  - unfold tvv. cbn [fst]. exact Heq.
Qed.

Theorem free_site_extA : ltac2:(tb__ "0|5|
S63OF_;S1S78S2dS3A1M0S2S2dS30S0S0A2M1A1S4bS37G1S3S2cFx;S64SeeVsegs;RbVKc;A3SacVsegs;VC;VE;A3S42S31G0A1Sb9RcSecVE;A1M2RbA3S35G0RaA2A3S42S2cS9eVC;VNP;RdG2RcRbS38S1SebVE;A1M3S3bS1A1A3A7S2fA3S42S2cSb4VNP;S5ReA1A2S2fA3S42S2cS9aS5RfA1RbA2S2fA3S42S2cS50S5R10A1RbA2S2fA3S42S31G1A1S6cG1RdRbA3S35G1RaA2A3S42S2cS13S33S0S0RbA3S7bR11PcA2A2S2fA3S42S2cS13S34S0S0RcA3S7bR12PdA2A2S2fA3S42S2cS6bS4S16S1aS19S91S33S0S0RdA3S9Z0A1A3A1A1S6R14A1A3S2fA3S42S2cS9fS6R15A1R11S35S37RfA2S3S2cS2cL_;S5bR11R1A2S2fReR1A1X2cx2Lo;R13A5S2fA3S3S3fS69S3R2R16A3S42S2cR11R3A1S2fA3VP0f;Vrho0;A1S7eVNP;Vrho0;R18A3S8aS4S8R19A1S6R1cA1A3S43S6eS33S3fS3fSfR1aR7A2M4A3R6A2S6fR6S34S3fS3fG4A3A2A2S9bVsegs;VC;Vrho0;VFB;R7A5F_;F_;F_;F_;F_;F_;Fa;Fo;S2S7eS5R18A1R15R1A3S66Vsegs;R1aS46Vsegs;S4cVsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;S99G1R13R15A3R14A9Sa3R19R18R17G3A4R2A4R10A4F_;Frho';S66Vsegs;R19S46Vsegs;S4cVsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;R14R13A9R18R15A4RfA4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fextra;Ft;Fi;Fam;Ftv;Frho;FR;Fs;FCl;Fok;").
Proof using ML HNP.
  intros ok Cl s R rho tv am i t extra Q Hok MC He Hchk Hnf Hnb Hamb Hnth H12 H13 Hnz Hrc Hext Tfree.
  apply sv_eqb_sound in H12. apply sv_eqb_sound in H13.
  apply (free_callA segs C E NP Kc rho0 P0f FB ML ok Cl s R rho tv am i t Q Hok MC He Hchk Hnf Hnb Hamb Hnth); [|exact Tfree].
  intros Ai HF HP0 Hav HP HN HD HZ HXA (rhoM & md & HM) HT.
  apply existsb_exists in Hnz as (f & Hf & Hfe). apply sprop_eqb_sound in Hfe. subst f.
  pose proof (proj1 (Forall_forall _ _) HF _ Hf) as Hnz.
  assert (Tnz : tnz rho t) by (rewrite (surjective_pairing t); apply (tnz_of_fact rho (fst t) (snd t)); exact Hnz).
  rewrite <- H12, <- H13. split; [exact Tnz|]. split; [reflexivity|].
  eapply (robjs_check_sound segs C FB Ai rho (ss_facts Cl) tv (Some i) _ R _ rhoM md HM HT HF HN HD HZ Hrc).
  - intros o a Ho Hx Hr. change (bv_unsigned (eval rho (fst t))) with (fst (tvv rho t)).
    apply lazy_orb_prop in Hx as [Hx|Hx].
    + exact (hdr_obj_caddr_free segs C FB am Ai rho tv o a t rhoM md HM HN (nth_error_In _ _ Hnth) Tnz HXA Hx Hr).
    + exact (pclF_caddr_free Ai rho tv t a rhoM md HM Hav HT HP HN (nth_error_In _ _ Hnth) Tnz (Hext o a Ho Hx HP0 Hav HF Hr)).
  - exists t. split; [exact Hnth|]. split; [exact Tnz|reflexivity].
Qed.

Theorem free_site_extA_ex : ltac2:(tb__ "0|5|
S1S78S2dS3A1M0S2S2dS30S0S0A2M1A1S4bS37G1S3S2cFx;S64SefVKc;A1SadVsegs;VC;VE;A3S42S31G0A1Sb9RcSecVE;A1M2RbA3S35G0RaA2A3S42S2cS9eVC;VNP;RdG2RcRbS38S1SebVE;A1M3S3bS1A1A3A7S2fA3S42S2cSb4VNP;S5ReA1A2S2fA3S42S2cS9aS5RfA1RbA2S2fA3S42S2cS50S5R10A1RbA2S2fA3S42S31G1A1S6cG1RdRbA3S35G1RaA2A3S42S2cS13S33S0S0RbA3S7bR11PcA2A2S2fA3S42S2cS13S34S0S0RcA3S7bR12PdA2A2S2fA3S42S2cS6bS4S16S1aS19S91S33S0S0RdA3S9Z0A1A3A1A1S6R14A1A3S2fA3S42S2cS9fS6R15A1R11S35S37RfA2S3S2cS2cL_;S5bR11R1A2S2fReR1A1X2cx2Lo;R13A5S2fA3S3S3fS69S3R2R16A3S42S2cR11R3A1S2fA3VP0f;Vrho0;A1S7eVNP;Vrho0;R18A3S8aS4S8R19A1S6R1cA1A3S43S6eS33S3fS3fSfR1aR7A2M4A3R6A2S6fR6S34S3fS3fG4A3A2A2S9bVsegs;VC;Vrho0;VFB;R7A5F_;F_;F_;F_;F_;F_;Fa;Fo;S2S7eS5R18A1R15R1A3S65Vsegs;S46Vsegs;S4cVsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;S99G1R13R15A3R14A9Sa3R19R18R17G3A4R2A4R10A3F_;Frho';S65Vsegs;S46Vsegs;S4cVsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;R14R13A9R18R15A4RfA3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fextra;Ft;Fi;Fam;Ftv;Frho;FR;Fs;FCl;").
Proof using ML HNP.
  intros Cl s R rho tv am i t extra Q Hvi MCX He Hchk Hnf Hnb Hamb Hnth H12 H13 Hnz Hrc Hext Tfree.
  apply sv_eqb_sound in H12. apply sv_eqb_sound in H13.
  apply (free_callA_ex segs C E NP Kc rho0 P0f FB ML Cl s R rho tv am i t Q Hvi MCX He Hchk Hnf Hnb Hamb Hnth); [|exact Tfree].
  intros Ai HF HP0 Hav HP HN HD HZ HXA (rhoM & md & HM) HT.
  apply existsb_exists in Hnz as (f & Hf & Hfe). apply sprop_eqb_sound in Hfe. subst f.
  pose proof (proj1 (Forall_forall _ _) HF _ Hf) as Hnz.
  assert (Tnz : tnz rho t) by (rewrite (surjective_pairing t); apply (tnz_of_fact rho (fst t) (snd t)); exact Hnz).
  rewrite <- H12, <- H13. split; [exact Tnz|]. split; [reflexivity|].
  eapply (robjs_check_sound segs C FB Ai rho (ss_facts Cl) tv (Some i) _ R _ rhoM md HM HT HF HN HD HZ Hrc).
  - intros o a Ho Hx Hr. change (bv_unsigned (eval rho (fst t))) with (fst (tvv rho t)).
    apply lazy_orb_prop in Hx as [Hx|Hx].
    + exact (hdr_obj_caddr_free segs C FB am Ai rho tv o a t rhoM md HM HN (nth_error_In _ _ Hnth) Tnz HXA Hx Hr).
    + exact (pclF_caddr_free Ai rho tv t a rhoM md HM Hav HT HP HN (nth_error_In _ _ Hnth) Tnz (Hext o a Ho Hx HP0 Hav HF Hr)).
  - exists t. split; [exact Hnth|]. split; [exact Tnz|reflexivity].
Qed.
End FreeX.
