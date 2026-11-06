(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "ss_next"; "sprop"; "sobj"; "SLit"; "ss_facts"; "SVar"; "ss_objs"; "rw"; "sstate"; "agree_below"; "sv_below"; "SPUle"; "mkObj"; "mkSS"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "swf"; "SAlu"; "SPBranch"; "SPNot"; "holds"; "obj_holds"; "obj_range"; "soff"; "sprop_eqb"; "DUnknown"; "cell"; "eval"; "odefault"; "rm"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "prod"; "app"; "cons"; "nil"; "None"; "fst"; "length"; "nat"; "snd"; "pair"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.PArith.BinPos.Pos"; "add"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA"; "AHead"; "AHeadN"; "ANone"; "amode"; "open_facts"; "JGA"; "hdr_cells"; "nodes_ok"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "of_nat"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_below"; "pclF"; "robjs_check"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ArenaDestroy.AD"; "blk_size"; "ghost_facts"; "lenN_state"; "pop_state"; "pop_stateN"; "pop_tv"; "popped"; "link_fact"; "two52"; "@Stdlib.Lists.List"; "In"; "existsb"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjArena"; "achain"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "MInvR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "lit_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "@stdpp.base"; "NoDup"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundL SymSoundI SymSoundM SymSoundR SymFrame SymEntail SymCFG SymSummary SymCall SymObj ExampleMemcpy Glue3 SymBytes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue ObjXform ListCommit TobjJV TobjJVx TobjArena TobjJVA TobjJVAx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section AD.
Variable segs : list Segment.
Variable C : mconsts.
Variable NP : positive.
Variable Kc : ltac2:(tb__ "0|0|
S29S42A1S41OF_;F_;").
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Hypothesis ML : malloc_laws segs C.
Hypothesis HNP : NP_ok NP.

Let JGv (tv : list (sv * sv)) (am : amode) : jpred := ltac2:(tb__ "0|0|
S3eVsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;Vtv;Vam;A9").

Lemma JGA_head_none : ltac2:(tb__ "0|0|
S29S2aS0S0A2A1S0S1S29S42A1S41VJGv;R5S39R4A1R3R2R1A5VJGv;R6S3bR4R3R2A5F_;Fmd;Ftr;Frho;Fe;Ftv;").
Proof using C FB Kc NP P0f rho0 segs. intros tv e rho tr md [Ai [HJ _]]. exists Ai. split; [exact HJ | exact I]. Qed.
Lemma SPJ_head_none : ltac2:(tb__ "0|0|
S29S2aS0S0A2A1S0SaS1S43S38Vsegs;VJGv;R5S39R4A1A2R3R2R1A5S38Vsegs;VJGv;R6S3bA2R4R3R2A5F_;Fw;Frho;FS;Fe;Ftv;").
Proof using C FB Kc NP P0f rho0. intros tv e S rho w [Hs HJ]. split; [exact Hs | exact (JGA_head_none _ _ _ _ _ HJ)]. Qed.

Definition blk_size (n : positive) : sv := ltac2:(tb__ "0|0|
S17S4dS7S36Vn;P1A2A1S5Z20A1A3").
Definition popped (hd : sv) (n : positive) : sobj := ltac2:(tb__ "0|0|
SeVhd;S5Z0A1S50Vn;A1S60S3fVn;A1A1S1fA5").
Definition pop_state (S : sstate) (hd : sv) : sstate := ltac2:(tb__ "0|0|
S2VS;A1S35SfS13VS;A1S14VS;A1S11VS;A1S10VS;A1S15VS;A1S2bS4S8VS;A1S2cS4S56Vhd;R1A2S2dS4A1A3A3S2bS3S3dVhd;R1A2S6VS;A1A3S36R1P3A2S12VS;A1A9Tn;").
Definition pop_tv (hd : sv) (n : positive) (tv : list (sv * sv)) : list (sv * sv) := ltac2:(tb__ "0|0|
S2cS2aS0S0A2S33S0S0Vhd;S50Vn;A1A4Vtv;A3").

Lemma obj_holds_hi_swap : ltac2:(tb__ "0|0|
S1S5dS0S0S0S0S29S20A1S22S24S34S1dR8R3A2S1dR8R4A2A3S1bVsegs;R9R8SeR7R6R5R3R2A5A4S1bVsegs;RaR9SeR8R7R5R4R3A5A4F_;F_;Fd;Fcells;Fhi';Fhi;Flo;Fb;Fms;Frho;").
Proof using .
  intros rho ms b lo hi hi' cells d E H. unfold obj_holds, obj_lo_of, obj_hi_of in *. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in *.
  rewrite E. exact H.
Qed.

Lemma JGA_pop : ltac2:(tb__ "0|2|
S29S2aS0S0A2A1S0SaS4S27F_;S1S43S24S27S16S53R4R5A2A1S28A3S24S27S37VNP;S2R5A1A2S28A3S24S27S4aS2R6A1R8A2S28A3S24S27ScS2R7A1R8A2S28A3S24S27S4cS6R8A1RaS2eS31A1R7S8R8A1A5S28A3S4S34S59S4R2S8RbA1A3S24S27RbR3A1S28A3VP0f;Vrho0;A1S4fVNP;Vrho0;RcA3S49S3S1aRdA1S6RfA1A3S25S44S2fS34S34S1cReR7A2M0A3R6A2S45R6S32S34S34G0A3A2A2S4bVsegs;VC;Vrho0;VFB;R7A5F_;F_;F_;F_;F_;F_;Fa;Fo;S24S27S5aS3S1eS19S18S4eRbS5Z0A1A3A1A1S6RaA1A3S28A3S38Vsegs;VJGv;RdS39RcA1A2RbR9R8A5S26S1S1S25SbS2RdA1M1RbR1A3S38Vsegs;VJGv;S55ReG1RfA3S39S7G1A1A1A2S53RdReA2R1RaA5A2Lrho';A2F_;F_;F_;F_;F_;F_;F_;F_;Fw;Frho;Fextra;FS;Fhd;Ftv;").
Proof using Kc ML HNP.
  intros tv hd S extra rho w Hwf Hnp Htb Hhb Hrc Hext Hnz [Hsm [Ai [HJ HX]]].
  destruct w as [tr [ms md]]. apply Pos.leb_le in Hnp.
  pose proof HJ as (Hav & Hk & HM & HP & (HN & HD & HZ) & HK & HP0).
  pose proof (MI1 segs C _ _ _ _ HM) as HMr.
  pose proof (smatch_facts_hold segs _ _ _ Hsm) as HF.
  cbn in HX. destruct HX as (ns & HA & HNS).
  assert (Hh : bv_unsigned (eval rho hd) <> 0).
  { exact (tnz_of_fact rho hd (SLit 0) (holds_fact_in segs rho S _ _ Hsm Hnz)). }
  destruct (achain_cons (rm rho) _ ns HA Hh) as (cap & r & ->).
  cbn [achain] in HA. destruct HA as (_ & _ & Hcap0 & Hrd8 & (u & Hrd16 & Hu) & Hdef & (nx & Hrd0 & HAr)).
  set (h := bv_unsigned (eval rho hd)) in *.
  destruct HNS as [HF1 HND]. pose proof (Forall_inv HF1) as (Hblk & Hnfb & Hut). cbn [fst snd] in Hblk, Hnfb, Hut.
  pose proof (Forall_inv_tail HF1) as HFr.
  pose proof (block_geom segs C ML Ai rho md h (HDR + cap) HMr Hblk) as (G0 & G1 & G2 & G3 & G4). unfold HDR in G3.
  pose proof (rd64_range _ _ _ Hrd0) as Rnx. pose proof (rd64_range _ _ _ Hrd8) as Rcap. pose proof (rd64_range _ _ _ Hrd16) as Ru.
  set (n := ss_next S) in *.
  destruct (rw_set3 rho n (Z_to_bv 64 nx) (Z_to_bv 64 cap) (Z_to_bv 64 u)) as (R0 & R1 & R2 & Hag).
  set (rho' := rho_set_rw (rho_set_rw (rho_set_rw rho n (Z_to_bv 64 nx)) (n + 1) (Z_to_bv 64 cap)) (n + 2) (Z_to_bv 64 u)) in *.
  exists rho'. split; [exact Hag|].
  assert (Hrm : rm rho' = rm rho) by reflexivity.
  assert (Ehd : eval rho' hd = eval rho hd) by (symmetry; apply (eval_agree n); [exact Hag | exact Hhb]).
  clearbody rho'.
  pose proof (agree_below_vals _ _ _ Hag) as Hagv.
  assert (HRF : robjs_okF segs C rho0 FB rho tv (ss_objs S)).
  { eapply (robjs_checkF_sound segs C rho0 FB rho (ss_facts S) tv extra (ss_objs S) HF (T_ok_T0 C NP rho0 HNP rho Ai Hav (proj2 (proj2 HM))) HZ Hrc).
    intros o a Ho Hx Hr. apply pclF_FBx. exact (Hext o a Ho Hx HP0 Hav HF Hr). }

  pose proof (smatch_agree segs rho rho' S _ Hag Hsm) as Hsm'.
  assert (Ucap : bv_unsigned (eval rho' (SVar (n + 1))) = cap) by (cbn [eval]; rewrite R1; apply u64_of_sum; lia).
  assert (Uu : bv_unsigned (eval rho' (SVar (n + 2))) = u) by (cbn [eval]; rewrite R2; apply u64_of_sum; lia).
  assert (Uhd : bv_unsigned (eval rho' hd) = h) by (rewrite Ehd; reflexivity).
  assert (Esz : soff rho' (blk_size n) = 32 + cap).
  { unfold soff, blk_size. rewrite bv_signed_U, U_add, Ucap, U_lit. unfold M64v, aceil in *. rewrite !Z.mod_small by lia.
    destruct (Zsigned_spec (cap + 32)) as [[_ X]|[X _]]; [lia | unfold aceil in *; lia]. }
  assert (Hwf0 : swf (mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S)
                            (ss_objs S ++ [popped hd n]) (ss_facts S) (n + 3) (ss_lenient S)) = true).
  { unfold pop_state in Hwf. eapply swf_facts_suffix. exact Hwf. }
  assert (Hwf1 : swf (mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S)
                            (ss_objs S ++ [carved hd 0 (32 + cap) (hdr_cells n)]) (ss_facts S) (n + 3) (ss_lenient S)) = true).
  { revert Hwf0. unfold swf. cbn [ss_regs ss_fregs ss_next ss_fcsr ss_resv ss_objs ss_facts].
    rewrite !forallb_app. cbn [forallb].
    replace (obj_wf (n + 3) (carved hd 0 (32 + cap) (hdr_cells n))) with (obj_wf (n + 3) (popped hd n)); [intros H; exact H|].
    unfold obj_wf, popped, carved. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt sv_below].
    replace (sv_below (n + 3) (blk_size n)) with true; [destruct (sv_below (n + 3) hd); reflexivity|].
    unfold blk_size. cbn [sv_below]. rewrite ?andb_true_r. symmetry. apply Pos.ltb_lt. lia. }
  pose proof (smatch_carve_obj segs rho' S (tr, mkCfg ms md) hd 0 (32 + cap) (hdr_cells n) (n + 3) Hsm' Hwf1) as CARVE.
  cbv zeta in CARVE. rewrite Ehd in CARVE. fold h in CARVE.
  assert (Hsm1 : smatch segs rho' (mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S)
                            (ss_objs S ++ [carved hd 0 (32 + cap) (hdr_cells n)]) (ss_facts S) (n + 3) (ss_lenient S)) (tr, mkCfg ms md)).
  { unfold aceil in G3. apply CARVE; clear CARVE; try lia.
    - unfold hdr_cells, cells_inside. repeat apply Forall_cons; try apply Forall_nil; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
    - apply Forall_forall. intros o Ho. rewrite (obj_range_agree_vals n rho rho' o Hagv (proj1 (forallb_forall _ _) (swf_objs _ (smatch_swf segs _ _ _ Hsm)) o Ho)).
      eapply (proj1 (Forall_forall _ _) (robjs_okF_disjoint segs C rho0 FB ML Ai rho md tv (ss_objs S) h (HDR + cap) (h + 0) (h + (32 + cap)) HMr (proj2 (proj2 HM)) HP HN Hblk Hnfb Hut HRF ltac:(lia) ltac:(unfold HDR; lia))). exact Ho.
    - intros off Hoff. rewrite Hrm. unfold wok_of, rd_of.
      destruct (rm rho (Z_to_bv 64 (h + off))) as [x|] eqn:Ex; [split; [reflexivity | exists x; reflexivity]|].
      exfalso. apply (Hdef (h + off)); [unfold HDR; lia | exact Ex].
    - unfold hdr_cells, cells_in_view. rewrite Hrm.
      repeat constructor; intros j Hj; cbn [eval]; rewrite ?R0, ?R1, ?R2; unfold rd_of.
      + rewrite Z.add_0_r. rewrite (rd64_enc_bytes (rm rho) h nx Hrd0 j Hj). reflexivity.
      + rewrite (rd64_enc_bytes (rm rho) (h + 8) cap Hrd8 j Hj). reflexivity.
      + rewrite (rd64_enc_bytes (rm rho) (h + 16) u Hrd16 j Hj). reflexivity. }
  clear CARVE.

  assert (EL : firstn (length (ss_objs S)) (ss_objs S ++ [carved hd 0 (32 + cap) (hdr_cells n)])
               ++ popped hd n :: skipn (Datatypes.S (length (ss_objs S))) (ss_objs S ++ [carved hd 0 (32 + cap) (hdr_cells n)])
               = ss_objs S ++ [popped hd n]).
  { rewrite firstn_app, Nat.sub_diag, firstn_all. cbn [firstn]. rewrite app_nil_r.
    rewrite skipn_app, skipn_all2 by lia. replace (Datatypes.S (length (ss_objs S)) - length (ss_objs S))%nat with 1%nat by lia. reflexivity. }
  assert (Hsm2 : smatch segs rho' (mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S)
                            (ss_objs S ++ [popped hd n]) (ss_facts S) (n + 3) (ss_lenient S)) (tr, mkCfg ms md)).
  { set (S1 := mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S)
                     (ss_objs S ++ [carved hd 0 (32 + cap) (hdr_cells n)]) (ss_facts S) (n + 3) (ss_lenient S)) in Hsm1.
    pose proof (smatch_obj_upd segs rho' S1 (length (ss_objs S)) (carved hd 0 (32 + cap) (hdr_cells n)) (popped hd n) tr ms md) as U0.
    subst S1. unfold obj_upd, set_objs in U0. cbn [ss_objs ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_facts ss_next ss_lenient] in U0.
    rewrite EL in U0. apply U0; clear U0.
    - rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
    - exact Hsm1.
    - pose proof (swf_objs _ Hwf0) as W. cbn [ss_objs ss_next] in W. rewrite forallb_app in W. apply andb_prop in W as [_ W]. cbn [forallb] in W. apply andb_prop in W as [W _]. exact W.
    - unfold obj_range, obj_lo_of, obj_hi_of, popped, carved. cbn [ob_base ob_lo ob_hi]. unfold aceil in *. rewrite Esz, !soff_lit_small by lia. reflexivity.
    - intros _ _ Ho. apply (obj_holds_hi_swap rho' ms hd (SLit 0) (SLit (32 + cap)) (blk_size n) (lit_cells (hdr_cells n)) DUnknown).
      + unfold aceil in *. rewrite Esz, soff_lit_small by lia. reflexivity.
      + exact Ho. }

  assert (HOF : Forall (holds rho') (open_facts hd n)).
  { unfold open_facts. apply Forall_app. split.
    - constructor. { cbn [holds]. rewrite Ucap, Uu. exact Hu. }
      constructor. { cbn [holds]. rewrite !U_add, U_lit, Ucap, Uhd, U_lit. unfold M64v, aceil in *. rewrite !Z.mod_small by lia. lia. }
      constructor. { cbn [holds]. rewrite Ucap, U_lit. unfold M64v, aceil in *. rewrite Z.mod_small by lia. lia. }
      constructor. { cbn [holds]. rewrite Uhd, U_lit. unfold M64v, aceil in *. rewrite Z.mod_small by lia. lia. }
      constructor. { cbn [holds]. rewrite Uhd, U_lit. unfold M64v, aceil in *. rewrite Z.mod_small by lia. lia. }
      constructor.
    - destruct hd as [|v| | | | | |]; try apply Forall_nil. constructor; [|apply Forall_nil].
      cbn [holds]. split; [lia|]. cbn [eval] in Uhd. rewrite Uhd. change (2 ^ 4) with 16. exact G1. }
  split.
  - unfold pop_state. fold n.
    change (smatch segs rho' (add_facts (open_facts hd n) (mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S)
                            (ss_objs S ++ [popped hd n]) (ss_facts S) (n + 3) (ss_lenient S))) (tr, mkCfg ms md)).
    apply smatch_add_facts; [exact Hsm2 | exact HOF |].
    unfold pop_state in Hwf. unfold swf in Hwf. cbn [ss_regs ss_fregs ss_next ss_fcsr ss_resv ss_objs ss_facts] in Hwf.
    apply andb_prop in Hwf as [_ Hwf]. rewrite forallb_app in Hwf. apply andb_prop in Hwf as [Hwf _]. exact Hwf.
  -
    assert (Utv : tvv rho' (hd, blk_size n) = (h, HDR + cap)).
    { unfold tvv. cbn [fst snd]. rewrite Uhd. unfold blk_size. rewrite U_add, Ucap, U_lit. unfold M64v, HDR, aceil in *. rewrite !Z.mod_small by lia. f_equal. lia. }
    assert (TVV : forall t, In t tv -> tvv rho' t = tvv rho t /\ (tnz rho' t <-> tnz rho t)).
    { intros t Ht. pose proof (proj1 (forallb_forall _ _) Htb t Ht) as Hbt. split; [exact (tvv_agree n rho rho' t Hagv Hbt) | exact (tnz_agree n rho rho' t Hagv Hbt)]. }
    exists Ai. split.
    + split; [eapply agree_vals_trans; [exact Hav | eapply agree_vals_le; [exact Hnp | exact Hagv]]|].
      split; [exact Hk|]. split; [unfold MInvR; rewrite Hrm; exact HM|]. split; [exact HP|]. split; [|split; [rewrite Hrm; exact HK | exact HP0]].
      split; [|split].
      *   unfold pop_tv. constructor.
        { intros _. rewrite Utv. cbn [snd]. split; [unfold HDR; lia|]. split; [exact Hblk | exact Hnfb]. }
        exact (tvin_agree FB Ai n rho rho' tv Hagv Htb HN).
      *   unfold pop_tv. cbn [tvd]. split; [|exact (tvd_agree n rho rho' tv Hagv Htb HD)].
        intros t' Ht' _ Hnz'. rewrite Utv. destruct (TVV t' Ht') as [E1 E2]. rewrite E1. intros Heq. apply (Hut t' Ht'); [apply (proj1 E2); exact Hnz' | symmetry; exact Heq].
      *   unfold pop_tv. constructor; [|exact (tvz_agree n rho rho' tv Hagv Htb HZ)].
        intros Hnz'. exfalso. apply Hnz'. unfold tnz. cbn [fst]. rewrite Uhd. exact Hh.
    +
      cbn -[HDR]. cbn [eval]. rewrite R0, Hrm. rewrite u64_of_sum by lia.
      exists r. split; [exact HAr|]. split; [|inversion HND; assumption].
      apply Forall_forall. intros bc Hbc. destruct (proj1 (Forall_forall _ _) HFr bc Hbc) as (Y1 & Y2 & Y3).
      split; [exact Y1|]. split; [exact Y2|]. intros t Ht Hnz'. unfold pop_tv in Ht. destruct Ht as [<-|Ht].
      * rewrite Utv. intros Heq. injection Heq as Hb _. inversion HND; subst. apply H1. apply list_elem_of_In.
        rewrite Hb. apply in_map_iff. exists bc. split; [reflexivity | exact Hbc].
      * destruct (TVV t Ht) as [E1 E2]. rewrite E1. apply (Y3 t Ht). apply (proj1 E2). exact Hnz'.
Qed.

Definition two52 : Z := 2 ^ 52.
Definition ghost_facts (g : positive) : list sprop := ltac2:(tb__ "0|1|
S2cS3SdS5ZfA1S7Vg;A1M0A2S2cS3SdG0S5S58A1A2S2dS3A1A3A3").

Definition link_fact (g : sv) (g' : positive) : sprop := ltac2:(tb__ "0|0|
SdS17S4dS7Vg';A1S5Z10A1A3Vg;A2").
Definition pop_stateN (S : sstate) (hd g : sv) : sstate := ltac2:(tb__ "0|1|
S2VS;A1S35SfS13VS;A1S14VS;A1S11VS;A1S10VS;A1S15VS;A1S2bS4S8VS;A1S2cS4S56Vhd;R1A2S2dS4A1A3A3S2bS3S2bS3S3dVhd;R1A2S2bS3S51S36R1P3A2M0A1S2cS3S57Vg;G0A2S2dS3A1A3A3A3S6VS;A1A3S36R1P4A2S12VS;A1A9Tn;").

Lemma rw_set4 : ltac2:(tb__ "0|4|
S1S35S5cQ40A1M0G0G0G0S48S48S48S48R6R5R4A3S36R5P1M1A2R3A3S36R5P2M2A2R2A3S36R5P3M3A2R1A3S1S25S24G0S9R1R6A2R5A3S25S24G0S9R1S36R6G1A2A2R4A3S25S24G0S9R1S36R6G2A2A2R3A3S25S24G0S9R1S36R6G3A2A2R2A3SbR6R7R1A3A2A2A2A2Trho';Ft;Fz;Fy;Fx;Fn;Frho;").
Proof using .
  clear. intros rho n x y z t. unfold rho_set_rw. cbn [rw].
  assert (E1 : Pos.eqb n (n + 3) = false) by (apply Pos.eqb_neq; lia).
  assert (E2 : Pos.eqb n (n + 2) = false) by (apply Pos.eqb_neq; lia).
  assert (E3 : Pos.eqb n (n + 1) = false) by (apply Pos.eqb_neq; lia).
  assert (E4 : Pos.eqb (n + 1) (n + 3) = false) by (apply Pos.eqb_neq; lia).
  assert (E5 : Pos.eqb (n + 1) (n + 2) = false) by (apply Pos.eqb_neq; lia).
  assert (E6 : Pos.eqb (n + 2) (n + 3) = false) by (apply Pos.eqb_neq; lia).
  rewrite E1, E2, E3, E4, E5, E6, !Pos.eqb_refl. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [|split; intros; reflexivity]. intros i Hi. cbn [rw].
  assert (A : Pos.eqb i (n + 3) = false) by (apply Pos.eqb_neq; lia). assert (B : Pos.eqb i (n + 2) = false) by (apply Pos.eqb_neq; lia).
  assert (C' : Pos.eqb i (n + 1) = false) by (apply Pos.eqb_neq; lia). assert (D : Pos.eqb i n = false) by (apply Pos.eqb_neq; lia).
  rewrite A, B, C', D. reflexivity.
Qed.

Lemma JGA_popN : ltac2:(tb__ "0|4|
S29S2aS0S0A2A1S0S0SaS4S27F_;S1S43S24S27S16S54R4R6R5A3A1S28A3S24S27ScS2R5A1R6A2S28A3S24S27S37VNP;S2R6A1A2S28A3S24S27S4aS2R7A1RaA2S28A3S24S27ScS2R8A1RaA2S28A3S24S27S4cS6R9A1RcS2eS31A1R8S8R9A1A5S28A3S4S34S59S4R2S8RcA1A3S24S27RcR3A1S28A3VP0f;Vrho0;A1S4fVNP;Vrho0;RdA3S49S3S1aReA1S6R10A1A3S25S44S2fS34S34S1cRfR7A2M0A3R6A2S45R6S32S34S34G0A3A2A2S4bVsegs;VC;Vrho0;VFB;R7A5F_;F_;F_;F_;F_;F_;Fa;Fo;S24S27S5aS3S1eS19S18S4eRdS5Z0A1A3A1A1S6RbA1A3S28A3S38Vsegs;VJGv;RfS3aReRdA2A2RcRaR9A5S26S1S1S25SbS2ReA1M1RcR1A3S25S38Vsegs;VJGv;S55R10G1R11A3S3aS7G1A1S7S36G1P3A2M2A1A2A2S54ReR10RfA3R1RbA5S24S34S47S5bQ40M3S9R1G2A2A2Z10A2S5bG3S21RcRfA2A2A3A2A2Lrho';A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Frho;Fextra;FS;Fg;Fhd;Ftv;").
Proof using Kc ML HNP.
  intros tv hd g S extra rho w Hwf Hgb Hnp Htb Hhb Hrc Hext Hnz [Hsm [Ai [HJ HX]]].
  destruct w as [tr [ms md]]. apply Pos.leb_le in Hnp.
  pose proof HJ as (Hav & Hk & HM & HP & (HN & HD & HZ) & HK & HP0).
  pose proof (MI1 segs C _ _ _ _ HM) as HMr.
  pose proof (smatch_facts_hold segs _ _ _ Hsm) as HF.
  cbn [XA] in HX. destruct HX as (ns & HA & HNS & HL).
  assert (Hh : bv_unsigned (eval rho hd) <> 0).
  { exact (tnz_of_fact rho hd (SLit 0) (holds_fact_in segs rho S _ _ Hsm Hnz)). }
  destruct (achain_cons (rm rho) _ ns HA Hh) as (cap & r & ->).
  cbn [achain] in HA. destruct HA as (_ & _ & Hcap0 & Hrd8 & (u & Hrd16 & Hu) & Hdef & (nx & Hrd0 & HAr)).
  set (h := bv_unsigned (eval rho hd)) in *.
  destruct HNS as [HF1 HND]. pose proof (Forall_inv HF1) as (Hblk & Hnfb & Hut). cbn [fst snd] in Hblk, Hnfb, Hut.
  pose proof (Forall_inv_tail HF1) as HFr.
  pose proof (block_geom segs C ML Ai rho md h (HDR + cap) HMr Hblk) as (G0 & G1 & G2 & G3 & G4). unfold HDR in G3.
  pose proof (rd64_range _ _ _ Hrd0) as Rnx. pose proof (rd64_range _ _ _ Hrd8) as Rcap. pose proof (rd64_range _ _ _ Hrd16) as Ru.
  set (n := ss_next S) in *.
  cbn [length] in HL. rewrite Nat2Z.inj_succ in HL.
  pose proof (bv_urange (eval rho g)) as Rg.
  destruct (rw_set4 rho n (Z_to_bv 64 nx) (Z_to_bv 64 cap) (Z_to_bv 64 u) (Z_to_bv 64 (bv_unsigned (eval rho g) - 16))) as (R0 & R1 & R2 & R3 & Hag).
  set (rho' := rho_set_rw (rho_set_rw (rho_set_rw (rho_set_rw rho n (Z_to_bv 64 nx)) (n + 1) (Z_to_bv 64 cap)) (n + 2) (Z_to_bv 64 u)) (n + 3) (Z_to_bv 64 (bv_unsigned (eval rho g) - 16))) in *.
  exists rho'.
  assert (Hrm : rm rho' = rm rho) by reflexivity.
  assert (Ehd : eval rho' hd = eval rho hd) by (symmetry; apply (eval_agree n); [exact Hag | exact Hhb]).
  assert (Eg : eval rho' g = eval rho g) by (symmetry; apply (eval_agree n); [exact Hag | exact Hgb]).
  assert (Ug' : bv_unsigned (rw rho' (n + 3)%positive) = bv_unsigned (eval rho g) - 16).
  { rewrite R3. apply u64_of_sum. pose proof (Nat2Z.is_nonneg (length r)). lia. }
  clearbody rho'. split; [exact Hag|].
  cut (SPJ segs (JGv (pop_tv hd n tv) (AHeadN (SVar n) (SVar (n + 3)))) (pop_stateN S hd g) rho' (tr, mkCfg ms md)); [intros X; split; [exact X | lia]|].
  pose proof (agree_below_vals _ _ _ Hag) as Hagv.
  assert (HRF : robjs_okF segs C rho0 FB rho tv (ss_objs S)).
  { eapply (robjs_checkF_sound segs C rho0 FB rho (ss_facts S) tv extra (ss_objs S) HF (T_ok_T0 C NP rho0 HNP rho Ai Hav (proj2 (proj2 HM))) HZ Hrc).
    intros o a Ho Hx Hr. apply pclF_FBx. exact (Hext o a Ho Hx HP0 Hav HF Hr). }

  pose proof (smatch_agree segs rho rho' S _ Hag Hsm) as Hsm'.
  assert (Ucap : bv_unsigned (eval rho' (SVar (n + 1))) = cap) by (cbn [eval]; rewrite R1; apply u64_of_sum; lia).
  assert (Uu : bv_unsigned (eval rho' (SVar (n + 2))) = u) by (cbn [eval]; rewrite R2; apply u64_of_sum; lia).
  assert (Uhd : bv_unsigned (eval rho' hd) = h) by (rewrite Ehd; reflexivity).
  assert (Esz : soff rho' (blk_size n) = 32 + cap).
  { unfold soff, blk_size. rewrite bv_signed_U, U_add, Ucap, U_lit. unfold M64v, aceil in *. rewrite !Z.mod_small by lia.
    destruct (Zsigned_spec (cap + 32)) as [[_ X]|[X _]]; [lia | unfold aceil in *; lia]. }
  assert (Hwf0 : swf (mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S)
                            (ss_objs S ++ [popped hd n]) (ss_facts S) (n + 4) (ss_lenient S)) = true).
  { unfold pop_stateN in Hwf. eapply swf_facts_suffix. exact Hwf. }
  assert (Hwf1 : swf (mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S)
                            (ss_objs S ++ [carved hd 0 (32 + cap) (hdr_cells n)]) (ss_facts S) (n + 4) (ss_lenient S)) = true).
  { revert Hwf0. unfold swf. cbn [ss_regs ss_fregs ss_next ss_fcsr ss_resv ss_objs ss_facts].
    rewrite !forallb_app. cbn [forallb].
    replace (obj_wf (n + 4) (carved hd 0 (32 + cap) (hdr_cells n))) with (obj_wf (n + 4) (popped hd n)); [intros H; exact H|].
    unfold obj_wf, popped, carved. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt sv_below].
    replace (sv_below (n + 4) (blk_size n)) with true; [destruct (sv_below (n + 4) hd); reflexivity|].
    unfold blk_size. cbn [sv_below]. rewrite ?andb_true_r. symmetry. apply Pos.ltb_lt. lia. }
  pose proof (smatch_carve_obj segs rho' S (tr, mkCfg ms md) hd 0 (32 + cap) (hdr_cells n) (n + 4) Hsm' Hwf1) as CARVE.
  cbv zeta in CARVE. rewrite Ehd in CARVE. fold h in CARVE.
  assert (Hsm1 : smatch segs rho' (mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S)
                            (ss_objs S ++ [carved hd 0 (32 + cap) (hdr_cells n)]) (ss_facts S) (n + 4) (ss_lenient S)) (tr, mkCfg ms md)).
  { unfold aceil in G3. apply CARVE; clear CARVE; try lia.
    - unfold hdr_cells, cells_inside. repeat apply Forall_cons; try apply Forall_nil; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
    - apply Forall_forall. intros o Ho. rewrite (obj_range_agree_vals n rho rho' o Hagv (proj1 (forallb_forall _ _) (swf_objs _ (smatch_swf segs _ _ _ Hsm)) o Ho)).
      eapply (proj1 (Forall_forall _ _) (robjs_okF_disjoint segs C rho0 FB ML Ai rho md tv (ss_objs S) h (HDR + cap) (h + 0) (h + (32 + cap)) HMr (proj2 (proj2 HM)) HP HN Hblk Hnfb Hut HRF ltac:(lia) ltac:(unfold HDR; lia))). exact Ho.
    - intros off Hoff. rewrite Hrm. unfold wok_of, rd_of.
      destruct (rm rho (Z_to_bv 64 (h + off))) as [x|] eqn:Ex; [split; [reflexivity | exists x; reflexivity]|].
      exfalso. apply (Hdef (h + off)); [unfold HDR; lia | exact Ex].
    - unfold hdr_cells, cells_in_view. rewrite Hrm.
      repeat constructor; intros j Hj; cbn [eval]; rewrite ?R0, ?R1, ?R2; unfold rd_of.
      + rewrite Z.add_0_r. rewrite (rd64_enc_bytes (rm rho) h nx Hrd0 j Hj). reflexivity.
      + rewrite (rd64_enc_bytes (rm rho) (h + 8) cap Hrd8 j Hj). reflexivity.
      + rewrite (rd64_enc_bytes (rm rho) (h + 16) u Hrd16 j Hj). reflexivity. }
  clear CARVE.

  assert (EL : firstn (length (ss_objs S)) (ss_objs S ++ [carved hd 0 (32 + cap) (hdr_cells n)])
               ++ popped hd n :: skipn (Datatypes.S (length (ss_objs S))) (ss_objs S ++ [carved hd 0 (32 + cap) (hdr_cells n)])
               = ss_objs S ++ [popped hd n]).
  { rewrite firstn_app, Nat.sub_diag, firstn_all. cbn [firstn]. rewrite app_nil_r.
    rewrite skipn_app, skipn_all2 by lia. replace (Datatypes.S (length (ss_objs S)) - length (ss_objs S))%nat with 1%nat by lia. reflexivity. }
  assert (Hsm2 : smatch segs rho' (mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S)
                            (ss_objs S ++ [popped hd n]) (ss_facts S) (n + 4) (ss_lenient S)) (tr, mkCfg ms md)).
  { set (S1 := mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S)
                     (ss_objs S ++ [carved hd 0 (32 + cap) (hdr_cells n)]) (ss_facts S) (n + 4) (ss_lenient S)) in Hsm1.
    pose proof (smatch_obj_upd segs rho' S1 (length (ss_objs S)) (carved hd 0 (32 + cap) (hdr_cells n)) (popped hd n) tr ms md) as U0.
    subst S1. unfold obj_upd, set_objs in U0. cbn [ss_objs ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_facts ss_next ss_lenient] in U0.
    rewrite EL in U0. apply U0; clear U0.
    - rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
    - exact Hsm1.
    - pose proof (swf_objs _ Hwf0) as W. cbn [ss_objs ss_next] in W. rewrite forallb_app in W. apply andb_prop in W as [_ W]. cbn [forallb] in W. apply andb_prop in W as [W _]. exact W.
    - unfold obj_range, obj_lo_of, obj_hi_of, popped, carved. cbn [ob_base ob_lo ob_hi]. unfold aceil in *. rewrite Esz, !soff_lit_small by lia. reflexivity.
    - intros _ _ Ho. apply (obj_holds_hi_swap rho' ms hd (SLit 0) (SLit (32 + cap)) (blk_size n) (lit_cells (hdr_cells n)) DUnknown).
      + unfold aceil in *. rewrite Esz, soff_lit_small by lia. reflexivity.
      + exact Ho. }

  assert (HOF : Forall (holds rho') (open_facts hd n ++ ghost_facts (n + 3) ++ [link_fact g (n + 3)])).
  { apply Forall_app. split; [| apply Forall_app; split; [unfold ghost_facts; constructor; [cbn [holds]; rewrite U_lit; cbn [eval]; rewrite Ug'; unfold M64v; rewrite Z.mod_small by lia; lia
                                                  | constructor; [cbn [holds]; unfold two52; rewrite U_lit; cbn [eval]; rewrite Ug'; unfold M64v; rewrite Z.mod_small by lia; lia | constructor]]
                                                  | constructor; [unfold link_fact; cbn [holds]; rewrite U_add, U_lit, Eg; cbn [eval]; rewrite Ug'; unfold M64v; rewrite (Z.mod_small 16) by lia; rewrite Z.mod_small by lia; lia | constructor]]].
    unfold open_facts. apply Forall_app. split.
    - constructor. { cbn [holds]. rewrite Ucap, Uu. exact Hu. }
      constructor. { cbn [holds]. rewrite !U_add, U_lit, Ucap, Uhd, U_lit. unfold M64v, aceil in *. rewrite !Z.mod_small by lia. lia. }
      constructor. { cbn [holds]. rewrite Ucap, U_lit. unfold M64v, aceil in *. rewrite Z.mod_small by lia. lia. }
      constructor. { cbn [holds]. rewrite Uhd, U_lit. unfold M64v, aceil in *. rewrite Z.mod_small by lia. lia. }
      constructor. { cbn [holds]. rewrite Uhd, U_lit. unfold M64v, aceil in *. rewrite Z.mod_small by lia. lia. }
      constructor.
    - destruct hd as [|v| | | | | |]; try apply Forall_nil. constructor; [|apply Forall_nil].
      cbn [holds]. split; [lia|]. cbn [eval] in Uhd. rewrite Uhd. change (2 ^ 4) with 16. exact G1. }
  split.
  - unfold pop_stateN. fold n.
    change (smatch segs rho' (add_facts (open_facts hd n ++ ghost_facts (n + 3) ++ [link_fact g (n + 3)]) (mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S)
                            (ss_objs S ++ [popped hd n]) (ss_facts S) (n + 4) (ss_lenient S))) (tr, mkCfg ms md)).
    apply smatch_add_facts; [exact Hsm2 | exact HOF |].
    unfold pop_stateN in Hwf. unfold swf in Hwf. cbn [ss_regs ss_fregs ss_next ss_fcsr ss_resv ss_objs ss_facts] in Hwf.
    apply andb_prop in Hwf as [_ Hwf]. rewrite forallb_app in Hwf. apply andb_prop in Hwf as [Hwf _]. exact Hwf.
  -
    assert (Utv : tvv rho' (hd, blk_size n) = (h, HDR + cap)).
    { unfold tvv. cbn [fst snd]. rewrite Uhd. unfold blk_size. rewrite U_add, Ucap, U_lit. unfold M64v, HDR, aceil in *. rewrite !Z.mod_small by lia. f_equal. lia. }
    assert (TVV : forall t, In t tv -> tvv rho' t = tvv rho t /\ (tnz rho' t <-> tnz rho t)).
    { intros t Ht. pose proof (proj1 (forallb_forall _ _) Htb t Ht) as Hbt. split; [exact (tvv_agree n rho rho' t Hagv Hbt) | exact (tnz_agree n rho rho' t Hagv Hbt)]. }
    exists Ai. split.
    + split; [eapply agree_vals_trans; [exact Hav | eapply agree_vals_le; [exact Hnp | exact Hagv]]|].
      split; [exact Hk|]. split; [unfold MInvR; rewrite Hrm; exact HM|]. split; [exact HP|]. split; [|split; [rewrite Hrm; exact HK | exact HP0]].
      split; [|split].
      *   unfold pop_tv. constructor.
        { intros _. rewrite Utv. cbn [snd]. split; [unfold HDR; lia|]. split; [exact Hblk | exact Hnfb]. }
        exact (tvin_agree FB Ai n rho rho' tv Hagv Htb HN).
      *   unfold pop_tv. cbn [tvd]. split; [|exact (tvd_agree n rho rho' tv Hagv Htb HD)].
        intros t' Ht' _ Hnz'. rewrite Utv. destruct (TVV t' Ht') as [E1 E2]. rewrite E1. intros Heq. apply (Hut t' Ht'); [apply (proj1 E2); exact Hnz' | symmetry; exact Heq].
      *   unfold pop_tv. constructor; [|exact (tvz_agree n rho rho' tv Hagv Htb HZ)].
        intros Hnz'. exfalso. apply Hnz'. unfold tnz. cbn [fst]. rewrite Uhd. exact Hh.
    +
      cbn -[HDR Z.mul Z.add Z.le Z.of_nat Z.pow Z.sub]. cbn [eval]. rewrite R0, Hrm, Ug'. rewrite u64_of_sum by lia.
      exists r. split; [exact HAr|]. split; [| lia].
      split; [|inversion HND; assumption].
      apply Forall_forall. intros bc Hbc. destruct (proj1 (Forall_forall _ _) HFr bc Hbc) as (Y1 & Y2 & Y3).
      split; [exact Y1|]. split; [exact Y2|]. intros t Ht Hnz'. unfold pop_tv in Ht. destruct Ht as [<-|Ht].
      * rewrite Utv. intros Heq. injection Heq as Hb _. inversion HND; subst. apply H1. apply list_elem_of_In.
        rewrite Hb. apply in_map_iff. exists bc. split; [reflexivity | exact Hbc].
      * destruct (TVV t Ht) as [E1 E2]. rewrite E1. apply (Y3 t Ht). apply (proj1 E2). exact Hnz'.
Qed.

Lemma NoDup_range_length : ltac2:(tb__ "0|1|
S29S34A1S34S44Z0R1A2M0S62S34R3A2S49S34S34S25G0S45R1R4A2A2Lz;R4A3S44S46S30S34R5A2A1R4A2F_;F_;F_;Fhi;Fl;").
Proof using .
  clear. intros l hi Hhi HD HF. apply NoDup_ListNoDup in HD.
  assert (HI : incl l (map Z.of_nat (seq 0 (Z.to_nat hi)))).
  { intros z Hz. pose proof (proj1 (Forall_forall _ _) HF z Hz) as Rz. cbv beta in Rz. apply in_map_iff. exists (Z.to_nat z). split; [lia|]. apply in_seq. lia. }
  pose proof (NoDup_incl_length HD HI) as L. rewrite length_map, length_seq in L. lia.
Qed.

Lemma chain_len_bound : ltac2:(tb__ "0|1|
S61S1S41S29S2aS0S0A2A1S29S2aS34S34A2M0A1S34S5fVsegs;VC;R6R5R4A5S40VFB;R7R6R4R3A5S5eS23R7A1R3R4A3S44S46S30G0R5A2A1Z7fffff800000A2F_;F_;F_;Fh;Fns;Ftv;Fmd;Frho;FAi;").
Proof using JGv ML.
  intros Ai rho md tv ns h HM [HF HND] HA.
  rewrite <- (length_map fst). apply NoDup_range_length; [lia | exact HND |].
  apply Forall_forall. intros b Hb. apply in_map_iff in Hb as ([b' cap] & <- & Hin). cbn [fst].
  destruct (proj1 (Forall_forall _ _) HF _ Hin) as (Hblk & _ & _). cbn [fst snd] in Hblk.
  pose proof (block_geom segs C ML Ai rho md b' (HDR + cap) HM Hblk) as (G0 & G1 & G2 & G3 & G4).
  unfold HDR in *. lia.
Qed.

Definition lenN_state (S : sstate) : sstate := ltac2:(tb__ "0|0|
S2VS;A1S35SfS13VS;A1S14VS;A1S11VS;A1S10VS;A1S15VS;A1S8VS;A1S2bS3S51R1A1S6VS;A1A3S36R1P1A2S12VS;A1A9Tn;").

Lemma JGA_lenN : ltac2:(tb__ "0|1|
S29S2aS0S0A2A1S0SaS1S43S24S27S37VNP;S2R3A1A2S28A3S24S27S4aS2R4A1R6A2S28A3S24S27ScS2R5A1R6A2S28A3S24S27S16S52R6A1A1S28A3S38Vsegs;VJGv;R9S39R8A1A2R7R6R5A5S26S1S1S25SbS2R9A1M0R8R1A3S38Vsegs;VJGv;RbS3aRaS7G0A1A2A2S52R9A1R1R7A5A2Lrho';A2F_;F_;F_;F_;F_;Fw;Frho;FS;Fhd;Ftv;").
Proof using FB Kc ML P0f rho0.
  intros tv hd S rho w Hnp Htb Hhb Hwf [Hsm [Ai [HJ HX]]]. destruct w as [tr [ms md]]. apply Pos.leb_le in Hnp.
  pose proof HJ as (Hav & Hk & HM & HP & (HN & HD & HZ) & HK & HP0).
  cbn [XA] in HX. destruct HX as (ns & HA & HNS).
  pose proof (chain_len_bound Ai rho md tv ns _ (MI1 segs C _ _ _ _ HM) HNS HA) as HLB.
  set (n := ss_next S) in *.
  set (v := 16 * Z.of_nat (length ns) + 15).
  set (rho' := rho_set_rw rho n (Z_to_bv 64 v)).
  assert (Hag : agree_below n rho rho').
  { subst rho'. split; [|split; intros; reflexivity]. intros i Hi. unfold rho_set_rw. cbn [rw].
    replace (Pos.eqb i n) with false; [reflexivity|]. symmetry. apply Pos.eqb_neq. lia. }
  assert (Uv' : bv_unsigned (rw rho' n) = v).
  { subst rho'. unfold rho_set_rw. cbn [rw]. rewrite Pos.eqb_refl. apply u64_of_sum. subst v. unfold aceil in HLB. pose proof (Nat2Z.is_nonneg (length ns)). lia. }
  assert (Hrm : rm rho' = rm rho) by reflexivity.
  exists rho'. split; [exact Hag|].
  assert (G1 : holds rho' (SPUle (SLit 15) (SVar n))).
  { cbn [holds]. rewrite U_lit, eval_var, Uv'. unfold M64v. rewrite Z.mod_small by lia. subst v. pose proof (Nat2Z.is_nonneg (length ns)). lia. }
  assert (G2 : holds rho' (SPUle (SVar n) (SLit two52))).
  { cbn [holds]. unfold two52. rewrite U_lit, eval_var, Uv'. unfold M64v. rewrite Z.mod_small by lia. subst v. unfold aceil in HLB. lia. }
  assert (HGF : Forall (holds rho') (ghost_facts n)) by (unfold ghost_facts; constructor; [exact G1 | constructor; [exact G2 | apply Forall_nil]]).
  split.
  - unfold lenN_state. fold n.
    change (smatch segs rho' (add_facts (ghost_facts n) (mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S) (ss_facts S) (n + 1) (ss_lenient S))) (tr, mkCfg ms md)).
    pose proof Hwf as Hwf0. unfold lenN_state in Hwf0. fold n in Hwf0.
    apply smatch_add_facts; [| exact HGF |].
    + apply smatch_set_objs_next; [exact (smatch_agree segs rho rho' S _ Hag Hsm) | | eapply swf_facts_suffix; exact Hwf0].
      pose proof (smatch_agree segs rho rho' S _ Hag Hsm) as Hsm'. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hsm'))))))))))).
    + unfold swf in Hwf0. cbn [ss_regs ss_fregs ss_next ss_fcsr ss_resv ss_objs ss_facts] in Hwf0.
      apply andb_prop in Hwf0 as [_ Hwf0]. rewrite forallb_app in Hwf0. apply andb_prop in Hwf0 as [Hwf0 _]. exact Hwf0.
  - exists Ai. split.
    + exact (proj1 (JGAi_stable segs C NP Kc rho0 P0f FB ML n tv (AHead hd) Ai rho rho' tr md Hnp Htb Hhb Hag (conj HJ (ex_intro _ ns (conj HA HNS))))).
    + cbn [XA]. rewrite Hrm. rewrite <- (eval_agree n rho rho' hd Hag Hhb). cbn [eval]. rewrite Uv'.
      exists ns. split; [exact HA|]. split; [exact (nodes_ok_agree FB Ai n rho rho' tv ns (agree_below_vals _ _ _ Hag) Htb HNS)|].
      subst v. unfold aceil in HLB. lia.
Qed.

Lemma JGA_dropN : ltac2:(tb__ "0|0|
S29S2aS0S0A2A1S0S0S1S29S42A1S41VJGv;R6S3aR5R4A2R3R2R1A5VJGv;R7S39R6A1R4R3R2A5F_;Fmd;Ftr;Frho;Fg;Fhd;Ftv;").
Proof using C FB Kc NP P0f rho0 segs. intros tv hd g rho tr md [Ai [HJ HX]]. exists Ai. split; [exact HJ|]. cbn [XA] in HX |- *. destruct HX as (ns & HA & HN & _). exists ns. auto. Qed.

Lemma JGA_head0 : ltac2:(tb__ "0|0|
S29S2aS0S0A2A1S3cS1S29S42A1S41VJGv;R5R4R3R2R1A5VJGv;R6S39S5Z0A1A1R4R3R2A5F_;Fmd;Ftr;Frho;Fam;Ftv;").
Proof using C FB Kc NP P0f rho0 segs.
  intros tv am rho tr md [Ai [HJ _]]. exists Ai. split; [exact HJ|]. cbn [XA]. rewrite U_lit. unfold M64v. rewrite Z.mod_0_l by lia.
  exists []. split; [reflexivity|]. split; [apply Forall_nil | constructor].
Qed.
Lemma SPJ_head0 : ltac2:(tb__ "0|0|
S29S2aS0S0A2A1S3cSaS1S43S38Vsegs;VJGv;R5R4A2R3R2R1A5S38Vsegs;VJGv;R6S39S5Z0A1A1A2R4R3R2A5F_;Fw;Frho;FS;Fam;Ftv;").
Proof using C FB Kc NP P0f rho0. intros tv am S rho w [Hs HJ]. split; [exact Hs | exact (JGA_head0 _ _ _ _ _ HJ)]. Qed.
End AD.
