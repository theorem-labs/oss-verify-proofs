(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; addresses measured on the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6): the end of the build segment of
   LLVMFuzzerTestOneInput (0x7ff88), pod.h:447 and fuzz.h:73. Proves no function (kind: segment lemma).
   THE CODE
     0x82094 srli a0,s10,3 / add a0,a0,s7 / lb a0,0(a0)     the shadow byte of &pp->corrupt (s10 = pp + 0x4d18)
     0x820a0 bnez a0 -> 0x82750                             its second test (andi a1,s10,7; addi a1,a1,3; blt a1,a0)
     0x820a4 addi a0,zero,1 / 0x820a8 sw a0,0(s10)          pp->corrupt = 1
     0x820ac lbu a0,0(s4) / bnez a0 -> 0x82b08              the shadow byte of &pp->len (s4 = (pp + 0x4000 >> 3) + K)
     0x820b4 ld s8,0(s5)                                    len = pp->len (s5 = pp + 0x4000)
     0x820b8 seqz a0,s8 / 0x820bc add a0,s8,a0              the second request, len + (len == 0)
     0x820c0 jal malloc                                     the cut C2 (role_build_contract's end), not run here
   Each instrumented check is one shadow obligation of the engine's token path (lib/Reusable/YCbn.v): the 4 bytes at
   &pp->corrupt and the 8 at &pp->len lie in the first block, whose bytes are marked usable (RPgMem.rm_blk_ra), so
   the error path is not reached.
   w10_tail: from 0x820ac (the three no-corruption arms of the piece and the corruption's end) to C2;
   w10_req: the statement rs_piece_W10_req_stmt (lib/A/RPgSeg.v), RT -> C2: the store of corrupt = 1, then w10_tail. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgImgA RPgMem RPgSeg RPgSiteA.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require RPgCfgChanges.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgW7bBase RPgPostK.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Local Arguments x_STK {segs} _. Local Arguments x_sp0 {segs} _. Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _. Local Arguments x_S {segs} _. Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _. Local Arguments x_md0 {segs} _. Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _. Local Arguments x_regs {segs} _. Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _. Local Arguments x_W {segs} _. Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _. Local Arguments x_RLO {segs} _. Local Arguments x_RHI {segs} _.
Local Arguments x_e {segs} _. Local Arguments x_pos {segs} _.

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

(* the record pod_build makes is well formed, and its image's fields fit Layout's bounds *)
Lemma w10_rec_facts : forall rest,
  pod_rec_wf (fst (pod_build rest)) /\
  Z.of_nat (length (buf (fst (pod_build rest)))) <= POD_BUF_MAX /\
  (length (ents (fst (pod_build rest))) <= 32)%nat /\
  Forall (fun e => (length (e_body e) <= 96)%nat) (ents (fst (pod_build rest))).
Proof.
intros rest. destruct (pod_build rest) as [r rest'] eqn:EB. cbn [fst].
pose proof (pod_build_wf rest r rest' EB) as Hwf. split; [exact Hwf|].
destruct (ents_wf r Hwf) as [HE1 HE2].
pose proof Hwf as (_ & _ & _ & _ & HL & Hc).
assert (Hb : length (buf r) = length (pod_encode r)).
{ unfold buf. destruct (p_corr r) as [[off bs]|] eqn:Ec; [|reflexivity].
  destruct Hc as (C1 & C2 & C3). apply length_overwrite. lia. }
split; [rewrite Hb; unfold POD_BUF_MAX; lia|]. split; [exact HE1|].
eapply Forall_impl; [|exact HE2]. intros e (_ & H1 & H2). lia.
Qed.

(* ---- 0x820ac -> C2 ---- *)
Lemma w10_tail : forall (cx : rs_scx rsegs) POST rest ly2 S2 (W2 : world rsegs) regs2 mem2 md2,
  rs_pre rsegs B cx -> rs_from_C2 rsegs B MT cx POST rest ->
  rs_core rsegs B MT cx (rs_E1 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
  rs_at_cx rsegs cx W2 mem2 regs2 (rs_L_post rsegs cx) ->
  rs_fsh_at rsegs cx W2 mem2 rs_P0 ->
  rs_pp_at rsegs cx W2 mem2 (pp_bytes (fst (pod_build rest))) ->
  e_len (x_e cx) = rl_len rest ->
  SRr rsegs W2 (cfg_at rsegs 0x820ac regs2 mem2 md2) POST.
Proof.
intros cx POST rest ly2 S2 W2 regs2 mem2 md2 HP HC2 HC HL Hfsh Hpp Hlen.
pose proof RPgCfgChanges.cfg_wx as Hwx. pose proof RPgCfgChanges.cfg_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
destruct (w10_ctx B MT cx ly2 S2 W2 regs2 mem2 md2 HP HC)
  as (Hin & Hfresh & Hal & Hlo & Hhi & Happ & Hpres & H2 & HR16 & HRS & HSTK & Hceil & H47 & HAR).
destruct (w10_F_ctx B cx HP) as (HF1 & HF2 & HF3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (w10_rec_facts rest) as (Hwf & Hb & He & Hs).
pose proof (rl_len_bounds rest) as HLb.
set (L := rl_len rest) in *.
assert (HLv : val_mem rsegs (mrestrict (w_H W2) mem2) (e_pp (x_e cx) + 0x4000) 8 L).
{ exact (rm_pp_len rsegs (buf (fst (pod_build rest))) _ _ _ _ _ Hb He Hs (w_H W2) mem2 (e_pp (x_e cx)) Hpp). }
pose proof HL as HL0.
unfold rs_at_cx, rs_at, rs_L_post in HL. cbv zeta in HL.
rewrite !Forall_cons_iff in HL.
destruct HL as (P8 & P9 & P19 & P23 & P21 & P27 & P25 & P20 & P26 & Q8 & Q28 & Q30 & Q68 & Q78 & Q80 & _).
cbn [fst snd rl_at] in P8, P9, P19, P23, P21, P27, P25, P20, P26.
pose proof HC as (HJ & _).
remember (Ereg regs2 [Z_to_bv 64 L]) as E eqn:HE.
assert (E21 : ew E 21 = Z_to_bv 64 (e_pp (x_e cx) + 0x4000)) by (subst E; rewrite (ew_Ereg_nat regs2 _ 21 (Z_to_bv 5 21) eq_refl); exact P21).
assert (E23 : ew E 23 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs2 _ 23 (Z_to_bv 5 23) eq_refl); exact P23).
assert (E32 : ew E 32 = Z_to_bv 64 L) by (subst E; exact (ew_Ereg_extra regs2 _ 0)).
assert (HS : st_ok rsegs E (mkSS 0x820ac
  (sr_set sr_atoms (Z_to_bv 5 20) (SAlu ALU_ADD (SAlu ALU_SRL (SOff 21 0) (SLit 3)) (SOff 23 0)))
  [YP09.mkRegion (Some 21%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))]] None
  (mkFacts [(21%nat, mkAF 4096 W10_HI 4); (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 8 5440 0)] [] []))
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 0x820ac) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. subst E. apply (entry_st_ok_full rsegs).
  - apply regs_ok_pin; [apply regs_ok_Ereg | intros X; apply (f_equal (@bv_unsigned 5)) in X; vm_compute in X; discriminate X |].
    rewrite (w10_den_sh _ 21 23 (e_pp (x_e cx) + 0x4000) E21 ltac:(lia) E23). exact P20.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (rm_ro_region rsegs _ (w_H W2) mem2 21 (e_pp (x_e cx) + 0x4000)).
    + rewrite E21. rewrite unsigned_lit_small by lia. reflexivity.
    + lia. + lia.
    + constructor; [|constructor]. apply (chunk_ok_val rsegs _ _ (e_pp (x_e cx) + 0x4000) 0 8 (SOff 32 0) L).
      * exact (w10_den_atom _ 32 L E32). * cbn. lia. * cbn. lia. * rewrite Z.add_0_r. exact HLv.
  - cbn. tauto.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E21, E23, E32, !unsigned_lit_small by (unfold SHADOW_OFF, W10_HI; lia).
    repeat match goal with |- _ /\ _ => split end; try exact I; try (unfold SHADOW_OFF, W10_HI; lia);
    try (rewrite Z.pow_0_r; apply Z.mod_1_r).
    change (2 ^ 4) with 16. rewrite Z.add_mod by lia. rewrite Hal. reflexivity. }
assert (SHOK : sh_ok rsegs W10Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
unfold cfg_at. change (w64 0x820ac) with (Z_to_bv 64 0x820ac).
aj_run_to_tok w10_tbl_ok HS HJ SHOK W10Bspan 0x820c0.
{ (* the shadow obligation of the 8-byte load of pp->len *)
  apply (w10_ob_blk B ly2 S2 W2 mem2 md2 E (e_pp (x_e cx)) PP_SIZE (e_pp (x_e cx) + 0x4000) 8 (SOff 21 0) HAR Hin);
  [lia | change (req_size PP_SIZE) with 19744; lia
  | exact (w10_U_atom E 23 SHADOW_OFF E23 ltac:(unfold SHADOW_OFF; lia))
  | exact (w10_U_atom E 21 _ E21 ltac:(lia))]. }
{ awr_ok_tac. }
(* the run's end, at C2 *)
assert (HK : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha. apply (w10_frame_kept _ _ _ _ _ HFr a Ha). intros (rg & Hr & Hrb). cbn [ss_mem] in Hr.
  destruct Hr as [<-|[]]. cbn in Hrb. lia. }
assert (HAE : env_agree 32 (Ereg regs2 [Z_to_bv 64 L]) (ewset E 33 w))
  by (subst E; eapply env_agree_le; [|apply env_agree_ewset]; lia).
pose proof (w7_regs_kept _ _ ms regs2 [Z_to_bv 64 L] (w_H W2) [Z_to_bv 5 10; Z_to_bv 5 24; Z_to_bv 5 20] HS HAE
  ltac:(vm_compute; reflexivity)) as RK.
assert (RK20 : getr (ms_regs ms) (Z_to_bv 5 20) = getr regs2 (Z_to_bv 5 20)).
{ rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 20) HS). w10_sr_eval.
  rewrite (sv_denot_agree 33 E (ewset E 33 w)); [| apply env_agree_ewset | reflexivity].
  rewrite (w10_den_sh _ 21 23 (e_pp (x_e cx) + 0x4000) E21 ltac:(lia) E23). symmetry. exact P20. }
assert (R10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (e_len (x_e cx))).
{ rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 10) HS). w10_sr_eval.
  rewrite (w10_den_atom _ 32 L); [rewrite Hlen; reflexivity|]. rewrite ew_ewset_other by lia. exact E32. }
assert (R24 : getr (ms_regs ms) (Z_to_bv 5 24) = w64 (e_len (x_e cx))).
{ rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 24) HS). w10_sr_eval.
  rewrite (w10_den_atom _ 32 L); [rewrite Hlen; reflexivity|]. rewrite ew_ewset_other by lia. exact E32. }
assert (Hcell : forall o i, 0 <= o < 0x138 -> 0 <= i < 8 ->
  aview rsegs (w_H W2) (ms_mem ms) (e_R (x_e cx) + o + i) = aview rsegs (w_H W2) mem2 (e_R (x_e cx) + o + i)).
{ intros o i Ho Hi. apply HK. unfold T_SEG_STK, ASTACK in *. lia. }
rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
unfold rs_from_C2 in HC2. apply (HC2 ly2 S2). unfold rs_cut_C2.
split; [|split; [|split; [|split]]].
- apply (w10_core_run B MT cx ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ (fun _ => False) HC HJ).
  + intros r Hr. apply RK; [destruct Hr as [->|[->| ->]]; vm_compute; discriminate |].
    apply w10_notin. destruct Hr as [->|[->| ->]]; vm_compute; reflexivity.
  + apply RPgCfgChanges.same_io_wvb.
  + intros a Ha _. exact (HK a Ha).
  + intros a [].
- apply (w10_L2_of_post cx (w_H W2) (ms_mem ms) (ms_regs ms)); [| exact R10 | exact R24 | lia].
  apply (rm_atl_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) regs2 (ms_regs ms) (x_e cx) _ HL0).
  intros f Hf. unfold rs_L_post in Hf. cbv zeta in Hf.
  repeat (destruct Hf as [<-|Hf]; [cbn [fst rm_keeps rl_xv];
    first [ exact RK20
          | (apply RK; [vm_compute; discriminate | apply w10_notin; vm_compute; reflexivity])
          | (intros i Hi; apply Hcell; lia) ] |]).
  destruct Hf.
- apply (rm_fsh_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) (e_F (x_e cx)) rs_P0 Hfsh).
  intros i Hi. apply HK. change (length rs_P0) with 52%nat in Hi.
  pose proof (Z.div_pos (e_F (x_e cx)) 8 ltac:(lia)). assert (e_F (x_e cx) / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia).
  unfold shadow_addr, SHADOW_OFF. lia.
- apply (rm_bytes_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) (e_pp (x_e cx)) _ Hpp).
  intros x Hx. apply HK. rewrite (length_pp_bytes _ Hwf) in Hx. unfold PP_SIZE in Hx. lia.
- exact Hlen.
Qed.

(* ---- RT -> C2: corrupt = 1, then the tail ---- *)
Theorem w10_req : rs_piece_W10_req_stmt rsegs B MT.
Proof.
unfold rs_piece_W10_req_stmt. intros cx POST rest Hst HC2.
unfold rs_from_RT. intros ly2 S2 W2 regs2 mem2 md2 sh ps off bs r HRT.
destruct Hst as (HP & _ & _ & _).
destruct HRT as (HC & HL & Hfsh & Hpp & Hin & Hsuf & Hwf & Hlen & Htie & Hoff & Hob & Hb7).
pose proof RPgCfgChanges.cfg_wx as Hwx. pose proof RPgCfgChanges.cfg_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
destruct (w10_ctx B MT cx ly2 S2 W2 regs2 mem2 md2 HP HC)
  as (Hinp & Hfresh & Hal & Hlo & Hhi & Happ & Hpres & H2 & HR16 & HRS & HSTK & Hceil & H47 & HAR).
destruct (w10_F_ctx B cx HP) as (HF1 & HF2 & HF3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (w10_wf_facts sh ps Hwf) as (HW1 & HW2 & HW3 & HW4 & HW5).
unfold rs_plen in Hob.
pose proof HL as HL0.
unfold rs_at_cx, rs_at, rs_L_post in HL. cbv zeta in HL.
rewrite !Forall_cons_iff in HL.
destruct HL as (P8 & P9 & P19 & P23 & P21 & P27 & P25 & P20 & P26 & Q8 & Q28 & Q30 & Q68 & Q78 & Q80 & _).
cbn [fst snd rl_at] in P8, P9, P19, P23, P21, P27, P25, P20, P26.
pose proof HC as (HJ & _).
remember (Ereg regs2 []) as E eqn:HE.
assert (E23 : ew E 23 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs2 _ 23 (Z_to_bv 5 23) eq_refl); exact P23).
assert (E26 : ew E 26 = Z_to_bv 64 (e_pp (x_e cx) + 0x4d18)) by (subst E; rewrite (ew_Ereg_nat regs2 _ 26 (Z_to_bv 5 26) eq_refl); exact P26).
assert (HS : st_ok rsegs E (mkSS 0x82094 sr_atoms
  [YP09.mkRegion (Some 26%nat) 0 4 0 4 []] None
  (mkFacts [(26%nat, mkAF 4096 W10_HI 3); (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] []))
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 0x82094) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. subst E. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (rm_rw_region rsegs _ (w_H W2) mem2 26 (e_pp (x_e cx) + 0x4d18)).
    + rewrite E26. rewrite unsigned_lit_small by lia. reflexivity.
    + lia. + lia.
    + intros o Ho. apply Hpres. lia.
    + constructor.
  - cbn. tauto.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E23, E26, !unsigned_lit_small by (unfold SHADOW_OFF, W10_HI; lia).
    repeat match goal with |- _ /\ _ => split end; try exact I; try (unfold SHADOW_OFF, W10_HI; lia);
    try (rewrite Z.pow_0_r; apply Z.mod_1_r).
    change (2 ^ 3) with 8. rewrite Z.add_mod by lia.
    assert (Hm8 : e_pp (x_e cx) mod 8 = 0).
    { apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal; [|lia]. destruct Hal as [q Hq]. exists (2 * q). lia. }
    rewrite Hm8. reflexivity. }
(* the write window [pp + 0x4d18, + 4) is a shadow entry of the engine: its bytes are marked usable *)
assert (SHOK : sh_ok rsegs W10Bx [mkSHE 26 0 4] E (mrestrict (w_H W2) mem2)).
{ constructor; [|constructor].
  apply (w10_shent_blk B ly2 S2 W2 mem2 md2 E (e_pp (x_e cx)) PP_SIZE 26 0 4 HAR Hinp);
  change (req_size PP_SIZE) with 19744;
  [exact Happ | exact (w10_U_atom E 23 SHADOW_OFF E23 ltac:(unfold SHADOW_OFF; lia)) | | | lia];
  rewrite (w10_U_atom E 26 _ E26 ltac:(lia)); lia. }
unfold cfg_at. change (w64 RS_RT) with (Z_to_bv 64 0x82094).
aj_run_to_tok w10_tbl_ok HS HJ SHOK W10Bspan 0x820ac.
{ eapply (w10_awr_cons_pp E _ _ _ _ _ _ _ _ _ 26%nat (e_pp (x_e cx) + 0x4d18) (e_pp (x_e cx))); [reflexivity | | exact Hinp | exact Hfresh | cbn; lia | cbn; unfold PP_SIZE; lia | apply awr_ok_nil].
  rewrite E26. apply unsigned_lit_small. lia. }
set (pc0 := e_pp (x_e cx) + 0x4d18) in *.
assert (HK : forall a, 0 <= a < 2 ^ 64 -> ~ (pc0 <= a < pc0 + 4) ->
  aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha Hn. apply (w10_frame_kept _ _ _ _ _ HFr a Ha). intros (rg & Hr & Hrb). cbn [ss_mem] in Hr.
  destruct Hr as [<-|[]]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb. rewrite E26 in Hrb.
  rewrite unsigned_lit_small in Hrb by lia. apply Hn. lia. }
assert (HV : val_mem rsegs (mrestrict (w_H W2) (ms_mem ms)) pc0 4 1).
{ pose proof (w7_region_nth _ _ _ 0 _ HS eq_refl) as HR0.
  replace pc0 with (pc0 + 0) by lia.
  apply (w7_field _ _ 26 pc0 _ 0 4 0 4 0 4 (SLit 1) 1 HR0); [| left; reflexivity | reflexivity | cbn; lia | cbn; lia].
  rewrite !ew_ewset_other by lia. rewrite E26. apply unsigned_lit_small. lia. }
assert (HE0 : env_agree 32 (Ereg regs2 []) (ewset (ewset E 32 w) 33 w0)).
{ subst E. eapply env_agree_trans; [apply env_agree_ewset|]. eapply env_agree_le; [|apply env_agree_ewset]. lia. }
pose proof (w7_regs_kept _ _ ms regs2 [] (w_H W2) [Z_to_bv 5 10; Z_to_bv 5 11] HS HE0
  ltac:(vm_compute; reflexivity)) as RK.
assert (Hcell : forall o i, 0 <= o < 0x138 -> 0 <= i < 8 ->
  aview rsegs (w_H W2) (ms_mem ms) (e_R (x_e cx) + o + i) = aview rsegs (w_H W2) mem2 (e_R (x_e cx) + o + i)).
{ intros o i Ho Hi. apply HK; [unfold T_SEG_STK, ASTACK in *; lia|]. subst pc0. unfold T_SEG_STK, ASTACK in *. lia. }
assert (Himg : Z.of_nat (length (rs_img_corr sh ps off bs (Z.of_nat (length bs)))) = PP_SIZE).
{ unfold rs_img_corr. apply length_pp_image; [| exact HW3 | exact HW4].
  rewrite length_overwrite; [unfold POD_BUF_MAX; lia|]. rewrite length_firstn. lia. }
assert (Hnew : rs_pp_at rsegs cx W2 (ms_mem ms) (pp_bytes (fst (pod_build rest)))).
{ rewrite Htie, <- (w10_img_corrupt sh ps off bs Hwf ltac:(lia) ltac:(lia)).
  replace bs with (firstn (Z.to_nat (Z.of_nat (length bs))) bs) at 1 by (rewrite Nat2Z.id; apply firstn_all).
  fold (rs_img_corr sh ps off bs (Z.of_nat (length bs))). unfold le32.
  apply (rm_bytes_store rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) (e_pp (x_e cx)) _ (Z.to_nat OFF_CORRUPT) 4 1 Hpp).
  - replace (e_pp (x_e cx) + Z.of_nat (Z.to_nat OFF_CORRUPT)) with pc0 by (subst pc0; unfold OFF_CORRUPT; lia). exact HV.
  - unfold OFF_CORRUPT, PP_SIZE in *. lia.
  - intros y Hy Hn. apply HK; [unfold PP_SIZE in *; lia|]. subst pc0. unfold OFF_CORRUPT in Hn. lia. }
rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
apply (w10_tail cx POST rest ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ HP HC2).
- apply (w10_core_run B MT cx ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ (fun a => pc0 <= a < pc0 + 4) HC HJ).
  + intros rr Hr. apply RK; [destruct Hr as [->|[->| ->]]; vm_compute; discriminate |].
    apply w10_notin. destruct Hr as [->|[->| ->]]; vm_compute; reflexivity.
  + apply RPgCfgChanges.same_io_wvb.
  + exact HK.
  + intros a Ha. right. subst pc0. unfold PP_SIZE. lia.
- apply (rm_atl_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) regs2 (ms_regs ms) (x_e cx) _ HL0).
  intros f Hf. unfold rs_L_post in Hf. cbv zeta in Hf.
  repeat (destruct Hf as [<-|Hf]; [cbn [fst rm_keeps rl_xv];
    first [ (apply RK; [vm_compute; discriminate | apply w10_notin; vm_compute; reflexivity])
          | (intros i Hi; apply Hcell; lia) ] |]).
  destruct Hf.
- apply (rm_fsh_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) (e_F (x_e cx)) rs_P0 Hfsh).
  intros i Hi. change (length rs_P0) with 52%nat in Hi.
  pose proof (Z.div_pos (e_F (x_e cx)) 8 ltac:(lia)). assert (e_F (x_e cx) / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia).
  apply HK; [unfold shadow_addr, SHADOW_OFF; lia|].
  pose proof (w10_shadow_not_pp (e_pp (x_e cx)) (e_F (x_e cx)) i Happ HF3 ltac:(lia)) as Hs. subst pc0. unfold PP_SIZE in Hs. lia.
- exact Hnew.
- exact Hlen.
Qed.
End r.

Print Assumptions w10_tail.
Print Assumptions w10_req.
