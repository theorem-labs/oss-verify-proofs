(* lv2_locate_manifest_readings, segment PP (rd_seg_P of lib/A/FMW_rd_cuts.v): the declaration body from P
   (0x81da8, lv2_locate.c:115) to the strchr call (0x81f1c).  This file walks P's own stretch -- the shadow check of
   p0 = at + s11, the byte there, the two isspace branches, and the scratch values the space body computes -- and
   assembles the three inner loops (FMW_rd_pp_w1/w2/w3.v) and the stores-and-call stretch (FMW_rd_pp_st.v) into
   rd_P_holds.  Not a space: the declaration is DNone (readings_scan.db_nsp) and the scan goes on at i + 1 (RD_L).
   A space: the first loop's head at 0x81df0 with no byte consumed yet. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YCbm.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC20 YI00 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMPstat FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_g3kit FMW_rd_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_rd_cuts FMW_rd_ret ACej.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_rd_pp_cuts.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import ManifestModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require readings_scan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ---- SP, 0x81dc8: the space body, reached from both isspace edges of P ---- *)
Definition PP_SP : Z := 0x81dc8.
Definition ss_pp_SP : sstate :=
  mkSS PP_SP pp_regsP [pp_frameR; pp_byte 35 0] None
    (mkFacts [PP_AF2; PP_AF8; pp_afstr 35; pp_afbyte 34] []
       [(SAlu ALU_ADD (SOff 24 0) (SOff 27 0), SOff 35 0)]).

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.

(* the entry state of the space body: P's state at the pc the two isspace edges reach *)
Lemma pp_entry_SP : forall (W : world tfibsegs) regs mem F u2v u3v s11 atv c,
  pp_fr W mem F u2v u3v ->
  getr regs 2 = w64 F -> getr regs 8 = w64 SHADOW_OFF -> getr regs 9 = w64 32 -> getr regs 18 = w64 5 ->
  getr regs 24 = w64 atv -> getr regs 27 = w64 s11 -> 0 <= s11 <= 7 ->
  4096 <= atv -> atv + s11 + 1 <= alloc_ceiling -> 0 <= c < 256 ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (atv + s11) 1 c ->
  st_ok tfibsegs (Ereg regs (pp_extra u2v u3v c (atv + s11))) ss_pp_SP
    (restrict (w_H W) (mkst regs (Z_to_bv 64 PP_SP) mem (seg_rom tfibsegs))).
Proof.
intros W regs mem F u2v u3v s11 atv c (V48 & V50 & V60 & Hu2 & Hu3 & HFc & HF2 & HF16)
  R2 R8 R9 R18 R24 R27 Hs11 Hat Hatc Hc Vc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Ereg regs (pp_extra u2v u3v c (atv + s11))).
assert (E2 : ew E 2 = w64 F) by (unfold E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact R2).
assert (E8 : ew E 8 = w64 SHADOW_OFF) by (unfold E; rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8).
assert (E24 : ew E 24 = w64 atv) by (unfold E; rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact R24).
assert (E27 : ew E 27 = w64 s11) by (unfold E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact R27).
assert (E32 : ew E 32 = w64 u2v) by (unfold E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 u3v) by (unfold E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 c) by (unfold E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = w64 (atv + s11)) by (unfold E; exact (ew_Ereg_extra regs _ 3)).
pp_uw E 2%nat F E2. pp_uw E 8%nat SHADOW_OFF E8. pp_uw E 24%nat atv E24. pp_uw E 27%nat s11 E27.
pp_uw E 34%nat c E34. pp_uw E 35%nat (atv + s11) E35.
unfold ss_pp_SP. apply (entry_st_ok_full tfibsegs);
  change (Ereg regs (pp_extra u2v u3v c (atv + s11))) with E.
- unfold pp_regsP.
  repeat (apply regs_ok_pin; [| intros X; discriminate X |]); [apply regs_ok_Ereg | ..];
    cbn [sv_denot]; first [exact R9 | exact R18].
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + apply (pp_frameR_ok E _ F u2v u3v); try assumption; try lia.
  + apply (pp_byteR_ok E _ 35 0 (atv + s11) c); try assumption; try lia. rewrite Z.add_0_r. exact Vc.
- apply pairwise_disjoint_of_extents. unfold pp_frameR, pp_byte, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  repeat match goal with H : bv_unsigned (ew E ?n) = ?v |- _ => rewrite H end.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I|]].
  + cbn [f_atoms atoms_ok PP_AF2 PP_AF8 pp_afstr pp_afbyte]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    repeat match goal with H : bv_unsigned (ew E ?n) = ?v |- _ => rewrite H end.
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF. repeat split; lia.
  + cbn [f_alias alias_ok]. split; [|exact I].
    apply U_inj.
    rewrite (U_add_off_atom E 24 0 27 0) by
      (repeat match goal with H : bv_unsigned (ew E ?n) = ?v |- _ => rewrite H end; unfold M64; lia).
    rewrite (U_atom E 35 (atv + s11) E35 ltac:(lia)).
    repeat match goal with H : bv_unsigned (ew E ?n) = ?v |- _ => rewrite H end. lia.
Qed.
End e.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable CTX : list (list Z).
Hypothesis IMG : fm_img_facts tfibsegs B.
Hypothesis STRCHR : astrchr_realizes tfibsegs B PC_strchr.

(* the space body 0x81dc8: it computes s10 = 0, the three counters and s6, and falls into the first loop *)
Lemma pp_space_body : forall f, pp_seg_W1 B CTX f ->
  forall cx i d s11 ly3 S3 W3 regs mem md,
  rd_base B CTX cx -> rd_loop B cx d ly3 S3 W3 regs mem md -> rd_acc cx i d (S f) ->
  (i < length (cx_tb cx))%nat -> head (cx_tb cx) i = Some (i + s11)%nat -> (s11 = 6 \/ s11 = 7)%nat ->
  is_space (byte_at (cx_tb cx) (i + s11)) = true ->
  getr regs 10 = w64 (rd_p0 cx i s11) -> getr regs 19 = w64 58 ->
  getr regs 24 = w64 (cx_t cx + Z.of_nat i) -> getr regs 27 = w64 (Z.of_nat s11) ->
  SRr tfibsegs W3 (cfg_at tfibsegs PP_SP regs mem md) (rd_post B cx).
Proof.
intros f HW1 cx i d s11 ly3 S3 W3 regs mem md HB HI HA Hi Hh Hs11 Hsp R10 R19 R24 R27.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof g3_wx as Hwx. pose proof g3_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (pp_facts_of B CTX cx d ly3 S3 W3 regs mem md HB HI) as
  (HFR & R2 & R8 & R9 & R18 & Ct & Cu & Ht4 & Htc & Hu4 & Huc & HWR & HJ).
assert (Hple : (i + s11 <= length (cx_tb cx))%nat) by exact (pp_head_le (cx_tb cx) i _ Hh).
destruct (pp_val_at W3 mem (cx_t cx) (cx_tb cx) (i + s11) Ct Hple) as [Vc Hc].
set (cb := byte_at (cx_tb cx) (i + s11)) in *.
set (atv := cx_t cx + Z.of_nat i) in *.
assert (Hp0 : rd_p0 cx i s11 = atv + Z.of_nat s11) by (unfold rd_p0, atv; lia).
assert (Vc' : val_mem tfibsegs (mrestrict (w_H W3) mem) (atv + Z.of_nat s11) 1 cb)
  by (replace (atv + Z.of_nat s11) with (cx_t cx + Z.of_nat (i + s11)) by (unfold atv; lia); exact Vc).
assert (Hs11z : 0 <= Z.of_nat s11 <= 7) by (destruct Hs11 as [-> | ->]; lia).
assert (Hatv : 4096 <= atv) by (unfold atv; lia).
assert (Hatc : atv + Z.of_nat s11 + 1 <= alloc_ceiling) by (unfold atv; lia).
pose proof (pp_entry_SP W3 regs mem (cx_F cx) (cx_u cx - 2) (cx_u cx - 3) (Z.of_nat s11) atv cb
  HFR R2 R8 R9 R18 R24 R27 Hs11z Hatv Hatc Hc Vc') as HS.
set (E := Ereg regs (pp_extra (cx_u cx - 2) (cx_u cx - 3) cb (atv + Z.of_nat s11))) in *.
assert (E32 : ew E 32 = w64 (cx_u cx - 2)) by (unfold E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 (cx_u cx - 3)) by (unfold E; exact (ew_Ereg_extra regs _ 1)).
assert (E35 : ew E 35 = w64 (atv + Z.of_nat s11)) by (unfold E; exact (ew_Ereg_extra regs _ 3)).
assert (E24 : ew E 24 = w64 atv) by (unfold E; rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact R24).
assert (E27 : ew E 27 = w64 (Z.of_nat s11))
  by (unfold E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact R27).
assert (E10 : ew E 10 = w64 (atv + Z.of_nat s11))
  by (unfold E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), R10, Hp0; reflexivity).
assert (SHOK : sh_ok tfibsegs PP_Bx [] E
  (mrestrict (w_H W3) (ms_mem (mkst regs (Z_to_bv 64 PP_SP) mem (seg_rom tfibsegs))))) by constructor.
change mem with (ms_mem (mkst regs (Z_to_bv 64 PP_SP) mem (seg_rom tfibsegs))) in HJ.
unfold cfg_at. change (w64 PP_SP) with (Z_to_bv 64 PP_SP).
aj_run_to_tok rd_tbl_ok HS HJ SHOK PP_Bspan PP_L1.
{ awr_ok_tac. }
pose proof (frame_of_read_only E (ss_mem ss_pp_SP) _ _ ltac:(vm_compute; reflexivity) HF) as Hm.
cbn [ms_mem] in Hm. rewrite Hm in HJ.
(* the register values at the first loop's head *)
pp_lift HS F32 32%nat E32. pp_lift HS F33 33%nat E33. pp_lift HS F35 35%nat E35.
pp_lift HS F24 24%nat E24. pp_lift HS F27 27%nat E27. pp_lift HS F10 10%nat E10.
pp_rd HS (10%bv : bv 5) Q10. pp_rd HS (11%bv : bv 5) Q11. pp_rd HS (16%bv : bv 5) Q16.
pp_rd HS (20%bv : bv 5) Q20. pp_rd HS (21%bv : bv 5) Q21. pp_rd HS (22%bv : bv 5) Q22.
pp_rd HS (25%bv : bv 5) Q25. pp_rd HS (26%bv : bv 5) Q26.
pp_rd HS (9%bv : bv 5) Q9. pp_rd HS (18%bv : bv 5) Q18.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
  pose proof (g3_regs_of_st_ok tfibsegs Ev _ _ regs _ PP_KEPT HS (env_agree_refl _ _)
    ltac:(vm_compute; reflexivity)) as HK end.
cbn [ms_regs restrict] in HK.
pose proof (g3_regs_of_st_ok tfibsegs _ _ _ regs _ [19; 24; 27]%bv HS (env_agree_refl _ _)
  ltac:(vm_compute; reflexivity)) as HK2.
cbn [ms_regs restrict] in HK2.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl).
lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?x)] =>
  let v := eval vm_compute in (ss_pc x) in change (ss_pc x) with v end.
rewrite Hm.
apply (HW1 cx i d s11 0%nat ly3 S3 W3 _ _ _ HB).
unfold pp_at_L1, pp_head. cbn [Z.of_nat].
split; [split|].
- apply (pp_loop_keep B cx d ly3 S3 W3 regs _ md); [exact HI | exact HJ | exact HK | |];
    [rewrite Q9 | rewrite Q18]; cbn [sv_denot]; reflexivity.
- split; [exact HA|]. split; [exact Hi|]. split; [exact Hh|]. split; [exact Hs11|]. split; [exact Hsp|].
  split; [rewrite (HK2 19%bv ltac:(cbv [In]; left; apply bv_eq; reflexivity)); exact R19|].
  split; [rewrite (HK2 24%bv ltac:(cbv [In]; right; left; apply bv_eq; reflexivity)); exact R24
         | rewrite (HK2 27%bv ltac:(cbv [In]; right; right; left; apply bv_eq; reflexivity)); exact R27].
- split; [lia|].
  rewrite Q10, Q11, Q16, Q20, Q21, Q22, Q25, Q26.
  rewrite Hp0.
  split; [rewrite (pp_reg_off _ 10%nat _ 0 F10); unfold w64; f_equal; lia|].
  split; [rewrite (pp_reg_off _ 35%nat _ 0 F35); unfold w64; f_equal; lia|].
  split; [rewrite (pp_v_neg _ 35%nat _ F35); unfold w64; f_equal; lia|].
  split; [rewrite (pp_v_sub2 _ 33%nat 35%nat _ _ F33 F35); unfold w64; f_equal; lia|].
  split; [rewrite (pp_v_sub3 _ 24%nat 27%nat 32%nat _ _ _ F24 F27 F32); unfold w64; f_equal; lia|].
  split; [rewrite (pp_reg_off _ 10%nat _ 0 F10); unfold w64; f_equal; lia|].
  split; [rewrite (pp_v_sub2 _ 32%nat 35%nat _ _ F32 F35); unfold w64; f_equal; lia|].
  cbn [sv_denot Z.of_nat]. reflexivity.
Qed.

(* P, 0x81da8: the shadow check of p0 and the byte there; not a space is a DNone declaration, a space falls into
   the space body at 0x81dc8 *)
Lemma pp_p_body : forall f, rd_seg_L B CTX f -> pp_seg_W1 B CTX f -> rd_seg_P B CTX (S f).
Proof.
intros f HL HW1 cx i d s11 ly3 S3 W3 regs mem md HB HP.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof g3_wx as Hwx. pose proof g3_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HP as (HI & HA & Hi & Hh & Hs11 & R19 & R20 & R24 & R27).
pose proof (pp_facts_of B CTX cx d ly3 S3 W3 regs mem md HB HI) as
  (HFR & R2 & R8 & R9 & R18 & Ct & Cu & Ht4 & Htc & Hu4 & Huc & HWR & HJ).
assert (Hple : (i + s11 <= length (cx_tb cx))%nat) by exact (pp_head_le (cx_tb cx) i _ Hh).
destruct (pp_val_at W3 mem (cx_t cx) (cx_tb cx) (i + s11) Ct Hple) as [Vc Hcb].
set (cb := byte_at (cx_tb cx) (i + s11)) in *.
set (atv := cx_t cx + Z.of_nat i) in *.
assert (Hp0 : rd_p0 cx i s11 = atv + Z.of_nat s11) by (unfold rd_p0, atv; lia).
assert (Vc' : val_mem tfibsegs (mrestrict (w_H W3) mem) (atv + Z.of_nat s11) 1 cb)
  by (replace (atv + Z.of_nat s11) with (cx_t cx + Z.of_nat (i + s11)) by (unfold atv; lia); exact Vc).
assert (Hs11z : 0 <= Z.of_nat s11 <= 7) by (destruct Hs11 as [-> | ->]; lia).
assert (Hatv : 4096 <= atv) by (unfold atv; lia).
assert (Hatc : atv + Z.of_nat s11 + 1 <= alloc_ceiling) by (unfold atv; lia).
pose proof (pp_entry_P W3 regs mem (cx_F cx) (cx_u cx - 2) (cx_u cx - 3) (Z.of_nat s11) atv cb
  HFR R2 R8 R9 R18 R24 R27 Hs11z Hatv Hatc Hcb Vc') as HS.
set (E := Ereg regs (pp_extra (cx_u cx - 2) (cx_u cx - 3) cb (atv + Z.of_nat s11))) in *.
assert (E34 : ew E 34 = w64 cb) by (unfold E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = w64 (atv + Z.of_nat s11)) by (unfold E; exact (ew_Ereg_extra regs _ 3)).
assert (E8 : ew E 8 = w64 SHADOW_OFF) by (unfold E; rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8).
assert (E24 : ew E 24 = w64 atv) by (unfold E; rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact R24).
assert (HBx : U E PP_Bx = SHADOW_OFF) by exact (pp_U_Bx E E8).
assert (SHOK : sh_ok tfibsegs PP_Bx [] E
  (mrestrict (w_H W3) (ms_mem (mkst regs (Z_to_bv 64 RD_P) mem (seg_rom tfibsegs))))) by constructor.
change mem with (ms_mem (mkst regs (Z_to_bv 64 RD_P) mem (seg_rom tfibsegs))) in HJ.
unfold cfg_at. change (w64 RD_P) with (Z_to_bv 64 RD_P).
aj_run_tok rd_tbl_ok HS HJ SHOK PP_Bspan.
{ apply (pp_obl1 W3 _ E (SOff 35 0) (cx_t cx) (cx_tb cx) Ct HBx);
    rewrite (pp_U_off E 35%nat (atv + Z.of_nat s11) 0 E35); unfold zcanon, M64;
    rewrite Z.mod_small by (unfold atv; lia); unfold atv; lia. }
{ awr_ok_tac. }
pose proof (frame_of_read_only E (ss_mem ss_pp_P) _ _ ltac:(vm_compute; reflexivity) HF) as Hm.
cbn [ms_mem] in Hm.
srr_branch_tok rd_tbl_ok HS SHOK PP_Bspan.
- (* not 9 .. 13 *)
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
    assert (H34 : ew Ev 34 = Z_to_bv 64 cb) by (cbn [ew ewset extK Nat.eqb]; exact E34) end.
  erewrite (pp_Db_of _ cb _ _ _ H34) in Hc by reflexivity. clear H34.
  aj_run_to_tok rd_tbl_ok HS HJ SHOK PP_Bspan 0x81ea4.
  { awr_ok_tac. }
  lazymatch type of HF0 with frame_of _ ?rs _ _ =>
    pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF0) as Hm2 end.
  cbn [ms_mem] in Hm2.
  srr_branch_tok rd_tbl_ok HS SHOK PP_Bspan.
  + (* and not 32: the byte is not a space, the declaration is DNone *)
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
      assert (H34b : ew Ev 34 = Z_to_bv 64 cb) by (cbn [ew ewset extK Nat.eqb]; exact E34) end.
    erewrite (pp_Db_of _ cb _ _ _ H34b) in Hc0 by reflexivity.
    assert (Hnsp : is_space cb = false) by exact (pp_sp_no cb Hcb Hc Hc0).
    assert (Hdecl : decl (cx_tb cx) i = DNone).
    { rewrite (readings_scan.decl_some (cx_tb cx) i (i + s11)%nat Hh).
      exact (readings_scan.db_nsp (cx_tb cx) (i + s11)%nat Hnsp). }
    aj_run_to_tok rd_tbl_ok HS HJ SHOK PP_Bspan RD_L.
    { awr_ok_tac. }
    lazymatch type of HF1 with frame_of _ ?rs _ _ =>
      pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF1) as Hm3 end.
    cbn [ms_mem] in Hm3.
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
      pose proof (g3_regs_of_st_ok tfibsegs Ev _ _ regs _ PP_KEPT HS ltac:(env_agree_chain (env_agree_refl 32 E))
        ltac:(vm_compute; reflexivity)) as HK;
      pose proof (g3_regs_of_st_ok tfibsegs Ev _ _ regs _ [20]%bv HS ltac:(env_agree_chain (env_agree_refl 32 E))
        ltac:(vm_compute; reflexivity)) as HK2 end.
    cbn [ms_regs restrict] in HK, HK2.
    pp_lift HS F24 24%nat E24.
    pp_rd HS (24%bv : bv 5) Q24. pp_rd HS (9%bv : bv 5) Q9. pp_rd HS (18%bv : bv 5) Q18.
    rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl).
    lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?x)] =>
      let v := eval vm_compute in (ss_pc x) in change (ss_pc x) with v end.
    rewrite Hm3, Hm2, Hm in HJ |- *.
    apply (pp_to_L B CTX f cx i d ly3 S3 W3 _ mem _ HL HB).
    * apply (pp_loop_keep B cx d ly3 S3 W3 regs _ md); [exact HI | exact HJ | exact HK | |];
        [rewrite Q9 | rewrite Q18]; cbn [sv_denot]; reflexivity.
    * exact HA.
    * exact Hi.
    * exact Hdecl.
    * rewrite (HK2 20%bv ltac:(cbv [In]; left; apply bv_eq; reflexivity)). exact R20.
    * rewrite Q24, (pp_reg_off _ 24%nat _ 1 F24). unfold w64. f_equal. all: unfold atv; lia.
  + (* the byte is 32, a space *)
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
      assert (H34b : ew Ev 34 = Z_to_bv 64 cb) by (cbn [ew ewset extK Nat.eqb]; exact E34) end.
    erewrite (pp_Db_of _ cb _ _ _ H34b) in Hc0 by reflexivity.
    assert (Hsp : is_space cb = true) by exact (pp_sp_32 cb Hcb Hc Hc0).
    aj_run_to_tok rd_tbl_ok HS HJ SHOK PP_Bspan PP_SP.
    { awr_ok_tac. }
    lazymatch type of HF1 with frame_of _ ?rs _ _ =>
      pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF1) as Hm3 end.
    cbn [ms_mem] in Hm3.
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
      pose proof (g3_regs_of_st_ok tfibsegs Ev _ _ regs _ PP_KEPT HS ltac:(env_agree_chain (env_agree_refl 32 E))
        ltac:(vm_compute; reflexivity)) as HK;
      pose proof (g3_regs_of_st_ok tfibsegs Ev _ _ regs _ [19; 24; 27]%bv HS ltac:(env_agree_chain (env_agree_refl 32 E))
        ltac:(vm_compute; reflexivity)) as HK2 end.
    cbn [ms_regs restrict] in HK, HK2.
    pp_lift HS F35 35%nat E35.
    pp_rd HS (10%bv : bv 5) Q10. pp_rd HS (9%bv : bv 5) Q9. pp_rd HS (18%bv : bv 5) Q18.
    rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl).
    lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?x)] =>
      let v := eval vm_compute in (ss_pc x) in change (ss_pc x) with v end.
    rewrite Hm3, Hm2, Hm in HJ |- *.
    apply (pp_space_body f HW1 cx i d s11 ly3 S3 W3 _ mem _ HB).
    * apply (pp_loop_keep B cx d ly3 S3 W3 regs _ md); [exact HI | exact HJ | exact HK | |];
        [rewrite Q9 | rewrite Q18]; cbn [sv_denot]; reflexivity.
    * exact HA.
    * exact Hi.
    * exact Hh.
    * exact Hs11.
    * exact Hsp.
    * rewrite Q10, (pp_reg_off _ 35%nat _ 0 F35), Hp0. unfold w64. f_equal. lia.
    * rewrite (HK2 19%bv ltac:(cbv [In]; left; apply bv_eq; reflexivity)). exact R19.
    * rewrite (HK2 24%bv ltac:(cbv [In]; right; left; apply bv_eq; reflexivity)). exact R24.
    * rewrite (HK2 27%bv ltac:(cbv [In]; right; right; left; apply bv_eq; reflexivity)). exact R27.
- (* 9 .. 13: a space *)
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
    assert (H34 : ew Ev 34 = Z_to_bv 64 cb) by (cbn [ew ewset extK Nat.eqb]; exact E34) end.
  erewrite (pp_Db_of _ cb _ _ _ H34) in Hc by reflexivity. clear H34.
  assert (Hsp : is_space cb = true) by exact (pp_sp_in cb Hcb Hc).
  aj_run_to_tok rd_tbl_ok HS HJ SHOK PP_Bspan PP_SP.
  { awr_ok_tac. }
  lazymatch type of HF0 with frame_of _ ?rs _ _ =>
    pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF0) as Hm2 end.
  cbn [ms_mem] in Hm2.
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
    pose proof (g3_regs_of_st_ok tfibsegs Ev _ _ regs _ PP_KEPT HS ltac:(env_agree_chain (env_agree_refl 32 E))
      ltac:(vm_compute; reflexivity)) as HK;
    pose proof (g3_regs_of_st_ok tfibsegs Ev _ _ regs _ [19; 24; 27]%bv HS ltac:(env_agree_chain (env_agree_refl 32 E))
      ltac:(vm_compute; reflexivity)) as HK2 end.
  cbn [ms_regs restrict] in HK, HK2.
  pp_lift HS F35 35%nat E35.
  pp_rd HS (10%bv : bv 5) Q10. pp_rd HS (9%bv : bv 5) Q9. pp_rd HS (18%bv : bv 5) Q18.
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl).
  lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?x)] =>
    let v := eval vm_compute in (ss_pc x) in change (ss_pc x) with v end.
  rewrite Hm2, Hm in HJ |- *.
  apply (pp_space_body f HW1 cx i d s11 ly3 S3 W3 _ mem _ HB).
  + apply (pp_loop_keep B cx d ly3 S3 W3 regs _ md); [exact HI | exact HJ | exact HK | |];
      [rewrite Q9 | rewrite Q18]; cbn [sv_denot]; reflexivity.
  + exact HA.
  + exact Hi.
  + exact Hh.
  + exact Hs11.
  + exact Hsp.
  + rewrite Q10, (pp_reg_off _ 35%nat _ 0 F35), Hp0. unfold w64. f_equal. lia.
  + rewrite (HK2 19%bv ltac:(cbv [In]; left; apply bv_eq; reflexivity)). exact R19.
  + rewrite (HK2 24%bv ltac:(cbv [In]; right; left; apply bv_eq; reflexivity)). exact R24.
  + rewrite (HK2 27%bv ltac:(cbv [In]; right; right; left; apply bv_eq; reflexivity)). exact R27.
Qed.

End c.
