(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMW_rd_pp.v (a working branch e2e59892bef), re-walked
   for B's code (B-readings.lst 0x82060 .. 0x82098 and CONT 0x81ffc .. 0x82010). *)
(* lv2_locate_manifest_readings on fm.asan-ubsan, segment PP (rd_seg_P of lib/B/FMW_rd_cuts.v): P's own stretch from
   0x82060 (lv2_locate.c:115) -- s6 = p0 = at + s11, the shadow check of p0, the byte there, the two isspace branches --
   and the space body 0x82080 (a1 = p0, s9 = u - 2 - s11 - at, s10 = u - 2 - p0, a0 = p0 + 1), which falls into the
   first loop's head 0x82098 with no byte consumed.  Not a space: the declaration is DNone (readings_scan.db_nsp) and
   CONT 0x81ffc goes on at i + 1 (RD_L); CONT's guard 0x8200c `bne a0, s0` (fall-through 0x82010 `j 0x823b4`) is
   refuted by a0 = at, a text position (FMTrapB K1n fmt_ne_taken, through pp_guard). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YCbm.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YC20 YI00 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_g3kit FMW_rd_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YCej.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_rd_cuts FMW_rd_ret.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMTrapB FMW_rd_pp_cuts.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import ManifestModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require readings_scan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* at a cut: the machine state in mkst form, the kept registers, the run's memory back to the entry memory *)
Ltac pp_land HS HJ E regs HK :=
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl);
  lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?x)] =>
    let v := eval vm_compute in (ss_pc x) in change (ss_pc x) with v end;
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
    pose proof (g3_regs_of_st_ok tfibsegs Ev _ _ regs _ PP_KEPT HS ltac:(env_agree_chain (env_agree_refl 32 E))
      ltac:(vm_compute; reflexivity)) as HK end;
  cbn [ms_regs restrict] in HK;
  repeat match goal with H : ms_mem _ = _ |- _ => rewrite H in HJ; rewrite H; clear H end.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable CTX : list (list Z).

(* the space body 0x82080: a1 = p0, a2 = (u - 2) - s11, a0 = p0 + 1, s9 = a2 - at, s10 = (u - 2) - p0; then the first
   loop's head 0x82098 with k = 0 *)
Lemma pp_space_body : forall f, pp_seg_W1 B CTX f ->
  forall cx i d s11 ly3 S3 W3 regs mem md,
  rd_base B CTX cx -> rd_loop B cx d ly3 S3 W3 regs mem md -> rd_acc cx i d (S f) ->
  (i < length (cx_tb cx))%nat -> head (cx_tb cx) i = Some (i + s11)%nat -> (s11 = 6 \/ s11 = 7)%nat ->
  is_space (byte_at (cx_tb cx) (i + s11)) = true ->
  getr regs 10 = w64 (Z.of_nat s11) -> getr regs 21 = w64 (cx_t cx + Z.of_nat i) ->
  getr regs 22 = w64 (rd_p0 cx i s11) ->
  SRr tfibsegs W3 (cfg_at tfibsegs PP_SP regs mem md) (rd_post B cx).
Proof.
intros f HW1 cx i d s11 ly3 S3 W3 regs mem md HB HI HA Hi Hh Hs11 Hsp R10 R21 R22.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof g3_wx as Hwx. pose proof g3_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (pp_facts_of B CTX cx d ly3 S3 W3 regs mem md HB HI) as
  (HFR & R2 & R27 & HPN & R9 & Ct & Cu & Ht4 & Htc & Hu4 & Huc & HWR & HJ).
assert (Hple : (i + s11 <= length (cx_tb cx))%nat) by exact (pp_head_le (cx_tb cx) i _ Hh).
destruct (pp_val_at W3 mem (cx_t cx) (cx_tb cx) (i + s11) Ct Hple) as [Vc Hcb].
set (cb := byte_at (cx_tb cx) (i + s11)) in *.
assert (Hp0 : rd_p0 cx i s11 = cx_t cx + Z.of_nat i + Z.of_nat s11) by reflexivity.
assert (Vc' : val_mem tfibsegs (mrestrict (w_H W3) mem) (cx_t cx + Z.of_nat i + Z.of_nat s11) 1 cb)
  by (replace (cx_t cx + Z.of_nat i + Z.of_nat s11) with (cx_t cx + Z.of_nat (i + s11)) by lia; exact Vc).
assert (Hs11z : 0 <= Z.of_nat s11 <= 7) by (destruct Hs11 as [-> | ->]; lia).
pose proof (pp_entry_P PP_SP W3 regs mem (cx_F cx) (cx_u cx - 2) (Z.of_nat s11) (cx_t cx + Z.of_nat i) cb
  HFR R2 R27 HPN R21 R10 Hs11z ltac:(lia) ltac:(lia) Hcb Vc') as HS.
set (E := Ereg regs (pp_extra (cx_u cx - 2) cb (cx_t cx + Z.of_nat i + Z.of_nat s11))) in *.
assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs q)
  by (intros n q Hn; unfold E; apply ew_Ereg_nat; exact Hn).
pose proof (eq_trans (EE 9%nat 9%bv eq_refl) R9) as E9.
pose proof (eq_trans (EE 10%nat 10%bv eq_refl) R10) as E10.
pose proof (eq_trans (EE 21%nat 21%bv eq_refl) R21) as E21.
pose proof (eq_trans (EE 22%nat 22%bv eq_refl) R22) as E22.
assert (E32 : ew E 32 = w64 (cx_u cx - 2)) by (unfold E; exact (ew_Ereg_extra regs _ 0)).
assert (E34 : ew E 34 = w64 (cx_t cx + Z.of_nat i + Z.of_nat s11)) by (unfold E; exact (ew_Ereg_extra regs _ 2)).
clear EE.
assert (SHOK : sh_ok tfibsegs PP_Bx [] E
  (mrestrict (w_H W3) (ms_mem (mkst regs (Z_to_bv 64 PP_SP) mem (seg_rom tfibsegs))))) by constructor.
change mem with (ms_mem (mkst regs (Z_to_bv 64 PP_SP) mem (seg_rom tfibsegs))) in HJ.
unfold cfg_at. change (w64 PP_SP) with (Z_to_bv 64 PP_SP).
aj_run_to_tok rd_tbl_ok HS HJ SHOK PP_Bspan PP_L1.
{ awr_ok_tac. }
pp_fr Hm.
pp_land HS HJ E regs HK.
apply (HW1 cx i d s11 0%nat ly3 S3 W3 _ _ _ HB).
unfold pp_at_L1, pp_head, pp_cd. cbv zeta.
split; [split|].
- apply (pp_loop_keep B cx d ly3 S3 W3 regs _ md); [exact HI | exact HJ | exact HK | ..]; pp_g HS.
- split; [exact HA|]. split; [exact Hi|]. split; [exact Hh|]. split; [exact Hs11|]. split; [exact Hsp|]. pp_g HS.
- split; [lia|]. do 4 (split; [pp_g HS|]). pp_g HS.
Qed.

(* P, 0x82060: s6 = p0, the shadow check of p0 and the byte there; not a space is a DNone declaration (CONT, guard
   0x8200c), a space falls into the space body at 0x82080 *)
Lemma pp_p_body : forall f, rd_seg_L B CTX f -> pp_seg_W1 B CTX f -> rd_seg_P B CTX (S f).
Proof.
intros f HL HW1 cx i d s11 ly3 S3 W3 regs mem md HB HP.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof g3_wx as Hwx. pose proof g3_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HP as (HI & HA & Hi & Hh & Hs11 & R10 & R21).
pose proof (pp_facts_of B CTX cx d ly3 S3 W3 regs mem md HB HI) as
  (HFR & R2 & R27 & HPN & R9 & Ct & Cu & Ht4 & Htc & Hu4 & Huc & HWR & HJ).
assert (Hple : (i + s11 <= length (cx_tb cx))%nat) by exact (pp_head_le (cx_tb cx) i _ Hh).
destruct (pp_val_at W3 mem (cx_t cx) (cx_tb cx) (i + s11) Ct Hple) as [Vc Hcb].
set (cb := byte_at (cx_tb cx) (i + s11)) in *.
assert (Hp0 : rd_p0 cx i s11 = cx_t cx + Z.of_nat i + Z.of_nat s11) by reflexivity.
assert (Vc' : val_mem tfibsegs (mrestrict (w_H W3) mem) (cx_t cx + Z.of_nat i + Z.of_nat s11) 1 cb)
  by (replace (cx_t cx + Z.of_nat i + Z.of_nat s11) with (cx_t cx + Z.of_nat (i + s11)) by lia; exact Vc).
assert (Hs11z : 0 <= Z.of_nat s11 <= 7) by (destruct Hs11 as [-> | ->]; lia).
pose proof (pp_entry_P RD_P W3 regs mem (cx_F cx) (cx_u cx - 2) (Z.of_nat s11) (cx_t cx + Z.of_nat i) cb
  HFR R2 R27 HPN R21 R10 Hs11z ltac:(lia) ltac:(lia) Hcb Vc') as HS.
set (E := Ereg regs (pp_extra (cx_u cx - 2) cb (cx_t cx + Z.of_nat i + Z.of_nat s11))) in *.
assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs q)
  by (intros n q Hn; unfold E; apply ew_Ereg_nat; exact Hn).
pose proof (eq_trans (EE 9%nat 9%bv eq_refl) R9) as E9.
pose proof (eq_trans (EE 10%nat 10%bv eq_refl) R10) as E10.
pose proof (eq_trans (EE 21%nat 21%bv eq_refl) R21) as E21.
pose proof (eq_trans (EE 27%nat 27%bv eq_refl) R27) as E27.
assert (E33 : ew E 33 = w64 cb) by (unfold E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 (cx_t cx + Z.of_nat i + Z.of_nat s11)) by (unfold E; exact (ew_Ereg_extra regs _ 2)).
clear EE.
assert (HBx : U E PP_Bx = SHADOW_OFF) by exact (pp_U_Bx E E27).
assert (SHOK : sh_ok tfibsegs PP_Bx [] E
  (mrestrict (w_H W3) (ms_mem (mkst regs (Z_to_bv 64 RD_P) mem (seg_rom tfibsegs))))) by constructor.
change mem with (ms_mem (mkst regs (Z_to_bv 64 RD_P) mem (seg_rom tfibsegs))) in HJ.
unfold cfg_at. change (w64 RD_P) with (Z_to_bv 64 RD_P).
(* 0x82060 .. 0x8207c: s6 = p0, the check of s6, the byte c at s6, a2 = c - 9 *)
aj_run_tok rd_tbl_ok HS HJ SHOK PP_Bspan.
{ apply (pp_obl1 W3 _ E (SOff 34 0) (cx_t cx) (cx_tb cx) Ct HBx);
    rewrite (pp_U_off E 34%nat _ 0 E34); unfold zcanon, M64; rewrite Z.mod_small by lia; lia. }
{ awr_ok_tac. }
pp_fr Hm.
srr_branch_tok rd_tbl_ok HS SHOK PP_Bspan.
- (* not 9 .. 13: 0x82140 tests c against 32 *)
  pp_decb HS E33 cb Hc.
  aj_run_tok rd_tbl_ok HS HJ SHOK PP_Bspan.
  { awr_ok_tac. }
  pp_fr Hm2.
  srr_branch_tok rd_tbl_ok HS SHOK PP_Bspan.
  + (* and not 32: not a space, the declaration is DNone; CONT 0x81ffc *)
    pp_decb HS E33 cb Hc0.
    assert (Hnsp : is_space cb = false) by exact (pp_sp_no cb Hcb Hc Hc0).
    assert (Hdecl : decl (cx_tb cx) i = DNone).
    { rewrite (readings_scan.decl_some (cx_tb cx) i (i + s11)%nat Hh).
      exact (readings_scan.db_nsp (cx_tb cx) (i + s11)%nat Hnsp). }
    aj_run_tok rd_tbl_ok HS HJ SHOK PP_Bspan.
    { awr_ok_tac. }
    pp_fr Hm3.
    srr_branch_tok rd_tbl_ok HS SHOK PP_Bspan.
    * (* 0x8200c bne a0, s0 taken: back to RD_L at i + 1 *)
      aj_run_to_tok rd_tbl_ok HS HJ SHOK PP_Bspan RD_L.
      { awr_ok_tac. }
      pp_fr Hm4.
      pp_land HS HJ E regs HK.
      apply (pp_to_L B CTX f cx i d ly3 S3 W3 _ mem _ HL HB).
      -- apply (pp_loop_keep B cx d ly3 S3 W3 regs _ md); [exact HI | exact HJ | exact HK | ..]; pp_g HS.
      -- exact HA.
      -- exact Hi.
      -- exact Hdecl.
      -- pp_g HS.
    * (* 0x82010 j 0x823b4: a0 = at is not -1 *)
      pp_guard Hc1.
  + (* c = 32: a space; 0x82144 j 0x82080 *)
    pp_decb HS E33 cb Hc0.
    assert (Hsp : is_space cb = true) by exact (pp_sp_32 cb Hcb Hc Hc0).
    aj_run_to_tok rd_tbl_ok HS HJ SHOK PP_Bspan PP_SP.
    { awr_ok_tac. }
    pp_fr Hm3.
    pp_land HS HJ E regs HK.
    apply (pp_space_body f HW1 cx i d s11 ly3 S3 W3 _ mem _ HB).
    * apply (pp_loop_keep B cx d ly3 S3 W3 regs _ md); [exact HI | exact HJ | exact HK | ..]; pp_g HS.
    * exact HA.
    * exact Hi.
    * exact Hh.
    * exact Hs11.
    * exact Hsp.
    * pp_g HS.
    * pp_g HS.
    * pp_g HS.
- (* 9 .. 13: a space, the space body *)
  pp_decb HS E33 cb Hc.
  assert (Hsp : is_space cb = true) by exact (pp_sp_in cb Hcb Hc).
  aj_run_to_tok rd_tbl_ok HS HJ SHOK PP_Bspan PP_SP.
  { awr_ok_tac. }
  pp_fr Hm2.
  pp_land HS HJ E regs HK.
  apply (pp_space_body f HW1 cx i d s11 ly3 S3 W3 _ mem _ HB).
  + apply (pp_loop_keep B cx d ly3 S3 W3 regs _ md); [exact HI | exact HJ | exact HK | ..]; pp_g HS.
  + exact HA.
  + exact Hi.
  + exact Hh.
  + exact Hs11.
  + exact Hsp.
  + pp_g HS.
  + pp_g HS.
  + pp_g HS.
Qed.

End c.
