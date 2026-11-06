(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMW_rd_pp_w2.v (a working branch e2e59892bef), re-walked
   for B's code (B-readings.lst 0x820ec .. 0x82150, CONT 0x81ffc .. 0x82010). *)
(* lv2_locate_manifest_readings on fm.asan-ubsan, segment PP, the second inner loop (lv2_locate.c:120, the name up to
   ':'): its head 0x820ec (FMW_rd_pp_cuts.v pp_at_L2) with m name bytes consumed after p1, a2 = the byte c at
   s8 = p1 + m.  `zext.b a2; bltu s7, a2` (c > ':' is a name byte); else bit c of s4 = RD_MASK1 (NUL or a space: the
   declaration is DNone, CONT 0x81ffc, its guard 0x8200c refuted by a0 = at, FMTrapB K1n); else `beq a2, s7` (':' ends
   the name: the cut L3E 0x82150); else a name byte.  A name byte: the guard 0x82104 `beq s8, s0` (decided not taken
   by the token engine from pp_entry_L2's fact 4096 <= s8 <= 2^47 - 16, atom 24), the shadow check of a0 = p1 + m + 1,
   s8 += 1, a2 = the next byte, a1 -= 1, a0 += 1, s9, s10 -= 1, back to the head at m + 1 (strong induction). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMTrapB FMW_rd_pp_cuts FMW_rd_pp.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import ManifestModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require readings_scan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* U of an atom-plus-offset in the goal, from the facts `ew _ n = w64 z` about the entry env *)
Ltac w2_Uat :=
  repeat match goal with |- context [U ?Ev (SOff ?n ?c)] =>
    match goal with H : ew _ n = w64 ?z |- _ =>
      let Hl := fresh "Hl" in
      assert (Hl : ew Ev n = w64 z) by (cbn [ew ewset extK Nat.eqb]; exact H);
      rewrite (pp_U_off Ev n z c Hl); clear Hl end end.
(* the inline check of the next name byte, a0 = text + p1 + m + 1, is a byte of the text *)
Ltac w2_obl W3 Ct :=
  repeat match goal with H : ms_mem _ = _ |- _ => rewrite H end;
  lazymatch goal with |- range_addressable _ (U ?Ev _) (U ?Ev ?v) _ =>
    let F27 := fresh "F27" in
    match goal with H : ew _ 27 = w64 SHADOW_OFF |- _ =>
      assert (F27 : ew Ev 27 = w64 SHADOW_OFF) by (cbn [ew ewset extK Nat.eqb]; exact H) end;
    apply (pp_obl1 W3 _ Ev v _ _ Ct (pp_U_Bx Ev F27)); w2_Uat; unfold zcanon, M64;
    rewrite Z.mod_small by lia; lia
  end.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable CTX : list (list Z).

Lemma w2_loop : forall f, rd_seg_L B CTX f -> pp_seg_L3E B CTX f ->
  forall r cx i d s11 p1 m ly3 S3 W3 regs mem md,
  (length (cx_tb cx) - (p1 + m) = r)%nat -> rd_base B CTX cx ->
  pp_at_L2 B cx i d (S f) s11 p1 m ly3 S3 W3 regs mem md ->
  SRr tfibsegs W3 (cfg_at tfibsegs PP_L2 regs mem md) (rd_post B cx).
Proof.
intros f HL HL3E r. induction r as [r IH] using lt_wf_ind.
intros cx i d s11 p1 m ly3 S3 W3 regs mem md Hr HB HA2.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof g3_wx as Hwx. pose proof g3_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HA2 as ((HI & HA & Hi & Hh & Hs11 & Hsp & R21) & Ep1 & Hk & R10 & R11 & R12 & R22 & R24 & R25 & R26).
pose proof (pp_facts_of B CTX cx d ly3 S3 W3 regs mem md HB HI) as
  ((V58 & Hu2 & HFc & HF2 & HF16) & R2 & R27 & HPN & R9 & Ct & Cu & Ht4 & Htc & Hu4 & Huc & HWR & HJ).
assert (Hple : (i + s11 <= length (cx_tb cx))%nat) by exact (pp_head_le (cx_tb cx) i _ Hh).
pose proof (pp_cw_le is_space (cx_tb cx) (i + s11)) as Hcw1.
pose proof (pp_cw_le name_ok (cx_tb cx) p1) as Hcw2.
assert (Hpk : (p1 + m <= length (cx_tb cx))%nat) by lia.
assert (Hp0 : rd_p0 cx i s11 = cx_t cx + Z.of_nat i + Z.of_nat s11) by reflexivity.
destruct (pp_val_at W3 mem (cx_t cx) (cx_tb cx) (p1 + m) Ct Hpk) as [_ Hc255].
assert (Hcn : 0 <= byte_at (cx_tb cx) (p1 + S m) < 256).
{ destruct (Nat.le_gt_cases (p1 + S m) (length (cx_tb cx))) as [H|H].
  - exact (proj2 (pp_val_at W3 mem (cx_t cx) (cx_tb cx) (p1 + S m) Ct H)).
  - unfold byte_at. rewrite nth_overflow by lia. lia. }
set (c := byte_at (cx_tb cx) (p1 + m)) in *.
assert (Hcdef : c = byte_at (cx_tb cx) (p1 + m)) by reflexivity.
unfold cfg_at. change (w64 PP_L2) with (Z_to_bv 64 PP_L2).
change mem with (ms_mem (mkst regs (Z_to_bv 64 PP_L2) mem (seg_rom tfibsegs))) in HJ.
destruct (name_ok c) eqn:Hnm.
- (* a name byte: the next byte is in the text; back to L2 at m + 1 *)
  assert (Hlt : (p1 + m < length (cx_tb cx))%nat).
  { destruct (Nat.lt_ge_cases (p1 + m) (length (cx_tb cx))) as [H|H]; [exact H|]. exfalso.
    assert (E0 : c = 0) by (unfold c, byte_at; apply nth_overflow; exact H).
    rewrite E0 in Hnm. discriminate Hnm. }
  destruct (pp_val_at W3 mem (cx_t cx) (cx_tb cx) (p1 + S m) Ct ltac:(lia)) as [Vn _].
  assert (Vn' : val_mem tfibsegs (mrestrict (w_H W3) mem) (cx_t cx + Z.of_nat p1 + Z.of_nat m + 1) 1
                  (byte_at (cx_tb cx) (p1 + S m)))
    by (replace (cx_t cx + Z.of_nat p1 + Z.of_nat m + 1) with (cx_t cx + Z.of_nat (p1 + S m)) by lia; exact Vn).
  pose proof (pp_entry_L2 W3 regs mem (cx_F cx) c (cx_t cx + Z.of_nat p1 + Z.of_nat m + 1)
    (cx_t cx + Z.of_nat p1 + Z.of_nat m) (byte_at (cx_tb cx) (p1 + S m))
    R2 R27 HPN HFc HF2 HF16 R12 R10 R24 Hc255 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hcn Vn') as HS.
  set (E := Ereg regs (pp_extra 0 (byte_at (cx_tb cx) (p1 + S m)) 0)) in *.
  assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs q)
    by (intros n q Hn; unfold E; apply ew_Ereg_nat; exact Hn).
  pose proof (eq_trans (EE 9%nat 9%bv eq_refl) R9) as E9.
  pose proof (eq_trans (EE 10%nat 10%bv eq_refl) R10) as E10.
  pose proof (eq_trans (EE 11%nat 11%bv eq_refl) R11) as E11.
  pose proof (eq_trans (EE 12%nat 12%bv eq_refl) R12) as E12.
  pose proof (eq_trans (EE 21%nat 21%bv eq_refl) R21) as E21.
  pose proof (eq_trans (EE 22%nat 22%bv eq_refl) R22) as E22.
  pose proof (eq_trans (EE 24%nat 24%bv eq_refl) R24) as E24.
  pose proof (eq_trans (EE 25%nat 25%bv eq_refl) R25) as E25.
  pose proof (eq_trans (EE 26%nat 26%bv eq_refl) R26) as E26.
  pose proof (eq_trans (EE 27%nat 27%bv eq_refl) R27) as E27.
  assert (E33 : ew E 33 = w64 (byte_at (cx_tb cx) (p1 + S m))) by (unfold E; exact (ew_Ereg_extra regs _ 1)).
  clear EE.
  assert (SHOK : sh_ok tfibsegs PP_Bx [] E
    (mrestrict (w_H W3) (ms_mem (mkst regs (Z_to_bv 64 PP_L2) mem (seg_rom tfibsegs))))) by constructor.
  aj_run_tok rd_tbl_ok HS HJ SHOK PP_Bspan.
  { awr_ok_tac. }
  pp_fr Hm1.
  srr_branch_tok rd_tbl_ok HS SHOK PP_Bspan.
  + (* c > ':': the guard 0x82104, the check of a0, the next byte, back to the head *)
    pp_decn HS E12 c Hc. clear Hc.
    aj_run_to_tok rd_tbl_ok HS HJ SHOK PP_Bspan PP_L2.
    { w2_obl W3 Ct. }
    { awr_ok_tac. }
    pp_fr Hm2.
    pp_land HS HJ E regs HK.
    eapply (IH (length (cx_tb cx) - (p1 + S m))%nat ltac:(lia) cx i d s11 p1 (S m) ly3 S3 W3 _ _ _ eq_refl HB).
    unfold pp_at_L2, pp_head, pp_cd, pp_s10_L2.
    split; [split|].
    * apply (pp_loop_keep B cx d ly3 S3 W3 regs _ md); [exact HI | exact HJ | exact HK | ..]; pp_g HS.
    * split; [exact HA|]. split; [exact Hi|]. split; [exact Hh|]. split; [exact Hs11|]. split; [exact Hsp|].
      pp_g HS.
    * split; [exact Ep1|]. split; [exact (pp_cw_next name_ok (cx_tb cx) p1 m Hk Hnm Hlt)|].
      do 6 (split; [pp_g HS|]). pp_g HS.
  + pp_decn HS E12 c Hc. rename Hc into D1.
    aj_run_tok rd_tbl_ok HS HJ SHOK PP_Bspan.
    { awr_ok_tac. }
    pp_fr Hm2.
    srr_branch_tok rd_tbl_ok HS SHOK PP_Bspan.
    * pp_decn HS E12 c Hc. exfalso. destruct (pp_nm_mk c Hc255 D1 Hc) as [X _]. rewrite Hnm in X. discriminate X.
    * pp_decn HS E12 c Hc. rename Hc into D2.
      aj_run_tok rd_tbl_ok HS HJ SHOK PP_Bspan.
      { awr_ok_tac. }
      pp_fr Hm3.
      srr_branch_tok rd_tbl_ok HS SHOK PP_Bspan.
      -- pp_decn HS E12 c Hc. exfalso. pose proof (pp_nm_eq c Hc255 D1 D2 Hc) as E58.
         rewrite E58 in Hnm. discriminate Hnm.
      -- (* a name byte at or below ':' that is neither NUL nor a space: the guard, the check, back *)
         pp_decn HS E12 c Hc. clear Hc.
         aj_run_to_tok rd_tbl_ok HS HJ SHOK PP_Bspan PP_L2.
         { w2_obl W3 Ct. }
         { awr_ok_tac. }
         pp_fr Hm4.
         pp_land HS HJ E regs HK.
         eapply (IH (length (cx_tb cx) - (p1 + S m))%nat ltac:(lia) cx i d s11 p1 (S m) ly3 S3 W3 _ _ _ eq_refl HB).
         unfold pp_at_L2, pp_head, pp_cd, pp_s10_L2.
         split; [split|].
         ++ apply (pp_loop_keep B cx d ly3 S3 W3 regs _ md); [exact HI | exact HJ | exact HK | ..]; pp_g HS.
         ++ split; [exact HA|]. split; [exact Hi|]. split; [exact Hh|]. split; [exact Hs11|]. split; [exact Hsp|].
            pp_g HS.
         ++ split; [exact Ep1|]. split; [exact (pp_cw_next name_ok (cx_tb cx) p1 m Hk Hnm Hlt)|].
            do 6 (split; [pp_g HS|]). pp_g HS.
- (* not a name byte: the name ends at p2 = p1 + m *)
  assert (Hcw : count_while name_ok (skipn p1 (cx_tb cx)) = m) by exact (pp_cw_exact name_ok (cx_tb cx) p1 m Hk Hnm).
  pose proof (pp_entry_L2x W3 regs mem (cx_F cx) c (cx_t cx + Z.of_nat p1 + Z.of_nat m + 1)
    (cx_t cx + Z.of_nat p1 + Z.of_nat m)
    R2 R27 HPN HFc HF2 HF16 R12 R10 R24 Hc255 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
  set (E := Ereg regs (pp_extra 0 0 0)) in *.
  assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs q)
    by (intros n q Hn; unfold E; apply ew_Ereg_nat; exact Hn).
  pose proof (eq_trans (EE 9%nat 9%bv eq_refl) R9) as E9.
  pose proof (eq_trans (EE 10%nat 10%bv eq_refl) R10) as E10.
  pose proof (eq_trans (EE 11%nat 11%bv eq_refl) R11) as E11.
  pose proof (eq_trans (EE 12%nat 12%bv eq_refl) R12) as E12.
  pose proof (eq_trans (EE 21%nat 21%bv eq_refl) R21) as E21.
  pose proof (eq_trans (EE 22%nat 22%bv eq_refl) R22) as E22.
  pose proof (eq_trans (EE 24%nat 24%bv eq_refl) R24) as E24.
  pose proof (eq_trans (EE 25%nat 25%bv eq_refl) R25) as E25.
  pose proof (eq_trans (EE 26%nat 26%bv eq_refl) R26) as E26.
  pose proof (eq_trans (EE 27%nat 27%bv eq_refl) R27) as E27.
  clear EE.
  assert (SHOK : sh_ok tfibsegs PP_Bx [] E
    (mrestrict (w_H W3) (ms_mem (mkst regs (Z_to_bv 64 PP_L2) mem (seg_rom tfibsegs))))) by constructor.
  aj_run_tok rd_tbl_ok HS HJ SHOK PP_Bspan.
  { awr_ok_tac. }
  pp_fr Hm1.
  srr_branch_tok rd_tbl_ok HS SHOK PP_Bspan.
  + pp_decn HS E12 c Hc. exfalso. pose proof (pp_nm_gt c Hc255 Hc) as X. rewrite Hnm in X. discriminate X.
  + pp_decn HS E12 c Hc. rename Hc into D1.
    aj_run_tok rd_tbl_ok HS HJ SHOK PP_Bspan.
    { awr_ok_tac. }
    pp_fr Hm2.
    srr_branch_tok rd_tbl_ok HS SHOK PP_Bspan.
    * (* NUL or a space (bit c of RD_MASK1): CONT 0x81ffc, the declaration is DNone, the scan goes on at i + 1 *)
      pp_decn HS E12 c Hc. destruct (pp_nm_mk c Hc255 D1 Hc) as [_ Hc58]. clear Hc.
      assert (Hdecl : decl (cx_tb cx) i = DNone).
      { rewrite (readings_scan.decl_some (cx_tb cx) i (i + s11)%nat Hh).
        apply (readings_scan.db_ncolon (cx_tb cx) (i + s11)%nat p1 (p1 + m)%nat Hsp Ep1);
          [rewrite Hcw; reflexivity | exact Hc58]. }
      aj_run_tok rd_tbl_ok HS HJ SHOK PP_Bspan.
      { awr_ok_tac. }
      pp_fr Hm3.
      srr_branch_tok rd_tbl_ok HS SHOK PP_Bspan.
      -- (* 0x8200c bne a0, s0 taken: RD_L at i + 1 *)
         aj_run_to_tok rd_tbl_ok HS HJ SHOK PP_Bspan RD_L.
         { awr_ok_tac. }
         pp_fr Hm4.
         pp_land HS HJ E regs HK.
         apply (pp_to_L B CTX f cx i d ly3 S3 W3 _ mem _ HL HB).
         ++ apply (pp_loop_keep B cx d ly3 S3 W3 regs _ md); [exact HI | exact HJ | exact HK | ..]; pp_g HS.
         ++ exact HA.
         ++ exact Hi.
         ++ exact Hdecl.
         ++ pp_g HS.
      -- (* 0x82010 j 0x823b4: a0 = at is not -1 *)
         pp_guard Hc.
    * pp_decn HS E12 c Hc. rename Hc into D2.
      aj_run_tok rd_tbl_ok HS HJ SHOK PP_Bspan.
      { awr_ok_tac. }
      pp_fr Hm3.
      srr_branch_tok rd_tbl_ok HS SHOK PP_Bspan.
      -- (* ':' : the cut L3E 0x82150 with p2 = p1 + m *)
         pp_decn HS E12 c Hc. pose proof (pp_nm_eq c Hc255 D1 D2 Hc) as E58. clear Hc.
         aj_run_to_tok rd_tbl_ok HS HJ SHOK PP_Bspan PP_L3E.
         { awr_ok_tac. }
         pp_fr Hm4.
         pp_land HS HJ E regs HK.
         apply (HL3E cx i d s11 p1 (p1 + m)%nat ly3 S3 W3 _ _ _ HB).
         unfold pp_at_L3E, pp_head, pp_cd.
         split; [split|].
         ++ apply (pp_loop_keep B cx d ly3 S3 W3 regs _ md); [exact HI | exact HJ | exact HK | ..]; pp_g HS.
         ++ split; [exact HA|]. split; [exact Hi|]. split; [exact Hh|]. split; [exact Hs11|]. split; [exact Hsp|].
            pp_g HS.
         ++ split; [exact Ep1|]. split; [rewrite Hcw; reflexivity|]. split; [exact E58|].
            do 4 (split; [pp_g HS|]). pp_g HS.
      -- pp_decn HS E12 c Hc. exfalso. destruct (pp_nm_ok c Hc255 D1 D2 Hc) as [X _]. rewrite Hnm in X.
         discriminate X.
Qed.

Theorem pp_w2_holds : forall f, rd_seg_L B CTX f -> pp_seg_L3E B CTX f -> pp_seg_W2 B CTX f.
Proof.
intros f HL HL3E cx i d s11 p1 m ly3 S3 W3 regs mem md HB HA2.
exact (w2_loop f HL HL3E _ cx i d s11 p1 m ly3 S3 W3 regs mem md eq_refl HB HA2).
Qed.

End c.
