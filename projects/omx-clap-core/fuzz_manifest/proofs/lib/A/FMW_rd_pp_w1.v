(* lv2_locate_manifest_readings, segment PP, piece W1: the first inner loop at PP_L1 (0x81df0, lv2_locate.c:116,
   `while (isspace (p[0])) p++`) from pp_at_L1 to the second loop's head PP_L2 (0x81e44): pp_w1_holds.
   One iteration: the inline shadow check of a1 = p0 + k (81df0..81dfc), `lbu a2, 0(s6)` (the byte c at p0 + k),
   `addi a3, a2, -9; bgeu a3, s2 (= 5)` (81e04/81e08) and `bne a2, s1 (= 32)` (81e28) decide ManifestModel.is_space c.
   A space: 81e0c..81e24 (s6, a1, s10 += 1; s4, s9, s5 -= 1) and back to L1 at k + 1. Not a space: 81e3c..81e40
   (s7 = 0, a3 = s6) reach L2 with p1 = i + s11 + k (the count of spaces is k) and no name byte consumed.
   The loop by strong induction on |text| - (i + s11 + k), after G4's FMW_ex_decl_d1.v (d1_loop with lt_wf_ind,
   d1_back, d1_exit); the run / branch / register-readback idiom after FMW_rd_pp.v (pp_p_body). *)
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

(* ---- pure facts ---- *)
(* one more space at p + k: the count of spaces from p is past k (after FMW_ex_decl_d1.v's use of dm_cw_next) *)
Lemma w1_cw_next : forall l p k, (k <= count_while is_space (skipn p l))%nat ->
  is_space (byte_at l (p + k)) = true -> (S k <= count_while is_space (skipn p l))%nat.
Proof.
intros l p k Hk Hs. rewrite (pp_cw_shift is_space l p k Hk).
destruct (Nat.lt_ge_cases (p + k) (length l)) as [H|H].
- rewrite (readings_scan.cw_step is_space l (p + k) H). rewrite Hs. cbv beta iota. lia.
- rewrite (readings_scan.byte_at_past l (p + k) H) in Hs. vm_compute in Hs. discriminate Hs.
Qed.

(* two words with the same value mod 2^64 *)
Lemma w1_w64_mod : forall x y, x mod 2 ^ 64 = y mod 2 ^ 64 -> w64 x = w64 y.
Proof.
intros x y H. apply bv_eq. unfold w64. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
replace (bv_modulus 64) with (2 ^ 64) by reflexivity. exact H.
Qed.
Lemma w1_mod_shift : forall x y, x = y + 2 ^ 64 -> x mod 2 ^ 64 = y mod 2 ^ 64.
Proof.
intros x y ->. rewrite <- (Z_mod_plus_full y 1 (2 ^ 64)). f_equal; lia.
Qed.

(* a register of the run's end state: its symbolic value (an entry atom plus a literal, or a literal), then the
   entry value of that atom from the hypothesis `ew _ n = w64 _` about the entry env, then arithmetic *)
Ltac w1_rg HS :=
  lazymatch goal with |- getr _ ?r = _ =>
    lazymatch type of HS with st_ok ?segs ?Ev ?ss (restrict ?H ?ms) =>
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in
      rewrite (st_ok_restrict_reg segs H Ev ss ms r HS); change (sr_get (ss_regs ss) r) with e
    end end;
  lazymatch goal with
  | |- sv_denot ?Ev (SOff ?n ?c) = _ =>
      match goal with Hn : ew _ n = w64 ?z |- _ =>
        let Hl := fresh "Hl" in
        assert (Hl : ew Ev n = w64 z) by (cbn [ew ewset extK Nat.eqb]; exact Hn);
        rewrite (pp_reg_off Ev n z c Hl); clear Hl
      end;
      first [ unfold w64; f_equal; lia | apply w1_w64_mod, w1_mod_shift; lia ]
  | |- sv_denot _ (SLit _) = _ => cbn [sv_denot]; reflexivity
  end.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable CTX : list (list Z).

(* ---- the back edge: a space at p0 + k, L1 at k + 1 (after FMW_ex_decl_d1.v d1_back) ---- *)
Lemma w1_back : forall cx i d f s11 k ly3 S3 W3 regs mem md regs4 md4,
  pp_at_L1 B cx i d f s11 k ly3 S3 W3 regs mem md ->
  is_space (byte_at (cx_tb cx) (i + s11 + k)) = true ->
  ajournal tfibsegs B (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx)
    (cx_md cx) [] ly3 S3 W3 mem md4 EV_names ->
  (forall r, In r PP_KEPT -> getr regs4 r = getr regs r) ->
  getr regs4 9 = w64 32 -> getr regs4 18 = w64 5 ->
  getr regs4 19 = w64 58 -> getr regs4 24 = w64 (cx_t cx + Z.of_nat i) -> getr regs4 27 = w64 (Z.of_nat s11) ->
  getr regs4 10 = w64 (rd_p0 cx i s11) ->
  getr regs4 11 = w64 (rd_p0 cx i s11 + Z.of_nat (S k)) ->
  getr regs4 16 = w64 (- rd_p0 cx i s11) ->
  getr regs4 20 = w64 (cx_u cx - 3 - rd_p0 cx i s11 - Z.of_nat (S k)) ->
  getr regs4 21 = w64 (cx_u cx - 2 - Z.of_nat s11 - (cx_t cx + Z.of_nat i) - Z.of_nat (S k)) ->
  getr regs4 22 = w64 (rd_p0 cx i s11 + Z.of_nat (S k)) ->
  getr regs4 25 = w64 (cx_u cx - 2 - rd_p0 cx i s11 - Z.of_nat (S k)) ->
  getr regs4 26 = w64 (Z.of_nat (S k)) ->
  pp_at_L1 B cx i d f s11 (S k) ly3 S3 W3 regs4 mem md4.
Proof.
intros cx i d f s11 k ly3 S3 W3 regs mem md regs4 md4
  ((HI & HA & Hi & Hh & Hs11 & Hsp0 & _ & _ & _) & Hk & _) Hsp HJ HK K9 K18 K19 K24 K27
  K10 K11 K16 K20 K21 K22 K25 K26.
unfold pp_at_L1, pp_head. cbv zeta.
split; [split|].
- exact (pp_loop_keep B cx d ly3 S3 W3 regs mem md regs4 md4 HI HJ HK K9 K18).
- split; [exact HA|]. split; [exact Hi|]. split; [exact Hh|]. split; [exact Hs11|]. split; [exact Hsp0|].
  split; [exact K19|]. split; [exact K24 | exact K27].
- split; [exact (w1_cw_next (cx_tb cx) (i + s11) k Hk Hsp)|].
  split; [exact K10|]. split; [exact K11|]. split; [exact K16|]. split; [exact K20|]. split; [exact K21|].
  split; [exact K22|]. split; [exact K25 | exact K26].
Qed.

(* ---- the exit: not a space at p0 + k, L2 with p1 = i + s11 + k and no name byte yet (after d1_exit) ---- *)
Lemma w1_exit : forall cx i d f s11 k ly3 S3 W3 regs mem md regs4 md4,
  pp_at_L1 B cx i d f s11 k ly3 S3 W3 regs mem md ->
  is_space (byte_at (cx_tb cx) (i + s11 + k)) = false ->
  ajournal tfibsegs B (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx)
    (cx_md cx) [] ly3 S3 W3 mem md4 EV_names ->
  (forall r, In r PP_KEPT -> getr regs4 r = getr regs r) ->
  getr regs4 9 = w64 32 -> getr regs4 18 = w64 5 ->
  getr regs4 19 = w64 58 -> getr regs4 24 = w64 (cx_t cx + Z.of_nat i) -> getr regs4 27 = w64 (Z.of_nat s11) ->
  getr regs4 10 = w64 (rd_p0 cx i s11) ->
  getr regs4 11 = w64 (rd_p0 cx i s11 + Z.of_nat k) ->
  getr regs4 12 = w64 (byte_at (cx_tb cx) (i + s11 + k)) ->
  getr regs4 13 = w64 (rd_p0 cx i s11 + Z.of_nat k) ->
  getr regs4 16 = w64 (- rd_p0 cx i s11) ->
  getr regs4 20 = w64 (cx_u cx - 3 - rd_p0 cx i s11 - Z.of_nat k) ->
  getr regs4 21 = w64 (cx_u cx - 2 - Z.of_nat s11 - (cx_t cx + Z.of_nat i) - Z.of_nat k) ->
  getr regs4 22 = w64 (rd_p0 cx i s11 + Z.of_nat k) ->
  getr regs4 23 = w64 0 ->
  getr regs4 25 = w64 (cx_u cx - 2 - rd_p0 cx i s11 - Z.of_nat k) ->
  getr regs4 26 = w64 (Z.of_nat k) ->
  pp_at_L2 B cx i d f s11 (i + s11 + k) 0 ly3 S3 W3 regs4 mem md4.
Proof.
intros cx i d f s11 k ly3 S3 W3 regs mem md regs4 md4
  ((HI & HA & Hi & Hh & Hs11 & Hsp0 & _ & _ & _) & Hk & _) Hns HJ HK K9 K18 K19 K24 K27
  K10 K11 K12 K13 K16 K20 K21 K22 K23 K25 K26.
assert (Hp0 : rd_p0 cx i s11 = cx_t cx + Z.of_nat i + Z.of_nat s11) by reflexivity.
unfold pp_at_L2, pp_head, pp_s10_L2. cbv zeta.
split; [split|].
- exact (pp_loop_keep B cx d ly3 S3 W3 regs mem md regs4 md4 HI HJ HK K9 K18).
- split; [exact HA|]. split; [exact Hi|]. split; [exact Hh|]. split; [exact Hs11|]. split; [exact Hsp0|].
  split; [exact K19|]. split; [exact K24 | exact K27].
- split; [rewrite (pp_cw_exact is_space (cx_tb cx) (i + s11) k Hk Hns); reflexivity|].
  split; [lia|].
  split; [exact K10|].
  split; [rewrite K11; unfold w64; f_equal; lia|].
  split; [rewrite Nat.add_0_r; exact K12|].
  split; [rewrite K13; unfold w64; f_equal; lia|].
  split; [exact K16|].
  split; [rewrite K20; unfold w64; f_equal; lia|].
  split; [rewrite K21; unfold w64; f_equal; lia|].
  split; [rewrite K22; unfold w64; f_equal; lia|].
  split; [exact K23|].
  split; [rewrite K25; unfold w64; f_equal; lia | rewrite K26; unfold w64; f_equal; lia].
Qed.

(* ---- the loop: one iteration from pp_at_L1, re-entry by strong induction on |text| - (i + s11 + k) ---- *)
Lemma w1_loop : forall f, pp_seg_W2 B CTX f ->
  forall r cx i d s11 k ly3 S3 W3 regs mem md,
  r = (length (cx_tb cx) - (i + s11 + k))%nat ->
  rd_base B CTX cx -> pp_at_L1 B cx i d (S f) s11 k ly3 S3 W3 regs mem md ->
  SRr tfibsegs W3 (cfg_at tfibsegs PP_L1 regs mem md) (rd_post B cx).
Proof.
intros f HW2 r. induction r as [r IH] using lt_wf_ind.
intros cx i d s11 k ly3 S3 W3 regs mem md Hr HB HP.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof g3_wx as Hwx. pose proof g3_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HP as ((HI & HA & Hi & Hh & Hs11 & Hsp0 & R19 & R24 & R27) & Hk & R10 & R11 & R16 & R20 & R21 & R22
  & R25 & R26).
pose proof (pp_facts_of B CTX cx d ly3 S3 W3 regs mem md HB HI) as
  (HFR & R2 & R8 & R9 & R18 & Ct & Cu & Ht4 & Htc & Hu4 & Huc & HWR & HJ).
pose proof (pp_head_le (cx_tb cx) i _ Hh) as Hple.
pose proof (pp_cw_le is_space (cx_tb cx) (i + s11)) as Hcwle.
assert (Hq : (i + s11 + k <= length (cx_tb cx))%nat) by lia.
destruct (pp_val_at W3 mem (cx_t cx) (cx_tb cx) (i + s11 + k) Ct Hq) as [Vc Hcb].
set (c := byte_at (cx_tb cx) (i + s11 + k)) in *.
assert (Hcdef : c = byte_at (cx_tb cx) (i + s11 + k)) by reflexivity.
assert (Hp0 : rd_p0 cx i s11 = cx_t cx + Z.of_nat i + Z.of_nat s11) by reflexivity.
assert (Vc' : val_mem tfibsegs (mrestrict (w_H W3) mem) (rd_p0 cx i s11 + Z.of_nat k) 1 c)
  by (replace (rd_p0 cx i s11 + Z.of_nat k) with (cx_t cx + Z.of_nat (i + s11 + k)) by lia; exact Vc).
assert (Hpk : 4096 <= rd_p0 cx i s11 + Z.of_nat k) by lia.
assert (Hpkc : rd_p0 cx i s11 + Z.of_nat k + 1 <= alloc_ceiling) by lia.
pose proof (pp_entry_L1 W3 regs mem (cx_F cx) (cx_u cx - 2) (cx_u cx - 3) (rd_p0 cx i s11 + Z.of_nat k) c
  HFR R2 R8 R9 R18 R11 R22 Hpk Hpkc Hcb Vc') as HS.
set (E := Ereg regs (pp_extra (cx_u cx - 2) (cx_u cx - 3) c 0)) in *.
assert (E8 : ew E 8 = w64 SHADOW_OFF) by (unfold E; rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8).
assert (E10 : ew E 10 = w64 (rd_p0 cx i s11))
  by (unfold E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact R10).
assert (E11 : ew E 11 = w64 (rd_p0 cx i s11 + Z.of_nat k))
  by (unfold E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact R11).
assert (E16 : ew E 16 = w64 (- rd_p0 cx i s11))
  by (unfold E; rewrite (ew_Ereg_nat regs _ 16 16%bv eq_refl); exact R16).
assert (E19 : ew E 19 = w64 58) by (unfold E; rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact R19).
assert (E20 : ew E 20 = w64 (cx_u cx - 3 - rd_p0 cx i s11 - Z.of_nat k))
  by (unfold E; rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact R20).
assert (E21 : ew E 21 = w64 (cx_u cx - 2 - Z.of_nat s11 - (cx_t cx + Z.of_nat i) - Z.of_nat k))
  by (unfold E; rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact R21).
assert (E22 : ew E 22 = w64 (rd_p0 cx i s11 + Z.of_nat k))
  by (unfold E; rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact R22).
assert (E24 : ew E 24 = w64 (cx_t cx + Z.of_nat i))
  by (unfold E; rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact R24).
assert (E25 : ew E 25 = w64 (cx_u cx - 2 - rd_p0 cx i s11 - Z.of_nat k))
  by (unfold E; rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact R25).
assert (E26 : ew E 26 = w64 (Z.of_nat k))
  by (unfold E; rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact R26).
assert (E27 : ew E 27 = w64 (Z.of_nat s11))
  by (unfold E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact R27).
assert (E34 : ew E 34 = w64 c) by (unfold E; exact (ew_Ereg_extra regs _ 2)).
assert (HBx : U E PP_Bx = SHADOW_OFF) by exact (pp_U_Bx E E8).
assert (SHOK : sh_ok tfibsegs PP_Bx [] E
  (mrestrict (w_H W3) (ms_mem (mkst regs (Z_to_bv 64 PP_L1) mem (seg_rom tfibsegs))))) by constructor.
change mem with (ms_mem (mkst regs (Z_to_bv 64 PP_L1) mem (seg_rom tfibsegs))) in HJ.
unfold cfg_at. change (w64 PP_L1) with (Z_to_bv 64 PP_L1).
(* 81df0..81e08: the shadow check of a1 = p0 + k, the byte c at s6 = p0 + k, a3 = c - 9 *)
aj_run_tok rd_tbl_ok HS HJ SHOK PP_Bspan.
{ apply (pp_obl1 W3 _ E (SOff 11 0) (cx_t cx) (cx_tb cx) Ct HBx);
    rewrite (pp_U_off E 11%nat (rd_p0 cx i s11 + Z.of_nat k) 0 E11); unfold zcanon, M64;
    rewrite Z.mod_small by lia; lia. }
{ awr_ok_tac. }
lazymatch type of HF with frame_of _ ?rs _ _ =>
  pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as Hm end.
cbn [ms_mem] in Hm.
srr_branch_tok rd_tbl_ok HS SHOK PP_Bspan.
- (* bgeu taken: c is not 9 .. 13; 81e28 tests c against 32 *)
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
    assert (H34 : ew Ev 34 = Z_to_bv 64 c) by (cbn [ew ewset extK Nat.eqb]; exact E34) end.
  erewrite (pp_Db_of _ c _ _ _ H34) in Hc by reflexivity. clear H34.
  aj_run_to_tok rd_tbl_ok HS HJ SHOK PP_Bspan 0x81e28.
  { awr_ok_tac. }
  lazymatch type of HF0 with frame_of _ ?rs _ _ =>
    pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF0) as Hm2 end.
  cbn [ms_mem] in Hm2.
  srr_branch_tok rd_tbl_ok HS SHOK PP_Bspan.
  + (* bne taken: c is not 32, not a space; 81e3c..81e40 reach L2 *)
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
      assert (H34b : ew Ev 34 = Z_to_bv 64 c) by (cbn [ew ewset extK Nat.eqb]; exact E34) end.
    erewrite (pp_Db_of _ c _ _ _ H34b) in Hc0 by reflexivity. clear H34b.
    assert (Hns : is_space c = false) by exact (pp_sp_no c Hcb Hc Hc0).
    aj_run_to_tok rd_tbl_ok HS HJ SHOK PP_Bspan PP_L2.
    { awr_ok_tac. }
    lazymatch type of HF1 with frame_of _ ?rs _ _ =>
      pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF1) as Hm3 end.
    cbn [ms_mem] in Hm3.
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
      pose proof (g3_regs_of_st_ok tfibsegs Ev _ _ regs _ PP_KEPT HS ltac:(env_agree_chain (env_agree_refl 32 E))
        ltac:(vm_compute; reflexivity)) as HK end.
    cbn [ms_regs restrict] in HK.
    rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl).
    lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?x)] =>
      let v := eval vm_compute in (ss_pc x) in change (ss_pc x) with v end.
    rewrite Hm3, Hm2, Hm in HJ |- *.
    apply (HW2 cx i d s11 (i + s11 + k)%nat 0%nat ly3 S3 W3 _ _ _ HB).
    apply (w1_exit cx i d (S f) s11 k ly3 S3 W3 regs mem md _ _ HP Hns HJ HK); w1_rg HS.
  + (* c = 32: a space; 81e2c, 81e0c..81e24 back to L1 *)
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
      assert (H34b : ew Ev 34 = Z_to_bv 64 c) by (cbn [ew ewset extK Nat.eqb]; exact E34) end.
    erewrite (pp_Db_of _ c _ _ _ H34b) in Hc0 by reflexivity. clear H34b.
    assert (Hsp : is_space c = true) by exact (pp_sp_32 c Hcb Hc Hc0).
    pose proof (w1_cw_next (cx_tb cx) (i + s11) k Hk Hsp) as Hn.
    aj_run_to_tok rd_tbl_ok HS HJ SHOK PP_Bspan PP_L1.
    { awr_ok_tac. }
    lazymatch type of HF1 with frame_of _ ?rs _ _ =>
      pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF1) as Hm3 end.
    cbn [ms_mem] in Hm3.
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
      pose proof (g3_regs_of_st_ok tfibsegs Ev _ _ regs _ PP_KEPT HS ltac:(env_agree_chain (env_agree_refl 32 E))
        ltac:(vm_compute; reflexivity)) as HK end.
    cbn [ms_regs restrict] in HK.
    rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl).
    lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?x)] =>
      let v := eval vm_compute in (ss_pc x) in change (ss_pc x) with v end.
    rewrite Hm3, Hm2, Hm in HJ |- *.
    apply (IH (length (cx_tb cx) - (i + s11 + S k))%nat ltac:(lia) cx i d s11 (S k) ly3 S3 W3 _ _ _
      eq_refl HB).
    apply (w1_back cx i d (S f) s11 k ly3 S3 W3 regs mem md _ _ HP Hsp HJ HK); w1_rg HS.
- (* bgeu not taken: c is 9 .. 13, a space; 81e0c..81e24 back to L1 *)
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
    assert (H34 : ew Ev 34 = Z_to_bv 64 c) by (cbn [ew ewset extK Nat.eqb]; exact E34) end.
  erewrite (pp_Db_of _ c _ _ _ H34) in Hc by reflexivity. clear H34.
  assert (Hsp : is_space c = true) by exact (pp_sp_in c Hcb Hc).
  pose proof (w1_cw_next (cx_tb cx) (i + s11) k Hk Hsp) as Hn.
  aj_run_to_tok rd_tbl_ok HS HJ SHOK PP_Bspan PP_L1.
  { awr_ok_tac. }
  lazymatch type of HF0 with frame_of _ ?rs _ _ =>
    pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF0) as Hm2 end.
  cbn [ms_mem] in Hm2.
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
    pose proof (g3_regs_of_st_ok tfibsegs Ev _ _ regs _ PP_KEPT HS ltac:(env_agree_chain (env_agree_refl 32 E))
      ltac:(vm_compute; reflexivity)) as HK end.
  cbn [ms_regs restrict] in HK.
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl).
  lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?x)] =>
    let v := eval vm_compute in (ss_pc x) in change (ss_pc x) with v end.
  rewrite Hm2, Hm in HJ |- *.
  apply (IH (length (cx_tb cx) - (i + s11 + S k))%nat ltac:(lia) cx i d s11 (S k) ly3 S3 W3 _ _ _
    eq_refl HB).
  apply (w1_back cx i d (S f) s11 k ly3 S3 W3 regs mem md _ _ HP Hsp HJ HK); w1_rg HS.
Qed.

Theorem pp_w1_holds : forall f, pp_seg_W2 B CTX f -> pp_seg_W1 B CTX f.
Proof.
intros f HW2 cx i d s11 k ly3 S3 W3 regs mem md HB HP.
exact (w1_loop f HW2 _ cx i d s11 k ly3 S3 W3 regs mem md eq_refl HB HP).
Qed.

End c.
