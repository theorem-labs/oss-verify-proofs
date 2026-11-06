(* has_prefixed on fm.asan-ubsan (G2, image B), loop segment TAIL 0x82520..0x82538 (lv2_locate.c:74-75):
   at = strstr (at + 1, location). The UBSan pointer-overflow guard of `at + 1` (0x82520 `beq s5, s10` with s10 = -1;
   trap `unimp` 0x825a0; FM-B-TRAPS.md row 8, class K1 fmt_eq_not) is refuted on its trap arm by B5's
   FMTrapB.fm_kill_trap from at = t + a < 2^47; the call 0x8252c goes through the kit's hp_call_rt with musl strstr's
   contract (hp_strstr_ro, ASTRSTR a Section hypothesis) on the text suffix from at + 1; a NULL answer (0x82534 beqz)
   returns 0 through the epilogue 0x82564 (hp_fin_of_st, hp_ret), a hit at at + 1 + j jumps back to the loop head
   0x8246c (0x82538 j) with s5 the new occurrence (hp_st_move, FMW_hp_model.first_occ_mt). Proves the kit's
   seg_tail_ok (lib/B/FMW_hp_kit.v). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI04 YN3v YI08.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YA0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YC20 YI16 YI00 YM05 YG0q YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_g2rt FMW_hp_kit FMW_hp_model.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require FMTrapB.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel has_prefixed_model.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- reading the engine's terms back as Z ---- *)
Lemma tl_sv_denot_U : forall E e, sv_denot E e = Z_to_bv 64 (U E e).
Proof. intros E e. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma tl_mod_small_eq : forall x y, x = y -> 0 <= y < 2 ^ 64 -> x mod 2 ^ 64 = y.
Proof. intros x y -> Hy. apply Z.mod_small. exact Hy. Qed.

Ltac tl_umod := repeat first [ rewrite U_add2 | rewrite U_mul2 | rewrite U_lit ].
Ltac tl_zmods := repeat first [ rewrite Zmult_mod_idemp_l | rewrite Zmult_mod_idemp_r
                              | rewrite Zplus_mod_idemp_l | rewrite Zplus_mod_idemp_r ].
(* getr of the register r after a run, as Z_to_bv 64 (U E e) *)
Ltac tl_rregU HS r Hr :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    assert (Hr : getr (ms_regs ms) r = Z_to_bv 64 (U E e))
      by (rewrite <- tl_sv_denot_U; exact (st_ok_restrict_reg segs H E ss ms r HS))
  end.
(* the pc of a state after a branch (add_cond ...) as a literal *)
Ltac tl_pcnorm := repeat lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?s)] =>
  let p := eval vm_compute in (ss_pc s) in change (ss_pc s) with p end.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Hypothesis HGOTS : as_got_shadow B = HP_GOT_shadow.
Hypothesis HCELL : as_shadow_cell B = HP_shadow_cell.
Hypothesis IMGF : fm_img_facts tfibsegs B.
Hypothesis ASTRSTR : astrstr_realizes tfibsegs B PC_strstr.

Lemma tl_keep_run : forall L E ss H ms regs0 extra,
  st_ok tfibsegs E ss (restrict H ms) -> env_agree 32 (Ereg regs0 extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) L = true ->
  regs_keep L regs0 (ms_regs ms).
Proof. intros L E ss H ms regs0 extra HS HA Hc. exact (regs_keep_of_st_ok L E ss (restrict H ms) regs0 extra HS HA Hc). Qed.

Lemma seg_tail : seg_tail_ok B.
Proof.
intros cx a KR KC lyc Sc W regs m mdc H _.
pose proof g2_segs_low as Hsegs. pose proof g2_wx as Hwx.
pose proof (hp_sp B cx a lyc Sc W regs m mdc H) as (Hsp1 & Hsp2 & Hspc).
pose proof (hp_cstr B IMGF cx a lyc Sc W regs m mdc H) as (Ht & Hl).
pose proof Ht as (_ & Ht4 & Htc & _).
pose proof Hl as (_ & Hl4 & Hlc & _).
pose proof H as (HE & HJ & Hab & Q3 & Q4 & Hsp & HF & HSL & Q8 & Q9 & Q19 & Q20 & Q21 & Q23 & Q24 & Q25 & Q26 & Q27
  & Hmt & Hgl).
pose proof HE as (_ & _ & _ & _ & _ & _ & _ & Hlb & _).
pose proof (has_prefixed_model.mt_len _ _ _ Hmt) as Halen.
assert (Hlbpos : (1 <= length (cx_lb cx))%nat) by (destruct (cx_lb cx); [contradiction | cbn; lia]).
assert (HSa : (S a <= length (cx_tb cx))%nat) by lia.
ceil2.
pose proof (hp_seat B IMGF cx a lyc Sc W regs m mdc HP_TAIL H) as HS.
set (E := Ereg regs [w64 (Z.of_nat (length (cx_lb cx))); w64 (cx_t cx + cx_q cx)]) in HS.
assert (HAE : env_agree 32 (Ereg regs [w64 (Z.of_nat (length (cx_lb cx))); w64 (cx_t cx + cx_q cx)]) E)
  by (split; [intros; reflexivity | reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (unfold E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (X8 : ew E 8 = Z_to_bv 64 (cx_lp cx)) by (unfold E; rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact Q8).
assert (X21 : ew E 21 = Z_to_bv 64 (cx_t cx + Z.of_nat a))
  by (unfold E; rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact Q21).
assert (X26 : ew E 26 = Z_to_bv 64 (-1)) by (unfold E; rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact Q26).
assert (U21 : U E (SOff 21 0) = cx_t cx + Z.of_nat a)
  by (rewrite (U_atom_mod E 21 0 _ X21); apply tl_mod_small_eq; lia).
assert (U26 : U E (SOff 26 0) = 2 ^ 64 - 1) by (rewrite (U_atom_mod E 26 0 _ X26); reflexivity).
unfold cfg_at. change (w64 HP_TAIL) with (Z_to_bv 64 HP_TAIL).
(* 0x82520: UBSan guard `beq s5, s10` (s10 = -1, trap 0x825a0; FM-B-TRAPS.md row 8, K1 fmt_eq_not): at = t + a < 2^47
   is not 2^64 - 1 *)
srr_branch_with tbl_hp_ok HS.
{ lazymatch goal with Hb : branch_taken _ _ _ = true |- _ => FMTrapB.fm_kill_trap Hb end. }
lazymatch goal with Hb : branch_taken _ _ _ = false |- _ => clear Hb end.
(* 0x82524..0x8252c: a0 = at + 1, a1 = location; jal strstr *)
aj_run tbl_hp_ok HS HJ.
{ awr_ok_tac. }
pose proof (gframe_of_frame tfibsegs W E _ 2 8 8 (spZ regs) (spZ (cx_regs0 cx) - STK_has_prefixed)
  (spZ (cx_regs0 cx) - 120) m _ HFr ltac:(vm_compute; reflexivity) Usp ltac:(rewrite hp_stk; lia) ltac:(lia)) as G1.
clear HF HFr HG.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?ms1) =>
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms1 HS eq_refl); cbn [ss_pc]; tl_pcnorm;
  pose proof (tl_keep_run HP_KEEP E _ _ ms1 regs _ HS HAE ltac:(vm_compute; reflexivity)) as K1;
  pose proof (tl_keep_run [21%bv] E _ _ ms1 regs _ HS HAE ltac:(vm_compute; reflexivity)) as K1b;
  tl_rregU HS (1%bv : bv 5) R1; tl_rregU HS (10%bv : bv 5) R10; tl_rregU HS (11%bv : bv 5) R11;
  set (regs1 := ms_regs ms1) in *; set (m1 := ms_mem ms1) in *
end.
pose proof (hp_st_keep B cx a lyc Sc W regs m mdc _ _ _ H HJ G1 K1 (K1b 21%bv (or_introl eq_refl))) as H1.
assert (V1 : getr regs1 1 = Z_to_bv 64 HP_TSR) by (rewrite R1; tl_umod; reflexivity).
assert (V10 : getr regs1 10 = w64 (cx_t cx + Z.of_nat (S a))).
{ rewrite R10. unfold w64. f_equal. tl_umod. rewrite ?(U_atom_mod E 21 _ _ X21). tl_zmods.
  apply tl_mod_small_eq; lia. }
assert (V11 : getr regs1 11 = w64 (cx_lp cx)).
{ rewrite R11. unfold w64. f_equal. tl_umod. rewrite ?(U_atom_mod E 8 _ _ X8). tl_zmods.
  apply tl_mod_small_eq; lia. }
clear R1 R10 R11 HS.
apply (hp_call_rt B cx a lyc Sc W regs1 m1 _ STK_RT_STRSTR PC_strstr HP_TSR
  (fun v => (v = 0 /\ no_occ (skipn (S a) (cx_tb cx)) (cx_lb cx)) \/
            (exists j, first_occ (skipn (S a) (cx_tb cx)) (cx_lb cx) j /\ v = cx_t cx + Z.of_nat (S a) + Z.of_nat j))
  H1).
- unfold STK_RT_STRSTR, ESTACK. lia.
- exact V1.
- unfold HP_TSR. lia.
- reflexivity.
- intros HPK.
  destruct (hp_rom B IMGF cx a lyc Sc W regs1 m1 _ H1) as (HN & HO).
  pose proof (hp_cstr B IMGF cx a lyc Sc W regs1 m1 _ H1) as (Ht1 & Hl1).
  exact (hp_strstr_ro B ASTRSTR lyc Sc W regs1 m1 _ _ _ _ _ HPK HN HO V10 V11
    (g2_cstr_suffix W m1 _ _ (S a) HSa Ht1) Hl1).
- (* strstr returned v: 0x82530 s5 = v; beqz v *)
  intros regs2 m2 md2 v H2 _ Ha0 Hv HR.
  pose proof (hp_seat B IMGF cx a lyc Sc W regs2 m2 md2 HP_TSR H2) as HS.
  pose proof H2 as (_ & HJ2 & _).
  set (E2 := Ereg regs2 [w64 (Z.of_nat (length (cx_lb cx))); w64 (cx_t cx + cx_q cx)]) in HS.
  assert (HAE2 : env_agree 32 (Ereg regs2 [w64 (Z.of_nat (length (cx_lb cx))); w64 (cx_t cx + cx_q cx)]) E2)
    by (split; [intros; reflexivity | reflexivity]).
  assert (Usp2 : bv_unsigned (ew E2 2) = spZ regs2)
    by (unfold E2; rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl); reflexivity).
  assert (Hsp2' : spZ regs2 = spZ (cx_regs0 cx) - 128) by (pose proof H2 as (_ & _ & _ & _ & _ & S2 & _); exact S2).
  assert (X10 : ew E2 10 = Z_to_bv 64 v) by (unfold E2; rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl); exact Ha0).
  assert (U10 : U E2 (SOff 10 0) = v) by exact (U_atom E2 10 v X10 Hv).
  unfold cfg_at. change (w64 HP_TSR) with (Z_to_bv 64 HP_TSR).
  aj_run tbl_hp_ok HS HJ2.
  { awr_ok_tac. }
  pose proof (gframe_of_frame tfibsegs W E2 _ 2 8 8 (spZ regs2) (spZ (cx_regs0 cx) - STK_has_prefixed)
    (spZ (cx_regs0 cx) - 120) m2 _ HFr ltac:(vm_compute; reflexivity) Usp2 ltac:(rewrite hp_stk; lia) ltac:(lia)) as G2.
  clear HF HFr HG.
  srr_branch_with tbl_hp_ok HS.
  + (* 0x82534 beqz taken, strstr returned NULL: no occurrence after at, return 0 through 0x82564 *)
    lazymatch goal with Hb : branch_taken _ _ _ = true |- _ =>
      rewrite branch_eq_U, U10, ?U_lit, ?Zmod_0_l in Hb; apply Z.eqb_eq in Hb; rename Hb into Hv0 end.
    assert (Hres : hp_res cx = 0).
    { destruct HR as [(_ & Hno) | (j & _ & Hj)]; [exact (KR Hno) | lia]. }
    aj_run_to tbl_hp_ok HS HJ2 A_hp_epi.
    { awr_ok_tac. }
    pose proof (gframe_of_frame tfibsegs W E2 _ 2 8 8 (spZ regs2) (spZ (cx_regs0 cx) - STK_has_prefixed)
      (spZ (cx_regs0 cx) - 120) _ _ HFr ltac:(vm_compute; reflexivity) Usp2 ltac:(rewrite hp_stk; lia) ltac:(lia)) as G3.
    clear HF HFr HG.
    lazymatch type of HS with st_ok _ _ _ (restrict _ ?ms3) =>
      rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E2 _ ms3 HS eq_refl); cbn [ss_pc]; tl_pcnorm;
      pose proof (tl_keep_run HP_KEEP E2 _ _ ms3 regs2 _ HS HAE2 ltac:(vm_compute; reflexivity)) as K3;
      pose proof (tl_keep_run [10%bv] E2 _ _ ms3 regs2 _ HS HAE2 ltac:(vm_compute; reflexivity)) as K3b;
      apply (hp_ret B HGOTS HCELL cx lyc Sc W (ms_regs ms3) (ms_mem ms3) _);
      [ apply (hp_fin_of_st B cx a lyc Sc W regs2 m2 md2 _ _ _ H2 HJ2 (gframe_seq tfibsegs W _ _ m2 _ _ G2 G3) K3)
      | rewrite (K3b 10%bv (or_introl eq_refl)), Ha0, Hres; f_equal; lia ]
    end.
  + (* a hit at at + 1 + j: back to the loop head with s5 = the new occurrence *)
    lazymatch goal with Hb : branch_taken _ _ _ = false |- _ =>
      rewrite branch_eq_U, U10, ?U_lit, ?Zmod_0_l in Hb; apply Z.eqb_neq in Hb; rename Hb into Hv0 end.
    destruct HR as [(Hz & _) | (j & Hfo & Hvj)]; [exfalso; lia|].
    aj_run_to tbl_hp_ok HS HJ2 HP_HEAD.
    { awr_ok_tac. }
    pose proof (gframe_of_frame tfibsegs W E2 _ 2 8 8 (spZ regs2) (spZ (cx_regs0 cx) - STK_has_prefixed)
      (spZ (cx_regs0 cx) - 120) _ _ HFr ltac:(vm_compute; reflexivity) Usp2 ltac:(rewrite hp_stk; lia) ltac:(lia)) as G3.
    clear HF HFr HG.
    lazymatch type of HS with st_ok _ _ _ (restrict _ ?ms3) =>
      rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E2 _ ms3 HS eq_refl); cbn [ss_pc]; tl_pcnorm;
      pose proof (tl_keep_run HP_KEEP E2 _ _ ms3 regs2 _ HS HAE2 ltac:(vm_compute; reflexivity)) as K3;
      tl_rregU HS (21%bv : bv 5) R21;
      apply (KC j Hfo lyc Sc W (ms_regs ms3) (ms_mem ms3) _);
      [ apply (hp_st_move B cx a (S a + j) lyc Sc W regs2 m2 md2 _ _ _ H2 HJ2
          (gframe_seq tfibsegs W _ _ m2 _ _ G2 G3) K3);
        [ rewrite R21, U10, Hvj; unfold w64; f_equal; lia
        | apply first_occ_mt; [exact HSa | exact Hfo] ]
      | exact I ]
    end.
Qed.
End s.
