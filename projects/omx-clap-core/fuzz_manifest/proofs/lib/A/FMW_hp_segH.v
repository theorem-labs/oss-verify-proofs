(* has_prefixed (G2) loop segment head: 0x821b0..0x821d8, kit lib/A/FMW_hp_kit.v.
   0x821b0 sub a0, s5, s3 (a0 = at - t = a); 0x821b4 blt a0, s8 (a < plen + 1 -> tail 0x82240); 0x821b8..0x821c0
   s9 = at - plen, s6 = s9 - 1, a0 = s6 + plen = at - 1; 0x821c4..0x821d4 the inline ASan check of at[-1] and its load
   (report 0x822c0); 0x821d8 bne a0, ':' (-> tail 0x82240, else on to strncmp 0x821dc). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI04 YN3v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YA0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC20 YI16 YI00 YM05 YG0q YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v ACeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_g2rt FMW_name_char FMW_hp_kit FMW_hp_model.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel has_prefixed_model.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* a register of a symbolic state as Z_to_bv 64 of its value *)
Ltac sgH_rsv HS r Hr :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    assert (Hr : getr (ms_regs ms) r = Z_to_bv 64 (U E e))
      by (rewrite <- denot_lit_U; refine (eq_trans (st_ok_restrict_reg segs H E ss ms r HS) _);
          change (sv_denot E e = sv_denot E e); reflexivity)
  end.
(* a run from a seat with no writable region leaves the memory as it was *)
Ltac sgH_ro HF Em :=
  lazymatch type of HF with
  | frame_of ?E ?rs ?m0 ?m1 =>
    assert (Em : m1 = m0) by (apply (frame_of_read_only E rs m0 m1); [vm_compute; reflexivity | exact HF])
  end.
(* the goal's configuration in cfg_at form, its machine state and model named *)
Ltac sgH_cfg HS MS MD :=
  lazymatch goal with |- SRr _ _ (mkCfg ?msx ?mdx) _ =>
    rewrite (st_ok_restrict_mkst tfibsegs _ _ _ msx HS eq_refl); cbn [ss_pc];
    set (MS := msx) in *; set (MD := mdx) in *
  end.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Hypothesis TL : TfibLib B.
Hypothesis IMGF : fm_img_facts tfibsegs B.

(* the loop state after a run that wrote no memory and kept s5 and HP_KEEP *)
Lemma sgH_move : forall cx a lyc Sc W regs m mdc E extra ss ms md',
  hp_st B cx a lyc Sc W regs m mdc ->
  st_ok tfibsegs E ss (restrict (w_H W) ms) ->
  env_agree 32 (Ereg regs extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0))
    ((21%bv : bv 5) :: HP_KEEP) = true ->
  ajournal tfibsegs B STK_has_prefixed (spZ (cx_regs0 cx)) [] (cx_ly cx) (cx_S cx) (cx_W0 cx) (cx_mem cx) (cx_md cx)
    [] lyc Sc W (ms_mem ms) md' 0 ->
  ms_mem ms = m ->
  hp_st B cx a lyc Sc W (ms_regs ms) (ms_mem ms) md'.
Proof.
intros cx a lyc Sc W regs m mdc E extra ss ms md' Hst HS HAE Hck HJ Em.
pose proof (regs_keep_of_st_ok _ E ss _ regs extra HS HAE Hck) as K. cbn [ms_regs restrict] in K.
pose proof Hst as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q21 & _ & _ & _ & _ & Hmt & _).
apply (hp_st_move B cx a a lyc Sc W regs m mdc (ms_regs ms) (ms_mem ms) md' Hst HJ).
- rewrite Em. apply gframe_refl.
- intros r Hr. apply K. right. exact Hr.
- rewrite (K 21%bv (or_introl eq_refl)). exact Q21.
- exact Hmt.
Qed.

Lemma hp_seg_head : seg_head_ok B.
Proof.
intros cx a KT KN lyc Sc W regs m mdc Hst _.
pose proof g2_segs_low as Hsegs. pose proof g2_wx as Hwx.
ceil2.
pose proof Hst as (HE & HJ & _ & _ & _ & _ & _ & _ & Q9 & _ & Q19 & _ & Q21 & _ & Q24 & _ & Q27 & Hmt & _).
pose proof HE as (_ & _ & _ & Ht & _ & _ & _ & Hlb & Hq & Hplen & Hqp & _).
pose proof Ht as (_ & Ht4096 & Htcl & _).
pose proof (has_prefixed_model.mt_len _ _ _ Hmt) as Halen.
assert (X9 : ew (Ereg regs []) 9 = Z_to_bv 64 (cx_plen cx))
  by (rewrite (ew_Ereg_nat regs [] 9 9%bv eq_refl); exact Q9).
assert (X19 : ew (Ereg regs []) 19 = Z_to_bv 64 (cx_t cx))
  by (rewrite (ew_Ereg_nat regs [] 19 19%bv eq_refl); exact Q19).
assert (X21 : ew (Ereg regs []) 21 = Z_to_bv 64 (cx_t cx + Z.of_nat a))
  by (rewrite (ew_Ereg_nat regs [] 21 21%bv eq_refl); exact Q21).
assert (X24 : ew (Ereg regs []) 24 = Z_to_bv 64 (cx_plen cx + 1))
  by (rewrite (ew_Ereg_nat regs [] 24 24%bv eq_refl); exact Q24).
assert (X27 : ew (Ereg regs []) 27 = Z_to_bv 64 (- cx_plen cx))
  by (rewrite (ew_Ereg_nat regs [] 27 27%bv eq_refl); exact Q27).
pose proof (hp_seat B cx a lyc Sc W regs m mdc HP_HEAD Hst) as HS.
unfold cfg_at. change (w64 HP_HEAD) with (Z_to_bv 64 HP_HEAD).
(* 0x821b0: a0 = at - t; the run stops at the blt 0x821b4 *)
aj_run tbl_hp_ok HS HJ.
{ apply awr_ok_nil. }
sgH_ro HF Em1. clear HF HFr HG.
assert (UA0 : U (Ereg regs []) (SAlu ALU_ADD (SMd M_MUL (SOff 19 0) (SLit (-1))) (SOff 21 0)) = Z.of_nat a).
{ rewrite U_add2, U_mul2, U_lit, (U_atom_mod _ 19 0 _ X19), (U_atom_mod _ 21 0 _ X21), !Z.add_0_r.
  rewrite (Z.mod_small (cx_t cx)) by lia. rewrite (Z.mod_small (cx_t cx + Z.of_nat a)) by lia.
  rewrite Zmult_mod_idemp_r, Zplus_mod_idemp_l. rewrite Z.mod_small by lia. lia. }
assert (U24 : U (Ereg regs []) (SOff 24 0) = cx_plen cx + 1).
{ rewrite (U_atom_mod _ 24 0 _ X24), Z.add_0_r. apply Z.mod_small. lia. }
srr_branch_with tbl_hp_ok HS.
- (* a < plen + 1: no room for a prefix and ':' before at -> tail *)
  rewrite branch_lt_small in Hc; [| rewrite UA0; lia | rewrite U24; lia].
  rewrite UA0, U24 in Hc. apply Z.ltb_lt in Hc.
  aj_run_to tbl_hp_ok HS HJ HP_TAIL.
  { apply awr_ok_nil. }
  sgH_ro HF Em2. clear HF HFr HG.
  sgH_cfg HS MS MD.
  assert (Hst1 : hp_st B cx a lyc Sc W (ms_regs MS) (ms_mem MS) MD).
  { apply (sgH_move cx a lyc Sc W regs m mdc _ [] _ MS MD Hst HS (env_agree_refl 32 _));
      [vm_compute; reflexivity | exact HJ | rewrite Em2; exact Em1]. }
  refine (KT lyc Sc W (ms_regs MS) (ms_mem MS) MD Hst1 (or_introl _)). lia.
- rewrite branch_lt_small in Hc; [| rewrite UA0; lia | rewrite U24; lia].
  rewrite UA0, U24 in Hc. apply Z.ltb_ge in Hc. rename Hc into Hlt.
  assert (Ha1 : (1 <= a)%nat) by lia.
  (* 0x821b4..0x821c0: s9 = at - plen, s6 = at - plen - 1, a0 = at - 1; stop at the check 0x821c4 *)
  aj_run_to tbl_hp_ok HS HJ 0x821c4.
  { apply awr_ok_nil. }
  sgH_ro HF Em2. clear HF HFr HG.
  sgH_rsv HS (10%bv : bv 5) P10. sgH_rsv HS (22%bv : bv 5) P22. sgH_rsv HS (25%bv : bv 5) P25.
  assert (UN1 : U (Ereg regs []) (SAlu ALU_ADD (SOff 9 (-1)) (SOff 21 0)) = cx_plen cx + cx_t cx + Z.of_nat a - 1).
  { rewrite U_add2, (U_atom_mod _ 9 (-1) _ X9), (U_atom_mod _ 21 0 _ X21), Zplus_mod_idemp_l, Zplus_mod_idemp_r.
    rewrite Z.mod_small by lia. lia. }
  assert (R10 : getr (ms_regs ms0) 10 = Z_to_bv 64 (cx_t cx + Z.of_nat (a - 1))).
  { rewrite P10. f_equal. rewrite U_add2, UN1, (U_atom_mod _ 27 0 _ X27), Zplus_mod_idemp_r.
    rewrite Z.mod_small by lia. lia. }
  assert (R22 : getr (ms_regs ms0) 22 = Z_to_bv 64 (cx_t cx + Z.of_nat a - cx_plen cx - 1)).
  { rewrite P22. f_equal.
    rewrite U_add2, (U_atom_mod _ 21 (-1) _ X21), (U_atom_mod _ 27 0 _ X27), Zplus_mod_idemp_l, Zplus_mod_idemp_r.
    rewrite Z.mod_small by lia. lia. }
  assert (R25 : getr (ms_regs ms0) 25 = Z_to_bv 64 (cx_t cx + Z.of_nat a - cx_plen cx)).
  { rewrite P25. f_equal.
    rewrite U_add2, (U_atom_mod _ 21 0 _ X21), (U_atom_mod _ 27 0 _ X27), Zplus_mod_idemp_l, Zplus_mod_idemp_r.
    rewrite Z.mod_small by lia. lia. }
  clear P10 P22 P25.
  sgH_cfg HS MS MD.
  assert (Hst2 : hp_st B cx a lyc Sc W (ms_regs MS) (ms_mem MS) MD).
  { apply (sgH_move cx a lyc Sc W regs m mdc _ [] _ MS MD Hst HS (env_agree_refl 32 _));
      [vm_compute; reflexivity | exact HJ | rewrite Em2; exact Em1]. }
  clear HS HJ.
  pose proof Hst2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q26 & _).
  assert (Hi : (a - 1 <= length (cx_tb cx))%nat) by lia.
  destruct (hp_tbyte B IMGF cx a lyc Sc W (ms_regs MS) (ms_mem MS) MD (a - 1) Hst2 Hi) as [Hv Hcr].
  set (c := ManifestModel.byte_at (cx_tb cx) (a - 1)) in *.
  assert (Hx : 4096 <= cx_t cx + Z.of_nat (a - 1) <= 2 ^ 47 - 8) by lia.
  pose proof (hp_seat_chk B cx a lyc Sc W (ms_regs MS) (ms_mem MS) MD 0x821c4 (cx_t cx + Z.of_nat (a - 1)) c
    Hst2 R10 Hx Hv Hcr) as HS.
  pose proof (hp_shok B IMGF cx a lyc Sc W (ms_regs MS) (ms_mem MS) MD c (a - 1) Hst2 R10 Hi) as SHOK.
  pose proof Hst2 as (_ & HJ & _).
  (* 0x821c4..0x821d4: srli/add/lb/bnez on the shadow of at[-1], then lbu. The token engine discharges the check
     from the shadow entry (the byte is a byte of the text, addressable by cstr_ok) and takes the fall-through:
     the report branch to 0x82258 / 0x822c0 (__asan_report_load1) is REFUTED. The run stops at the bne 0x821d8. *)
  aj_run_tok tbl_hp_ok HS HJ SHOK hp_Bspan.
  { apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  sgH_ro HF Em3. clear HF HFr HG.
  lazymatch type of HS with st_ok _ ?E3 _ _ =>
    assert (UB : U E3 (SExt false 8 (SOff 32 0)) = c);
    [ rewrite U_SExt; cbv beta iota;
      rewrite (U_atom _ 32 c); [| rewrite !ew_ewset_other by lia; exact (ew_Ereg_extra _ _ 0) | lia];
      change (2 ^ Z.of_N 8) with 256; rewrite (Z.mod_small c 256) by lia; apply zcanon_id; unfold M64; lia
    | ];
    assert (U26 : U E3 (SOff 26 0) = 58);
    [ apply (U_atom _ 26 58); [rewrite !ew_ewset_other by lia; rewrite (ew_Ereg_nat _ _ 26 26%bv eq_refl); exact Q26
                              | lia]
    | ];
    assert (HAE : env_agree 32 (Ereg (ms_regs MS) [w64 c]) E3)
      by env_agree_chain (env_agree_refl 32 (Ereg (ms_regs MS) [w64 c]))
  end.
  srr_branch_with tbl_hp_ok HS.
  + (* at[-1] <> ':' -> tail *)
    rewrite branch_ne_U, UB, U26 in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
    aj_run_to tbl_hp_ok HS HJ HP_TAIL.
    { awr_ok_tac. }
    sgH_ro HF Em4. clear HF HFr HG.
    sgH_cfg HS MS3 MD3.
    assert (Hst3 : hp_st B cx a lyc Sc W (ms_regs MS3) (ms_mem MS3) MD3).
    { apply (sgH_move cx a lyc Sc W (ms_regs MS) (ms_mem MS) MD _ [w64 c] _ MS3 MD3 Hst2 HS HAE);
        [vm_compute; reflexivity | exact HJ | rewrite Em4; exact Em3]. }
    refine (KT lyc Sc W (ms_regs MS3) (ms_mem MS3) MD3 Hst3 (or_intror _)). exact Hc.
  + (* at[-1] = ':' -> strncmp 0x821dc *)
    rewrite branch_ne_U, UB, U26 in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
    aj_run_to tbl_hp_ok HS HJ HP_NCMP.
    { awr_ok_tac. }
    sgH_ro HF Em4. clear HF HFr HG.
    sgH_cfg HS MS3 MD3.
    assert (Hst3 : hp_st B cx a lyc Sc W (ms_regs MS3) (ms_mem MS3) MD3).
    { apply (sgH_move cx a lyc Sc W (ms_regs MS) (ms_mem MS) MD _ [w64 c] _ MS3 MD3 Hst2 HS HAE);
        [vm_compute; reflexivity | exact HJ | rewrite Em4; exact Em3]. }
    assert (K : regs_keep [22%bv; 25%bv] (ms_regs MS) (ms_regs MS3))
      by exact (regs_keep_of_st_ok [22%bv; 25%bv] _ _ _ (ms_regs MS) [w64 c] HS HAE ltac:(vm_compute; reflexivity)).
    refine (KN lyc Sc W (ms_regs MS3) (ms_mem MS3) MD3 Hst3 (conj (conj _ (conj _ _)) Hc)).
    * lia.
    * rewrite (K 22%bv (or_introl eq_refl)). exact R22.
    * rewrite (K 25%bv (or_intror (or_introl eq_refl))). exact R25.
Qed.
End s.
