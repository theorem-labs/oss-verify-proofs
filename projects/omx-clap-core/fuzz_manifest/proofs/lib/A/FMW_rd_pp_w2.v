(* lv2_locate_manifest_readings, segment PP, piece W2: the name loop at L2 (0x81e44, lv2_locate.c:120,
   `while (name_ok (p[k])) k++`) proves pp_seg_W2 of lib/A/FMW_rd_pp_cuts.v.
   One iteration from L2 at k: the byte c at p1 + k (a2, atom 12) is decided on its value alone (pp_dgt / pp_dmk /
   pp_deq over the 256 byte values, FMW_rd_pp_cuts.v): a name byte checks text + p1 + k + 1 (a1 + s7 + 1, atom 13 + 1
   by the alias), loads it and re-enters L2 at k + 1; NUL or a space (bit c of RD_MASK1) exits through 0x82024 to RD_L
   at i + 1 (the declaration is DNone, readings_scan.db_ncolon); ':' goes to L3 (0x81eb4) with p2 = p1 + k, m = 0.
   The loop closes by strong induction on |text| - (p1 + k). Technique after G4's FMW_ex_decl_d2.v
   (a working branch: d2_loop, the name case / exit case split of the entry state, w2_cw_next = its dm_cw_next)
   and FMW_rd_pp.v (pp_space_body / pp_p_body: the run, branch and register-readback idiom). *)
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

(* ---- the exit case's state: L2 without the next byte. When the byte at p1 + k is not a name byte it may be the
   text's NUL, past which cstr_ok says nothing; the exit paths never read the next byte (after G4's ss_D2x) ---- *)
Definition ss_w2_x : sstate :=
  mkSS PP_L2 pp_regsL2 [pp_frameR] None
    (mkFacts [PP_AF2; PP_AF8; pp_afbyte 12; pp_afstr 13; pp_afbyte 34] []
       [(SAlu ALU_ADD (SOff 11 0) (SOff 23 0), SOff 13 0); (SAlu ALU_ADD (SOff 24 0) (SOff 27 0), SOff 10 0)]).

(* a count_while prefix grows by one over a byte of its class (G4 FMW_ex_decl_base.v dm_cw_next) *)
Lemma w2_cw_next : forall f l p k, (k <= count_while f (skipn p l))%nat -> (p + k < length l)%nat ->
  f (byte_at l (p + k)) = true -> (S k <= count_while f (skipn p l))%nat.
Proof.
intros f l p k Hk Hl Hf. rewrite (pp_cw_shift f l p k Hk).
rewrite (readings_scan.cw_step f l (p + k) Hl), Hf. lia.
Qed.

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.

(* the entry state of the exit case: pp_entry_L2 (FMW_rd_pp_cuts.v) without the byte region *)
Lemma w2_entry_x : forall (W : world tfibsegs) regs mem F u2v u3v atv s11 p1 k c cn,
  pp_fr W mem F u2v u3v ->
  getr regs 2 = w64 F -> getr regs 8 = w64 SHADOW_OFF -> getr regs 19 = w64 58 ->
  getr regs 10 = w64 (atv + s11) -> getr regs 24 = w64 atv -> getr regs 27 = w64 s11 ->
  getr regs 11 = w64 p1 -> getr regs 23 = w64 k -> getr regs 13 = w64 (p1 + k) -> getr regs 12 = w64 c ->
  4096 <= atv -> 0 <= s11 <= 7 -> atv + s11 + 1 <= alloc_ceiling ->
  4096 <= p1 -> 0 <= k -> p1 + k + 2 <= alloc_ceiling -> 0 <= c < 256 -> 0 <= cn < 256 ->
  st_ok tfibsegs (Ereg regs (pp_extra u2v u3v cn 0)) ss_w2_x
    (restrict (w_H W) (mkst regs (Z_to_bv 64 PP_L2) mem (seg_rom tfibsegs))).
Proof.
intros W regs mem F u2v u3v atv s11 p1 k c cn (V48 & V50 & V60 & Hu2 & Hu3 & HFc & HF2 & HF16)
  R2 R8 R19 R10 R24 R27 R11 R23 R13 R12 Hat Hs11 Hatc Hp1 Hk Hpk Hc Hcn.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Ereg regs (pp_extra u2v u3v cn 0)).
assert (E2 : ew E 2 = w64 F) by (unfold E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact R2).
assert (E8 : ew E 8 = w64 SHADOW_OFF) by (unfold E; rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8).
assert (E10 : ew E 10 = w64 (atv + s11)) by (unfold E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact R10).
assert (E11 : ew E 11 = w64 p1) by (unfold E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact R11).
assert (E12 : ew E 12 = w64 c) by (unfold E; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact R12).
assert (E13 : ew E 13 = w64 (p1 + k)) by (unfold E; rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact R13).
assert (E23 : ew E 23 = w64 k) by (unfold E; rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl); exact R23).
assert (E24 : ew E 24 = w64 atv) by (unfold E; rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact R24).
assert (E27 : ew E 27 = w64 s11) by (unfold E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact R27).
assert (E32 : ew E 32 = w64 u2v) by (unfold E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 u3v) by (unfold E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 cn) by (unfold E; exact (ew_Ereg_extra regs _ 2)).
pp_uw E 2%nat F E2. pp_uw E 8%nat SHADOW_OFF E8. pp_uw E 11%nat p1 E11. pp_uw E 12%nat c E12.
pp_uw E 13%nat (p1 + k) E13. pp_uw E 23%nat k E23. pp_uw E 34%nat cn E34.
pp_uw E 10%nat (atv + s11) E10. pp_uw E 24%nat atv E24. pp_uw E 27%nat s11 E27.
unfold ss_w2_x. apply (entry_st_ok_full tfibsegs); change (Ereg regs (pp_extra u2v u3v cn 0)) with E.
- unfold pp_regsL2.
  repeat (apply regs_ok_pin; [| intros X; discriminate X |]); [apply regs_ok_Ereg | ..];
    cbn [sv_denot]; exact R19.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  apply (pp_frameR_ok E _ F u2v u3v); try assumption; try lia.
- apply pairwise_disjoint_of_extents. unfold pp_frameR, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  cbn [zpairwise_disjoint zall_disjoint]. tauto.
- split; [|split; [exact I|]].
  + cbn [f_atoms atoms_ok PP_AF2 PP_AF8 pp_afstr pp_afbyte]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    repeat match goal with H : bv_unsigned (ew E ?n) = ?v |- _ => rewrite H end.
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF. repeat split; lia.
  + cbn [f_alias alias_ok]. split; [|split; [|exact I]].
    * apply U_inj.
      rewrite (U_add_off_atom E 11 0 23 0) by
        (repeat match goal with H : bv_unsigned (ew E ?n) = ?v |- _ => rewrite H end; unfold M64; lia).
      rewrite (U_atom E 13 (p1 + k) E13 ltac:(lia)).
      repeat match goal with H : bv_unsigned (ew E ?n) = ?v |- _ => rewrite H end. lia.
    * apply U_inj.
      rewrite (U_add_off_atom E 24 0 27 0) by
        (repeat match goal with H : bv_unsigned (ew E ?n) = ?v |- _ => rewrite H end; unfold M64; lia).
      rewrite (U_atom E 10 (atv + s11) E10 ltac:(lia)).
      repeat match goal with H : bv_unsigned (ew E ?n) = ?v |- _ => rewrite H end. lia.
Qed.
End e.

(* ---- the walk's tactics ---- *)
(* the run's memory is the entry memory: take the region list from HF's type (no evar under vm_compute) *)
Ltac w2_fr Hm :=
  lazymatch goal with HF : frame_of _ ?rs _ (ms_mem _) |- _ =>
    pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as Hm end;
  cbn [ms_mem] in Hm;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* turn a branch hypothesis on atom 12 into a closed byte decision pp_Dn (FMW_rd_pp_cuts.v pp_Dn_of) *)
Ltac w2_dec HS E12 c Hc :=
  let H12 := fresh "H12" in
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
    assert (H12 : ew Ev 12 = Z_to_bv 64 c) by (cbn [ew ewset extK Nat.eqb]; exact E12) end;
  erewrite (pp_Dn_of _ c _ _ _ H12) in Hc by reflexivity; clear H12.
(* a register goal after a run: the engine's value is an atom plus a literal (pp_reg_off) or a literal *)
Ltac w2_g HS :=
  lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
    lazymatch type of HS with st_ok ?segs ?Ev ?ss (restrict ?H ?ms') =>
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in
      rewrite (st_ok_restrict_reg segs H Ev ss ms' r HS); change (sr_get (ss_regs ss) r) with e
    end end;
  first [ erewrite pp_reg_off by (cbn [ew ewset extK Nat.eqb]; eassumption) | idtac ];
  unfold w64; first [ reflexivity
                    | f_equal; try unfold rd_p0; try unfold pp_s10_L2; try unfold pp_s10_L3; lia ].
(* the inline check of the next name byte, text + p1 + k + 1 (atom 13 + 1), is a byte of the text *)
Ltac w2_obl W3 E8 E13 Ct :=
  repeat match goal with H : ms_mem _ = _ |- _ => rewrite H end;
  lazymatch goal with |- range_addressable _ (U ?Ev _) (U ?Ev ?v) _ =>
    let F8 := fresh "F8" in let F13 := fresh "F13" in
    assert (F8 : ew Ev 8 = w64 SHADOW_OFF) by (cbn [ew ewset extK Nat.eqb]; exact E8);
    lazymatch type of E13 with _ = ?z13 =>
      assert (F13 : ew Ev 13 = z13) by (cbn [ew ewset extK Nat.eqb]; exact E13) end;
    apply (pp_obl1 W3 _ Ev v _ _ Ct (pp_U_Bx Ev F8));
    rewrite (pp_U_off Ev 13 _ 1 F13); unfold zcanon, M64; rewrite Z.mod_small by lia; lia
  end.
(* at a cut: the machine state in mkst form, the kept registers, the run's memory back to the entry memory *)
Ltac w2_land HS HJ E regs HK :=
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

Lemma w2_loop : forall f, rd_seg_L B CTX f -> pp_seg_W3 B CTX f ->
  forall r cx i d s11 p1 k ly3 S3 W3 regs mem md,
  (length (cx_tb cx) - (p1 + k) = r)%nat -> rd_base B CTX cx ->
  pp_at_L2 B cx i d (S f) s11 p1 k ly3 S3 W3 regs mem md ->
  SRr tfibsegs W3 (cfg_at tfibsegs PP_L2 regs mem md) (rd_post B cx).
Proof.
intros f HL HW3 r. induction r as [r IH] using lt_wf_ind.
intros cx i d s11 p1 k ly3 S3 W3 regs mem md Hr HB HA2.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof g3_wx as Hwx. pose proof g3_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HA2 as (HH & Ep1 & Hk & R10 & R11 & R12 & R13 & R16 & R20 & R21 & R22 & R23 & R25 & R26).
pose proof HH as (HI & HA & Hi & Hh & Hs11 & Hsp & R19 & R24 & R27).
pose proof (pp_facts_of B CTX cx d ly3 S3 W3 regs mem md HB HI) as
  (HFR & R2 & R8 & R9 & R18 & Ct & Cu & Ht4 & Htc & Hu4 & Huc & HWR & HJ).
assert (Hple : (i + s11 <= length (cx_tb cx))%nat) by exact (pp_head_le (cx_tb cx) i _ Hh).
pose proof (pp_cw_le is_space (cx_tb cx) (i + s11)) as Hcw1.
pose proof (pp_cw_le name_ok (cx_tb cx) p1) as Hcw2.
assert (Hpk : (p1 + k <= length (cx_tb cx))%nat) by lia.
assert (Hs11z : 0 <= Z.of_nat s11 <= 7) by (destruct Hs11 as [-> | ->]; lia).
destruct (pp_val_at W3 mem (cx_t cx) (cx_tb cx) (p1 + k) Ct Hpk) as [_ Hc255].
assert (Hcn : 0 <= byte_at (cx_tb cx) (p1 + S k) < 256).
{ destruct (Nat.le_gt_cases (p1 + S k) (length (cx_tb cx))) as [H|H].
  - exact (proj2 (pp_val_at W3 mem (cx_t cx) (cx_tb cx) (p1 + S k) Ct H)).
  - unfold byte_at. rewrite nth_overflow by lia. lia. }
set (c := byte_at (cx_tb cx) (p1 + k)) in *.
(* the entry env: the registers, then u - 2, u - 3, the byte at p1 + k + 1 (atoms 32, 33, 34) *)
set (E := Ereg regs (pp_extra (cx_u cx - 2) (cx_u cx - 3) (byte_at (cx_tb cx) (p1 + S k)) 0)).
assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs q)
  by (intros n q Hn; unfold E; apply ew_Ereg_nat; exact Hn).
pose proof (eq_trans (EE 2%nat 2%bv eq_refl) R2) as E2.
pose proof (eq_trans (EE 8%nat 8%bv eq_refl) R8) as E8.
pose proof (eq_trans (EE 9%nat 9%bv eq_refl) R9) as E9.
pose proof (eq_trans (EE 10%nat 10%bv eq_refl) R10) as E10.
pose proof (eq_trans (EE 11%nat 11%bv eq_refl) R11) as E11.
pose proof (eq_trans (EE 12%nat 12%bv eq_refl) R12) as E12.
pose proof (eq_trans (EE 13%nat 13%bv eq_refl) R13) as E13.
pose proof (eq_trans (EE 16%nat 16%bv eq_refl) R16) as E16.
pose proof (eq_trans (EE 18%nat 18%bv eq_refl) R18) as E18.
pose proof (eq_trans (EE 20%nat 20%bv eq_refl) R20) as E20.
pose proof (eq_trans (EE 21%nat 21%bv eq_refl) R21) as E21.
pose proof (eq_trans (EE 22%nat 22%bv eq_refl) R22) as E22.
pose proof (eq_trans (EE 23%nat 23%bv eq_refl) R23) as E23.
pose proof (eq_trans (EE 24%nat 24%bv eq_refl) R24) as E24.
pose proof (eq_trans (EE 25%nat 25%bv eq_refl) R25) as E25.
pose proof (eq_trans (EE 26%nat 26%bv eq_refl) R26) as E26.
pose proof (eq_trans (EE 27%nat 27%bv eq_refl) R27) as E27.
assert (E32 : ew E 32 = w64 (cx_u cx - 2)) by (unfold E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 (cx_u cx - 3)) by (unfold E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 (byte_at (cx_tb cx) (p1 + S k))) by (unfold E; exact (ew_Ereg_extra regs _ 2)).
clear EE.
unfold cfg_at. change (w64 PP_L2) with (Z_to_bv 64 PP_L2).
change mem with (ms_mem (mkst regs (Z_to_bv 64 PP_L2) mem (seg_rom tfibsegs))) in HJ.
destruct (name_ok c) eqn:Hnm.
- (* a name byte: the next byte is in the text; back to L2 at k + 1 *)
  assert (Hlt : (p1 + k < length (cx_tb cx))%nat).
  { destruct (Nat.lt_ge_cases (p1 + k) (length (cx_tb cx))) as [H|H]; [exact H|]. exfalso.
    assert (E0 : c = 0) by (unfold c, byte_at; apply nth_overflow; exact H).
    rewrite E0 in Hnm. discriminate Hnm. }
  destruct (pp_val_at W3 mem (cx_t cx) (cx_tb cx) (p1 + S k) Ct ltac:(lia)) as [Vn _].
  assert (Vn' : val_mem tfibsegs (mrestrict (w_H W3) mem) (cx_t cx + Z.of_nat p1 + Z.of_nat k + 1) 1
                  (byte_at (cx_tb cx) (p1 + S k)))
    by (replace (cx_t cx + Z.of_nat p1 + Z.of_nat k + 1) with (cx_t cx + Z.of_nat (p1 + S k)) by lia; exact Vn).
  pose proof (pp_entry_L2 W3 regs mem (cx_F cx) (cx_u cx - 2) (cx_u cx - 3) (cx_t cx + Z.of_nat i) (Z.of_nat s11)
    (cx_t cx + Z.of_nat p1) (Z.of_nat k) c (byte_at (cx_tb cx) (p1 + S k))
    HFR R2 R8 R19 R10 R24 R27 R11 R23 R13 R12 ltac:(lia) Hs11z ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    Hc255 Hcn Vn') as HS.
  change (Ereg regs (pp_extra (cx_u cx - 2) (cx_u cx - 3) (byte_at (cx_tb cx) (p1 + S k)) 0)) with E in HS.
  assert (SHOK : sh_ok tfibsegs PP_Bx [] E
    (mrestrict (w_H W3) (ms_mem (mkst regs (Z_to_bv 64 PP_L2) mem (seg_rom tfibsegs))))) by constructor.
  aj_run_tok rd_tbl_ok HS HJ SHOK PP_Bspan.
  { awr_ok_tac. }
  w2_fr Hm1.
  srr_branch_tok rd_tbl_ok HS SHOK PP_Bspan.
  + (* c > ':' *)
    w2_dec HS E12 c Hc. clear Hc.
    aj_run_to_tok rd_tbl_ok HS HJ SHOK PP_Bspan PP_L2.
    { w2_obl W3 E8 E13 Ct. }
    { awr_ok_tac. }
    w2_fr Hm2.
    w2_land HS HJ E regs HK.
    eapply (IH (length (cx_tb cx) - (p1 + S k))%nat ltac:(lia) cx i d s11 p1 (S k) ly3 S3 W3 _ _ _ eq_refl HB).
    unfold pp_at_L2, pp_head. cbv zeta.
    split; [split|].
    * apply (pp_loop_keep B cx d ly3 S3 W3 regs _ md); [exact HI | exact HJ | exact HK | w2_g HS | w2_g HS].
    * split; [exact HA|]. split; [exact Hi|]. split; [exact Hh|]. split; [exact Hs11|]. split; [exact Hsp|].
      split; [w2_g HS|]. split; [w2_g HS | w2_g HS].
    * split; [exact Ep1|]. split; [exact (w2_cw_next name_ok (cx_tb cx) p1 k Hk Hlt Hnm)|].
      do 10 (split; [w2_g HS|]). w2_g HS.
  + w2_dec HS E12 c Hc. rename Hc into D1.
    aj_run_tok rd_tbl_ok HS HJ SHOK PP_Bspan.
    { awr_ok_tac. }
    w2_fr Hm2.
    srr_branch_tok rd_tbl_ok HS SHOK PP_Bspan.
    * w2_dec HS E12 c Hc. exfalso. destruct (pp_nm_mk c Hc255 D1 Hc) as [X _]. rewrite Hnm in X. discriminate X.
    * w2_dec HS E12 c Hc. rename Hc into D2.
      aj_run_tok rd_tbl_ok HS HJ SHOK PP_Bspan.
      { awr_ok_tac. }
      w2_fr Hm3.
      srr_branch_tok rd_tbl_ok HS SHOK PP_Bspan.
      -- w2_dec HS E12 c Hc. exfalso. pose proof (pp_nm_eq c Hc255 D1 D2 Hc) as E58.
         rewrite E58 in Hnm. discriminate Hnm.
      -- (* a name byte at or below ':' that is neither NUL nor a space *)
         w2_dec HS E12 c Hc. clear Hc.
         aj_run_to_tok rd_tbl_ok HS HJ SHOK PP_Bspan PP_L2.
         { w2_obl W3 E8 E13 Ct. }
         { awr_ok_tac. }
         w2_fr Hm4.
         w2_land HS HJ E regs HK.
         eapply (IH (length (cx_tb cx) - (p1 + S k))%nat ltac:(lia) cx i d s11 p1 (S k) ly3 S3 W3 _ _ _ eq_refl HB).
         unfold pp_at_L2, pp_head. cbv zeta.
         split; [split|].
         ++ apply (pp_loop_keep B cx d ly3 S3 W3 regs _ md); [exact HI | exact HJ | exact HK | w2_g HS | w2_g HS].
         ++ split; [exact HA|]. split; [exact Hi|]. split; [exact Hh|]. split; [exact Hs11|]. split; [exact Hsp|].
            split; [w2_g HS|]. split; [w2_g HS | w2_g HS].
         ++ split; [exact Ep1|]. split; [exact (w2_cw_next name_ok (cx_tb cx) p1 k Hk Hlt Hnm)|].
            do 10 (split; [w2_g HS|]). w2_g HS.
- (* not a name byte: the name ends at p2 = p1 + k *)
  assert (Hcw : count_while name_ok (skipn p1 (cx_tb cx)) = k) by exact (pp_cw_exact name_ok (cx_tb cx) p1 k Hk Hnm).
  pose proof (w2_entry_x W3 regs mem (cx_F cx) (cx_u cx - 2) (cx_u cx - 3) (cx_t cx + Z.of_nat i) (Z.of_nat s11)
    (cx_t cx + Z.of_nat p1) (Z.of_nat k) c (byte_at (cx_tb cx) (p1 + S k))
    HFR R2 R8 R19 R10 R24 R27 R11 R23 R13 R12 ltac:(lia) Hs11z ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    Hc255 Hcn) as HS.
  change (Ereg regs (pp_extra (cx_u cx - 2) (cx_u cx - 3) (byte_at (cx_tb cx) (p1 + S k)) 0)) with E in HS.
  assert (SHOK : sh_ok tfibsegs PP_Bx [] E
    (mrestrict (w_H W3) (ms_mem (mkst regs (Z_to_bv 64 PP_L2) mem (seg_rom tfibsegs))))) by constructor.
  aj_run_tok rd_tbl_ok HS HJ SHOK PP_Bspan.
  { awr_ok_tac. }
  w2_fr Hm1.
  srr_branch_tok rd_tbl_ok HS SHOK PP_Bspan.
  + w2_dec HS E12 c Hc. exfalso. pose proof (pp_nm_gt c Hc255 Hc) as X. rewrite Hnm in X. discriminate X.
  + w2_dec HS E12 c Hc. rename Hc into D1.
    aj_run_tok rd_tbl_ok HS HJ SHOK PP_Bspan.
    { awr_ok_tac. }
    w2_fr Hm2.
    srr_branch_tok rd_tbl_ok HS SHOK PP_Bspan.
    * (* NUL or a space (bit c of RD_MASK1): 0x82024, the declaration is DNone and the scan goes on at i + 1 *)
      w2_dec HS E12 c Hc. destruct (pp_nm_mk c Hc255 D1 Hc) as [_ Hc58]. clear Hc.
      assert (Hdecl : decl (cx_tb cx) i = DNone).
      { rewrite (readings_scan.decl_some (cx_tb cx) i (i + s11)%nat Hh).
        apply (readings_scan.db_ncolon (cx_tb cx) (i + s11)%nat p1 (p1 + k)%nat Hsp Ep1);
          [rewrite Hcw; reflexivity | exact Hc58]. }
      aj_run_to_tok rd_tbl_ok HS HJ SHOK PP_Bspan RD_L.
      { awr_ok_tac. }
      w2_fr Hm3.
      w2_land HS HJ E regs HK.
      apply (pp_to_L B CTX f cx i d ly3 S3 W3 _ mem _ HL HB).
      -- apply (pp_loop_keep B cx d ly3 S3 W3 regs _ md); [exact HI | exact HJ | exact HK | w2_g HS | w2_g HS].
      -- exact HA.
      -- exact Hi.
      -- exact Hdecl.
      -- w2_g HS.
      -- w2_g HS.
    * w2_dec HS E12 c Hc. rename Hc into D2.
      aj_run_tok rd_tbl_ok HS HJ SHOK PP_Bspan.
      { awr_ok_tac. }
      w2_fr Hm3.
      srr_branch_tok rd_tbl_ok HS SHOK PP_Bspan.
      -- (* ':' : the third loop's head with p2 = p1 + k and no space consumed yet *)
         w2_dec HS E12 c Hc. pose proof (pp_nm_eq c Hc255 D1 D2 Hc) as E58. clear Hc.
         aj_run_to_tok rd_tbl_ok HS HJ SHOK PP_Bspan PP_L3.
         { awr_ok_tac. }
         w2_fr Hm4.
         w2_land HS HJ E regs HK.
         apply (HW3 cx i d s11 p1 (p1 + k)%nat 0%nat ly3 S3 W3 _ _ _ HB).
         unfold pp_at_L3, pp_head. cbv zeta.
         split; [split|].
         ++ apply (pp_loop_keep B cx d ly3 S3 W3 regs _ md); [exact HI | exact HJ | exact HK | w2_g HS | w2_g HS].
         ++ split; [exact HA|]. split; [exact Hi|]. split; [exact Hh|]. split; [exact Hs11|]. split; [exact Hsp|].
            split; [w2_g HS|]. split; [w2_g HS | w2_g HS].
         ++ split; [exact Ep1|]. split; [rewrite Hcw; reflexivity|]. split; [exact E58|]. split; [lia|].
            do 9 (split; [w2_g HS|]). w2_g HS.
      -- w2_dec HS E12 c Hc. exfalso. destruct (pp_nm_ok c Hc255 D1 D2 Hc) as [X _]. rewrite Hnm in X.
         discriminate X.
Qed.

Theorem pp_w2_holds : forall f, rd_seg_L B CTX f -> pp_seg_W3 B CTX f -> pp_seg_W2 B CTX f.
Proof.
intros f HL HW3 cx i d s11 p1 k ly3 S3 W3 regs mem md HB HA2.
exact (w2_loop f HL HW3 _ cx i d s11 p1 k ly3 S3 W3 regs mem md eq_refl HB HA2).
Qed.

End c.
