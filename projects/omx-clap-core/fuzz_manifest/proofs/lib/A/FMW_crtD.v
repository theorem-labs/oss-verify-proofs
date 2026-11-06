(* check_round_trip, the four snprintf/reader pairs of one used split point k (fuzz_manifest.c:279-287; plain (uri + k)
   holds): crt_segD1 (CRT_L1 -> t1 -> names -> CRT_L3), crt_segD2 (CRT_L3 -> t2 -> names -> CRT_L5), crt_segD3
   (CRT_L5 -> t3 -> names -> CRT_L7), crt_segD4 (CRT_L7 -> t1x -> as_ruled -> CRT_L9). The pair glue is FMW_crtC.v. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d YC20.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v AF0l ACej FMPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_kit FMW_K FMW_kitS FMW_seg FMW_crt0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_crtX FMW_crtC.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Local Ltac cs_tac := unfold acallee_saved; lazymatch goal with |- context [bv_unsigned ?q] =>
  let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end; lia.

(* the resume state at CRT_L1: every register its own atom, atom 33 = the t1 format pointer the frame slot sp + 0
   holds (fuzz_manifest.c:280 reloads it with `ld a2, 0(sp)`), read-only *)
Definition crt_slot_region : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))].
Definition crt_fss_slot (pc : Z) : sstate := mkSS pc sr_atoms [crt_slot_region] None (mkFacts [] [] []).

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma crt_resume_slot : forall (W : world tfibsegs) regs mem pc v,
  0 <= spZ regs -> spZ regs + 8 <= 2 ^ 64 ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (spZ regs) 8 v -> 0 <= v < 2 ^ 64 ->
  st_ok tfibsegs (fmw_env regs [v]) (crt_fss_slot pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) mem (seg_rom tfibsegs))).
Proof.
intros W regs mem pc v H0 H1 Hv Hvr.
rewrite restrict_mkst_fx. unfold crt_fss_slot. unfold fmw_env at 1.
apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
  assert (Usp : forall ex, bv_unsigned (ew (Ereg regs ex) 2) = spZ regs)
    by (intros ex; rewrite (ew_Ereg_nat regs ex 2 2%bv eq_refl); reflexivity).
  unfold region_ok, crt_slot_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Usp.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val tfibsegs _ _ (spZ regs) 0 8 (SOff 33 0) v).
  + rewrite fmw_SOff0. change 33%nat with (32 + 1)%nat. rewrite ew_Ereg_extra. cbn [nth map]. reflexivity.
  + exact Hvr.
  + lia.
  + rewrite Z.add_0_r. exact Hv.
- first [ (cbn; tauto) | (apply pairwise_disjoint_of_extents; cbn; tauto) | (cbn; repeat constructor) ].
- split; [exact I | split; exact I].
Qed.
End r.

(* the frame of a run from crt_fss_slot (no writable byte), as same_below *)
Ltac crt_sb_ro m1 m2 SB :=
  match goal with H : frame_of _ _ m1 m2 |- _ =>
    let H' := fresh "HF'" in pose proof H as H'; cbn [add_cond ss_mem crt_fss_slot] in H';
    pose proof (same_below_frame _ _ m1 m2 (2 ^ 64) H'
      ltac:(constructor; [left; cbn; lia | constructor]) ltac:(lia)) as SB; clear H' end.

Section D. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis IMG : fm_img_facts tfibsegs B.
Hypothesis SNP : asnprintf_realizes tfibsegs B PC_snprintf.
Hypothesis NAMES : names_spec tfibsegs B CTX_lv2_locate_manifest_names.
Hypothesis ASR : as_ruled_spec tfibsegs B CTX_as_ruled.

(* ---- the loop registers and the t1 slot ride along ---- *)
Lemma crt_sb_keep : forall cx (W : world tfibsegs) mem mem', crt_base B cx -> same_below mem mem' (2 ^ 64) ->
  forall a, cx_sp0 cx - CRT_FRAME <= a < 2 ^ 64 -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a.
Proof.
intros cx W mem mem' ((HAP & _) & _) SB a Ha.
pose proof (fmw_sp B _ _ _ _ _ _ _ _ HAP) as (_ & Hceil & _ & HS0).
pose proof asan_consts as (C1 & _).
apply (aview_below (w_H W) mem mem' (2 ^ 64) a SB). unfold cx_sp0, CRT_FRAME in Ha. lia.
Qed.
Lemma crt_lregs_regs : forall cx (W W' : world tfibsegs) regs regs' mem mem' k,
  crt_base B cx -> crt_lregs cx W regs mem k ->
  getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 -> getr regs' 21 = getr regs 21 ->
  getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 -> getr regs' 24 = getr regs 24 ->
  getr regs' 25 = getr regs 25 -> getr regs' 27 = getr regs 27 ->
  (forall a, cx_sp0 cx - CRT_FRAME <= a < 2 ^ 64 ->
     aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) ->
  crt_lregs cx W' regs' mem' k.
Proof.
intros cx W W' regs regs' mem mem' k ((HAP & _) & _) (L19 & L20 & L21 & L22 & L23 & L24 & L25 & L27 & Ls)
  R19 R20 R21 R22 R23 R24 R25 R27 Hm.
pose proof (fmw_sp B _ _ _ _ _ _ _ _ HAP) as (_ & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _).
unfold crt_lregs. rewrite R19, R20, R21, R22, R23, R24, R25, R27.
split; [exact L19|]. split; [exact L20|]. split; [exact L21|]. split; [exact L22|].
split; [exact L23|]. split; [exact L24|]. split; [exact L25|]. split; [exact L27|].
eapply (val_mem_kept tfibsegs); [|exact Ls]. intros j Hj. apply Hm.
cbn in Hj. unfold cx_sp0, CRT_FRAME in *. lia.
Qed.
Lemma crt_lregs_pres : forall cx (W W' : world tfibsegs) regs regs' mem mem' k,
  crt_base B cx -> crt_lregs cx W regs mem k -> aregs_preserved regs regs' ->
  (forall a, cx_sp0 cx - CRT_FRAME <= a < 2 ^ 64 ->
     aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) ->
  crt_lregs cx W' regs' mem' k.
Proof.
intros cx W W' regs regs' mem mem' k HB HL HP Hm.
apply (crt_lregs_regs cx W W' regs regs' mem mem' k HB HL).
all: first [ exact Hm | (apply (fmw_pres _ _ _ HP); cs_tac) ].
Qed.
(* reader calls left are bounded: the pair's reader call keeps g_count below its budget *)
Lemma crt_m_bound : forall cx m (k : nat), crt_base B cx ->
  m + crt_rest cx k = rt_calls (cx_ub cx) -> (k < length (cx_ub cx))%nat ->
  ManifestModel.byte_at (cx_ub cx) (k - 1) <> 62 -> ManifestModel.plain_name (skipn k (cx_ub cx)) = true ->
  m + 4 <= 3 + 4 * 254.
Proof.
intros cx m k (_ & _ & _ & _ & _ & Hlu & _) Hr Hk Hb Hp.
rewrite (crt_rest_stepP cx k Hk Hb Hp) in Hr.
pose proof (crt_rest_pos cx (S k)). pose proof (rt_calls_le (cx_ub cx) Hlu). lia.
Qed.

(* ---- crt_segD1: CRT_L1 (0x80fd4), plain (uri + k) = 1: `beqz a0` falls through; a2 := the t1 format (frame slot
   sp + 0); snprintf (t, 3 n + 64, t1, k, uri, uri + k) at 0x80ff0; names (t, uri) at 0x80ffc answers 1
   (ManifestModel.rt_t1); back at CRT_L3 with one of the four calls made ---- *)
Lemma crt_segD1 : forall cx ly' S' (W' : world tfibsegs) regs' mem' md' k0 t m (k : nat),
  crt_base B cx -> crt_L1 B cx ly' S' W' regs' mem' md' k0 t m k ->
  ManifestModel.plain_name (skipn k (cx_ub cx)) = true ->
  (forall ly2 S2 (W2 : world tfibsegs) regs2 mem2 md2 k2,
     crt_Lj B cx ly2 S2 W2 regs2 mem2 md2 k2 t m k 1 ->
     SRr tfibsegs W2 (cfg_at tfibsegs CRT_L3 regs2 mem2 md2) (crt_post B cx)) ->
  SRr tfibsegs W' (cfg_at tfibsegs CRT_L1 regs' mem' md') (crt_post B cx).
Proof.
intros cx ly S W regs mem md k0 t m k HB ((HT & HLR & Hkb & Hrest & Hfk) & Hbyte & H10) Hplain K3.
rewrite Hplain in H10.
pose proof (AR_laws_ok tfibsegs B) as LAWS'. pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
pose proof asan_consts as (C1 & _).
pose proof HB as (_ & _ & _ & _ & Hku0 & Hlu & _).
pose proof HT as ((HJ & _ & Hsp & _ & _ & Hs0 & _ & Hcu & _ & _) & Hk & Hn1 & H9 & H18 & _ & Hperm & _).
pose proof HLR as (L19 & L20 & L21 & L22 & L23 & L24 & L25 & L27 & Lslot).
assert (Hkn : (k < length (cx_ub cx))%nat) by (unfold cx_n in Hkb; lia).
pose proof (crt_m_bound cx m k HB Hrest Hkn Hbyte Hplain) as Hmb.
assert (Hnpos : 0 < crt_tsz (cx_n cx)) by (unfold crt_tsz, cx_n; lia).
pose proof Hcu as ((_ & Hnzu) & Hu1 & Hu2 & _).
assert (Hsp0 : 0 <= spZ regs /\ spZ regs + 8 <= 2 ^ 64).
{ pose proof HB as ((HAP & _) & _). pose proof (fmw_sp B _ _ _ _ _ _ _ _ HAP) as (_ & Hc & H47 & HS0).
  unfold cx_sp0, CRT_FRAME in Hsp. lia. }
(* the resume state, the dead branch, the stretch to snprintf *)
pose proof (crt_resume_slot W regs mem CRT_L1 FMT_t1 (proj1 Hsp0) (proj2 Hsp0)
  ltac:(rewrite Hsp; exact Lslot) ltac:(unfold FMT_t1; lia)) as HS.
unfold fmw_env in HS.
unfold crt_J in HJ.
unfold cfg_at. change (w64 CRT_L1) with (Z_to_bv 64 CRT_L1).
assert (U10 : U (Ereg regs (Z_to_bv 64 FMW_SB :: map (Z_to_bv 64) [FMT_t1])) (SOff 10 0) = 1)
  by (apply U_atom; [rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10 | lia]).
assert (U0 : U (Ereg regs (Z_to_bv 64 FMW_SB :: map (Z_to_bv 64) [FMT_t1])) (SLit 0) = 0) by (apply U_lit; lia).
eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 10 0) (b := SLit 0); [exact HS | intros Hb _ | intros Hb HSb].
{ exfalso. rewrite branch_eq_U, U10, U0 in Hb. discriminate Hb. }
clear HS.
aj_run_to fmw_tbl_crt_ok HSb HJ PC_snprintf.
{ awr_ok_tac. }
lazymatch type of HSb with context [restrict _ ?m] => rename m into ms1 end.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md1 := mdx) in * end.
set (E1 := Ereg regs (Z_to_bv 64 FMW_SB :: map (Z_to_bv 64) [FMT_t1])) in HSb.
crt_sb_ro mem (ms_mem ms1) SB1.
pose proof (fmw_reg_lit _ E1 _ ms1 1%bv CRT_L2 HSb ltac:(vm_compute; reflexivity) ltac:(unfold CRT_L2; lia)) as R1.
pose proof (fmw_reg_atom _ regs _ _ ms1 10%bv 18%bv 18 HSb ltac:(vm_compute; reflexivity) eq_refl) as R10.
pose proof (fmw_reg_atom _ regs _ _ ms1 11%bv 9%bv 9 HSb ltac:(vm_compute; reflexivity) eq_refl) as R11.
pose proof (fmw_reg_extra _ regs _ _ ms1 12%bv 1 HSb ltac:(vm_compute; reflexivity)) as R12. cbn [nth map] in R12.
pose proof (fmw_reg_atom _ regs _ _ ms1 (Z_to_bv 5 13) 25%bv 25 HSb ltac:(vm_compute; reflexivity) eq_refl) as R13.
pose proof (fmw_reg_atom _ regs _ _ ms1 (Z_to_bv 5 14) 8%bv 8 HSb ltac:(vm_compute; reflexivity) eq_refl) as R14.
pose proof (fmw_reg_atom _ regs _ _ ms1 (Z_to_bv 5 15) 19%bv 19 HSb ltac:(vm_compute; reflexivity) eq_refl) as R15.
assert (HT1 : crt_tcore B cx ly S W (ms_regs ms1) (ms_mem ms1) md1 k0 t m).
{ apply (crt_tcore_nr B IMG cx ly S W regs mem md k0 t m (ms_regs ms1) (ms_mem ms1) md1 HB HT HJ SB1);
    crt_keep HSb. }
assert (LR1 : crt_lregs cx W (ms_regs ms1) (ms_mem ms1) k).
{ apply (crt_lregs_regs cx W W regs (ms_regs ms1) mem (ms_mem ms1) k HB HLR).
  all: first [ exact (crt_sb_keep cx W mem (ms_mem ms1) HB SB1) | crt_keep HSb ]. }
pose proof HT1 as ((HJ1 & _ & _ & _ & _ & _ & _ & Hcu1 & _ & _) & _).
pose proof HJ1 as (HAR1 & _).
pose proof (crt_uri_disj B cx ly S W (ms_mem ms1) md1 t (crt_tsz (cx_n cx)) (cx_u cx) (cx_ub cx)
  HAR1 Hperm Hku0 Hnpos) as Hdisj.
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E1 _ ms1 HSb eq_refl). cbn [ss_pc].
change (mkCfg (mkst (ms_regs ms1) (Z_to_bv 64 PC_snprintf) (ms_mem ms1) (seg_rom tfibsegs)) md1)
  with (cfg_at tfibsegs PC_snprintf (ms_regs ms1) (ms_mem ms1) md1).
apply (crt_snp B IMG SNP cx ly S W (ms_regs ms1) (ms_mem ms1) md1 k0 t m CRT_L2 ps_t1 FMT_t1
  (ManifestModel.txt_t1 (cx_ub cx) k) _ HB HT1 R1).
- unfold CRT_L2; lia.
- reflexivity.
- rewrite R10. exact H18.
- rewrite R11. exact H9.
- rewrite R12. reflexivity.
- exact in_ps_t1.
- cbn [map]. rewrite R13, R14, R15, L25, Hs0, L19. unfold w64.
  rewrite (unsigned_lit_small (Z.of_nat k)) by (unfold cx_n in Hkb; lia).
  rewrite (unsigned_lit_small (cx_u cx)) by lia.
  rewrite (unsigned_lit_small (cx_u cx + Z.of_nat k)) by (unfold cx_n in Hkb; lia).
  unfold ps_t1.
  apply (frender_lplsl W (ms_mem ms1) t _ _ _ _ (Z.of_nat k) (cx_u cx) (cx_ub cx) (cx_u cx + Z.of_nat k)
    (skipn k (cx_ub cx))).
  + unfold cx_n in Hkb. lia.
  + exact Hcu1.
  + exact Hdisj.
  + exact (cstr_ok_suffix W (ms_mem ms1) (cx_u cx) (cx_ub cx) k ltac:(lia) Hcu1).
  + rewrite length_skipn. lia.
  + rewrite Nat2Z.id. reflexivity.
- rewrite (txt_len_t1 (cx_ub cx) k ltac:(lia)). unfold crt_tsz, cx_n. lia.
- apply nz_txt_t1. exact Hnzu.
- intros regs2 mem2 md2 HT2 HP2 Hout2 Hkeep2.
  pose proof HT2 as ((HJ2 & _ & _ & _ & _ & Hs02 & _ & _ & _ & _) & _ & _ & _ & H182 & _).
  pose proof (crt_lregs_pres cx W W (ms_regs ms1) regs2 (ms_mem ms1) mem2 k HB LR1 HP2 Hkeep2) as LR2.
  (* the stretch to names: a0 := s2, a1 := s0 *)
  pose proof (fmw_resume_nr W regs2 [] mem2 CRT_L2) as HS2.
  unfold crt_J in HJ2.
  unfold cfg_at. change (w64 CRT_L2) with (Z_to_bv 64 CRT_L2).
  aj_run_to fmw_tbl_crt_ok HS2 HJ2 A_names.
  { apply awr_ok_nil. }
  lazymatch type of HS2 with context [restrict _ ?m] => rename m into ms3 end.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md3 := mdx) in * end.
  set (E3 := Ereg regs2 []) in HS2.
  crt_sb0 mem2 (ms_mem ms3) SB3.
  pose proof (fmw_reg_lit _ E3 _ ms3 1%bv CRT_L3 HS2 ltac:(vm_compute; reflexivity) ltac:(unfold CRT_L3; lia)) as Q1.
  pose proof (fmw_reg_atom _ regs2 _ _ ms3 10%bv 18%bv 18 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q10.
  pose proof (fmw_reg_atom _ regs2 _ _ ms3 11%bv 8%bv 8 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q11.
  assert (HT3 : crt_tcore B cx ly S W (ms_regs ms3) (ms_mem ms3) md3 k0 t m).
  { apply (crt_tcore_nr B IMG cx ly S W regs2 mem2 md2 k0 t m (ms_regs ms3) (ms_mem ms3) md3 HB HT2 HJ2 SB3);
      crt_keep HS2. }
  assert (LR3 : crt_lregs cx W (ms_regs ms3) (ms_mem ms3) k).
  { apply (crt_lregs_regs cx W W regs2 (ms_regs ms3) mem2 (ms_mem ms3) k HB LR2).
    all: first [ exact (crt_sb_keep cx W mem2 (ms_mem ms3) HB SB3) | crt_keep HS2 ]. }
  assert (Hout3 : cstr_ok tfibsegs W (ms_mem ms3) t (ManifestModel.txt_t1 (cx_ub cx) k)).
  { apply (cstr_ok_below W mem2 (ms_mem ms3)); [apply (same_below_mono _ _ _ _ SB3); lia | exact Hout2]. }
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E3 _ ms3 HS2 eq_refl). cbn [ss_pc].
  change (mkCfg (mkst (ms_regs ms3) (Z_to_bv 64 A_names) (ms_mem ms3) (seg_rom tfibsegs)) md3)
    with (cfg_at tfibsegs A_names (ms_regs ms3) (ms_mem ms3) md3).
  apply (crt_names_call B IMG NAMES cx ly S W (ms_regs ms3) (ms_mem ms3) md3 k0 t m CRT_L3
    (ManifestModel.txt_t1 (cx_ub cx) k) _ HB HT3 Q1).
  + unfold CRT_L3; lia.
  + reflexivity.
  + cbv [CTX_lv2_locate_manifest_names CRT_L3]. repeat (first [left; reflexivity | right]).
  + rewrite Q10. exact H182.
  + rewrite Q11. exact Hs02.
  + exact Hout3.
  + rewrite (txt_len_t1 (cx_ub cx) k ltac:(lia)). unfold crt_tsz, cx_n. lia.
  + lia.
  + unfold EV_names. lia.
  + intros ly4 S4 W4 regs4 mem4 md4 HT4 HP4 H10' Hkeep4.
    pose proof (crt_lregs_pres cx W W4 (ms_regs ms3) regs4 (ms_mem ms3) mem4 k HB LR3 HP4 Hkeep4) as LR4.
    assert (Hfk' : forallb (fun c => negb (c =? 62)) (firstn k (cx_ub cx)) = true)
      by (apply (forallb_firstn_step (cx_ub cx) k); [unfold cx_n in Hkb; lia | lia | exact Hfk | exact Hbyte]).
    apply (K3 ly4 S4 W4 regs4 mem4 md4 (k0 + EV_names)).
    split; [exact HT4|]. split; [exact LR4|]. split; [exact Hkb|]. split; [exact Hrest|].
    split; [exact Hbyte|]. split; [exact Hplain|]. split; [|exact Hfk'].
    rewrite H10', (ManifestModel.rt_t1 (cx_ub cx) k Hkn Hfk' Hplain). reflexivity.
Qed.

(* ---- crt_segD2: CRT_L3 (0x81000), one call made: `bne a0, s5` falls through (a0 = 1 = s5); snprintf (t, 3 n + 64,
   t2, k, uri, uri + k) at 0x8101c; names (t, uri) at 0x81028 answers 1 (ManifestModel.rt_t2); back at CRT_L5 ---- *)
Lemma crt_segD2 : forall cx ly' S' (W' : world tfibsegs) regs' mem' md' k0 t m (k : nat),
  crt_base B cx -> crt_Lj B cx ly' S' W' regs' mem' md' k0 t m k 1 ->
  (forall ly2 S2 (W2 : world tfibsegs) regs2 mem2 md2 k2,
     crt_Lj B cx ly2 S2 W2 regs2 mem2 md2 k2 t m k 2 ->
     SRr tfibsegs W2 (cfg_at tfibsegs CRT_L5 regs2 mem2 md2) (crt_post B cx)) ->
  SRr tfibsegs W' (cfg_at tfibsegs CRT_L3 regs' mem' md') (crt_post B cx).
Proof.
intros cx ly S W regs mem md k0 t m k HB (HT & HLR & Hkb & Hrest & Hbyte & Hplain & H10 & Hfk) K5.
pose proof (AR_laws_ok tfibsegs B) as LAWS'. pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
pose proof asan_consts as (C1 & _).
pose proof HB as (_ & _ & _ & _ & Hku0 & Hlu & _).
pose proof HT as ((HJ & _ & Hsp & _ & _ & Hs0 & _ & Hcu & _ & _) & Hk & Hn1 & H9 & H18 & _ & Hperm & _).
pose proof HLR as (L19 & L20 & L21 & L22 & L23 & L24 & L25 & L27 & Lslot).
assert (Hkn : (k < length (cx_ub cx))%nat) by (unfold cx_n in Hkb; lia).
pose proof (crt_m_bound cx m k HB Hrest Hkn Hbyte Hplain) as Hmb.
assert (Hnpos : 0 < crt_tsz (cx_n cx)) by (unfold crt_tsz, cx_n; lia).
pose proof Hcu as ((_ & Hnzu) & Hu1 & Hu2 & _).
pose proof (fmw_resume_nr W regs [] mem CRT_L3) as HS.
unfold crt_J in HJ.
unfold cfg_at. change (w64 CRT_L3) with (Z_to_bv 64 CRT_L3).
assert (U10 : U (Ereg regs []) (SOff 10 0) = 1)
  by (apply U_atom; [rewrite (ew_Ereg_nat regs [] 10 10%bv eq_refl); exact H10 | lia]).
assert (U21 : U (Ereg regs []) (SOff 21 0) = 1)
  by (apply U_atom; [rewrite (ew_Ereg_nat regs [] 21 21%bv eq_refl); exact L21 | lia]).
eapply SRr_sym_branch with (c := BC_NE) (a := SOff 10 0) (b := SOff 21 0); [exact HS | intros Hb _ | intros Hb HSb].
{ exfalso. rewrite branch_ne_U, U10, U21 in Hb. discriminate Hb. }
clear HS.
aj_run_to fmw_tbl_crt_ok HSb HJ PC_snprintf.
{ apply awr_ok_nil. }
lazymatch type of HSb with context [restrict _ ?m] => rename m into ms1 end.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md1 := mdx) in * end.
set (E1 := Ereg regs []) in HSb.
crt_sb0 mem (ms_mem ms1) SB1.
pose proof (fmw_reg_lit _ E1 _ ms1 1%bv CRT_L4 HSb ltac:(vm_compute; reflexivity) ltac:(unfold CRT_L4; lia)) as R1.
pose proof (fmw_reg_atom _ regs _ _ ms1 10%bv 18%bv 18 HSb ltac:(vm_compute; reflexivity) eq_refl) as R10.
pose proof (fmw_reg_atom _ regs _ _ ms1 11%bv 9%bv 9 HSb ltac:(vm_compute; reflexivity) eq_refl) as R11.
pose proof (fmw_reg_atom _ regs _ _ ms1 12%bv 22%bv 22 HSb ltac:(vm_compute; reflexivity) eq_refl) as R12.
pose proof (fmw_reg_atom _ regs _ _ ms1 (Z_to_bv 5 13) 25%bv 25 HSb ltac:(vm_compute; reflexivity) eq_refl) as R13.
pose proof (fmw_reg_atom _ regs _ _ ms1 (Z_to_bv 5 14) 8%bv 8 HSb ltac:(vm_compute; reflexivity) eq_refl) as R14.
pose proof (fmw_reg_atom _ regs _ _ ms1 (Z_to_bv 5 15) 19%bv 19 HSb ltac:(vm_compute; reflexivity) eq_refl) as R15.
assert (HT1 : crt_tcore B cx ly S W (ms_regs ms1) (ms_mem ms1) md1 k0 t (m + 1)).
{ apply (crt_tcore_nr B IMG cx ly S W regs mem md k0 t (m + 1) (ms_regs ms1) (ms_mem ms1) md1 HB HT HJ SB1);
    crt_keep HSb. }
assert (LR1 : crt_lregs cx W (ms_regs ms1) (ms_mem ms1) k).
{ apply (crt_lregs_regs cx W W regs (ms_regs ms1) mem (ms_mem ms1) k HB HLR).
  all: first [ exact (crt_sb_keep cx W mem (ms_mem ms1) HB SB1) | crt_keep HSb ]. }
pose proof HT1 as ((HJ1 & _ & _ & _ & _ & _ & _ & Hcu1 & _ & _) & _).
pose proof HJ1 as (HAR1 & _).
pose proof (crt_uri_disj B cx ly S W (ms_mem ms1) md1 t (crt_tsz (cx_n cx)) (cx_u cx) (cx_ub cx)
  HAR1 Hperm Hku0 Hnpos) as Hdisj.
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E1 _ ms1 HSb eq_refl). cbn [ss_pc].
change (mkCfg (mkst (ms_regs ms1) (Z_to_bv 64 PC_snprintf) (ms_mem ms1) (seg_rom tfibsegs)) md1)
  with (cfg_at tfibsegs PC_snprintf (ms_regs ms1) (ms_mem ms1) md1).
apply (crt_snp B IMG SNP cx ly S W (ms_regs ms1) (ms_mem ms1) md1 k0 t (m + 1) CRT_L4 ps_t2 FMT_t2
  (ManifestModel.txt_t2 (cx_ub cx) k) _ HB HT1 R1).
- unfold CRT_L4; lia.
- reflexivity.
- rewrite R10. exact H18.
- rewrite R11. exact H9.
- rewrite R12. exact L22.
- exact in_ps_t2.
- cbn [map]. rewrite R13, R14, R15, L25, Hs0, L19. unfold w64.
  rewrite (unsigned_lit_small (Z.of_nat k)) by (unfold cx_n in Hkb; lia).
  rewrite (unsigned_lit_small (cx_u cx)) by lia.
  rewrite (unsigned_lit_small (cx_u cx + Z.of_nat k)) by (unfold cx_n in Hkb; lia).
  unfold ps_t2.
  apply (frender_lplsl W (ms_mem ms1) t _ _ _ _ (Z.of_nat k) (cx_u cx) (cx_ub cx) (cx_u cx + Z.of_nat k)
    (skipn k (cx_ub cx))).
  + unfold cx_n in Hkb. lia.
  + exact Hcu1.
  + exact Hdisj.
  + exact (cstr_ok_suffix W (ms_mem ms1) (cx_u cx) (cx_ub cx) k ltac:(lia) Hcu1).
  + rewrite length_skipn. lia.
  + rewrite Nat2Z.id. reflexivity.
- rewrite (txt_len_t2 (cx_ub cx) k ltac:(lia)). unfold crt_tsz, cx_n. lia.
- apply nz_txt_t2. exact Hnzu.
- intros regs2 mem2 md2 HT2 HP2 Hout2 Hkeep2.
  pose proof HT2 as ((HJ2 & _ & _ & _ & _ & Hs02 & _ & _ & _ & _) & _ & _ & _ & H182 & _).
  pose proof (crt_lregs_pres cx W W (ms_regs ms1) regs2 (ms_mem ms1) mem2 k HB LR1 HP2 Hkeep2) as LR2.
  pose proof (fmw_resume_nr W regs2 [] mem2 CRT_L4) as HS2.
  unfold crt_J in HJ2.
  unfold cfg_at. change (w64 CRT_L4) with (Z_to_bv 64 CRT_L4).
  aj_run_to fmw_tbl_crt_ok HS2 HJ2 A_names.
  { apply awr_ok_nil. }
  lazymatch type of HS2 with context [restrict _ ?m] => rename m into ms3 end.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md3 := mdx) in * end.
  set (E3 := Ereg regs2 []) in HS2.
  crt_sb0 mem2 (ms_mem ms3) SB3.
  pose proof (fmw_reg_lit _ E3 _ ms3 1%bv CRT_L5 HS2 ltac:(vm_compute; reflexivity) ltac:(unfold CRT_L5; lia)) as Q1.
  pose proof (fmw_reg_atom _ regs2 _ _ ms3 10%bv 18%bv 18 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q10.
  pose proof (fmw_reg_atom _ regs2 _ _ ms3 11%bv 8%bv 8 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q11.
  assert (HT3 : crt_tcore B cx ly S W (ms_regs ms3) (ms_mem ms3) md3 k0 t (m + 1)).
  { apply (crt_tcore_nr B IMG cx ly S W regs2 mem2 md2 k0 t (m + 1) (ms_regs ms3) (ms_mem ms3) md3 HB HT2 HJ2 SB3);
      crt_keep HS2. }
  assert (LR3 : crt_lregs cx W (ms_regs ms3) (ms_mem ms3) k).
  { apply (crt_lregs_regs cx W W regs2 (ms_regs ms3) mem2 (ms_mem ms3) k HB LR2).
    all: first [ exact (crt_sb_keep cx W mem2 (ms_mem ms3) HB SB3) | crt_keep HS2 ]. }
  assert (Hout3 : cstr_ok tfibsegs W (ms_mem ms3) t (ManifestModel.txt_t2 (cx_ub cx) k)).
  { apply (cstr_ok_below W mem2 (ms_mem ms3)); [apply (same_below_mono _ _ _ _ SB3); lia | exact Hout2]. }
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E3 _ ms3 HS2 eq_refl). cbn [ss_pc].
  change (mkCfg (mkst (ms_regs ms3) (Z_to_bv 64 A_names) (ms_mem ms3) (seg_rom tfibsegs)) md3)
    with (cfg_at tfibsegs A_names (ms_regs ms3) (ms_mem ms3) md3).
  apply (crt_names_call B IMG NAMES cx ly S W (ms_regs ms3) (ms_mem ms3) md3 k0 t (m + 1) CRT_L5
    (ManifestModel.txt_t2 (cx_ub cx) k) _ HB HT3 Q1).
  + unfold CRT_L5; lia.
  + reflexivity.
  + cbv [CTX_lv2_locate_manifest_names CRT_L5]. repeat (first [left; reflexivity | right]).
  + rewrite Q10. exact H182.
  + rewrite Q11. exact Hs02.
  + exact Hout3.
  + rewrite (txt_len_t2 (cx_ub cx) k ltac:(lia)). unfold crt_tsz, cx_n. lia.
  + lia.
  + unfold EV_names. lia.
  + intros ly4 S4 W4 regs4 mem4 md4 HT4 HP4 H10' Hkeep4.
    pose proof (crt_lregs_pres cx W W4 (ms_regs ms3) regs4 (ms_mem ms3) mem4 k HB LR3 HP4 Hkeep4) as LR4.
    replace (m + 1 + 1) with (m + 2) in HT4 by lia.
    apply (K5 ly4 S4 W4 regs4 mem4 md4 (k0 + EV_names)).
    split; [exact HT4|]. split; [exact LR4|]. split; [exact Hkb|]. split; [exact Hrest|].
    split; [exact Hbyte|]. split; [exact Hplain|]. split; [|exact Hfk].
    rewrite H10', (ManifestModel.rt_t2 (cx_ub cx) k Hkn Hfk Hplain). reflexivity.
Qed.

(* ---- crt_segD3: CRT_L5 (0x8102c), two calls made: `bne a0, s5` falls through; snprintf (t, 3 n + 64, t3, k, uri,
   uri + k) at 0x81048; names (t, uri) at 0x81054 answers 1 (ManifestModel.rt_t3); back at CRT_L7 ---- *)
Lemma crt_segD3 : forall cx ly' S' (W' : world tfibsegs) regs' mem' md' k0 t m (k : nat),
  crt_base B cx -> crt_Lj B cx ly' S' W' regs' mem' md' k0 t m k 2 ->
  (forall ly2 S2 (W2 : world tfibsegs) regs2 mem2 md2 k2,
     crt_Lj B cx ly2 S2 W2 regs2 mem2 md2 k2 t m k 3 ->
     SRr tfibsegs W2 (cfg_at tfibsegs CRT_L7 regs2 mem2 md2) (crt_post B cx)) ->
  SRr tfibsegs W' (cfg_at tfibsegs CRT_L5 regs' mem' md') (crt_post B cx).
Proof.
intros cx ly S W regs mem md k0 t m k HB (HT & HLR & Hkb & Hrest & Hbyte & Hplain & H10 & Hfk) K7.
pose proof (AR_laws_ok tfibsegs B) as LAWS'. pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
pose proof asan_consts as (C1 & _).
pose proof HB as (_ & _ & _ & _ & Hku0 & Hlu & _).
pose proof HT as ((HJ & _ & Hsp & _ & _ & Hs0 & _ & Hcu & _ & _) & Hk & Hn1 & H9 & H18 & _ & Hperm & _).
pose proof HLR as (L19 & L20 & L21 & L22 & L23 & L24 & L25 & L27 & Lslot).
assert (Hkn : (k < length (cx_ub cx))%nat) by (unfold cx_n in Hkb; lia).
pose proof (crt_m_bound cx m k HB Hrest Hkn Hbyte Hplain) as Hmb.
assert (Hnpos : 0 < crt_tsz (cx_n cx)) by (unfold crt_tsz, cx_n; lia).
pose proof Hcu as ((_ & Hnzu) & Hu1 & Hu2 & _).
pose proof (fmw_resume_nr W regs [] mem CRT_L5) as HS.
unfold crt_J in HJ.
unfold cfg_at. change (w64 CRT_L5) with (Z_to_bv 64 CRT_L5).
assert (U10 : U (Ereg regs []) (SOff 10 0) = 1)
  by (apply U_atom; [rewrite (ew_Ereg_nat regs [] 10 10%bv eq_refl); exact H10 | lia]).
assert (U21 : U (Ereg regs []) (SOff 21 0) = 1)
  by (apply U_atom; [rewrite (ew_Ereg_nat regs [] 21 21%bv eq_refl); exact L21 | lia]).
eapply SRr_sym_branch with (c := BC_NE) (a := SOff 10 0) (b := SOff 21 0); [exact HS | intros Hb _ | intros Hb HSb].
{ exfalso. rewrite branch_ne_U, U10, U21 in Hb. discriminate Hb. }
clear HS.
aj_run_to fmw_tbl_crt_ok HSb HJ PC_snprintf.
{ apply awr_ok_nil. }
lazymatch type of HSb with context [restrict _ ?m] => rename m into ms1 end.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md1 := mdx) in * end.
set (E1 := Ereg regs []) in HSb.
crt_sb0 mem (ms_mem ms1) SB1.
pose proof (fmw_reg_lit _ E1 _ ms1 1%bv CRT_L6 HSb ltac:(vm_compute; reflexivity) ltac:(unfold CRT_L6; lia)) as R1.
pose proof (fmw_reg_atom _ regs _ _ ms1 10%bv 18%bv 18 HSb ltac:(vm_compute; reflexivity) eq_refl) as R10.
pose proof (fmw_reg_atom _ regs _ _ ms1 11%bv 9%bv 9 HSb ltac:(vm_compute; reflexivity) eq_refl) as R11.
pose proof (fmw_reg_atom _ regs _ _ ms1 12%bv 23%bv 23 HSb ltac:(vm_compute; reflexivity) eq_refl) as R12.
pose proof (fmw_reg_atom _ regs _ _ ms1 (Z_to_bv 5 13) 25%bv 25 HSb ltac:(vm_compute; reflexivity) eq_refl) as R13.
pose proof (fmw_reg_atom _ regs _ _ ms1 (Z_to_bv 5 14) 8%bv 8 HSb ltac:(vm_compute; reflexivity) eq_refl) as R14.
pose proof (fmw_reg_atom _ regs _ _ ms1 (Z_to_bv 5 15) 19%bv 19 HSb ltac:(vm_compute; reflexivity) eq_refl) as R15.
assert (HT1 : crt_tcore B cx ly S W (ms_regs ms1) (ms_mem ms1) md1 k0 t (m + 2)).
{ apply (crt_tcore_nr B IMG cx ly S W regs mem md k0 t (m + 2) (ms_regs ms1) (ms_mem ms1) md1 HB HT HJ SB1);
    crt_keep HSb. }
assert (LR1 : crt_lregs cx W (ms_regs ms1) (ms_mem ms1) k).
{ apply (crt_lregs_regs cx W W regs (ms_regs ms1) mem (ms_mem ms1) k HB HLR).
  all: first [ exact (crt_sb_keep cx W mem (ms_mem ms1) HB SB1) | crt_keep HSb ]. }
pose proof HT1 as ((HJ1 & _ & _ & _ & _ & _ & _ & Hcu1 & _ & _) & _).
pose proof HJ1 as (HAR1 & _).
pose proof (crt_uri_disj B cx ly S W (ms_mem ms1) md1 t (crt_tsz (cx_n cx)) (cx_u cx) (cx_ub cx)
  HAR1 Hperm Hku0 Hnpos) as Hdisj.
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E1 _ ms1 HSb eq_refl). cbn [ss_pc].
change (mkCfg (mkst (ms_regs ms1) (Z_to_bv 64 PC_snprintf) (ms_mem ms1) (seg_rom tfibsegs)) md1)
  with (cfg_at tfibsegs PC_snprintf (ms_regs ms1) (ms_mem ms1) md1).
apply (crt_snp B IMG SNP cx ly S W (ms_regs ms1) (ms_mem ms1) md1 k0 t (m + 2) CRT_L6 ps_t3 FMT_t3
  (ManifestModel.txt_t3 (cx_ub cx) k) _ HB HT1 R1).
- unfold CRT_L6; lia.
- reflexivity.
- rewrite R10. exact H18.
- rewrite R11. exact H9.
- rewrite R12. exact L23.
- exact in_ps_t3.
- cbn [map]. rewrite R13, R14, R15, L25, Hs0, L19. unfold w64.
  rewrite (unsigned_lit_small (Z.of_nat k)) by (unfold cx_n in Hkb; lia).
  rewrite (unsigned_lit_small (cx_u cx)) by lia.
  rewrite (unsigned_lit_small (cx_u cx + Z.of_nat k)) by (unfold cx_n in Hkb; lia).
  unfold ps_t3.
  apply (frender_lplsl W (ms_mem ms1) t _ _ _ _ (Z.of_nat k) (cx_u cx) (cx_ub cx) (cx_u cx + Z.of_nat k)
    (skipn k (cx_ub cx))).
  + unfold cx_n in Hkb. lia.
  + exact Hcu1.
  + exact Hdisj.
  + exact (cstr_ok_suffix W (ms_mem ms1) (cx_u cx) (cx_ub cx) k ltac:(lia) Hcu1).
  + rewrite length_skipn. lia.
  + rewrite Nat2Z.id. reflexivity.
- rewrite (txt_len_t3 (cx_ub cx) k ltac:(lia)). unfold crt_tsz, cx_n. lia.
- apply nz_txt_t3. exact Hnzu.
- intros regs2 mem2 md2 HT2 HP2 Hout2 Hkeep2.
  pose proof HT2 as ((HJ2 & _ & _ & _ & _ & Hs02 & _ & _ & _ & _) & _ & _ & _ & H182 & _).
  pose proof (crt_lregs_pres cx W W (ms_regs ms1) regs2 (ms_mem ms1) mem2 k HB LR1 HP2 Hkeep2) as LR2.
  pose proof (fmw_resume_nr W regs2 [] mem2 CRT_L6) as HS2.
  unfold crt_J in HJ2.
  unfold cfg_at. change (w64 CRT_L6) with (Z_to_bv 64 CRT_L6).
  aj_run_to fmw_tbl_crt_ok HS2 HJ2 A_names.
  { apply awr_ok_nil. }
  lazymatch type of HS2 with context [restrict _ ?m] => rename m into ms3 end.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md3 := mdx) in * end.
  set (E3 := Ereg regs2 []) in HS2.
  crt_sb0 mem2 (ms_mem ms3) SB3.
  pose proof (fmw_reg_lit _ E3 _ ms3 1%bv CRT_L7 HS2 ltac:(vm_compute; reflexivity) ltac:(unfold CRT_L7; lia)) as Q1.
  pose proof (fmw_reg_atom _ regs2 _ _ ms3 10%bv 18%bv 18 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q10.
  pose proof (fmw_reg_atom _ regs2 _ _ ms3 11%bv 8%bv 8 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q11.
  assert (HT3 : crt_tcore B cx ly S W (ms_regs ms3) (ms_mem ms3) md3 k0 t (m + 2)).
  { apply (crt_tcore_nr B IMG cx ly S W regs2 mem2 md2 k0 t (m + 2) (ms_regs ms3) (ms_mem ms3) md3 HB HT2 HJ2 SB3);
      crt_keep HS2. }
  assert (LR3 : crt_lregs cx W (ms_regs ms3) (ms_mem ms3) k).
  { apply (crt_lregs_regs cx W W regs2 (ms_regs ms3) mem2 (ms_mem ms3) k HB LR2).
    all: first [ exact (crt_sb_keep cx W mem2 (ms_mem ms3) HB SB3) | crt_keep HS2 ]. }
  assert (Hout3 : cstr_ok tfibsegs W (ms_mem ms3) t (ManifestModel.txt_t3 (cx_ub cx) k)).
  { apply (cstr_ok_below W mem2 (ms_mem ms3)); [apply (same_below_mono _ _ _ _ SB3); lia | exact Hout2]. }
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E3 _ ms3 HS2 eq_refl). cbn [ss_pc].
  change (mkCfg (mkst (ms_regs ms3) (Z_to_bv 64 A_names) (ms_mem ms3) (seg_rom tfibsegs)) md3)
    with (cfg_at tfibsegs A_names (ms_regs ms3) (ms_mem ms3) md3).
  apply (crt_names_call B IMG NAMES cx ly S W (ms_regs ms3) (ms_mem ms3) md3 k0 t (m + 2) CRT_L7
    (ManifestModel.txt_t3 (cx_ub cx) k) _ HB HT3 Q1).
  + unfold CRT_L7; lia.
  + reflexivity.
  + cbv [CTX_lv2_locate_manifest_names CRT_L7]. repeat (first [left; reflexivity | right]).
  + rewrite Q10. exact H182.
  + rewrite Q11. exact Hs02.
  + exact Hout3.
  + rewrite (txt_len_t3 (cx_ub cx) k ltac:(lia)). unfold crt_tsz, cx_n. lia.
  + lia.
  + unfold EV_names. lia.
  + intros ly4 S4 W4 regs4 mem4 md4 HT4 HP4 H10' Hkeep4.
    pose proof (crt_lregs_pres cx W W4 (ms_regs ms3) regs4 (ms_mem ms3) mem4 k HB LR3 HP4 Hkeep4) as LR4.
    replace (m + 2 + 1) with (m + 3) in HT4 by lia.
    apply (K7 ly4 S4 W4 regs4 mem4 md4 (k0 + EV_names)).
    split; [exact HT4|]. split; [exact LR4|]. split; [exact Hkb|]. split; [exact Hrest|].
    split; [exact Hbyte|]. split; [exact Hplain|]. split; [|exact Hfk].
    rewrite H10', (ManifestModel.rt_t3 (cx_ub cx) k Hkn Hfk Hplain). reflexivity.
Qed.

(* ---- crt_segD4: CRT_L7 (0x81058), three calls made: `bne a0, s5` falls through; snprintf (t, 3 n + 64, t1x, k,
   uri, uri + k) at 0x81074; as_ruled (t, uri) at 0x81080; at CRT_L9 the split point's four calls are made and the
   split points from k + 1 on add the rest ---- *)
Lemma crt_segD4 : forall cx ly' S' (W' : world tfibsegs) regs' mem' md' k0 t m (k : nat),
  crt_base B cx -> crt_Lj B cx ly' S' W' regs' mem' md' k0 t m k 3 ->
  (forall ly2 S2 (W2 : world tfibsegs) regs2 mem2 md2 k2,
     crt_I B cx ly2 S2 W2 regs2 mem2 md2 k2 t (m + 4) k ->
     SRr tfibsegs W2 (cfg_at tfibsegs CRT_L9 regs2 mem2 md2) (crt_post B cx)) ->
  SRr tfibsegs W' (cfg_at tfibsegs CRT_L7 regs' mem' md') (crt_post B cx).
Proof.
intros cx ly S W regs mem md k0 t m k HB (HT & HLR & Hkb & Hrest & Hbyte & Hplain & H10 & Hfk) K9.
pose proof (AR_laws_ok tfibsegs B) as LAWS'. pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
pose proof asan_consts as (C1 & _).
pose proof HB as (_ & _ & _ & _ & Hku0 & Hlu & _).
pose proof HT as ((HJ & _ & Hsp & _ & _ & Hs0 & _ & Hcu & _ & _) & Hk & Hn1 & H9 & H18 & _ & Hperm & _).
pose proof HLR as (L19 & L20 & L21 & L22 & L23 & L24 & L25 & L27 & Lslot).
assert (Hkn : (k < length (cx_ub cx))%nat) by (unfold cx_n in Hkb; lia).
pose proof (crt_m_bound cx m k HB Hrest Hkn Hbyte Hplain) as Hmb.
assert (Hnpos : 0 < crt_tsz (cx_n cx)) by (unfold crt_tsz, cx_n; lia).
pose proof Hcu as ((_ & Hnzu) & Hu1 & Hu2 & _).
pose proof (fmw_resume_nr W regs [] mem CRT_L7) as HS.
unfold crt_J in HJ.
unfold cfg_at. change (w64 CRT_L7) with (Z_to_bv 64 CRT_L7).
assert (U10 : U (Ereg regs []) (SOff 10 0) = 1)
  by (apply U_atom; [rewrite (ew_Ereg_nat regs [] 10 10%bv eq_refl); exact H10 | lia]).
assert (U21 : U (Ereg regs []) (SOff 21 0) = 1)
  by (apply U_atom; [rewrite (ew_Ereg_nat regs [] 21 21%bv eq_refl); exact L21 | lia]).
eapply SRr_sym_branch with (c := BC_NE) (a := SOff 10 0) (b := SOff 21 0); [exact HS | intros Hb _ | intros Hb HSb].
{ exfalso. rewrite branch_ne_U, U10, U21 in Hb. discriminate Hb. }
clear HS.
aj_run_to fmw_tbl_crt_ok HSb HJ PC_snprintf.
{ apply awr_ok_nil. }
lazymatch type of HSb with context [restrict _ ?m] => rename m into ms1 end.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md1 := mdx) in * end.
set (E1 := Ereg regs []) in HSb.
crt_sb0 mem (ms_mem ms1) SB1.
pose proof (fmw_reg_lit _ E1 _ ms1 1%bv CRT_L8 HSb ltac:(vm_compute; reflexivity) ltac:(unfold CRT_L8; lia)) as R1.
pose proof (fmw_reg_atom _ regs _ _ ms1 10%bv 18%bv 18 HSb ltac:(vm_compute; reflexivity) eq_refl) as R10.
pose proof (fmw_reg_atom _ regs _ _ ms1 11%bv 9%bv 9 HSb ltac:(vm_compute; reflexivity) eq_refl) as R11.
pose proof (fmw_reg_atom _ regs _ _ ms1 12%bv 24%bv 24 HSb ltac:(vm_compute; reflexivity) eq_refl) as R12.
pose proof (fmw_reg_atom _ regs _ _ ms1 (Z_to_bv 5 13) 25%bv 25 HSb ltac:(vm_compute; reflexivity) eq_refl) as R13.
pose proof (fmw_reg_atom _ regs _ _ ms1 (Z_to_bv 5 14) 8%bv 8 HSb ltac:(vm_compute; reflexivity) eq_refl) as R14.
pose proof (fmw_reg_atom _ regs _ _ ms1 (Z_to_bv 5 15) 19%bv 19 HSb ltac:(vm_compute; reflexivity) eq_refl) as R15.
assert (HT1 : crt_tcore B cx ly S W (ms_regs ms1) (ms_mem ms1) md1 k0 t (m + 3)).
{ apply (crt_tcore_nr B IMG cx ly S W regs mem md k0 t (m + 3) (ms_regs ms1) (ms_mem ms1) md1 HB HT HJ SB1);
    crt_keep HSb. }
assert (LR1 : crt_lregs cx W (ms_regs ms1) (ms_mem ms1) k).
{ apply (crt_lregs_regs cx W W regs (ms_regs ms1) mem (ms_mem ms1) k HB HLR).
  all: first [ exact (crt_sb_keep cx W mem (ms_mem ms1) HB SB1) | crt_keep HSb ]. }
pose proof HT1 as ((HJ1 & _ & _ & _ & _ & _ & _ & Hcu1 & _ & _) & _).
pose proof HJ1 as (HAR1 & _).
pose proof (crt_uri_disj B cx ly S W (ms_mem ms1) md1 t (crt_tsz (cx_n cx)) (cx_u cx) (cx_ub cx)
  HAR1 Hperm Hku0 Hnpos) as Hdisj.
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E1 _ ms1 HSb eq_refl). cbn [ss_pc].
change (mkCfg (mkst (ms_regs ms1) (Z_to_bv 64 PC_snprintf) (ms_mem ms1) (seg_rom tfibsegs)) md1)
  with (cfg_at tfibsegs PC_snprintf (ms_regs ms1) (ms_mem ms1) md1).
apply (crt_snp B IMG SNP cx ly S W (ms_regs ms1) (ms_mem ms1) md1 k0 t (m + 3) CRT_L8 ps_t1x FMT_t1x
  (ManifestModel.txt_t1x (cx_ub cx) k) _ HB HT1 R1).
- unfold CRT_L8; lia.
- reflexivity.
- rewrite R10. exact H18.
- rewrite R11. exact H9.
- rewrite R12. exact L24.
- exact in_ps_t1x.
- cbn [map]. rewrite R13, R14, R15, L25, Hs0, L19. unfold w64.
  rewrite (unsigned_lit_small (Z.of_nat k)) by (unfold cx_n in Hkb; lia).
  rewrite (unsigned_lit_small (cx_u cx)) by lia.
  rewrite (unsigned_lit_small (cx_u cx + Z.of_nat k)) by (unfold cx_n in Hkb; lia).
  unfold ps_t1x.
  apply (frender_lplsl W (ms_mem ms1) t _ _ _ _ (Z.of_nat k) (cx_u cx) (cx_ub cx) (cx_u cx + Z.of_nat k)
    (skipn k (cx_ub cx))).
  + unfold cx_n in Hkb. lia.
  + exact Hcu1.
  + exact Hdisj.
  + exact (cstr_ok_suffix W (ms_mem ms1) (cx_u cx) (cx_ub cx) k ltac:(lia) Hcu1).
  + rewrite length_skipn. lia.
  + rewrite Nat2Z.id. reflexivity.
- rewrite (txt_len_t1x (cx_ub cx) k ltac:(lia)). unfold crt_tsz, cx_n. lia.
- apply nz_txt_t1x. exact Hnzu.
- intros regs2 mem2 md2 HT2 HP2 Hout2 Hkeep2.
  pose proof HT2 as ((HJ2 & _ & _ & _ & _ & Hs02 & _ & _ & _ & _) & _ & _ & _ & H182 & _).
  pose proof (crt_lregs_pres cx W W (ms_regs ms1) regs2 (ms_mem ms1) mem2 k HB LR1 HP2 Hkeep2) as LR2.
  pose proof (fmw_resume_nr W regs2 [] mem2 CRT_L8) as HS2.
  unfold crt_J in HJ2.
  unfold cfg_at. change (w64 CRT_L8) with (Z_to_bv 64 CRT_L8).
  aj_run_to fmw_tbl_crt_ok HS2 HJ2 A_as_ruled.
  { apply awr_ok_nil. }
  lazymatch type of HS2 with context [restrict _ ?m] => rename m into ms3 end.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md3 := mdx) in * end.
  set (E3 := Ereg regs2 []) in HS2.
  crt_sb0 mem2 (ms_mem ms3) SB3.
  pose proof (fmw_reg_lit _ E3 _ ms3 1%bv CRT_L9 HS2 ltac:(vm_compute; reflexivity) ltac:(unfold CRT_L9; lia)) as Q1.
  pose proof (fmw_reg_atom _ regs2 _ _ ms3 10%bv 18%bv 18 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q10.
  pose proof (fmw_reg_atom _ regs2 _ _ ms3 11%bv 8%bv 8 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q11.
  assert (HT3 : crt_tcore B cx ly S W (ms_regs ms3) (ms_mem ms3) md3 k0 t (m + 3)).
  { apply (crt_tcore_nr B IMG cx ly S W regs2 mem2 md2 k0 t (m + 3) (ms_regs ms3) (ms_mem ms3) md3 HB HT2 HJ2 SB3);
      crt_keep HS2. }
  assert (LR3 : crt_lregs cx W (ms_regs ms3) (ms_mem ms3) k).
  { apply (crt_lregs_regs cx W W regs2 (ms_regs ms3) mem2 (ms_mem ms3) k HB LR2).
    all: first [ exact (crt_sb_keep cx W mem2 (ms_mem ms3) HB SB3) | crt_keep HS2 ]. }
  assert (Hout3 : cstr_ok tfibsegs W (ms_mem ms3) t (ManifestModel.txt_t1x (cx_ub cx) k)).
  { apply (cstr_ok_below W mem2 (ms_mem ms3)); [apply (same_below_mono _ _ _ _ SB3); lia | exact Hout2]. }
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E3 _ ms3 HS2 eq_refl). cbn [ss_pc].
  change (mkCfg (mkst (ms_regs ms3) (Z_to_bv 64 A_as_ruled) (ms_mem ms3) (seg_rom tfibsegs)) md3)
    with (cfg_at tfibsegs A_as_ruled (ms_regs ms3) (ms_mem ms3) md3).
  apply (crt_asr_call B IMG ASR cx ly S W (ms_regs ms3) (ms_mem ms3) md3 k0 t (m + 3) CRT_L9
    (ManifestModel.txt_t1x (cx_ub cx) k) _ HB HT3 Q1).
  + unfold CRT_L9; lia.
  + reflexivity.
  + cbv [CTX_as_ruled CRT_L9]. repeat (first [left; reflexivity | right]).
  + rewrite Q10. exact H182.
  + rewrite Q11. exact Hs02.
  + exact Hout3.
  + rewrite (txt_len_t1x (cx_ub cx) k ltac:(lia)). unfold crt_tsz, cx_n. lia.
  + lia.
  + unfold EV_as_ruled, EV_names. lia.
  + intros ly4 S4 W4 regs4 mem4 md4 HT4 HP4 Hkeep4.
    pose proof (crt_lregs_pres cx W W4 (ms_regs ms3) regs4 (ms_mem ms3) mem4 k HB LR3 HP4 Hkeep4) as LR4.
    replace (m + 3 + 1) with (m + 4) in HT4 by lia.
    apply (K9 ly4 S4 W4 regs4 mem4 md4 (k0 + EV_as_ruled)).
    split; [exact HT4|]. split; [exact LR4|]. split; [exact Hkb|].
    split; [rewrite (crt_rest_stepP cx k Hkn Hbyte Hplain) in Hrest; lia | exact Hfk].
Qed.
End D.
