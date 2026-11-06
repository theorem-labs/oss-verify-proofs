(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v, with its module paths and module names changed; 157 of its 204 lines of code are new or changed and 1326 lines of the source are left out. *)
(* fs program part, lane ENTRY, IMAGE B (fs.asan-ubsan, pinned sha256 5ac5ce0954f8...): the canonical boundary state of
   the LLVMFuzzerTestOneInput walk (lib/B/FSW_entry_defs.v fe_ss) holds at any machine state that has the eleven saved
   words at s0 - 8 .. s0 - 88, the live class-0 fake frame with its flag word, and s0 / s2 / s8 / s9 at the entry sp /
   the frame / the frame / its shadow: a segment re-establishes it after a runtime call, after a program call, or at a
   branch join, from the journal's and AR's facts alone. The proof is entry_st_ok_full (Reusable/YI04.v) with the three
   regions' facts; nothing in it is image-specific beyond the B kit it loads. Also `len`'s shadow byte layer (fe_lensh,
   fe_ss_z: the ENTRY owner's A text of 06:53Z, lensh-wip): the chunk added before a run (fe_ss_z_ok, lib/B/YFeu.v
   st_ok_set_region) and read back after it (fe_lensh_of, fe_drop_z), the z regions' windows (fe_wrange_z, fe_frame_z,
   fe_awr_z), the byte across a callee journal (fe_lensh_journal, fe_lensh_npstat) and decode_spec_ff's
   range_addressable premise from it (fe_lensh_ra).
   rule 24: proves function LLVMFuzzerTestOneInput (shared kit of the entry walk's segments; reuse search:
   proof-index LLVMFuzzerTestOneInput, ported from a working branch 08ad70da3bf).
   Ported from: lib/A/FSW_entry_canon.v (a working branch 0d34d65d2b7), A's names, the imports moved to
   lib/B. RELOC-B hypotheses: none. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q YC5d YCbp.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSW_K FSW_ret FSW_frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YCfn FSH_Harness FSH_Fn_entry FSW_entry_defs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YFeu YF0x FSW_pstat_store.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

Lemma fe_extra_len : forall cx, length (fe_extra cx) = 14%nat.
Proof. reflexivity. Qed.
(* an env whose extra list starts with fe_extra carries fe_E (later segments append atoms 46, ... in xs) *)
Lemma fe_extra_atom : forall cx regs xs j, (j < 14)%nat ->
  ew (Ereg regs (fe_extra cx ++ xs)) (32 + j) = nth j (fe_extra cx) (Z_to_bv 64 0).
Proof. intros cx regs xs j Hj. rewrite ew_Ereg_extra. apply app_nth1. rewrite fe_extra_len. exact Hj. Qed.
Lemma fe_E_Ereg : forall cx regs xs, fe_E cx (Ereg regs (fe_extra cx ++ xs)).
Proof. intros cx regs xs j Hj. exact (fe_extra_atom cx regs xs j Hj). Qed.

(* the regions are well formed whatever chunks below the flag word the caller adds, as long as regions_wf says so;
   the common case cs = [] and cs = [len] are by computation *)
Lemma fe_regions_wf_nil : regions_wf (fe_regions []) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma fe_regions_wf_len_atom : forall n, regions_wf (fe_regions [fe_len_atom n]) = true.
Proof. intros n. vm_compute. reflexivity. Qed.
Lemma fe_regions_wf_len_lit : forall v, regions_wf (fe_regions [fe_len_lit v]) = true.
Proof. intros v. vm_compute. reflexivity. Qed.

Lemma fe_canon : forall cx ly3 S3 U3 (W3 : world tfibsegs) mem3 md3 regs' xs r cs,
  ARU tfibsegs B ly3 S3 U3 W3 mem3 md3 -> In (0, c_fpos cx) (frames S3) ->
  ly_F ly3 = ly_F (c_ly cx) ->
  YK11.getr regs' 8%bv = Z_to_bv 64 (fe_sp0 cx) -> YK11.getr regs' 24%bv = Z_to_bv 64 (fe_F cx) ->
  YK11.getr regs' 18%bv = Z_to_bv 64 (fe_F cx) -> YK11.getr regs' 25%bv = Z_to_bv 64 (fe_SF cx) ->
  fe_sp0 cx mod 16 = 0 -> alloc_ceiling <= fe_sp0 cx - 88 -> fe_sp0 cx <= 2 ^ 47 ->
  (forall a, fe_sp0 cx - 88 <= a < fe_sp0 cx -> apresent (w_H W3) mem3 a) ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs' (fe_extra cx ++ xs)) (mrestrict (w_H W3) mem3) (fe_sp0 cx)) fe_sv_chunks ->
  rdword (aview tfibsegs (w_H W3) mem3) (fe_F cx + 56) = Some (fe_FL cx) ->
  regions_wf (fe_regions cs) = true ->
  Forall (fun c => 0 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= 56) cs ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs' (fe_extra cx ++ xs)) (mrestrict (w_H W3) mem3) (fe_F cx)) cs ->
  st_ok tfibsegs (Ereg regs' (fe_extra cx ++ xs)) (fe_ss r cs)
    (restrict (w_H W3) (mkst regs' (Z_to_bv 64 r) mem3 (seg_rom tfibsegs))).
Proof.
intros cx ly3 S3 U3 W3 mem3 md3 regs' xs r cs HARU Hin ELY R8 R24 R18 R25 Hal16 Hceil H47 Hpres Hsv Hflag Hwf Hcin Hcs.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (ARU_AR tfibsegs B ly3 S3 U3 W3 mem3 md3 HARU) as HAR.
assert (EF : frame_addr ly3 0 (c_fpos cx) = fe_F cx) by (unfold fe_F, frame_addr; rewrite ELY; reflexivity).
assert (EFL : flag_addr ly3 0 (c_fpos cx) = fe_FL cx) by (unfold fe_FL, flag_addr; rewrite ELY; reflexivity).
destruct (al_frames _ _ LAWS ly3 S3 W3 (unpoison U3 mem3) md3 0 (c_fpos cx) HAR Hin) as (Hal32 & Happ & Hfp & Hsp).
destruct (frames_bounds tfibsegs B LAWS ly3 S3 W3 (unpoison U3 mem3) md3 0 (c_fpos cx) HAR Hin) as (H4096 & Hfc & _).
destruct (al_flag _ _ LAWS ly3 S3 W3 (unpoison U3 mem3) md3 0 (c_fpos cx) HAR Hin) as (_ & _ & Hflapp & Hflc).
rewrite EF in Hal32, Happ, Hfp, Hsp, H4096, Hfc. rewrite EFL in Hflapp, Hflc.
unfold in_app in Hflapp.
assert (Hfb : fs_frame_bytes 0 = 64) by reflexivity. rewrite Hfb in Happ, Hfp, Hsp, Hfc.
change (64 / 8) with 8 in Hsp.
set (F := fe_F cx) in *. set (SF := fe_SF cx) in *.
assert (ESF : SF = shadow_addr F) by reflexivity.
pose proof (shadow_addr_bounds F ltac:(unfold kHighMemEnd in *; lia)) as (Hs1 & Hs2).
pose proof (shadow_addr_bounds (F + 63) ltac:(unfold kHighMemEnd in *; lia)) as (_ & Hs4).
assert (Hs5 : shadow_addr F + 7 <= shadow_addr (F + 63)) by (unfold shadow_addr; Z.div_mod_to_equations; lia).
set (E := Ereg regs' (fe_extra cx ++ xs)).
assert (E8 : bv_unsigned (ew E 8) = fe_sp0 cx)
  by (subst E; rewrite (ew_Ereg_nat regs' (fe_extra cx ++ xs) 8 8%bv eq_refl), R8; apply wz; lia).
assert (E24 : bv_unsigned (ew E 24) = F)
  by (subst E; rewrite (ew_Ereg_nat regs' (fe_extra cx ++ xs) 24 24%bv eq_refl), R24; apply wz; lia).
assert (E18 : bv_unsigned (ew E 18) = F)
  by (subst E; rewrite (ew_Ereg_nat regs' (fe_extra cx ++ xs) 18 18%bv eq_refl), R18; apply wz; lia).
assert (E25 : bv_unsigned (ew E 25) = SF)
  by (subst E; rewrite (ew_Ereg_nat regs' (fe_extra cx ++ xs) 25 25%bv eq_refl), R25; apply wz; lia).
assert (E44 : ew E 44 = Z_to_bv 64 (fe_FL cx)) by (subst E; change 44%nat with (32 + 12)%nat; rewrite (fe_extra_atom cx regs' xs 12) by lia; reflexivity).
subst E.
rewrite restrict_mkst_fx. unfold fe_ss. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- exact Hwf.
- unfold fe_regions. constructor; [|constructor; [|constructor; [|constructor]]].
  + (* the frame *)
    unfold region_ok, fe_frame_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E24. split; [lia|]. split; [lia|]. split.
    * intros o Ho. apply (apresent_writable tfibsegs).
      destruct (Hfp (F + o) ltac:(lia)) as (Hp & Hno).
      exact (fsw_apresent_notowned B ly3 S3 U3 W3 mem3 md3 (F + o) HARU ltac:(lia) Hno Hp).
    * constructor; [|exact Hcs].
      apply (chunk_ok_val tfibsegs _ _ F 56 8 (SOff 44 0) (fe_FL cx));
        [rewrite fsw_SOff0, E44; reflexivity | cbn; unfold kLowShadowBeg, kHighMemBeg in *; lia | cbn; lia |].
      exact (val_mem_of_rdword tfibsegs (w_H W3) mem3 _ _ Hflag).
  + (* its shadow *)
    unfold region_ok, fe_shadow_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E25. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable tfibsegs).
    destruct (Hsp o ltac:(lia)) as (Hp & Hno). rewrite <- ESF in Hp, Hno.
    exact (fsw_apresent_notowned B ly3 S3 U3 W3 mem3 md3 (SF + o) HARU ltac:(lia) Hno Hp).
  + (* the saved words *)
    unfold region_ok, fs_ret_s0_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E8. split; [lia|]. split; [lia|]. split; [|exact Hsv].
    intros o Ho. apply (apresent_writable tfibsegs). apply Hpres. lia.
- apply pairwise_disjoint_of_extents. unfold fe_regions, fe_frame_region, fe_shadow_region, fs_ret_s0_region,
    extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E24, E25, E8.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E8, E24, E18. change (2 ^ 4) with 16. change (2 ^ 5) with 32.
  split; [split; [lia | split; [exact Hal16 | lia]]|].
  split; [split; [lia | split; [exact Hal32 | lia]]|].
  split; [split; [lia | split; [exact Hal32 | lia]]|]. exact I.
Qed.

(* ---- `len`'s shadow byte (FSW_entry_defs.v fe_lensh / fe_ss_z): the canonical state with the byte as a chunk, the
   byte from a state that has that chunk, the byte across a callee's journal (the frames clause keeps a live frame's
   shadow), and decode_spec_ff's range_addressable premise from it ---- *)
Lemma fe_denot_lit0 : forall E, sv_denot E (SLit 0) = Z_to_bv 64 0.
Proof.
intros E. apply bv_eq. rewrite (wz 0) by lia. change (bv_unsigned (sv_denot E (SLit 0))) with (U E (SLit 0)).
rewrite U_SLit. reflexivity.
Qed.
Lemma fe_ss_z_ok : forall cx E r cs (H : word -> bool) ms,
  st_ok tfibsegs E (fe_ss r cs) (restrict H ms) -> bv_unsigned (ew E 25) = fe_SF cx ->
  aview tfibsegs H (ms_mem ms) (fe_SF cx + 4) = Some 0 ->
  st_ok tfibsegs E (fe_ss_z r cs) (restrict H ms).
Proof.
intros cx E r cs H ms HS E25 Hz.
change (fe_ss_z r cs) with (mkSS (ss_pc (fe_ss r cs)) (ss_regs (fe_ss r cs))
  (YFeu.smem_upd (ss_mem (fe_ss r cs)) 1 fe_shadow_region_z) (ss_resv (fe_ss r cs)) (ss_facts (fe_ss r cs))).
apply (YFeu.st_ok_set_region E (fe_ss r cs) (restrict H ms) 1 fe_shadow_region fe_shadow_region_z HS eq_refl).
- unfold YFeu.same_frame. repeat split.
- vm_compute. reflexivity.
- constructor; [|constructor].
  cbn [YP09.r_base fe_shadow_region_z base_val]. rewrite E25.
  apply (chunk_ok_val tfibsegs E _ _ 4 1 (SLit 0) 0); [exact (fe_denot_lit0 E) | cbn; lia | cbn; lia |].
  intros kk Hkk. change (N.to_nat 1) with 1%nat in Hkk. assert (kk = 0%nat) as -> by lia.
  cbn [Z.of_nat]. rewrite Z.add_0_r. change (ms_mem (restrict H ms)) with (mrestrict H (ms_mem ms)).
  rewrite (YF0x.aview_byte H (ms_mem ms) (fe_SF cx + 4) 0 Hz). reflexivity.
Qed.
Lemma fe_lensh_of : forall cx E ss (H : word -> bool) ms,
  st_ok tfibsegs E ss (restrict H ms) -> nth_error (ss_mem ss) 1 = Some fe_shadow_region_z ->
  bv_unsigned (ew E 25) = fe_SF cx -> aview tfibsegs H (ms_mem ms) (fe_SF cx + 4) = Some 0.
Proof.
intros cx E ss H ms HS H1 E25.
pose proof (YF0x.st_ok_chunk_val H E ss ms 1 fe_shadow_region_z 0 4 1 (SLit 0) 0 HS H1 eq_refl (fe_denot_lit0 E)
  ltac:(cbn; lia) ltac:(cbn; lia)) as Hv.
cbn [YP09.r_base fe_shadow_region_z base_val] in Hv. rewrite E25 in Hv.
pose proof (Hv 0%nat ltac:(change (N.to_nat 1) with 1%nat; lia)) as H0. cbn [Z.of_nat] in H0. rewrite Z.add_0_r in H0.
unfold aview. rewrite H0. vm_compute. reflexivity.
Qed.
(* the chunk dropped again after a run, so that the run's end state has the canonical shadow region *)
Lemma fe_drop_z : forall E ss (H : word -> bool) ms,
  st_ok tfibsegs E ss (restrict H ms) -> nth_error (ss_mem ss) 1 = Some fe_shadow_region_z ->
  st_ok tfibsegs E (mkSS (ss_pc ss) (ss_regs ss) (YFeu.smem_upd (ss_mem ss) 1 fe_shadow_region) (ss_resv ss)
    (ss_facts ss)) (restrict H ms).
Proof.
intros E ss H ms HS H1.
apply (YFeu.st_ok_set_region E ss (restrict H ms) 1 fe_shadow_region_z fe_shadow_region HS H1).
- unfold YFeu.same_frame. repeat split.
- vm_compute. reflexivity.
- constructor.
Qed.
Lemma fe_wrange_z : forall E cs a, in_wrange E (fe_regions_z cs) a -> in_wrange E (fe_regions cs) a.
Proof.
intros E cs a (r & Hin & Ha). destruct Hin as [<-|[<-|[<-|[]]]].
- exists (fe_frame_region cs). split; [left; reflexivity | exact Ha].
- exists fe_shadow_region. split; [right; left; reflexivity | exact Ha].
- exists (fs_ret_s0_region (-88) 0 fe_sv_chunks). split; [right; right; left; reflexivity | exact Ha].
Qed.
Lemma fe_frame_z : forall E cs m m', frame_of E (fe_regions_z cs) m m' -> frame_of E (fe_regions cs) m m'.
Proof. intros E cs m m' HF x Hx. apply HF. intros Hz. exact (Hx (fe_wrange_z E cs _ Hz)). Qed.
Lemma fe_awr_z : forall E cs STK sp0 FP bl0 blc ly own fr0,
  awr_ok tfibsegs B E (fe_regions cs) STK sp0 FP bl0 blc ly own fr0 ->
  awr_ok tfibsegs B E (fe_regions_z cs) STK sp0 FP bl0 blc ly own fr0.
Proof. intros E cs STK sp0 FP bl0 blc ly own fr0 HA a Ha. exact (HA a (fe_wrange_z E cs a Ha)). Qed.
Lemma fe_lensh_npstat : forall cx, 0 <= fe_F cx -> ~ inFP FS_PSTAT_FP (fe_SF cx + 4).
Proof.
intros cx H0 Hf. apply B.FSW_pstat_store.pstat_bounds in Hf. unfold fe_SF, shadow_addr, SHADOW_OFF in Hf.
pose proof (Z.div_pos (fe_F cx) 8 ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma fe_lensh_journal : forall cx STK sp0 FP ly S (W : world tfibsegs) mem md own ly' S' W' mem' md' k,
  ajournal tfibsegs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  In (0, c_fpos cx) (frames S) -> frame_addr ly 0 (c_fpos cx) = fe_F cx -> ~ inFP FP (fe_SF cx + 4) ->
  aview tfibsegs (w_H W) mem (fe_SF cx + 4) = Some 0 -> aview tfibsegs (w_H W') mem' (fe_SF cx + 4) = Some 0.
Proof.
intros cx STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ Hin EF Hnfp Hz.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G4 & _).
rewrite (G4 0 (c_fpos cx) (fe_SF cx + 4) Hin); [exact Hz | | exact Hnfp].
right. unfold in_zr. cbn [fst snd]. rewrite EF. change (fs_frame_bytes 0 / 8) with 8. unfold fe_SF. lia.
Qed.
Lemma fe_lensh_ra : forall cx (H : word -> bool) m, fe_F cx mod 8 = 0 ->
  aview tfibsegs H m (fe_SF cx + 4) = Some 0 ->
  range_addressable (aview tfibsegs H m) SHADOW_OFF (fe_F cx + 32) 8.
Proof.
intros cx H m Hal Hz x Hx. exists 0. split; [|left; reflexivity].
replace (shadow_of_addr SHADOW_OFF x) with (fe_SF cx + 4); [exact Hz|].
unfold shadow_of_addr, fe_SF, shadow_addr. Z.div_mod_to_equations. lia.
Qed.
End c.
