(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: IMAGE B (fs.asan-ubsan) walk of parse_value 0x82fcc, stage lemmas. HEADER: see
   FSW_parse_value_holds.v (the composition into parse_value_spec k, the rule-24 line, the reuse search, the port
   sources, every pc walked and every report site). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSW_K FSW_frame FSW_ret FSH_Fn_reader FSW_rd.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.Prog Require Import FSW_parse_value_tbl.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YN2j.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved.
   YI14 is required (not imported) so that the second probe names a loaded class. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YI14.
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Ltac pv_cs := unfold acallee_saved; lazymatch goal with |- context [bv_unsigned ?q] =>
  let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end; lia.

(* ================= pure facts ================= *)
(* ported from image A's walk (a working branch c4ac4207dc3 lib/A/FSH_parse_value.v pv_grant), with
   lib/A/FSH_Fn_entry.v's fs_fake_granted inlined (no lib/A entry file is loaded here): the class-0 fake frame is
   granted, at most FRL_parse_value k = 2 + k <= 4 frames are live at the call *)
Lemma pv_count_le : forall cid (l : list (Z * Z)), count_cid cid l <= Z.of_nat (length l).
Proof.
intros cid l. induction l as [|[c p] t IH]; cbn [count_cid length]; [lia|].
destruct (c =? cid); lia.
Qed.
Lemma pv_grant : forall (k : nat) (l : list (Z * Z)), (k <= 2)%nat ->
  Z.of_nat (length l) <= FRL_parse_value (Z.of_nat k) -> count_cid 0 l < fs_frames 0.
Proof.
intros k l Hk Hl. pose proof (pv_count_le 0 l) as Hle.
assert (E : fs_frames 0 = 16384) by (vm_compute; reflexivity). rewrite E.
unfold FRL_parse_value in Hl. lia.
Qed.

(* the entry state: fs's T state (sp atom 2, the shadow-base cells) with the use-after-return flag's GOT word and cell *)
Definition pv_ss0 : sstate := fss0T_args A_parse_value 160 fs_uar_regions [].
(* MEASURED (vm_compute): at the call of __asan_stack_malloc_0 (0x8303c -> 0x3d4f4) sp = s1 = the re-aligned
   SAlu AND (SOff 2 (-160)) (SLit (-32)), a0 = 64, a2 = 1 (the flag: `beqz a2` 0x83034 not taken), s3 = a1 (v),
   s4 = a0 (q), s7 = the shadow base atom 32, ra = 0x83040; the prologue saved ra, s0 .. s11 at sp0 - 8 .. sp0 - 104
   and stored 0 at sp0 - 160 (B's prologue 0x82fcc .. 0x8303c is A's 0x82f9c .. 0x8300c moved by 0x30, instruction
   for instruction) *)
Definition pv_ss1 : sstate := Eval vm_compute in fst (sym_run_toN tfibsegs pv_tbl FUEL PC_stack_malloc_0 pv_ss0).

(* ---- the symbolic state at the return address r of __asan_stack_malloc_<cid> in a re-aligned fake-frame caller whose
   journal top sp0 may lie ABOVE its s0 value s (a raised window: parse_value writes pj_parse's struct pj_in above its
   own sp). Ported verbatim from image A's walk (c4ac4207dc3 lib/A/FSH_parse_value.v pv_resume_regions / pv_resume_ss /
   pv_resume_sm, itself a Theorem Labs lane's crcs_resume_sm with the journal top sp0 and the s0 value s separated). ---- *)
Definition pv_resume_regions (lo hi : Z) (cs : list YP09.chunk) (nsl : nat) (slo shi : Z) (nF : nat) (eflag : sv)
  (cid : Z) : list YP09.region :=
  [YP09.mkRegion (Some 8%nat) lo hi lo hi cs;
   YP09.mkRegion (Some nsl) slo shi slo shi [];
   YP09.mkRegion (Some nF) 0 (fs_frame_bytes cid) 0 (fs_frame_bytes cid) [YP09.mkChunk (fs_frame_bytes cid - 8) (CVal 8 eflag)]].
Definition pv_resume_ss (r lo hi : Z) (cs : list YP09.chunk) (nsl : nat) (slo shi : Z) (nF : nat) (eflag : sv)
  (cid : Z) : sstate :=
  mkSS r sr_atoms (pv_resume_regions lo hi cs nsl slo shi nF eflag cid) None
    (mkFacts [(8%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (nF, mkAF 4096 (2 ^ 47) 5)] [] []).

Section R. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Lemma pv_resume_sm : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc S2 U (W : world tfibsegs) memT mdc mem2 md2 k
  cid pos s sp1 regs2 extra r lo hi cs nsl slo shi nF eflag,
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 ((cid, pos) :: own) lyc S2 W (unpoison U mem2) md2 k ->
  ARU tfibsegs B lyc S2 U W mem2 md2 -> ARU tfibsegs B lyc Sc U W memT mdc ->
  acall_kept tfibsegs B lyc Sc W (unpoison U memT) W (unpoison U mem2) (sp1 - ESTACK) sp1 (fun _ => False) ->
  In (cid, pos) (frames S2) -> 0 <= cid ->
  bv_unsigned (ew (Ereg regs2 extra) 8) = s -> bv_unsigned (ew (Ereg regs2 extra) nsl) = sp1 ->
  bv_unsigned (ew (Ereg regs2 extra) nF) = frame_addr lyc cid pos ->
  sv_denot (Ereg regs2 extra) eflag = Z_to_bv 64 (flag_addr lyc cid pos) ->
  rdword (aview tfibsegs (w_H W) mem2) (frame_addr lyc cid pos + fs_frame_bytes cid - 8) = Some (flag_addr lyc cid pos) ->
  lo <= hi <= 0 -> sp1 <= s + lo -> slo <= shi -> sp1 + shi <= s + lo -> sp0 - STK <= sp1 + slo -> s <= sp0 ->
  s mod 16 = 0 ->
  regions_wf (pv_resume_regions lo hi cs nsl slo shi nF eflag cid) = true ->
  Forall (fun c => lo <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= hi) cs ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs2 extra) (mrestrict (w_H W) memT) s) cs ->
  st_ok tfibsegs (Ereg regs2 extra) (pv_resume_ss r lo hi cs nsl slo shi nF eflag cid)
    (restrict (w_H W) (mkst regs2 (Z_to_bv 64 r) mem2 (seg_rom tfibsegs))).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc S2 U W memT mdc mem2 md2 k cid pos s sp1 regs2 extra r lo hi cs nsl slo
  shi nF eflag HJ HARU2 HARUc Hkept Hin Hc0 E8 Esl EF Eflag Hflag Hlohi Hlo Hsl Hsh Hsw Hs0 Hal16s Hwf Hcin Hcs.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (ARU_AR tfibsegs B lyc S2 U W mem2 md2 HARU2) as HAR2.
destruct (al_frames _ _ LAWS lyc S2 W (unpoison U mem2) md2 cid pos HAR2 Hin) as (Hal32 & _ & Hfp & _).
destruct (frames_bounds tfibsegs B LAWS lyc S2 W (unpoison U mem2) md2 cid pos HAR2 Hin) as (H4096 & Hfc & _).
destruct (al_flag _ _ LAWS lyc S2 W (unpoison U mem2) md2 cid pos HAR2 Hin) as (_ & _ & Hflapp & Hflc).
pose proof (fs_frame_bytes_pos cid Hc0) as Hfb.
destruct Hkept as (K1 & _).
set (F := frame_addr lyc cid pos) in *. set (FL := flag_addr lyc cid pos) in *.
assert (FL4096 : 4096 <= FL) by (unfold in_app in Hflapp; lia).
rewrite restrict_mkst_fx. unfold pv_resume_ss. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- exact Hwf.
- unfold pv_resume_regions. constructor; [|constructor; [|constructor; [|constructor]]].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E8. split; [lia|]. split; [lia|]. split.
    * intros o Ho. apply (apresent_writable tfibsegs).
      apply (fsw_apresent_unpoison B lyc S2 U W mem2 md2 _ HARU2); [lia|]. apply Hpres. lia.
    * apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) Hcin c Hc) as Hci.
      pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hck.
      apply (chunk_ok_mbyte _ (mrestrict (w_H W) memT)); [|exact Hck].
      destruct Hci as [Hc1 Hc2]. intros i Hi. apply (mbyte_of_aview tfibsegs).
      rewrite <- (fsw_aview_unpoison_high B lyc S2 U W mem2 md2 _ HARU2) by lia.
      rewrite <- (fsw_aview_unpoison_high B lyc Sc U W memT mdc _ HARUc) by lia.
      apply K1; lia.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Esl. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable tfibsegs).
    apply (fsw_apresent_unpoison B lyc S2 U W mem2 md2 _ HARU2); [lia|]. apply Hpres. lia.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite EF. split; [lia|]. split; [lia|]. split.
    * intros o Ho. apply (apresent_writable tfibsegs).
      destruct (Hfp (F + o) ltac:(lia)) as (Hp & Hno).
      exact (fsw_apresent_notowned B lyc S2 U W mem2 md2 (F + o) HARU2 ltac:(lia) Hno Hp).
    * constructor; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs _ _ F (fs_frame_bytes cid - 8) 8 eflag FL Eflag); [cbn; lia | cbn; lia|].
      replace (F + (fs_frame_bytes cid - 8)) with (F + fs_frame_bytes cid - 8) by lia.
      exact (val_mem_of_rdword tfibsegs (w_H W) mem2 _ _ Hflag).
- apply pairwise_disjoint_of_extents. unfold pv_resume_regions, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E8, Esl, EF.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia].
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E8, EF. change (2 ^ 4) with 16. change (2 ^ 5) with 32.
  split; [split; [lia | split; [exact Hal16s | lia]]|]. split; [|exact I].
  split; [lia | split; [exact Hal32 | lia]].
Qed.
End R.

(* the env of the walk after the grant: atom 32 the shadow base, atoms 33 .. 45 the thirteen words the prologue saved
   (ra, s0, s1, s2 .. s11 of the entry, at s0 - 8 .. s0 - 104), atom 46 the flag address; the walk's own atoms follow
   (atom 47 the frame's shadow address). Ported from image A's walk (pv_extra0 / pv_sv_chunks / pv_saved). *)
Definition pv_extra0 (regs : bvmap 5 word) (flag : Z) : list word :=
  [Z_to_bv 64 SHADOW_OFF; YK11.getr regs 1%bv; YK11.getr regs 8%bv; YK11.getr regs 9%bv; YK11.getr regs 18%bv;
   YK11.getr regs 19%bv; YK11.getr regs 20%bv; YK11.getr regs 21%bv; YK11.getr regs 22%bv; YK11.getr regs 23%bv;
   YK11.getr regs 24%bv; YK11.getr regs 25%bv; YK11.getr regs 26%bv; YK11.getr regs 27%bv; Z_to_bv 64 flag].
Definition pv_sv_chunks : list YP09.chunk :=
  map (fun k => YP09.mkChunk (- 8 * (Z.of_nat k + 1)) (CVal 8 (SOff (33 + k) 0))) (seq 0 13).
Lemma pv_sv_chunks_eq : pv_sv_chunks =
  [YP09.mkChunk (-8) (CVal 8 (SOff 33 0)); YP09.mkChunk (-16) (CVal 8 (SOff 34 0));
   YP09.mkChunk (-24) (CVal 8 (SOff 35 0)); YP09.mkChunk (-32) (CVal 8 (SOff 36 0));
   YP09.mkChunk (-40) (CVal 8 (SOff 37 0)); YP09.mkChunk (-48) (CVal 8 (SOff 38 0));
   YP09.mkChunk (-56) (CVal 8 (SOff 39 0)); YP09.mkChunk (-64) (CVal 8 (SOff 40 0));
   YP09.mkChunk (-72) (CVal 8 (SOff 41 0)); YP09.mkChunk (-80) (CVal 8 (SOff 42 0));
   YP09.mkChunk (-88) (CVal 8 (SOff 43 0)); YP09.mkChunk (-96) (CVal 8 (SOff 44 0));
   YP09.mkChunk (-104) (CVal 8 (SOff 45 0))].
Proof. reflexivity. Qed.
(* the state at 0x83040: the saved words at s0, the re-aligned slot 0x30(s1) (atom 9), the frame at atom 10 (a0) *)
Definition pv_ss2 : sstate := pv_resume_ss 0x83040 (-104) 0 pv_sv_chunks 9 0x30 0x38 10 (SOff 46 0) 0.
(* the thirteen saved words, in chunk order (s0 - 8 .. s0 - 104) *)
Definition pv_saved (regs : bvmap 5 word) : list word := firstn 13 (tl (pv_extra0 regs 0)).
Definition pv_saved_ok (m : word -> option byte) (s : Z) (regs : bvmap 5 word) : Prop :=
  forall j, (j < 13)%nat -> val_mem tfibsegs m (s - 8 * (Z.of_nat j + 1)) 8 (bv_unsigned (nth j (pv_saved regs) (Z_to_bv 64 0))).

Section H. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Lemma pv_chunk_xfer : forall E1 E2 (m : word -> option byte) base o (n : N) e1 e2, sv_denot E1 e1 = sv_denot E2 e2 ->
  YP09.chunk_ok tfibsegs E1 m base (YP09.mkChunk o (CVal n e1)) -> YP09.chunk_ok tfibsegs E2 m base (YP09.mkChunk o (CVal n e2)).
Proof.
intros E1 E2 m base o n e1 e2 H Hc i Hi. destruct (Hc i Hi) as (b & Hb & Hm). exists b. split; [|exact Hm].
cbn [cbyte YP09.c_val YP09.c_off] in *. rewrite <- H. exact Hb.
Qed.
Lemma pv_shadow_denot : forall E (p b : nat) pv Bv, ew E p = Z_to_bv 64 pv -> 0 <= pv < 2 ^ 64 ->
  ew E b = Z_to_bv 64 Bv -> 0 <= Bv -> Bv + pv / 8 < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff p 0) (SLit 3)) (SOff b 0)) = Z_to_bv 64 (pv / 8 + Bv).
Proof.
intros E p b pv Bv Hp Hpv Hb HB0 HB1. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
pose proof (Z.div_pos pv 8 ltac:(lia) ltac:(lia)) as Hd.
rewrite U_srl3, (U_atom E p pv Hp Hpv), (U_atom E b Bv Hb ltac:(lia)).
apply zcanon_id. unfold M64. lia.
Qed.
Lemma pv_U_off : forall E n v x, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + x < 2 ^ 64 -> U E (SOff n x) = v + x.
Proof. intros E n v x Hn Hv Hx. rewrite U_SOff, Hn, (unsigned_lit_small v Hv). apply zcanon_id. unfold M64. lia. Qed.
Lemma pv_denot_off : forall E n v x, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + x < 2 ^ 64 ->
  sv_denot E (SOff n x) = Z_to_bv 64 (v + x).
Proof. intros E n v x Hn Hv Hx. rewrite denot_lit_U. f_equal. apply pv_U_off; assumption. Qed.
Lemma pv_denot_lit : forall E z, 0 <= z < 2 ^ 64 -> sv_denot E (SLit z) = Z_to_bv 64 z.
Proof. intros E z Hz. rewrite denot_lit_U, U_lit by lia. reflexivity. Qed.
End H.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the shadow-base cells of B (lib/B/FSH_Base.v FsShadowSyms: GOT word 0x9fc10, cell 0xa8438) *)
Hypothesis HSS : FsShadowSyms B.
(* the use-after-return flag's GOT word and cell of B (lib/B/FSW_K.v fs_D_GOT_uar 0x9fc68 / fs_D_uar_cell 0xa8440,
   MEASURED there; YD2l.v's TfibBU gives both by computation): fsw_uar_regions_ok's premises *)
Hypothesis HGUAR : as_got_uar B = fs_D_GOT_uar.
Hypothesis HUCELL : as_uar_cell B = fs_D_uar_cell.
(* the class-0 fake-frame call (lib/B/FSH_Rt.v FsRt's field fr_stack_malloc_0, the text of its type): the pc pin and
   FSupoisonU's astack_malloc_realizesU at class 0 *)
Hypothesis SM0 : pc_stack_malloc (as_code B) 0 = PC_stack_malloc_0 /\ FSupoisonU.astack_malloc_realizesU tfibsegs B 0.
(* the unit laws fsw_stack_malloc_atU takes (lib/B/FSW_frame.v Section f) *)
Hypothesis errno_low : api_env tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.

Let HGOT : as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address := proj1 HSS.
Let HCELL : as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address := proj2 HSS.

Lemma pv_stk : forall k, (k <= 2)%nat -> 4351 <= STK_parse_value (2 - k).
Proof. intros k Hk. destruct k as [|[|[|k]]]; [vm_compute; discriminate..| lia]. Qed.

Lemma pv_entry : forall k ly S U (W : world tfibsegs) regs mem md ch, (k <= 2)%nat ->
  afn_preU tfibsegs B (STK_parse_value (2 - k)) ly S U W regs mem md ch ->
  st_ok tfibsegs (Ereg regs fs_extraT) pv_ss0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 A_parse_value) mem (seg_rom tfibsegs))).
Proof.
intros k ly S U W regs mem md ch Hk HPRE.
pose proof (fsw_sp B _ ly S U W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _). pose proof (pv_stk k Hk) as FS.
assert (E2 : bv_unsigned (ew (Ereg regs fs_extraT) 2) = spZ regs)
  by (rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl); reflexivity).
apply (fsw_entryT_args B _ 160 ly S U W regs mem md ch _ fs_uar_regions [] HGOT HCELL HPRE).
- lia.
- vm_compute. reflexivity.
- exact (fsw_uar_regions_ok B _ ly S U W regs mem md ch _ HGUAR HUCELL HPRE).
- apply pairwise_disjoint_of_extents.
  unfold fsT_regions_args, fsT_regions, fs_uar_regions, fs_got_uar_region, fs_uar_cell_region, fs_got_region,
    fs_bcell_region, fstk, extent_of_region.
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, fs_D_GOT_uar,
    fs_D_uar_cell.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia].
- exact I.
Qed.

(* segment 0: the prologue, the re-align and the flag test, up to the call of __asan_stack_malloc_0 0x8303c *)
Lemma pv_seg0 : forall k ly S U (W : world tfibsegs) regs mem md ch FP ot (Q : world tfibsegs -> config -> Prop),
  (k <= 2)%nat ->
  afn_preU tfibsegs B (STK_parse_value (2 - k)) ly S U W regs mem md ch ->
  spZ regs <= ot -> ot mod 16 = 0 -> ot <= ly_top ly -> (forall a, spZ regs <= a < ot -> apresent (w_H W) mem a) ->
  (forall ms mat,
     st_ok tfibsegs (Ereg regs fs_extraT) pv_ss1 (restrict (w_H W) ms) ->
     ajournal tfibsegs B (STK_parse_value (2 - k) + (ot - spZ regs)) ot FP ly S W (unpoison U mem) md [] ly S W
       (unpoison U (ms_mem ms)) (with_vm_backing (m_vm_lazy md) mat md) 0 ->
     ARU tfibsegs B ly S U W (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md) ->
     frame_of (Ereg regs fs_extraT) (ss_mem pv_ss0) mem (ms_mem ms) ->
     frame_of (Ereg regs fs_extraT) (ss_mem pv_ss0) (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms)) ->
     SRr tfibsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) Q) ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_parse_value regs mem md) Q.
Proof.
intros k ly S U W regs mem md ch FP ot Q Hk HPRE Hot Hal Htop Hpot K.
pose proof (fsw_sp B _ ly S U W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _). pose proof (pv_stk k Hk) as FS.
pose proof (pv_entry k ly S U W regs mem md ch Hk HPRE) as HS.
pose proof (fsw_ARU B _ ly S U W regs mem md ch HPRE) as HARU.
pose proof (fsw_ajournal_init_ot B _ FP ly S U W regs mem md ch ot HPRE Hot Hal Htop Hpot) as HJ.
assert (Usp : bv_unsigned (ew (Ereg regs fs_extraT) 2) = spZ regs)
  by (rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl); reflexivity).
unfold YG0d.cfg_at. change (w64 A_parse_value) with (Z_to_bv 64 A_parse_value).
fsw_aj_run_toU pv_tbl_ok HS HJ HARU PC_stack_malloc_0.
{ cbv [pv_ss0 fss0T_args ss_mem fsT_regions_args fsT_regions fs_uar_regions app].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - ot);
    [reflexivity | rewrite Usp; lia | cbn; lia | cbn; lia |].
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
exact (K _ _ HS HJ HARU HF HFr).
Qed.

(* the registers at the call of __asan_stack_malloc_0 (read off pv_ss1) *)
Lemma pv_sm_site : forall ly S U (W : world tfibsegs) regs mem md ch k ms, (k <= 2)%nat ->
  afn_preU tfibsegs B (STK_parse_value (2 - k)) ly S U W regs mem md ch ->
  st_ok tfibsegs (Ereg regs fs_extraT) pv_ss1 (restrict (w_H W) ms) ->
  YK11.getr (ms_regs ms) 2%bv = Z_to_bv 64 (32 * ((spZ regs - 160) / 32)) /\
  YK11.getr (ms_regs ms) 9%bv = Z_to_bv 64 (32 * ((spZ regs - 160) / 32)) /\
  spZ regs - 176 <= 32 * ((spZ regs - 160) / 32) <= spZ regs - 160 /\ (32 * ((spZ regs - 160) / 32)) mod 32 = 0 /\
  YK11.getr (ms_regs ms) 1%bv = Z_to_bv 64 0x83040 /\ YK11.getr (ms_regs ms) 10%bv = Z_to_bv 64 64 /\
  YK11.getr (ms_regs ms) 3%bv = YK11.getr regs 3%bv /\ YK11.getr (ms_regs ms) 4%bv = YK11.getr regs 4%bv /\
  YK11.getr (ms_regs ms) 8%bv = YK11.getr regs 2%bv /\ YK11.getr (ms_regs ms) 23%bv = Z_to_bv 64 SHADOW_OFF /\
  YK11.getr (ms_regs ms) 19%bv = YK11.getr regs 11%bv /\ YK11.getr (ms_regs ms) 20%bv = YK11.getr regs 10%bv.
Proof.
intros ly S U W regs mem md ch k ms Hk HPRE HS.
pose proof (fsw_sp B _ ly S U W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _). pose proof (pv_stk k Hk) as FS.
set (E := Ereg regs fs_extraT) in *.
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs)) by (subst E; rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl);
  unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
pose proof (fsw_realign_facts (spZ regs - 160) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity)) as (F1 & F2 & F3).
set (sp1 := 32 * ((spZ regs - 160) / 32)) in *.
assert (R2 : YK11.getr (ms_regs ms) 2%bv = Z_to_bv 64 sp1).
{ exact (fsw_realign_val E pv_ss1 (restrict (w_H W) ms) 2%bv 2 (-160) (spZ regs) HS
    ltac:(vm_compute; reflexivity) E2 ltac:(unfold spZ; apply u64_range) ltac:(lia)). }
assert (R9 : YK11.getr (ms_regs ms) 9%bv = Z_to_bv 64 sp1).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E pv_ss1 ms 9%bv HS).
  lazymatch goal with |- _ = Z_to_bv 64 ?v => change (sr_get (ss_regs pv_ss1) 9%bv) with
    (SAlu ALU_ADD (SAlu ALU_AND (SOff 2 (-160)) (SLit (-32))) (SLit 0)) end.
  rewrite denot_lit_U, U_SAlu. f_equal. cbn [zalu_raw]. rewrite U_SLit.
  assert (UA : YP0e.U E (SAlu ALU_AND (SOff 2 (-160)) (SLit (-32))) = sp1).
  { unfold YP0e.U. rewrite (denot_and_m32 E 2 (spZ regs) (-160) E2 ltac:(lia) ltac:(lia) ltac:(unfold spZ; apply u64_range)).
    apply wz. lia. }
  rewrite UA. change (zcanon 0) with 0. rewrite Z.add_0_r. apply zcanon_id. unfold M64. lia. }
split; [exact R2|]. split; [exact R9|]. split; [lia|]. split; [exact F2|].
split; [exact (fsw_reg_lit _ E _ ms 1%bv 0x83040 HS ltac:(vm_compute; reflexivity) ltac:(lia))|].
split; [exact (fsw_reg_lit _ E _ ms 10%bv 64 HS ltac:(vm_compute; reflexivity) ltac:(lia))|].
split; [exact (fsw_reg_atom _ regs fs_extraT _ ms 3%bv 3%bv 3 HS ltac:(vm_compute; reflexivity) eq_refl)|].
split; [exact (fsw_reg_atom _ regs fs_extraT _ ms 4%bv 4%bv 4 HS ltac:(vm_compute; reflexivity) eq_refl)|].
split; [exact (fsw_reg_atom _ regs fs_extraT _ ms 8%bv 2%bv 2 HS ltac:(vm_compute; reflexivity) eq_refl)|].
split.
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E pv_ss1 ms 23%bv HS).
  change (sr_get (ss_regs pv_ss1) 23%bv) with (SOff 32 0). rewrite fsw_SOff0.
  subst E. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity. }
split; [exact (fsw_reg_atom _ regs fs_extraT _ ms 19%bv 11%bv 11 HS ltac:(vm_compute; reflexivity) eq_refl)|].
exact (fsw_reg_atom _ regs fs_extraT _ ms 20%bv 10%bv 10 HS ltac:(vm_compute; reflexivity) eq_refl).
Qed.

(* the grant: __asan_stack_malloc_0 through SM0 (fsw_stack_malloc_atU), and the resume state at 0x83040 *)
Lemma pv_sm : forall k ly S U (W : world tfibsegs) regs mem md ch FP ot ms mat (Q : world tfibsegs -> config -> Prop),
  (k <= 2)%nat ->
  afn_preU tfibsegs B (STK_parse_value (2 - k)) ly S U W regs mem md ch ->
  Z.of_nat (length (frames S)) <= FRL_parse_value (Z.of_nat k) -> spZ regs <= ot -> ot mod 16 = 0 ->
  st_ok tfibsegs (Ereg regs fs_extraT) pv_ss1 (restrict (w_H W) ms) ->
  ajournal tfibsegs B (STK_parse_value (2 - k) + (ot - spZ regs)) ot FP ly S W (unpoison U mem) md [] ly S W
    (unpoison U (ms_mem ms)) (with_vm_backing (m_vm_lazy md) mat md) 0 ->
  ARU tfibsegs B ly S U W (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md) ->
  (forall S2 regs2 mem2 md2 pos,
     (forall xs, st_ok tfibsegs (Ereg regs2 (pv_extra0 regs (flag_addr ly 0 pos) ++ xs)) pv_ss2
       (restrict (w_H W) (mkst regs2 (Z_to_bv 64 0x83040) mem2 (seg_rom tfibsegs)))) ->
     ajournal tfibsegs B (STK_parse_value (2 - k) + (ot - spZ regs)) ot FP ly S W (unpoison U mem) md [(0, pos)]
       ly S2 W (unpoison U mem2) md2 0 ->
     ARU tfibsegs B ly S2 U W mem2 md2 ->
     aregs_preserved (ms_regs ms) regs2 -> YK11.getr regs2 10%bv = w64 (frame_addr ly 0 pos) ->
     ablocks B ly S2 = ablocks B ly S -> frames S2 = (0, pos) :: frames S -> ~ In (0, pos) (frames S) ->
     st_nev S2 = st_nev S -> blocks_bytes S2 = blocks_bytes S ->
     zero_shadow (aview tfibsegs (w_H W) mem2) SHADOW_OFF (frame_addr ly 0 pos) (fs_frame_bytes 0) ->
     acall_kept tfibsegs B ly S W (unpoison U (ms_mem ms)) W (unpoison U mem2)
       (32 * ((spZ regs - 160) / 32) - ESTACK) (32 * ((spZ regs - 160) / 32)) (fun _ => False) ->
     SRr tfibsegs W (mkCfg (mkst regs2 (Z_to_bv 64 0x83040) mem2 (seg_rom tfibsegs)) md2) Q) ->
  SRr tfibsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) Q.
Proof.
intros k ly S U W regs mem md ch FP ot ms mat Q Hk HPRE Hfrl Hot Hot16' HS HJ HARU K.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (fsw_sp B _ ly S U W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _). pose proof (pv_stk k Hk) as FS.
pose proof HPRE as (HAP & _ & _). pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & _).
destruct (pv_sm_site ly S U W regs mem md ch k ms Hk HPRE HS)
  as (R2 & R9 & Fsp1 & Fal & R1 & R10 & R3 & R4 & R8 & R23 & R19 & R20).
set (sp1 := 32 * ((spZ regs - 160) / 32)) in *.
destruct SM0 as [Hpc0 ASM0].
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ pv_ss1 ms HS eq_refl).
change (ss_pc pv_ss1) with PC_stack_malloc_0. rewrite <- Hpc0.
(* the saved words at the call, read off pv_ss1's stack region *)
assert (HCS : Forall (YP09.chunk_ok tfibsegs (Ereg regs fs_extraT) (mrestrict (w_H W) (ms_mem ms)) (spZ regs))
  (YP09.r_chunks (YP09.mkRegion (Some 2%nat) (-160) 0 (-160) 0
    [YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0));
     YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0));
     YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
     YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
     YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
     YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
     YP09.mkChunk (-8) (CVal 8 (SOff 1 0)); YP09.mkChunk (-160) (CVal 8 (SLit 0))]))).
{ pose proof (fsw_region_nth _ _ _ 0 _ HS ltac:(vm_compute; reflexivity)) as (_ & _ & _ & Hc).
  cbn [YP09.r_base base_val ms_mem restrict] in Hc.
  rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl) in Hc. exact Hc. }
cbn [YP09.r_chunks] in HCS.
eapply SRr_bind.
{ eapply (fsw_stack_malloc_atU B errno_low ML SMP 0 ASM0 ltac:(lia) W (ms_regs ms) (ms_mem ms)
    (STK_parse_value (2 - k) + (ot - spZ regs)) ot FP ly S W (unpoison U mem) md [] ly S U _ 0 (sp1 - ot) _ HJ HARU).
  - unfold spZ at 1. rewrite R2. rewrite wz by lia. lia.
  - assert (Hs1 : sp1 mod 16 = 0) by (subst sp1;
      replace (32 * ((spZ regs - 160) / 32)) with (((spZ regs - 160) / 32 * 2) * 16) by lia; apply Z_mod_mult).
    assert (Hot16 : ot mod 16 = 0) by exact Hot16'.
    rewrite Zminus_mod, Hs1, Hot16. reflexivity.
  - lia.
  - unfold ESTACK. lia.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - exact R1.
  - vm_compute. reflexivity.
  - exact (pv_grant k (frames S) Hk Hfrl). }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & Ec2 & HJ2 & HARU2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin
  & Hnev2 & Hbb2 & Hz & Hflag & HK).
replace (ot + (sp1 - ot) - ESTACK) with (sp1 - ESTACK) in HK by lia. replace (ot + (sp1 - ot)) with sp1 in HK by lia.
assert (Ec2' : c2 = mkCfg (mkst regs2 (Z_to_bv 64 0x83040) mem2 (seg_rom tfibsegs)) md2) by exact Ec2.
rewrite Ec2'. clear Ec2 Ec2'.
assert (Hin0 : In (0, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
assert (Q8 : getr regs2 8%bv = getr regs 2%bv) by (rewrite (fsw_pres _ _ 8%bv HP2 ltac:(pv_cs)); exact R8).
assert (Q9 : getr regs2 9%bv = Z_to_bv 64 sp1) by (rewrite (fsw_pres _ _ 9%bv HP2 ltac:(pv_cs)); exact R9).
apply (K S2 regs2 mem2 md2 pos); try assumption.
intros xs. set (E2 := Ereg regs2 (pv_extra0 regs (flag_addr ly 0 pos) ++ xs)).
eapply (pv_resume_sm B _ ot FP ly S W (unpoison U mem) md [] ly S S2 U W (ms_mem ms) _ mem2 md2 0 0 pos (spZ regs) sp1
  regs2 _ 0x83040 (-104) 0 pv_sv_chunks 9 0x30 0x38 10 (SOff 46 0) HJ2 HARU2 HARU HK Hin0 ltac:(lia)).
- subst E2. rewrite (ew_Ereg_nat _ _ 8 8%bv eq_refl), Q8. reflexivity.
- subst E2. rewrite (ew_Ereg_nat _ _ 9 9%bv eq_refl), Q9. apply wz. lia.
- subst E2. rewrite (ew_Ereg_nat _ _ 10 10%bv eq_refl), Ha0. unfold w64.
  pose proof (ARU_AR tfibsegs B ly S2 U W mem2 md2 HARU2) as HAR2.
  destruct (frames_bounds tfibsegs B LAWS ly S2 W (unpoison U mem2) md2 0 pos HAR2 Hin0) as (Fb1 & Fb2 & _).
  pose proof (fs_frame_bytes_pos 0 ltac:(lia)). apply wz. lia.
- subst E2. change (SOff 46 0) with (SOff (32 + 14) 0). rewrite fsw_extra_atom. reflexivity.
- exact Hflag.
- lia.
- lia.
- lia.
- lia.
- lia.
- lia.
- exact Hal16.
- vm_compute. reflexivity.
- unfold pv_sv_chunks. cbn [map seq]. repeat (apply Forall_cons; [cbn [YP09.c_off YP09.c_len YP09.c_val cv_len Z.of_N Z.of_nat]; lia|]). apply Forall_nil.
- rewrite pv_sv_chunks_eq.
  repeat (apply Forall_cons; [eapply pv_chunk_xfer;
    [| eapply (proj1 (Forall_forall _ _) HCS); repeat (first [left; reflexivity | right])]; subst E2; reflexivity|]).
  apply Forall_nil.
Qed.

End W.

(* ---- glue tactics of the walk (ported from image A's walk, c4ac4207dc3 lib/A/FSH_parse_value.v: pv_bv, pv_fact,
   pv_disj, pv_norm, pv_addreg, pv_reg, pv_region, pv_ewo) ---- *)
Ltac pv_bv := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?v)] =>
  rewrite (unsigned_lit_small v) by (unfold SHADOW_OFF in *; lia) end.
Ltac pv_fact HS n af :=
  lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
    let H := fresh "HS" in
    assert (H : st_ok tfibsegs Ev (add_atom ssx n af) msx);
    [ apply (st_ok_add_fact tfibsegs Ev ssx msx n af HS); unfold afact_ok; cbn [af_lo af_hi af_al2]
    | clear HS; rename H into HS ] end.
Ltac pv_disj :=
  lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
    let rs2 := eval vm_compute in rsy in let r2 := eval vm_compute in ry in change (all_disjoint Ey r2 rs2) end;
  apply all_disjoint_of_extents; unfold extent_of_region; cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zall_disjoint].
Ltac pv_norm HS := lazymatch type of HS with st_ok ?sg ?Ev ?ssx ?msx =>
  let ss' := eval vm_compute in ssx in change (st_ok sg Ev ss' msx) in HS end.
Ltac pv_addreg HS r ROK :=
  lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
    let H := fresh "HSa" in pose proof (ast_ok_add_region tfibsegs Ev ssx msx r HS eq_refl ROK) as H;
    lazymatch type of H with _ -> ?T =>
      let H2 := fresh "HSb" in assert (H2 : T); [apply H; pv_disj | clear HS H; rename H2 into HS] end end.
Ltac pv_reg HS H r name :=
  lazymatch type of HS with st_ok _ ?Ex ?sx (restrict _ ?msx) =>
    pose proof (st_ok_restrict_reg tfibsegs H Ex sx msx r HS) as name;
    lazymatch type of name with _ = sv_denot _ ?t =>
      let t' := eval vm_compute in t in change t with t' in name end end.
Ltac pv_region HS i name :=
  lazymatch type of HS with st_ok _ _ ?sx _ =>
    let r := eval vm_compute in (nth i (ss_mem sx) (YP09.mkRegion None 0 0 0 0 [])) in
    pose proof (fsw_region_nth _ _ _ i r HS ltac:(vm_compute; reflexivity)) as name end.
Ltac pv_ewo := repeat rewrite ew_ewset_other by lia.
Ltac pv_ewo_in H := repeat rewrite ew_ewset_other in H by lia.

Section H2. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the stack's shadow reads 0 (AR_zshadow_law at zero_shadow_ranges' head, the stack, page-aligned by lo_top), and a
   shadow byte of an address at or above alloc_ceiling is no user-poisoned byte. Ported from image A's walk
   (pv_stack_cells8, pv_stack_ra, pv_unpoison_shadow_high, pv_ra_unpoison; their port-from is fs lib/A/ACex.v:313-337). *)
Lemma pv_stack_cells8 : forall lo hi x, lo mod 4096 = 0 -> hi mod 4096 = 0 -> lo <= x -> x + 8 <= hi ->
  lo mod 8 = 0 /\ (hi - lo) mod 8 = 0.
Proof.
intros lo hi x Hlo Hhi H1 H2.
pose proof (Z.div_mod lo 4096 ltac:(lia)) as A. pose proof (Z.div_mod hi 4096 ltac:(lia)) as C.
rewrite Hlo, Z.add_0_r in A. rewrite Hhi, Z.add_0_r in C. split.
- rewrite A. replace (4096 * (lo / 4096)) with ((512 * (lo / 4096)) * 8) by lia. apply Z_mod_mult.
- rewrite A, C. replace (4096 * (hi / 4096) - 4096 * (lo / 4096)) with ((512 * (hi / 4096) - 512 * (lo / 4096)) * 8) by lia.
  apply Z_mod_mult.
Qed.
Lemma pv_stack_ra : forall ly S (W : world tfibsegs) mem md x n,
  AR tfibsegs B ly S W mem md -> ly_stk_lo ly <= x -> x + n <= ly_stk_hi ly -> x mod 8 = 0 -> n mod 8 = 0 -> 8 <= n ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n.
Proof.
intros ly S W mem md x n HAR Hlo Hhi Hx8 Hn8 Hn.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & Hpal & Hpah & _). unfold page_aligned in Hpal, Hpah.
pose proof (al_zshadow _ _ LAWS _ _ _ _ _ (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR ltac:(left; reflexivity)) as Hz.
cbn [fst snd] in Hz.
destruct (pv_stack_cells8 _ _ x Hpal Hpah ltac:(lia) ltac:(lia)) as [Hm1 Hm2].
eapply range_addressable_sub; [apply zero_shadow_range; [exact Hm1 | exact Hm2 | exact Hz] | lia | lia].
Qed.
Lemma pv_unpoison_shadow_high : forall ly S U (W : world tfibsegs) mem md x,
  ARU tfibsegs B ly S U W mem md -> alloc_ceiling <= x < 2 ^ 47 ->
  unpoison U mem (Z_to_bv 64 (SHADOW_OFF + x / 8)) = mem (Z_to_bv 64 (SHADOW_OFF + x / 8)).
Proof.
intros ly S U W mem md x HARU Hx. pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & _).
apply unpoison_out.
assert (Hx8 : 0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
rewrite (wz (SHADOW_OFF + x / 8)) by (unfold SHADOW_OFF; lia).
destruct (in_ush U (SHADOW_OFF + x / 8)) eqn:Hs; [|reflexivity]. exfalso.
destruct HARU as (HAR & OK & _).
destruct (ush_granule B ly S U _ OK Hs) as (g & p & n & Hb & G8 & Gs & Gp & Gn).
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md p n HAR Hb) as (_ & _ & Hc & _).
pose proof (Z.mul_div_le (req_size n) 8 ltac:(lia)).
assert (g / 8 < x / 8).
{ assert (g + 8 <= x) by lia. apply (Z.lt_le_trans _ ((g + 8) / 8)); [|apply Z.div_le_mono; lia].
  replace (g + 8) with (g + 1 * 8) by lia. rewrite Z.div_add by lia. lia. }
unfold shadow_addr in Gs. lia.
Qed.
Lemma pv_ra_unpoison : forall ly S U (W : world tfibsegs) mem md x n,
  ARU tfibsegs B ly S U W mem md -> alloc_ceiling <= x -> x + n <= 2 ^ 47 ->
  range_addressable (aview tfibsegs (w_H W) (unpoison U mem)) SHADOW_OFF x n ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n.
Proof.
intros ly S U W mem md x n HARU Hx Hn HRA y Hy. destruct (HRA y Hy) as (s & Es & Hok). exists s. split; [|exact Hok].
rewrite <- Es. unfold shadow_of_addr. apply (aview_at tfibsegs). symmetry.
exact (pv_unpoison_shadow_high ly S U W mem md y HARU ltac:(lia)).
Qed.
End H2.

Section H3. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* the bytes segment 1 writes between the grant and the skip_ws call: F's frame and shadow, the saved-word window at
   s0 (writable in the state, written by the prologue only) and the slot 0x30(s1) *)
Definition pv_wr1 (F s sp1 a : Z) : Prop :=
  (F <= a < F + 64) \/ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 8) \/ (s - 104 <= a < s) \/
  (sp1 + 48 <= a < sp1 + 56).
(* ported from image A's walk (pv_frame_P, pv_wrange_cases, pv_wrange_nil, pv_saved_of_region, pv_mbyte_keep,
   pv_val_keep, pv_saved_keep) *)
Lemma pv_frame_P : forall E rs (m m' : word -> option byte) (P : Z -> Prop), frame_of E rs m m' ->
  (forall a, in_wrange E rs a -> P a) -> forall x : word, ~ P (bv_unsigned x) -> m' x = m x.
Proof. intros E rs m m' P HF HP x Hx. apply HF. intros Hin. exact (Hx (HP _ Hin)). Qed.
Lemma pv_wrange_cases : forall E (r : YP09.region) rs a,
  in_wrange E (r :: rs) a -> (base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r)
    \/ in_wrange E rs a.
Proof. intros E r rs a (r' & [<-|Hin] & Ha); [left; exact Ha | right; exists r'; split; assumption]. Qed.
Lemma pv_wrange_nil : forall E a, ~ in_wrange E [] a.
Proof. intros E a (r & [] & _). Qed.
Lemma pv_saved_of_region : forall regs regs0 FL xs (m : word -> option byte) s lo hi wlo whi,
  region_ok tfibsegs (Ereg regs (pv_extra0 regs0 FL ++ xs)) m (YP09.mkRegion (Some 8%nat) lo hi wlo whi pv_sv_chunks) ->
  bv_unsigned (ew (Ereg regs (pv_extra0 regs0 FL ++ xs)) 8) = s -> pv_saved_ok m s regs0.
Proof.
intros regs regs0 FL xs m s lo hi wlo whi HR Hs j Hj.
assert (Hin : In (YP09.mkChunk (- 8 * (Z.of_nat j + 1)) (CVal 8 (SOff (33 + j) 0))) pv_sv_chunks).
{ unfold pv_sv_chunks. apply (in_map (fun k => YP09.mkChunk (- 8 * (Z.of_nat k + 1)) (CVal 8 (SOff (33 + k) 0)))).
  apply in_seq. lia. }
pose proof (fsw_field _ m 8 s pv_sv_chunks lo hi wlo whi _ 8 _ (bv_unsigned (nth j (pv_saved regs0) (Z_to_bv 64 0))) HR Hs Hin)
  as Hv.
replace (s + - 8 * (Z.of_nat j + 1)) with (s - 8 * (Z.of_nat j + 1)) in Hv by lia. apply Hv.
- rewrite Z_to_bv_bv_unsigned. change (33 + j)%nat with (32 + S j)%nat. rewrite fsw_extra_atom.
  rewrite app_nth1 by (cbn [length pv_extra0]; lia).
  do 13 (destruct j as [|j]; [reflexivity|]). lia.
- change (8 * Z.of_N 8) with 64. apply u64_range.
- cbn. lia.
Qed.
Lemma pv_mbyte_keep : forall (m m' : word -> option byte) (P : Z -> Prop) a,
  (forall x : word, ~ P (bv_unsigned x) -> m' x = m x) -> 0 <= a < 2 ^ 64 -> ~ P a ->
  mbyte tfibsegs m' a = mbyte tfibsegs m a.
Proof.
intros m m' P a HK Ha HP. unfold mbyte. rewrite (HK (Z_to_bv 64 a)); [reflexivity|].
rewrite (wz a Ha). exact HP.
Qed.
Lemma pv_val_keep : forall (m m' : word -> option byte) (P : Z -> Prop) a (n : nat) v,
  (forall x : word, ~ P (bv_unsigned x) -> m' x = m x) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall k, 0 <= k < Z.of_nat n -> ~ P (a + k)) ->
  val_mem tfibsegs m a n v -> val_mem tfibsegs m' a n v.
Proof.
intros m m' P a n v HK Ha Hn HP Hv k Hk. rewrite (pv_mbyte_keep m m' P (a + Z.of_nat k) HK ltac:(lia) (HP (Z.of_nat k) ltac:(lia))).
exact (Hv k Hk).
Qed.
Lemma pv_saved_keep : forall (m m' : word -> option byte) (P : Z -> Prop) s regs0,
  (forall x : word, ~ P (bv_unsigned x) -> m' x = m x) -> 104 <= s <= 2 ^ 64 ->
  (forall a, s - 104 <= a < s -> ~ P a) -> pv_saved_ok m s regs0 -> pv_saved_ok m' s regs0.
Proof.
intros m m' P s regs0 HK Hs HP Hv j Hj.
apply (pv_val_keep m m' P (s - 8 * (Z.of_nat j + 1)) 8 _ HK); [lia | cbn; lia | | exact (Hv j Hj)].
intros k Hk. apply HP. cbn in Hk. lia.
Qed.
End H3.

Ltac pv_wr_tac rw :=
  let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha; cbn [ss_mem add_cond] in Ha;
  repeat (apply pv_wrange_cases in Ha; destruct Ha as [Ha|Ha]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    rw Ha; unfold pv_wr1; lia|]);
  exfalso; exact (pv_wrange_nil _ _ Ha).

(* ================= segment 1: 0x83040 -> THE CALLEE'S ENTRY A_skip_ws (ra = 0x830d4) =================
   MEASURED (vm_compute over pv_tbl from pv_ss2): s2 := a0 (F), `j` 0x83044, s10 := s2, `bnez s2` 0x83050 TAKEN (F >=
   4096: atom 10's fact), 0x30(s1) := F (0x83070), F's header (magic 0x41b58ab3, the frame descriptor, the pc) at F + 0 /
   8 / 16 (0x83094 .. 0x8309c), s11 := F / 8 + s7 (0x830a4), F's shadow := f1 f1 f1 f1 f8 f3 f3 f3 (0x830a8 .. 0x830c8),
   a0 := s4 (q), `jal skip_ws` 0x830d0 -> 0x83598 with ra = 0x830d4. No shadow check, no UBSan check, no obligation:
   B's white-space loop is this one call (A inlines it). The real-stack fallback 0x83048 / 0x83054 .. 0x8306c is not
   reached (the `bnez` is decided). *)
Section S1. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Lemma pv_seg1 : forall STK ot FP ly S S2 U (W : world tfibsegs) regs mem md regs2 mem2 md2 pos s sp1 v q
  (Q : world tfibsegs -> config -> Prop),
  let F := frame_addr ly 0 pos in let FL := flag_addr ly 0 pos in
  let E := Ereg regs2 (pv_extra0 regs FL ++ [Z_to_bv 64 (SHADOW_OFF + F / 8)]) in
  st_ok tfibsegs E pv_ss2 (restrict (w_H W) (mkst regs2 (Z_to_bv 64 0x83040) mem2 (seg_rom tfibsegs))) ->
  ajournal tfibsegs B STK ot FP ly S W (unpoison U mem) md [(0, pos)] ly S2 W (unpoison U mem2) md2 0 ->
  ARU tfibsegs B ly S2 U W mem2 md2 -> In (0, pos) (frames S2) ->
  YK11.getr regs2 10%bv = Z_to_bv 64 F -> YK11.getr regs2 23%bv = Z_to_bv 64 SHADOW_OFF ->
  YK11.getr regs2 20%bv = Z_to_bv 64 q -> YK11.getr regs2 8%bv = Z_to_bv 64 s -> YK11.getr regs2 9%bv = Z_to_bv 64 sp1 ->
  YK11.getr regs2 19%bv = Z_to_bv 64 v -> YK11.getr regs2 2%bv = Z_to_bv 64 sp1 ->
  0 <= q < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  sp1 + 160 <= s -> 2 ^ 46 <= s <= 2 ^ 47 -> s mod 16 = 0 -> ot - STK <= sp1 - 4096 -> s <= ot ->
  (forall msh math,
     msh = mkst (ms_regs msh) (Z_to_bv 64 A_skip_ws) (ms_mem msh) (seg_rom tfibsegs) ->
     ajournal tfibsegs B STK ot FP ly S W (unpoison U mem) md [(0, pos)] ly S2 W (unpoison U (ms_mem msh))
       (with_vm_backing (m_vm_lazy md2) math md2) 0 ->
     ARU tfibsegs B ly S2 U W (ms_mem msh) (with_vm_backing (m_vm_lazy md2) math md2) ->
     (forall x : word, ~ pv_wr1 F s sp1 (bv_unsigned x) -> mrestrict (w_H W) (ms_mem msh) x = mrestrict (w_H W) mem2 x) ->
     pv_saved_ok (mrestrict (w_H W) (ms_mem msh)) s regs ->
     val_mem tfibsegs (mrestrict (w_H W) (ms_mem msh)) (F + 56) 8 FL ->
     YK11.getr (ms_regs msh) 1%bv = Z_to_bv 64 0x830d4 -> YK11.getr (ms_regs msh) 10%bv = Z_to_bv 64 q ->
     YK11.getr (ms_regs msh) 2%bv = Z_to_bv 64 sp1 ->
     YK11.getr (ms_regs msh) 3%bv = YK11.getr regs2 3%bv -> YK11.getr (ms_regs msh) 4%bv = YK11.getr regs2 4%bv ->
     YK11.getr (ms_regs msh) 8%bv = Z_to_bv 64 s -> YK11.getr (ms_regs msh) 9%bv = Z_to_bv 64 sp1 ->
     YK11.getr (ms_regs msh) 18%bv = Z_to_bv 64 F -> YK11.getr (ms_regs msh) 19%bv = Z_to_bv 64 v ->
     YK11.getr (ms_regs msh) 20%bv = Z_to_bv 64 q -> YK11.getr (ms_regs msh) 23%bv = Z_to_bv 64 SHADOW_OFF ->
     YK11.getr (ms_regs msh) 26%bv = Z_to_bv 64 F ->
     YK11.getr (ms_regs msh) 27%bv = Z_to_bv 64 (SHADOW_OFF + F / 8) ->
     SRr tfibsegs W (mkCfg msh (with_vm_backing (m_vm_lazy md2) math md2)) Q) ->
  SRr tfibsegs W (mkCfg (mkst regs2 (Z_to_bv 64 0x83040) mem2 (seg_rom tfibsegs)) md2) Q.
Proof.
intros STK ot FP ly S S2 U W regs mem md regs2 mem2 md2 pos s sp1 v q Q F FL E HS HJ HARU Hin0 R10 R23 R20 R8 R9
  R19 R2 Hq Hv Hsp1 Hsp32 Hsps Hs Hs16 Hstk Hsot K.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (ARU_AR tfibsegs B ly S2 U W mem2 md2 HARU) as HAR2.
destruct (al_frames _ _ LAWS ly S2 W (unpoison U mem2) md2 0 pos HAR2 Hin0) as (HF32 & HFapp & HFp & HFSp).
destruct (frames_bounds tfibsegs B LAWS ly S2 W (unpoison U mem2) md2 0 pos HAR2 Hin0) as (HF4096 & HFc & _).
change (fs_frame_bytes 0) with 64 in *. fold F in HF32, HFapp, HFp, HFSp, HF4096, HFc.
assert (EA : forall (r : bv 5) n z, Z.of_nat n = bv_unsigned r -> getr regs2 r = Z_to_bv 64 z -> ew E n = Z_to_bv 64 z)
  by (intros r n z Hn Hr; subst E; rewrite (ew_Ereg_nat _ _ n r Hn), Hr; reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 F) by (apply (EA 10%bv); [reflexivity | exact R10]).
assert (E23 : ew E 23 = Z_to_bv 64 SHADOW_OFF) by (apply (EA 23%bv); [reflexivity | exact R23]).
assert (E20 : ew E 20 = Z_to_bv 64 q) by (apply (EA 20%bv); [reflexivity | exact R20]).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (apply (EA 9%bv); [reflexivity | exact R9]).
assert (E8 : ew E 8 = Z_to_bv 64 s) by (apply (EA 8%bv); [reflexivity | exact R8]).
assert (E19 : ew E 19 = Z_to_bv 64 v) by (apply (EA 19%bv); [reflexivity | exact R19]).
assert (E2 : ew E 2 = Z_to_bv 64 sp1) by (apply (EA 2%bv); [reflexivity | exact R2]).
assert (E47 : ew E 47 = Z_to_bv 64 (SHADOW_OFF + F / 8))
  by (subst E; change 47%nat with (32 + 15)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (HF8 : 512 <= F / 8 < 2 ^ 44) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
(* the facts the walk adds: s7 is the shadow base, s1 a stack address, atom 47 F's shadow address *)
pv_fact HS 23%nat (mkAF SHADOW_OFF SHADOW_OFF 0). { rewrite E23. pv_bv. rewrite Z.pow_0_r, Z.mod_1_r. unfold SHADOW_OFF; lia. }
pv_fact HS 9%nat (mkAF (2 ^ 46) (2 ^ 47) 5). { rewrite E9. pv_bv. change (2 ^ 5) with 32. lia. }
pv_fact HS 47%nat (mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 2).
{ rewrite E47. pv_bv. change (2 ^ 2) with 4.
  assert (HF84 : (F / 8) mod 4 = 0).
  { assert (HFq : F = (F / 32 * 4) * 8) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
    rewrite HFq, Z.div_mul by lia. apply Z_mod_mult. }
  unfold SHADOW_OFF. split; [lia|]. split; [rewrite Zplus_mod, HF84; reflexivity | lia]. }
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_add_alias tfibsegs Ev ssx msx _ _ HS (shadow_decl_ok Ev 10 23 47 F SHADOW_OFF E10 ltac:(lia) E23 E47))
    as HS1 end.
clear HS. rename HS1 into HS.
pv_norm HS.
assert (B10 : bv_unsigned (ew E 10) = F) by (rewrite E10; pv_bv; reflexivity).
assert (B9 : bv_unsigned (ew E 9) = sp1) by (rewrite E9; pv_bv; reflexivity).
assert (B8 : bv_unsigned (ew E 8) = s) by (rewrite E8; pv_bv; reflexivity).
assert (B47 : bv_unsigned (ew E 47) = SHADOW_OFF + F / 8) by (rewrite E47; pv_bv; reflexivity).
(* F's shadow, written by the frame setup: present and not runtime-owned (AR_frames_law), hence writable *)
assert (ROKs : region_ok tfibsegs E (mrestrict (w_H W) mem2) (YP09.mkRegion (Some 47%nat) 0 8 0 8 [])).
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite B47. split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|apply Forall_nil].
  intros o Ho. apply (apresent_writable tfibsegs). destruct (HFSp o ltac:(change (64 / 8) with 8; lia)) as (Hp1 & Hno).
  unfold shadow_addr in Hp1, Hno.
  exact (fsw_apresent_notowned B ly S2 U W mem2 md2 (SHADOW_OFF + F / 8 + o) HARU ltac:(unfold SHADOW_OFF; lia) Hno Hp1). }
pv_addreg HS (YP09.mkRegion (Some 47%nat) 0 8 0 8 []) ROKs.
{ rewrite B8, B9, B10, B47. unfold zdisj. cbn [fst snd].
  unfold in_app, kLowShadowBeg, ASAN_CEIL in HFapp. unfold SHADOW_OFF.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
pv_norm HS.
(* 0x83040 -> A_skip_ws: s2, s10, the slot, F's header and shadow, a0 := q, the jal *)
fsw_aj_run_toU pv_tbl_ok HS HJ HARU A_skip_ws.
{ cbn [ss_mem].
  eapply awr_ok_cons_gen with (k := 47%nat) (b := SHADOW_OFF + F / 8); [reflexivity | exact B47 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. unfold awr_byte, awr_byte0. left; right; right; right.
    exists 0, pos. split; [left; reflexivity|].
    right. unfold in_zr, shadow_addr. cbn [fst snd]. change (fs_frame_bytes 0 / 8) with 8. fold F. lia. }
  eapply awr_ok_cons_stack_off with (n := 8%nat) (d := s - ot); [reflexivity | rewrite B8; lia | cbn; lia | cbn; lia |].
  eapply awr_ok_cons_stack_off with (n := 9%nat) (d := sp1 - ot); [reflexivity | rewrite B9; lia | cbn; lia | cbn; lia |].
  eapply awr_ok_cons_gen with (k := 10%nat) (b := F); [reflexivity | exact B10 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. unfold awr_byte, awr_byte0. left; right; right; right.
    exists 0, pos. split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 0) with 64. fold F. lia. }
  apply awr_ok_nil. }
assert (KEEP : forall x : word, ~ pv_wr1 F s sp1 (bv_unsigned x) ->
  mrestrict (w_H W) (ms_mem ms) x = mrestrict (w_H W) mem2 x).
{ intros x Hx.
  rewrite (pv_frame_P _ _ _ _ (pv_wr1 F s sp1) HFr
    ltac:(pv_wr_tac ltac:(fun H => rewrite ?B47, ?B8, ?B9, ?B10 in H)) x Hx).
  reflexivity. }
pv_reg HS (w_H W) (1%bv : bv 5) H1. pv_reg HS (w_H W) (10%bv : bv 5) H10. pv_reg HS (w_H W) (2%bv : bv 5) H2.
pv_reg HS (w_H W) (3%bv : bv 5) H3. pv_reg HS (w_H W) (4%bv : bv 5) H4.
pv_reg HS (w_H W) (8%bv : bv 5) H8. pv_reg HS (w_H W) (9%bv : bv 5) H9. pv_reg HS (w_H W) (18%bv : bv 5) H18.
pv_reg HS (w_H W) (19%bv : bv 5) H19. pv_reg HS (w_H W) (20%bv : bv 5) H20. pv_reg HS (w_H W) (23%bv : bv 5) H23.
pv_reg HS (w_H W) (26%bv : bv 5) H26. pv_reg HS (w_H W) (27%bv : bv 5) H27.
rewrite pv_denot_lit in H1 by lia.
rewrite fsw_SOff0, E20 in H10. rewrite fsw_SOff0, E2 in H2.
assert (E3 : ew E 3 = getr regs2 3%bv) by (subst E; exact (ew_Ereg_nat _ _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs2 4%bv) by (subst E; exact (ew_Ereg_nat _ _ 4 4%bv eq_refl)).
rewrite fsw_SOff0, E3 in H3. rewrite fsw_SOff0, E4 in H4.
rewrite fsw_SOff0, E8 in H8. rewrite fsw_SOff0, E9 in H9. rewrite fsw_SOff0, E10 in H18.
rewrite fsw_SOff0, E19 in H19. rewrite fsw_SOff0, E20 in H20. rewrite fsw_SOff0, E23 in H23.
rewrite fsw_SOff0, E10 in H26. rewrite fsw_SOff0, E47 in H27.
(* the memory facts at ms, read off the state's regions: the saved words (region 1) and the flag word (region 3) *)
pv_region HS 1%nat RS0.
pv_region HS 3%nat RFR.
cbn [ms_mem restrict] in RS0, RFR.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms HS eq_refl) as Hshape.
lazymatch type of Hshape with _ = mkst _ (Z_to_bv 64 ?pc) _ _ =>
  let pc' := eval vm_compute in pc in change pc with pc' in Hshape end.
destruct (al_flag _ _ LAWS ly S2 W (unpoison U mem2) md2 0 pos HAR2 Hin0) as (_ & _ & HFLa & HFLc). fold FL in HFLa, HFLc.
assert (B46 : bv_unsigned (ew E 46) = FL).
{ subst E. change 46%nat with (32 + 14)%nat. rewrite ew_Ereg_extra. cbn [nth pv_extra0 app].
  unfold in_app in HFLa. apply wz. lia. }
apply (K ms mat); try assumption.
- exact (pv_saved_of_region regs2 regs FL _ _ s _ _ _ _ RS0 B8).
- exact (fsw_field _ _ 10 F _ 0 64 0 64 56 8 (SOff 46 0) FL RFR B10 ltac:(cbn [In]; tauto)
    ltac:(rewrite fsw_SOff0, <- B46; symmetry; apply Z_to_bv_bv_unsigned) ltac:(cbn; unfold in_app in HFLa; lia) ltac:(cbn; lia)).
Qed.
End S1.

(* ================= segment 2: after skip_ws, 0x830d4 -> the dispatch -> THE CALLEE'S ENTRY =================
   The state at 0x830d4 is built afresh from machine facts (pd_st): q's two words (atom 20; in->p = atom 33, in->end =
   atom 34; read only), the text byte at in->p (atom 33, value atom 35; read only), the shadow base (atom 23), v (atom
   19, facts only). The env is Ereg regs (fs_extraT ++ [in->p; in->end; byte]).
   MEASURED (vm_compute over pv_tbl from pd_st), report sites refuted on the way (report-sites-B.tsv):
     0x830d8 `bnez (q & 7)` -> the trap 0x834e8: NOT taken, decided by atom 20's alignment fact (q mod 8 = 0);
     0x830e8 `bnez` on q's shadow byte -> __asan_report_load8 0x83558: NOT taken, token covered by pd_SH's q entry;
     0x830fc `bnez` on q + 8's shadow byte -> __asan_report_load8 0x8355c: NOT taken, the same entry;
     0x83108 `bgeu in->p, in->end` -> the failure exit 0x83154: NOT taken (SRr_sym_branch), in->p < in->end;
     0x8310c `beqz in->p` -> the trap 0x834e8: NOT taken, decided by atom 33's fact (in->p >= 4096);
     0x8311c `bnez` on the byte's shadow -> the slow path 0x834ec / __asan_report_load1 0x834f4: NOT taken, token
       covered by pd_SH's byte entry;
     the dispatch 0x83128 .. 0x83170 (SRr_sym_branch at each test): byte 34 -> 0x83184 (string arm), byte 123 ->
       0x83174 (object arm); every other arm (literal 0x83294, parse_number 0x831e8 .., with its report sites 0x833b4,
       0x83514, 0x83520, 0x8352c, 0x83540, 0x83550, 0x8356c, 0x83574, 0x8357c, 0x83584, 0x8358c, 0x83594 and its trap
       edges 0x831fc, 0x83238, 0x833c8, 0x833d4, 0x83428, 0x83438, 0x8343c, 0x83488) is not reached;
     string arm: 0x83184 `beqz v` and 0x8318c `bnez (v & 7)` -> the trap 0x834e8: NOT taken, decided by atom 19's facts
       (v >= 4096, v mod 8 = 0); 0x8319c `bnez` on v's shadow -> the slow path 0x834f8 / __asan_report_store4 0x83504:
       NOT taken, token covered by pd_SH's v entry; v->type := 4 (0x831a4); a0 := q; `jal parse_string` 0x831ac ->
       0x85534 with ra = 0x831b0;
     object arm: a2 := 1, a0 := q, a1 := v, `j` 0x83180, `jal parse_items` 0x83278 -> 0x84e70 with ra = 0x8327c. *)
Definition pd_xs (cur endv c : Z) : list word := fs_extraT ++ [Z_to_bv 64 cur; Z_to_bv 64 endv; Z_to_bv 64 c].
Definition pd_q_region : YP09.region :=
  YP09.mkRegion (Some 20%nat) 0 24 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0)); YP09.mkChunk 8 (CVal 8 (SOff 34 0))].
Definition pd_txt_region : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 35 0))].
Definition pd_v_region : YP09.region := YP09.mkRegion (Some 19%nat) 0 56 0 4 [].
Definition pd_facts : facts :=
  mkFacts [(19%nat, mkAF 4096 (2 ^ 47 - 56) 3); (20%nat, mkAF (2 ^ 46) (2 ^ 47 - 24) 3);
           (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 4096 (2 ^ 47 - 8) 0); (35%nat, mkAF 0 255 0)] [] [].
Definition pd_st : sstate := mkSS 0x830d4 sr_atoms [pd_q_region; pd_txt_region] None pd_facts.
Definition pd_SH : list shent := [mkSHE 20 0 24; mkSHE 33 0 1; mkSHE 19 0 56].
Definition pd_Bx : sv := SOff 23 0.

Section PD. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Lemma pd_ok : forall (H : word -> bool) regs mem v q cur endv c,
  YK11.getr regs 19%bv = Z_to_bv 64 v -> YK11.getr regs 20%bv = Z_to_bv 64 q ->
  YK11.getr regs 23%bv = Z_to_bv 64 SHADOW_OFF ->
  4096 <= v <= 2 ^ 47 - 56 -> v mod 8 = 0 -> 2 ^ 46 <= q <= 2 ^ 47 - 24 -> q mod 8 = 0 ->
  4096 <= cur <= 2 ^ 47 - 8 -> 0 <= c <= 255 -> 0 <= endv < 2 ^ 64 -> (cur + 1 <= q \/ q + 24 <= cur) ->
  val_mem tfibsegs (mrestrict H mem) q 8 cur -> val_mem tfibsegs (mrestrict H mem) (q + 8) 8 endv ->
  val_mem tfibsegs (mrestrict H mem) cur 1 c ->
  st_ok tfibsegs (Ereg regs (pd_xs cur endv c)) pd_st
    (restrict H (mkst regs (Z_to_bv 64 0x830d4) mem (seg_rom tfibsegs))).
Proof.
intros H regs mem v q cur endv c R19 R20 R23 Hv Hv8 Hq Hq8 Hcur Hc Hend Hcq Vq0 Vq8 Vc.
set (E := Ereg regs (pd_xs cur endv c)).
pose proof asan_consts as (C1 & _).
assert (A : forall (r : bv 5) n z, Z.of_nat n = bv_unsigned r -> getr regs r = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 ->
  bv_unsigned (ew E n) = z) by (intros r n z Hn Hr Hz; subst E; rewrite (ew_Ereg_nat _ _ n r Hn), Hr; apply wz; exact Hz).
assert (X : forall j z, nth j (pd_xs cur endv c) (Z_to_bv 64 0) = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 ->
  bv_unsigned (ew E (32 + j)) = z) by (intros j z Hj Hz; subst E; rewrite ew_Ereg_extra, Hj; apply wz; exact Hz).
assert (E19 : bv_unsigned (ew E 19) = v) by (apply (A 19%bv); [reflexivity | exact R19 | lia]).
assert (E20 : bv_unsigned (ew E 20) = q) by (apply (A 20%bv); [reflexivity | exact R20 | lia]).
assert (E23 : bv_unsigned (ew E 23) = SHADOW_OFF) by (apply (A 23%bv); [reflexivity | exact R23 | unfold SHADOW_OFF; lia]).
assert (E33 : bv_unsigned (ew E 33) = cur) by (apply (X 1%nat); [reflexivity | lia]).
assert (E34 : bv_unsigned (ew E 34) = endv) by (apply (X 2%nat); [reflexivity | lia]).
assert (E35 : bv_unsigned (ew E 35) = c) by (apply (X 3%nat); [reflexivity | lia]).
assert (D : forall n w, bv_unsigned (ew E n) = w -> sv_denot E (SOff n 0) = Z_to_bv 64 w)
  by (intros n w Hn; rewrite fsw_SOff0, <- Hn; symmetry; apply Z_to_bv_bv_unsigned).
rewrite restrict_mkst_fx. unfold pd_st. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
  + unfold region_ok, pd_q_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. fold E.
    rewrite E20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val tfibsegs _ _ q 0 8 (SOff 33 0) cur (D 33%nat cur E33)); [cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Vq0].
    * apply (chunk_ok_val tfibsegs _ _ q 8 8 (SOff 34 0) endv (D 34%nat endv E34)); [cbn; lia | cbn; lia | exact Vq8].
  + unfold region_ok, pd_txt_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. fold E.
    rewrite E33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val tfibsegs _ _ cur 0 1 (SOff 35 0) c (D 35%nat c E35)); [cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Vc].
- apply pairwise_disjoint_of_extents. unfold pd_q_region, pd_txt_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold E. rewrite E20, E33.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
- unfold pd_facts. split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  fold E. rewrite E19, E20, E23, E33, E35. change (2 ^ 3) with 8.
  rewrite Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; try lia; unfold SHADOW_OFF; lia.
Qed.
End PD.

Ltac pd_wr_P rw :=
  let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha; cbv beta;
  try (unfold pd_st, pd_q_region, pd_txt_region, pd_v_region in Ha);
  cbn [ss_mem add_cond] in Ha;
  repeat (apply pv_wrange_cases in Ha; destruct Ha as [Ha|Ha]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    pv_ewo_in Ha; rw Ha; lia|]);
  exfalso; exact (pv_wrange_nil _ _ Ha).
(* the write windows of the dispatch states: every region is read only, the string arm's v region last added *)
Ltac pd_awr_ro := cbn [ss_mem add_cond]; repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
(* writability reads one byte of the view (skip_ws walk's skw_wr_eq) *)
Lemma pv_wr_keep : forall (m m' : word -> option byte) a, m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) ->
  (writable_at tfibsegs m a <-> writable_at tfibsegs m' a).
Proof. intros m m' a E. unfold writable_at, wview. rewrite E. reflexivity. Qed.
(* the memory is the same at every address after a run whose regions are all read only *)
Ltac pd_keep_all :=
  let x := fresh "x" in intros x;
  repeat lazymatch goal with
  | |- mrestrict ?Hh (ms_mem ?mA) x = mrestrict ?Hh (ms_mem ?m0) x =>
      lazymatch mA with m0 => fail | _ =>
      lazymatch goal with
      | HFx : frame_of _ _ (mrestrict Hh (ms_mem ?mB)) (mrestrict Hh (ms_mem mA)) |- _ =>
          rewrite (pv_frame_P _ _ _ _ (fun _ => False) HFx ltac:(pd_wr_P ltac:(fun H => idtac)) x ltac:(cbv beta; tauto))
      end end
  end; reflexivity.

(* the callee-saved registers the dispatch keeps: every one but s8 (B writes s8 := q / 8 + shadow base at 0x830dc,
   which the epilogue restores from the save area) *)
Definition PV_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27]%bv.
Section RK. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Lemma pv_regs_keep_l : forall (l : list (bv 5)) (H : word -> bool) (E : env) ss ms regs0 extra,
  st_ok tfibsegs E ss (restrict H ms) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) l = true ->
  (forall n : nat, (n < 32)%nat -> ew E n = ew (Ereg regs0 extra) n) ->
  forall r : bv 5, In r l -> YK11.getr (ms_regs ms) r = YK11.getr regs0 r.
Proof.
intros l H E ss ms regs0 extra HS Hall Hag r Hr. pose proof (u5_range r) as Hr5.
pose proof (proj1 (forallb_forall _ _) Hall r Hr) as Hq. cbn beta in Hq. apply sv_eqb_eq in Hq.
rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), Hq, fsw_SOff0, (Hag (Z.to_nat (bv_unsigned r)) ltac:(lia)).
apply (ew_Ereg_nat regs0 extra _ r). lia.
Qed.
Lemma pv_regs_keep : forall (H : word -> bool) (E : env) ss ms regs0 extra,
  st_ok tfibsegs E ss (restrict H ms) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) PV_KEPT = true ->
  (forall n : nat, (n < 32)%nat -> ew E n = ew (Ereg regs0 extra) n) ->
  forall r : bv 5, In r PV_KEPT -> YK11.getr (ms_regs ms) r = YK11.getr regs0 r.
Proof.
intros H E ss ms regs0 extra HS Hall Hag r Hr. pose proof (u5_range r) as Hr5.
pose proof (proj1 (forallb_forall _ _) Hall r Hr) as Hq. cbn beta in Hq. apply sv_eqb_eq in Hq.
rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), Hq, fsw_SOff0, (Hag (Z.to_nat (bv_unsigned r)) ltac:(lia)).
apply (ew_Ereg_nat regs0 extra _ r). lia.
Qed.
End RK.
Section DSP. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Lemma pv_disp : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc U (W : world tfibsegs) ms mdx k v q cur endv c
  (Q : world tfibsegs -> config -> Prop),
  ms = mkst (ms_regs ms) (Z_to_bv 64 0x830d4) (ms_mem ms) (seg_rom tfibsegs) ->
  YK11.getr (ms_regs ms) 19%bv = Z_to_bv 64 v -> YK11.getr (ms_regs ms) 20%bv = Z_to_bv 64 q ->
  YK11.getr (ms_regs ms) 23%bv = Z_to_bv 64 SHADOW_OFF ->
  4096 <= v -> v + 56 <= alloc_ceiling -> v mod 8 = 0 -> (v + 56 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= v) ->
  2 ^ 46 <= q <= 2 ^ 47 - 24 -> q mod 8 = 0 -> alloc_ceiling <= q ->
  ly_stk_lo lyc <= q -> q + 24 <= ly_stk_hi lyc ->
  4096 <= cur -> cur + 1 <= endv -> endv <= 2 ^ 47 - 8 -> (endv <= q \/ q + 24 <= cur) ->
  (cur + 1 <= v \/ v + 56 <= cur) -> (cur + 1 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= cur) ->
  c = 34 \/ c = 123 ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) q 8 cur ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (q + 8) 8 endv ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) cur 1 c ->
  range_addressable (aview tfibsegs (w_H W) (ms_mem ms)) SHADOW_OFF cur 1 ->
  range_addressable (aview tfibsegs (w_H W) (ms_mem ms)) SHADOW_OFF v 56 ->
  (forall o, 0 <= o < 56 -> writable_at tfibsegs (mrestrict (w_H W) (ms_mem ms)) (v + o)) ->
  (forall a, in_zr a (v, 56) -> awr_byte tfibsegs B STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own (frames S) a) ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison U (ms_mem ms)) mdx k ->
  ARU tfibsegs B lyc Sc U W (ms_mem ms) mdx ->
  (c = 34 -> forall ms' mdx',
     ms' = mkst (ms_regs ms') (Z_to_bv 64 A_parse_string) (ms_mem ms') (seg_rom tfibsegs) ->
     YK11.getr (ms_regs ms') 10%bv = Z_to_bv 64 q -> YK11.getr (ms_regs ms') 1%bv = Z_to_bv 64 0x831b0 ->
     (forall r, In r PV_KEPT -> YK11.getr (ms_regs ms') r = YK11.getr (ms_regs ms) r) ->
     val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms')) v 4 4 ->
     ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison U (ms_mem ms')) mdx' k ->
     ARU tfibsegs B lyc Sc U W (ms_mem ms') mdx' ->
     (forall x : word, ~ (v <= bv_unsigned x < v + 4) ->
        mrestrict (w_H W) (ms_mem ms') x = mrestrict (w_H W) (ms_mem ms) x) ->
     (forall o, 0 <= o < 56 -> writable_at tfibsegs (mrestrict (w_H W) (ms_mem ms')) (v + o)) ->
     SRr tfibsegs W (mkCfg ms' mdx') Q) ->
  (c = 123 -> forall ms' mdx',
     ms' = mkst (ms_regs ms') (Z_to_bv 64 A_parse_items) (ms_mem ms') (seg_rom tfibsegs) ->
     YK11.getr (ms_regs ms') 10%bv = Z_to_bv 64 q -> YK11.getr (ms_regs ms') 11%bv = Z_to_bv 64 v ->
     YK11.getr (ms_regs ms') 12%bv = Z_to_bv 64 1 -> YK11.getr (ms_regs ms') 1%bv = Z_to_bv 64 0x8327c ->
     (forall r, In r PV_KEPT -> YK11.getr (ms_regs ms') r = YK11.getr (ms_regs ms) r) ->
     ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison U (ms_mem ms')) mdx' k ->
     ARU tfibsegs B lyc Sc U W (ms_mem ms') mdx' ->
     (forall x : word, mrestrict (w_H W) (ms_mem ms') x = mrestrict (w_H W) (ms_mem ms) x) ->
     SRr tfibsegs W (mkCfg ms' mdx') Q) ->
  SRr tfibsegs W (mkCfg ms mdx) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc U W ms mdx k v q cur endv c Q Hms R19 R20 R23 Hv1 Hv2 Hv8 Hvsh Hq Hq8
  Hqc Hqlo Hqhi Hcur Hend Hend47 Hcq Hcv Hcsh Hc Vq0 Vq8 Vc HRAc HRAv Wv HAWR HJ HARU Kstr Kobj.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (ARU_AR tfibsegs B lyc Sc U W (ms_mem ms) mdx HARU) as HAR.
assert (Hc0 : 0 <= c <= 255) by (destruct Hc as [->| ->]; lia).
pose proof (pd_ok (w_H W) (ms_regs ms) (ms_mem ms) v q cur endv c R19 R20 R23 ltac:(lia) Hv8 Hq Hq8 ltac:(lia) Hc0
  ltac:(lia) ltac:(lia) Vq0 Vq8 Vc) as HS.
rewrite <- Hms in HS.
set (E := Ereg (ms_regs ms) (pd_xs cur endv c)) in HS.
assert (EA : forall (r : bv 5) n z, Z.of_nat n = bv_unsigned r -> getr (ms_regs ms) r = Z_to_bv 64 z -> ew E n = Z_to_bv 64 z)
  by (intros r n z Hn Hr; subst E; rewrite (ew_Ereg_nat _ _ n r Hn), Hr; reflexivity).
assert (E19 : ew E 19 = Z_to_bv 64 v) by (apply (EA 19%bv); [reflexivity | exact R19]).
assert (E20 : ew E 20 = Z_to_bv 64 q) by (apply (EA 20%bv); [reflexivity | exact R20]).
assert (E23 : ew E 23 = Z_to_bv 64 SHADOW_OFF) by (apply (EA 23%bv); [reflexivity | exact R23]).
assert (E33 : ew E 33 = Z_to_bv 64 cur) by (subst E; change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E34 : ew E 34 = Z_to_bv 64 endv) by (subst E; change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E35 : ew E 35 = Z_to_bv 64 c) by (subst E; change 35%nat with (32 + 3)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (B19 : bv_unsigned (ew E 19) = v) by (rewrite E19; apply unsigned_lit_small; lia).
assert (B20 : bv_unsigned (ew E 20) = q) by (rewrite E20; apply unsigned_lit_small; lia).
assert (B33 : bv_unsigned (ew E 33) = cur) by (rewrite E33; apply unsigned_lit_small; lia).
assert (UB : YP0e.U E pd_Bx = SHADOW_OFF) by (unfold pd_Bx; apply (U_atom E 23 SHADOW_OFF E23); unfold SHADOW_OFF; lia).
(* the token run's shadow entries: q (stack, shadow 0), the byte at in->p, v (pobj's addressable 56 bytes) *)
assert (SHOK : sh_ok tfibsegs pd_Bx pd_SH E (mrestrict (w_H W) (ms_mem ms))).
{ constructor; [|constructor; [|constructor; [|constructor]]].
  - split.
    + cbn [she_m she_lo she_hi]. rewrite (U_atom E 20 q E20 ltac:(lia)), Z.add_0_r.
      eapply (obl_of_range tfibsegs (w_H W) (ms_mem ms) E pd_Bx q 24 q 24); [|exact UB | lia | lia].
      apply (pv_ra_unpoison B lyc Sc U W (ms_mem ms) _ q 24 HARU); [lia | lia|].
      apply (pv_stack_ra B lyc Sc W _ _ q 24 HAR); [lia | lia | exact Hq8 | reflexivity | lia].
    + intros a Ha. cbn [she_m she_lo she_hi] in Ha. rewrite (U_atom E 20 q E20 ltac:(lia)) in Ha. rewrite UB.
      unfold SHADOW_OFF. lia.
  - split.
    + cbn [she_m she_lo she_hi]. rewrite (U_atom E 33 cur E33 ltac:(lia)), Z.add_0_r.
      exact (obl_of_range tfibsegs (w_H W) (ms_mem ms) E pd_Bx cur 1 cur 1 HRAc UB ltac:(lia) ltac:(lia)).
    + intros a Ha. cbn [she_m she_lo she_hi] in Ha. rewrite (U_atom E 33 cur E33 ltac:(lia)) in Ha. rewrite UB.
      unfold SHADOW_OFF in *. lia.
  - split.
    + cbn [she_m she_lo she_hi]. rewrite (U_atom E 19 v E19 ltac:(lia)), Z.add_0_r.
      exact (obl_of_range tfibsegs (w_H W) (ms_mem ms) E pd_Bx v 56 v 56 HRAv UB ltac:(lia) ltac:(lia)).
    + intros a Ha. cbn [she_m she_lo she_hi] in Ha. rewrite (U_atom E 19 v E19 ltac:(lia)) in Ha. rewrite UB.
      unfold SHADOW_OFF in *. lia. }
(* 0x830d4 .. `bgeu in->p, in->end` 0x83108: q's alignment and its two shadow checks, the two loads *)
fsw_aj_run_tokU pv_tbl_ok HS HJ HARU SHOK fs_Bspan.
{ unfold pd_st, pd_q_region, pd_txt_region. pd_awr_ro. }
eapply SRr_sym_branch with (c := BC_GEU) (a := SOff 33 0) (b := SOff 34 0); [exact HS | |].
{ intros Hb _. exfalso. rewrite branch_geu_U, (pv_U_off _ 33 cur 0), (pv_U_off _ 34 endv 0) in Hb
    by first [pv_ewo; first [exact E33 | exact E34] | lia].
  apply negb_true_iff, Z.ltb_ge in Hb. lia. }
intros _ HS1. clear HS. rename HS1 into HS.
(* .. `beqz in->p` (decided), the byte's shadow check (covered), the byte, and the first dispatch test 0x83128 *)
fsw_aj_run_tokU pv_tbl_ok HS HJ HARU SHOK fs_Bspan.
{ pd_awr_ro. }
assert (DLT : forall Ex, ew Ex 35 = Z_to_bv 64 c ->
  branch_taken BC_LT (sv_denot Ex (SLit 109)) (sv_denot Ex (SOff 35 0)) = (109 <? c)).
{ intros Ex H35. rewrite (pv_denot_lit Ex 109 ltac:(lia)), (pv_denot_off Ex 35 c 0 H35 ltac:(lia) ltac:(lia)).
  rewrite Z.add_0_r. exact (bv_lts_small 109 c ltac:(lia) ltac:(destruct Hc as [->| ->]; lia)). }
assert (DEQ : forall Ex (zz : Z), ew Ex 35 = Z_to_bv 64 c -> 0 <= zz < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot Ex (SOff 35 0)) (sv_denot Ex (SLit zz)) = (c =? zz)).
{ intros Ex zz H35 Hzz. rewrite branch_eq_U, (pv_U_off Ex 35 c 0 H35 ltac:(lia) ltac:(lia)), U_lit by lia.
  rewrite Z.add_0_r. reflexivity. }
destruct Hc as [Hc34 | Hc123].
- (* the string arm *)
  lazymatch type of HS with st_ok _ ?Ey _ _ => assert (G35 : ew Ey 35 = Z_to_bv 64 c) by (pv_ewo; exact E35) end.
  eapply SRr_sym_branch with (c := BC_LT) (a := SLit 109) (b := SOff 35 0); [exact HS | |].
  { intros Hb _. exfalso. rewrite (DLT _ G35) in Hb. rewrite Hc34 in Hb. discriminate Hb. }
  intros _ HS1. clear HS G35. rename HS1 into HS.
  fsw_aj_run_tokU pv_tbl_ok HS HJ HARU SHOK fs_Bspan.
  { pd_awr_ro. }
  lazymatch type of HS with st_ok _ ?Ey _ _ => assert (G35 : ew Ey 35 = Z_to_bv 64 c) by (pv_ewo; exact E35) end.
  eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 35 0) (b := SLit 34); [exact HS | |].
  2: { intros Hb _. exfalso. rewrite (DEQ _ 34 G35 ltac:(lia)) in Hb. rewrite Hc34 in Hb. discriminate Hb. }
  intros _ HS1. clear HS G35. rename HS1 into HS.
  (* 0x83184: v's region, written by v->type := 4; the memory is still the dispatch's (read-only runs) *)
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msF) =>
    assert (KEEP0 : forall x : word, mrestrict (w_H W) (ms_mem msF) x = mrestrict (w_H W) (ms_mem ms) x) by pd_keep_all end.
  lazymatch type of HS with st_ok _ ?Ey _ (restrict _ ?msF) =>
    assert (ROKv : region_ok tfibsegs Ey (mrestrict (w_H W) (ms_mem msF)) pd_v_region) end.
  { unfold region_ok, pd_v_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    pv_ewo. rewrite B19. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (proj1 (pv_wr_keep _ _ (v + o) (KEEP0 _))). apply Wv. lia. }
  pv_addreg HS pd_v_region ROKv.
  { pv_ewo. rewrite B19, B20, B33. unfold zdisj. cbn [fst snd].
    repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
  fsw_aj_run_to_tokU pv_tbl_ok HS HJ HARU SHOK fs_Bspan A_parse_string.
  { cbn [ss_mem add_cond].
    eapply awr_ok_cons_gen with (k := 19%nat) (b := v); [reflexivity | pv_ewo; exact B19 | | pd_awr_ro].
    intros a Ha. cbn [YP09.r_wlo YP09.r_whi pd_v_region] in Ha. apply HAWR. unfold in_zr. cbn [fst snd]. lia. }
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msF) =>
    assert (KEEP : forall x : word, ~ (v <= bv_unsigned x < v + 4) ->
      mrestrict (w_H W) (ms_mem msF) x = mrestrict (w_H W) (ms_mem ms) x) end.
  { intros x Hx.
    repeat lazymatch goal with
    | |- mrestrict ?Hh (ms_mem ?mA) x = mrestrict ?Hh (ms_mem ms) x =>
        lazymatch goal with
        | HFx : frame_of _ _ (mrestrict Hh (ms_mem _)) (mrestrict Hh (ms_mem mA)) |- _ =>
            rewrite (pv_frame_P _ _ _ _ (fun a => v <= a < v + 4) HFx
              ltac:(pd_wr_P ltac:(fun H => rewrite ?B19 in H)) x Hx)
        end
    end; reflexivity. }
  lazymatch type of HS with st_ok _ ?Ey _ _ => set (E1 := Ey) in * end.
  assert (F19 : bv_unsigned (ew E1 19) = v) by (subst E1; pv_ewo; exact B19).
  assert (F20 : ew E1 20 = Z_to_bv 64 q) by (subst E1; pv_ewo; exact E20).
  pv_reg HS (w_H W) (10%bv : bv 5) H10. pv_reg HS (w_H W) (1%bv : bv 5) H1.
  rewrite fsw_SOff0, F20 in H10.
  pose proof (st_ok_restrict_mkst tfibsegs (w_H W) _ _ _ HS eq_refl) as Hshape.
  lazymatch type of Hshape with _ = mkst _ (Z_to_bv 64 ?pc) _ _ =>
    let pc' := eval vm_compute in pc in change pc with pc' in Hshape end.
  pv_region HS 0%nat RV. cbn [ms_mem restrict] in RV.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msF) =>
    assert (Vty : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) v 4 4) end.
  { pose proof (fsw_field _ _ 19 v _ 0 56 0 4 0 4 (SLit 4) 4 RV F19 ltac:(cbn [In]; tauto)
      ltac:(apply pv_denot_lit; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as V.
    rewrite Z.add_0_r in V. exact V. }
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msF) =>
    assert (Wv' : forall o, 0 <= o < 56 -> writable_at tfibsegs (mrestrict (w_H W) (ms_mem msF)) (v + o)) end.
  { intros o Ho. destruct (Z_lt_le_dec o 4) as [Hl|Hl].
    - destruct RV as (_ & _ & RW & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RW. rewrite F19 in RW.
      apply RW. lia.
    - apply (proj1 (pv_wr_keep _ _ (v + o) (KEEP (Z_to_bv 64 (v + o)) ltac:(rewrite wz by lia; lia)))). apply Wv. lia. }
  apply (Kstr Hc34 _ _); [exact Hshape | exact H10 | | | exact Vty | exact HJ | exact HARU | exact KEEP | exact Wv'].
  + rewrite H1. apply pv_denot_lit. lia.
  + lazymatch type of HS with st_ok _ _ _ (restrict _ ?msF) =>
      apply (pv_regs_keep (w_H W) E1 _ msF (ms_regs ms) (pd_xs cur endv c) HS) end;
      [vm_compute; reflexivity | intros nn Hnn; subst E1; rewrite ?ew_ewset_other by lia; reflexivity].
- (* the object arm *)
  lazymatch type of HS with st_ok _ ?Ey _ _ => assert (G35 : ew Ey 35 = Z_to_bv 64 c) by (pv_ewo; exact E35) end.
  eapply SRr_sym_branch with (c := BC_LT) (a := SLit 109) (b := SOff 35 0); [exact HS | |].
  2: { intros Hb _. exfalso. rewrite (DLT _ G35) in Hb. rewrite Hc123 in Hb. discriminate Hb. }
  intros _ HS1. clear HS G35. rename HS1 into HS.
  fsw_aj_run_tokU pv_tbl_ok HS HJ HARU SHOK fs_Bspan.
  { pd_awr_ro. }
  lazymatch type of HS with st_ok _ ?Ey _ _ => assert (G35 : ew Ey 35 = Z_to_bv 64 c) by (pv_ewo; exact E35) end.
  eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 35 0) (b := SLit 110); [exact HS | |].
  { intros Hb _. exfalso. rewrite (DEQ _ 110 G35 ltac:(lia)) in Hb. rewrite Hc123 in Hb. discriminate Hb. }
  intros _ HS1. clear HS G35. rename HS1 into HS.
  fsw_aj_run_tokU pv_tbl_ok HS HJ HARU SHOK fs_Bspan.
  { pd_awr_ro. }
  lazymatch type of HS with st_ok _ ?Ey _ _ => assert (G35 : ew Ey 35 = Z_to_bv 64 c) by (pv_ewo; exact E35) end.
  eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 35 0) (b := SLit 116); [exact HS | |].
  { intros Hb _. exfalso. rewrite (DEQ _ 116 G35 ltac:(lia)) in Hb. rewrite Hc123 in Hb. discriminate Hb. }
  intros _ HS1. clear HS G35. rename HS1 into HS.
  fsw_aj_run_tokU pv_tbl_ok HS HJ HARU SHOK fs_Bspan.
  { pd_awr_ro. }
  lazymatch type of HS with st_ok _ ?Ey _ _ => assert (G35 : ew Ey 35 = Z_to_bv 64 c) by (pv_ewo; exact E35) end.
  eapply SRr_sym_branch with (c := BC_NE) (a := SOff 35 0) (b := SLit 123); [exact HS | |].
  { intros Hb _. exfalso. rewrite branch_ne_U, (pv_U_off _ 35 c 0 G35 ltac:(lia) ltac:(lia)), U_lit in Hb by lia.
    rewrite Z.add_0_r, Hc123 in Hb. discriminate Hb. }
  intros _ HS1. clear HS G35. rename HS1 into HS.
  fsw_aj_run_to_tokU pv_tbl_ok HS HJ HARU SHOK fs_Bspan A_parse_items.
  { pd_awr_ro. }
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msF) =>
    assert (KEEP : forall x : word, mrestrict (w_H W) (ms_mem msF) x = mrestrict (w_H W) (ms_mem ms) x) by pd_keep_all end.
  lazymatch type of HS with st_ok _ ?Ey _ _ => set (E1 := Ey) in * end.
  assert (F19 : ew E1 19 = Z_to_bv 64 v) by (subst E1; pv_ewo; exact E19).
  assert (F20 : ew E1 20 = Z_to_bv 64 q) by (subst E1; pv_ewo; exact E20).
  pv_reg HS (w_H W) (10%bv : bv 5) H10. pv_reg HS (w_H W) (11%bv : bv 5) H11. pv_reg HS (w_H W) (12%bv : bv 5) H12.
  pv_reg HS (w_H W) (1%bv : bv 5) H1.
  rewrite fsw_SOff0, F20 in H10. rewrite fsw_SOff0, F19 in H11.
  pose proof (st_ok_restrict_mkst tfibsegs (w_H W) _ _ _ HS eq_refl) as Hshape.
  lazymatch type of Hshape with _ = mkst _ (Z_to_bv 64 ?pc) _ _ =>
    let pc' := eval vm_compute in pc in change pc with pc' in Hshape end.
  apply (Kobj Hc123 _ _); [exact Hshape | exact H10 | exact H11 | | | | exact HJ | exact HARU | exact KEEP].
  + rewrite H12. apply pv_denot_lit. lia.
  + rewrite H1. apply pv_denot_lit. lia.
  + lazymatch type of HS with st_ok _ _ _ (restrict _ ?msF) =>
      apply (pv_regs_keep (w_H W) E1 _ msF (ms_regs ms) (pd_xs cur endv c) HS) end;
      [vm_compute; reflexivity | intros nn Hnn; subst E1; rewrite ?ew_ewset_other by lia; reflexivity].
Qed.
End DSP.

(* ================= segment 3: after parse_string, 0x831b0 -> the epilogue 0x8329c =================
   The state at 0x831b0 is built afresh (ps2_st): v (atom 19, 56 bytes, writable), the shadow base (atom 23), the
   string a (atom 10 = a0, a >= 4096 + HEAD by parse_string_spec's post). MEASURED (vm_compute over pv_tbl from
   ps2_st): s3 := v + 16 (0x831b0), `bnez` on v + 16's shadow byte (0x831c0) -> __asan_report_store8 0x83564: NOT
   taken, token covered by ps2_SH's v entry; v->str := a (0x831c4), s5 := (a <> 0) - 1 (0x831c8 / 0x831cc), `j`
   0x831d0 -> 0x8329c. The only write is v->str, [v + 16, v + 24). *)
Definition ps2_v_region : YP09.region := YP09.mkRegion (Some 19%nat) 0 56 16 24 [].
Definition ps2_facts : facts :=
  mkFacts [(19%nat, mkAF 4096 (2 ^ 47 - 56) 3); (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (10%nat, mkAF 4096 (2 ^ 47) 0)]
    [] [].
Definition ps2_st : sstate := mkSS 0x831b0 sr_atoms [ps2_v_region] None ps2_facts.
Definition ps2_SH : list shent := [mkSHE 19 0 56].
(* the callee-saved registers segment 3 keeps: every one but s3 (v + 16) and s5 (the result) *)
Definition PS_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 20; 22; 23; 24; 25; 26; 27]%bv.

Section PS. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Lemma ps2_ok : forall (H : word -> bool) regs mem extra v a,
  YK11.getr regs 19%bv = Z_to_bv 64 v -> YK11.getr regs 23%bv = Z_to_bv 64 SHADOW_OFF ->
  YK11.getr regs 10%bv = Z_to_bv 64 a ->
  4096 <= v <= 2 ^ 47 - 56 -> v mod 8 = 0 -> 4096 <= a <= 2 ^ 47 ->
  (forall o, 0 <= o < 56 -> writable_at tfibsegs (mrestrict H mem) (v + o)) ->
  st_ok tfibsegs (Ereg regs extra) ps2_st (restrict H (mkst regs (Z_to_bv 64 0x831b0) mem (seg_rom tfibsegs))).
Proof.
intros H regs mem extra v a R19 R23 R10 Hv Hv8 Ha Wv.
set (E := Ereg regs extra).
pose proof asan_consts as (C1 & _).
assert (E19 : bv_unsigned (ew E 19) = v) by (subst E; rewrite (ew_Ereg_nat regs extra 19 19%bv eq_refl), R19; apply wz; lia).
assert (E23 : bv_unsigned (ew E 23) = SHADOW_OFF)
  by (subst E; rewrite (ew_Ereg_nat regs extra 23 23%bv eq_refl), R23; apply wz; unfold SHADOW_OFF; lia).
assert (E10 : bv_unsigned (ew E 10) = a) by (subst E; rewrite (ew_Ereg_nat regs extra 10 10%bv eq_refl), R10; apply wz; lia).
rewrite restrict_mkst_fx. unfold ps2_st. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold ps2_v_region. constructor; [|constructor].
  unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. fold E.
  rewrite E19. split; [lia|]. split; [lia|]. split; [intros o Ho; apply Wv; lia | apply Forall_nil].
- apply pairwise_disjoint_of_extents. unfold ps2_v_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint]. split; exact I.
- unfold ps2_facts. split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  fold E. rewrite E19, E23, E10. change (2 ^ 3) with 8. rewrite Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; try lia; unfold SHADOW_OFF; lia.
Qed.
End PS.

Section PS1. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Lemma pv_str1 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc U (W : world tfibsegs) regs mem2 md2 k v a
  (Q : world tfibsegs -> config -> Prop),
  YK11.getr regs 19%bv = Z_to_bv 64 v -> YK11.getr regs 23%bv = Z_to_bv 64 SHADOW_OFF ->
  YK11.getr regs 10%bv = Z_to_bv 64 a ->
  4096 <= v -> v + 56 <= 2 ^ 47 -> v mod 8 = 0 -> 4096 <= a <= 2 ^ 47 ->
  (v + 56 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= v) ->
  range_addressable (aview tfibsegs (w_H W) mem2) SHADOW_OFF v 56 ->
  (forall o, 0 <= o < 56 -> writable_at tfibsegs (mrestrict (w_H W) mem2) (v + o)) ->
  (forall a, in_zr a (v, 56) -> awr_byte tfibsegs B STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own (frames S) a) ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison U mem2) md2 k ->
  ARU tfibsegs B lyc Sc U W mem2 md2 ->
  (forall ms' mdx',
     ms' = mkst (ms_regs ms') (Z_to_bv 64 0x8329c) (ms_mem ms') (seg_rom tfibsegs) ->
     YK11.getr (ms_regs ms') 21%bv = Z_to_bv 64 0 ->
     (forall r, In r PS_KEPT -> YK11.getr (ms_regs ms') r = YK11.getr regs r) ->
     val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms')) (v + 16) 8 a ->
     ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison U (ms_mem ms')) mdx' k ->
     ARU tfibsegs B lyc Sc U W (ms_mem ms') mdx' ->
     (forall x : word, ~ (v + 16 <= bv_unsigned x < v + 24) ->
        mrestrict (w_H W) (ms_mem ms') x = mrestrict (w_H W) mem2 x) ->
     (forall o, 0 <= o < 56 -> writable_at tfibsegs (mrestrict (w_H W) (ms_mem ms')) (v + o)) ->
     SRr tfibsegs W (mkCfg ms' mdx') Q) ->
  SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 0x831b0) mem2 (seg_rom tfibsegs)) md2) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc U W regs mem2 md2 k v a Q R19 R23 R10 Hv1 Hv2 Hv8 Ha Hvb HRA Wv HAWR
  HJ HARU K.
pose proof asan_consts as (C1 & _).
pose proof (ps2_ok (w_H W) regs mem2 fs_extraT v a R19 R23 R10 ltac:(lia) Hv8 Ha Wv) as HS.
set (E := Ereg regs fs_extraT) in HS.
assert (E19 : bv_unsigned (ew E 19) = v)
  by (subst E; rewrite (ew_Ereg_nat regs fs_extraT 19 19%bv eq_refl), R19; apply wz; lia).
assert (E19' : ew E 19 = Z_to_bv 64 v)
  by (subst E; rewrite (ew_Ereg_nat regs fs_extraT 19 19%bv eq_refl), R19; reflexivity).
assert (E23 : bv_unsigned (ew E 23) = SHADOW_OFF)
  by (subst E; rewrite (ew_Ereg_nat regs fs_extraT 23 23%bv eq_refl), R23; apply wz; unfold SHADOW_OFF; lia).
assert (E10 : ew E 10 = Z_to_bv 64 a) by (subst E; rewrite (ew_Ereg_nat regs fs_extraT 10 10%bv eq_refl), R10; reflexivity).
assert (UB : YP0e.U E pd_Bx = SHADOW_OFF) by (unfold pd_Bx; rewrite U_SOff, E23; apply zcanon_id; unfold M64, SHADOW_OFF; lia).
assert (SHOK : sh_ok tfibsegs pd_Bx ps2_SH E (mrestrict (w_H W) mem2)).
{ constructor; [|constructor]. split.
  - cbn [she_m she_lo she_hi]. rewrite (U_atom E 19 v E19' ltac:(lia)), Z.add_0_r.
    exact (obl_of_range tfibsegs (w_H W) mem2 E pd_Bx v 56 v 56 HRA UB ltac:(lia) ltac:(lia)).
  - intros x Hx. cbn [she_m she_lo she_hi] in Hx. rewrite (U_atom E 19 v E19' ltac:(lia)) in Hx.
    rewrite UB. unfold SHADOW_OFF in *. lia. }
fsw_aj_run_to_tokU pv_tbl_ok HS HJ HARU SHOK fs_Bspan 0x8329c.
{ cbn [ss_mem ps2_st]. eapply awr_ok_cons_gen with (k := 19%nat) (b := v); [reflexivity | exact E19 | | apply awr_ok_nil].
  intros x Hx. cbn [YP09.r_wlo YP09.r_whi ps2_v_region] in Hx. apply HAWR. unfold in_zr. cbn [fst snd]. lia. }
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msF) =>
  assert (KEEP : forall x : word, ~ (v + 16 <= bv_unsigned x < v + 24) ->
    mrestrict (w_H W) (ms_mem msF) x = mrestrict (w_H W) mem2 x) end.
{ intros x Hx.
  rewrite (pv_frame_P _ _ _ _ (fun z => v + 16 <= z < v + 24) HFr
    ltac:(intros z Hz; cbn [ss_mem ps2_st] in Hz; apply pv_wrange_cases in Hz; destruct Hz as [Hz|Hz];
          [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ps2_v_region] in Hz; rewrite E19 in Hz; lia
          | exfalso; exact (pv_wrange_nil _ _ Hz)]) x Hx).
  reflexivity. }
lazymatch type of HS with st_ok _ ?Ey _ _ => set (E1 := Ey) in * end.
assert (F19 : bv_unsigned (ew E1 19) = v) by (subst E1; pv_ewo; exact E19).
assert (F10 : ew E1 10 = Z_to_bv 64 a) by (subst E1; pv_ewo; exact E10).
pv_reg HS (w_H W) (21%bv : bv 5) H21.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) _ _ _ HS eq_refl) as Hshape.
lazymatch type of Hshape with _ = mkst _ (Z_to_bv 64 ?pc) _ _ =>
  let pc' := eval vm_compute in pc in change pc with pc' in Hshape end.
pv_region HS 0%nat RV. cbn [ms_mem restrict] in RV.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msF) =>
  assert (Vstr : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) (v + 16) 8 a) end.
{ exact (fsw_field _ _ 19 v _ 0 56 16 24 16 8 (SOff 10 0) a RV F19 ltac:(cbn [In]; tauto)
    ltac:(rewrite fsw_SOff0; exact F10) ltac:(cbn; lia) ltac:(cbn; lia)). }
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msF) =>
  assert (Wv' : forall o, 0 <= o < 56 -> writable_at tfibsegs (mrestrict (w_H W) (ms_mem msF)) (v + o)) end.
{ intros o Ho. destruct (Z_lt_le_dec o 16) as [Hl|Hl]; [|destruct (Z_lt_le_dec o 24) as [Hl2|Hl2]].
  - apply (proj1 (pv_wr_keep _ _ (v + o) (KEEP (Z_to_bv 64 (v + o)) ltac:(rewrite wz by lia; lia)))). apply Wv. lia.
  - destruct RV as (_ & _ & RW & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RW. rewrite F19 in RW.
    apply RW. lia.
  - apply (proj1 (pv_wr_keep _ _ (v + o) (KEEP (Z_to_bv 64 (v + o)) ltac:(rewrite wz by lia; lia)))). apply Wv. lia. }
apply (K _ _); [exact Hshape | | | exact Vstr | exact HJ | exact HARU | exact KEEP | exact Wv'].
- rewrite H21. apply pv_denot_lit. lia.
- lazymatch type of HS with st_ok _ _ _ (restrict _ ?msF) =>
    intros r Hr; apply (pv_regs_keep_l PS_KEPT (w_H W) E1 _ msF regs fs_extraT HS) end;
    [vm_compute; reflexivity | intros nn Hnn; subst E1; rewrite ?ew_ewset_other by lia; reflexivity | exact Hr].
Qed.
End PS1.

(* ================= segment 4: the epilogue 0x8329c (string arm) / 0x8327c (object arm) -> `ret` 0x8333c ==========
   Ported from image A's walk (c4ac4207dc3 lib/A/FSH_parse_value.v pe_st / pe_ok / pe_extra / pv_epi, A 0x83318 ->
   0x833b8), on B's registers: B keeps F's shadow address in s11 (atom 27; A: s8). The state: F (atom 26, also s2
   through SOff 26 0), F's shadow (atom 27), the flag byte (atom 46, the address the word at F + 56 holds), and the 13
   saved words at s0 (atom 8, read only). MEASURED (vm_compute over pv_tbl): [object arm only: `j` 0x8327c -> 0x83298,
   s5 := a0 (0x83298)]; F's magic := 0x45e0360e (0x832a4), `beqz s2` 0x832a8 NOT taken (atom 26's fact F >= 4096: the
   real-stack exit 0x832dc .. 0x832f8 is not reached), F's shadow := f5 x 8 (0x832b0 .. 0x832cc), a0 := the word at
   F + 56 (0x832d0), the flag byte := 0 (0x832d4, which releases the frame through FSW_frame.fsw_flag_storeU), `j`
   0x832d8 -> 0x832fc, a0 := s5, sp := s0 - 160, ra, s0 .. s11 reloaded, `ret` 0x8333c (FSW_ret.fsw_retU). No shadow
   check, no UBSan check, no obligation. *)
Definition pe_regs : list sv := sr_set sr_atoms 18%bv (SOff 26 0).
Definition pe_s0_region : YP09.region := YP09.mkRegion (Some 8%nat) (-104) 0 0 0 pv_sv_chunks.
Definition pe_F_region : YP09.region :=
  YP09.mkRegion (Some 26%nat) 0 64 0 64 [YP09.mkChunk 56 (CVal 8 (SOff 46 0))].
Definition pe_sh_region : YP09.region := YP09.mkRegion (Some 27%nat) 0 8 0 8 [].
Definition pe_fl_region : YP09.region := YP09.mkRegion (Some 46%nat) 0 1 0 1 [].
Definition pe_facts : facts :=
  mkFacts [(8%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (26%nat, mkAF 4096 (2 ^ 47) 5);
           (27%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 2); (46%nat, mkAF 4096 (2 ^ 47) 0)] [] [].
Definition pe_st (pc : Z) : sstate :=
  mkSS pc pe_regs [pe_F_region; pe_sh_region; pe_fl_region; pe_s0_region] None pe_facts.
(* what the epilogue writes: F's 64 bytes, F's shadow, the flag byte *)
Definition pe_wr (F FL a : Z) : Prop :=
  (F <= a < F + 64) \/ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 8) \/ (FL <= a < FL + 1).

Section EP. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Lemma pe_ok : forall (H : word -> bool) regs mem regs0 F FL s xs pc,
  YK11.getr regs 8%bv = Z_to_bv 64 s -> YK11.getr regs 18%bv = Z_to_bv 64 F ->
  YK11.getr regs 27%bv = Z_to_bv 64 (SHADOW_OFF + F / 8) -> YK11.getr regs 26%bv = Z_to_bv 64 F ->
  2 ^ 46 <= s <= 2 ^ 47 -> s mod 16 = 0 -> 4096 <= F -> F + 64 <= 2 ^ 47 -> F mod 32 = 0 ->
  4096 <= FL <= 2 ^ 47 ->
  F + 64 <= s - 104 -> (FL + 1 <= F \/ F + 64 <= FL) -> (FL + 1 <= s - 104 \/ s <= FL) ->
  (F + 64 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= F) -> (FL + 1 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= FL) ->
  pv_saved_ok (mrestrict H mem) s regs0 ->
  val_mem tfibsegs (mrestrict H mem) (F + 56) 8 FL ->
  (forall o, 0 <= o < 64 -> writable_at tfibsegs (mrestrict H mem) (F + o)) ->
  (forall o, 0 <= o < 8 -> writable_at tfibsegs (mrestrict H mem) (SHADOW_OFF + F / 8 + o)) ->
  writable_at tfibsegs (mrestrict H mem) FL ->
  st_ok tfibsegs (Ereg regs (pv_extra0 regs0 FL ++ xs)) (pe_st pc)
    (restrict H (mkst regs (Z_to_bv 64 pc) mem (seg_rom tfibsegs))).
Proof.
intros H regs mem regs0 F FL s xs pc R8 R18 R27 R26 Hs Hs16 HF1 HF2 HF32 HFL Hfs Hflf Hfls Hfsh Hflsh Vsv Vfl WF Wsh
  Wfl.
set (E := Ereg regs (pv_extra0 regs0 FL ++ xs)).
pose proof asan_consts as (C1 & _ & C3 & _).
assert (A : forall (r : bv 5) n z, Z.of_nat n = bv_unsigned r -> getr regs r = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 ->
  bv_unsigned (ew E n) = z) by (intros r n z Hn Hr Hz; subst E; rewrite (ew_Ereg_nat _ _ n r Hn), Hr; apply wz; exact Hz).
assert (HF8 : 512 <= F / 8 <= 2 ^ 44) by (split; [apply Z.div_le_lower_bound | apply Z.div_le_upper_bound]; lia).
assert (E8 : bv_unsigned (ew E 8) = s) by (apply (A 8%bv); [reflexivity | exact R8 | lia]).
assert (E27 : bv_unsigned (ew E 27) = SHADOW_OFF + F / 8)
  by (apply (A 27%bv); [reflexivity | exact R27 | unfold SHADOW_OFF in *; lia]).
assert (E26 : bv_unsigned (ew E 26) = F) by (apply (A 26%bv); [reflexivity | exact R26 | lia]).
assert (E46 : bv_unsigned (ew E 46) = FL).
{ subst E. change 46%nat with (32 + 14)%nat. rewrite ew_Ereg_extra.
  rewrite app_nth1 by (cbn [length pv_extra0]; lia). cbn [nth pv_extra0]. apply wz. lia. }
assert (D : forall n v, bv_unsigned (ew E n) = v -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
  by (intros n v Hn; rewrite fsw_SOff0, <- Hn; symmetry; apply Z_to_bv_bv_unsigned).
rewrite restrict_mkst_fx. unfold pe_st. apply (entry_st_ok_full tfibsegs).
- unfold pe_regs. apply regs_ok_pin; [apply regs_ok_Ereg | discriminate |].
  rewrite R18. symmetry. exact (D 26%nat F E26).
- vm_compute. reflexivity.
- unfold pe_F_region, pe_sh_region, pe_fl_region, pe_s0_region.
  constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. fold E.
    rewrite E26. split; [lia|]. split; [lia|]. split; [intros o Ho; apply WF; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val tfibsegs _ _ F 56 8 (SOff 46 0) FL (D 46%nat FL E46)); [cbn; lia | cbn; lia | exact Vfl].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. fold E.
    rewrite E27. split; [unfold SHADOW_OFF in *; lia|]. split; [unfold SHADOW_OFF in *; lia|].
    split; [intros o Ho; apply Wsh; lia | apply Forall_nil].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. fold E.
    rewrite E46. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. replace (FL + o) with FL by lia. exact Wfl.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. fold E.
    rewrite E8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    rewrite pv_sv_chunks_eq.
    assert (SV : forall j, (j < 13)%nat -> YP09.chunk_ok tfibsegs E (mrestrict H mem) s
      (YP09.mkChunk (- 8 * (Z.of_nat j + 1)) (CVal 8 (SOff (33 + j) 0)))).
    { intros j Hj. apply (chunk_ok_val tfibsegs _ _ s _ 8 _ (bv_unsigned (nth j (pv_saved regs0) (Z_to_bv 64 0)))).
      - rewrite Z_to_bv_bv_unsigned. subst E. change (33 + j)%nat with (32 + S j)%nat. rewrite fsw_extra_atom.
        rewrite app_nth1 by (cbn [length pv_extra0]; lia).
        do 13 (destruct j as [|j]; [reflexivity|]). lia.
      - change (8 * Z.of_N 8) with 64. pose proof (u64_range (nth j (pv_saved regs0) (Z_to_bv 64 0))). lia.
      - cbn. lia.
      - replace (s + - 8 * (Z.of_nat j + 1)) with (s - 8 * (Z.of_nat j + 1)) by lia. exact (Vsv j Hj). }
    repeat (apply Forall_cons; [match goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 8 (SOff ?a 0))) =>
      let j := eval vm_compute in (a - 33)%nat in exact (SV j ltac:(lia)) end|]). apply Forall_nil.
- apply pairwise_disjoint_of_extents. unfold pe_F_region, pe_sh_region, pe_fl_region, pe_s0_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold E. rewrite E26, E27, E46, E8.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF in *; lia.
- unfold pe_facts. split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  fold E. rewrite E8, E27, E26, E46. change (2 ^ 4) with 16. change (2 ^ 5) with 32. change (2 ^ 2) with 4.
  rewrite Z.pow_0_r, !Z.mod_1_r.
  assert (HF84 : (F / 8) mod 4 = 0).
  { assert (HFq : F = (F / 32 * 4) * 8) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
    rewrite HFq, Z.div_mul by lia. apply Z_mod_mult. }
  repeat match goal with |- _ /\ _ => split end; try exact I; try (unfold SHADOW_OFF in *; lia).
Qed.
End EP.
(* an extra atom of the walk's env (32 .. 46: the shadow base, the 13 saved words, the flag address) *)
Lemma pe_extra : forall (regs regs0 : bvmap 5 word) FL (xs : list word) (n : nat), (32 <= n < 47)%nat ->
  ew (Ereg regs (pv_extra0 regs0 FL ++ xs)) n = nth (n - 32) (pv_extra0 regs0 FL) (Z_to_bv 64 0).
Proof.
intros regs regs0 FL xs n Hn. replace n with (32 + (n - 32))%nat at 1 by lia. rewrite ew_Ereg_extra.
apply app_nth1. cbn [length pv_extra0]. lia.
Qed.
Ltac pe_wr_tac B26 B27 B46 :=
  let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha; cbn [ss_mem pe_st] in Ha;
  repeat (apply pv_wrange_cases in Ha; destruct Ha as [Ha|Ha];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val pe_F_region pe_sh_region pe_fl_region pe_s0_region] in Ha;
     rewrite ?B26, ?B27, ?B46 in Ha; unfold pe_wr; lia|]);
  exfalso; exact (pv_wrange_nil _ _ Ha).

Section EP2. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the fake-frame kit's unit laws fsw_flag_storeU takes (FSW_frame.v Section f; RUNTIME's, as FSH_Fn_reader.v's header
   names the class-0 stack-free law) *)
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Lemma pv_epi : forall STK ot FP ly S U0 (W0 : world tfibsegs) mem0 md0 lyc S2 U (W : world tfibsegs) regs0 regs mem2 md2
  pos s res k pc (rr : bv 5) (xs : list word)
  (Q : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  let F := frame_addr lyc 0 pos in let FL := flag_addr lyc 0 pos in
  (pc = 0x8329c /\ rr = 21%bv) \/ (pc = 0x8327c /\ rr = 10%bv) ->
  In (0, pos) (frames S2) ->
  YK11.getr regs 8%bv = Z_to_bv 64 s -> YK11.getr regs 18%bv = Z_to_bv 64 F ->
  YK11.getr regs 27%bv = Z_to_bv 64 (SHADOW_OFF + F / 8) -> YK11.getr regs 26%bv = Z_to_bv 64 F ->
  YK11.getr regs rr = Z_to_bv 64 res ->
  YK11.getr regs 3%bv = YK11.getr regs0 3%bv -> YK11.getr regs 4%bv = YK11.getr regs0 4%bv ->
  spZ regs0 = s -> YK0s.ret_ok (YK11.getr regs0 1%bv) ->
  2 ^ 46 <= s <= 2 ^ 47 -> s mod 16 = 0 -> alloc_ceiling + 104 <= s ->
  0 <= res < 2 ^ 64 ->
  pv_saved_ok (mrestrict (w_H W) mem2) s regs0 ->
  val_mem tfibsegs (mrestrict (w_H W) mem2) (F + 56) 8 FL ->
  ajournal tfibsegs B STK ot FP ly S W0 (unpoison U0 mem0) md0 [(0, pos)] lyc S2 W (unpoison U mem2) md2 k ->
  ARU tfibsegs B lyc S2 U W mem2 md2 ->
  (forall mat regsf memf,
     YK11.getr regsf 10%bv = Z_to_bv 64 res ->
     (forall x : word, ~ pe_wr F FL (bv_unsigned x) -> mrestrict (w_H W) memf x = mrestrict (w_H W) mem2 x) ->
     Q lyc (stack_free_state 0 pos S2) W regsf memf (with_vm_backing (m_vm_lazy md2) mat md2)) ->
  SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 pc) mem2 (seg_rom tfibsegs)) md2)
    (fpostU tfibsegs B STK ot FP regs0 ly S U0 W0 mem0 md0 k U Q).
Proof.
intros STK ot FP ly S U0 W0 mem0 md0 lyc S2 U W regs0 regs mem2 md2 pos s res k pc rr xs Q F FL Hpc Hin0 R8 R18 R27
  R26 Rrr R3 R4 Hsp Hra Hs Hs16 Hsc Hres Vsv Vfl HJ HARU HQ.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (ARU_AR tfibsegs B lyc S2 U W mem2 md2 HARU) as HAR.
destruct (al_frames _ _ LAWS lyc S2 W (unpoison U mem2) md2 0 pos HAR Hin0) as (HF32 & HFapp & HFp & HFSp).
destruct (frames_bounds tfibsegs B LAWS lyc S2 W (unpoison U mem2) md2 0 pos HAR Hin0) as (HF4096 & HFc & _).
destruct (al_flag _ _ LAWS lyc S2 W (unpoison U mem2) md2 0 pos HAR Hin0) as (HFLp & HFLo & HFLapp & HFLc).
assert (HFLlo : 4096 <= flag_addr lyc 0 pos) by (unfold in_app in HFLapp; lia).
change (fs_frame_bytes 0) with 64 in *.
fold F in HF32, HFapp, HFp, HFSp, HF4096, HFc. fold FL in HFLp, HFLo, HFLapp, HFLc, HFLlo.
(* the frame's bytes, its shadow and the flag byte are writable; the flag is no frame byte and no stack byte *)
assert (WF : forall o, 0 <= o < 64 -> writable_at tfibsegs (mrestrict (w_H W) mem2) (F + o)).
{ intros o Ho. apply (apresent_writable tfibsegs). destruct (HFp (F + o) ltac:(lia)) as (Hp & Hno).
  exact (fsw_apresent_notowned B lyc S2 U W mem2 md2 (F + o) HARU ltac:(lia) Hno Hp). }
assert (HF8 : 512 <= F / 8 <= 2 ^ 44) by (split; [apply Z.div_le_lower_bound | apply Z.div_le_upper_bound]; lia).
assert (Wsh : forall o, 0 <= o < 8 -> writable_at tfibsegs (mrestrict (w_H W) mem2) (SHADOW_OFF + F / 8 + o)).
{ intros o Ho. apply (apresent_writable tfibsegs). destruct (HFSp o ltac:(change (64 / 8) with 8; lia)) as (Hp & Hno).
  unfold shadow_addr in Hp, Hno.
  exact (fsw_apresent_notowned B lyc S2 U W mem2 md2 (SHADOW_OFF + F / 8 + o) HARU ltac:(unfold SHADOW_OFF; lia) Hno Hp). }
(* the flag byte is no user-poisoned byte of U (those are live blocks' shadow bytes, inside the band; the flag is
   application memory), so the machine's memory holds it where the unpoisoned reading does *)
assert (HflagU : in_ush U FL = false).
{ destruct (in_ush U FL) eqn:Eu; [|reflexivity]. exfalso.
  pose proof (ush_facts tfibsegs B lyc S2 U W mem2 md2 _ HARU Eu) as (_ & L1 & L2).
  unfold in_app, kLowShadowBeg, ASAN_CEIL, kHighMemBeg, SHADOW_OFF in *. lia. }
assert (Wfl : writable_at tfibsegs (mrestrict (w_H W) mem2) FL).
{ apply (apresent_writable tfibsegs). destruct HFLp as (Hh & b & Hb). split; [exact Hh|]. exists b.
  rewrite <- Hb. symmetry. apply unpoison_out. rewrite (wz FL ltac:(unfold in_app in HFLapp; lia)). exact HflagU. }
assert (HflF : FL + 1 <= F \/ F + 64 <= FL).
{ destruct (Z_lt_le_dec FL F) as [Hl|Hl]; [left; lia|]. destruct (Z_le_gt_dec (F + 64) FL) as [Hr|Hr]; [right; lia|].
  exfalso. destruct (HFp FL ltac:(lia)) as (_ & Hno). exact (Hno HFLo). }
assert (HflS : FL + 1 <= s - 104 \/ s <= FL) by lia.
assert (HflSh : FL + 1 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= FL)
  by (unfold in_app, kLowShadowBeg, ASAN_CEIL, kHighMemBeg in HFLapp; unfold SHADOW_OFF; lia).
assert (HFsh : F + 64 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= F)
  by (unfold in_app, kLowShadowBeg, ASAN_CEIL, kHighMemBeg in HFapp; unfold SHADOW_OFF; lia).
assert (HFs : F + 64 <= s - 104) by lia.
pose proof (pe_ok (w_H W) regs mem2 regs0 F FL s xs pc R8 R18 R27 R26 Hs Hs16 ltac:(lia) ltac:(lia) HF32
  ltac:(lia) HFs HflF HflS HFsh HflSh Vsv Vfl WF Wsh Wfl) as HS.
set (E := Ereg regs (pv_extra0 regs0 FL ++ xs)) in HS.
assert (A : forall (r : bv 5) n z, Z.of_nat n = bv_unsigned r -> getr regs r = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 ->
  bv_unsigned (ew E n) = z) by (intros r n z Hn Hr Hz; subst E; rewrite (ew_Ereg_nat _ _ n r Hn), Hr; apply wz; exact Hz).
assert (B27 : bv_unsigned (ew E 27) = SHADOW_OFF + F / 8)
  by (apply (A 27%bv); [reflexivity | exact R27 | unfold SHADOW_OFF in *; lia]).
assert (B26 : bv_unsigned (ew E 26) = F) by (apply (A 26%bv); [reflexivity | exact R26 | lia]).
assert (B46 : bv_unsigned (ew E 46) = FL).
{ subst E. change 46%nat with (32 + 14)%nat. rewrite ew_Ereg_extra.
  rewrite app_nth1 by (cbn [length pv_extra0]; lia). cbn [nth pv_extra0]. apply wz. lia. }
destruct Hpc as [[-> ->] | [-> ->]].
- (* the string arm: from 0x8329c, a0 := s5 *)
  lazymatch eval vm_compute in (sym_runN tfibsegs pv_tbl FUEL (pe_st 0x8329c)) with (?ssF, ?stF) =>
    assert (Hrun : sym_runN tfibsegs pv_tbl FUEL (pe_st 0x8329c) = (ssF, stF)) by (vm_compute; reflexivity);
    apply (fsw_flag_storeU B ML ASF FFL pv_tbl pv_tbl_ok W FUEL E (pe_st 0x8329c) ssF stF _ STK ot FP ly S W0
      (unpoison U0 mem0) md0 [] lyc S2 U md2 k 0 pos _ HS Hrun I HJ HARU ltac:(lia)) end.
  + intros a Ha. cbn [ss_mem pe_st] in Ha.
    apply pv_wrange_cases in Ha; destruct Ha as [Ha|Ha].
    { cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val pe_F_region] in Ha. rewrite B26 in Ha.
      left. unfold awr_byte, awr_byte0. left; right; right; right. exists 0, pos. split; [left; reflexivity|].
      left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 0) with 64. lia. }
    apply pv_wrange_cases in Ha; destruct Ha as [Ha|Ha].
    { cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val pe_sh_region] in Ha. rewrite B27 in Ha.
      left. unfold awr_byte, awr_byte0. left; right; right; right. exists 0, pos. split; [left; reflexivity|].
      right. unfold in_zr, shadow_addr. cbn [fst snd]. change (fs_frame_bytes 0 / 8) with 8. lia. }
    apply pv_wrange_cases in Ha; destruct Ha as [Ha|Ha].
    { cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val pe_fl_region] in Ha. rewrite B46 in Ha. right. lia. }
    apply pv_wrange_cases in Ha; destruct Ha as [Ha|Ha].
    { cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val pe_s0_region] in Ha. lia. }
    exfalso. exact (pv_wrange_nil _ _ Ha).
  + intros msr HSr. pv_region HSr 2%nat RF.
    pose proof (fsw_field _ _ 46 FL _ 0 1 0 1 0 1 (SLit 0) 0 RF B46 ltac:(left; reflexivity)
      ltac:(apply pv_denot_lit; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as V.
    pose proof (V 0%nat ltac:(cbn; lia)) as V0. cbn [Z.of_nat] in V0. rewrite !Z.add_0_r in V0. exact V0.
  + intros msf matf HSf HJf HARUf HFr HFrr HG.
    lazymatch type of HSf with st_ok _ _ ?ssx _ =>
      apply (fsw_retU B pv_tbl pv_tbl_ok W E ssx msf _ STK ot FP regs0 ly S U0 W0 mem0 md0 lyc (stack_free_state 0 pos S2) U k
        Q HSf ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) end.
    * pose proof (fsw_reg_extra _ regs (pv_extra0 regs0 FL ++ xs) _ msf 1%bv 1 HSf ltac:(vm_compute; reflexivity)) as R1F.
      rewrite R1F, app_nth1 by (cbn [length pv_extra0]; lia). cbn [nth pv_extra0]. exact Hra.
    * exact HJf.
    * exact HARUf.
    * intros r Hr. unfold acallee_saved in Hr.
      rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ msf (Z_to_bv 5 r) HSf).
      assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      repeat (destruct Hr' as [->|Hr']); try subst r;
        lazymatch goal with |- sv_denot _ (sr_get (ss_regs ?sx) ?rr) = _ =>
          let t := eval vm_compute in (sr_get (ss_regs sx) rr) in change (sr_get (ss_regs sx) rr) with t end;
        rewrite fsw_SOff0; subst E;
        first
        [ rewrite pe_extra by lia; cbn [Nat.sub nth pv_extra0]; reflexivity
        | rewrite (ew_Ereg_nat regs (pv_extra0 regs0 FL ++ xs) 8 8%bv eq_refl), R8;
          unfold spZ in Hsp; rewrite <- Hsp; apply Z_to_bv_bv_unsigned
        | rewrite (ew_Ereg_nat regs (pv_extra0 regs0 FL ++ xs) 3 3%bv eq_refl); exact R3
        | rewrite (ew_Ereg_nat regs (pv_extra0 regs0 FL ++ xs) 4 4%bv eq_refl); exact R4 ].
    * intros mat. apply HQ.
      -- pv_reg HSf (w_H W) (10%bv : bv 5) H10f. rewrite H10f, fsw_SOff0. subst E.
         rewrite (ew_Ereg_nat regs (pv_extra0 regs0 FL ++ xs) 21 21%bv eq_refl). exact Rrr.
      -- intros x Hx. exact (pv_frame_P _ _ _ _ (pe_wr F FL) HFrr ltac:(pe_wr_tac B26 B27 B46) x Hx).
- (* the object arm: from 0x8327c, `j` 0x83298, s5 := a0, a0 := s5 *)
  lazymatch eval vm_compute in (sym_runN tfibsegs pv_tbl FUEL (pe_st 0x8327c)) with (?ssF, ?stF) =>
    assert (Hrun : sym_runN tfibsegs pv_tbl FUEL (pe_st 0x8327c) = (ssF, stF)) by (vm_compute; reflexivity);
    apply (fsw_flag_storeU B ML ASF FFL pv_tbl pv_tbl_ok W FUEL E (pe_st 0x8327c) ssF stF _ STK ot FP ly S W0
      (unpoison U0 mem0) md0 [] lyc S2 U md2 k 0 pos _ HS Hrun I HJ HARU ltac:(lia)) end.
  + intros a Ha. cbn [ss_mem pe_st] in Ha.
    apply pv_wrange_cases in Ha; destruct Ha as [Ha|Ha].
    { cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val pe_F_region] in Ha. rewrite B26 in Ha.
      left. unfold awr_byte, awr_byte0. left; right; right; right. exists 0, pos. split; [left; reflexivity|].
      left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 0) with 64. lia. }
    apply pv_wrange_cases in Ha; destruct Ha as [Ha|Ha].
    { cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val pe_sh_region] in Ha. rewrite B27 in Ha.
      left. unfold awr_byte, awr_byte0. left; right; right; right. exists 0, pos. split; [left; reflexivity|].
      right. unfold in_zr, shadow_addr. cbn [fst snd]. change (fs_frame_bytes 0 / 8) with 8. lia. }
    apply pv_wrange_cases in Ha; destruct Ha as [Ha|Ha].
    { cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val pe_fl_region] in Ha. rewrite B46 in Ha. right. lia. }
    apply pv_wrange_cases in Ha; destruct Ha as [Ha|Ha].
    { cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val pe_s0_region] in Ha. lia. }
    exfalso. exact (pv_wrange_nil _ _ Ha).
  + intros msr HSr. pv_region HSr 2%nat RF.
    pose proof (fsw_field _ _ 46 FL _ 0 1 0 1 0 1 (SLit 0) 0 RF B46 ltac:(left; reflexivity)
      ltac:(apply pv_denot_lit; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as V.
    pose proof (V 0%nat ltac:(cbn; lia)) as V0. cbn [Z.of_nat] in V0. rewrite !Z.add_0_r in V0. exact V0.
  + intros msf matf HSf HJf HARUf HFr HFrr HG.
    lazymatch type of HSf with st_ok _ _ ?ssx _ =>
      apply (fsw_retU B pv_tbl pv_tbl_ok W E ssx msf _ STK ot FP regs0 ly S U0 W0 mem0 md0 lyc (stack_free_state 0 pos S2) U k
        Q HSf ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) end.
    * pose proof (fsw_reg_extra _ regs (pv_extra0 regs0 FL ++ xs) _ msf 1%bv 1 HSf ltac:(vm_compute; reflexivity)) as R1F.
      rewrite R1F, app_nth1 by (cbn [length pv_extra0]; lia). cbn [nth pv_extra0]. exact Hra.
    * exact HJf.
    * exact HARUf.
    * intros r Hr. unfold acallee_saved in Hr.
      rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ msf (Z_to_bv 5 r) HSf).
      assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      repeat (destruct Hr' as [->|Hr']); try subst r;
        lazymatch goal with |- sv_denot _ (sr_get (ss_regs ?sx) ?rr) = _ =>
          let t := eval vm_compute in (sr_get (ss_regs sx) rr) in change (sr_get (ss_regs sx) rr) with t end;
        rewrite fsw_SOff0; subst E;
        first
        [ rewrite pe_extra by lia; cbn [Nat.sub nth pv_extra0]; reflexivity
        | rewrite (ew_Ereg_nat regs (pv_extra0 regs0 FL ++ xs) 8 8%bv eq_refl), R8;
          unfold spZ in Hsp; rewrite <- Hsp; apply Z_to_bv_bv_unsigned
        | rewrite (ew_Ereg_nat regs (pv_extra0 regs0 FL ++ xs) 3 3%bv eq_refl); exact R3
        | rewrite (ew_Ereg_nat regs (pv_extra0 regs0 FL ++ xs) 4 4%bv eq_refl); exact R4 ].
    * intros mat. apply HQ.
      -- pv_reg HSf (w_H W) (10%bv : bv 5) H10f. rewrite H10f, fsw_SOff0. subst E.
         rewrite (ew_Ereg_nat regs (pv_extra0 regs0 FL ++ xs) 10 10%bv eq_refl). exact Rrr.
      -- intros x Hx. exact (pv_frame_P _ _ _ _ (pe_wr F FL) HFrr ltac:(pe_wr_tac B26 B27 B46) x Hx).
Qed.
End EP2.
