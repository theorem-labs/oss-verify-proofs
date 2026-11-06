(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACem.v, with its module paths and module names changed; 1540 of its 1601 lines of code are new or changed and 390 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_pj_string.v, with its module paths and module names changed; 114 of its 182 lines of code are new or changed and 1533 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/FSW_ret.v from a working branch
   2767db174a0, same lemma names; imports point at lib/B's image files (YB1v, YB1w, YF0x, FSH_Base, FSH_Rt, FSPstat,
   FSH_Fn_reader and the other lib/B FSW files); the image-agnostic FSupoison, FSupoisonU, FSH_YC20, FSH_Gen stay lib/A's.
   rule 24: proves no function (kind: segment lemma). *)
(* The resume state after a program call in an INSTRUMENTED function, for walks that go on to read heap objects (or other
   memory outside the frame) after the call: fss_retT is FSW_K.fss_ret plus fss0T's shadow-base cells (the GOT word
   tfib_D_GOT_asan_shadow_memory_dynamic_address and the cell tfib_D_asan_shadow_memory_dynamic_address, as regions; the
   shadow base SHADOW_OFF as extra atom 32), plus a caller-chosen list of extra regions rs (e.g. a heap object the
   callee returned in a0, as a region based at atom 10, the a0 of the resumed env) with extra atom facts gf: the same
   premise shape as FSW_K.fsw_entryT_args (fss0T_args / fsT_regions_args, a working branch 7dee8c7178b).
   fsw_after_callU_args is FSW_K.fsw_after_callU resuming in it. The SHADOW of an extra object is NOT a region here:
   the walk's inline shadow checks go through FSW_K's token run (fsw_run_tok_AJU / fsw_aj_run_tokU with Bx := fs_Bx,
   Bspan := fs_Bspan, one shent per object atom), the donor's way (A/ACes.v:28-29, Reusable/YCbn.v:345-346).
   Owner: a Theorem Labs lane (reader lane), per the walk-kit layout of FSH_Fn_FORM.md; imports FSW_K, copies none of its lemmas.
   A kit: no function's contract is proved here (rule 24). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1w FSH_Base FSH_Rt FSW_K.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* the regions of the resume state: the frame (as fss_ret), the two shadow-base cells (as fss0T), then rs *)
Definition fsT_ret_regions (f : Z) (cs : list YP09.chunk) (rs : list YP09.region) : list YP09.region :=
  [fstk_ret f cs; fs_got_region; fs_bcell_region 32] ++ rs.
(* atom 2 is sp (as fss_ret), atom 32 the shadow base (as fss0T); gf gives further atom facts, as fss0T_args *)
Definition fss_retT (pc f : Z) (cs : list YP09.chunk) (rs : list YP09.region) (gf : list (nat * afact)) : sstate :=
  mkSS pc sr_atoms (fsT_ret_regions f cs rs) None
    (mkFacts ((2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) :: (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0) :: gf) [] []).

(* fsw_after_callU, resuming in fss_retT under the env Ereg regs' (fs_extraT ++ xs): atom 32 = SHADOW_OFF (fss0T's),
   atoms 33, ... = xs (field-value atoms of the extra regions, as FSW_K's fsw_entryT_argsX; xs = [] is fss0T's env). The walker
   gives, for its extra regions: regions_wf of the whole list, region_ok of rs on the machine's memory after the call,
   pairwise disjointness of the whole list (pairwise_disjoint_of_extents), and the facts gf: fsw_entryT_args's shape.
   The two cell equations of B are fsw_entryT's premises (the donor's TfibLib gives them). *)
Lemma fsw_after_callU_args : forall B STK sp0 ly S U W mem md lyc Sc Uc memC mdC k STKc f regsC ly' S' U' W' regs'
  mem' md' kc xs cs rs gf r,
  as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address ->
  as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address ->
  ajournal tfibsegs B STK sp0 [] ly S W (unpoison U mem) md [] lyc Sc W (unpoison Uc memC) mdC k ->
  ARU tfibsegs B lyc Sc Uc W memC mdC ->
  ajournal tfibsegs B STKc (spZ regsC) [] lyc Sc W (unpoison Uc memC) mdC [] ly' S' W' (unpoison U' mem') md' kc ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  aregs_preserved regsC regs' ->
  spZ regsC = sp0 - f -> 0 < f -> 0 <= STKc -> STKc + f <= STK -> f mod 16 = 0 ->
  regions_wf (fsT_ret_regions f cs rs) = true ->
  Forall (fun c => 0 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= f) cs ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs' (fs_extraT ++ xs)) (mrestrict (w_H W) memC) (sp0 - f)) cs ->
  Forall (region_ok tfibsegs (Ereg regs' (fs_extraT ++ xs)) (mrestrict (w_H W') mem')) rs ->
  pairwise_disjoint (Ereg regs' (fs_extraT ++ xs)) (fsT_ret_regions f cs rs) ->
  atoms_ok (Ereg regs' (fs_extraT ++ xs)) gf ->
  ajournal tfibsegs B STK sp0 [] ly S W (unpoison U mem) md [] ly' S' W' (unpoison U' mem') md' (k + kc) /\
  st_ok tfibsegs (Ereg regs' (fs_extraT ++ xs)) (fss_retT r f cs rs gf)
    (restrict (w_H W') (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))).
Proof.
intros B STK sp0 ly S U W mem md lyc Sc Uc memC mdC k STKc f regsC ly' S' U' W' regs' mem' md' kc xs cs rs gf r
  Hgot Hcell HJ HARUc HJc OK' PO' HP Hsp Hf HSc Hbud Hal Hwf Hin Hcs Hrs Hpd Hgf.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & _ & C3 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HJ2 : ajournal tfibsegs B STK sp0 [] ly S W (unpoison U mem) md [] ly' S' W' (unpoison U' mem') md' (k + kc)).
{ pose proof (ajournal_sub tfibsegs B LAWS fs_segs_low STK sp0 [] ly S W (unpoison U mem) md [] lyc Sc W
    (unpoison Uc memC) mdC k STKc (spZ regsC) [] [] ly' S' W' (unpoison U' mem') md' kc HJ HJc ltac:(lia) ltac:(lia)
    ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as H. exact H. }
split; [exact HJ2|].
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
assert (HARU' : ARU tfibsegs B ly' S' U' W' mem' md') by (split; [exact HAR2 | split; [exact OK' | exact PO']]).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
assert (Esp : getr regs' 2 = getr regsC 2) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (Usp : spZ regs' = sp0 - f) by (unfold spZ; rewrite Esp; exact Hsp).
assert (E2 : bv_unsigned (ew (Ereg regs' (fs_extraT ++ xs)) 2) = sp0 - f)
  by (rewrite (ew_Ereg_nat regs' (fs_extraT ++ xs) 2 2%bv eq_refl); exact Usp).
assert (E32 : ew (Ereg regs' (fs_extraT ++ xs)) 32 = Z_to_bv 64 SHADOW_OFF)
  by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (U32 : bv_unsigned (ew (Ereg regs' (fs_extraT ++ xs)) 32) = SHADOW_OFF) by (rewrite E32; apply wz; unfold SHADOW_OFF; lia).
(* the two image cells of AR after the call, carried to the machine's own memory mem' (below the shadow: U' cannot
   touch them), as fsw_entryT does at entry *)
destruct (fsw_got_shadow B ly' S' W' (unpoison U' mem') md' Hgot Hcell HAR2) as [Kgot Kcell].
assert (MB : forall x, 0 <= x < SHADOW_OFF ->
  mbyte tfibsegs (mrestrict (w_H W') mem') x = mbyte tfibsegs (mrestrict (w_H W') (unpoison U' mem')) x).
{ intros x Hx. unfold mbyte, mrestrict.
  rewrite (ARU_mem_low tfibsegs B ly' S' U' W' mem' md' (Z_to_bv 64 x) HARU'
    ltac:(rewrite (wz x ltac:(unfold SHADOW_OFF in *; lia)); unfold SHADOW_OFF in *; lia)).
  reflexivity. }
assert (VM : forall a v, 0 <= a -> a + 8 <= SHADOW_OFF ->
  val_mem tfibsegs (mrestrict (w_H W') (unpoison U' mem')) a 8 v -> val_mem tfibsegs (mrestrict (w_H W') mem') a 8 v).
{ intros a v Ha Hb Hv k0 Hk0. rewrite (MB (a + Z.of_nat k0) ltac:(lia)). exact (Hv k0 Hk0). }
assert (Vgot : val_mem tfibsegs (mrestrict (w_H W') mem') tfib_D_GOT_asan_shadow_memory_dynamic_address 8
  tfib_D_asan_shadow_memory_dynamic_address).
{ apply VM; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia
  | unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, SHADOW_OFF; lia
  | exact (val_mem_of_rdword tfibsegs (w_H W') (unpoison U' mem') _ _ Kgot)]. }
assert (Vcell : val_mem tfibsegs (mrestrict (w_H W') mem') tfib_D_asan_shadow_memory_dynamic_address 8 SHADOW_OFF).
{ apply VM; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia
  | unfold tfib_D_asan_shadow_memory_dynamic_address, SHADOW_OFF; lia
  | exact (val_mem_of_rdword tfibsegs (w_H W') (unpoison U' mem') _ _ Kcell)]. }
rewrite restrict_mkst_fx. unfold fss_retT, fsT_ret_regions in *. cbn [app] in *. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- exact Hwf.
- constructor; [|constructor; [|constructor; [|exact Hrs]]].
  + (* the frame, as fsw_after_callU *)
    unfold region_ok, fstk_ret. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E2. split; [lia|]. split; [lia|]. split.
    * intros o Ho. apply (apresent_writable tfibsegs).
      apply (fsw_apresent_unpoison B ly' S' U' W' mem' md' _ HARU'); [lia|]. apply Hpres2. lia.
    * apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) Hin c Hc) as Hci.
      pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hck.
      apply (chunk_ok_mbyte _ (mrestrict (w_H W) memC)); [|exact Hck].
      destruct Hci as [Hc0 Hc1]. intros i Hi. apply (mbyte_of_aview tfibsegs).
      rewrite <- (fsw_aview_unpoison_high B ly' S' U' W' mem' md' _ HARU') by lia.
      rewrite <- (fsw_aview_unpoison_high B lyc Sc Uc W memC mdC _ HARUc) by lia.
      apply F1; [lia | intros Hx; lia].
  + (* the GOT word of the shadow base, as fsw_entryT *)
    unfold fs_got_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia|].
    split; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val tfibsegs _ _ 0 tfib_D_GOT_asan_shadow_memory_dynamic_address 8
      (SLit tfib_D_asan_shadow_memory_dynamic_address) tfib_D_asan_shadow_memory_dynamic_address);
      [reflexivity | unfold tfib_D_asan_shadow_memory_dynamic_address; cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
      | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_l; exact Vgot].
  + (* the shadow-base cell, as fsw_entryT *)
    unfold fs_bcell_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia|].
    split; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val tfibsegs _ _ 0 tfib_D_asan_shadow_memory_dynamic_address 8 (SOff 32 0) SHADOW_OFF);
      [rewrite fsw_SOff0, E32; reflexivity | unfold SHADOW_OFF; cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
      | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_l; exact Vcell].
- exact Hpd.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok at 1 2. cbn [af_lo af_hi af_al2].
  rewrite E2, U32. split; [|split; [|exact Hgf]].
  + change (2 ^ 4) with 16. split; [lia|]. split; [|lia].
    rewrite Zminus_mod, Hal16. assert (f mod 16 = 0) as -> by exact Hal. reflexivity.
  + rewrite Z.pow_0_r. split; [lia | split; [apply Z.mod_1_r | lia]].
Qed.

(* ---- the RETURN of a function stated in fpostU (FSH_Gen.v: the reader specs' form, a working branch
   d3689f592c6): at the final `ret` (RET_WORD_r at ss_pc), the walk's journal over the unpoisoned memories, its ARU at the
   final memory and the callee-saved registers give fpostU, leaving Q. The U form of FSW_K's fsw_ret (fpost, U = []):
   fpostU's two extra conjuncts upoison_ok / upoisoned are ARU's last two, at the U' the spec names. ---- *)
Lemma fsw_retU : forall B tbl (tbl_ok : table_ok tfibsegs tbl) W2 E ssf msf mdf STK sp0 FP regs0 ly S U W mem md lyf
  Sf U' k Q,
  st_ok tfibsegs E ssf (restrict (w_H W2) msf) -> ss_resv ssf = None ->
  clookup tbl (ss_pc ssf) = Some RET_WORD_r ->
  v_jalr (getr (ms_regs msf) 1) 0 = getr regs0 1 ->
  ajournal tfibsegs B STK sp0 FP ly S W (unpoison U mem) md [] lyf Sf W2 (unpoison U' (ms_mem msf)) mdf k ->
  ARU tfibsegs B lyf Sf U' W2 (ms_mem msf) mdf ->
  aregs_preserved regs0 (ms_regs msf) ->
  (forall mat, Q lyf Sf W2 (ms_regs msf) (ms_mem msf) (with_vm_backing (m_vm_lazy mdf) mat mdf)) ->
  SRr tfibsegs W2 (mkCfg msf mdf) (fpostU tfibsegs B STK sp0 FP regs0 ly S U W mem md k U' Q).
Proof.
intros B tbl tbl_ok W2 E ssf msf mdf STK sp0 FP regs0 ly S U W mem md lyf Sf U' k Q HSf Hrv Hpc Hjalr HJf HARUf HP HQ.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
eapply (SRr_ret_at tfibsegs _ tbl_ok fs_wx);
  first [ solve [exact HSf] | solve [exact Hrv] | solve [exact Hpc] | lazymatch goal with |- forall _, _ => idtac end ].
intros mat. rewrite Hjalr. unfold fpostU.
exists lyf, Sf, (ms_regs msf), (ms_mem msf), (with_vm_backing (m_vm_lazy mdf) mat mdf).
split; [reflexivity|].
split; [apply (ajournal_materialize tfibsegs _ LAWS fs_segs_low); exact HJf|].
destruct HARUf as (_ & OK & PO).
split; [exact OK|]. split; [exact PO|]. split; [exact HP|]. exact (HQ mat).
Qed.

(* ---- the callee's fpreU at a program call (the U form of the donor's afn_pre_at use in a Theorem Labs lane's call walks, e.g.
   FMW_check_reject_clean.v:68-77): afn_pre from the caller's journal over the unpoisoned memories (YCbq.v afn_pre_at),
   upoison_ok / upoisoned from ARU at the call, arodata at the call (FSW_K.arodata_below gives it from the entry's).
   Any caller footprint FP and own list, and any journal START memory mem0 (the callee's fpreU depends on none of
   them: a Theorem Labs lane, writer callers have FP = FS_PSTAT_FP, and after a fuzz_malloc in the same caller the journal runs
   from unpoison U0 mem0 to unpoison U3 memc with U3 <> U0); fsw_fpreU_at is the FP = [] / own = [] / same-U instance. ---- *)
Lemma fsw_fpreU_atFP : forall B STK sp0 FP ly S U W0 mem0 md own lyc Sc W memc mdc k regsc STK1 (o : Z) ch1,
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md own lyc Sc W (unpoison U memc) mdc k ->
  ARU tfibsegs B lyc Sc U W memc mdc ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) memc) ->
  spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  YK0s.ret_ok (getr regsc 1) -> 4096 <= raZ regsc ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  achain lyc (aview tfibsegs (w_H W) (unpoison U memc)) (spZ regsc) (s0Z regsc) ch1 ->
  fpreU tfibsegs B STK1 lyc Sc U W regsc memc mdc ch1.
Proof.
intros B STK sp0 FP ly S U W0 mem0 md own lyc Sc W memc mdc k regsc STK1 o ch1 HJ HARU Hro Hsp Hal Hneg Hstk1 Hbud Hra
  Hra4 Hgp Htp Hch.
destruct HARU as (_ & OK & PO).
split; [|exact Hro]. split; [|split; [exact OK | exact PO]].
exact (afn_pre_at tfibsegs B STK sp0 FP ly S W0 mem0 md own lyc Sc W (unpoison U memc) mdc k regsc STK1 o ch1
  HJ Hsp Hal Hneg Hstk1 Hbud Hra Hra4 Hgp Htp Hch).
Qed.
Lemma fsw_fpreU_at : forall B STK sp0 ly S U W0 mem md lyc Sc W memc mdc k regsc STK1 (o : Z) ch1,
  ajournal tfibsegs B STK sp0 [] ly S W0 (unpoison U mem) md [] lyc Sc W (unpoison U memc) mdc k ->
  ARU tfibsegs B lyc Sc U W memc mdc ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) memc) ->
  spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  YK0s.ret_ok (getr regsc 1) -> 4096 <= raZ regsc ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  achain lyc (aview tfibsegs (w_H W) (unpoison U memc)) (spZ regsc) (s0Z regsc) ch1 ->
  fpreU tfibsegs B STK1 lyc Sc U W regsc memc mdc ch1.
Proof. intros B STK sp0 ly S U W0 mem md lyc Sc W memc mdc k. exact (fsw_fpreU_atFP B STK sp0 [] ly S U W0 (unpoison U mem) md [] lyc Sc W memc mdc k). Qed.
End e.
