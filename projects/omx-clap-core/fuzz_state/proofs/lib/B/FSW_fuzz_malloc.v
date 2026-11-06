(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACf1.v, with its module paths and module names changed; 639 of its 687 lines of code are new or changed and 451 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_fuzz_free.v, with its module paths changed; 469 of its 535 lines of code are new or changed and 621 lines of the source are left out. *)
(* fs ASan, group ALLOC, image B (fs.asan-ubsan): the walk of fuzz_malloc (A_fuzz_malloc = 0x82a58, alloc.c:61-66),
   proving fuzz_malloc_spec of lib/B/FSH_Fn_alloc.v (statement a working branch 338b0dd7601, no CTX).

   proves function fuzz_malloc (B 0x82a58) (reuse search: proof-index on main@c4c03c57ba1 / ossv/recipes@e5e7eba2cc0 /
   ossv/candidates@ee89628c997 / release/pau-projects-recipes@b6a0088adcb + lemma index over 11131 working branches + live
   working heads; a Theorem Labs lane, brief-B-walks.md). Result: the released fuzz_malloc proofs are plain / ubsan / cut-free
   only (lib/Prog, lib/U/Prog), no ASan B proof; written new, porting ALLOC's A proof (lib/A/FSW_fuzz_malloc.v,
   a working branch) to B's shape.

   Measured control flow (capstone on the unstripped twin of the pinned fs.asan-ubsan): 0x82a58..0x82a64 frame 16
   (FRAME_fuzz_malloc), save ra / s0, s0 = n; g_count := cnt + 1 (0x82a7c); `bne cnt, fail` 0x82a80.
   - NULL arm (failing(): cnt = fail): g_fail_at := -1 (0x82a88), a0 = 0, restore, ret 0x82ac8.
   - malloc arm: `bltu -17, n` 0x82a94 (not taken, n < MALLOC_MAX); `jal __wrap_malloc` 0x82a9c (ra 0x82aa0) with
     a0 = n + 16; `beqz a0` 0x82aa0 (not taken: the call is non-NULL); a1 = n; restore ra / s0; `j own` 0x82ab4 (a TAIL
     call: B's own() is out of line, lib/B/FSW_own.v own_holds, with a0 = b, a1 = n, ra / sp / s0 the caller's).
   B's fuzz_malloc has no inline shadow check and no poison call of its own (own() does both).

   Shape: lib/A/FSW_fuzz_malloc.v's prefix (entry FSW_statics.fsw_entryTS, runs by FSW_K.fsw_aj_runU with awr_ok from
   FSW_statics_awr, the malloc call by FSW_malloc_free.fsw_aj_malloc04U_sub, the resume by FSW_K3.fsw_after_callFPU_args),
   then the tail call: own's fpreU at the tail state from the caller's journal (FSW_ret.fsw_fpreU_atFP, o = 0), own_holds,
   and the composition of own's fpostU into fuzz_malloc's (fmB_tail_post, here: the callee journal is absorbed by
   ajournal_sub, own's footprint FS_PSTAT_FP ++ [(b, b + 8)] being the caller's statics and the head of the block the
   caller's own malloc made). Kit rules R1 / R2 followed. Relocated files: none. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG08 YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q YG05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen FSpoisonS.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w YF0m FSH_Base FSH_Rt FSPstat FSH_Fn_alloc FSW_K FSW_K3 FSW_ret FSW_rres FSW_rd FSW_statics FSW_statics_awr
FSW_head FSW_malloc_free FSpoisonS FSW_poison_conv FSW_own.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* the return address of fuzz_malloc's `jal __wrap_malloc` (0x82a9c; MEASURED) *)
Definition A_fuzz_malloc_raB : Z := 0x82aa0.

(* the state resumed after the malloc call (0x82aa0): env Ereg regs2 (fs_extraT ++ fmB_xs), atoms 33..36 the statics,
   37 / 38 the frame's saved ra / s0 (fuzz_malloc's frame: s0 at sp + 0, ra at sp + 8) *)
Definition fmB_cs : list YP09.chunk := [YP09.mkChunk 0 (CVal 8 (SOff 38 0)); YP09.mkChunk 8 (CVal 8 (SOff 37 0))].
Definition fmB_xs (regs : bvmap 5 word) (cnt fail live peak : Z) : list word :=
  fs_pstat_xs (cnt + 1) fail live peak ++ [getr regs 1; getr regs 8].
(* the callee-saved registers at the tail call: sp back up by the frame, s0 reloaded from atom 38, the rest untouched *)
Definition fmB_expect (r : bv 5) : sv :=
  match bv_unsigned r with
  | 2 => SOff 2 16 | 8 => SOff 38 0
  | z => SOff (Z.to_nat z) 0
  end.

(* FS_PSTAT_FP: the sink stays closed and no static is read-only (arodata_kept's two side conditions for fuzz_malloc's
   own footprint) *)
Lemma fmB_pstat_sink : ~ YI16.sink_open_fp FS_PSTAT_FP.
Proof.
intros (r & Hr & H0). unfold FS_PSTAT_FP, G_COUNT, G_FAIL, G_LIVE, G_PEAK in Hr.
repeat (destruct Hr as [<- | Hr]; [cbn [fst snd] in H0; lia|]). destruct Hr.
Qed.
Lemma fmB_pstat_not_ro : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> ~ inFP FS_PSTAT_FP a.
Proof.
intros a Hro Ha. pose proof (ow_pstat_bounds a Ha) as Hb.
destruct Hro as [(s & Hs & Hw & Hsa) | Hr]; [| unfold FS_RLO, FS_RHI, G_FAIL, G_LIVE, G_PEAK, G_COUNT in *; lia].
assert (C : forallb (fun s => seg_writable s || forallb (fun r : Z * Z => (snd r <=? Z.of_N (seg_base s)) ||
    (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? fst r)) FS_PSTAT_FP) tfibsegs = true) by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) C s Hs) as Cs. cbv beta in Cs. rewrite Hw in Cs. cbn [orb] in Cs.
destruct Ha as (r & Hr & Hra).
pose proof (proj1 (forallb_forall _ _) Cs r Hr) as Cr. cbv beta in Cr.
apply orb_true_iff in Cr as [Cr | Cr]; apply Z.leb_le in Cr; cbn [fst snd] in *; lia.
Qed.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* a block whose start is no head of U is addressable over its whole length, the head bytes included (the fresh block
   own() receives); fsw_block_body_addressable's proof with the head case closed by the premise *)
Lemma fmB_block_addressable : forall B ly S U (W : world tfibsegs) mem md P n,
  ARU tfibsegs B ly S U W mem md -> FSupoisonU.fs_heads B ly S U ->
  In (P, n) (ablocks B ly S) -> ~ In (P, 16) U ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF P (req_size n).
Proof.
intros B ly S U W mem md P n HARU FH Hin Hnin.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
pose proof (YCbq.range_addressable_of_block tfibsegs B LAWS ly S W (unpoison U mem) md P n P (req_size n) HAR Hin
  ltac:(lia) ltac:(lia)) as HRA.
pose proof asan_consts as (C1 & _).
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md P n HAR Hin) as (HP16 & HP4096 & HPc & _ & _ & PW & _).
intros x Hx. destruct (HRA x Hx) as (s & Es & Hok). exists s. split; [|exact Hok].
assert (NI : in_ush U (bv_unsigned (Z_to_bv 64 (shadow_of_addr SHADOW_OFF x))) = false).
{ rewrite wz by (unfold shadow_of_addr, SHADOW_OFF; Z.div_mod_to_equations; lia).
  apply fsw_head_ush_out; [lia|]. intros (h & q) Hr. cbn [fst snd].
  destruct (FH (h, q) Hr) as (E16 & m & Hm & M16). cbn [fst snd] in E16, Hm. subst q.
  destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md h m HAR Hm) as (Hh16 & _).
  split; [reflexivity|].
  split; [apply Z.mod_divide in Hh16 as [k Hk]; [|lia]; rewrite Hk; replace (k * 16) with ((k * 2) * 8) by lia; apply Z_mod_mult|].
  destruct (Z.eq_dec h P) as [->|NE]; [exfalso; exact (Hnin Hr)|].
  assert (I1 : In (h, req_size m) (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)))
    by (apply (in_map (fun b => (fst b, req_size (snd b))) _ (h, m)); exact Hm).
  assert (I2 : In (P, req_size n) (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)))
    by (apply (in_map (fun b => (fst b, req_size (snd b))) _ (P, n)); exact Hin).
  destruct (FSupoisonU.pairwise_In2 zdisjoint _ _ _ PW I1 I2 ltac:(intros E; injection E; intros _ E'; exact (NE E')))
    as [D|D]; unfold zdisjoint in D; cbn [fst snd] in D; lia. }
rewrite <- (aview_unpoison_out tfibsegs (w_H W) U mem _ NI). exact Es.
Qed.
End k.

Section n. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* fs's image facts (FSH_Rt.fs_img_facts); owner RELOC, proved once for fs's TfibB; used for awr_byte's static arm *)
Hypothesis IMG : fs_img_facts tfibsegs B.
(* the two shadow-base cells of fs.asan-ubsan (GOT word 0x9fc10 -> cell 0xa8438): FSH_Base.FsShadowSyms (owner the S0
   start-up layer / B's TfibLib) *)
Hypothesis SHS : FsShadowSyms B.
Let FS_GOT_SHADOW : as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address := proj1 SHS.
Let FS_SHADOW_CELL : as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address := proj2 SHS.

(* the NULL arm of fuzz_malloc_spec (failing(): cnt = fail): g_count := cnt + 1, g_fail_at := SIZE_MAX, a0 = 0 *)
Lemma fmB_null_arm : forall ly S U (W : world tfibsegs) regs mem md ch live peak cnt fail,
  fpreU tfibsegs B STK_fuzz_malloc ly S U W regs mem md ch -> fs_heads B ly S U ->
  fs_glob tfibsegs W mem live peak cnt fail -> cnt + 1 < 2 ^ 64 -> cnt = fail ->
  SRr tfibsegs W (cfg_at tfibsegs A_fuzz_malloc regs mem md)
    (apost_baseU tfibsegs B STK_fuzz_malloc FS_PSTAT_FP regs ly S W mem md 0 U U
       (fun ly' S' W' regs' mem' md' =>
          getr regs' 10 = w64 0 /\ ablocks B ly' S' = ablocks B ly S /\
          fs_heads B ly' S' U /\
          fs_glob tfibsegs W' mem' live peak (cnt + 1) SIZE_MAXZ)).
Proof.
intros ly S U W regs mem md ch live peak cnt fail HPRE FH HGL Hcn Hcf.
pose proof HPRE as (HAP & HRO).
pose proof (fsw_ARU B STK_fuzz_malloc ly S U W regs mem md ch HAP) as HARU.
pose proof HAP as (HAN & _ & _).
pose proof HAN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof HGL as (_ & _ & _ & _ & Hlp & Hp64 & Hc64 & Hf64).
assert (FM : 16 <= STK_fuzz_malloc) by (apply Z.leb_le; vm_compute; reflexivity).
pose proof (fsw_entryTS B STK_fuzz_malloc 16 ly S U W regs mem md ch A_fuzz_malloc live peak cnt fail
  FS_GOT_SHADOW FS_SHADOW_CELL HAP ltac:(lia) ltac:(vm_compute; reflexivity) HGL) as HS.
pose proof (ajournal_init tfibsegs B STK_fuzz_malloc FS_PSTAT_FP ly S W regs (unpoison U mem) md ch HAN) as HJ.
set (E := Ereg regs (fs_extraTS cnt fail live peak)) in HS.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (EX : forall j v, (j < 5)%nat -> nth j (fs_extraTS cnt fail live peak) (Z_to_bv 64 0) = Z_to_bv 64 v ->
  ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj Hv; subst E; rewrite ew_Ereg_extra; exact Hv).
assert (A0 : forall pc f FPx bl0 blc lyx own fr0, (forall a, inFP FS_PSTAT_FP a -> inFP FPx a) -> 0 <= f <= STK_fuzz_malloc ->
  awr_ok tfibsegs B E (ss_mem (fss0TS pc f)) STK_fuzz_malloc (spZ regs) FPx bl0 blc lyx own fr0)
  by (intros pc f FPx bl0 blc lyx own fr0 HFP Hf; exact (fsw_awr_TS B IMG E pc f STK_fuzz_malloc (spZ regs) FPx bl0 blc lyx own fr0 Usp ltac:(lia) HFP)).
unfold cfg_at. change (w64 A_fuzz_malloc) with (Z_to_bv 64 A_fuzz_malloc).
(* 0x82a58..0x82a7c: frame, saves, s0 = n, g_count := cnt + 1; stops at `bne a2, a3` *)
fsw_aj_runU tbl_fm_ok HS HJ HARU.
{ exact (A0 A_fuzz_malloc 16 FS_PSTAT_FP _ _ _ _ _ (fun a H => H) ltac:(lia)). }
clear HF HFr HG.
eapply SRr_sym_branch with (c := BC_NE) (a := SOff 33 0) (b := SOff 34 0) (1 := HS).
- (* taken: cnt <> fail, refuted *)
  intros Hb _. exfalso.
  rewrite branch_ne_U, (U_atom E 33 cnt (EX 1%nat cnt ltac:(lia) eq_refl) Hc64),
    (U_atom E 34 fail (EX 2%nat fail ltac:(lia) eq_refl) Hf64), Hcf, Z.eqb_refl in Hb.
  discriminate Hb.
- (* not taken: cnt = fail; 0x82a84..0x82ac4: g_fail_at := -1, a0 = 0, restore; stops at ret 0x82ac8 *)
  intros _ HS2. clear HS.
  fsw_aj_runU tbl_fm_ok HS2 HJ HARU.
  { eapply ow_awr_skel; [| exact (A0 A_fuzz_malloc 16 FS_PSTAT_FP _ _ _ _ _ (fun a H => H) ltac:(lia))].
    lazymatch goal with |- skeleton _ = skeleton _ => vm_compute; reflexivity end. }
  pose proof HS2 as HS2c.
  destruct HS2c as (_ & _ & _ & _ & _ & _ & _ & HMEM & _).
  rreg HS2 (1%bv : bv 5) R1.
  rreg HS2 (10%bv : bv 5) R10.
  rewrite ?wvb_collapse in HJ, HARU.
  unfold apost_baseU.
  eapply (fsw_retU B tbl_fm tbl_fm_ok).
  all: first
    [ solve [exact HS2] | solve [exact HJ] | solve [exact HARU]
    | solve [lazymatch goal with |- ss_resv _ = None => reflexivity end]
    | solve [lazymatch goal with |- clookup _ _ = Some _ => vm_compute; reflexivity end]
    | solve [rewrite R1, ?fsw_SOff0, E1; exact Hra]
    | solve [eapply (aregs_preserved_of_st_ok tfibsegs _ E _ _ regs (fs_extraTS cnt fail live peak) HS2);
             first [ solve [apply env_agree_refl]
                   | solve [lazymatch goal with |- forallb _ _ = true => vm_compute; reflexivity end] ]]
    | idtac ].
  intros mat1. cbv beta.
  split; [rewrite R10; reflexivity|]. split; [reflexivity|]. split; [exact FH|].
  assert (E33 : ew E 33 = Z_to_bv 64 cnt) by exact (EX 1%nat cnt ltac:(lia) eq_refl).
  apply (fs_glob_of_TS E W _ _ live peak (cnt + 1) SIZE_MAXZ (SOff 35 0) (SOff 36 0) (SOff 33 1) (SLit SIZE_MAXZ) HMEM).
  all: first
    [ solve [lazymatch goal with |- fs_pstat_find _ _ = Some _ => vm_compute; reflexivity end]
    | solve [rewrite fsw_SOff0; exact (EX 3%nat live ltac:(lia) eq_refl)]
    | solve [rewrite fsw_SOff0; exact (EX 4%nat peak ltac:(lia) eq_refl)]
    | solve [lazymatch goal with |- sv_denot _ (SOff 33 1) = _ =>
               apply bv_eq; rewrite denot_SOff, E33; rewrite !unsigned_lit_small by lia;
               apply zcanon_id; unfold M64; lia end]
    | solve [lazymatch goal with |- sv_denot _ (SLit _) = _ => reflexivity end]
    | solve [unfold SIZE_MAXZ; lia]
    | solve [lia] ].
Qed.

End n.

Section m. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* as Section n *)
Hypothesis IMG : fs_img_facts tfibsegs B.
Hypothesis SHS : FsShadowSyms B.
Let FS_GOT_SHADOW : as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address := proj1 SHS.
Let FS_SHADOW_CELL : as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address := proj2 SHS.
(* fs's B is TfibB (lib/B/YF0m.v TfibSyms): its code pcs (Tfib_code), errno, the universe's laws; owner the S0 start-up
   layer *)
Hypothesis HB : TfibSyms B.
(* the donor allocator walks' errno / UNIV0 environment (Reusable/YCbq.v api_env); owner RELOC *)
Hypothesis FS_ENV : api_env tfibsegs B.
(* __wrap_malloc in ARU form (FSupoisonU.amalloc_realizesU); owner the shared runtime (a Theorem Labs lane's U twin of the cgif core
   AF0w, SHARED-WALKS row 'Allocate / Deallocate') *)
Hypothesis FS_AMALLOC_AU : FSupoisonU.amalloc_realizesU tfibsegs B.
(* __asan_poison_memory_region at B's PC_poison (lib/B/FSpoisonS.fs_poison16), own()'s call (FSW_own.own_holds's
   premise); owner the shared runtime (SHARED-WALKS row 'poison / unpoison'; B's proof not yet written) *)
Hypothesis FS_POISON : fs_poison16 tfibsegs B.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Let ML : model_laws (as_universe B) := model_laws_ok (as_universe B) (ts_universe B HB).
Let segs_low : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd := fs_segs_low.

(* below the shadow (the image, the heap) the unpoisoned reading is the machine's *)
Lemma fmB_aview_low : forall ly S U (W : world tfibsegs) mem md a, ARU tfibsegs B ly S U W mem md -> 0 <= a < SHADOW_OFF ->
  aview tfibsegs (w_H W) (unpoison U mem) a = aview tfibsegs (w_H W) mem a.
Proof.
intros ly S U W mem md a H Ha. apply (aview_at tfibsegs).
apply (fs_head_app_view B ly S U W mem md a H); [unfold SHADOW_OFF in *; lia | left; lia].
Qed.
(* the statics are kept across an allocator call (acall_kept's image clause, read without unpoison) *)
Lemma fmB_glob_acall : forall lyc Sc U (W W2 : world tfibsegs) memc mem2 mdc ly2 S2 md2 slo shi Ex live peak cnt fail,
  ARU tfibsegs B lyc Sc U W memc mdc -> ARU tfibsegs B ly2 S2 U W2 mem2 md2 ->
  acall_kept tfibsegs B lyc Sc W (unpoison U memc) W2 (unpoison U mem2) slo shi Ex ->
  fs_glob tfibsegs W memc live peak cnt fail -> fs_glob tfibsegs W2 mem2 live peak cnt fail.
Proof.
intros lyc Sc U W W2 memc mem2 mdc ly2 S2 md2 slo shi Ex live peak cnt fail H1 H2 (_ & _ & HKimg & _) G.
apply (ow_glob_keep W W2 memc mem2 _ _ _ _ G). intros a Ha.
pose proof (ow_pstat_bounds a Ha) as Hb.
assert (Hlo : 0 <= a < SHADOW_OFF) by (unfold G_FAIL, G_LIVE, G_PEAK, G_COUNT, SHADOW_OFF in *; lia).
apply (mbyte_of_aview tfibsegs).
rewrite <- (fmB_aview_low ly2 S2 U W2 mem2 md2 a H2 Hlo), <- (fmB_aview_low lyc Sc U W memc mdc a H1 Hlo).
apply HKimg; [exact (fs_pstat_img a Ha) | exact (fs_pstat_not_owned tfibsegs B _ _ _ _ _ _ _ IMG a Ha) |].
rewrite (ts_errno B HB). unfold TFIB_ERRNO, G_FAIL, G_LIVE, G_PEAK, G_COUNT in *. lia.
Qed.

(* ---- a TAIL call's post: the callee's fpostU at the tail state (sp back to the caller's entry sp, ra the caller's) is
   the caller's fpostU, its journal composed by ajournal_sub (the callee's window inside the caller's, the callee's
   footprint the caller's or a block the caller made), the callee-saved registers by transitivity ---- *)
Lemma fmB_tail_post : forall STK sp0 FP regs ly S U (W : world tfibsegs) mem md k lyc Sc Uc Wc memc mdc regsc STK1 FP1 k1 k2
  U' (Q1 Q : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  ajournal tfibsegs B STK sp0 FP ly S W (unpoison U mem) md [] lyc Sc Wc (unpoison Uc memc) mdc k ->
  spZ regsc = sp0 -> STK1 <= STK -> getr regsc 1 = getr regs 1 -> aregs_preserved regs regsc -> k + k1 = k2 ->
  (forall a, inFP FP1 a -> (inFP FP a /\ in_img tfibsegs a) \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
  (forall ly' S' W' regs' mem' md', Q1 ly' S' W' regs' mem' md' -> Q ly' S' W' regs' mem' md') ->
  forall W' c', fpostU tfibsegs B STK1 (spZ regsc) FP1 regsc lyc Sc Uc Wc memc mdc k1 U' Q1 W' c' ->
  fpostU tfibsegs B STK sp0 FP regs ly S U W mem md k2 U' Q W' c'.
Proof.
intros STK sp0 FP regs ly S U W mem md k lyc Sc Uc Wc memc mdc regsc STK1 FP1 k1 k2 U' Q1 Q HJ Hsp HSTK Hra HP Hk HF HQ
  W' c' (ly' & S' & regs' & mem' & md' & -> & HJ1 & OK & PO & HP' & HQ1).
exists ly', S', regs', mem', md'.
split; [rewrite Hra; reflexivity|].
split.
{ subst k2. rewrite Hsp in HJ1.
  eapply (ajournal_sub tfibsegs B LAWS segs_low STK sp0 FP ly S W (unpoison U mem) md [] lyc Sc Wc (unpoison Uc memc) mdc k
    STK1 sp0 FP1 []).
  all: first
    [ solve [exact HJ] | solve [exact HJ1] | solve [lia]
    | solve [intros a Ha; destruct (HF a Ha) as [H | H];
             first [ solve [right; left; exact H] | solve [right; right; exact H] | solve [left; exact H]
                   | solve [left; right; exact H] | solve [right; exact H] ]] ]. }
split; [exact OK|]. split; [exact PO|].
split; [exact (aregs_preserved_trans _ _ _ HP HP')|].
exact (HQ _ _ _ _ _ _ HQ1).
Qed.

Lemma fmB_malloc_arm : forall ly S U (W : world tfibsegs) regs mem md ch n live peak cnt fail,
  fpreU tfibsegs B STK_fuzz_malloc ly S U W regs mem md ch -> fs_heads B ly S U ->
  getr regs 10 = w64 n -> 1 <= n -> n + HEAD < MALLOC_MAX ->
  fs_glob tfibsegs W mem live peak cnt fail -> live + n < 2 ^ 64 -> cnt + 1 < 2 ^ 64 ->
  st_nev S + 1 <= EV_MAX -> blocks_bytes S + (n + HEAD) <= LIVE_MAX -> cnt <> fail ->
  SRr tfibsegs W (cfg_at tfibsegs A_fuzz_malloc regs mem md)
    (fun W' c' => exists res,
       apost_baseU tfibsegs B STK_fuzz_malloc FS_PSTAT_FP regs ly S W mem md 1 U (U ++ [(res - HEAD, HEAD)])
       (fun ly' S' W' regs' mem' md' =>
          getr regs' 10 = w64 res /\ 4096 + HEAD <= res /\
          ablocks B ly' S' = ablocks B ly S ++ [(res - HEAD, n + HEAD)] /\
          fs_heads B ly' S' (U ++ [(res - HEAD, HEAD)]) /\
          (0 < n -> fs_rblock tfibsegs B ly' S' W' mem' res n) /\
          range_addressable (aview tfibsegs (w_H W') mem') SHADOW_OFF res n /\
          fs_glob tfibsegs W' mem' (live + n) (Z.max peak (live + n)) (cnt + 1) fail) W' c').
Proof.
intros ly S U W regs mem md ch n live peak cnt fail HPRE FH H10 Hn1 Hn2 HGL Hlv Hcn Hev Hbb Hcf.
pose proof HPRE as (HAP & HRO).
pose proof (fsw_ARU B STK_fuzz_malloc ly S U W regs mem md ch HAP) as HARU.
pose proof HARU as HARU0.
pose proof HAP as (HAN & _ & _).
pose proof HAN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof HGL as (_ & _ & _ & _ & Hlp & Hp64 & Hc64 & Hf64).
pose proof (fsw_sp B STK_fuzz_malloc ly S U W regs mem md ch HAP) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _ & C3 & _).
assert (FM : ASTACK + 16 <= STK_fuzz_malloc) by (apply Z.leb_le; vm_compute; reflexivity).
assert (FMo : STK_own <= STK_fuzz_malloc) by (apply Z.leb_le; vm_compute; reflexivity).
assert (Hn64 : 0 <= n < 2 ^ 64) by (unfold MALLOC_MAX, HEAD in *; lia).
pose proof (fsw_entryTS B STK_fuzz_malloc 16 ly S U W regs mem md ch A_fuzz_malloc live peak cnt fail
  FS_GOT_SHADOW FS_SHADOW_CELL HAP ltac:(unfold ASTACK in FM; lia) ltac:(vm_compute; reflexivity) HGL) as HS.
pose proof (ajournal_init tfibsegs B STK_fuzz_malloc FS_PSTAT_FP ly S W regs (unpoison U mem) md ch HAN) as HJ.
set (E := Ereg regs (fs_extraTS cnt fail live peak)) in HS.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 n) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (EX : forall j v, (j < 5)%nat -> nth j (fs_extraTS cnt fail live peak) (Z_to_bv 64 0) = Z_to_bv 64 v ->
  ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj Hv; subst E; rewrite ew_Ereg_extra; exact Hv).
assert (A0 : forall pc f FPx bl0 blc lyx own fr0, (forall a, inFP FS_PSTAT_FP a -> inFP FPx a) -> 0 <= f <= STK_fuzz_malloc ->
  awr_ok tfibsegs B E (ss_mem (fss0TS pc f)) STK_fuzz_malloc (spZ regs) FPx bl0 blc lyx own fr0)
  by (intros pc f FPx bl0 blc lyx own fr0 HFP Hf; exact (fsw_awr_TS B IMG E pc f STK_fuzz_malloc (spZ regs) FPx bl0 blc lyx own fr0 Usp ltac:(lia) HFP)).
unfold cfg_at. change (w64 A_fuzz_malloc) with (Z_to_bv 64 A_fuzz_malloc).
(* 0x82a58..0x82a7c as in fmB_null_arm; stops at `bne a2, a3` *)
fsw_aj_runU tbl_fm_ok HS HJ HARU.
{ exact (A0 A_fuzz_malloc 16 FS_PSTAT_FP _ _ _ _ _ (fun a H => H) ltac:(unfold ASTACK in FM; lia)). }
clear HF HFr HG.
eapply SRr_sym_branch with (c := BC_NE) (a := SOff 33 0) (b := SOff 34 0) (1 := HS).
2: { (* not taken: cnt = fail, refuted *)
  intros Hb _. exfalso.
  rewrite branch_ne_U, (U_atom E 33 cnt (EX 1%nat cnt ltac:(lia) eq_refl) Hc64),
    (U_atom E 34 fail (EX 2%nat fail ltac:(lia) eq_refl) Hf64) in Hb.
  apply negb_false_iff, Z.eqb_eq in Hb. exact (Hcf Hb). }
intros _ HS2. clear HS.
(* 0x82a90: a0 = -17; stops at `bltu a0, s0` *)
fsw_aj_runU tbl_fm_ok HS2 HJ HARU.
{ eapply ow_awr_skel; [| exact (A0 A_fuzz_malloc 16 FS_PSTAT_FP _ _ _ _ _ (fun a H => H) ltac:(unfold ASTACK in FM; lia))].
  lazymatch goal with |- skeleton _ = skeleton _ => vm_compute; reflexivity end. }
clear HF HFr HG.
eapply SRr_sym_branch with (c := BC_LTU) (a := SLit 18446744073709551599) (b := SOff 10 0) (1 := HS2).
1: { (* taken: n > 2^64 - 17, refuted *)
  intros Hb _. exfalso.
  rewrite branch_ltu_U, (U_lit E 18446744073709551599 ltac:(lia)), (U_atom E 10 n E10 Hn64) in Hb.
  apply Z.ltb_lt in Hb. unfold MALLOC_MAX, HEAD in *. lia. }
intros _ HS3. clear HS2.
(* 0x82a98: a0 = n + 16; `jal __wrap_malloc`: stops at the fetch of B's __wrap_malloc *)
fsw_aj_runU tbl_fm_ok HS3 HJ HARU.
{ eapply ow_awr_skel; [| exact (A0 A_fuzz_malloc 16 FS_PSTAT_FP _ _ _ _ _ (fun a H => H) ltac:(unfold ASTACK in FM; lia))].
  lazymatch goal with |- skeleton _ = skeleton _ => vm_compute; reflexivity end. }
clear HF HFr HG.
rewrite ?wvb_collapse in HJ, HARU.
(* ---- at the `jal __wrap_malloc` target: register facts, the statics, the call ---- *)
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms1 HS3 eq_refl) as Hshape.
assert (E33 : ew E 33 = Z_to_bv 64 cnt) by exact (EX 1%nat cnt ltac:(lia) eq_refl).
assert (U10 : bv_unsigned (ew E 10) = n) by (rewrite E10; apply unsigned_lit_small; lia).
assert (R1 : getr (ms_regs ms1) 1 = Z_to_bv 64 A_fuzz_malloc_raB)
  by exact (fsw_reg_lit _ E _ ms1 1%bv 535200 HS3 ltac:(vm_compute; reflexivity) ltac:(lia)).
assert (R10 : getr (ms_regs ms1) 10 = w64 (n + 16)).
{ pose proof (fsw_reg_off _ E _ ms1 10%bv 10 16 n HS3 ltac:(vm_compute; reflexivity) U10
    ltac:(unfold MALLOC_MAX, HEAD in *; lia)) as H.
  unfold w64. rewrite <- H. symmetry. apply Z_to_bv_bv_unsigned. }
assert (Rsp : spZ (ms_regs ms1) = spZ regs - 16).
{ unfold spZ at 1. exact (fsw_reg_off _ E _ ms1 2%bv 2 (-16) (spZ regs) HS3 ltac:(vm_compute; reflexivity) Usp
    ltac:(unfold spZ in *; pose proof (bv_unsigned_in_range _ (getr regs 2)); lia)). }
assert (R3 : getr (ms_regs ms1) 3 = getr regs 3)
  by exact (fsw_reg_atom (w_H W) regs _ _ ms1 3%bv 3%bv 3 HS3 ltac:(vm_compute; reflexivity) eq_refl).
assert (R4 : getr (ms_regs ms1) 4 = getr regs 4)
  by exact (fsw_reg_atom (w_H W) regs _ _ ms1 4%bv 4%bv 4 HS3 ltac:(vm_compute; reflexivity) eq_refl).
assert (R8 : getr (ms_regs ms1) 8 = getr regs 10)
  by exact (fsw_reg_atom (w_H W) regs _ _ ms1 8%bv 10%bv 10 HS3 ltac:(vm_compute; reflexivity) eq_refl).
pose proof HS3 as HS3c. destruct HS3c as (_ & _ & _ & _ & _ & _ & _ & HM3 & _).
(* the statics at the call: g_count = cnt + 1 (fs_glob read back from the symbolic memory) *)
assert (G1 : fs_glob tfibsegs W (ms_mem ms1) live peak (cnt + 1) fail).
{ apply (fs_glob_of_TS E W _ _ live peak (cnt + 1) fail (SOff 35 0) (SOff 36 0) (SOff 33 1) (SOff 34 0) HM3).
  all: first
    [ solve [lazymatch goal with |- fs_pstat_find _ _ = Some _ => vm_compute; reflexivity end]
    | solve [rewrite fsw_SOff0; exact (EX 3%nat live ltac:(lia) eq_refl)]
    | solve [rewrite fsw_SOff0; exact (EX 4%nat peak ltac:(lia) eq_refl)]
    | solve [rewrite fsw_SOff0; exact (EX 2%nat fail ltac:(lia) eq_refl)]
    | solve [lazymatch goal with |- sv_denot _ (SOff 33 1) = _ =>
               apply bv_eq; rewrite denot_SOff, E33; rewrite !unsigned_lit_small by lia;
               apply zcanon_id; unfold M64; lia end]
    | solve [lia] ]. }
rewrite Hshape.
replace (Z_to_bv 64 (ss_pc _)) with (Z_to_bv 64 (pc_wrap_malloc (as_code B))) by (rewrite (ts_code B HB); reflexivity).
eapply SRr_bind.
{ apply (fsw_aj_malloc04U_sub B FS_ENV ML FS_AMALLOC_AU W (ms_regs ms1) (ms_mem ms1) STK_fuzz_malloc (spZ regs)
    FS_PSTAT_FP ly S W mem md [] ly S U _ 0 (n + 16) (-16) (Z_to_bv 64 A_fuzz_malloc_raB) [] HJ HARU).
  all: first
    [ solve [exact R10] | solve [exact R1] | solve [rewrite R3; exact Hgp] | solve [rewrite R4; exact Htp]
    | solve [lazymatch goal with |- _ <= _ < MALLOC_MAX => unfold MALLOC_MAX, HEAD in *; lia end]
    | solve [lazymatch goal with |- blocks_bytes _ + _ <= _ => unfold HEAD in *; lia end]
    | solve [lazymatch goal with |- spZ _ = _ => rewrite Rsp; lia end]
    | solve [lazymatch goal with |- _ mod _ = _ => reflexivity end]
    | solve [lazymatch goal with |- ASTACK - _ <= _ => lia end]
    | solve [lazymatch goal with |- YK0s.ret_ok _ =>
               apply ret_ok_even; rewrite unsigned_lit_small by (unfold A_fuzz_malloc_raB; lia); reflexivity end]
    | solve [lazymatch goal with |- chain_pre _ _ _ _ =>
               unfold chain_pre; split;
               [ unfold raZ; rewrite R1, unsigned_lit_small by (unfold A_fuzz_malloc_raB; lia); unfold A_fuzz_malloc_raB; lia
               | destruct (frame0_ok ly (ms_regs ms1)); [|reflexivity];
                 replace (bad_next (spZ (ms_regs ms1)) (ly_top ly) (s0Z (ms_regs ms1))) with true; [reflexivity|];
                 symmetry; unfold bad_next; rewrite Rsp; unfold s0Z; rewrite R8, H10; unfold w64;
                 rewrite unsigned_lit_small by lia;
                 apply orb_true_iff; left; apply orb_true_iff; left; apply Z.leb_le;
                 unfold MALLOC_MAX, HEAD in *; lia ] end]
    | solve [lia] ]. }
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & b & -> & HARU2 & HJc & HP & Hb10 & Hfr & Hb4096 & Hbl & HK).
(* ---- resume at 0x82aa0 (FSW_K3.fsw_after_callFPU_args): the frame's two saved registers and the statics ---- *)
assert (Hnew : In (b, n + 16) (ablocks B ly2 S2)) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
assert (Hrq : req_size (n + 16) = n + 16) by (unfold req_size; destruct (Z.eqb_spec (n + 16) 0); lia).
destruct (al_blocks _ _ LAWS ly2 S2 W2 (unpoison U mem2) md2 b (n + 16) (proj1 HARU2) Hnew) as (Hb16 & _ & Hbceil & _).
pose proof alloc_ceiling_val as AC.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HstJ & _).
pose proof HstJ as (Hal16J & Hstk0J & HceilJ & HsloJ & HshiJ & H47J & HbotJ & Htop2J & HtopJ).
assert (Ub : bv_unsigned (getr regs2 10) = b) by (rewrite Hb10; unfold w64; apply unsigned_lit_small; lia).
assert (P2 : getr regs2 2 = getr (ms_regs ms1) 2) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs2 8 = getr (ms_regs ms1) 8) by exact (HP 8 ltac:(unfold acallee_saved; lia)).
set (xs := fmB_xs regs cnt fail live peak).
set (E2 := Ereg regs2 (fs_extraT ++ xs)).
assert (E2_10 : bv_unsigned (ew E2 10) = b) by (subst E2; rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl); exact Ub).
assert (E2_2 : bv_unsigned (ew E2 2) = spZ regs - 16)
  by (subst E2; rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl), P2; unfold spZ in Rsp; exact Rsp).
assert (EX2 : forall j w, nth j (fs_extraT ++ xs) (Z_to_bv 64 0) = w -> ew E2 (32 + j) = w)
  by (intros j w Hw; subst E2; rewrite ew_Ereg_extra; exact Hw).
assert (G2 : fs_glob tfibsegs W2 mem2 live peak (cnt + 1) fail)
  by exact (fmB_glob_acall ly S U W W2 (ms_mem ms1) mem2 _ ly2 S2 md2 _ _ _ live peak (cnt + 1) fail HARU HARU2 HK G1).
replace (spZ regs + -16) with (spZ (ms_regs ms1)) in HJc by lia.
(* the frame's two saved registers, read at the call (the call state's frame region), moved to atoms 37 / 38 *)
destruct HM3 as (_ & HR3 & _).
cbn [ss_mem] in HR3.
pose proof (Forall_inv HR3) as (_ & _ & _ & HCK).
cbn [YP09.r_chunks YP09.r_base base_val] in HCK. rewrite Usp in HCK.
assert (FC : forall off e, In (YP09.mkChunk off (CVal 8 e))
    [YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))] ->
  YP09.chunk_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms1)) (spZ regs) (YP09.mkChunk off (CVal 8 e)))
  by (intros off e Hin; exact (proj1 (Forall_forall _ _) HCK _ Hin)).
assert (V : forall (k j : nat) (r : bv 5), nth j (fs_extraT ++ xs) (Z_to_bv 64 0) = getr regs r ->
    Z.of_nat k = bv_unsigned r -> sv_denot E (SOff k 0) = sv_denot E2 (SOff (32 + j) 0)).
{ intros k j r Hn Hk. rewrite !fsw_SOff0. rewrite (EX2 j _ Hn). subst E. exact (ew_Ereg_nat regs _ k r Hk). }
assert (Hck : Forall (YP09.chunk_ok tfibsegs E2 (mrestrict (w_H W) (ms_mem ms1)) (spZ regs - 16)) fmB_cs).
{ unfold fmB_cs. constructor; [|constructor; [|constructor]].
  - apply (ow_chunk_move E E2 _ (spZ regs) (spZ regs - 16) (-16) 0 8 (SOff 8 0) (SOff 38 0));
      [lia | exact (V 8%nat 6%nat 8%bv eq_refl eq_refl) | apply FC; cbn; tauto].
  - apply (ow_chunk_move E E2 _ (spZ regs) (spZ regs - 16) (-8) 8 8 (SOff 1 0) (SOff 37 0));
      [lia | exact (V 1%nat 5%nat 1%bv eq_refl eq_refl) | apply FC; cbn; tauto]. }
assert (Hrs : Forall (region_ok tfibsegs E2 (mrestrict (w_H W2) mem2)) fs_pstat_regions)
  by exact (ow_pstat_ok W2 regs2 mem2 live peak (cnt + 1) fail [getr regs 1; getr regs 8] G2).
assert (Hpdj : pairwise_disjoint E2 (fsT_ret_regions 16 fmB_cs fs_pstat_regions)).
{ apply pairwise_disjoint_of_extents.
  unfold fsT_ret_regions, fs_pstat_regions, fs_got_region, fs_bcell_region, fstk_ret, fs_pstat_region, extent_of_region.
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E2_2.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address,
    G_COUNT, G_FAIL, G_LIVE, G_PEAK in *.
  cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia | lia]. }
destruct (fsw_after_callFPU_args B STK_fuzz_malloc (spZ regs) FS_PSTAT_FP [] ly S U W mem md W ly S U (ms_mem ms1) _ 0
  ASTACK [] 16 (ms_regs ms1) ly2 S2 U W2 regs2 mem2 md2 1 xs fmB_cs fs_pstat_regions [] A_fuzz_malloc_raB
  FS_GOT_SHADOW FS_SHADOW_CELL HJ HARU HJc (fun a Ha => False_ind _ (inFP_nil a Ha))
  (proj1 (proj2 HARU2)) (proj2 (proj2 HARU2)) HP Rsp ltac:(lia) ltac:(unfold ASTACK; lia)
  ltac:(lia) eq_refl ltac:(vm_compute; reflexivity)
  ltac:(unfold fmB_cs; repeat constructor; cbn; lia) Hck Hrs Hpdj ltac:(first [exact I | constructor]))
  as (HJ2 & HARU3 & HS4).
fold E2 in HS4.
(* ---- 0x82aa0 `beqz a0` (not taken: a0 = b >= 4096), then a1 = n, restore, `j own`: stops at own's entry ---- *)
assert (A1 : forall ss, skeleton (ss_mem ss) = skeleton (ss_mem (fss_retT A_fuzz_malloc_raB 16 fmB_cs fs_pstat_regions [])) ->
  awr_ok tfibsegs B E2 (ss_mem ss) STK_fuzz_malloc (spZ regs) FS_PSTAT_FP (ablocks B ly S) (ablocks B ly2 S2) ly2 []
    (frames S))
  by (intros ss Hsk; eapply ow_awr_skel; [exact Hsk | exact (fsw_awr_retTS B IMG E2 A_fuzz_malloc_raB 16 STK_fuzz_malloc
    (spZ regs) fmB_cs [] FS_PSTAT_FP _ _ ly2 [] (frames S) E2_2 ltac:(unfold ASTACK in FM; lia) (fun a H => H))]).
fsw_aj_runU tbl_fm_ok HS4 HJ2 HARU3.
{ apply A1. reflexivity. }
clear HF HFr HG.
eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 10 0) (b := SLit 0) (1 := HS4).
1: { intros Hb' _. exfalso. rewrite branch_eq_U, U_SOff, E2_10, Z.add_0_r, (U_lit E2 0 ltac:(lia)) in Hb'.
     rewrite zcanon_id in Hb' by (unfold M64; lia). apply Z.eqb_eq in Hb'. lia. }
intros _ HS5. clear HS4.
fsw_aj_runU tbl_fm_ok HS5 HJ2 HARU3.
{ apply A1. lazymatch goal with |- skeleton _ = skeleton _ => vm_compute; reflexivity end. }
clear HF HFr HG.
rewrite ?wvb_collapse in HJ2, HARU3.
rename ms into ms_beqz. rename ms0 into ms.
(* ---- the tail call into own ---- *)
pose proof HS5 as HS5c. destruct HS5c as (_ & _ & _ & _ & _ & _ & _ & HM5 & _).
pose proof (st_ok_restrict_mkst tfibsegs (w_H W2) E2 _ ms HS5 eq_refl) as Hshape5.
assert (E2_37 : ew E2 37 = getr regs 1) by exact (EX2 5%nat _ eq_refl).
assert (E2_38 : ew E2 38 = getr regs 8) by exact (EX2 6%nat _ eq_refl).
(* the registers at own's entry: ra / sp / s0 the caller's, a0 = b, a1 = n, gp / tp and s1 .. s11 untouched *)
assert (T1 : getr (ms_regs ms) 1 = getr regs 1).
{ apply bv_eq. rewrite (fsw_reg_off _ E2 _ ms 1%bv 37 0 (bv_unsigned (getr regs 1)) HS5 ltac:(vm_compute; reflexivity)
    ltac:(rewrite E2_37; reflexivity)
    ltac:(pose proof (bv_unsigned_in_range _ (getr regs 1)) as Hrr; change (bv_modulus 64) with (2 ^ 64) in Hrr; lia)). lia. }
assert (T8 : getr (ms_regs ms) 8 = getr regs 8).
{ apply bv_eq. rewrite (fsw_reg_off _ E2 _ ms 8%bv 38 0 (bv_unsigned (getr regs 8)) HS5 ltac:(vm_compute; reflexivity)
    ltac:(rewrite E2_38; reflexivity)
    ltac:(pose proof (bv_unsigned_in_range _ (getr regs 8)) as Hrr; change (bv_modulus 64) with (2 ^ 64) in Hrr; lia)). lia. }
assert (Tsp : spZ (ms_regs ms) = spZ regs).
{ unfold spZ at 1. rewrite (fsw_reg_off _ E2 _ ms 2%bv 2 16 (spZ regs - 16) HS5 ltac:(vm_compute; reflexivity) E2_2
    ltac:(unfold spZ in *; pose proof (bv_unsigned_in_range _ (getr regs 2)); lia)). lia. }
assert (T10 : getr (ms_regs ms) 10 = w64 b).
{ rewrite (fsw_reg_atom (w_H W2) regs2 (fs_extraT ++ xs) _ ms 10%bv 10%bv 10 HS5 ltac:(vm_compute; reflexivity) eq_refl).
  exact Hb10. }
assert (T11 : getr (ms_regs ms) 11 = w64 n).
{ rewrite (fsw_reg_atom (w_H W2) regs2 (fs_extraT ++ xs) _ ms 11%bv 8%bv 8 HS5 ltac:(vm_compute; reflexivity) eq_refl).
  rewrite P8, R8. exact H10. }
assert (TP : aregs_preserved regs (ms_regs ms)).
{ intros r Hcs.
  assert (Hr : In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]) by (cbn; unfold acallee_saved in Hcs; lia).
  repeat (destruct Hr as [<- | Hr]); [..| destruct Hr].
  all: first
    [ solve [apply bv_eq; change (bv_unsigned (getr (ms_regs ms) (Z_to_bv 5 2)) = bv_unsigned (getr regs (Z_to_bv 5 2)));
             exact Tsp]
    | solve [exact T8]
    | solve [lazymatch goal with |- getr _ (Z_to_bv 5 ?z) = _ =>
        let k := eval vm_compute in (Z.to_nat z) in
        transitivity (getr regs2 (Z_to_bv 5 z));
        [ exact (fsw_reg_atom (w_H W2) regs2 (fs_extraT ++ xs) _ ms (Z_to_bv 5 z) (Z_to_bv 5 z) k HS5
                   ltac:(vm_compute; reflexivity) eq_refl)
        | transitivity (getr (ms_regs ms1) (Z_to_bv 5 z));
          [ exact (HP z ltac:(unfold acallee_saved; lia))
          | exact (fsw_reg_atom (w_H W) regs (fs_extraTS cnt fail live peak) _ ms1 (Z_to_bv 5 z) (Z_to_bv 5 z) k HS3
                     ltac:(vm_compute; reflexivity) eq_refl) ] ] end] ]. }
assert (Tgp : getr (ms_regs ms) 3 = w64 (as_gp B))
  by (transitivity (getr regs 3); [exact (TP 3 ltac:(unfold acallee_saved; lia)) | exact Hgp]).
assert (Ttp : getr (ms_regs ms) 4 = w64 (as_tp B))
  by (transitivity (getr regs 4); [exact (TP 4 ltac:(unfold acallee_saved; lia)) | exact Htp]).
(* the block malloc made is fresh, its head no head of U; U's heads stay heads of the grown block list *)
assert (Hfresh : ~ In (b, n + 16) (ablocks B ly S))
  by exact (fresh_of_snoc B ly2 S2 W2 (unpoison U mem2) md2 (ablocks B ly S) b (n + 16) (proj1 HARU2) Hbl
    ltac:(rewrite Hrq; lia)).
assert (Hnin : ~ In (b, 16) U).
{ intros Hin. pose proof (new_head_disjoint B ly S ly2 S2 W2 (unpoison U mem2) md2 U b (n + 16) (proj1 HARU2) FH
    (fun x Hx => ltac:(rewrite Hbl; apply in_or_app; left; exact Hx)) Hnew Hfresh ltac:(rewrite Hrq; lia) _ Hin) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. lia. }
assert (FH2 : FSupoisonU.fs_heads B ly2 S2 U).
{ intros r Hr. destruct (FH r Hr) as (E16 & m & Hm & M16). split; [exact E16|]. exists m.
  split; [rewrite Hbl; apply in_or_app; left; exact Hm | exact M16]. }
(* the statics at own's entry *)
assert (G5 : fs_glob tfibsegs W2 (ms_mem ms) live peak (cnt + 1) fail).
{ apply (fs_glob_of_TS E2 W2 _ _ live peak (cnt + 1) fail (SOff 35 0) (SOff 36 0) (SOff 33 0) (SOff 34 0) HM5).
  all: first
    [ solve [lazymatch goal with |- fs_pstat_find _ _ = Some _ => vm_compute; reflexivity end]
    | solve [rewrite fsw_SOff0; exact (EX2 3%nat _ eq_refl)]
    | solve [rewrite fsw_SOff0; exact (EX2 4%nat _ eq_refl)]
    | solve [rewrite fsw_SOff0; exact (EX2 1%nat _ eq_refl)]
    | solve [rewrite fsw_SOff0; exact (EX2 2%nat _ eq_refl)]
    | solve [lia] ]. }
(* own's fpreU: the caller's journal at o = 0, the read-only view kept, the caller's chain kept (above sp0) *)
pose proof HJ2 as (_ & HlyJ & _ & _ & _ & _ & _ & _ & HkeepJ & _).
pose proof HlyJ as (_ & _ & _ & _ & _ & _ & _ & _ & Etop2 & _).
assert (HRO5 : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W2) (ms_mem ms)))
  by exact (arodata_kept B STK_fuzz_malloc (spZ regs) FS_PSTAT_FP ly S U W mem md ly2 S2 U W2 (ms_mem ms) _ (0 + 1)
    HJ2 HARU0 (proj1 (proj2 HARU3)) (proj2 (proj2 HARU3)) fmB_pstat_sink fmB_pstat_not_ro HRO).
assert (Hch5 : achain ly2 (aview tfibsegs (w_H W2) (unpoison U (ms_mem ms))) (spZ (ms_regs ms)) (s0Z (ms_regs ms)) ch).
{ rewrite Tsp. unfold s0Z. rewrite T8. fold (s0Z regs).
  apply (achain_ly_top ly ly2 _ _ _ _ Etop2).
  apply (achain_kept ly _ _ _ _ _ (spZ regs) Hch ltac:(lia) ltac:(lia)).
  intros a Ha. apply HkeepJ; [lia | lia]. }
assert (HPRE5 : fpreU tfibsegs B STK_own ly2 S2 U W2 (ms_regs ms) (ms_mem ms) _ ch)
  by exact (fsw_fpreU_atFP B STK_fuzz_malloc (spZ regs) FS_PSTAT_FP ly S U W (unpoison U mem) md [] ly2 S2 W2 (ms_mem ms) _
    (0 + 1) (ms_regs ms) STK_own 0 ch HJ2 HARU3 HRO5 ltac:(lia) eq_refl ltac:(lia)
    ltac:(apply Z.leb_le; vm_compute; reflexivity) ltac:(lia)
    ltac:(rewrite T1; exact Hra) ltac:(unfold raZ; rewrite T1; exact Hra4) Tgp Ttp Hch5).
rewrite Hshape5.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdg) ?Qg =>
  change (SRr tfibsegs W2 (cfg_at tfibsegs A_own (ms_regs ms) (ms_mem ms) mdg) Qg) end.
eapply SRr_mono.
{ apply (own_holds B IMG SHS FS_POISON ly2 S2 U W2 (ms_regs ms) (ms_mem ms) _ ch b n live peak (cnt + 1) fail HPRE5 FH2).
  all: first
    [ solve [exact T10] | solve [exact T11] | solve [exact Hnew] | solve [exact Hnin] | solve [exact Hb16]
    | solve [exact Hb4096] | solve [exact Hn1] | solve [exact Hn2] | solve [exact G5] | solve [exact Hlv]
    | solve [lazymatch goal with |- range_addressable _ _ _ _ =>
               pose proof (fmB_block_addressable B ly2 S2 U W2 (ms_mem ms) _ b (n + 16) HARU3 FH2 Hnew Hnin) as RA;
               rewrite Hrq in RA; exact RA end]
    | solve [lazymatch goal with |- _ < 2 ^ 64 - HEAD => rewrite Hrq in Hbceil; unfold HEAD; lia end] ]. }
intros W' c' _ HQ. exists (b + HEAD). rewrite Z.add_simpl_r.
unfold apost_baseU in HQ |- *.
(* own's post (HQ) fixes fmB_tail_post's Q1 before its other premises are closed *)
refine (fmB_tail_post STK_fuzz_malloc (spZ regs) FS_PSTAT_FP regs ly S U W mem md (0 + 1) ly2 S2 U W2 (ms_mem ms) _
  (ms_regs ms) STK_own (FS_PSTAT_FP ++ [(b, b + 8)]) 0 1 _ _ _ _ _ _ _ _ _ _ _ W' c' HQ).
all: first
  [ solve [exact HJ2] | solve [exact Tsp] | solve [exact FMo] | solve [exact T1] | solve [exact TP]
  | solve [lazymatch goal with |- _ + _ = _ => lia end]
  | solve [exact HQ]
  | solve [lazymatch goal with |- forall a, inFP _ a -> _ =>
      intros a (r & Hr & Ha); apply in_app_or in Hr as [Hr | Hr];
      [ left; assert (Hp : inFP FS_PSTAT_FP a) by (exists r; split; assumption);
        split; [exact Hp | exact (fs_pstat_img a Hp)]
      | right; destruct Hr as [Ep | []]; rewrite <- Ep in Ha; cbn [fst snd] in Ha;
        exists b, (n + HEAD); split; [exact Hnew|]; split; [exact Hfresh | unfold HEAD; rewrite Hrq; lia] ] end]
  | (* own's post Q into fuzz_malloc's at res = b + HEAD *)
    solve [intros ly' S' W'' regs' mem' md' HQ1; cbv beta in HQ1; destruct HQ1 as (Q10 & Qbl & Qfh & Qrb & Qra & Qgl);
           split; [exact Q10|]; split; [unfold HEAD; lia|]; split; [rewrite Qbl, Hbl; reflexivity|];
           split; [exact Qfh|]; split; [intros _; exact Qrb|]; split; [exact Qra | exact Qgl]] ].
Qed.

End m.

(* fuzz_malloc_spec of lib/B/FSH_Fn_alloc.v: the two arms, by failing() *)
Theorem fuzz_malloc_holds : forall {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} (B : asyms),
  fs_img_facts tfibsegs B -> FsShadowSyms B -> TfibSyms B -> api_env tfibsegs B ->
  FSupoisonU.amalloc_realizesU tfibsegs B -> fs_poison16 tfibsegs B -> @fuzz_malloc_spec fx rc SK tfibsegs B.
Proof.
intros fx rc SK B IMG SHS HB FS_ENV FS_AMALLOC_AU FS_POISON.
unfold fuzz_malloc_spec.
intros ly S U W regs mem md ch n live peak cnt fail HPRE FH H10 Hn1 Hn2 HGL Hlv Hcn Hev Hbb.
destruct (Z.eq_dec cnt fail) as [Hcf | Hcf].
- eapply SRr_mono; [exact (fmB_null_arm B IMG SHS ly S U W regs mem md ch live peak cnt fail HPRE FH HGL Hcn Hcf) |].
  intros W' c' _ HQ. left. split; [exact Hcf | exact HQ].
- eapply SRr_mono;
    [exact (fmB_malloc_arm B IMG SHS HB FS_ENV FS_AMALLOC_AU FS_POISON ly S U W regs mem md ch n live peak cnt fail
              HPRE FH H10 Hn1 Hn2 HGL (Hlv Hcf) Hcn Hev (Hbb Hcf) Hcf) |].
  intros W' c' _ HQ. right. split; [exact Hcf | exact HQ].
Qed.
