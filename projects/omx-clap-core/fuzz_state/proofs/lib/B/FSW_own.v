(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACf1.v, with its module paths and module names changed; 639 of its 687 lines of code are new or changed and 451 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_fuzz_free.v, with its module paths and module names changed; 530 of its 619 lines of code are new or changed and 598 lines of the source are left out. *)
(* fs ASan, group ALLOC, image B (fs.asan-ubsan): the walk of B's out-of-line own() (A_own = 0x82acc, alloc.c:41-49),
   proving own_spec of lib/B/FSH_Fn_alloc.v (statement a working branch bd583ec73f2: FP =
   FS_PSTAT_FP ++ [(b, b + 8)], exactly the 8 head bytes own writes; no CTX).

   proves function own (B 0x82acc) (reuse search: proof-index on main@c4c03c57ba1 / ossv/recipes@e5e7eba2cc0 /
   ossv/candidates@ee89628c997 / release/pau-projects-recipes@b6a0088adcb + lemma index over 11131 working branches + live
   working heads; by address on the four release refs / `proof-index fuzz_strdup fuzz_alloc_live fuzz_alloc_peak
   fuzz_alloc_peak_reset fuzz_alloc_fail own`, `git grep -l -i -e <addr> <ref> -- proofs/omx-clap-core/fuzz_state`).
   Result (a Theorem Labs lane, brief-B-walks.md): own: 0 files named for it, 0 by address; written new, porting ALLOC's A proof
   of fuzz_malloc (lib/A/FSW_fuzz_malloc.v, where A inlines own).

   Measured control flow (capstone on the unstripped twin of the pinned fs.asan-ubsan; a Theorem Labs lane own_spec_B.md):
   0x82acc..0x82ad8 frame 32 (FRAME_own), save ra / s0 / s1; 0x82adc..0x82ae4 a2 = the shadow base (GOT word 0x9fc10 ->
   cell 0xa8438); s0 = b, s1 = n; the two inline 8-byte shadow checks of the head (0x82aec..0x82b10, report arms not
   taken); the eight `sb` of n into b[0..8) (0x82b2c..0x82b4c); `jal __asan_poison_memory_region` 0x82b58 (ra 0x82b5c)
   with (b, 16); g_live += n (0x82b70), `bgeu g_peak, live + n` 0x82b74 (g_peak := live + n when below); the UBSan
   pointer-overflow check `bgeu b, 2^64 - 16` 0x82b80 to `unimp` (not taken: b < 2^64 - HEAD); a0 = b + 16; restore;
   ret 0x82b98.

   Shape: lib/A/FSW_fuzz_malloc.v's own() part (the token run over FSW_head's shent, the poison step
   FSW_poison_conv.fsw_poison16_atU with Permutation_cons_append, the resume FSW_rres.fsw_resume_after_rtU_args, then
   the g_live / g_peak tail with fsw_retU and FSW_statics.fs_glob_of_TS), from an entry state of its own:
   FSW_K.fsw_entryT_argsX with the four statics and the head's region (writable [b, b + 8)). The head is a block of the
   caller (in ablocks at entry), so its stores go through awr_byte0's FP arm (the spec's [(b, b + 8)]).
   STACK: the poison contract's ecall_pre needs ESTACK (4096) present bytes below the call's sp = sp0 - 32; own_walk
   takes `ESTACK + 32 <= STK_own` as its premise (a Theorem Labs lane is landing STK_RT_POISON := ESTACK, which gives it).
   Kit rules R1 / R2 followed. Relocated files: none. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen FSpoisonS.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSH_Fn_alloc FSW_K FSW_K3 FSW_ret FSW_rres FSW_rd FSW_statics FSW_statics_awr FSW_head
FSW_malloc_free FSpoisonS FSW_poison_conv.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YB13.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ---- code table: own, A_own = 0x82acc, st_size 248 (62 words, no RVC; capstone on the unstripped twin) ---- *)
Definition tbl_own : ctable := Eval vm_compute in build_table tfibsegs A_own 62 TEmpty.
Lemma tbl_own_eq : tbl_own = build_table tfibsegs A_own 62 TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_own). Qed.
Lemma tbl_own_ok : table_ok tfibsegs tbl_own.
Proof. rewrite tbl_own_eq. apply build_table_ok0. unfold A_own. lia. Qed.

(* the return address of own's `jal __asan_poison_memory_region` (0x82b58; MEASURED) *)
Definition A_own_ra_po : Z := 0x82b5c.

Lemma ow_awr_skel : forall segs B E rs rs' STK sp0 FP bl0 blc ly own fr0,
  skeleton rs' = skeleton rs ->
  awr_ok segs B E rs STK sp0 FP bl0 blc ly own fr0 -> awr_ok segs B E rs' STK sp0 FP bl0 blc ly own fr0.
Proof. intros segs B E rs rs' STK sp0 FP bl0 blc ly own fr0 Hsk H a Ha. apply H. exact (in_wrange_skeleton E rs' rs a Hsk Ha). Qed.

(* B's GOT word 0x9fc10 and shadow cell 0xa8438 are image bytes (FSW_statics.fs_pstat_img's method) *)
Definition OW_CELLS : list (Z * Z) := [(0x9fc10, 0x9fc18); (0xa8438, 0xa8440)].
Lemma ow_cells_img : forall a, inFP OW_CELLS a -> in_img tfibsegs a.
Proof.
intros a (r & Hr & Ha).
assert (Hb : forallb (fun r : Z * Z => existsb (fun s => (Z.of_N (seg_base s) <=? fst r) &&
    (snd r <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs) OW_CELLS = true) by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) Hb r Hr) as H. cbv beta in H.
apply existsb_exists in H as (s & Hs & Hss). apply andb_prop in Hss as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists s. split; [exact Hs | lia].
Qed.

Lemma ow_chunk_move : forall E E' m base base' off off' sz e e',
  base + off = base' + off' -> sv_denot E e = sv_denot E' e' ->
  YP09.chunk_ok tfibsegs E m base (YP09.mkChunk off (CVal sz e)) ->
  YP09.chunk_ok tfibsegs E' m base' (YP09.mkChunk off' (CVal sz e')).
Proof.
intros E E' m base base' off off' sz e e' Hb He H i Hi. destruct (H i Hi) as (b & H1 & H2). exists b.
cbn [YP09.cbyte YP09.c_off YP09.c_val] in *. rewrite <- He, <- Hb. split; [exact H1 | exact H2].
Qed.

(* FSW_statics.fs_pstat_regions_ok under an env with further atoms after the statics' *)
Lemma ow_pstat_ok : forall (W : world tfibsegs) regs mem live peak cnt fail ys,
  fs_glob tfibsegs W mem live peak cnt fail ->
  Forall (region_ok tfibsegs (Ereg regs (fs_extraTS cnt fail live peak ++ ys)) (mrestrict (w_H W) mem)) fs_pstat_regions.
Proof.
intros W regs mem live peak cnt fail ys GL.
pose proof GL as (G1 & G2 & G3 & G4 & GR).
set (E := Ereg regs (fs_extraTS cnt fail live peak ++ ys)).
assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j (fs_extraTS cnt fail live peak) (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite ew_Ereg_extra; apply app_nth1; cbn; lia).
assert (RS : forall g (j : nat) v, (1 <= j < 5)%nat -> nth j (fs_extraTS cnt fail live peak) (Z_to_bv 64 0) = Z_to_bv 64 v ->
  0 <= v < 2 ^ 64 -> 0x9f000 <= g -> g + 8 <= 0x5fd000 -> val_mem tfibsegs (mrestrict (w_H W) mem) g 8 v ->
  region_ok tfibsegs E (mrestrict (w_H W) mem) (fs_pstat_region g (32 + j))).
{ intros g j v Hj Hv Hr Hg1 Hg2 Hm.
  unfold region_ok, fs_pstat_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  split; [lia|]. split; [lia|]. split.
  - intros o Ho. unfold writable_at. apply YB13.tfib_rw_window. rewrite unsigned_lit_small by lia. lia.
  - constructor; [|constructor].
    exact (chunk_ok_val tfibsegs _ _ 0 g 8 (SOff (32 + j) 0) v
      ltac:(rewrite fsw_SOff0; etransitivity; [exact (EX j ltac:(lia)) | exact Hv]) ltac:(cbn [Z.of_N]; lia)
      ltac:(cbn [Z.of_N]; lia) ltac:(cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_l; exact Hm)). }
unfold fs_pstat_regions, xatom.
constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
- apply (RS G_COUNT 1%nat cnt); first [solve [lia] | solve [reflexivity] | solve [unfold G_COUNT; lia] | solve [exact G3]].
- apply (RS G_FAIL 2%nat fail); first [solve [lia] | solve [reflexivity] | solve [unfold G_FAIL; lia] | solve [exact G4]].
- apply (RS G_LIVE 3%nat live); first [solve [lia] | solve [reflexivity] | solve [unfold G_LIVE; lia] | solve [exact G1]].
- apply (RS G_PEAK 4%nat peak); first [solve [lia] | solve [reflexivity] | solve [unfold G_PEAK; lia] | solve [exact G2]].
Qed.

(* the entry state's extra regions and atom facts: the four statics, the head of the block (b at a0 = atom 10) as a
   writable 8-byte region; atom 10 a 16-aligned block address below alloc_ceiling (the token run's shent range) *)
Definition ow_rs : list YP09.region := fs_pstat_regions ++ [fs_head_region 10 8 []].
Definition ow_gf : list (nat * afact) := [(10%nat, mkAF 4096 0x7fffff800000 4)].

(* own's eight `sb` of n (atom 11 = a1 at entry) into the head, as the token run leaves them (MEASURED) *)
Definition ow_head_cs : list YP09.chunk :=
  [YP09.mkChunk 3 (CVal 1 (SAlu ALU_SRL (SOff 11 0) (SLit 24)));
   YP09.mkChunk 2 (CVal 1 (SAlu ALU_SRL (SOff 11 0) (SLit 16)));
   YP09.mkChunk 1 (CVal 1 (SAlu ALU_SRL (SOff 11 0) (SLit 8)));
   YP09.mkChunk 0 (CVal 1 (SOff 11 0));
   YP09.mkChunk 7 (CVal 1 (SAlu ALU_SRL (SOff 11 0) (SLit 56)));
   YP09.mkChunk 6 (CVal 1 (SAlu ALU_SRL (SOff 11 0) (SLit 48)));
   YP09.mkChunk 5 (CVal 1 (SAlu ALU_SRL (SOff 11 0) (SLit 40)));
   YP09.mkChunk 4 (CVal 1 (SAlu ALU_SRL (SOff 11 0) (SLit 32)))].

Lemma ow_byte_chunk : forall E m h k e,
  YP09.chunk_ok tfibsegs E m h (YP09.mkChunk k (CVal 1 e)) ->
  mbyte tfibsegs m (h + k) = Some (Z_to_bv 8 (bv_unsigned (sv_denot E e))).
Proof.
intros E m h k e H.
destruct (H 0 ltac:(cbn; lia)) as (b0 & H1 & H2).
cbn [YP09.cbyte YP09.c_off YP09.c_val] in H1, H2.
injection H1 as <-.
rewrite Z.add_0_r in H2. rewrite H2. unfold YP09.byte_of_word. rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity.
Qed.

Lemma ow_srl_unsigned : forall E (k : nat) n s, bv_unsigned (ew E k) = n -> 0 <= n < 2 ^ 64 -> 0 <= s < 64 ->
  bv_unsigned (sv_denot E (SAlu ALU_SRL (SOff k 0) (SLit s))) = Z.shiftr n s.
Proof.
intros E k n s Hn Hr Hs. cbn [sv_denot]. rewrite alu64_unsigned. cbn [zalu_raw].
rewrite !Z_to_bv_unsigned. rewrite Hn, Z.add_0_r.
assert (W1 : bv_wrap 64 n = n) by (apply bv_wrap_small; change (bv_modulus 64) with (2 ^ 64); lia).
assert (W2 : bv_wrap 64 s = s) by (apply bv_wrap_small; change (bv_modulus 64) with (2 ^ 64); lia).
rewrite W1, W2.
assert (L : Z.land s 63 = s)
  by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia; apply Z.mod_small; change (2 ^ 6) with 64; lia).
rewrite L.
assert (S0 : 0 <= Z.shiftr n s <= n).
{ split; [apply Z.shiftr_nonneg; lia|]. rewrite Z.shiftr_div_pow2 by lia.
  apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|].
  pose proof (Z.pow_pos_nonneg 2 s ltac:(lia) ltac:(lia)). nia. }
apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.

Lemma ow_head_val : forall E m h n,
  bv_unsigned (ew E 11) = n -> 0 <= n < 2 ^ 64 ->
  Forall (YP09.chunk_ok tfibsegs E m h) ow_head_cs -> val_mem tfibsegs m h 8 n.
Proof.
intros E m h n Hn Hr H k Hk.
rewrite (le_byte_small n 8 k ltac:(change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); lia) Hk).
unfold ow_head_cs in H.
pose proof (Forall_inv H) as Hc3. apply Forall_inv_tail in H.
pose proof (Forall_inv H) as Hc2. apply Forall_inv_tail in H.
pose proof (Forall_inv H) as Hc1. apply Forall_inv_tail in H.
pose proof (Forall_inv H) as Hc0. apply Forall_inv_tail in H.
pose proof (Forall_inv H) as Hc7. apply Forall_inv_tail in H.
pose proof (Forall_inv H) as Hc6. apply Forall_inv_tail in H.
pose proof (Forall_inv H) as Hc5. apply Forall_inv_tail in H.
pose proof (Forall_inv H) as Hc4.
destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; [..| lia].
all: first
  [ etransitivity; [exact (ow_byte_chunk E m h _ _ Hc0) |]
  | etransitivity; [exact (ow_byte_chunk E m h _ _ Hc1) |]
  | etransitivity; [exact (ow_byte_chunk E m h _ _ Hc2) |]
  | etransitivity; [exact (ow_byte_chunk E m h _ _ Hc3) |]
  | etransitivity; [exact (ow_byte_chunk E m h _ _ Hc4) |]
  | etransitivity; [exact (ow_byte_chunk E m h _ _ Hc5) |]
  | etransitivity; [exact (ow_byte_chunk E m h _ _ Hc6) |]
  | etransitivity; [exact (ow_byte_chunk E m h _ _ Hc7) |] ].
all: f_equal; f_equal.
all: first
  [ solve [apply (ow_srl_unsigned E 11 n); [exact Hn | exact Hr | lia]]
  | solve [change (8 * Z.of_nat 0) with 0; rewrite Z.shiftr_0_r; cbn [sv_denot]; rewrite Z_to_bv_unsigned, Hn, Z.add_0_r;
           apply bv_wrap_small; change (bv_modulus 64) with (2 ^ 64); lia] ].
Qed.

(* the state resumed after the poison call (0x82b5c), env Ereg regs3 (fs_extraT ++ ow_xs): atoms 33..36 the statics,
   37..39 the frame's saved ra / s0 / s1 (own saves three registers; slot 0 of the frame is unused) *)
Definition ow_cs : list YP09.chunk :=
  [YP09.mkChunk 8 (CVal 8 (SOff 39 0)); YP09.mkChunk 16 (CVal 8 (SOff 38 0)); YP09.mkChunk 24 (CVal 8 (SOff 37 0))].
Definition ow_xs (regs : bvmap 5 word) (cnt fail live peak : Z) : list word :=
  fs_pstat_xs cnt fail live peak ++ [getr regs 1; getr regs 8; getr regs 9].
(* the callee-saved registers at own's `ret`: sp back up by the frame, s0 / s1 reloaded from atoms 38 / 39 *)
Definition ow_expect (r : bv 5) : sv :=
  match bv_unsigned r with
  | 2 => SOff 2 32 | 8 => SOff 38 0 | 9 => SOff 39 0
  | z => SOff (Z.to_nat z) 0
  end.

Lemma ow_pstat_bounds : forall a, inFP FS_PSTAT_FP a ->
  (G_FAIL <= a < G_FAIL + 8) \/ (G_LIVE <= a < G_LIVE + 8) \/ (G_PEAK <= a < G_PEAK + 8) \/ (G_COUNT <= a < G_COUNT + 8).
Proof.
intros a (r & Hr & Ha). unfold FS_PSTAT_FP in Hr. unfold G_FAIL, G_LIVE, G_PEAK, G_COUNT.
repeat (destruct Hr as [<- | Hr]; [cbn [fst snd] in Ha; lia|]). destruct Hr.
Qed.

Lemma ow_glob_keep : forall (W W' : world tfibsegs) m m' live peak cnt fail,
  fs_glob tfibsegs W m live peak cnt fail ->
  (forall a, inFP FS_PSTAT_FP a -> mbyte tfibsegs (mrestrict (w_H W') m') a = mbyte tfibsegs (mrestrict (w_H W) m) a) ->
  fs_glob tfibsegs W' m' live peak cnt fail.
Proof.
intros W W' m m' live peak cnt fail (G1 & G2 & G3 & G4 & GR) He.
assert (V : forall g v, In (g, g + 8) FS_PSTAT_FP -> val_mem tfibsegs (mrestrict (w_H W) m) g 8 v ->
  val_mem tfibsegs (mrestrict (w_H W') m') g 8 v).
{ intros g v Hg Hv k Hk. rewrite He; [exact (Hv k Hk)|]. apply (inFP_FS_PSTAT_FP g Hg). lia. }
split; [apply (V G_LIVE); [vm_compute; tauto | exact G1]|].
split; [apply (V G_PEAK); [vm_compute; tauto | exact G2]|].
split; [apply (V G_COUNT); [vm_compute; tauto | exact G3]|].
split; [apply (V G_FAIL); [vm_compute; tauto | exact G4]|].
exact GR.
Qed.

Lemma ow_val_mem_frame : forall E rs (H : word -> bool) m m' a (k : nat) v,
  frame_of E rs m m' -> (forall i, (i < k)%nat -> ~ in_wrange E rs (a + Z.of_nat i)) -> 0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
  val_mem tfibsegs (mrestrict H m) a k v -> val_mem tfibsegs (mrestrict H m') a k v.
Proof.
intros E rs H m m' a k v HF Hn Ha Hk Hv i Hi. rewrite <- (Hv i Hi).
apply (mbyte_of_aview tfibsegs). apply (aview_at tfibsegs). apply HF. rewrite (wz (a + Z.of_nat i) ltac:(lia)). exact (Hn i Hi).
Qed.

(* the two halves of own's footprint FS_PSTAT_FP ++ [(b, b + 8)] *)
Lemma ow_fp_l : forall X a, inFP FS_PSTAT_FP a -> inFP (FS_PSTAT_FP ++ X) a.
Proof. intros X a (r & Hr & Ha). exists r. split; [apply in_or_app; left; exact Hr | exact Ha]. Qed.
Lemma ow_fp_head : forall X b a, b <= a < b + 8 -> inFP (X ++ [(b, b + 8)]) a.
Proof. intros X b a Ha. exists (b, b + 8). split; [apply in_or_app; right; left; reflexivity | cbn [fst snd]; lia]. Qed.

Section o. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* fs's image facts (FSH_Rt.fs_img_facts); owner RELOC, proved once for fs's TfibB; used for awr_byte's static arm *)
Hypothesis IMG : fs_img_facts tfibsegs B.
(* the two shadow-base cells of fs.asan-ubsan (GOT word 0x9fc10 -> cell 0xa8438): FSH_Base.FsShadowSyms, the one named
   shadow-cell hypothesis of fs's walks (owner the S0 start-up layer / B's TfibLib) *)
Hypothesis SHS : FsShadowSyms B.
Let FS_GOT_SHADOW : as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address := proj1 SHS.
Let FS_SHADOW_CELL : as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address := proj2 SHS.
(* __asan_poison_memory_region at B's entry PC_poison (lib/B/FSpoisonS.fs_poison16, A/FSpoisonS.v's apoison16_realizes
   text at B's PC_poison); owner the shared runtime (SHARED-WALKS row 'poison / unpoison'; B's proof not yet written) *)
Hypothesis FS_POISON : fs_poison16 tfibsegs B.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* a block's head (b, 16) apart from every head of U when (b, 16) is not one of them (U's heads start blocks, AR's blocks
   are pairwise disjoint) *)
Lemma ow_head_disjoint : forall ly S U (W : world tfibsegs) mem md b m,
  AR tfibsegs B ly S W mem md -> FSupoisonU.fs_heads B ly S U ->
  In (b, m) (ablocks B ly S) -> ~ In (b, 16) U -> 16 <= req_size m ->
  forall r, In r U -> zdisjoint (b, 16) r.
Proof.
intros ly S U W mem md b m HAR FH Hb Hnin Hm r Hr.
destruct (FH r Hr) as (E16 & m' & Hm' & Hreq). destruct r as [q s]. cbn [fst snd] in *. subst s.
destruct (Z.eq_dec q b) as [-> | Hqb]; [exfalso; exact (Hnin Hr)|].
assert (Hne : (b, m) <> (q, m')) by (intros E; injection E as E1 _; exact (Hqb (eq_sym E1))).
pose proof (sep_blocks tfibsegs B LAWS ly S W mem md b m q m' HAR Hb Hm' Hne) as D.
unfold zdisjoint in *. cbn [fst snd] in *. lia.
Qed.

(* across the poison call: an application byte away from the call's stack window keeps its machine value *)
Lemma ow_keep_app : forall ly S U U' (W : world tfibsegs) memT mem2 md md2 sp a,
  ARU tfibsegs B ly S U W memT md -> ARU tfibsegs B ly S U' W mem2 md2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - PO_WIN <= a < sp) ->
     aview tfibsegs (w_H W) (unpoison U' mem2) a = aview tfibsegs (w_H W) (unpoison U memT) a) ->
  0 <= a < 2 ^ 64 -> a < SHADOW_OFF \/ kHighMemBeg <= a -> ~ (sp - PO_WIN <= a < sp) ->
  mbyte tfibsegs (mrestrict (w_H W) mem2) a = mbyte tfibsegs (mrestrict (w_H W) memT) a.
Proof.
intros ly S U U' W memT mem2 md md2 sp a H1 H2 HK Ha Happ Hw.
apply (mbyte_of_aview tfibsegs).
assert (V1 : aview tfibsegs (w_H W) (unpoison U' mem2) a = aview tfibsegs (w_H W) mem2 a)
  by (apply (aview_at tfibsegs); exact (fs_head_app_view B ly S U' W mem2 md2 a H2 Ha Happ)).
assert (V2 : aview tfibsegs (w_H W) (unpoison U memT) a = aview tfibsegs (w_H W) memT a)
  by (apply (aview_at tfibsegs); exact (fs_head_app_view B ly S U W memT md a H1 Ha Happ)).
rewrite <- V1, <- V2. exact (HK a Ha Hw).
Qed.

(* awr_ok at own's entry state: FSW_statics_awr.fsw_awr_TS for the frame, cells and statics; the head's window
   [b, b + 8) through awr_byte0's FP arm (a byte of a live block in FP: the spec's [(b, b + 8)]) *)
Lemma ow_awr : forall E (pc STK sp0 b m : Z) gf FP bl0 blc ly own fr0,
  bv_unsigned (ew E 2) = sp0 -> 32 <= STK -> bv_unsigned (ew E 10) = b ->
  (forall a, inFP FS_PSTAT_FP a -> inFP FP a) -> (forall a, b <= a < b + 8 -> inFP FP a) ->
  In (b, m) blc -> 8 <= req_size m ->
  awr_ok tfibsegs B E (ss_mem (fss0T_args pc 32 ow_rs gf)) STK sp0 FP bl0 blc ly own fr0.
Proof.
intros E pc STK sp0 b m gf FP bl0 blc ly own fr0 E2 Hf E10 HFP HFPh Hin Hm a (rg & Hr & Ha).
change (In rg (fsT_regions_args 32 (fs_pstat_regions ++ [fs_head_region 10 8 []]))) in Hr.
unfold fsT_regions_args in Hr. rewrite app_assoc in Hr. apply in_app_or in Hr as [Hr | [<- | []]].
- apply (fsw_awr_TS B IMG E pc 32 STK sp0 FP bl0 blc ly own fr0 E2 ltac:(lia) HFP a).
  exists rg. split; [exact Hr | exact Ha].
- cbn [fs_head_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite E10 in Ha.
  left. right. left. split; [apply HFPh; lia|]. exists b, m. split; [exact Hin | lia].
Qed.

(* ---- the tail after the poison call: from the state resumed at 0x82b5c (fss_retT, rs = the statics) to the return.
   0x82b5c..0x82b70: g_live := live + n; `bgeu g_peak, live + n` 0x82b74 (taken skips g_peak := live + n); both arms
   `bgeu b, 2^64 - 16` 0x82b80 (taken = the UBSan trap, refuted); a0 = b + 16, epilogue, ret 0x82b98. ---- *)
Lemma ow_tail : forall ly S U (W : world tfibsegs) regs mem md b n live peak cnt fail regs3 mem3 md3,
  st_ok tfibsegs (Ereg regs3 (fs_extraT ++ ow_xs regs cnt fail live peak))
    (fss_retT A_own_ra_po 32 ow_cs fs_pstat_regions [])
    (restrict (w_H W) (mkst regs3 (Z_to_bv 64 A_own_ra_po) mem3 (seg_rom tfibsegs))) ->
  ajournal tfibsegs B STK_own (spZ regs) (FS_PSTAT_FP ++ [(b, b + 8)]) ly S W (unpoison U mem) md [] ly S W
    (unpoison (U ++ [(b, HEAD)]) mem3) md3 0 ->
  ARU tfibsegs B ly S (U ++ [(b, HEAD)]) W mem3 md3 ->
  spZ regs3 = spZ regs - 32 -> getr regs3 8 = w64 b -> getr regs3 9 = w64 n ->
  (forall r, acallee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> getr regs3 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  YK0s.ret_ok (getr regs 1) -> 1 <= n -> live + n < 2 ^ 64 -> 0 <= live <= peak -> peak < 2 ^ 64 ->
  0 <= cnt < 2 ^ 64 -> 0 <= fail < 2 ^ 64 -> 32 <= STK_own ->
  4096 <= b -> b mod 16 = 0 -> b < 2 ^ 64 - HEAD -> b + (n + HEAD) <= alloc_ceiling ->
  In (b, n + HEAD) (ablocks B ly S) -> fs_heads B ly S U ->
  val_mem tfibsegs (mrestrict (w_H W) mem3) b 8 n ->
  (forall g, In (g, g + 8) FS_PSTAT_FP -> b + 8 <= g \/ g + 8 <= b) ->
  SRr tfibsegs W (mkCfg (mkst regs3 (Z_to_bv 64 A_own_ra_po) mem3 (seg_rom tfibsegs)) md3)
    (apost_baseU tfibsegs B STK_own (FS_PSTAT_FP ++ [(b, b + 8)]) regs ly S W mem md 0 U (U ++ [(b, HEAD)])
       (fun ly' S' W' regs' mem' md' =>
          getr regs' 10 = w64 (b + HEAD) /\
          ablocks B ly' S' = ablocks B ly S /\
          fs_heads B ly' S' (U ++ [(b, HEAD)]) /\
          fs_rblock tfibsegs B ly' S' W' mem' (b + HEAD) n /\
          range_addressable (aview tfibsegs (w_H W') mem') SHADOW_OFF (b + HEAD) n /\
          fs_glob tfibsegs W' mem' (live + n) (Z.max peak (live + n)) cnt fail)).
Proof.
intros ly S U W regs mem md b n live peak cnt fail regs3 mem3 md3 HS6 HJ HARU Rsp3 R8 R9 Hkept Hra Hn1
  Hlv Hlp Hp64 Hc64 Hf64 HSTK Hb4096 Hb16 Hbtop Hbceil Hin FH Hval IS.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HstJ & _).
pose proof HstJ as (Hal16J & Hstk0J & HceilJ & HsloJ & HshiJ & H47J & HbotJ & Htop2J & HtopJ).
pose proof asan_consts as (C1 & _ & C3 & _).
set (E3 := Ereg regs3 (fs_extraT ++ ow_xs regs cnt fail live peak)) in HS6.
assert (E3_2 : bv_unsigned (ew E3 2) = spZ regs - 32)
  by (subst E3; rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl); unfold spZ in Rsp3; exact Rsp3).
assert (EX3 : forall j w, nth j (fs_extraT ++ ow_xs regs cnt fail live peak) (Z_to_bv 64 0) = w -> ew E3 (32 + j) = w)
  by (intros j w Hw; subst E3; rewrite ew_Ereg_extra; exact Hw).
assert (U3_8 : bv_unsigned (ew E3 8) = b)
  by (subst E3; rewrite (ew_Ereg_nat regs3 _ 8 8%bv eq_refl), R8; unfold w64; apply unsigned_lit_small; unfold HEAD in *; lia).
assert (U3_9 : bv_unsigned (ew E3 9) = n)
  by (subst E3; rewrite (ew_Ereg_nat regs3 _ 9 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (E3_35 : ew E3 35 = Z_to_bv 64 live) by exact (EX3 3%nat _ eq_refl).
assert (E3_36 : ew E3 36 = Z_to_bv 64 peak) by exact (EX3 4%nat _ eq_refl).
assert (E3_37 : ew E3 37 = getr regs 1) by exact (EX3 5%nat _ eq_refl).
assert (E3_38 : ew E3 38 = getr regs 8) by exact (EX3 6%nat _ eq_refl).
assert (E3_39 : ew E3 39 = getr regs 9) by exact (EX3 7%nat _ eq_refl).
assert (U3_35 : bv_unsigned (ew E3 35) = live) by (rewrite E3_35; apply unsigned_lit_small; lia).
assert (U3_36 : bv_unsigned (ew E3 36) = peak) by (rewrite E3_36; apply unsigned_lit_small; lia).
assert (Hrq : req_size (n + HEAD) = n + HEAD) by (unfold req_size, HEAD; destruct (Z.eqb_spec (n + 16) 0); lia).
assert (FH2 : fs_heads B ly S (U ++ [(b, HEAD)]))
  by exact (fs_heads_snoc B ly S ly S U b (n + HEAD) FH (fun x Hx => Hx) Hin ltac:(rewrite Hrq; unfold HEAD; lia)).
pose proof (IS G_FAIL ltac:(vm_compute; tauto)) as I3. pose proof (IS G_LIVE ltac:(vm_compute; tauto)) as I4.
pose proof (IS G_PEAK ltac:(vm_compute; tauto)) as I5. pose proof (IS G_COUNT ltac:(vm_compute; tauto)) as I6.
(* the head's 8 bytes are written by no region of the tail's runs (below the frame, off the statics) *)
assert (NW : forall rs, skeleton rs = skeleton (ss_mem (fss_retT A_own_ra_po 32 ow_cs fs_pstat_regions [])) ->
  forall i, (i < 8)%nat -> ~ in_wrange E3 rs (b + Z.of_nat i)).
{ intros rs Hsk i Hi Hw. apply (in_wrange_skeleton E3 rs _ _ Hsk) in Hw. destruct Hw as (rg & Hr & Ha).
  unfold fss_retT, fsT_ret_regions, fs_pstat_regions in Hr. cbn [ss_mem app] in Hr.
  repeat (destruct Hr as [<- | Hr]).
  all: first
    [ solve [exact Hr]
    | solve [cbn [fstk_ret fs_got_region fs_bcell_region fs_pstat_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
             rewrite ?E3_2 in Ha; unfold G_FAIL, G_LIVE, G_PEAK, G_COUNT, xatom, HEAD in *; lia] ]. }
assert (A3 : forall ss, skeleton (ss_mem ss) = skeleton (ss_mem (fss_retT A_own_ra_po 32 ow_cs fs_pstat_regions [])) ->
  awr_ok tfibsegs B E3 (ss_mem ss) STK_own (spZ regs) (FS_PSTAT_FP ++ [(b, b + 8)]) (ablocks B ly S)
    (ablocks B ly S) ly [] (frames S))
  by (intros ss Hsk; eapply ow_awr_skel; [exact Hsk | exact (fsw_awr_retTS B IMG E3 A_own_ra_po 32 STK_own
    (spZ regs) ow_cs [] _ _ _ ly [] (frames S) E3_2 ltac:(lia) (ow_fp_l _))]).
assert (ADD : sv_denot E3 (SAlu ALU_ADD (SOff 9 0) (SOff 35 0)) = Z_to_bv 64 (live + n)).
{ apply bv_eq. change (bv_unsigned (sv_denot E3 (SAlu ALU_ADD (SOff 9 0) (SOff 35 0))))
    with (YP0e.U E3 (SAlu ALU_ADD (SOff 9 0) (SOff 35 0))).
  rewrite U_add_off_atom; rewrite ?U3_9, ?U3_35; [rewrite unsigned_lit_small by lia; lia | unfold M64; lia | unfold M64; lia]. }
(* 0x82b5c..0x82b70: g_live := live + n; stops at `bgeu a3, s1` *)
fsw_aj_runU tbl_own_ok HS6 HJ HARU.
{ apply A3. reflexivity. }
pose proof HF as HF1. clear HFr HG HF.
eapply SRr_sym_branch with (c := BC_GEU) (a := SOff 36 0) (b := SAlu ALU_ADD (SOff 9 0) (SOff 35 0)) (1 := HS6).
all: intros Hbr HS7; clear HS6.
all: rewrite branch_geu_U, (U_off E3 36 0 ltac:(rewrite U3_36; unfold M64; lia)), U3_36 in Hbr.
all: change (YP0e.U E3 (SAlu ALU_ADD (SOff 9 0) (SOff 35 0))) with (bv_unsigned (sv_denot E3 (SAlu ALU_ADD (SOff 9 0) (SOff 35 0)))) in Hbr.
all: rewrite ADD, unsigned_lit_small in Hbr by lia.
(* to `bgeu s0, -16` 0x82b80 *)
all: fsw_aj_runU tbl_own_ok HS7 HJ HARU.
all: try (apply A3; lazymatch goal with |- skeleton _ = skeleton _ => vm_compute; reflexivity end).
all: pose proof HF as HF2; clear HFr HG HF.
all: eapply SRr_sym_branch with (c := BC_GEU) (a := SOff 8 0) (b := SLit 18446744073709551600) (1 := HS7).
all: intros Hu HS8; clear HS7.
all: rewrite branch_geu_U, (U_off E3 8 0 ltac:(rewrite U3_8; unfold M64, HEAD in *; lia)), U3_8,
       (U_lit E3 18446744073709551600 ltac:(lia)) in Hu.
(* taken: the UBSan trap needs b >= 2^64 - 16 *)
all: try (exfalso; apply negb_true_iff, Z.ltb_ge in Hu; unfold HEAD in *; lia).
(* not taken: a0 = b + 16, epilogue; stops at ret 0x82b98 *)
all: fsw_aj_runU tbl_own_ok HS8 HJ HARU.
all: try (apply A3; lazymatch goal with |- skeleton _ = skeleton _ => vm_compute; reflexivity end).
all: pose proof HF as HF3; clear HFr HG HF.
all: pose proof HS8 as HS8c; destruct HS8c as (_ & _ & _ & _ & _ & _ & _ & HMf & _).
all: rreg HS8 (1%bv : bv 5) R1f; rreg HS8 (10%bv : bv 5) R10f.
all: rewrite ?wvb_collapse in HJ, HARU.
all: unfold apost_baseU.
all: eapply (fsw_retU B tbl_own tbl_own_ok).
all: first
  [ solve [exact HS8] | solve [exact HJ] | solve [exact HARU]
  | solve [lazymatch goal with |- ss_resv _ = None => reflexivity end]
  | solve [lazymatch goal with |- clookup _ _ = Some _ => vm_compute; reflexivity end]
  | solve [lazymatch goal with |- v_jalr _ _ = _ =>
             rewrite R1f, ?fsw_SOff0, E3_37; exact Hra end]
  | solve [lazymatch goal with |- aregs_preserved _ _ =>
             apply (fsw_preserved _ E3 _ _ regs ow_expect HS8);
             [ lazymatch goal with |- forallb _ _ = true => vm_compute; reflexivity end
             | intros r Hr; cbv [CALLEE_SAVED In] in Hr;
               repeat (destruct Hr as [<-|Hr]); [..|destruct Hr];
               lazymatch goal with |- sv_denot _ (ow_expect ?q) = _ =>
                 let e := eval vm_compute in (ow_expect q) in change (ow_expect q) with e end;
               first
               [ apply fsw_sp_back; exact E3_2
               | rewrite fsw_SOff0; first [exact E3_38 | exact E3_39]
               | rewrite fsw_SOff0; subst E3;
                 lazymatch goal with |- ew _ ?k = YK11.getr _ ?q =>
                   rewrite (ew_Ereg_nat regs3 _ k q eq_refl);
                   let z := eval vm_compute in (bv_unsigned q) in
                   pose proof (Hkept z ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hk;
                   exact Hk end ] ] end]
  | idtac ].
(* left: the post Q of each arm *)
all: intros mat2; cbv beta.
all: split; [apply bv_eq; rewrite R10f; rewrite ?denot_SOff, ?U3_8; unfold w64, HEAD; rewrite ?unsigned_lit_small by lia;
             first [reflexivity | lia | (apply zcanon_id; unfold M64; lia)]|].
all: split; [reflexivity|].
all: split; [exact FH2|].
all: split; [unfold fs_rblock; rewrite Z.add_simpl_r; split; [exact Hin|];
             split; [unfold HEAD; rewrite Z.add_mod, Hb16 by lia; reflexivity|]; split; [lia|];
             apply (ow_val_mem_frame E3 _ (w_H W) _ _ b 8 n HF3);
             [ apply NW; lazymatch goal with |- skeleton _ = skeleton _ => vm_compute; reflexivity end
             | unfold HEAD in *; lia | unfold HEAD in *; lia |];
             apply (ow_val_mem_frame E3 _ (w_H W) _ _ b 8 n HF2);
             [ apply NW; lazymatch goal with |- skeleton _ = skeleton _ => vm_compute; reflexivity end
             | unfold HEAD in *; lia | unfold HEAD in *; lia |];
             apply (ow_val_mem_frame E3 _ (w_H W) mem3 _ b 8 n HF1);
             [ apply NW; reflexivity | unfold HEAD in *; lia | unfold HEAD in *; lia | exact Hval ]|].
all: split; [exact (fsw_block_body_addressable B ly S (U ++ [(b, HEAD)]) W _ _ b (n + HEAD) (b + HEAD) n HARU FH2 Hin
               ltac:(unfold HEAD; lia) ltac:(lia) ltac:(rewrite Hrq; unfold HEAD; lia))|].
- (* bgeu taken: peak >= live + n, g_peak kept *)
  rewrite Z.max_l by (apply negb_true_iff, Z.ltb_ge in Hbr; lia).
  apply (fs_glob_of_TS E3 W _ _ (live + n) peak cnt fail (SAlu ALU_ADD (SOff 9 0) (SOff 35 0)) (SOff 36 0)
    (SOff 33 0) (SOff 34 0) HMf).
  all: first
    [ solve [lazymatch goal with |- fs_pstat_find _ _ = Some _ => vm_compute; reflexivity end]
    | solve [exact ADD]
    | solve [rewrite fsw_SOff0; exact (EX3 4%nat _ eq_refl)]
    | solve [rewrite fsw_SOff0; exact (EX3 1%nat _ eq_refl)]
    | solve [rewrite fsw_SOff0; exact (EX3 2%nat _ eq_refl)]
    | solve [apply negb_true_iff, Z.ltb_ge in Hbr; lia]
    | solve [lia] ].
- (* bgeu not taken: peak < live + n, g_peak := live + n *)
  rewrite Z.max_r by (apply negb_false_iff, Z.ltb_lt in Hbr; lia).
  apply (fs_glob_of_TS E3 W _ _ (live + n) (live + n) cnt fail (SAlu ALU_ADD (SOff 9 0) (SOff 35 0))
    (SAlu ALU_ADD (SOff 9 0) (SOff 35 0)) (SOff 33 0) (SOff 34 0) HMf).
  all: first
    [ solve [lazymatch goal with |- fs_pstat_find _ _ = Some _ => vm_compute; reflexivity end]
    | solve [exact ADD]
    | solve [rewrite fsw_SOff0; exact (EX3 1%nat _ eq_refl)]
    | solve [rewrite fsw_SOff0; exact (EX3 2%nat _ eq_refl)]
    | solve [lia] ].
Qed.

(* ---- own_spec, given the stack the poison call needs (ESTACK below the call's sp = sp0 - 32) ---- *)
Lemma own_walk : ESTACK + 32 <= STK_own -> @own_spec fx rc SK tfibsegs B.
Proof.
intros HSTK. unfold own_spec.
intros ly S U W regs mem md ch b n live peak cnt fail HPRE FH H10 H11 Hin Hnin Hb16 Hb4096 Hbtop Hn1 Hn2 Hra0 HGL Hlv.
pose proof HPRE as (HAP & HRO).
pose proof (fsw_ARU B STK_own ly S U W regs mem md ch HAP) as HARU.
pose proof HAP as (HAN & _ & _).
pose proof HAN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof HGL as (_ & _ & _ & _ & Hlp & Hp64 & Hc64 & Hf64).
pose proof (fsw_sp B STK_own ly S U W regs mem md ch HAP) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _ & C3 & _). pose proof alloc_ceiling_val as AC.
assert (HE : ESTACK = 4096) by reflexivity.
assert (Hn64 : 0 <= n < 2 ^ 64) by (unfold MALLOC_MAX, HEAD in *; lia).
assert (Hrq : req_size (n + 16) = n + 16) by (unfold req_size; destruct (Z.eqb_spec (n + 16) 0); lia).
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md b (n + 16) HAR Hin) as (_ & _ & Hbceil & Happ & _).
set (E := Ereg regs (fs_extraT ++ fs_pstat_xs cnt fail live peak)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E10 : bv_unsigned (ew E 10) = b)
  by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), H10; unfold w64; apply unsigned_lit_small; unfold HEAD in *; lia).
assert (E11 : bv_unsigned (ew E 11) = n)
  by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl), H11; unfold w64; apply unsigned_lit_small; lia).
assert (EX : forall j w, nth j (fs_extraT ++ fs_pstat_xs cnt fail live peak) (Z_to_bv 64 0) = w -> ew E (32 + j) = w)
  by (intros j w Hw; subst E; rewrite ew_Ereg_extra; exact Hw).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by exact (EX 0%nat (Z_to_bv 64 SHADOW_OFF) eq_refl).
assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF) by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
(* the head is apart from U, the image cells and the statics *)
assert (DJ : Forall (zdisjoint (b, 16)) U)
  by (apply Forall_forall; exact (ow_head_disjoint ly S U W (unpoison U mem) md b (n + 16) HAR FH Hin Hnin
        ltac:(rewrite Hrq; lia))).
destruct (fs_head_shadow0 B ly S U W mem md b (n + 16) HARU Hin ltac:(rewrite Hrq; lia) DJ) as [Z0 Z1].
assert (Himg : forall g, (forall x, g <= x < g + 8 -> in_img tfibsegs x) -> b + 8 <= g \/ g + 8 <= b)
  by (intros g Hg; exact (fs_head_img_apart B ly S W (unpoison U mem) md b (n + 16) b g 8 HAR Hin
        ltac:(lia) ltac:(rewrite Hrq; lia) ltac:(lia) Hg)).
pose proof (Himg 0x9fc10 (fun x Hx => ow_cells_img x (ex_intro _ (0x9fc10, 0x9fc18) (conj (or_introl eq_refl) Hx)))) as I1.
pose proof (Himg 0xa8438 (fun x Hx => ow_cells_img x (ex_intro _ (0xa8438, 0xa8440) (conj (or_intror (or_introl eq_refl)) Hx)))) as I2.
assert (IS : forall g, In (g, g + 8) FS_PSTAT_FP -> b + 8 <= g \/ g + 8 <= b)
  by (intros g Hg; apply Himg; intros x Hx; exact (fs_pstat_img x (inFP_FS_PSTAT_FP g Hg x Hx))).
pose proof (IS G_FAIL ltac:(vm_compute; tauto)) as I3. pose proof (IS G_LIVE ltac:(vm_compute; tauto)) as I4.
pose proof (IS G_PEAK ltac:(vm_compute; tauto)) as I5. pose proof (IS G_COUNT ltac:(vm_compute; tauto)) as I6.
(* ---- entry: the frame, the shadow-base cells, the four statics and the head ---- *)
assert (Hrs : Forall (region_ok tfibsegs E (mrestrict (w_H W) mem)) ow_rs).
{ unfold ow_rs. apply Forall_app. split.
  - exact (fs_pstat_regions_ok W regs mem live peak cnt fail HGL).
  - constructor; [|constructor].
    apply (fs_head_region_ok B ly S U W mem md E 10 b 8 [] b (n + 16) HARU Hin);
      first [solve [exact E10] | solve [rewrite Hrq; lia] | solve [constructor] | solve [lia]]. }
assert (Hdj : pairwise_disjoint E (fsT_regions_args 32 ow_rs)).
{ apply pairwise_disjoint_of_extents.
  unfold fsT_regions_args, fsT_regions, ow_rs, fs_pstat_regions, fs_got_region, fs_bcell_region, fstk, fs_pstat_region,
    fs_head_region, extent_of_region.
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite Usp, E10.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address,
    G_COUNT, G_FAIL, G_LIVE, G_PEAK in *.
  cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia | lia]. }
assert (Hgf : atoms_ok E ow_gf).
{ unfold ow_gf. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E10.
  repeat split; first [solve [exact I] | solve [change (2 ^ 4) with 16; exact Hb16] | solve [lia]]. }
pose proof (fsw_entryT_argsX B STK_own 32 ly S U W regs mem md ch A_own ow_rs ow_gf (fs_pstat_xs cnt fail live peak)
  FS_GOT_SHADOW FS_SHADOW_CELL HAP ltac:(lia) ltac:(vm_compute; reflexivity) Hrs Hdj Hgf) as HS.
fold E in HS.
pose proof (ajournal_init tfibsegs B STK_own (FS_PSTAT_FP ++ [(b, b + 8)]) ly S W regs (unpoison U mem) md ch
  HAN) as HJ.
unfold cfg_at. change (w64 A_own) with (Z_to_bv 64 A_own).
(* ---- 0x82acc..0x82b54: frame, saves, the two inline checks, the eight `sb`; stops at the poison entry ---- *)
assert (SHOK : sh_ok tfibsegs fs_Bx [YCbn.mkSHE 10 0 16] E (mrestrict (w_H W) mem)).
{ constructor; [|constructor].
  apply (fs_head_shent fs_Bx E W mem 10 b).
  all: first
    [ solve [exact Z0] | solve [exact Z1]
    | solve [lazymatch goal with |- YP0e.U _ (SOff 10 0) = _ => rewrite U_SOff, E10, Z.add_0_r; apply zcanon_id; unfold M64; lia end]
    | solve [lazymatch goal with |- YP0e.U _ fs_Bx = _ =>
               unfold fs_Bx; rewrite U_SOff, U32, Z.add_0_r; apply zcanon_id; unfold M64, SHADOW_OFF; lia end]
    | solve [lazymatch goal with |- _ mod 8 = 0 =>
               apply Z.mod_divide; [lia|]; apply Z.mod_divide in Hb16; [|lia]; destruct Hb16 as [q Hq]; exists (2 * q); lia end]
    | solve [lazymatch goal with |- in_app _ _ => apply (in_app_sub b (req_size (n + 16)) b 16 Happ); rewrite ?Hrq; lia end] ]. }
fsw_aj_run_tokU tbl_own_ok HS HJ HARU SHOK fs_Bspan.
{ apply (ow_awr E A_own STK_own (spZ regs) b (n + 16) ow_gf).
  all: first
    [ solve [exact Usp] | solve [lia] | solve [exact E10] | solve [exact (ow_fp_l _)]
    | solve [intros a Ha; apply ow_fp_head; lia] | solve [exact Hin] | solve [rewrite Hrq; lia] ]. }
(* ---- the poison call: FSW_poison_conv.fsw_poison16_atU over fs_poison16; the head is consed at the front, the
   statement appends it (Permutation_cons_append) ---- *)
pose proof HS as HSc. destruct HSc as (_ & _ & _ & _ & _ & _ & _ & HM5 & _).
pose proof HM5 as HM5c. destruct HM5c as (_ & HR5 & _). cbn [ss_mem] in HR5.
pose proof (Forall_inv HR5) as (_ & _ & _ & HCK5). cbn [YP09.r_chunks YP09.r_base base_val] in HCK5. rewrite Usp in HCK5.
pose proof HR5 as HRl. do 7 apply Forall_inv_tail in HRl.
pose proof (Forall_inv HRl) as (_ & _ & _ & HHC). cbn [YP09.r_chunks YP09.r_base base_val] in HHC. rewrite E10 in HHC.
clear HFr HG.
rewrite ?wvb_collapse in HJ, HARU |- *.
assert (Hval0 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) b 8 n) by exact (ow_head_val E _ b n E11 Hn64 HHC).
assert (T1 : getr (ms_regs ms) 1 = Z_to_bv 64 A_own_ra_po)
  by exact (fsw_reg_lit _ E _ ms 1%bv 535388 HS ltac:(vm_compute; reflexivity) ltac:(lia)).
assert (T11 : getr (ms_regs ms) 11 = w64 16)
  by exact (fsw_reg_lit _ E _ ms 11%bv 16 HS ltac:(vm_compute; reflexivity) ltac:(lia)).
assert (T10 : getr (ms_regs ms) 10 = w64 b).
{ rewrite (fsw_reg_atom (w_H W) regs (fs_extraT ++ fs_pstat_xs cnt fail live peak) _ ms 10%bv 10%bv 10 HS
    ltac:(vm_compute; reflexivity) eq_refl). exact H10. }
assert (T8 : getr (ms_regs ms) 8 = w64 b).
{ rewrite (fsw_reg_atom (w_H W) regs (fs_extraT ++ fs_pstat_xs cnt fail live peak) _ ms 8%bv 10%bv 10 HS
    ltac:(vm_compute; reflexivity) eq_refl). exact H10. }
assert (T9 : getr (ms_regs ms) 9 = w64 n).
{ rewrite (fsw_reg_atom (w_H W) regs (fs_extraT ++ fs_pstat_xs cnt fail live peak) _ ms 9%bv 11%bv 11 HS
    ltac:(vm_compute; reflexivity) eq_refl). exact H11. }
assert (T3 : getr (ms_regs ms) 3 = w64 (as_gp B)).
{ rewrite (fsw_reg_atom (w_H W) regs (fs_extraT ++ fs_pstat_xs cnt fail live peak) _ ms 3%bv 3%bv 3 HS
    ltac:(vm_compute; reflexivity) eq_refl). exact Hgp. }
assert (T4 : getr (ms_regs ms) 4 = w64 (as_tp B)).
{ rewrite (fsw_reg_atom (w_H W) regs (fs_extraT ++ fs_pstat_xs cnt fail live peak) _ ms 4%bv 4%bv 4 HS
    ltac:(vm_compute; reflexivity) eq_refl). exact Htp. }
assert (T2 : spZ (ms_regs ms) = spZ regs + -32).
{ unfold spZ at 1.
  exact (fsw_reg_off _ E _ ms 2%bv 2 (-32) (spZ regs) HS ltac:(vm_compute; reflexivity) Usp
    ltac:(unfold spZ in *; pose proof (bv_unsigned_in_range _ (getr regs 2)); lia)). }
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms HS eq_refl) as Hshape.
rewrite Hshape.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdg) ?Qg =>
  change (SRr tfibsegs W (cfg_at tfibsegs PC_poison (ms_regs ms) (ms_mem ms) mdg) Qg) end.
eapply SRr_bind.
{ apply (fsw_poison16_atU B PC_poison FS_POISON STK_own (spZ regs) (FS_PSTAT_FP ++ [(b, b + 8)]) ly S W
    (unpoison U mem) md [] ly S U (U ++ [(b, 16)]) W (ms_mem ms) _ 0 (ms_regs ms) (-32) b b (n + 16) HJ HARU).
  all: first
    [ solve [exact T2] | solve [exact T3] | solve [exact T4] | solve [exact T10] | solve [exact T11] | solve [exact Hin]
    | solve [lazymatch goal with |- _ mod _ = _ => reflexivity end]
    | solve [lazymatch goal with |- ESTACK - _ <= _ => lia end]
    | solve [lazymatch goal with |- YK0s.ret_ok _ =>
               rewrite T1; apply ret_ok_even; rewrite unsigned_lit_small by (unfold A_own_ra_po; lia); reflexivity end]
    | solve [apply (upoison_ok_new_head B ly S U b (n + 16) (proj1 (proj2 HARU)) Hin);
             first
             [ solve [lazymatch goal with |- _ mod 8 = 0 =>
                        apply Z.mod_divide; [lia|]; apply Z.mod_divide in Hb16; [|lia]; destruct Hb16 as [q Hq];
                        exists (2 * q); lia end]
             | solve [lazymatch goal with |- 16 <= 8 * (_ / 8) =>
                        rewrite Hrq; assert (2 <= (n + 16) / 8) by (apply Z.div_le_lower_bound; lia); lia end]
             | solve [intros r Hr; exact (proj1 (Forall_forall _ _) DJ r Hr)] ]]
    | solve [lazymatch goal with |- Permutation _ _ => apply Permutation_cons_append end]
    | solve [lazymatch goal with |- _ + _ < _ + req_size _ => rewrite Hrq; lia end]
    | solve [lazymatch goal with |- _ <= _ => lia end] ]. }
intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HARU4 & HP3 & HFK & HAK).
rewrite T1.
(* ---- resume at 0x82b5c with the frame and the statics (FSW_rres.fsw_resume_after_rtU_args), then ow_tail ---- *)
set (E3 := Ereg regs3 (fs_extraT ++ ow_xs regs cnt fail live peak)).
assert (Q2 : getr regs3 2 = getr (ms_regs ms) 2) by exact (HP3 2 ltac:(unfold acallee_saved; lia)).
assert (Q8 : getr regs3 8 = getr (ms_regs ms) 8) by exact (HP3 8 ltac:(unfold acallee_saved; lia)).
assert (Q9 : getr regs3 9 = getr (ms_regs ms) 9) by exact (HP3 9 ltac:(unfold acallee_saved; lia)).
assert (E3_2 : bv_unsigned (ew E3 2) = spZ regs - 32)
  by (subst E3; rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl), Q2; unfold spZ in T2 |- *; lia).
assert (EX3 : forall j w, nth j (fs_extraT ++ ow_xs regs cnt fail live peak) (Z_to_bv 64 0) = w -> ew E3 (32 + j) = w)
  by (intros j w Hw; subst E3; rewrite ew_Ereg_extra; exact Hw).
(* the statics at the poison call, read back from the symbolic memory *)
assert (G0 : fs_glob tfibsegs W (ms_mem ms) live peak cnt fail).
{ apply (fs_glob_of_TS E W _ _ live peak cnt fail (SOff 35 0) (SOff 36 0) (SOff 33 0) (SOff 34 0) HM5).
  all: first
    [ solve [lazymatch goal with |- fs_pstat_find _ _ = Some _ => vm_compute; reflexivity end]
    | solve [rewrite fsw_SOff0; exact (EX 3%nat (Z_to_bv 64 live) eq_refl)]
    | solve [rewrite fsw_SOff0; exact (EX 4%nat (Z_to_bv 64 peak) eq_refl)]
    | solve [rewrite fsw_SOff0; exact (EX 1%nat (Z_to_bv 64 cnt) eq_refl)]
    | solve [rewrite fsw_SOff0; exact (EX 2%nat (Z_to_bv 64 fail) eq_refl)]
    | solve [lia] ]. }
(* ... kept across the call (application bytes far below the call's stack window) *)
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> a < SHADOW_OFF \/ kHighMemBeg <= a -> a + 1 <= spZ regs - STK_own ->
  mbyte tfibsegs (mrestrict (w_H W) mem3) a = mbyte tfibsegs (mrestrict (w_H W) (ms_mem ms)) a).
{ intros a Ha Happ' Hlo.
  apply (ow_keep_app ly S U (U ++ [(b, 16)]) W (ms_mem ms) mem3 _ md3 (spZ (ms_regs ms)) a HARU HARU4 HAK Ha Happ').
  unfold PO_WIN. rewrite T2. lia. }
assert (G3 : fs_glob tfibsegs W mem3 live peak cnt fail).
{ apply (ow_glob_keep W W (ms_mem ms) mem3 live peak cnt fail G0). intros a Ha.
  pose proof (ow_pstat_bounds a Ha) as Hb.
  apply KEEP; unfold G_FAIL, G_LIVE, G_PEAK, G_COUNT, SHADOW_OFF in *; lia. }
assert (Hval3 : val_mem tfibsegs (mrestrict (w_H W) mem3) b 8 n).
{ intros k Hk. rewrite KEEP; [exact (Hval0 k Hk) | | |].
  all: rewrite ?Hrq in Happ; unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, ASAN_CEIL in *;
       rewrite ?Hrq in Hbceil; unfold ASAN_CEIL in *; lia. }
assert (Hck3 : Forall (YP09.chunk_ok tfibsegs E3 (mrestrict (w_H W) (ms_mem ms)) (spZ regs - 32)) ow_cs).
{ unfold ow_cs.
  pose proof HCK5 as H0.
  pose proof (Forall_inv H0) as K39. apply Forall_inv_tail in H0.
  pose proof (Forall_inv H0) as K38. apply Forall_inv_tail in H0.
  pose proof (Forall_inv H0) as K37.
  assert (D : forall (k : nat) (j : nat) (r : bv 5), nth j (fs_extraT ++ ow_xs regs cnt fail live peak) (Z_to_bv 64 0) = getr regs r ->
    Z.of_nat k = bv_unsigned r -> sv_denot E (SOff k 0) = sv_denot E3 (SOff (32 + j) 0)).
  { intros k j r Hn Hk. rewrite !fsw_SOff0. rewrite (EX3 j _ Hn). subst E. exact (ew_Ereg_nat regs _ k r Hk). }
  repeat constructor.
  - apply (ow_chunk_move E E3 _ (spZ regs) (spZ regs - 32) (-24) 8 8 (SOff 9 0) (SOff 39 0));
      [lia | exact (D 9%nat 7%nat 9%bv eq_refl eq_refl) | exact K39].
  - apply (ow_chunk_move E E3 _ (spZ regs) (spZ regs - 32) (-16) 16 8 (SOff 8 0) (SOff 38 0));
      [lia | exact (D 8%nat 6%nat 8%bv eq_refl eq_refl) | exact K38].
  - apply (ow_chunk_move E E3 _ (spZ regs) (spZ regs - 32) (-8) 24 8 (SOff 1 0) (SOff 37 0));
      [lia | exact (D 1%nat 5%nat 1%bv eq_refl eq_refl) | exact K37]. }
assert (Hpdj3 : pairwise_disjoint E3 (fsT_ret_regions 32 ow_cs fs_pstat_regions)).
{ apply pairwise_disjoint_of_extents.
  unfold fsT_ret_regions, fs_pstat_regions, fs_got_region, fs_bcell_region, fstk_ret, fs_pstat_region, extent_of_region.
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E3_2.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address,
    G_COUNT, G_FAIL, G_LIVE, G_PEAK in *.
  cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia | lia]. }
pose proof (fsw_resume_after_rtU_args B STK_own (spZ regs) (FS_PSTAT_FP ++ [(b, b + 8)]) ly S W
  (unpoison U mem) md [] ly S (U ++ [(b, 16)]) W mem3 md3 0 (ms_regs ms) regs3 (ms_mem ms) 32
  (ow_xs regs cnt fail live peak) ow_cs fs_pstat_regions [] A_own_ra_po FS_GOT_SHADOW FS_SHADOW_CELL HJ3 HARU4 HP3
  ltac:(rewrite T2; lia) ltac:(lia) ltac:(lia) eq_refl ltac:(vm_compute; reflexivity)
  ltac:(unfold ow_cs; repeat constructor; cbn; lia) Hck3
  ltac:(intros a Ha; apply HFK; rewrite T2; lia)
  (ow_pstat_ok W regs3 mem3 live peak cnt fail [getr regs 1; getr regs 8; getr regs 9] G3)
  Hpdj3 ltac:(first [exact I | constructor])) as HS6.
apply (ow_tail ly S U W regs mem md b n live peak cnt fail regs3 mem3 md3 HS6 HJ3 HARU4).
all: first
  [ solve [exact Hin] | solve [exact FH] | solve [exact Hval3] | solve [exact IS] | solve [exact Hra]
  | solve [exact Hb16] | solve [exact Hn1] | solve [exact Hlv] | solve [exact Hb4096] | solve [exact Hbtop]
  | solve [lazymatch goal with |- spZ _ = _ => unfold spZ; rewrite Q2; unfold spZ in T2; lia end]
  | solve [lazymatch goal with |- getr _ 8 = _ => rewrite Q8; exact T8 end]
  | solve [lazymatch goal with |- getr _ 9 = _ => rewrite Q9; exact T9 end]
  | solve [lazymatch goal with |- forall r, acallee_saved r -> _ =>
      intros r Hcs H2 H8 H9; rewrite (HP3 r Hcs);
      assert (Hr : In r [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]) by (cbn; unfold acallee_saved in Hcs; lia);
      repeat (destruct Hr as [<- | Hr]); [..| destruct Hr];
      lazymatch goal with |- getr _ (Z_to_bv 5 ?z) = _ =>
        let k := eval vm_compute in (Z.to_nat z) in
        exact (fsw_reg_atom (w_H W) regs (fs_extraT ++ fs_pstat_xs cnt fail live peak) _ ms (Z_to_bv 5 z) (Z_to_bv 5 z) k HS
                 ltac:(vm_compute; reflexivity) eq_refl) end end]
  | solve [lazymatch goal with |- _ + (_ + HEAD) <= _ => rewrite ?Hrq in Hbceil; unfold HEAD in *; lia end]
  | solve [lia] ].
Qed.

End o.

(* own_spec of lib/B/FSH_Fn_alloc.v: STK_own = FRAME_own + zmaxl [STK_RT_POISON] = 32 + ESTACK (S0 834df0ca5d9's
   STK_RT_POISON := ESTACK) gives own_walk's stack premise *)
Theorem own_holds : forall {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} (B : asyms),
  fs_img_facts tfibsegs B -> FsShadowSyms B -> fs_poison16 tfibsegs B -> @own_spec fx rc SK tfibsegs B.
Proof.
intros fx rc SK B IMG SHS FS_POISON.
exact (own_walk B IMG SHS FS_POISON ltac:(apply Z.leb_le; vm_compute; reflexivity)).
Qed.
