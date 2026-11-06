(* proves function fuzz_realloc, segment SEG-C (A 0x829e8), as fsr_segC : forall B, fsr_segC_stmt B against a Theorem Labs lane's frozen FSW_realloc_pn.v (reuse search: ossv proof index v5, built 2026-10-29T04:26:29Z from main@f4cc67298b7 ossv/recipes@e5e7eba2cc0 ossv/candidates@ee89628c997 release/pau-projects-recipes@b6a0088adcb, every branch is where the index read it / `proof-index fuzz_realloc 0x82ba8 0x82bbc 0x82c74 0x82b34 0x54894`, exit 1: none for the ASan image; two named working branches: none; CONFIRM x2, (internal path)) *)
(* SEG-C: from fsr_at_realloc (the `jal __wrap_realloc` at 0x82b30, pc PC_realloc) through the realloc call
   (FSW_realloc.fsw_aj_reallocU), the resume at A_fuzz_realloc_ra = 0x82b34 (FSW_rres.fsw_resume_after_rtU_args_chunks),
   `beqz a0` (the NULL arm is dead: 4096 <= a0), own()'s two inline shadow checks and the eight `sb` of n into the new
   head (token run, FSW_K.fsw_aj_run_tokU with Bx = s4 = atom 20, SH = [mkSHE 10 0 16], FSW_head), to the fetch of
   0x54894 (`jal __asan_poison_memory_region`, pc PC_poison), i.e. fsr_at_poison.
   Kit rules R1 (per-goal `first [solve ..]`, computing alternatives guarded by goal shape) and R2 are followed. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YM05 YG00 YG0a YG01 YG0l YG0d YG0f YG0n YG05 YG08 YG0q YCbq YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSH_Fn_alloc FSH_ReallocModel FSupoisonRealloc
FSpoisonS FSW_K FSW_ret FSW_rres FSW_statics FSW_statics_awr FSW_head FSW_poison_conv FSW_K3 FSW_fuzz_realloc_tbl
FSW_realloc FSW_realloc_pn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Helpers (prefix fsrC_).                                                                                           *)
(* ---------------------------------------------------------------------------------------------------------------- *)

(* unpoisoning a SUBSET of U on top of unpoison U changes nothing: the segment's journal runs over `unpoison U mem`
   while the call step reads it as `unpoison (U1 ++ U2) (unpoison U mem)` *)
Lemma fsrC_unpoison_sub : forall (U U' : list (Z * Z)) (mem : word -> option byte),
  (forall r, In r U' -> In r U) -> unpoison U' (unpoison U mem) = unpoison U mem.
Proof.
intros U U' mem HS. apply functional_extensionality. intros w.
destruct (in_ush U' (bv_unsigned w)) eqn:E1.
- rewrite (unpoison_in U' (unpoison U mem) w E1). symmetry. apply unpoison_in.
  apply in_ush_spec. apply in_ush_spec in E1 as (r & Hr & Hrng). exists r. split; [exact (HS r Hr) | exact Hrng].
- rewrite (unpoison_out U' (unpoison U mem) w E1). reflexivity.
Qed.

(* the two shadow-base cells of fs.asan are image bytes (FSW_statics.fs_pstat_img's method) *)
Definition fsrC_cells : list (Z * Z) :=
  [(tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_GOT_asan_shadow_memory_dynamic_address + 8);
   (tfib_D_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address + 8)].
Lemma fsrC_cells_img : forall a, inFP fsrC_cells a -> in_img tfibsegs a.
Proof.
intros a (r & Hr & Ha).
assert (Hb : forallb (fun r : Z * Z => existsb (fun s => (Z.of_N (seg_base s) <=? fst r) &&
    (snd r <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs) fsrC_cells = true) by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) Hb r Hr) as H. cbv beta in H.
apply existsb_exists in H as (s & Hs & Hss). apply andb_prop in Hss as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists s. split; [exact Hs | lia].
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.

(* a value held HIGH (at or above kHighMemBeg: the caller's frame) is kept across a call that keeps its aview *)
Lemma fsrC_val_keep : forall B ly S ly' S' U (W W' : world tfibsegs) mem mem' md md' a (j : nat) v,
  ARU tfibsegs B ly S U W mem md -> ARU tfibsegs B ly' S' U W' mem' md' ->
  (forall x, a <= x < a + Z.of_nat j ->
     aview tfibsegs (w_H W') (unpoison U mem') x = aview tfibsegs (w_H W) (unpoison U mem) x) ->
  kHighMemBeg <= a -> a + Z.of_nat j < 2 ^ 64 ->
  val_mem tfibsegs (mrestrict (w_H W) mem) a j v -> val_mem tfibsegs (mrestrict (w_H W') mem') a j v.
Proof.
intros B ly S ly' S' U W W' mem mem' md md' a j v H1 H2 HV Hlo Hhi Hv i Hi.
rewrite <- (Hv i Hi). apply fsr_mbyte_of_aview2.
rewrite <- (fsw_aview_unpoison_high B ly' S' U W' mem' md' (a + Z.of_nat i) H2 ltac:(lia)).
rewrite <- (fsw_aview_unpoison_high B ly S U W mem md (a + Z.of_nat i) H1 ltac:(lia)).
exact (HV (a + Z.of_nat i) ltac:(lia)).
Qed.

(* bytes no region of a run writes keep their value across the run (frame_of) *)
Lemma fsrC_val_frame : forall E rs (H : word -> bool) (m m' : word -> option byte) a (j : nat) v,
  frame_of E rs m m' -> (forall i, (i < j)%nat -> ~ in_wrange E rs (a + Z.of_nat i)) ->
  0 <= a -> a + Z.of_nat j <= 2 ^ 64 ->
  val_mem tfibsegs (mrestrict H m) a j v -> val_mem tfibsegs (mrestrict H m') a j v.
Proof.
intros E rs H m m' a j v HF Hn Ha Hj Hv i Hi. rewrite <- (Hv i Hi).
apply (mbyte_of_aview tfibsegs). apply (aview_at tfibsegs). apply HF.
rewrite (wz (a + Z.of_nat i) ltac:(lia)). exact (Hn i Hi).
Qed.

(* fs_glob is kept by a run that writes no byte of the four statics *)
Lemma fsrC_glob_frame : forall E rs (W : world tfibsegs) (m m' : word -> option byte) live peak cnt fail,
  frame_of E rs m m' ->
  (forall a, inFP FS_PSTAT_FP a -> ~ in_wrange E rs a) ->
  fs_glob tfibsegs W m live peak cnt fail -> fs_glob tfibsegs W m' live peak cnt fail.
Proof.
intros E rs W m m' live peak cnt fail HF HN (G1 & G2 & G3 & G4 & GR).
assert (V : forall g v, In (g, g + 8) FS_PSTAT_FP -> 0 <= g -> g + 8 <= 2 ^ 64 ->
  val_mem tfibsegs (mrestrict (w_H W) m) g 8 v -> val_mem tfibsegs (mrestrict (w_H W) m') g 8 v).
{ intros g v Hg Hg0 Hg1 Hv.
  apply (fsrC_val_frame E rs (w_H W) m m' g 8 v HF);
    [ intros i Hi; apply HN; exists (g, g + 8); split; [exact Hg | cbn [fst snd]; lia]
    | exact Hg0 | change (Z.of_nat 8) with 8; lia | exact Hv ]. }
split; [apply (V G_LIVE live); [vm_compute; tauto | unfold G_LIVE; lia | unfold G_LIVE; lia | exact G1]|].
split; [apply (V G_PEAK peak); [vm_compute; tauto | unfold G_PEAK; lia | unfold G_PEAK; lia | exact G2]|].
split; [apply (V G_COUNT cnt); [vm_compute; tauto | unfold G_COUNT; lia | unfold G_COUNT; lia | exact G3]|].
split; [apply (V G_FAIL fail); [vm_compute; tauto | unfold G_FAIL; lia | unfold G_FAIL; lia | exact G4]|].
exact GR.
Qed.

(* where the four statics live (FS_PSTAT_FP's four 8-byte ranges) *)
Lemma fsrC_pstat_bounds : forall a, inFP FS_PSTAT_FP a ->
  (G_FAIL <= a < G_FAIL + 8) \/ (G_LIVE <= a < G_LIVE + 8) \/ (G_PEAK <= a < G_PEAK + 8) \/
  (G_COUNT <= a < G_COUNT + 8).
Proof.
intros a (r & Hr & Ha). unfold FS_PSTAT_FP in Hr. unfold G_FAIL, G_LIVE, G_PEAK, G_COUNT.
repeat (destruct Hr as [<- | Hr]; [cbn [fst snd] in Ha; lia|]). destruct Hr.
Qed.

(* a byte is its value mod 256 *)
Lemma fsrC_bv8_mod : forall z, Z_to_bv 8 (z mod 256) = Z_to_bv 8 z.
Proof.
intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* the value own()'s `srli s0, s` stores: the 64-bit value of atom 8 shifted right *)
Lemma fsrC_srl_val : forall E v s, ew E 8 = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= s < 64 -> Z.land s 63 = s ->
  bv_unsigned (sv_denot E (SAlu ALU_SRL (SOff 8 0) (SLit s))) = Z.shiftr v s.
Proof.
intros E v s Hv Hr Hs Hl.
change (bv_unsigned (sv_denot E (SAlu ALU_SRL (SOff 8 0) (SLit s))))
  with (U E (SAlu ALU_SRL (SOff 8 0) (SLit s))).
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 8 v Hv Hr), (U_lit E s ltac:(lia)), Hl.
rewrite Z.shiftr_div_pow2 by lia.
assert (H1 : 1 <= 2 ^ s) by (change 1 with (2 ^ 0); apply Z.pow_le_mono_r; lia).
apply zcanon_id. unfold M64. split; [apply Z.div_pos; lia|].
apply Z.le_lt_trans with v; [apply Z.div_le_upper_bound; [lia | nia] | lia].
Qed.

(* fs_glob is kept by any memory change that keeps the four statics' bytes *)
Lemma fsrC_glob_mbyte : forall (W W' : world tfibsegs) (m m' : word -> option byte) live peak cnt fail,
  (forall a, inFP FS_PSTAT_FP a ->
     mbyte tfibsegs (mrestrict (w_H W') m') a = mbyte tfibsegs (mrestrict (w_H W) m) a) ->
  fs_glob tfibsegs W m live peak cnt fail -> fs_glob tfibsegs W' m' live peak cnt fail.
Proof.
intros W W' m m' live peak cnt fail KB (G1 & G2 & G3 & G4 & GR).
assert (V : forall g v, In (g, g + 8) FS_PSTAT_FP ->
  val_mem tfibsegs (mrestrict (w_H W) m) g 8 v -> val_mem tfibsegs (mrestrict (w_H W') m') g 8 v).
{ intros g v Hg Hv i Hi. rewrite (KB (g + Z.of_nat i)); [exact (Hv i Hi)|].
  exists (g, g + 8). split; [exact Hg | cbn [fst snd]; lia]. }
split; [apply (V G_LIVE live); [vm_compute; tauto | exact G1]|].
split; [apply (V G_PEAK peak); [vm_compute; tauto | exact G2]|].
split; [apply (V G_COUNT cnt); [vm_compute; tauto | exact G3]|].
split; [apply (V G_FAIL fail); [vm_compute; tauto | exact G4]|].
exact GR.
Qed.

(* fs_glob across an allocator call: the statics are image bytes, no owned static and off errno (fs_img_facts) *)
Lemma fsrC_glob_acall : forall B ly S ly' S' U (W W' : world tfibsegs) mem mem' md md' slo shi Ex
  live peak cnt fail,
  fs_img_facts tfibsegs B ->
  ARU tfibsegs B ly S U W mem md -> ARU tfibsegs B ly' S' U W' mem' md' ->
  acall_kept tfibsegs B ly S W (unpoison U mem) W' (unpoison U mem') slo shi Ex ->
  fs_glob tfibsegs W mem live peak cnt fail -> fs_glob tfibsegs W' mem' live peak cnt fail.
Proof.
intros B ly S ly' S' U W W' mem mem' md md' slo shi Ex live peak cnt fail IMG H1 H2 (_ & _ & HKimg & _) G.
apply (fsrC_glob_mbyte W W' mem mem' live peak cnt fail); [|exact G].
intros a Ha. destruct (proj1 IMG a Ha) as (HnOwn & HnErr).
assert (Hlo : 0 <= a < SHADOW_OFF).
{ destruct (fsrC_pstat_bounds a Ha) as [H|[H|[H|H]]];
    unfold G_FAIL, G_LIVE, G_PEAK, G_COUNT, SHADOW_OFF in *; lia. }
apply fsr_mbyte_of_aview2.
rewrite (aview_at tfibsegs (w_H W') mem' (unpoison U mem') a
  (eq_sym (fs_head_app_view B ly' S' U W' mem' md' a H2 ltac:(unfold SHADOW_OFF in *; lia) ltac:(left; lia)))).
rewrite (aview_at tfibsegs (w_H W) mem (unpoison U mem) a
  (eq_sym (fs_head_app_view B ly S U W mem md a H1 ltac:(unfold SHADOW_OFF in *; lia) ltac:(left; lia)))).
exact (HKimg a (fs_pstat_img a Ha) HnOwn HnErr).
Qed.

(* the resumed state at 0x82b34: the eight saved words of fuzz_realloc's frame as atoms 37..44, the new block's head
   as a writable region based at atom 10 (a0 = s2 = b), and the token run's atom facts (MEASURED: without the Bx atom
   (s4 = atom 20, the shadow base) and the head atom sh_static_ok is false) *)
Definition fsrC_cs : list YP09.chunk :=
  [YP09.mkChunk 0 (CVal 8 (SOff 37 0)); YP09.mkChunk 8 (CVal 8 (SOff 38 0));
   YP09.mkChunk 16 (CVal 8 (SOff 39 0)); YP09.mkChunk 24 (CVal 8 (SOff 40 0));
   YP09.mkChunk 32 (CVal 8 (SOff 41 0)); YP09.mkChunk 40 (CVal 8 (SOff 42 0));
   YP09.mkChunk 48 (CVal 8 (SOff 43 0)); YP09.mkChunk 56 (CVal 8 (SOff 44 0))].
Definition fsrC_rs : list YP09.region := [fs_head_region 10 8 []].
Definition fsrC_gf : list (nat * afact) :=
  [(20%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (10%nat, mkAF 4096 (2 ^ 47 - 32) 4)].

Theorem fsr_segC : forall B, fsr_segC_stmt B.
Proof.
intros B AREALLOC ENV IMG FS_GOT FS_CELL ly S U W regs mem md ch p k n old live peak cnt fail U1 U2 W2 c HPRE HAT.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FR : STK_fuzz_realloc = 18656) by reflexivity.
assert (HD : HEAD = 16) by reflexivity.
assert (HMM : MALLOC_MAX = 2 ^ 28) by reflexivity.
assert (HSO : SHADOW_OFF = 0x7fff8000) by reflexivity.
assert (HAS : ASTACK = 16384) by reflexivity.
pose proof HPRE as (HPREU & FH & H10 & H11 & Hn1 & HnM & HGL & Hlv & Hcn & Hcf & Hp0 & EU & HRB & Hlen & HZ & Hkl & Hev & Hbb).
destruct HAT as (regsT & memT & md2 & Ec & HJ & HARU & T10 & T11 & T1 & Tsp & T8 & T19 & T20 & HKP & HFV & HGL2 & HZT).
pose proof HPREU as (HAP & HRO).
pose proof (fsw_ARU B STK_fuzz_realloc ly S U W regs mem md ch HAP) as HARU0.
pose proof (fsw_sp B STK_fuzz_realloc ly S U W regs mem md ch HAP) as (Hal16 & Hceil & H47 & HSTK0).
pose proof HARU0 as (HAR0 & (HUF & HUPW) & HUPO).
destruct HFV as (V22 & V21 & V20 & V19 & V18 & V9 & V8 & V1).
assert (Hk0 : 0 <= k) by (rewrite <- Hlen; apply Zle_0_nat).
assert (FHU : fs_heads B ly S (U1 ++ (p - HEAD, HEAD) :: U2)) by (rewrite <- EU; exact FH).
assert (PWU : pairwise zdisjoint (U1 ++ (p - HEAD, HEAD) :: U2)) by (rewrite <- EU; exact HUPW).
assert (FH12 : fs_heads B ly S (U1 ++ U2)).
{ intros r Hr. apply FHU. apply in_app_or in Hr as [Hx|Hx]; apply in_or_app; [left; exact Hx | right; right; exact Hx]. }
assert (HNIN : ~ In (p - HEAD, HEAD) (U1 ++ U2)) by (apply (pairwise_head_once U1 U2 (p - HEAD)); exact PWU).
assert (HUout : forall rg, In rg (U1 ++ U2) ->
  fst rg + snd rg <= p - HEAD \/ (p - HEAD) + req_size (k + HEAD) <= fst rg).
{ intros rg Hrg. eapply (ARU_free_outside tfibsegs B).
  all: first [ solve [exact LAWS] | solve [exact HARU] | solve [exact FH12] | solve [exact (proj1 HRB)]
             | solve [exact HNIN] | solve [exact Hrg] ]. }
assert (EUM : unpoison (U1 ++ U2) (unpoison U mem) = unpoison U mem).
{ apply fsrC_unpoison_sub. intros r Hr. rewrite EU.
  apply in_app_or in Hr as [Hx|Hx]; apply in_or_app; [left; exact Hx | right; right; exact Hx]. }
assert (HJ0 : ajournal tfibsegs B STK_fuzz_realloc (spZ regs) (fsr_FPc p k) ly S W
  (unpoison (U1 ++ U2) (unpoison U mem)) md [] ly S W2 (unpoison (U1 ++ U2) memT) md2 0)
  by (rewrite EUM; exact HJ).
rewrite Ec. change (Z_to_bv 64 PC_realloc) with (Z_to_bv 64 FS_AREALLOC_PC_A).
(* ---- the realloc call (FSW_realloc.fsw_aj_reallocU): three ticks, the block swapped, the kept bytes ---- *)
eapply SRr_bind.
{ eapply (fsw_aj_reallocU B ENV AREALLOC W2 regsT memT STK_fuzz_realloc (spZ regs) (fsr_FPc p k) ly S W
    (unpoison U mem) md [] ly S (U1 ++ U2) md2 0 (p - HEAD) (k + HEAD) (n + HEAD) (-64)
    (Z_to_bv 64 A_fuzz_realloc_ra) []).
  all: first
    [ solve [exact HJ0] | solve [exact HARU] | solve [exact (proj1 HRB)] | solve [exact HUout]
    | solve [exact T10] | solve [exact T11] | solve [exact T1] | solve [exact Hbb]
    | solve [exact (proj1 (proj2 HKP))] | solve [exact (proj2 (proj2 HKP))]
    | solve [lazymatch goal with |- _ <= _ < MALLOC_MAX => unfold MALLOC_MAX, HEAD in *; lia end]
    | solve [lazymatch goal with |- spZ _ = _ => rewrite Tsp; lia end]
    | solve [lazymatch goal with |- _ mod _ = _ => reflexivity end]
    | solve [lazymatch goal with |- _ + 16 < 0 => lia end]
    | solve [lazymatch goal with |- STK_RT_REALLOC - _ <= _ => unfold STK_RT_REALLOC; rewrite FR; lia end]
    | solve [lazymatch goal with |- YK0s.ret_ok _ =>
               apply ret_ok_even; rewrite unsigned_lit_small by (unfold A_fuzz_realloc_ra; lia); reflexivity end]
    | solve [lazymatch goal with |- st_nev _ + 2 < EV_MAX => lia end]
    | solve [lazymatch goal with |- chain_pre _ _ _ _ =>
               unfold chain_pre; split;
               [ unfold raZ; rewrite T1, unsigned_lit_small by (unfold A_fuzz_realloc_ra; lia);
                 unfold A_fuzz_realloc_ra; lia
               | destruct (frame0_ok ly regsT); [|reflexivity];
                 replace (bad_next (spZ regsT) (ly_top ly) (s0Z regsT)) with true; [reflexivity|];
                 symmetry; unfold bad_next; rewrite Tsp; unfold s0Z; rewrite T8; unfold w64;
                 rewrite unsigned_lit_small by (unfold MALLOC_MAX, HEAD in *; lia);
                 apply orb_true_iff; left; apply orb_true_iff; left; apply Z.leb_le;
                 unfold MALLOC_MAX, HEAD in *; lia ] end]
    | solve [lazymatch goal with |- forall i, _ -> inFP _ _ =>
               intros i Hi; exists (p - HEAD, p - HEAD + req_size (k + HEAD)); split;
               [ unfold fsr_FPc, ablocks_fp; apply in_or_app; right; cbn [map fst snd]; left; reflexivity
               | cbn [fst snd]; lia ] end]
    | solve [lia] ]. }
intros W3 c3 _ (ly2 & S2 & regs2 & mem2 & md3 & b & -> & HARU2 & HJc & HP & R10 & Hfr2 & Hnev2 & Hb4096 &
  (b1 & b2 & Eb1 & Eb2) & CPY & HK).
rewrite EUM in HJc. change (0 + 3) with 3 in HJc.
assert (GA : fs_glob tfibsegs W3 mem2 (live - k) peak (cnt + 1) fail)
  by exact (fsrC_glob_acall B ly S ly2 S2 (U1 ++ U2) W2 W3 memT mem2 md2 md3 _ _ _
       (live - k) peak (cnt + 1) fail IMG HARU HARU2 HK HGL2).
(* ---- the new block ---- *)
assert (Hnew : In (b, n + HEAD) (ablocks B ly2 S2)) by (rewrite Eb2; apply in_or_app; right; left; reflexivity).
assert (Hrq : req_size (n + HEAD) = n + HEAD)
  by (unfold req_size, HEAD; destruct (Z.eqb_spec (n + 16) 0); lia).
assert (Hrqk : req_size (k + HEAD) = k + HEAD)
  by (unfold req_size, HEAD; destruct (Z.eqb_spec (k + 16) 0); lia).
destruct (al_blocks _ _ LAWS ly2 S2 W3 (unpoison (U1 ++ U2) mem2) md3 b (n + HEAD) (proj1 HARU2) Hnew)
  as (Hb16 & _ & Hbceil & Happ & Hpr & _ & _).
destruct (fsr_new_heads B ly S ly2 S2 W3 (unpoison (U1 ++ U2) mem2) md3 U1 U2 (p - HEAD) k b n b1 b2
  (proj1 HARU2) FHU PWU Eb1 Eb2 ltac:(lia)) as (FH12b & FHnew & DJ).
assert (HFRESH : ~ In (b, n + HEAD) (b1 ++ b2)).
{ intros Hin. apply in_split in Hin as (x1 & x2 & Ex).
  pose proof (sep_blocks_pos tfibsegs B LAWS ly2 S2 W3 (unpoison (U1 ++ U2) mem2) md3 (b, n + HEAD) (b, n + HEAD)
    x1 x2 [] (proj1 HARU2) ltac:(rewrite Eb2, Ex, <- app_assoc; reflexivity)) as D.
  unfold zdisjoint, block_rng in D. cbn [fst snd] in D. rewrite Hrq in D. unfold HEAD in *. lia. }
(* ---- the resume at 0x82b34 (FSW_rres.fsw_resume_after_rtU_args_chunks) ---- *)
assert (P2 : getr regs2 2 = getr regsT 2) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs2 8 = getr regsT 8) by exact (HP 8 ltac:(unfold acallee_saved; lia)).
assert (P19 : getr regs2 19 = getr regsT 19) by exact (HP 19 ltac:(unfold acallee_saved; lia)).
assert (P20 : getr regs2 20 = getr regsT 20) by exact (HP 20 ltac:(unfold acallee_saved; lia)).
set (xs := fs_pstat_xs (cnt + 1) fail (live - k) peak ++
  [getr regs 22; getr regs 21; getr regs 20; getr regs 19; getr regs 18; getr regs 9; getr regs 8; getr regs 1]).
set (E2 := Ereg regs2 (fs_extraT ++ xs)).
assert (E2_2 : bv_unsigned (ew E2 2) = spZ regs - 64)
  by (unfold E2; rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl), P2; unfold spZ in Tsp |- *; exact Tsp).
assert (E2_10 : bv_unsigned (ew E2 10) = b)
  by (unfold E2; rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl), R10; unfold w64; apply unsigned_lit_small; lia).
assert (E2_20 : bv_unsigned (ew E2 20) = SHADOW_OFF)
  by (unfold E2; rewrite (ew_Ereg_nat regs2 _ 20 20%bv eq_refl), P20, T20; unfold w64; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
assert (EX2 : forall j w, nth j (fs_extraT ++ xs) (Z_to_bv 64 0) = w -> ew E2 (32 + j) = w)
  by (intros j w Hw; unfold E2; rewrite ew_Ereg_extra; exact Hw).
assert (KEEPF : forall x, spZ regs - 64 <= x < spZ regs ->
  aview tfibsegs (w_H W3) (unpoison (U1 ++ U2) mem2) x = aview tfibsegs (w_H W2) (unpoison (U1 ++ U2) memT) x).
{ intros x Hx. apply (proj1 HK); lia. }
assert (VK : forall a v, spZ regs - 64 <= a -> a + 8 <= spZ regs ->
  val_mem tfibsegs (mrestrict (w_H W2) memT) a 8 v -> val_mem tfibsegs (mrestrict (w_H W3) mem2) a 8 v).
{ intros a v Ha1 Ha2 Hv.
  apply (fsrC_val_keep B ly S ly2 S2 (U1 ++ U2) W2 W3 memT mem2 md2 md3 a 8 v HARU HARU2);
    [ intros x Hx; apply KEEPF; cbn [Z.of_nat] in Hx; lia | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | exact Hv ]. }
assert (CK : forall (j : nat) (r : bv 5) (off a : Z),
  nth j (fs_extraT ++ xs) (Z_to_bv 64 0) = getr regs r -> spZ regs - 64 + off = a ->
  spZ regs - 64 <= a -> a + 8 <= spZ regs ->
  val_mem tfibsegs (mrestrict (w_H W2) memT) a 8 (bv_unsigned (getr regs r)) ->
  YP09.chunk_ok tfibsegs E2 (mrestrict (w_H W3) mem2) (spZ regs - 64)
    (YP09.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros j r off a Hnth Hoff Hlo Hhi Hv.
  apply (chunk_ok_val tfibsegs E2 _ (spZ regs - 64) off 8 (SOff (32 + j) 0) (bv_unsigned (getr regs r))).
  - rewrite fsw_SOff0, (EX2 j _ Hnth), Z_to_bv_bv_unsigned. reflexivity.
  - pose proof (u64_range (getr regs r)). cbn [Z.of_N]. lia.
  - cbn [Z.of_N]. lia.
  - cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. rewrite Hoff. apply VK; assumption. }
assert (Hck : Forall (YP09.chunk_ok tfibsegs E2 (mrestrict (w_H W3) mem2) (spZ regs - 64)) fsrC_cs).
{ unfold fsrC_cs. repeat apply Forall_cons; try apply Forall_nil.
  - apply (CK 5%nat 22%bv 0 (spZ regs - 64)); first [reflexivity | lia | exact V22].
  - apply (CK 6%nat 21%bv 8 (spZ regs - 56)); first [reflexivity | lia | exact V21].
  - apply (CK 7%nat 20%bv 16 (spZ regs - 48)); first [reflexivity | lia | exact V20].
  - apply (CK 8%nat 19%bv 24 (spZ regs - 40)); first [reflexivity | lia | exact V19].
  - apply (CK 9%nat 18%bv 32 (spZ regs - 32)); first [reflexivity | lia | exact V18].
  - apply (CK 10%nat 9%bv 40 (spZ regs - 24)); first [reflexivity | lia | exact V9].
  - apply (CK 11%nat 8%bv 48 (spZ regs - 16)); first [reflexivity | lia | exact V8].
  - apply (CK 12%nat 1%bv 56 (spZ regs - 8)); first [reflexivity | lia | exact V1]. }
assert (Hrs : Forall (region_ok tfibsegs E2 (mrestrict (w_H W3) mem2)) fsrC_rs).
{ unfold fsrC_rs. constructor; [|constructor].
  apply (fs_head_region_ok B ly2 S2 (U1 ++ U2) W3 mem2 md3 E2 10 b 8 [] b (n + HEAD) HARU2 Hnew);
    first [ solve [exact E2_10] | solve [rewrite Hrq; unfold HEAD; lia] | solve [constructor] | solve [lia] ]. }
assert (Himg : forall g, (forall x, g <= x < g + 8 -> in_img tfibsegs x) -> b + 8 <= g \/ g + 8 <= b)
  by (intros g Hg; exact (fs_head_img_apart B ly2 S2 W3 (unpoison (U1 ++ U2) mem2) md3 b (n + HEAD) b g 8
        (proj1 HARU2) Hnew ltac:(lia) ltac:(rewrite Hrq; unfold HEAD; lia) ltac:(lia) Hg)).
pose proof (Himg tfib_D_GOT_asan_shadow_memory_dynamic_address
  (fun x Hx => fsrC_cells_img x (ex_intro _
     (tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_GOT_asan_shadow_memory_dynamic_address + 8)
     (conj (or_introl eq_refl) Hx)))) as I1.
pose proof (Himg tfib_D_asan_shadow_memory_dynamic_address
  (fun x Hx => fsrC_cells_img x (ex_intro _
     (tfib_D_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address + 8)
     (conj (or_intror (or_introl eq_refl)) Hx)))) as I2.
assert (IS : forall g, In (g, g + 8) FS_PSTAT_FP -> b + 8 <= g \/ g + 8 <= b)
  by (intros g Hg; apply Himg; intros x Hx; exact (fs_pstat_img x (inFP_FS_PSTAT_FP g Hg x Hx))).
pose proof (IS G_COUNT ltac:(vm_compute; tauto)) as I3.
pose proof (IS G_FAIL ltac:(vm_compute; tauto)) as I4.
pose proof (IS G_LIVE ltac:(vm_compute; tauto)) as I5.
pose proof (IS G_PEAK ltac:(vm_compute; tauto)) as I6.
assert (Hpdj : pairwise_disjoint E2 (fsT_ret_regions 64 fsrC_cs fsrC_rs)).
{ apply pairwise_disjoint_of_extents.
  unfold fsT_ret_regions, fsrC_rs, fs_got_region, fs_bcell_region, fstk_ret, fs_head_region, extent_of_region.
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E2_2, E2_10.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address in *.
  cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia | lia]. }
assert (Hgf : atoms_ok E2 fsrC_gf).
{ unfold fsrC_gf. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2_20, E2_10.
  split; [|split; [|exact I]].
  - split; [unfold SHADOW_OFF; lia|]. split; [change (2 ^ 0) with 1; apply Z.mod_1_r | lia].
  - split; [lia|]. split; [change (2 ^ 4) with 16; exact Hb16 | lia]. }
assert (HS0 : st_ok tfibsegs E2 (fss_retT A_fuzz_realloc_ra 64 fsrC_cs fsrC_rs fsrC_gf)
  (restrict (w_H W3) (mkst regs2 (Z_to_bv 64 A_fuzz_realloc_ra) mem2 (seg_rom tfibsegs)))).
{ apply (fsw_resume_after_rtU_args_chunks B STK_fuzz_realloc (spZ regs) (fsr_FPc p k) ly S W (unpoison U mem) md []
    ly2 S2 (U1 ++ U2) W3 mem2 md3 3 regs2 64 xs fsrC_cs fsrC_rs fsrC_gf A_fuzz_realloc_ra).
  all: first
    [ solve [exact FS_GOT] | solve [exact FS_CELL] | solve [exact HJc] | solve [exact HARU2]
    | solve [exact Hck] | solve [exact Hrs] | solve [exact Hpdj] | solve [exact Hgf]
    | solve [lazymatch goal with |- spZ _ = _ => unfold spZ; rewrite P2; unfold spZ in Tsp; rewrite Tsp; reflexivity end]
    | solve [lazymatch goal with |- regions_wf _ = true => vm_compute; reflexivity end]
    | solve [lazymatch goal with |- _ mod _ = _ => reflexivity end]
    | solve [lia] ]. }
(* ---- awr_ok for every run of this stretch: the frame (stack arm) and the new head (the FP arm if realloc gave the
   old address back, else awr_byte0's temporary-block arm) ---- *)
assert (A0 : awr_ok tfibsegs B E2 (ss_mem (fss_retT A_fuzz_realloc_ra 64 fsrC_cs fsrC_rs fsrC_gf))
  STK_fuzz_realloc (spZ regs) (fsr_FPc p k) (ablocks B ly S) (ablocks B ly2 S2) ly2 [] (frames S)).
{ intros a (r & Hr & Hra).
  change (In r (fsT_ret_regions 64 fsrC_cs fsrC_rs)) in Hr.
  unfold fsT_ret_regions, fsrC_rs in Hr. cbn [app] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[]]]]].
  - left. left. cbn [fstk_ret YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra. rewrite E2_2 in Hra. lia.
  - exfalso. cbn [fs_got_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra. lia.
  - exfalso. cbn [fs_bcell_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra. lia.
  - cbn [fs_head_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra. rewrite E2_10 in Hra.
    destruct (Z.eq_dec b (p - HEAD)) as [Eb|Nb].
    + left. right. left. split.
      * exists (p - HEAD, p - HEAD + req_size (k + HEAD)). split;
          [ unfold fsr_FPc, ablocks_fp; apply in_or_app; right; cbn [map fst snd]; left; reflexivity
          | cbn [fst snd]; rewrite Hrqk; unfold HEAD in *; lia ].
      * exists b, (n + HEAD). split; [exact Hnew | rewrite Hrq; unfold HEAD in *; lia].
    + left. right. right. left. exists b, (n + HEAD). split; [exact Hnew|].
      split; [|rewrite Hrq; unfold HEAD in *; lia].
      intros Hin. rewrite Eb1 in Hin. apply in_app_or in Hin as [Hx|[Hx|Hx]].
      * apply HFRESH. apply in_or_app. left. exact Hx.
      * injection Hx as Hx1 _. exact (Nb (eq_sym Hx1)).
      * apply HFRESH. apply in_or_app. right. exact Hx. }
assert (A1 : forall ss, skeleton (ss_mem ss) = skeleton (ss_mem (fss_retT A_fuzz_realloc_ra 64 fsrC_cs fsrC_rs fsrC_gf)) ->
  awr_ok tfibsegs B E2 (ss_mem ss) STK_fuzz_realloc (spZ regs) (fsr_FPc p k) (ablocks B ly S) (ablocks B ly2 S2)
    ly2 [] (frames S))
  by (intros ss Hsk; exact (fsr_awr_skel B E2 _ (ss_mem ss) STK_fuzz_realloc (spZ regs) (fsr_FPc p k)
        (ablocks B ly S) (ablocks B ly2 S2) ly2 [] (frames S) A0 Hsk)).
(* ---- 0x82b34 `beqz a0`: the NULL arm is dead (4096 <= a0 = b) ---- *)
fsw_aj_runU fsr_tbl_ok HS0 HJc HARU2.
{ apply A1. lazymatch goal with |- skeleton _ = skeleton _ => vm_compute; reflexivity end. }
pose proof HF as HFa. clear HF HFr HG.
eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 10 0) (b := SLit 0) (1 := HS0).
1: { intros Hb' _. exfalso.
     rewrite branch_eq_U, U_SOff, E2_10, Z.add_0_r, (U_lit E2 0 ltac:(lia)) in Hb'.
     rewrite zcanon_id in Hb' by (unfold M64; lia). apply Z.eqb_eq in Hb'. lia. }
intros _ HS1. clear HS0.
(* ---- own(): the two inline shadow checks and the eight `sb` of n into the head (token run) ---- *)
lazymatch type of HARU2 with ARU _ _ _ _ _ _ ?mm _ => set (MM := mm) in * end.
destruct (fs_head_shadow0 B ly2 S2 (U1 ++ U2) W3 MM _ b (n + HEAD) HARU2 Hnew
  ltac:(rewrite Hrq; unfold HEAD; lia) DJ) as [Z0 Z1].
assert (SHOK : sh_ok tfibsegs (SOff 20 0) [YCbn.mkSHE 10 0 16] E2 (mrestrict (w_H W3) MM)).
{ constructor; [|constructor].
  apply (fs_head_shent (SOff 20 0) E2 W3 MM 10 b).
  all: first
    [ solve [exact Z0] | solve [exact Z1]
    | solve [lazymatch goal with |- U _ (SOff 10 0) = _ =>
               rewrite U_SOff, E2_10, Z.add_0_r; apply zcanon_id; unfold M64; lia end]
    | solve [lazymatch goal with |- U _ (SOff 20 0) = _ =>
               rewrite U_SOff, E2_20, Z.add_0_r; apply zcanon_id; unfold M64, SHADOW_OFF; lia end]
    | solve [lazymatch goal with |- _ mod 8 = 0 =>
               apply Z.mod_divide; [lia|]; apply Z.mod_divide in Hb16; [|lia];
               destruct Hb16 as [q Hq]; exists (2 * q); lia end]
    | solve [lazymatch goal with |- in_app _ _ =>
               apply (in_app_sub b (req_size (n + HEAD)) b 16 Happ); rewrite ?Hrq; unfold HEAD in *; lia end] ]. }
fsw_aj_run_tokU fsr_tbl_ok HS1 HJc HARU2 SHOK fs_Bspan.
{ apply A1. lazymatch goal with |- skeleton _ = skeleton _ => vm_compute; reflexivity end. }
(* ---- at the fetch of 0x54894 (`jal __asan_poison_memory_region`): the poison call point ---- *)
rewrite ?wvb_collapse in HJc, HARU2.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W3) E2 _ ms0 HS1 eq_refl) as Hshape.
pose proof (st_ok_mem_ok tfibsegs E2 _ _ HS1) as HM. cbn [restrict ms_mem] in HM.
destruct HM as (_ & HR & _). cbn [ss_mem] in HR.
pose proof (Forall_inv HR) as RF.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HR)))) as RH.
destruct RF as (_ & _ & _ & CKF). cbn [YP09.r_chunks YP09.r_base base_val] in CKF.
destruct RH as (_ & _ & _ & CKH). cbn [YP09.r_chunks YP09.r_base base_val] in CKH.
rewrite E2_10 in CKH.
pose proof (Forall_inv CKF) as CF0.
pose proof (Forall_inv (Forall_inv_tail CKF)) as CF1.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail CKF))) as CF2.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail CKF)))) as CF3.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail CKF))))) as CF4.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail
  (Forall_inv_tail CKF)))))) as CF5.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail
  (Forall_inv_tail (Forall_inv_tail CKF))))))) as CF6.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail
  (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail CKF)))))))) as CF7.
pose proof (Forall_inv CKH) as CH3.
pose proof (Forall_inv (Forall_inv_tail CKH)) as CH2.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail CKH))) as CH1.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail CKH)))) as CH0.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail CKH))))) as CH7.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail
  (Forall_inv_tail CKH)))))) as CH6.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail
  (Forall_inv_tail (Forall_inv_tail CKH))))))) as CH5.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail
  (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail CKH)))))))) as CH4.
clear HR CKF CKH.
(* the registers at the call point *)
assert (E2_8 : ew E2 8 = Z_to_bv 64 n)
  by (unfold E2; rewrite (ew_Ereg_nat regs2 _ 8 8%bv eq_refl), P8; exact T8).
assert (Hn64 : 0 <= n < 2 ^ 64) by lia.
assert (Q1 : getr (ms_regs ms0) 1 = Z_to_bv 64 FSR_RA_POISON)
  by exact (fsw_reg_lit (w_H W3) E2 _ ms0 1%bv 535464 HS1 ltac:(vm_compute; reflexivity) ltac:(lia)).
assert (Q11 : getr (ms_regs ms0) 11 = w64 HEAD)
  by exact (fsw_reg_lit (w_H W3) E2 _ ms0 11%bv 16 HS1 ltac:(vm_compute; reflexivity) ltac:(lia)).
assert (Q10 : getr (ms_regs ms0) 10 = w64 b)
  by (rewrite (fsw_reg_atom (w_H W3) regs2 (fs_extraT ++ xs) _ ms0 10%bv 10%bv 10 HS1
        ltac:(vm_compute; reflexivity) eq_refl); exact R10).
assert (Q18 : getr (ms_regs ms0) 18 = w64 b)
  by (rewrite (fsw_reg_atom (w_H W3) regs2 (fs_extraT ++ xs) _ ms0 18%bv 10%bv 10 HS1
        ltac:(vm_compute; reflexivity) eq_refl); exact R10).
assert (Q8 : getr (ms_regs ms0) 8 = w64 n)
  by (rewrite (fsw_reg_atom (w_H W3) regs2 (fs_extraT ++ xs) _ ms0 8%bv 8%bv 8 HS1
        ltac:(vm_compute; reflexivity) eq_refl), P8; exact T8).
assert (Q19 : getr (ms_regs ms0) 19 = w64 FSR_S3)
  by (rewrite (fsw_reg_atom (w_H W3) regs2 (fs_extraT ++ xs) _ ms0 19%bv 19%bv 19 HS1
        ltac:(vm_compute; reflexivity) eq_refl), P19; exact T19).
assert (Q2 : spZ (ms_regs ms0) = spZ regs - 64).
{ unfold spZ. rewrite (fsw_reg_atom (w_H W3) regs2 (fs_extraT ++ xs) _ ms0 2%bv 2%bv 2 HS1
    ltac:(vm_compute; reflexivity) eq_refl), P2. unfold spZ in Tsp. exact Tsp. }
assert (K23 : getr (ms_regs ms0) (Z_to_bv 5 23) = getr regs (Z_to_bv 5 23)).
{ etransitivity; [exact (fsw_reg_atom (w_H W3) regs2 (fs_extraT ++ xs) _ ms0 (Z_to_bv 5 23) (Z_to_bv 5 23) 23 HS1
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))|].
  etransitivity; [exact (HP 23 ltac:(unfold acallee_saved; lia))|]. exact (proj1 HKP 23 ltac:(lia)). }
assert (K24 : getr (ms_regs ms0) (Z_to_bv 5 24) = getr regs (Z_to_bv 5 24)).
{ etransitivity; [exact (fsw_reg_atom (w_H W3) regs2 (fs_extraT ++ xs) _ ms0 (Z_to_bv 5 24) (Z_to_bv 5 24) 24 HS1
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))|].
  etransitivity; [exact (HP 24 ltac:(unfold acallee_saved; lia))|]. exact (proj1 HKP 24 ltac:(lia)). }
assert (K25 : getr (ms_regs ms0) (Z_to_bv 5 25) = getr regs (Z_to_bv 5 25)).
{ etransitivity; [exact (fsw_reg_atom (w_H W3) regs2 (fs_extraT ++ xs) _ ms0 (Z_to_bv 5 25) (Z_to_bv 5 25) 25 HS1
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))|].
  etransitivity; [exact (HP 25 ltac:(unfold acallee_saved; lia))|]. exact (proj1 HKP 25 ltac:(lia)). }
assert (K26 : getr (ms_regs ms0) (Z_to_bv 5 26) = getr regs (Z_to_bv 5 26)).
{ etransitivity; [exact (fsw_reg_atom (w_H W3) regs2 (fs_extraT ++ xs) _ ms0 (Z_to_bv 5 26) (Z_to_bv 5 26) 26 HS1
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))|].
  etransitivity; [exact (HP 26 ltac:(unfold acallee_saved; lia))|]. exact (proj1 HKP 26 ltac:(lia)). }
assert (K27 : getr (ms_regs ms0) (Z_to_bv 5 27) = getr regs (Z_to_bv 5 27)).
{ etransitivity; [exact (fsw_reg_atom (w_H W3) regs2 (fs_extraT ++ xs) _ ms0 (Z_to_bv 5 27) (Z_to_bv 5 27) 27 HS1
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))|].
  etransitivity; [exact (HP 27 ltac:(unfold acallee_saved; lia))|]. exact (proj1 HKP 27 ltac:(lia)). }
assert (QK : fsr_kept B regs (ms_regs ms0)).
{ split; [|split].
  - intros r Hr. assert (Hc : r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    repeat (destruct Hc as [->|Hc]); try subst r;
      [exact K23 | exact K24 | exact K25 | exact K26 | exact K27].
  - rewrite (fsw_reg_atom (w_H W3) regs2 (fs_extraT ++ xs) _ ms0 3%bv 3%bv 3 HS1
      ltac:(vm_compute; reflexivity) eq_refl).
    etransitivity; [exact (HP 3 ltac:(unfold acallee_saved; lia))|]. exact (proj1 (proj2 HKP)).
  - rewrite (fsw_reg_atom (w_H W3) regs2 (fs_extraT ++ xs) _ ms0 4%bv 4%bv 4 HS1
      ltac:(vm_compute; reflexivity) eq_refl).
    etransitivity; [exact (HP 4 ltac:(unfold acallee_saved; lia))|]. exact (proj2 (proj2 HKP)). }
(* no run of this stretch writes a static byte or a block byte above the head *)
assert (NWX : forall rs, skeleton rs = skeleton (ss_mem (fss_retT A_fuzz_realloc_ra 64 fsrC_cs fsrC_rs fsrC_gf)) ->
  forall x, 0 <= x -> x < spZ regs - 64 -> (x < b \/ b + 8 <= x) -> ~ in_wrange E2 rs x).
{ intros rs Hsk x Hx0 Hx1 Hx2 Hw. apply (in_wrange_skeleton E2 rs _ x Hsk) in Hw.
  destruct Hw as (r & Hr & Hra).
  change (In r (fsT_ret_regions 64 fsrC_cs fsrC_rs)) in Hr.
  unfold fsT_ret_regions, fsrC_rs in Hr. cbn [app] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[]]]]].
  - cbn [fstk_ret YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra. rewrite E2_2 in Hra. lia.
  - cbn [fs_got_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra. lia.
  - cbn [fs_bcell_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra. lia.
  - cbn [fs_head_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra. rewrite E2_10 in Hra. lia. }
assert (NWS : forall rs, skeleton rs = skeleton (ss_mem (fss_retT A_fuzz_realloc_ra 64 fsrC_cs fsrC_rs fsrC_gf)) ->
  forall a, inFP FS_PSTAT_FP a -> ~ in_wrange E2 rs a).
{ intros rs Hsk a Ha. pose proof (fsrC_pstat_bounds a Ha) as Hb.
  apply (NWX rs Hsk a); unfold G_COUNT, G_FAIL, G_LIVE, G_PEAK in *; lia. }
(* the bytes of the new block above its head are kept by both runs *)
assert (AVK : forall x, b + 8 <= x -> x < b + req_size (n + HEAD) ->
  aview tfibsegs (w_H W3) (ms_mem ms0) x = aview tfibsegs (w_H W3) mem2 x).
{ intros x Hx1 Hx2.
  assert (Hx64 : 0 <= x < 2 ^ 64) by lia.
  etransitivity.
  - apply (aview_at tfibsegs (w_H W3) (ms_mem ms0) (ms_mem ms) x). apply HF.
    rewrite unsigned_lit_small by lia.
    apply NWX; [ lazymatch goal with |- skeleton _ = _ => vm_compute; reflexivity end | lia | lia | right; lia ].
  - apply (aview_at tfibsegs (w_H W3) (ms_mem ms) mem2 x). apply HFa.
    rewrite unsigned_lit_small by lia.
    apply NWX; [ lazymatch goal with |- skeleton _ = _ => vm_compute; reflexivity end | lia | lia | right; lia ]. }
(* the eight saved words of the frame, read back from the final symbolic memory *)
assert (FV : forall (j : nat) (off a : Z) (r : bv 5),
  YP09.chunk_ok tfibsegs E2 (mrestrict (w_H W3) (ms_mem ms0)) (bv_unsigned (ew E2 2))
    (YP09.mkChunk off (CVal 8 (SOff (32 + j) 0))) ->
  nth j (fs_extraT ++ xs) (Z_to_bv 64 0) = getr regs r -> spZ regs - 64 + off = a ->
  val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms0)) a 8 (bv_unsigned (getr regs r))).
{ intros j off a r HC Hnth Ha. rewrite <- Ha, <- E2_2.
  apply (val_of_chunk_ok tfibsegs E2 _ (bv_unsigned (ew E2 2)) off 8 (SOff (32 + j) 0)
    (bv_unsigned (getr regs r)) HC).
  - rewrite fsw_SOff0, (EX2 j _ Hnth), Z_to_bv_bv_unsigned. reflexivity.
  - pose proof (u64_range (getr regs r)). cbn [Z.of_N]. lia.
  - cbn [Z.of_N]. lia. }
(* the eight `sb` of n into the new head *)
assert (BY : forall (j : nat) (off s : Z) (e : sv),
  Z.of_nat j = off -> 8 * Z.of_nat j = s ->
  YP09.chunk_ok tfibsegs E2 (mrestrict (w_H W3) (ms_mem ms0)) b (YP09.mkChunk off (CVal 1 e)) ->
  bv_unsigned (sv_denot E2 e) = Z.shiftr n s ->
  mbyte tfibsegs (mrestrict (w_H W3) (ms_mem ms0)) (b + Z.of_nat j) = Some (Z_to_bv 8 (le_byte n 8 j))).
{ intros j off s e Hoff Hs HC Hz.
  destruct (HC 0 ltac:(cbn [YP09.c_len YP09.c_val cv_len Z.of_N]; lia)) as (bb & Hb1 & Hb2).
  assert (Hby : Some (Z_to_bv 8 (bv_unsigned (sv_denot E2 e))) = Some bb) by (rewrite <- Hb1; reflexivity).
  injection Hby as <-.
  assert (Hm : mbyte tfibsegs (mrestrict (w_H W3) (ms_mem ms0)) (b + off) =
    Some (Z_to_bv 8 (bv_unsigned (sv_denot E2 e)))) by (rewrite <- Hb2; f_equal; cbn [YP09.c_off]; lia).
  rewrite Hoff, Hm, Hz.
  unfold le_byte. rewrite (Z.mod_small n) by (cbn; lia). rewrite Hs, fsrC_bv8_mod. reflexivity. }
assert (HVAL : val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms0)) b 8 n).
{ intros i Hi.
  assert (Hc : (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7)%nat) by lia.
  repeat (destruct Hc as [->|Hc]); try subst i.
  - apply (BY 0%nat 0 0 (SOff 8 0) eq_refl eq_refl CH0). rewrite Z.shiftr_0_r.
    change (bv_unsigned (sv_denot E2 (SOff 8 0))) with (YP0e.U E2 (SOff 8 0)). exact (U_atom E2 8 n E2_8 Hn64).
  - apply (BY 1%nat 1 8 _ eq_refl eq_refl CH1).
    exact (fsrC_srl_val E2 n 8 E2_8 Hn64 ltac:(lia) ltac:(reflexivity)).
  - apply (BY 2%nat 2 16 _ eq_refl eq_refl CH2).
    exact (fsrC_srl_val E2 n 16 E2_8 Hn64 ltac:(lia) ltac:(reflexivity)).
  - apply (BY 3%nat 3 24 _ eq_refl eq_refl CH3).
    exact (fsrC_srl_val E2 n 24 E2_8 Hn64 ltac:(lia) ltac:(reflexivity)).
  - apply (BY 4%nat 4 32 _ eq_refl eq_refl CH4).
    exact (fsrC_srl_val E2 n 32 E2_8 Hn64 ltac:(lia) ltac:(reflexivity)).
  - apply (BY 5%nat 5 40 _ eq_refl eq_refl CH5).
    exact (fsrC_srl_val E2 n 40 E2_8 Hn64 ltac:(lia) ltac:(reflexivity)).
  - apply (BY 6%nat 6 48 _ eq_refl eq_refl CH6).
    exact (fsrC_srl_val E2 n 48 E2_8 Hn64 ltac:(lia) ltac:(reflexivity)).
  - apply (BY 7%nat 7 56 _ eq_refl eq_refl CH7).
    exact (fsrC_srl_val E2 n 56 E2_8 Hn64 ltac:(lia) ltac:(reflexivity)). }
(* the kept bytes of the old block, at the new block's body *)
assert (HZB : zbytes_at tfibsegs W3 (ms_mem ms0) (b + HEAD) (firstn (Z.to_nat (Z.min k n)) old)).
{ apply (fsr_zbytes_copy W2 W3 memT (ms_mem ms0) p (b + HEAD) old (Z.min k n) HZT ltac:(lia) ltac:(lia)).
  intros i Hi.
  replace (b + HEAD + i) with (b + (HEAD + i)) by lia.
  rewrite (AVK (b + (HEAD + i)) ltac:(lia) ltac:(rewrite Hrq; lia)), (CPY (HEAD + i) ltac:(lia)).
  f_equal. lia. }
(* the statics, across the call and the two runs *)
assert (GB : fs_glob tfibsegs W3 (ms_mem ms0) (live - k) peak (cnt + 1) fail).
{ eapply (fsrC_glob_frame E2 _ W3 (ms_mem ms) (ms_mem ms0) (live - k) peak (cnt + 1) fail HF).
  { apply NWS. lazymatch goal with |- skeleton _ = _ => vm_compute; reflexivity end. }
  eapply (fsrC_glob_frame E2 _ W3 mem2 (ms_mem ms) (live - k) peak (cnt + 1) fail HFa).
  { apply NWS. lazymatch goal with |- skeleton _ = _ => vm_compute; reflexivity end. }
  exact GA. }
(* ---- fsr_at_poison ---- *)
apply SRr_ret. rewrite Hshape.
exists ly2, S2, (ms_regs ms0), (ms_mem ms0), (with_vm_backing (m_vm_lazy md3) mat0 md3), b, b1, b2.
split; [reflexivity|].
split; [exact HJc|].
split; [exact HARU2|].
split; [exact Eb1|].
split; [exact Eb2|].
split.
{ apply (fsr_upoison_ok_cons B ly2 S2 (U1 ++ U2) b (n + HEAD) (proj1 (proj2 HARU2)) DJ Hnew).
  - apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hb16; [|lia]. destruct Hb16 as [q Hq]. exists (2 * q). lia.
  - rewrite Hrq. pose proof (Z.div_mod (n + HEAD) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (n + HEAD) 8 ltac:(lia)). lia. }
split; [exact FHnew|].
split; [exact Q10|].
split; [exact Q11|].
split; [exact Q1|].
split; [exact Q2|].
split; [exact Q8|].
split; [exact Q18|].
split; [exact Q19|].
split; [exact QK|].
split.
{ unfold fsr_frame_vals.
  split; [exact (FV 5%nat 0 (spZ regs - 64) 22%bv CF0 eq_refl ltac:(lia))|].
  split; [exact (FV 6%nat 8 (spZ regs - 56) 21%bv CF1 eq_refl ltac:(lia))|].
  split; [exact (FV 7%nat 16 (spZ regs - 48) 20%bv CF2 eq_refl ltac:(lia))|].
  split; [exact (FV 8%nat 24 (spZ regs - 40) 19%bv CF3 eq_refl ltac:(lia))|].
  split; [exact (FV 9%nat 32 (spZ regs - 32) 18%bv CF4 eq_refl ltac:(lia))|].
  split; [exact (FV 10%nat 40 (spZ regs - 24) 9%bv CF5 eq_refl ltac:(lia))|].
  split; [exact (FV 11%nat 48 (spZ regs - 16) 8%bv CF6 eq_refl ltac:(lia))|].
  exact (FV 12%nat 56 (spZ regs - 8) 1%bv CF7 eq_refl ltac:(lia)). }
split; [exact GB|].
split; [exact HVAL|].
exact HZB.
Qed.

End c.
