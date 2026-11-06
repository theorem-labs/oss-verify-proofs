(* fs ASan+UBSan (build B), group ALLOC (fuzz/alloc.c:118-141): the walks of the four counters over fs.asan-ubsan (image
   tfibsegs = lib/B/YB1v.v's AsanUbsan.M.loaded_segments), proving lib/B/FSH_Fn_alloc.v's fuzz_alloc_live_spec,
   fuzz_alloc_peak_spec, fuzz_alloc_peak_reset_spec and fuzz_alloc_fail_spec. None has a frame, a call or an event;
   U, the blocks and the frames pass through.
   rule 24: proves function fuzz_alloc_live (B 0x82eec), fuzz_alloc_peak (B 0x82ef8), fuzz_alloc_peak_reset (B 0x82f04), fuzz_alloc_fail (B 0x82f18) (reuse search: proof-index on main@c4c03c57ba1 / ossv/recipes@e5e7eba2cc0 / ossv/candidates@ee89628c997 / release/pau-projects-recipes@b6a0088adcb + lemma index over 11131 working branches + live working heads; by address on the four release refs / `proof-index fuzz_strdup fuzz_alloc_live fuzz_alloc_peak fuzz_alloc_peak_reset fuzz_alloc_fail own`, `git grep -l -i -e <addr> <ref> -- proofs/omx-clap-core/fuzz_state`). Result: none; written new for image B, porting ALLOC's A proofs.
   Measured code (capstone 5.0.7 on the pinned fuzz_state.asan-ubsan, sha256 5ac5ce09...; 20 words, no RVC; each word is
   re-fetched from tfibsegs by vm_compute below, the F_<addr> lemmas), the same instructions as build A with B's displacements:
   - fuzz_alloc_live (0x82eec) / fuzz_alloc_peak (0x82ef8): `auipc a0, 0x558; ld a0, lo(a0); ret`, lo = -0x42c
     (g_live 0x5daac0) resp. -0x418 (g_peak 0x5daae0). The memory is unchanged, so the journal is ajournal_init's (over
     unpoison U mem) materialized at the end. Any asyms B, no Section hypothesis.
   - fuzz_alloc_peak_reset (0x82f04): `auipc a0, 0x558; ld a0, -0x444(a0) (g_live); auipc a1, 0x558; sd a0, -0x42c(a1)
     (g_peak); ret`. fuzz_alloc_fail (0x82f18): `auipc a1, 0x558; ld a1, -0x418(a1) (g_count 0x5dab00); add a0, a1, a0;
     sltu a1, a0, a1; neg a1, a1; or a0, a1, a0; auipc a1, 0x21; sd a0, 0x290(a1) (g_fail_at 0xa41c0); ret`, i.e.
     g_count + k saturated at SIZE_MAX (fsa_sat). Each stores into ONE static of lib/B/FSPstat.v's FS_PSTAT_FP: the
     journal (FP = FS_PSTAT_FP) takes the store through ajournal_after_write (awr_byte's static arm), ARU after it is
     lib/B/FSW_pstat_store.v's pstat_store_ARU, which needs the statics not to be runtime-owned: the Section hypothesis
     IMG : fs_img_facts tfibsegs B (lib/B/FSH_Rt.v; S0's, projected by FSH_Gen.fs_pstat_not_owned; its final instance is
     proved once for build B's TfibB).
   Cells read: only the four alloc.c statics g_live / g_peak / g_count / g_fail_at (lib/B/FSH_Base.v G_*, each re-checked
   against the code: the auipc + ld / sd targets are computed by vm_compute from fs.asan-ubsan's own bytes) and the
   instruction words. No GOT shadow, uar flag, A_EMPTY or rodata shadow cell is read.
   ported from: lib/A/FSW_alloc_counters.v (a working branch a402e796fc1 = another working branch's bc4cbdce0f5
   + the SINK GUARD), proofs unchanged. Changed in ONE simultaneous pass (regex alternation over the address map, then
   each displacement by hand): the 20 instruction addresses (A 0x82e5c..0x82ea8 -> B 0x82eec..0x82f38, also in the
   F_<addr> lemma names), the five words that carry a displacement (auipc imm 0x557 -> 0x558; ld / sd imm12 0x764 ->
   0xbd4, 0x778 -> 0xbe8, 0x74c -> 0xbbc, 0xe00 -> 0x290), the two static literals in fs_glob_reset / fs_glob_fail
   (0x5da5e0 -> 0x5daae0, 0xa3ca0 -> 0xa41c0), and the imports (lib/A AB1v / FSH_Base / FSH_Rt / FSPstat / FSW_K /
   FSW_pstat_store / FSH_Fn_alloc -> lib/B's YB1v and the same names; FSupoison, FSupoisonU, FSH_YC20, FSH_Gen stay lib/A's,
   as lib/B's kit imports them). Templates behind the A file: fs's released plain lib/Prog/fuzz_alloc_*_c.v (control
   flow), cgif_file lib/A/AE2x.v:83-115 (concrete SRr_step), lib/A/AFep.v:87-125 (store bookkeeping). No rename. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YP09 YP03 YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK04 YA0i YA0n YA0o YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YN01 YK0u.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v FSH_Base FSH_Rt FSPstat FSW_K FSW_pstat_store FSH_Fn_alloc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ---- fetch and decode facts at the six instruction words (dis 0x82eec-0x82f00) ---- *)
Lemma F_82eec : fetch_word tfibsegs (Z_to_bv 64 0x82eec) = Some (Z_to_bv 32 0x00558517).
Proof. vm_compute. reflexivity. Qed.
Lemma F_82ef0 : fetch_word tfibsegs (Z_to_bv 64 0x82ef0) = Some (Z_to_bv 32 0xbd453503).
Proof. vm_compute. reflexivity. Qed.
Lemma F_82ef4 : fetch_word tfibsegs (Z_to_bv 64 0x82ef4) = Some (Z_to_bv 32 0x00008067).
Proof. vm_compute. reflexivity. Qed.
Lemma F_82ef8 : fetch_word tfibsegs (Z_to_bv 64 0x82ef8) = Some (Z_to_bv 32 0x00558517).
Proof. vm_compute. reflexivity. Qed.
Lemma F_82efc : fetch_word tfibsegs (Z_to_bv 64 0x82efc) = Some (Z_to_bv 32 0xbe853503).
Proof. vm_compute. reflexivity. Qed.
Lemma F_82f00 : fetch_word tfibsegs (Z_to_bv 64 0x82f00) = Some (Z_to_bv 32 0x00008067).
Proof. vm_compute. reflexivity. Qed.
(* auipc a0, 0x558 *)
Lemma D_auipc_a0 : decode_any (Z_to_bv 32 0x00558517) = Some (Auipc (10%bv : bv 5) (0x558%bv : bv 20), 4%Z).
Proof. vm_refl_bv. Qed.
(* ld a0, -0x42c(a0) / ld a0, -0x418(a0) (imm12 0xbd4 / 0xbe8) *)
Lemma D_ld_live : decode_any (Z_to_bv 32 0xbd453503) =
  Some (Load SZ8 true (10%bv : bv 5) (10%bv : bv 5) (0xbd4%bv : bv 12), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma D_ld_peak : decode_any (Z_to_bv 32 0xbe853503) =
  Some (Load SZ8 true (10%bv : bv 5) (10%bv : bv 5) (0xbe8%bv : bv 12), 4%Z).
Proof. vm_refl_bv. Qed.
(* ret = jalr x0, 0(ra) *)
Lemma D_ret : decode_any (Z_to_bv 32 0x00008067) = Some (Jalr (0%bv : bv 5) (1%bv : bv 5) (0%bv : bv 12), 4%Z).
Proof. vm_refl_bv. Qed.
(* fuzz_alloc_peak_reset (dis 0x82f04-0x82f14): auipc a0, 0x558; ld a0, -0x444(a0); auipc a1, 0x558; sd a0, -0x42c(a1); ret *)
Lemma F_82f04 : fetch_word tfibsegs (Z_to_bv 64 0x82f04) = Some (Z_to_bv 32 0x00558517).
Proof. vm_compute. reflexivity. Qed.
Lemma F_82f08 : fetch_word tfibsegs (Z_to_bv 64 0x82f08) = Some (Z_to_bv 32 0xbbc53503).
Proof. vm_compute. reflexivity. Qed.
Lemma F_82f0c : fetch_word tfibsegs (Z_to_bv 64 0x82f0c) = Some (Z_to_bv 32 0x00558597).
Proof. vm_compute. reflexivity. Qed.
Lemma F_82f10 : fetch_word tfibsegs (Z_to_bv 64 0x82f10) = Some (Z_to_bv 32 0xbca5ba23).
Proof. vm_compute. reflexivity. Qed.
Lemma F_82f14 : fetch_word tfibsegs (Z_to_bv 64 0x82f14) = Some (Z_to_bv 32 0x00008067).
Proof. vm_compute. reflexivity. Qed.
Lemma D_ld_reset : decode_any (Z_to_bv 32 0xbbc53503) =
  Some (Load SZ8 true (10%bv : bv 5) (10%bv : bv 5) (0xbbc%bv : bv 12), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma D_auipc_a1 : decode_any (Z_to_bv 32 0x00558597) = Some (Auipc (11%bv : bv 5) (0x558%bv : bv 20), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma D_sd_peak : decode_any (Z_to_bv 32 0xbca5ba23) =
  Some (Store SZ8 (11%bv : bv 5) (10%bv : bv 5) (0xbd4%bv : bv 12), 4%Z).
Proof. vm_refl_bv. Qed.
(* fuzz_alloc_fail (dis 0x82f18-0x82f38): auipc a1, 0x558; ld a1, -0x418(a1); add a0, a1, a0; sltu a1, a0, a1;
   neg a1, a1 (sub a1, zero, a1); or a0, a1, a0; auipc a1, 0x21; sd a0, 0x290(a1); ret *)
Lemma F_82f18 : fetch_word tfibsegs (Z_to_bv 64 0x82f18) = Some (Z_to_bv 32 0x00558597).
Proof. vm_compute. reflexivity. Qed.
Lemma F_82f1c : fetch_word tfibsegs (Z_to_bv 64 0x82f1c) = Some (Z_to_bv 32 0xbe85b583).
Proof. vm_compute. reflexivity. Qed.
Lemma F_82f20 : fetch_word tfibsegs (Z_to_bv 64 0x82f20) = Some (Z_to_bv 32 0x00a58533).
Proof. vm_compute. reflexivity. Qed.
Lemma F_82f24 : fetch_word tfibsegs (Z_to_bv 64 0x82f24) = Some (Z_to_bv 32 0x00b535b3).
Proof. vm_compute. reflexivity. Qed.
Lemma F_82f28 : fetch_word tfibsegs (Z_to_bv 64 0x82f28) = Some (Z_to_bv 32 0x40b005b3).
Proof. vm_compute. reflexivity. Qed.
Lemma F_82f2c : fetch_word tfibsegs (Z_to_bv 64 0x82f2c) = Some (Z_to_bv 32 0x00a5e533).
Proof. vm_compute. reflexivity. Qed.
Lemma F_82f30 : fetch_word tfibsegs (Z_to_bv 64 0x82f30) = Some (Z_to_bv 32 0x00021597).
Proof. vm_compute. reflexivity. Qed.
Lemma F_82f34 : fetch_word tfibsegs (Z_to_bv 64 0x82f34) = Some (Z_to_bv 32 0x28a5b823).
Proof. vm_compute. reflexivity. Qed.
Lemma F_82f38 : fetch_word tfibsegs (Z_to_bv 64 0x82f38) = Some (Z_to_bv 32 0x00008067).
Proof. vm_compute. reflexivity. Qed.
Lemma D_ld_cnt : decode_any (Z_to_bv 32 0xbe85b583) =
  Some (Load SZ8 true (11%bv : bv 5) (11%bv : bv 5) (0xbe8%bv : bv 12), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma D_add : decode_any (Z_to_bv 32 0x00a58533) = Some (Op ALU_ADD (10%bv : bv 5) (11%bv : bv 5) (10%bv : bv 5), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma D_sltu : decode_any (Z_to_bv 32 0x00b535b3) = Some (Op ALU_SLTU (11%bv : bv 5) (10%bv : bv 5) (11%bv : bv 5), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma D_neg : decode_any (Z_to_bv 32 0x40b005b3) = Some (Op ALU_SUB (11%bv : bv 5) (0%bv : bv 5) (11%bv : bv 5), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma D_or : decode_any (Z_to_bv 32 0x00a5e533) = Some (Op ALU_OR (10%bv : bv 5) (11%bv : bv 5) (10%bv : bv 5), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma D_auipc_a1_21 : decode_any (Z_to_bv 32 0x00021597) = Some (Auipc (11%bv : bv 5) (0x21%bv : bv 20), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma D_sd_fail : decode_any (Z_to_bv 32 0x28a5b823) =
  Some (Store SZ8 (11%bv : bv 5) (10%bv : bv 5) (0x290%bv : bv 12), 4%Z).
Proof. vm_refl_bv. Qed.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.

(* the three steps `auipc a0, hi; ld a0, lo(a0); ret` at pc, the load reading the 8-byte word v at g: a0 ends as v, the
   memory is unchanged, the run returns to ra (the plain proofs' `step. step. step.`, fuzz_alloc_live.v:16) *)
Lemma fsa_ld_ret : forall (W : world tfibsegs) regs mem md (pc g v : Z) (hi : bv 20) (lo : bv 12) (w0 w1 w2 : bv 32),
  fetch_word tfibsegs (Z_to_bv 64 pc) = Some w0 -> is_ecall w0 = false ->
  decode_any w0 = Some (Auipc (10%bv : bv 5) hi, 4%Z) ->
  fetch_word tfibsegs (Z_to_bv 64 (pc + 4)) = Some w1 -> is_ecall w1 = false ->
  decode_any w1 = Some (Load SZ8 true (10%bv : bv 5) (10%bv : bv 5) lo, 4%Z) ->
  fetch_word tfibsegs (Z_to_bv 64 (pc + 8)) = Some w2 -> is_ecall w2 = false ->
  decode_any w2 = Some (Jalr (0%bv : bv 5) (1%bv : bv 5) (0%bv : bv 12), 4%Z) ->
  0 <= pc -> pc + 8 < 2 ^ 64 ->
  v_addi (v_auipc (Z_to_bv 64 pc) (Z.shiftl (bv_signed hi) 12)) (bv_signed lo) = Z_to_bv 64 g ->
  0 <= g -> g + 8 <= 2 ^ 64 ->
  val_mem tfibsegs (mrestrict (w_H W) mem) g 8 v ->
  YK0s.ret_ok (YK11.getr regs 1) ->
  SRr tfibsegs W (mkCfg (YK11.mkst regs (Z_to_bv 64 pc) mem (YK11.seg_rom tfibsegs)) md)
    (fun W' c' => W' = W /\ exists md', same_but_materialized md md' /\
       c' = mkCfg (YK11.mkst (regupd (regupd regs (10%bv : bv 5) (v_auipc (Z_to_bv 64 pc) (Z.shiftl (bv_signed hi) 12)))
                           (10%bv : bv 5) (Z_to_bv 64 v))
                     (YK11.getr regs 1) mem (YK11.seg_rom tfibsegs)) md').
Proof.
intros W regs mem md pc g v hi lo w0 w1 w2 F0 E0 D0 F1 E1 D1 F2 E2 D2 Hpc Hpc8 Ha Hg Hg8 Hv Hra.
pose proof fs_wx as Hwx.
assert (N10 : (10%bv : bv 5) <> (0%bv : bv 5)) by (intros E; apply (f_equal bv_unsigned) in E; vm_compute in E; discriminate).
assert (N1 : (1%bv : bv 5) <> (10%bv : bv 5)) by (intros E; apply (f_equal bv_unsigned) in E; vm_compute in E; discriminate).
set (a1 := v_auipc (Z_to_bv 64 pc) (Z.shiftl (bv_signed hi) 12)) in *.
(* auipc a0, hi *)
eapply (SRr_step tfibsegs Hwx W); [reflexivity | |].
{ rewrite restrict_mkst_fx. exact (step_auipc tfibsegs regs _ _ _ w0 _ hi F0 E0 D0). }
intros md1 Hs1. rewrite unrestrict_mkst_mrestrict.
replace (bv_eqb (10%bv : bv 5) 0) with false by reflexivity. cbn beta iota. fold a1.
replace (v_addi (Z_to_bv 64 pc) 4) with (Z_to_bv 64 (pc + 4)) by (unfold v_addi; rewrite unsigned_lit_small by lia; reflexivity).
(* ld a0, lo(a0) *)
destruct (YN01.word_mem_ld tfibsegs (mrestrict (w_H W) mem) g v (proj1 (val_mem_word_mem tfibsegs _ g v) Hv) Hg Hg8)
  as (bs & Hrd & Hbs).
eapply (SRr_step tfibsegs Hwx W); [reflexivity | |].
{ rewrite restrict_mkst_fx. apply (step_ld tfibsegs _ _ _ _ w1 _ _ lo bs (Z_to_bv 64 v) F1 E1 D1); [|exact Hbs].
  rewrite (getr_same regs (10%bv : bv 5) a1 N10), Ha. exact Hrd. }
intros md2 Hs2. rewrite unrestrict_mkst_mrestrict.
replace (bv_eqb (10%bv : bv 5) 0) with false by reflexivity. cbn beta iota.
replace (v_addi (Z_to_bv 64 (pc + 4)) 4) with (Z_to_bv 64 (pc + 8))
  by (unfold v_addi; rewrite unsigned_lit_small by lia; f_equal; lia).
(* ret *)
eapply (SRr_step tfibsegs Hwx W); [reflexivity | |].
{ rewrite restrict_mkst_fx. exact (step_jalr tfibsegs _ _ _ _ w2 _ _ _ F2 E2 D2). }
intros md3 Hs3. rewrite unrestrict_mkst_mrestrict.
replace (bv_eqb (0%bv : bv 5) 0) with true by reflexivity. cbn beta iota.
lazymatch goal with |- context [v_jalr ?x (bv_signed ?i)] =>
  replace (v_jalr x (bv_signed i)) with (YK11.getr regs 1) end.
2:{ rewrite (getr_other _ (10%bv : bv 5) _ (1%bv : bv 5) N1), (getr_other _ (10%bv : bv 5) _ (1%bv : bv 5) N1).
    symmetry. exact Hra. }
apply SRr_ret. split; [reflexivity|]. exists md3. split; [|reflexivity].
eapply same_but_materialized_trans; [exact Hs1|]. eapply same_but_materialized_trans; [exact Hs2 | exact Hs3].
Qed.

(* the callee-saved registers survive two writes of a0 *)
Lemma fsa_preserved_a0 : forall regs x y,
  aregs_preserved regs (regupd (regupd regs (10%bv : bv 5) x) (10%bv : bv 5) y).
Proof.
intros regs x y r Hr.
assert (NE : Z_to_bv 5 r <> (10%bv : bv 5)).
{ intros E. unfold acallee_saved in Hr. apply (f_equal bv_unsigned) in E.
  rewrite Z_to_bv_unsigned, bv_wrap_small in E by (unfold bv_modulus; cbn [Z.of_N]; lia).
  vm_compute in E. lia. }
rewrite (getr_other _ _ _ _ NE), (getr_other _ _ _ _ NE). reflexivity.
Qed.

(* fuzz_alloc_live 0x82eec (alloc.c:118-120): returns g_live *)
Theorem fuzz_alloc_live_ok : forall B, @fuzz_alloc_live_spec fx rc SK tfibsegs B.
Proof.
intros B ly S U W regs mem md ch live peak cnt fail PRE FH GL.
pose proof PRE as ((HAP & OK & PO) & RO).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof GL as (G1 & G2 & G3 & G4 & GR).
unfold cfg_at.
eapply SRr_mono.
{ apply (fsa_ld_ret W regs mem md A_fuzz_alloc_live G_LIVE live (0x558%bv : bv 20) (0xbd4%bv : bv 12)
    (Z_to_bv 32 0x00558517) (Z_to_bv 32 0xbd453503) (Z_to_bv 32 0x00008067)
    F_82eec eq_refl D_auipc_a0 F_82ef0 eq_refl D_ld_live F_82ef4 eq_refl D_ret);
  [unfold A_fuzz_alloc_live; lia | unfold A_fuzz_alloc_live; lia | apply bv_eq; vm_compute; reflexivity
  | unfold G_LIVE; lia | unfold G_LIVE; lia | exact G1 | exact Hra]. }
intros W' c' _ (-> & md' & Hsb & ->).
unfold apost_baseU, fpostU.
exists ly, S. do 3 eexists. split; [reflexivity|].
split.
{ rewrite (same_but_materialized_wvb md md' Hsb).
  apply (ajournal_materialize tfibsegs B (AR_laws_ok tfibsegs B) fs_segs_low).
  exact (ajournal_init tfibsegs B STK_fuzz_alloc [] ly S W regs (unpoison U mem) md ch HAP). }
split; [exact OK|]. split; [exact PO|]. split; [apply fsa_preserved_a0|].
split; [apply getr_same; intros E; apply (f_equal bv_unsigned) in E; vm_compute in E; discriminate|].
split; [reflexivity|]. split; [exact GL | exact FH].
Qed.

(* fuzz_alloc_peak 0x82ef8 (alloc.c:122-125): returns g_peak *)
Theorem fuzz_alloc_peak_ok : forall B, @fuzz_alloc_peak_spec fx rc SK tfibsegs B.
Proof.
intros B ly S U W regs mem md ch live peak cnt fail PRE FH GL.
pose proof PRE as ((HAP & OK & PO) & RO).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof GL as (G1 & G2 & G3 & G4 & GR).
unfold cfg_at.
eapply SRr_mono.
{ apply (fsa_ld_ret W regs mem md A_fuzz_alloc_peak G_PEAK peak (0x558%bv : bv 20) (0xbe8%bv : bv 12)
    (Z_to_bv 32 0x00558517) (Z_to_bv 32 0xbe853503) (Z_to_bv 32 0x00008067)
    F_82ef8 eq_refl D_auipc_a0 F_82efc eq_refl D_ld_peak F_82f00 eq_refl D_ret);
  [unfold A_fuzz_alloc_peak; lia | unfold A_fuzz_alloc_peak; lia | apply bv_eq; vm_compute; reflexivity
  | unfold G_PEAK; lia | unfold G_PEAK; lia | exact G2 | exact Hra]. }
intros W' c' _ (-> & md' & Hsb & ->).
unfold apost_baseU, fpostU.
exists ly, S. do 3 eexists. split; [reflexivity|].
split.
{ rewrite (same_but_materialized_wvb md md' Hsb).
  apply (ajournal_materialize tfibsegs B (AR_laws_ok tfibsegs B) fs_segs_low).
  exact (ajournal_init tfibsegs B STK_fuzz_alloc [] ly S W regs (unpoison U mem) md ch HAP). }
split; [exact OK|]. split; [exact PO|]. split; [apply fsa_preserved_a0|].
split; [apply getr_same; intros E; apply (f_equal bv_unsigned) in E; vm_compute in E; discriminate|].
split; [reflexivity|]. split; [exact GL | exact FH].
Qed.

(* ======== the two static-writing counters: the machine walks (their journals wait on the core's static-store arm) ======== *)

Lemma fsa_ne : forall (r r' : bv 5), bv_unsigned r <> bv_unsigned r' -> r <> r'.
Proof. intros r r' H E. apply H. rewrite E. reflexivity. Qed.
Ltac fsa_neq := apply fsa_ne; vm_compute; let E := fresh "E" in intros E; discriminate E.
(* rewrite every getr of an explicit regupd chain in the goal *)
Ltac fsa_gsimp :=
  repeat match goal with
  | |- context [YK11.getr (regupd ?R ?r ?v) ?r] => rewrite (getr_same R r v) by fsa_neq
  | |- context [YK11.getr (regupd ?R ?r ?v) ?r'] => rewrite (getr_other R r v r') by fsa_neq
  end.

(* one non-store step *)
Lemma fsa_step : forall (W : world tfibsegs) regs mem md pc regs' pc' Q,
  RiscvSemantics.step tfibsegs (YK11.mkst regs pc (mrestrict (w_H W) mem) (YK11.seg_rom tfibsegs)) =
    MachineOk (YK11.mkst regs' pc' (mrestrict (w_H W) mem) (YK11.seg_rom tfibsegs)) ->
  (forall md', same_but_materialized md md' ->
     SRr tfibsegs W (mkCfg (YK11.mkst regs' pc' mem (YK11.seg_rom tfibsegs)) md') Q) ->
  SRr tfibsegs W (mkCfg (YK11.mkst regs pc mem (YK11.seg_rom tfibsegs)) md) Q.
Proof.
intros W regs mem md pc regs' pc' Q Hs Hk.
eapply (SRr_step tfibsegs fs_wx W); [reflexivity | rewrite restrict_mkst_fx; exact Hs |].
intros md' Hsb. rewrite unrestrict_mkst_mrestrict. exact (Hk md' Hsb).
Qed.

Lemma fsa_nth_le : forall (w : word) k, (k < 8)%nat ->
  nth k (word_to_le_bytes 8 w) (Z_to_bv 8 0) = Z_to_bv 8 (le_byte (bv_unsigned w) 8 k).
Proof.
intros w k Hk. apply nth_error_nth. unfold word_to_le_bytes. rewrite YN01.nth_error_Z_to_le_bytes by exact Hk.
rewrite YN01.le_byte_bv by exact Hk. rewrite (Z.mod_small (bv_unsigned w)); [reflexivity|].
change (2 ^ (8 * Z.of_nat 8)) with (bv_modulus 64). apply bv_unsigned_in_range.
Qed.

(* one `sd` into an image static g of fs.asan's last RW segment: the memory changes only in [g, g + 8), where it holds
   the stored word's little-endian bytes *)
Lemma fsa_step_sd : forall (W : world tfibsegs) regs mem md pc w (rs1 rs2 : bv 5) (imm : bv 12) g Q,
  fetch_word tfibsegs pc = Some w -> is_ecall w = false -> decode_any w = Some (Store SZ8 rs1 rs2 imm, 4%Z) ->
  v_addi (YK11.getr regs rs1) (bv_signed imm) = Z_to_bv 64 g ->
  0xa1000 <= g -> g + 8 <= 0x5fd000 ->
  RiscvSemantics.store_ok tfibsegs (mrestrict (w_H W) mem) (Z_to_bv 64 g) 8 = true ->
  (forall md' mem', same_but_materialized md md' ->
     (forall x : word, ~ (g <= bv_unsigned x < g + 8) -> mem' x = mem x) ->
     (forall k, (k < 8)%nat ->
        mem' (Z_to_bv 64 (g + Z.of_nat k)) = Some (Z_to_bv 8 (le_byte (bv_unsigned (YK11.getr regs rs2)) 8 k))) ->
     SRr tfibsegs W (mkCfg (YK11.mkst regs (v_addi pc 4) mem' (YK11.seg_rom tfibsegs)) md') Q) ->
  SRr tfibsegs W (mkCfg (YK11.mkst regs pc mem (YK11.seg_rom tfibsegs)) md) Q.
Proof.
intros W regs mem md pc w rs1 rs2 imm g Q F E D Ha Hg Hg8 Hok Hk.
eapply (SRr_step tfibsegs fs_wx W); [reflexivity | rewrite restrict_mkst_fx;
  exact (step_sd_val tfibsegs regs pc _ _ w rs1 rs2 imm F E D ltac:(rewrite Ha; exact Hok)) |].
intros md' Hsb. rewrite Ha.
set (bs := word_to_le_bytes 8 (YK11.getr regs rs2)).
assert (Lbs : Z.of_nat (length bs) = 8) by (unfold bs; rewrite length_N_to_le_bytes; reflexivity).
set (m1 := wbytes (mrestrict (w_H W) mem) (Z_to_bv 64 g) bs).
apply (Hk md' (munrestrict (w_H W) mem m1) Hsb).
- intros x Hx. unfold munrestrict. destruct (w_H W x) eqn:Hh; [reflexivity|].
  unfold m1. pose proof (u64_range x) as Ux. destruct (Z_lt_le_dec (bv_unsigned x) g) as [L|L].
  + rewrite wbytes_below; [| rewrite Lbs, unsigned_lit_small by lia; lia | rewrite unsigned_lit_small by lia; lia].
    unfold mrestrict. rewrite Hh. reflexivity.
  + rewrite wbytes_above; [| rewrite Lbs, unsigned_lit_small by lia; lia].
    unfold mrestrict. rewrite Hh. reflexivity.
- intros k Hk8. unfold munrestrict. rewrite (fs_rw3_vis W (g + Z.of_nat k)) by lia. unfold m1.
  rewrite YK0u.wbytes_inside; rewrite ?Lbs, ?unsigned_lit_small by lia; [| lia | lia].
  replace (Z.to_nat (g + Z.of_nat k - g)) with k by lia. unfold bs. rewrite fsa_nth_le by exact Hk8. reflexivity.
Qed.

Lemma fsa_pres_refl : forall regs, aregs_preserved regs regs.
Proof. intros regs z _. reflexivity. Qed.
Lemma fsa_pres_upd : forall regs regs1 (r : bv 5) v, aregs_preserved regs regs1 ->
  (bv_unsigned r = 10 \/ bv_unsigned r = 11) -> aregs_preserved regs (regupd regs1 r v).
Proof.
intros regs regs1 r v HP Hr z Hz. rewrite getr_other; [exact (HP z Hz)|].
intros E. unfold acallee_saved in Hz. apply (f_equal bv_unsigned) in E.
rewrite Z_to_bv_unsigned, bv_wrap_small in E by (unfold bv_modulus; cbn [Z.of_N]; lia). lia.
Qed.
Lemma fsa_getr0 : forall regs, YK11.getr regs (0%bv : bv 5) = Z_to_bv 64 0.
Proof. intros regs. reflexivity. Qed.

(* `neg a1, a1; or a0, a1, a0` after `add a0, a1, a0; sltu a1, a0, a1`: g_count + k saturated at SIZE_MAX
   (alloc.c:138-141) *)
Lemma fsa_sat : forall cnt k, 0 <= cnt < 2 ^ 64 -> 0 <= k < 2 ^ 64 ->
  v_or (v_sub (Z_to_bv 64 0) (v_sltu (v_add (Z_to_bv 64 cnt) (Z_to_bv 64 k)) (Z_to_bv 64 cnt)))
       (v_add (Z_to_bv 64 cnt) (Z_to_bv 64 k))
  = Z_to_bv 64 (if cnt + k <? 2 ^ 64 then cnt + k else SIZE_MAXZ).
Proof.
intros cnt k Hc Hk.
assert (LOR : forall y, 0 <= y < 2 ^ 64 -> Z.lor (2 ^ 64 - 1) y = 2 ^ 64 - 1).
{ intros y Hy. apply Z.bits_inj'. intros n Hn. rewrite Z.lor_spec.
  replace (2 ^ 64 - 1) with (Z.ones 64) by reflexivity.
  destruct (Z_lt_le_dec n 64) as [N|N].
  - rewrite Z.ones_spec_low by lia. reflexivity.
  - rewrite Z.ones_spec_high by lia. cbn [orb].
    rewrite <- (Z.mod_small y (2 ^ 64)) by lia. apply Z.mod_pow2_bits_high. lia. }
unfold v_or, v_sub, v_sltu, v_add, c_ltu, bv_ltu.
rewrite !(unsigned_lit_small cnt) by lia. rewrite (unsigned_lit_small k) by lia.
destruct (Z.ltb_spec (cnt + k) (2 ^ 64)) as [L|L].
- rewrite (unsigned_lit_small (cnt + k)) by lia.
  replace (cnt + k <? cnt) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite (unsigned_lit_small 0) by lia. change (0 - 0) with 0. rewrite (unsigned_lit_small 0) by lia.
  rewrite Z.lor_0_l. reflexivity.
- assert (Es : bv_unsigned (Z_to_bv 64 (cnt + k)) = cnt + k - 2 ^ 64).
  { rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    symmetry. apply Z.mod_unique_pos with (q := 1); lia. }
  rewrite Es. replace (cnt + k - 2 ^ 64 <? cnt) with true by (symmetry; apply Z.ltb_lt; lia).
  rewrite (unsigned_lit_small 0) by lia. rewrite (unsigned_lit_small 1) by lia.
  replace (bv_unsigned (Z_to_bv 64 (0 - 1))) with (2 ^ 64 - 1) by (vm_compute; reflexivity).
  rewrite LOR by lia. unfold SIZE_MAXZ. reflexivity.
Qed.

(* fuzz_alloc_peak_reset's machine run (alloc.c:131-134): g_peak := g_live, return *)
Lemma fsa_reset_walk : forall (W : world tfibsegs) regs mem md live,
  val_mem tfibsegs (mrestrict (w_H W) mem) G_LIVE 8 live -> 0 <= live < 2 ^ 64 ->
  YK0s.ret_ok (YK11.getr regs 1) ->
  SRr tfibsegs W (mkCfg (YK11.mkst regs (Z_to_bv 64 A_fuzz_alloc_peak_reset) mem (YK11.seg_rom tfibsegs)) md)
    (fun W' c' => W' = W /\ exists regs' md' mem', same_but_materialized md md' /\ aregs_preserved regs regs' /\
       c' = mkCfg (YK11.mkst regs' (YK11.getr regs 1) mem' (YK11.seg_rom tfibsegs)) md' /\
       (forall x : word, ~ (G_PEAK <= bv_unsigned x < G_PEAK + 8) -> mem' x = mem x) /\
       (forall k, (k < 8)%nat -> mem' (Z_to_bv 64 (G_PEAK + Z.of_nat k)) = Some (Z_to_bv 8 (le_byte live 8 k)))).
Proof.
intros W regs mem md live Hv Hl Hra.
(* auipc a0, 0x558 *)
eapply fsa_step; [exact (step_auipc tfibsegs regs _ _ _ _ _ _ F_82f04 eq_refl D_auipc_a0) | intros md1 Hs1].
replace (bv_eqb (10%bv : bv 5) 0) with false by reflexivity. cbn beta iota.
replace (v_addi (Z_to_bv 64 0x82f04) 4) with (Z_to_bv 64 0x82f08) by (apply bv_eq; vm_compute; reflexivity).
(* ld a0, -0x444(a0) *)
destruct (YN01.word_mem_ld tfibsegs (mrestrict (w_H W) mem) G_LIVE live (proj1 (val_mem_word_mem tfibsegs _ G_LIVE live) Hv)
  ltac:(unfold G_LIVE; lia) ltac:(unfold G_LIVE; lia)) as (bs & Hrd & Hbs).
eapply fsa_step.
{ apply (step_ld tfibsegs _ _ _ _ _ _ _ _ bs (Z_to_bv 64 live) F_82f08 eq_refl D_ld_reset); [|exact Hbs].
  fsa_gsimp. lazymatch goal with |- rdn _ _ ?t _ = _ =>
    replace t with (Z_to_bv 64 G_LIVE) by (apply bv_eq; vm_compute; reflexivity) end. exact Hrd. }
intros md2 Hs2.
replace (bv_eqb (10%bv : bv 5) 0) with false by reflexivity. cbn beta iota.
replace (v_addi (Z_to_bv 64 0x82f08) 4) with (Z_to_bv 64 0x82f0c) by (apply bv_eq; vm_compute; reflexivity).
(* auipc a1, 0x558 *)
eapply fsa_step; [exact (step_auipc tfibsegs _ _ _ _ _ _ _ F_82f0c eq_refl D_auipc_a1) | intros md3 Hs3].
replace (bv_eqb (11%bv : bv 5) 0) with false by reflexivity. cbn beta iota.
replace (v_addi (Z_to_bv 64 0x82f0c) 4) with (Z_to_bv 64 0x82f10) by (apply bv_eq; vm_compute; reflexivity).
(* sd a0, -0x42c(a1): the one static store *)
eapply (fsa_step_sd W _ mem md3 _ _ _ _ _ G_PEAK _ F_82f10 eq_refl D_sd_peak).
{ fsa_gsimp. apply bv_eq; vm_compute; reflexivity. }
{ unfold G_PEAK; lia. }
{ unfold G_PEAK; lia. }
{ apply store_ok_wseg. vm_compute. reflexivity. }
intros md4 mem4 Hs4 Hout Hin.
replace (v_addi (Z_to_bv 64 0x82f10) 4) with (Z_to_bv 64 0x82f14) by (apply bv_eq; vm_compute; reflexivity).
(* ret *)
eapply fsa_step; [exact (step_jalr tfibsegs _ _ _ _ _ _ _ _ F_82f14 eq_refl D_ret) | intros md5 Hs5].
replace (bv_eqb (0%bv : bv 5) 0) with true by reflexivity. cbn beta iota.
lazymatch goal with |- context [v_jalr ?x (bv_signed ?i)] => replace (v_jalr x (bv_signed i)) with (YK11.getr regs 1) end.
2:{ fsa_gsimp. symmetry. exact Hra. }
apply SRr_ret. split; [reflexivity|]. do 3 eexists.
refine (conj _ (conj _ (conj eq_refl (conj Hout _)))).
- eapply same_but_materialized_trans; [exact Hs1|]; eapply same_but_materialized_trans; [exact Hs2|];
  eapply same_but_materialized_trans; [exact Hs3|]; eapply same_but_materialized_trans; [exact Hs4 | exact Hs5].
- repeat (apply fsa_pres_upd; [| vm_compute; lia]); apply fsa_pres_refl.
- intros k Hk. rewrite (Hin k Hk). fsa_gsimp. rewrite unsigned_lit_small by lia. reflexivity.
Qed.

(* fuzz_alloc_fail's machine run (alloc.c:138-141): g_fail_at := g_count + k saturated at SIZE_MAX, return *)
Lemma fsa_fail_walk : forall (W : world tfibsegs) regs mem md cnt k,
  val_mem tfibsegs (mrestrict (w_H W) mem) G_COUNT 8 cnt -> 0 <= cnt < 2 ^ 64 ->
  YK11.getr regs 10 = Z_to_bv 64 k -> 0 <= k < 2 ^ 64 ->
  YK0s.ret_ok (YK11.getr regs 1) ->
  SRr tfibsegs W (mkCfg (YK11.mkst regs (Z_to_bv 64 A_fuzz_alloc_fail) mem (YK11.seg_rom tfibsegs)) md)
    (fun W' c' => W' = W /\ exists regs' md' mem', same_but_materialized md md' /\ aregs_preserved regs regs' /\
       c' = mkCfg (YK11.mkst regs' (YK11.getr regs 1) mem' (YK11.seg_rom tfibsegs)) md' /\
       (forall x : word, ~ (G_FAIL <= bv_unsigned x < G_FAIL + 8) -> mem' x = mem x) /\
       (forall j, (j < 8)%nat -> mem' (Z_to_bv 64 (G_FAIL + Z.of_nat j)) =
          Some (Z_to_bv 8 (le_byte (if cnt + k <? 2 ^ 64 then cnt + k else SIZE_MAXZ) 8 j)))).
Proof.
intros W regs mem md cnt k Hv Hc Hk Hk64 Hra.
(* auipc a1, 0x558 *)
eapply fsa_step; [exact (step_auipc tfibsegs regs _ _ _ _ _ _ F_82f18 eq_refl D_auipc_a1) | intros md1 Hs1].
replace (bv_eqb (11%bv : bv 5) 0) with false by reflexivity. cbn beta iota.
replace (v_addi (Z_to_bv 64 0x82f18) 4) with (Z_to_bv 64 0x82f1c) by (apply bv_eq; vm_compute; reflexivity).
(* ld a1, -0x418(a1) *)
destruct (YN01.word_mem_ld tfibsegs (mrestrict (w_H W) mem) G_COUNT cnt (proj1 (val_mem_word_mem tfibsegs _ G_COUNT cnt) Hv)
  ltac:(unfold G_COUNT; lia) ltac:(unfold G_COUNT; lia)) as (bs & Hrd & Hbs).
eapply fsa_step.
{ apply (step_ld tfibsegs _ _ _ _ _ _ _ _ bs (Z_to_bv 64 cnt) F_82f1c eq_refl D_ld_cnt); [|exact Hbs].
  fsa_gsimp. lazymatch goal with |- rdn _ _ ?t _ = _ =>
    replace t with (Z_to_bv 64 G_COUNT) by (apply bv_eq; vm_compute; reflexivity) end. exact Hrd. }
intros md2 Hs2.
replace (bv_eqb (11%bv : bv 5) 0) with false by reflexivity. cbn beta iota.
replace (v_addi (Z_to_bv 64 0x82f1c) 4) with (Z_to_bv 64 0x82f20) by (apply bv_eq; vm_compute; reflexivity).
(* add a0, a1, a0 *)
eapply fsa_step; [exact (step_add tfibsegs _ _ _ _ _ _ _ _ F_82f20 eq_refl D_add) | intros md3 Hs3].
replace (bv_eqb (10%bv : bv 5) 0) with false by reflexivity. cbn beta iota. fsa_gsimp. rewrite Hk.
replace (v_addi (Z_to_bv 64 0x82f20) 4) with (Z_to_bv 64 0x82f24) by (apply bv_eq; vm_compute; reflexivity).
(* sltu a1, a0, a1 *)
eapply fsa_step; [exact (step_sltu tfibsegs _ _ _ _ _ _ _ _ F_82f24 eq_refl D_sltu) | intros md4 Hs4].
replace (bv_eqb (11%bv : bv 5) 0) with false by reflexivity. cbn beta iota. fsa_gsimp.
replace (v_addi (Z_to_bv 64 0x82f24) 4) with (Z_to_bv 64 0x82f28) by (apply bv_eq; vm_compute; reflexivity).
(* neg a1, a1 *)
eapply fsa_step; [exact (step_sub tfibsegs _ _ _ _ _ _ _ _ F_82f28 eq_refl D_neg) | intros md5 Hs5].
replace (bv_eqb (11%bv : bv 5) 0) with false by reflexivity. cbn beta iota. fsa_gsimp. rewrite fsa_getr0.
replace (v_addi (Z_to_bv 64 0x82f28) 4) with (Z_to_bv 64 0x82f2c) by (apply bv_eq; vm_compute; reflexivity).
(* or a0, a1, a0 *)
eapply fsa_step; [exact (step_or tfibsegs _ _ _ _ _ _ _ _ F_82f2c eq_refl D_or) | intros md6 Hs6].
replace (bv_eqb (10%bv : bv 5) 0) with false by reflexivity. cbn beta iota. fsa_gsimp.
rewrite (fsa_sat cnt k Hc Hk64).
replace (v_addi (Z_to_bv 64 0x82f2c) 4) with (Z_to_bv 64 0x82f30) by (apply bv_eq; vm_compute; reflexivity).
(* auipc a1, 0x21 *)
eapply fsa_step; [exact (step_auipc tfibsegs _ _ _ _ _ _ _ F_82f30 eq_refl D_auipc_a1_21) | intros md7 Hs7].
replace (bv_eqb (11%bv : bv 5) 0) with false by reflexivity. cbn beta iota.
replace (v_addi (Z_to_bv 64 0x82f30) 4) with (Z_to_bv 64 0x82f34) by (apply bv_eq; vm_compute; reflexivity).
(* sd a0, 0x290(a1): the one static store *)
eapply (fsa_step_sd W _ mem md7 _ _ _ _ _ G_FAIL _ F_82f34 eq_refl D_sd_fail).
{ fsa_gsimp. apply bv_eq; vm_compute; reflexivity. }
{ unfold G_FAIL; lia. }
{ unfold G_FAIL; lia. }
{ apply store_ok_wseg. vm_compute. reflexivity. }
intros md8 mem8 Hs8 Hout Hin.
replace (v_addi (Z_to_bv 64 0x82f34) 4) with (Z_to_bv 64 0x82f38) by (apply bv_eq; vm_compute; reflexivity).
(* ret *)
eapply fsa_step; [exact (step_jalr tfibsegs _ _ _ _ _ _ _ _ F_82f38 eq_refl D_ret) | intros md9 Hs9].
replace (bv_eqb (0%bv : bv 5) 0) with true by reflexivity. cbn beta iota.
lazymatch goal with |- context [v_jalr ?x (bv_signed ?i)] => replace (v_jalr x (bv_signed i)) with (YK11.getr regs 1) end.
2:{ fsa_gsimp. symmetry. exact Hra. }
apply SRr_ret. split; [reflexivity|]. do 3 eexists.
refine (conj _ (conj _ (conj eq_refl (conj Hout _)))).
- eapply same_but_materialized_trans; [exact Hs1|]; eapply same_but_materialized_trans; [exact Hs2|];
  eapply same_but_materialized_trans; [exact Hs3|]; eapply same_but_materialized_trans; [exact Hs4|];
  eapply same_but_materialized_trans; [exact Hs5|]; eapply same_but_materialized_trans; [exact Hs6|];
  eapply same_but_materialized_trans; [exact Hs7|]; eapply same_but_materialized_trans; [exact Hs8 | exact Hs9].
- repeat (apply fsa_pres_upd; [| vm_compute; lia]); apply fsa_pres_refl.
- intros j Hj. rewrite (Hin j Hj). fsa_gsimp.
rewrite unsigned_lit_small by (unfold SIZE_MAXZ; destruct (cnt + k <? 2 ^ 64) eqn:E;
  [apply Z.ltb_lt in E | ]; lia).
reflexivity.
Qed.

(* the statics after a store into one of them *)
Lemma val_mem_store_hit : forall (W : world tfibsegs) mem' g v,
  0xa1000 <= g -> g + 8 <= 0x5fd000 ->
  (forall k, (k < 8)%nat -> mem' (Z_to_bv 64 (g + Z.of_nat k)) = Some (Z_to_bv 8 (le_byte v 8 k))) ->
  val_mem tfibsegs (mrestrict (w_H W) mem') g 8 v.
Proof.
intros W mem' g v H1 H2 Hm k Hk. unfold mbyte, mrestrict. rewrite (fs_rw3_vis W (g + Z.of_nat k)) by lia.
rewrite (Hm k Hk). reflexivity.
Qed.
Lemma val_mem_store_miss : forall (W : world tfibsegs) mem mem' g a v,
  (forall x : word, ~ (g <= bv_unsigned x < g + 8) -> mem' x = mem x) ->
  0 <= a -> a + 8 <= 2 ^ 64 -> (a + 8 <= g \/ g + 8 <= a) ->
  val_mem tfibsegs (mrestrict (w_H W) mem) a 8 v -> val_mem tfibsegs (mrestrict (w_H W) mem') a 8 v.
Proof.
intros W mem mem' g a v Hout Ha Ha8 Hd Hv k Hk. specialize (Hv k Hk). unfold mbyte, mrestrict in *.
rewrite (Hout (Z_to_bv 64 (a + Z.of_nat k))); [exact Hv|]. rewrite unsigned_lit_small by lia. lia.
Qed.
Lemma fs_glob_reset : forall (W : world tfibsegs) mem mem' live peak cnt fail,
  fs_glob tfibsegs W mem live peak cnt fail ->
  (forall x : word, ~ (G_PEAK <= bv_unsigned x < G_PEAK + 8) -> mem' x = mem x) ->
  (forall k, (k < 8)%nat -> mem' (Z_to_bv 64 (G_PEAK + Z.of_nat k)) = Some (Z_to_bv 8 (le_byte live 8 k))) ->
  fs_glob tfibsegs W mem' live live cnt fail.
Proof.
intros W mem mem' live peak cnt fail (G1 & G2 & G3 & G4 & R) Hout Hin.
unfold fs_glob, fs_glob_at. unfold G_LIVE, G_PEAK, G_COUNT, G_FAIL in *.
split; [apply (val_mem_store_miss W mem mem' 0x5daae0); [exact Hout | lia | lia | lia | exact G1]|].
split; [apply (val_mem_store_hit W mem' 0x5daae0); [lia | lia | exact Hin]|].
split; [apply (val_mem_store_miss W mem mem' 0x5daae0); [exact Hout | lia | lia | lia | exact G3]|].
split; [apply (val_mem_store_miss W mem mem' 0x5daae0); [exact Hout | lia | lia | lia | exact G4]|].
lia.
Qed.
Lemma fs_glob_fail : forall (W : world tfibsegs) mem mem' live peak cnt fail fail',
  fs_glob tfibsegs W mem live peak cnt fail -> 0 <= fail' < 2 ^ 64 ->
  (forall x : word, ~ (G_FAIL <= bv_unsigned x < G_FAIL + 8) -> mem' x = mem x) ->
  (forall k, (k < 8)%nat -> mem' (Z_to_bv 64 (G_FAIL + Z.of_nat k)) = Some (Z_to_bv 8 (le_byte fail' 8 k))) ->
  fs_glob tfibsegs W mem' live peak cnt fail'.
Proof.
intros W mem mem' live peak cnt fail fail' (G1 & G2 & G3 & G4 & R) Hf Hout Hin.
unfold fs_glob, fs_glob_at. unfold G_LIVE, G_PEAK, G_COUNT, G_FAIL in *.
split; [apply (val_mem_store_miss W mem mem' 0xa41c0); [exact Hout | lia | lia | lia | exact G1]|].
split; [apply (val_mem_store_miss W mem mem' 0xa41c0); [exact Hout | lia | lia | lia | exact G2]|].
split; [apply (val_mem_store_miss W mem mem' 0xa41c0); [exact Hout | lia | lia | lia | exact G3]|].
split; [apply (val_mem_store_hit W mem' 0xa41c0); [lia | lia | exact Hin]|].
lia.
Qed.

Lemma fsa_present_of : forall (mem' : word -> option byte) g (f : nat -> byte),
  (forall k, (k < 8)%nat -> mem' (Z_to_bv 64 (g + Z.of_nat k)) = Some (f k)) ->
  forall x : word, g <= bv_unsigned x < g + 8 -> mem' x <> None.
Proof.
intros mem' g f Hin x Hx. replace x with (Z_to_bv 64 (g + Z.of_nat (Z.to_nat (bv_unsigned x - g)))).
2:{ rewrite Z2Nat.id by lia. replace (g + (bv_unsigned x - g)) with (bv_unsigned x) by lia. apply Z_to_bv_bv_unsigned. }
rewrite Hin by lia. discriminate.
Qed.

(* the journal's acceptance of a write into a static byte a, from the three facts the static-store arm asks:
   inFP FS_PSTAT_FP a, in_img tfibsegs a, a not runtime-owned. Written against the arm's SHAPE, not its position,
   so it closes ajournal_after_write's write premise for either one-text form of awr_byte. *)
Ltac fsa_awr_static_core :=
  unfold awr_byte;
  repeat match goal with |- _ \/ _ => first [left; solve [repeat split; assumption] | right] end;
  repeat split; assumption.
Ltac fsa_awr_static := first [solve [fsa_awr_static_core] | solve [left; fsa_awr_static_core]].

(* the post of a counter whose run stores into the one static g and changes nothing else *)
Lemma fsa_store_post : forall B ly S U (W : world tfibsegs) regs mem md ch regs' mem' md' g
  (Q : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  fs_img_facts tfibsegs B ->
  fpreU tfibsegs B STK_fuzz_alloc ly S U W regs mem md ch ->
  In (g, g + 8) FS_PSTAT_FP ->
  same_but_materialized md md' -> aregs_preserved regs regs' ->
  (forall x : word, ~ (g <= bv_unsigned x < g + 8) -> mem' x = mem x) ->
  (forall x : word, g <= bv_unsigned x < g + 8 -> mem' x <> None) ->
  Q ly S W regs' mem' md' ->
  apost_baseU tfibsegs B STK_fuzz_alloc FS_PSTAT_FP regs ly S W mem md 0 U U Q W
    (mkCfg (YK11.mkst regs' (YK11.getr regs 1) mem' (YK11.seg_rom tfibsegs)) md').
Proof.
intros B ly S U W regs mem md ch regs' mem' md' g Q IMG PRE Hg Hsb HP Hout Hin HQ.
pose proof PRE as ((HAP & OK & PO) & RO).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (fs_pstat_not_owned tfibsegs B _ _ _ _ _ _ _ IMG) as PSF.
assert (HARU : ARU tfibsegs B ly S U W mem md) by (split; [exact HAR | split; [exact OK | exact PO]]).
pose proof (pstat_store_ARU B ly S U W mem mem' md g PSF HARU Hg Hout Hin) as HARU'.
pose proof HARU' as (HAR' & _ & PO').
assert (Gfp : forall a, g <= a < g + 8 -> inFP FS_PSTAT_FP a)
  by (intros a Ha; exists (g, g + 8); split; [exact Hg | cbn [fst snd]; exact Ha]).
assert (Gin : forall x : word, g <= bv_unsigned x < g + 8 -> inFP FS_PSTAT_FP (bv_unsigned x))
  by (intros x Hx; exact (Gfp _ Hx)).
assert (HJ0 := ajournal_init tfibsegs B STK_fuzz_alloc FS_PSTAT_FP ly S W regs (unpoison U mem) md ch HAP).
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (g <= a < g + 8) ->
  aview tfibsegs (w_H W) (unpoison U mem') a = aview tfibsegs (w_H W) (unpoison U mem) a).
{ intros a Ha Hn. apply aview_at. unfold unpoison.
  destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))); [reflexivity|].
  apply Hout. rewrite unsigned_lit_small by lia. exact Hn. }
assert (PRES : forall a, apresent (w_H W) (unpoison U mem) a -> apresent (w_H W) (unpoison U mem') a).
{ intros a (Hh & b & Hb). split; [exact Hh|].
  destruct (Z_lt_le_dec (bv_unsigned (Z_to_bv 64 a)) g) as [L|L];
    [| destruct (Z_lt_le_dec (bv_unsigned (Z_to_bv 64 a)) (g + 8)) as [L'|L']].
  - exists b. unfold unpoison in Hb |- *. destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))); [exact Hb|].
    rewrite (Hout (Z_to_bv 64 a) ltac:(lia)). exact Hb.
  - rewrite (pstat_unpoison_id B ly S U W mem md mem' (Z_to_bv 64 a) HARU (Gin (Z_to_bv 64 a) ltac:(lia))).
    destruct (mem' (Z_to_bv 64 a)) as [b'|] eqn:E; [exists b'; reflexivity | exfalso; exact (Hin (Z_to_bv 64 a) ltac:(lia) E)].
  - exists b. unfold unpoison in Hb |- *. destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))); [exact Hb|].
    rewrite (Hout (Z_to_bv 64 a) ltac:(lia)). exact Hb. }
assert (WR : forall a, g <= a < g + 8 -> inFP FS_PSTAT_FP a /\ in_img tfibsegs a /\ ~ Exists (in_zr a) (as_owned_static B)).
{ intros a Ha. pose proof (pstat_bounds a (Gfp a Ha)) as Hb.
  split; [exact (Gfp a Ha)|]. split; [exact (fs_rw3_img a Hb) | exact (PSF a (Gfp a Ha))]. }
unfold apost_baseU, fpostU.
exists ly, S, regs', mem', md'. split; [reflexivity|].
split.
{ rewrite (same_but_materialized_wvb md md' Hsb).
  apply (ajournal_materialize tfibsegs B LAWS fs_segs_low).
  eapply (ajournal_after_write tfibsegs B LAWS fs_segs_low) with (Wr := fun a => g <= a < g + 8).
  all: first
    [ solve [exact HJ0]
    | solve [exact KEEP]
    | solve [exact PRES]
    | solve [apply same_but_materialized_refl]
    | solve [intros a Ha; destruct (WR a Ha) as (Hfp & Himg & Hno); fsa_awr_static]
    | solve [exact HAR']
    | solve [exact HQT]
    | solve [lazymatch goal with |- (_ <= _)%Z => lia end]
    | solve [lazymatch goal with |- @eq _ _ _ => reflexivity end] ]. }
split; [exact OK|]. split; [exact PO'|]. split; [exact HP | exact HQ].
Qed.

End w.

(* ======== the two static-writing counters, with the build's image facts as the Section hypothesis ======== *)
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* S0's image facts (FSH_Rt.v fs_img_facts; owner a Theorem Labs lane / S0, final instance proved once for fs's TfibB); only its
   first conjunct is used, through FSH_Gen.fs_pstat_not_owned: no byte of FS_PSTAT_FP is runtime-owned *)
Hypothesis IMG : fs_img_facts tfibsegs B.

(* fuzz_alloc_peak_reset 0x82f04 (alloc.c:131-134): g_peak = g_live *)
Theorem fuzz_alloc_peak_reset_ok : @fuzz_alloc_peak_reset_spec fx rc SK tfibsegs B.
Proof.
intros ly S U W regs mem md ch live peak cnt fail PRE FH GL.
pose proof PRE as ((HAP & OK & PO) & RO). pose proof HAP as (HAR & Hra & _).
pose proof GL as (G1 & G2 & G3 & G4 & GR).
unfold cfg_at.
eapply SRr_mono; [exact (fsa_reset_walk W regs mem md live G1 ltac:(lia) Hra) |].
intros W' c' _ (-> & regs' & md' & mem' & Hsb & HP & -> & Hout & Hin).
apply (fsa_store_post B ly S U W regs mem md ch regs' mem' md' G_PEAK _ IMG PRE
  ltac:(unfold FS_PSTAT_FP, G_PEAK; cbn [In]; right; right; left; reflexivity)
  Hsb HP Hout (fsa_present_of mem' G_PEAK _ Hin)).
cbv beta. split; [reflexivity|]. split; [exact (fs_glob_reset W mem mem' live peak cnt fail GL Hout Hin) | exact FH].
Qed.

(* fuzz_alloc_fail 0x82f18 (alloc.c:138-141): g_fail_at = g_count + k, saturating at SIZE_MAX *)
Theorem fuzz_alloc_fail_ok : @fuzz_alloc_fail_spec fx rc SK tfibsegs B.
Proof.
intros ly S U W regs mem md ch live peak cnt fail k PRE FH GL Hk Hk64.
pose proof PRE as ((HAP & OK & PO) & RO). pose proof HAP as (HAR & Hra & _).
pose proof GL as (G1 & G2 & G3 & G4 & GR).
unfold cfg_at.
eapply SRr_mono; [exact (fsa_fail_walk W regs mem md cnt k G3 ltac:(lia) Hk Hk64 Hra) |].
intros W' c' _ (-> & regs' & md' & mem' & Hsb & HP & -> & Hout & Hin).
apply (fsa_store_post B ly S U W regs mem md ch regs' mem' md' G_FAIL _ IMG PRE
  ltac:(unfold FS_PSTAT_FP, G_FAIL; cbn [In]; left; reflexivity)
  Hsb HP Hout (fsa_present_of mem' G_FAIL _ Hin)).
cbv beta. split; [reflexivity|]. split; [exact FH|].
apply (fs_glob_fail W mem mem' live peak cnt fail _ GL); [| exact Hout | exact Hin].
unfold SIZE_MAXZ. destruct (cnt + k <? 2 ^ 64) eqn:E; [apply Z.ltb_lt in E|]; lia.
Qed.

End f.

Print Assumptions fuzz_alloc_live_ok.
Print Assumptions fuzz_alloc_peak_ok.
Print Assumptions fuzz_alloc_peak_reset_ok.
Print Assumptions fuzz_alloc_fail_ok.
