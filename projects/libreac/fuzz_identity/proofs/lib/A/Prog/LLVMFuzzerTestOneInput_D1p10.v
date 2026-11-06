(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YI08.v:162-174, 176-180;
   projects/cgif/cgif_file_fuzzer/proofs/lib/YN13.v:121-125; projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC1n.v:201-203, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_D1.v, with its module paths, module names and addresses changed; 397 of its 490 lines of code are new or changed and 5972 lines of the source are left out. *)
(* Phase 10 of segment D1 of LLVMFuzzerTestOneInput's ASan walk (0x80cd8..0x80d04): the two ingest results and
   the first three bytes of `id` and `again` agree, and the record's boundary inv_D1_end holds.
   The statement is d1_ph10 below; LLVMFuzzerTestOneInput_D1cut.v holds the predicates it uses. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentFrame IdentCJ IdentRo
IdentProgSig YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YK1g YK0w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv reac_identity_ingest.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import LLVMFuzzerTestOneInput_D1cut.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec reac_identity_ingest_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* YC4b turns lia's division and modulo handling off; the shadow arithmetic here needs it. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- Ph10's symbolic state at 0x80cd8 --------------------------------------------------------------------- *)
(* Atoms: 33 the address of `id` (mf+184), 34 the first two bytes of the identity (fw_milli), 35 its third byte
   (has_fw). `again` holds the same three bytes, so the three compares are decided. *)
Definition p10_mf : YP09.region := YP09.mkRegion (Some 9%nat) 184 192 184 184 [YP09.mkChunk 184 (CVal 8 (SOff 33 0))].
Definition p10_idr : YP09.region := YP09.mkRegion (Some 33%nat) 0 3 0 0
  [YP09.mkChunk 0 (CVal 2 (SOff 34 0)); YP09.mkChunk 2 (CVal 1 (SOff 35 0))].
Definition p10_agr : YP09.region := YP09.mkRegion (Some 20%nat) 0 3 0 0
  [YP09.mkChunk 0 (CVal 2 (SOff 34 0)); YP09.mkChunk 2 (CVal 1 (SOff 35 0))].
Definition p10_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
           (20%nat, mkAF 4096 (2 ^ 47) 0); (33%nat, mkAF 4096 (2 ^ 47) 0);
           (34%nat, mkAF 0 65535 0); (35%nat, mkAF 0 255 0)] [] [].
Definition ss_p10 : sstate := mkSS 0x5cc sr_atoms [p10_mf; p10_idr; p10_agr] None p10_facts.
Definition p10_extra (idb : list byte) (sf : Z) : list word :=
  map (Z_to_bv 64) [0; sf + V_id; RcIdentModel.fw_milli idb; RcIdentModel.bz (RcIdentModel.nthb idb 2)].


Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* The Section of LLVMFuzzerTestOneInput.v / _inv.v, in the same order. *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
#[local] Notation ECOMMON := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
(* What this segment takes, each with the name and type the contract's Section gives it (LLVMFuzzerTestOneInput.v). *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis HEV : EV_LLVMF <= EV_LIB.
Hypothesis HLIVE : LIVE_LLVMF <= LIVE_LIB.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis PSIG : ident_prog_sig_ok (PI := PI).
Hypothesis AMALLOC4 : amalloc04_rule SEGS B MT.
Hypothesis AFREE4 : afree04_rule SEGS B MT.
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA IS___asan_memcpy).
(* The allocator call traces (LLVMFuzzerTestOneInput.v, the contract's text). *)
Hypothesis HUMM : forall c, In c (LLVMF_MALLOC_CTX RA_LLVMF) ->
In (firstn kUnwindMax (pc_malloc_ra0 (as_code B)
:: flat_map (fun r => if r =? pc_malloc_ra0 (as_code B) then [] else [r]) c)) (as_universe B).
Hypothesis HUMF : forall c, In c (LLVMF_FREE_CTX RA_LLVMF) ->
In (firstn kUnwindMax (pc_free_ra0 (as_code B)
:: flat_map (fun r => if r =? pc_free_ra0 (as_code B) then [] else [r]) c)) (as_universe B).
(* cgif ACfh.v:162-164 *)
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  m_fds md' = m_fds md /\ m_fs md' = m_fs md.
(* the program callee (lib/A/Prog/reac_identity_ingest.v) *)
Hypothesis HING : treac_identity_ingest_spec B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
(* the cut file's predicates and facts, with this Section's parameters *)
#[local] Notation CTX := (D1ctx B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation RUNS := (D1S B MT LLVMF_STK).
#[local] Notation NUMS := (d1_nums B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS HSTK LAWS).
#[local] Notation INVD1 := (inv_D1_end B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).



(* ---- the two-byte and one-byte reads of the identity ------------------------------------------------------ *)
Lemma d1_le2 : forall b0 b1, 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  le_byte b0 1 0 = le_byte (b0 + 256 * b1) 2 0 /\ le_byte b1 1 0 = le_byte (b0 + 256 * b1) 2 1.
Proof.
intros b0 b1 H0 H1. unfold le_byte.
change (2 ^ (8 * Z.of_nat 1)) with 256. change (2 ^ (8 * Z.of_nat 2)) with 65536.
change (8 * Z.of_nat 0) with 0. change (8 * Z.of_nat 1) with 8.
rewrite !Z.shiftr_0_r. rewrite (Z.mod_small b0 256) by lia. rewrite (Z.mod_small b1 256) by lia.
rewrite (Z.mod_small (b0 + 256 * b1) 65536) by lia.
rewrite (Z.shiftr_div_pow2 (b0 + 256 * b1) 8) by lia. change (2 ^ 8) with 256.
replace (b0 + 256 * b1) with (b0 + b1 * 256) by lia.
split.
- rewrite Z_mod_plus_full. rewrite (Z.mod_small b0 256) by lia. reflexivity.
- rewrite Z.div_add by lia. rewrite (Z.div_small b0 256) by lia. rewrite Z.add_0_l.
  rewrite (Z.mod_small b1 256) by lia. reflexivity.
Qed.
Lemma d1_val1_of_bytes : forall (W : world SEGS) mem a bs j, bytes_at8 W mem a bs -> (j < length bs)%nat ->
  val_mem SEGS (rd W mem) (a + Z.of_nat j) 1 (RcIdentModel.bz (RcIdentModel.nthb bs j)).
Proof.
intros W mem a bs j Hb Hj. destruct (Hb j ltac:(rewrite length_map; exact Hj)) as [Hv _].
unfold RcIdentModel.bz, RcIdentModel.nthb.
replace (bv_unsigned (nth j bs (RcIdentModel.zb 0))) with (nth j (map (fun b : byte => bv_unsigned b) bs) 0);
[exact Hv|].
rewrite (nth_indep _ 0 (bv_unsigned (RcIdentModel.zb 0))) by (rewrite length_map; exact Hj). apply map_nth.
Qed.
Lemma d1_mb1 : forall m a v, val_mem SEGS m a 1 v -> mbyte SEGS m a = Some (Z_to_bv 8 (le_byte v 1 0)).
Proof.
intros m a v H. pose proof (H 0%nat ltac:(lia)) as H0. replace (a + Z.of_nat 0) with a in H0 by lia. exact H0.
Qed.
Lemma d1_val2_of_bytes : forall (W : world SEGS) mem a bs, bytes_at8 W mem a bs -> (2 <= length bs)%nat ->
  val_mem SEGS (rd W mem) a 2 (RcIdentModel.bz (RcIdentModel.nthb bs 0) +
                               256 * RcIdentModel.bz (RcIdentModel.nthb bs 1)).
Proof.
intros W mem a bs Hb Hl.
pose proof (d1_val1_of_bytes W mem a bs 0 Hb ltac:(lia)) as H0.
pose proof (d1_val1_of_bytes W mem a bs 1 Hb ltac:(lia)) as H1.
replace (a + Z.of_nat 0) with a in H0 by lia.
pose proof (SlotModel.bz_range (RcIdentModel.nthb bs 0)) as B0.
pose proof (SlotModel.bz_range (RcIdentModel.nthb bs 1)) as B1.
destruct (d1_le2 _ _ B0 B1) as [E0 E1].
intros k Hk. assert (Hk2 : (k = 0 \/ k = 1)%nat) by lia. destruct Hk2 as [-> | ->].
- replace (a + Z.of_nat 0) with a by lia. rewrite (d1_mb1 _ _ _ H0), E0. reflexivity.
- rewrite (d1_mb1 _ _ _ H1), E1. reflexivity.
Qed.

(* ---- Ph10's entry state at 0x80cd8 ------------------------------------------------------------------------ *)
Lemma d1_fw_range : forall idb, 0 <= RcIdentModel.fw_milli idb <= 65535.
Proof.
intros idb. unfold RcIdentModel.fw_milli.
pose proof (SlotModel.bz_range (RcIdentModel.nthb idb 0)). pose proof (SlotModel.bz_range (RcIdentModel.nthb idb 1)).
lia.
Qed.
Lemma d1_p10_entry : forall g pos mf (W : world SEGS) (regs : bvmap 5 word) mem idb,
  getr regs 2 = w64 mf -> getr regs 9 = w64 mf -> getr regs 20 = w64 (SFa g pos + V_again) ->
  alloc_ceiling + ASTACK <= mf -> mf + 320 <= 2 ^ 47 -> 2 ^ 46 <= mf -> mf mod 32 = 0 ->
  4096 <= SFa g pos -> SFa g pos + 1024 <= alloc_ceiling ->
  val_mem SEGS (rd W mem) (mf + 184) 8 (SFa g pos + V_id) ->
  bytes_at8 W mem (SFa g pos + V_id) idb -> bytes_at8 W mem (SFa g pos + V_again) idb ->
  length idb = RcIdentModel.ID_SIZE ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (p10_extra idb (SFa g pos)))) ss_p10
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x5cc)) mem (seg_rom SEGS))).
Proof.
intros g pos mf W regs mem idb R2 R9 R20 Hmf0 Hmf47 Hmf46 Hmf32 HSF0 HSF1 Hmfid Hid Hag Hlen.
pose proof asan_consts as (C1 & _).
assert (Has : ASTACK = 16384) by reflexivity.
set (E := Eimg (Ereg regs (p10_extra idb (SFa g pos)))).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (p10_extra idb (SFa g pos))) k)
  by (intros k Hk; subst E; apply Eimg_low; exact Hk).
assert (E2 : ew E 2 = w64 mf)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact R2).
assert (E9 : ew E 9 = w64 mf)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
assert (E20 : ew E 20 = w64 (SFa g pos + V_again))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact R20).
assert (E33 : ew E 33 = Z_to_bv 64 (SFa g pos + V_id))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (RcIdentModel.fw_milli idb))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb idb 2)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (VB : forall k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some k) = v)
  by (intros k v Hk Hv; cbn [base_val]; rewrite Hk; apply unsigned_lit_small; exact Hv).
pose proof (d1_fw_range idb) as Hfw.
pose proof (SlotModel.bz_range (RcIdentModel.nthb idb 2)) as Hb2.
unfold RcIdentModel.ID_SIZE in Hlen.
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|constructor]]].
  + unfold region_ok, p10_mf. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite (VB 9%nat mf E9) by (clear - Hmf46 Hmf47 C1; lia).
    split; [clear - Hmf46 Hmf47; lia|]. split; [clear - Hmf46 Hmf47; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ mf 184 8 (SOff 33 0) (SFa g pos + V_id));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold V_id; cbn; clear - HSF0 HSF1 C1; lia | lia | exact Hmfid].
  + unfold region_ok, p10_idr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite (VB 33%nat (SFa g pos + V_id) E33) by (unfold V_id; clear - HSF0 HSF1 C1; lia).
    split; [unfold V_id; clear - HSF0; lia|]. split; [unfold V_id; clear - HSF1 C1; lia|].
    split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val SEGS E _ (SFa g pos + V_id) 0 2 (SOff 34 0) (RcIdentModel.fw_milli idb));
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | cbn; clear - Hfw; lia | lia |].
      rewrite Z.add_0_r. apply (d1_val2_of_bytes W mem (SFa g pos + V_id) idb Hid). lia.
    * apply (chunk_ok_val SEGS E _ (SFa g pos + V_id) 2 1 (SOff 35 0)
        (RcIdentModel.bz (RcIdentModel.nthb idb 2)));
        [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | cbn; clear - Hb2; lia | lia |].
      replace (SFa g pos + V_id + 2) with (SFa g pos + V_id + Z.of_nat 2) by lia.
      apply (d1_val1_of_bytes W mem (SFa g pos + V_id) idb 2 Hid). lia.
  + unfold region_ok, p10_agr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite (VB 20%nat (SFa g pos + V_again) E20) by (unfold V_again; clear - HSF0 HSF1 C1; lia).
    split; [unfold V_again; clear - HSF0; lia|]. split; [unfold V_again; clear - HSF1 C1; lia|].
    split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val SEGS E _ (SFa g pos + V_again) 0 2 (SOff 34 0) (RcIdentModel.fw_milli idb));
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | cbn; clear - Hfw; lia | lia |].
      rewrite Z.add_0_r. apply (d1_val2_of_bytes W mem (SFa g pos + V_again) idb Hag). lia.
    * apply (chunk_ok_val SEGS E _ (SFa g pos + V_again) 2 1 (SOff 35 0)
        (RcIdentModel.bz (RcIdentModel.nthb idb 2)));
        [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | cbn; clear - Hb2; lia | lia |].
      replace (SFa g pos + V_again + 2) with (SFa g pos + V_again + Z.of_nat 2) by lia.
      apply (d1_val1_of_bytes W mem (SFa g pos + V_again) idb 2 Hag). lia.
- cbn [pairwise_disjoint all_disjoint].
  unfold extent_disjoint, p10_mf, p10_idr, p10_agr. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB 9%nat mf E9) by (clear - Hmf46 Hmf47 C1; lia).
  rewrite (VB 33%nat (SFa g pos + V_id) E33) by (unfold V_id; clear - HSF0 HSF1 C1; lia).
  rewrite (VB 20%nat (SFa g pos + V_again) E20) by (unfold V_again; clear - HSF0 HSF1 C1; lia).
  unfold V_id, V_again.
  repeat match goal with |- _ /\ _ => split end; try exact I;
  first [left; clear - Hmf0 HSF1 Has C1; lia | right; clear - Hmf0 HSF1 Has C1; lia].
- unfold facts_ok, p10_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split; exact I].
  assert (UB : forall k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E k) = v)
    by (intros k v Hk Hv; rewrite Hk; apply unsigned_lit_small; exact Hv).
  pose proof (UB 2%nat mf E2 ltac:(clear - Hmf46 Hmf47 C1; lia)) as U2.
  pose proof (UB 9%nat mf E9 ltac:(clear - Hmf46 Hmf47 C1; lia)) as U9.
  pose proof (UB 20%nat (SFa g pos + V_again) E20 ltac:(unfold V_again; clear - HSF0 HSF1 C1; lia)) as U20.
  pose proof (UB 33%nat (SFa g pos + V_id) E33 ltac:(unfold V_id; clear - HSF0 HSF1 C1; lia)) as U33.
  pose proof (UB 34%nat _ E34 ltac:(clear - Hfw; lia)) as U34.
  pose proof (UB 35%nat _ E35 ltac:(clear - Hb2; lia)) as U35.
  repeat match goal with |- _ /\ _ => split end; unfold afact_ok; cbn [af_lo af_hi af_al2];
  rewrite ?U2, ?U9, ?U20, ?U33, ?U34, ?U35;
  change (2 ^ 5) with 32; rewrite ?Z.pow_0_r, ?Z.mod_1_r;
  unfold V_id, V_again; clear - Hmf46 Hmf47 Hmf32 HSF0 HSF1 Hfw Hb2 C1;
  try lia; try exact I.
Qed.

Lemma d1_sh_off : forall f j, shadow_addr (f + 8 * j) = shadow_addr f + j.
Proof.
intros f j. unfold shadow_addr. rewrite (Z.mul_comm 8 j), Z.div_add by lia. lia.
Qed.
Lemma d1_hwb_length : forall inp i, length (SlotModel.rec_hwb inp i) = 8%nat.
Proof.
intros inp i. unfold SlotModel.rec_hwb.
assert (H : match SlotModel.rec_hw inp i with Some h => length h = 8%nat | None => True end).
{ induction i as [|i IH]; cbn [SlotModel.rec_hw]; [exact I|].
  destruct ((SlotModel.rec_addr inp i =? RcIdentModel.ADDR_REAC_VERSION) && (8 <=? SlotModel.rec_k inp i)) eqn:Hc;
  [|exact IH].
  apply andb_prop in Hc as [_ Hk]. apply Z.leb_le in Hk.
  rewrite length_firstn, SlotModel.rec_pl_length. lia. }
destruct (SlotModel.rec_hw inp i); [exact H | reflexivity].
Qed.

(* ---- Ph10: 0x80cd8 .. 0x80d04 ------------------------------------------------------------------------------ *)
Lemma d1_ph10 : forall g pos mf i ly2 S2 W2 regs2 mem2 md2 pl W3 c3,
  CTX g pos mf i ly2 S2 W2 regs2 mem2 md2 ->
  RUNS g pos mf i ly2 S2 W2 mem2 3 (BASE + 0x5cc)
    (mo_malloc MT (D1k g i) + mo_malloc MT (D1k g i + 1) + mo_free MT) [(pl, D1k g i)]
    (WR1 g pos mf) (P9 B g pos mf i pl) W3 c3 ->
  SRr SEGS W3 c3 (INVD1 g pos mf i pl).
Proof.
intros g pos mf i ly2 S2 W2 regs2 mem2 md2 pl W3 c3 HC HD.
pose proof (NUMS g pos mf i ly2 S2 W2 regs2 mem2 md2 HC) as (Hmf0 & Hmfb & Hmf32 & Hsp0al & H47 & HSTKm &
  (HSF0 & HSF1 & HSF64 & HSFapp & EFa) & (Hn & Hinp2 & Hine & Hp4096 & Hpce & Hpapp & Hnlen) & Hi64 & Hcur).
pose proof HC as (HJ & Hfrs & Hk & MLE & MOK & HEC & Hi & _ & _ & _ & HRL).
destruct HD as (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hfrs3 & Hperm3 & Hhs3 & MLE3 & KEEP3 & HP9).
destruct HP9 as ((R2 & R9 & R8 & R3 & R4 & R19 & R24) & R20 & R21 & R23 & R25 & R22 & R27 & VM136 & VM144 &
  VM152 & VM160 & Hpl & SHbef & Hbef & SHag & Hag & Hid).
destruct HRL as (VM112 & Hfix & Hcur' & Hidat & Hhw & Hbl & Hmfid & Hmfag).
pose proof asan_consts as (C1 & _).
assert (Has : ASTACK = 16384) by reflexivity.
assert (Hmfr : 2 ^ 46 <= mf /\ mf + 320 <= 2 ^ 47) by (clear - Hmf0 Hmfb H47 C1 Has; lia).
(* the stack above mf, outside mf+136..168: as at the segment's start *)
assert (STK3 : forall a, mf <= a < e_sp0 g -> ~ (mf + 136 <= a < mf + 168) ->
  aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hn'. apply KEEP3; [clear - Ha Hmfb H47 Hmf0 C1 Has; lia | left; clear - Ha Hmf0 Has; lia |].
  apply d1_nwr_stack; [exact Hmf0 | exact HSF0 | exact HSF1 | clear - Ha; lia | exact Hn']. }
assert (Hmfid3 : val_mem SEGS (rd W3 mem3) (mf + 184) 8 (SFa g pos + V_id)).
{ unfold mf_id in Hmfid. apply (val_mem_moved SEGS (w_H W2) (w_H W3) mem2 mem3 (mf + 184) (mf + 184) 8 _); [|exact Hmfid].
  intros kk Hkk. apply STK3; clear - Hkk Hmfb; lia. }
pose proof (d1_p10_entry g pos mf W3 regs3 mem3 (m_id g (S i)) R2 R9 R20 Hmf0 (proj2 Hmfr) (proj1 Hmfr) Hmf32
  HSF0 HSF1 Hmfid3 Hid Hag (SlotModel.rec_id_length _ _)) as HS0.
set (E := Eimg (Ereg regs3 (p10_extra (m_id g (S i)) (SFa g pos)))) in HS0.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
unfold cfg_at. change (w64 (BASE + 0x5cc)) with (Z_to_bv 64 (BASE + 0x5cc)).
(* the start's ecommon, and what the segment kept of it *)
destruct HEC as (Rsp & Rs1 & Rs0 & _ & _ & Rgp & Rtp & Rs3 & V80 & V192 & V176 & Vra & Vs0 & V24 & V32 & V40 & V48 &
  V56 & V64 & V72 & V80b & V88 & V96 & V104 & Vmf24 & Vflag & HPRE & Hfds & Hfs & Hinb).
assert (HAE : env_agree 32 (Ereg regs3 (p10_extra (m_id g (S i)) (SFa g pos))) E)
  by (subst E; split; [intros kk Hkk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E34 : ew E 34 = Z_to_bv 64 (RcIdentModel.fw_milli (m_id g (S i))))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb (m_id g (S i)) 2)))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 3)).
pose proof (d1_shadow_lo (SFa g pos) HSF0 HSF1) as HSH.
assert (Hrq : e_n g <= req_size (e_n g)) by (apply req_size_pos; lia).
(* the blocks: the payload copy and the entry's *)
assert (Hbl3 : Permutation (ablocks B ly3 S3) ([(pl, D1k g i)] ++ ablocks B (e_ly g) (e_S g))).
{ destruct Hbl as [Hp2 _]. eapply Permutation_trans; [exact Hperm3|]. apply Permutation_app_head. exact Hp2. }
assert (Hinp3 : In (e_p g, e_n g) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym Hbl3)). apply in_or_app. right. exact Hine. }
assert (Hmeter : mo_malloc MT (D1k g i) + mo_malloc MT (D1k g i + 1) + mo_free MT <=
                 3 * (mo_malloc MT 256 + mo_free MT)).
{ pose proof (SlotModel.rec_k_range (e_pl g) i) as Hkr. change (SlotModel.rec_k (e_pl g) i) with (D1k g i) in Hkr.
  pose proof (mo_malloc_mono MT MTL (D1k g i) 256 ltac:(lia)).
  pose proof (mo_malloc_mono MT MTL (D1k g i + 1) 256 ltac:(lia)).
  pose proof (mo_malloc_nonneg MT MTL 256 ltac:(lia)). pose proof (mo_free_nonneg MT MTL). lia. }
pose proof (mo_malloc_nonneg MT MTL 256 ltac:(lia)) as HM0. pose proof (mo_free_nonneg MT MTL) as HF0.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & J10 & _).
unfold cfg_at. change (w64 (BASE + 0x5cc)) with (Z_to_bv 64 (BASE + 0x5cc)).
Ltac p10_post Er :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ex _ (restrict (w_H ?W) ?ms), HFr : frame_of _ _ _ _,
                      HJ3 : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  (* the run kept the memory (its three regions are read-only) *)
  let KEEP4 := fresh "KEEP4" in
  assert (KEEP4 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) _ a)
    by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
        apply (kept_of_frame _ _ (w_H W) _ (ms_mem ms) (fun _ => False) HFr); [|exact Ha|intros []];
        let bb := fresh in let wl := fresh in let wh := fresh in let aa := fresh in let Hin := fresh in
        let Hr := fresh in intros bb wl wh aa Hin Hr; cbn in Hin;
        repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; clear - Hr; lia |]); destruct Hin);
  clear HFr; repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end
  end.
assert (EE : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs3 r)
  by (intros nn rr Hnn Hrr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hrr).
(* the stack and frame bytes the segment did not write, from the start's memory to the end's *)
assert (SH0 : 0 <= shadow_addr (SFa g pos)) by (unfold shadow_addr, SHADOW_OFF; pose proof (Z.div_pos (SFa g pos) 8);
  clear - HSF0 H; lia).
destruct (SlotModel.rec_r_range (e_pl g) i) as [Er | Er]; rewrite Er in R21, R23;
(lazymatch type of R21 with getr _ _ = w64 ?v =>
  pose proof (st_ok_pi_pin_reg' E _ _ 21%bv v HS0
    ltac:(cbn [ms_regs restrict mkst]; rewrite R21; reflexivity) eq_refl) as HS1;
  pose proof (st_ok_pi_pin_reg' E _ _ 23%bv v HS1
    ltac:(cbn [ms_regs restrict mkst]; rewrite R23; reflexivity) eq_refl) as HS
 end);
clear HS0 HS1;
(paj_run_to_sh RUNTOP HS HJ3 0x5f8;
 [ unfold ss_p10, p10_mf, p10_idr, p10_agr; cbn [ss_mem];
   repeat (apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia |]); apply awr_ok_nil
 | p10_post Er ]);
(assert (KEEPS : forall a, 0 <= a < 2 ^ 64 ->
   (alloc_ceiling <= a \/ SFa g pos <= a < SFa g pos + 1024 \/
    shadow_addr (SFa g pos) <= a < shadow_addr (SFa g pos) + 128) ->
   ~ WR1 g pos mf a -> aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a)
   by (intros a Ha Hz Hw; rewrite (KEEP4 a Ha); exact (KEEP3 a Ha Hz Hw));
 assert (VMS : forall a (n : nat) v, mf <= a ->
   (a + Z.of_nat n <= mf + 136 \/ (mf + 168 <= a /\ a + Z.of_nat n <= e_sp0 g)) ->
   val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W3 (ms_mem ms)) a n v)
   by (intros a n v H1 H2 Hv; apply (val_mem_moved SEGS (w_H W2) (w_H W3) mem2 (ms_mem ms) a a n v); [|exact Hv];
       intros kk Hkk; rewrite (KEEP4 (a + kk)) by (clear - H1 H2 Hkk Hmf0 Hmfb H47 C1 Has; lia);
       apply STK3; [clear - H1 H2 Hkk Hmfb; lia | clear - H1 H2 Hkk; lia]);
 assert (FRK : forall off, 432 <= off < 1024 ->
   aview SEGS (w_H W3) (ms_mem ms) (SFa g pos + off) = aview SEGS (w_H W2) mem2 (SFa g pos + off))
   by (intros off Ho; apply KEEPS; [clear - Ho HSF0 HSF1 C1; lia | right; left; clear - Ho; lia |];
       apply d1_nwr_frame; [exact Hmf0 | exact HSF0 | exact HSF1 | exact HSFapp | clear - Ho; lia
       | unfold V_before, N_before; clear - Ho; lia | unfold V_again, N_again; clear - Ho; lia
       | unfold V_id, N_id; clear - Ho; lia]);
 assert (VMF : forall off (n : nat) v, 432 <= off -> off + Z.of_nat n <= 1024 ->
   val_mem SEGS (rd W2 mem2) (SFa g pos + off) n v -> val_mem SEGS (rd W3 (ms_mem ms)) (SFa g pos + off) n v)
   by (intros off n v H1 H2 Hv;
       apply (val_mem_moved SEGS (w_H W2) (w_H W3) mem2 (ms_mem ms) (SFa g pos + off) (SFa g pos + off) n v);
       [|exact Hv]; intros kk Hkk; rewrite <- Z.add_assoc; apply FRK; clear - H1 H2 Hkk; lia);
 assert (SHK : forall j, 19 <= j < 128 ->
   aview SEGS (w_H W3) (ms_mem ms) (shadow_addr (SFa g pos) + j) =
   aview SEGS (w_H W2) mem2 (shadow_addr (SFa g pos) + j))
   by (intros j Hj; apply KEEPS; [clear - Hj HSH SH0 C1; lia | right; right; clear - Hj; lia |];
       apply d1_nwr_fshadow; [exact Hmf0 | exact HSF0 | exact HSF1 | exact HSFapp | clear - Hj; lia
       | clear - Hj; lia | clear - Hj; lia]);
 assert (VM4 : forall a (n : nat) v, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
   val_mem SEGS (rd W3 mem3) a n v -> val_mem SEGS (rd W3 (ms_mem ms)) a n v)
   by (intros a n v H1 H2 Hv; apply (val_mem_moved SEGS (w_H W3) (w_H W3) mem3 (ms_mem ms) a a n v); [|exact Hv];
       intros kk Hkk; apply KEEP4; clear - H1 H2 Hkk; lia);
 assert (G4 : forall a bs, 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
   bytes_at8 W3 mem3 a bs -> bytes_at8 W3 (ms_mem ms) a bs)
   by (intros a bs H1 H2 Hb; apply (d1_bytes_moved W3 W3 mem3 (ms_mem ms) a bs); [|exact Hb];
       intros kk Hkk; apply KEEP4; clear - H1 H2 Hkk; lia);
 assert (SH4 : forall a n, 0 <= shadow_addr a -> shadow_addr a + (n + 7) / 8 <= 2 ^ 64 ->
   sh_blk W3 mem3 a n -> sh_blk W3 (ms_mem ms) a n)
   by (intros a n H1 H2 Hb; apply (d1_shblk_moved W3 W3 mem3 (ms_mem ms) a n); [|exact Hb];
       intros kk Hkk; apply KEEP4; clear - H1 H2 Hkk; lia);
 (* the registers at 0x80d04 *)
 prreg HS (2%bv : bv 5) Q2; prreg HS (9%bv : bv 5) Q9; prreg HS (8%bv : bv 5) Q8; prreg HS (3%bv : bv 5) Q3;
 prreg HS (4%bv : bv 5) Q4; prreg HS (19%bv : bv 5) Q19; prreg HS (22%bv : bv 5) Q22; prreg HS (27%bv : bv 5) Q27;
 prreg HS (21%bv : bv 5) Q21; prreg HS (23%bv : bv 5) Q23; prreg HS (25%bv : bv 5) Q25;
 rewrite (EE 2%nat 2%bv ltac:(lia) eq_refl), R2 in Q2; rewrite (EE 9%nat 9%bv ltac:(lia) eq_refl), R9 in Q9;
 rewrite (EE 8%nat 8%bv ltac:(lia) eq_refl), R8 in Q8; rewrite (EE 3%nat 3%bv ltac:(lia) eq_refl), R3 in Q3;
 rewrite (EE 4%nat 4%bv ltac:(lia) eq_refl), R4 in Q4; rewrite (EE 19%nat 19%bv ltac:(lia) eq_refl), R19 in Q19;
 rewrite (EE 22%nat 22%bv ltac:(lia) eq_refl), R22 in Q22; rewrite (EE 27%nat 27%bv ltac:(lia) eq_refl), R27 in Q27;
 rewrite E34 in Q21; rewrite E35 in Q25;
 destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as [Efd Efs];
 pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & J3 & _);
 (* ---- the boundary inv_D1_end at 0x80d04 ---- *)
 apply SRr_ret; unfold inv_D1_end, acut; pmkst HS;
 exists ly3, S3, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md3) mat md3);
 split; [reflexivity|];
 split; [exact HJ3|];
 split; [exact Hfrs3|];
 split; [unfold EV_LLVMF; clear - Hi64; lia|];
 split; [eapply (mo_le_mono MT MTL); [exact (mo_le_trans MT MTL _ _ _ _ _ MLE MLE3)|]; clear - Hmeter; nia|];
 split; [apply (mo_ok_step MT MTL S2 S3 (mo_malloc MT (D1k g i) + mo_malloc MT (D1k g i + 1) + mo_free MT));
         [|exact MLE3]; apply (mo_ok_le MT MTL _ _ _ MOK);
         unfold EV_LLVMF; clear - Hmeter Hi64; nia|];
 split; [
   unfold ecommon;
   split; [exact Q2|]; split; [exact Q9|]; split; [exact Q8|];
   split; [exact Hmfb|]; split; [exact Hmf32|]; split; [exact Q3|]; split; [exact Q4|];
   split; [exact Q19|];
   do 17 (split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | assumption]|]);
   split; [apply (VMF 1016 8%nat); [clear; lia | clear; lia | exact Vflag]|];
   split; [exact HPRE|];
   split; [intros fd; rewrite Efd; reflexivity|];
   split; [exact Efs|];
   apply (d1_bytes_moved W2 W3 mem2 (ms_mem ms) (e_p g) (e_pl g)); [|exact Hinb];
   intros kk Hkk; unfold SlotModel.nlen in Hnlen; rewrite Hnlen in Hkk;
   rewrite (J3 (e_p g) (e_n g) kk Hine Hinp3 ltac:(clear - Hkk Hrq; lia) (inFP_nil _));
   rewrite <- (J10 (e_p g) (e_n g) kk Hine Hinp2 ltac:(clear - Hkk Hrq; lia) (inFP_nil _)); reflexivity
 |];
 (* the P part of inv_D1_end *)
 pose proof HJ3 as (HAR3 & _);
 assert (Hinpl3 : In (pl, D1k g i) (ablocks B ly3 S3))
   by (apply (Permutation_in _ (Permutation_sym Hbl3)); left; reflexivity);
 destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinpl3) as (_ & Hpl4096 & Hplce & _ & _);
 pose proof (SlotModel.rec_k_range (e_pl g) i) as Hkr;
 pose proof (req_size_pos (D1k g i) ltac:(change (D1k g i) with (SlotModel.rec_k (e_pl g) i); lia)) as Hrqk;
 assert (Eid : shadow_addr (SFa g pos + V_id) = shadow_addr (SFa g pos) + 44)
   by (rewrite <- d1_sh_off; f_equal; unfold V_id; lia);
 assert (Ehw : shadow_addr (SFa g pos + V_hw) = shadow_addr (SFa g pos) + 54)
   by (rewrite <- d1_sh_off; f_equal; unfold V_hw; lia);
 assert (Ebf : shadow_addr (SFa g pos + V_before) = shadow_addr (SFa g pos) + 4)
   by (rewrite <- d1_sh_off; f_equal; unfold V_before; lia);
 assert (Eag : shadow_addr (SFa g pos + V_again) = shadow_addr (SFa g pos) + 14)
   by (rewrite <- d1_sh_off; f_equal; unfold V_again; lia);
 destruct Hidat as (_ & Hidz & Hidb);
 destruct Hhw as (Hw1 & Hw2 & Hw3 & Hw4);
 split; [
   (* P_body *)
   split; [exact Hi|];
   split; [split; [exact Hbl3 | constructor; [|constructor]];
           split; [exact Hpl4096 | cbn [snd]; clear - Hkr; lia]|];
   split; [apply G4; [clear - Hpl4096; lia | rewrite SlotModel.rec_pl_length;
                      change (SlotModel.rec_k (e_pl g) i) with (D1k g i) in *;
                      clear - Hplce Hrqk Hkr C1; lia | exact Hpl]|];
   split; [
     split; [apply G4; [unfold V_id; clear - HSF0; lia
                       | unfold m_id; rewrite SlotModel.rec_id_length; unfold RcIdentModel.ID_SIZE, V_id;
                         clear - HSF1 C1; lia | exact Hid]|];
     split;
     [ apply (d1_shzero_moved W2 W3 mem2 (ms_mem ms)); [|exact Hidz];
       intros kk Hkk; rewrite Eid, <- Z.add_assoc; apply SHK; unfold N_id in Hkk; clear - Hkk; lia
     | apply (d1_shblk_moved W2 W3 mem2 (ms_mem ms)); [|exact Hidb];
       intros kk Hkk; rewrite Eid, <- Z.add_assoc; apply SHK; unfold N_id in Hkk; clear - Hkk; lia ]
   |];
   split; [apply VMS; [clear; lia | clear; lia | exact VM112]|];
   split; [destruct Hfix as (F32 & F40 & F48 & F72 & F88 & F96 & F104 & F120 & F128);
           repeat split; apply VMS; first [assumption | clear; lia]|];
   split; [apply VMS; [clear; lia | right; clear - Hmfb; lia | exact Hmfid]|];
   split; [apply VMS; [clear; lia | right; clear - Hmfb; lia | exact Hmfag]|];
   split; [apply VM4; [clear - Hmf0 C1 Has; lia | clear - Hmfr; lia | exact VM136]|];
   split; [apply VM4; [clear - Hmf0 C1 Has; lia | clear - Hmfr; lia | exact VM144]|];
   split; [apply VM4; [clear - Hmf0 C1 Has; lia | clear - Hmfr; lia | exact VM152]|];
   split; [apply VM4; [clear - Hmf0 C1 Has; lia | clear - Hmfr; lia | exact VM160]|];
   split; [exact Q22|];
   pose proof (SlotModel.rec_c_range (e_pl g) (S i)) as Hcr; unfold m_cur; rewrite <- Hnlen; exact Hcr
 |];
 split; [
   (* hw_at *)
   split; [apply (VMF 432 4%nat); [clear; lia | clear; lia | exact Hw1]|];
   split; [apply (d1_bytes_moved W2 W3 mem2 (ms_mem ms)); [|exact Hw2];
           intros kk Hkk; unfold m_hwb in Hkk; rewrite d1_hwb_length in Hkk;
           replace (SFa g pos + V_hw + 4 + kk) with (SFa g pos + (436 + kk)) by (unfold V_hw; clear; lia);
           apply FRK; clear - Hkk; lia|];
   split;
   [ apply (d1_shzero_moved W2 W3 mem2 (ms_mem ms)); [|exact Hw3];
     intros kk Hkk; rewrite Ehw, <- Z.add_assoc; apply SHK; unfold N_hw in Hkk; clear - Hkk; lia
   | apply (d1_shblk_moved W2 W3 mem2 (ms_mem ms)); [|exact Hw4];
     intros kk Hkk; rewrite Ehw, <- Z.add_assoc; apply SHK; unfold N_hw in Hkk; clear - Hkk; lia ]
 |];
 split; [apply SH4; [rewrite Ebf; clear - SH0; lia | rewrite Ebf; unfold N_before; clear - HSH C1; lia
                   | exact SHbef]|];
 split; [apply SH4; [rewrite Eag; clear - SH0; lia | rewrite Eag; unfold N_again; clear - HSH C1; lia
                   | exact SHag]|];
 split; [exact Q21|];
 split; [apply G4; [unfold V_before; clear - HSF0; lia
                   | unfold m_id; rewrite SlotModel.rec_id_length; unfold RcIdentModel.ID_SIZE, V_before;
                     clear - HSF1 C1; lia | exact Hbef]|];
 split; [apply G4; [unfold V_again; clear - HSF0; lia
                   | unfold m_id; rewrite SlotModel.rec_id_length; unfold RcIdentModel.ID_SIZE, V_again;
                     clear - HSF1 C1; lia | exact Hag]|];
 split; [exact Q27|];
 split; [rewrite Q23, Er; reflexivity|];
 exact Q25).
Qed.

End c.
End b.
End a.
