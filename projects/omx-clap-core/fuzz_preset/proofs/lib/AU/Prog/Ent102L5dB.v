(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset, image B' (asan-ubsan, harness fix #102 pin sha256
   d663f82d7f488d30f8e8d7496cb814e595a2f3cbbf16bde81a65cb3ea9af0994): SEGMENT L5d of the walk of
   LLVMFuzzerTestOneInput (B' 0x816cc): cut_crs1 (+0x320, B' 0x819ec) -> cut_free (+0x1bc, B' 0x81888), the one
   `j` (slot 200, `Jal 0 (-356)`). Proves seg_L5d_stmt of the B' cut file lib/AU/Ent102CutsB.v, read at
   commit 8422ba84f257 (no DW, ec_pjf, ec_inv over a spent wild budget wk, the
   journal `exists WS, ajournal_xw .. WS /\ wbudget [] wk WS`; cut_crs1 at ec_wk_crs1, cut_free at ec_wk_free).
   First PORTED by port/a2b.py (sha256 f5113cbc90e503da) from lib/A/Prog/Ent102L5dA.v (a Theorem Labs lane's Qed proof on A',
   a working branch fcf2f3385c7); re-proved on the exact-position cuts: the `j` emits no event, so
   cut_crs1's position (e_os E ++ [trp], its index), `ec_ranout E trp = false` and `e_n E <= EC_NMAX` are cut_free's,
   carried unchanged; cut_free's accepted-arm tie `fst (jr_run (e_sm E) (e_x E) []) = Some t` is cut_crs1's
   `ck_read (e_x E) = Some t` by the record's lib/AU/Ent102PosB.v ec_rd_ck_read at ec_pre's
   `e_sm E = ReaderRes.jr_strtod` (l5d_inv_sm).
   - LISTING: lib/B/Listing_prog.v (B_prog_listing, pin d663f82d) with lib/B/Ent102PLB.PL_102_B; generic over
     `{PA : PAImg B_prog_listing}` (route b). Slot 200 (+0x320) is PW 0xe9dff06f on B' as on A' (the `j` is
     pc-relative inside the body, so the word and both offsets 0x320 / 0x1bc are the same on both images).
   - ec_inv BY TYPE (lib/AU/Prog/Ent102CallB.v's ec_conj_split / ec_inv_pre): only the journal reads the model; the
     `j` is a no-call stretch, so l5d_inv_wvb cites the cut file's shared ec_inv_wk_grow (materialize, the budget
     kept, wk' = wk since ec_wk_free is ec_wk_crs1) and carries every other conjunct by its type. l5d_inv_sm takes
     ec_pre's strtod conjunct by type.
   - ec_read_fd: lib/A/Ent102FdA.v, generic over the segments.
   rule 24: proves function LLVMFuzzerTestOneInput (reuse search: a Theorem Labs lane record, the internal file idx-llvm-newpin.txt
   exit=0; NEW walk on the #102 pins; proof-index seg_L5d_B: 0 hits, CONFIRM), segment L5d on B'. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK1d YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0lawscf YGcallcf YGcallScf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog Ent102PLB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import Ent102CutsB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Ent102FdA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Ent102PosB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.Prog Require Import Ent102CallB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

Section L5d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {PA : @PAImg rc B_prog_listing}.
Variable B : asyms.
Variable SK : YI16.sink_head.
Variables EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP : Z.
Variable EC_SIO : reader -> Prop.
Variable EC_SIO_IMG : Z -> Prop.
Variable ec_ccut : ecx -> nat -> Z.
Variable ec_lcut : ecx -> nat -> Z.

#[local] Notation SEGS := (@pa_segs rc B_prog_listing PA).
#[local] Notation BASE := (@pa_val rc B_prog_listing PA A_TEXT).
#[local] Notation PST := (@prh_pst PI).
#[local] Notation ARc := (@ec_ARx rc ci cp B_prog_listing PA B).
(* the cuts of this lane are after check_no_overread's frees: ec_inv at wle' (Ent102CutsB.v ec_invR) *)
#[local] Notation WLE' := (wle' SEGS (@YGcfRehidePost.RZ_cf rc)).
#[local] Notation ECINV := (@ec_invR fx rc ci cp PI RL B_prog_listing PA B SK EC_RA EC_EMPTY EC_SIO WLE').

Lemma l5d_fetch : fetch_word SEGS (Z_to_bv 64 (BASE + 0x320)) = Some (Z_to_bv 32 0xe9dff06f).
Proof.
exact (pa_fetch_pw (L := B_prog_listing) (PL := PL_102_B) (PI := PA) 0x320 0xe9dff06f ltac:(vm_compute; reflexivity)).
Qed.

Lemma l5d_dec : decode_any (Z_to_bv 32 0xe9dff06f) = Some (Jal 0 (Z_to_bv 21 (-356)), 4%Z).
Proof. vm_compute. f_equal. f_equal. f_equal. all: apply bv_eq; reflexivity. Qed.

Lemma l5d_j : forall (fy : YK11.FPState) (W : world SEGS) regs mem md Q,
  (forall X, SRr SEGS W (@cfg_at fy SEGS (BASE + 0x1bc) regs mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (@cfg_at fy SEGS (BASE + 0x320) regs mem md) Q.
Proof.
intros fy W regs mem md Q HK.
unfold cfg_at, YG0d.w64.
eapply (SRr_step SEGS pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  exact (step_jal_x0 SEGS regs _ (mrestrict (w_H W) mem) (seg_rom SEGS) _ _ l5d_fetch
    (not_ecall_of_decode _ _ _ l5d_dec ltac:(discriminate)) l5d_dec).
- intros model' Hsame. rewrite (same_but_materialized_wvb md model' Hsame).
  cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
  rewrite YCbn.btgt_lit.
  replace (bv_signed (Z_to_bv 21 (-356))) with (-356) by (vm_compute; reflexivity).
  replace (BASE + 0x320 + -356) with (BASE + 0x1bc) by lia.
  exact (HK (m_vm_materialized model')).
Qed.

(* ec_inv's journal conjunct, BY TYPE (ec_conj_pick) *)
Lemma l5d_inv_jw : forall E fk ly S Hp (W : world SEGS) mem md own Lam peak cnt ran k os_c i_c wk,
  ECINV E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk ->
  exists WS, ajournal_xwR (SK := SK) SEGS B PST ARc WLE' LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E) (e_mem E)
    (e_md E) own ly S Hp W mem md k WS /\ YCbqGwild.wbudget [] wk WS.
Proof.
intros E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk H.
unfold ec_invR in H. ec_conj_pick H.
Qed.

(* ec_inv at the `j`'s materialized model: only the journal reads md. The `j` is a NO-CALL stretch, so the cut file's
   shared ec_inv_wk_grow carries the budgeted journal to the materialized model at the same spent budget (wk' = wk;
   ec_wk_free is ec_wk_crs1). Every other conjunct (the exact room position at os_c / i_c among them) is carried BY
   ITS TYPE (ec_conj_split, Ent102CallB.v), never by its position *)
Lemma l5d_inv_wvb : forall E fk ly S Hp (W : world SEGS) mem md own Lam peak cnt ran k os_c i_c wk X,
  ECINV E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk ->
  ECINV E fk ly S Hp W mem (with_vm_backing (m_vm_lazy md) X md) own Lam peak cnt ran k os_c i_c wk.
Proof.
intros E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk X H.
destruct (l5d_inv_jw E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk H) as (WS & HJ & HB).
assert (LAWS : AR_laws_x SEGS B ARc cf_head) by exact (AR_laws_x_xs SEGS B (AR_laws_ok_cf SEGS B)).
destruct (ec_inv_wk_growR B SK WLE' LAWS E own ly S Hp W mem md k WS wk wk X HJ HB (le_n wk)) as (WS' & HJm & HBm).
unfold ec_invR in H |- *. ec_conj_split H.
repeat match goal with |- _ /\ _ => split end.
all: first [ assumption | exists WS'; split; [exact HJm | exact HBm] ].
Qed.

(* ec_pre's run-model strtod, BY TYPE from ec_inv's ec_pre (Ent102CallB.ec_inv_pre, then ec_conj_pick) *)
Lemma l5d_inv_sm : forall E fk ly S Hp (W : world SEGS) mem md own Lam peak cnt ran k os_c i_c wk,
  ECINV E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk -> e_sm E = ReaderRes.jr_strtod.
Proof.
intros E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk H.
unfold ec_invR, ec_pre in H. ec_conj_pick H.
Qed.

Theorem seg_L5d_B :
  @seg_L5d_stmt fx rc ci cp PI RL B_prog_listing PA B SK EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG
    ec_ccut ec_lcut.
Proof.
unfold seg_L5d_stmt, ec_laneR.
intros E fk t D HYP W c Hcut.
pose proof HYP as HCC. apply ech_ccut_ok in HCC.
pose proof HYP as HLC. apply ech_lcut_ok in HLC.
destruct Hcut as (ly & S & Hp & regs & mem & md & own & Lam & peak & cnt & k & trp & Hat & Hinv & Hro & Hcc
  & Hlc & Hrkd & Hfrm & Hrd & HP & HN & HnM).
pose proof (proj2 (HCC E 9%nat 10%nat) ltac:(lia)) as Hc10.
pose proof (proj2 (HLC E 9%nat 10%nat) ltac:(lia)) as Hl10.
destruct Hat as (fy & Hfz & Hkept & ->).
(* a no-call lane: the plain SRr proof lifts to SRr' (YA0nH.SRr_SRr') *)
apply (SRr_SRr' SEGS (@YGcfRehidePost.RZ_cf rc)).
unfold EC_AR_CRS1, EC_BASE.
apply l5d_j. intros X.
apply SRr_ret.
(* cut_free at cut_crs1's own position (e_os E ++ [trp], the same index) and its ec_ranout = false: no event; the
   same spent wild budget (ec_wk_free is ec_wk_crs1) *)
exists ly, S, Hp, regs, mem, (with_vm_backing (m_vm_lazy md) X md), own, Lam, peak, cnt, k, D, trp, t.
split; [exists fy; split; [exact Hfz|]; split; [exact Hkept | reflexivity]|].
split; [exact (l5d_inv_wvb E fk ly S Hp W mem md own Lam peak cnt 0 k _ _ _ X Hinv)|].
split; [exact Hro|].
split; [lia|].
split; [lia|].
split; [exact Hrkd|].
split; [exact Hfrm|].
split; [exact HP|].
split; [exact (ec_read_fd SEGS _ _ (e_x E) t (ec_doc fk) D Hrd HN)|].
split; [exact (proj1 HnM)|].
split; [exact (proj2 HnM)|].
(* call_tail's accepted arm at the same t: the model's reading is ck_read under ec_pre's strtod tie
   (Ent102PosB.ec_rd_ck_read, the record's lemma) *)
rewrite (Ent102PosB.ec_rd_ck_read rc B_prog_listing PA E
  (l5d_inv_sm E fk ly S Hp W mem md own Lam peak cnt 0 k _ _ _ Hinv)).
exact Hrd.
Qed.

End L5d.

Check seg_L5d_B.
Print Assumptions seg_L5d_B.
