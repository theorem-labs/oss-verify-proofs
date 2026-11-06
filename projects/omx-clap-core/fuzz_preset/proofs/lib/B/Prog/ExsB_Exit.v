(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* RELOCATED B -> B' (h-pre-b3's #102 row, 2026-10-29): the walk of origin/cold/h-pre-b3-exstring-b 5f62ea0b5c45 (OLD
   pin f8f98a95, unstripped twin 3b5e1a09) moved to the #102 pin B' (asan-ubsan d663f82d7f48, unstripped twin
   c90d4fa54d43, facts 8f3e7e1a07f1) by alreloc c4338d099cfb8025 (cold/c-asan-tools d99acc3edd9), on int102 with the kit
   decff67d721f. ex_string, ex_hex4 and ex_utf8 have equal instruction words on B and B' up to pc-relative fields,
   and every pc-relative target names the same symbol + offset. Every address in this file, in a comment or in a term, is the B' image's; a mention of the record image
   f8f98a95 below names the donor's image. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B (record f8f98a95), ex_string's two EXIT cuts (ExsB_Stmt.v):
     CUT_FAIL   B 0x847c0 `li a0,-1`, the epilogue (B 0x847c4-0x847f8), `ret` (B 0x847fc)
     CUT_QUOTE  B 0x84800 the closing quote: `beqz s2` (UBSan, to B 0x84834), o's shadow (B 0x84804-0x84810, report
                0x84844 via the slow block 0x84838), `sb zero,0(s2)`, `beq s3,-1` (UBSan), q's shadow (B 0x84820-0x84824,
                report 0x848d0 via 0x848cc), in->p = p + 1 (B 0x8482c), the epilogue, `ret`
   Each is ONE engine run (paj_run_x over B_prog_listing) from a fresh symbolic state whose stack region holds the
   thirteen words the prologue saved (ESB's frame clause), to `ret` (paj_ret_at). The report calls and the UBSan
   trap are unreachable INSIDE the runs: the trap's branches are decided by the atoms' ranges (o >= 4096, p < 2 ^ 47),
   o's shadow branch by its shadow entry (the scratch is addressable: ExsB_Lib.v es_inblk_ra) and q's by its (the
   real stack: es_stk_ra).
   Numerals: atoms 32 .. 44 (DERIVED: the saved words); 0x470, 0x4b0 (DERIVED: cut offsets); region bounds 1, 8
   (LENGTH); 2 ^ 44, 2 ^ 46, 2 ^ 47 (LENGTH: address-space widths); 0x7fffff800000 (DERIVED: CEIL_MAX, YM05.v:12). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB ExsB_Stmt ExsB_Model ExsB_Lib ExsB_Sym.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Existing Instance prh_img_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PI_prog_B).
#[local] Notation VAL := (@pa_val _ B_prog_listing PI_prog_B).
#[local] Notation BASE := (@pa_val _ B_prog_listing PI_prog_B A_TEXT).

Definition ES_CEIL : Z := 0x7fffff800000.
Definition ES_SPAN : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the FAIL state: the saved words only *)
Definition ss_fail : sstate := mkSS (ES_PC + 0x470) sr_atoms [ES_SAVR] None (mkFacts [] [] []).
(* the QUOTE state: the saved words, the output byte o (atom 18, written), in->p (atom 8 = q, written); s5 (21) is q's
   shadow address in the form the engine's shadow token reads *)
Definition ES_RO : YP09.region := YP09.mkRegion (Some 18%nat) 0 1 0 1 [].
Definition ES_RQ : YP09.region := YP09.mkRegion (Some 8%nat) 0 8 0 8 [].
Definition es_qshx : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 0) (SLit 3)) (SOff 22 0).
Definition ss_quote : sstate :=
  mkSS (ES_PC + 0x4b0) (sr_set sr_atoms 21%bv es_qshx) [ES_SAVR; ES_RO; ES_RQ] None
    (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF (2 ^ 46) (2 ^ 47 - 32) 3);
              (18%nat, mkAF 4096 ES_CEIL 0); (19%nat, mkAF 4096 ES_CEIL 0); (22%nat, mkAF SHADOW_OFF SHADOW_OFF 0)]
      [] []).
Definition es_SHq : list shent := [mkSHE 18 0 1; mkSHE 8 0 8].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis LAWS : AR_laws_x rsegs B ARx cf_head.
Hypothesis HHEAD : 8 <= cf_head.

(* after the epilogue's run: ra and the callee-saved registers from the saved words, sp back at the entry sp *)
Ltac es_exit_regs HS E Ex HEx R2 R3 R4 Hra :=
  lazymatch type of HS with st_ok_pi _ _ ?Ef _ (restrict _ ?ms) =>
  let EW := fresh "EW" in
  assert (EW : forall n, (n < 512)%nat -> ew Ef n = ew Ex n)
    by (intros n Hn; repeat (rewrite ew_ewset_other by lia); reflexivity);
  let ES := fresh "ES" in
  assert (ES : forall j, (j < 13)%nat -> ew Ef (32 + j) = getr (e_regs E) (Z_to_bv 5 (snd (nth j es_saved (0, 0)))))
    by (intros j Hj; try (rewrite EW by lia); rewrite HEx; apply es_xE_saved; exact Hj);
  let EX2 := fresh "EX2" in
  assert (EX2 : ew Ef 2 = Z_to_bv 64 (es_sp E - 144))
    by (try (rewrite EW by lia); rewrite HEx, (es_xE_reg _ _ _ 2%bv 2) by reflexivity; exact R2);
  let EX3 := fresh "EX3" in
  assert (EX3 : ew Ef 3 = getr (e_regs E) (Z_to_bv 5 3))
    by (try (rewrite EW by lia); rewrite HEx, (es_xE_reg _ _ _ 3%bv 3) by reflexivity; rewrite R3; f_equal;
        try (apply bv_eq; reflexivity));
  let EX4 := fresh "EX4" in
  assert (EX4 : ew Ef 4 = getr (e_regs E) (Z_to_bv 5 4))
    by (try (rewrite EW by lia); rewrite HEx, (es_xE_reg _ _ _ 4%bv 4) by reflexivity; rewrite R4; f_equal;
        try (apply bv_eq; reflexivity));
  let Rra := fresh "Rra" in es_reg0 HS (1%bv : bv 5) Rra;
  let ES0 := fresh "ES0" in
  pose proof (ES 0%nat ltac:(lia)) as ES0; cbn [Nat.add nth es_saved snd] in ES0;
  assert (XRA : v_jalr (getr (ms_regs ms) 1) 0 = getr (e_regs E) 1)
    by (rewrite Rra, es_den0, ES0;
        replace (Z_to_bv 5 1) with (1%bv : bv 5) by (apply bv_eq; reflexivity);
        unfold YK0s.ret_ok in Hra; exact Hra);
  assert (XAR : aregs_preserved (e_regs E) (ms_regs ms));
  [ apply es_exit_aregs;
    [ let Q := fresh "Q" in es_reg0 HS (Z_to_bv 5 2) Q; rewrite Q;
      rewrite (es_den_off Ef 2 144 (es_sp E - 144) EX2) by lia;
      replace (es_sp E - 144 + 144) with (es_sp E) by ring; unfold es_sp, spZ;
      replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity); apply Z_to_bv_bv_unsigned
    | let Q := fresh "Q" in es_reg0 HS (Z_to_bv 5 3) Q; rewrite Q, es_den0; exact EX3
    | let Q := fresh "Q" in es_reg0 HS (Z_to_bv 5 4) Q; rewrite Q, es_den0; exact EX4
    | let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj;
      assert (Hcase : (j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/ j = 10 \/ j = 11 \/
        j = 12)%nat) by lia;
      destruct Hcase as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]; cbn [nth es_saved snd];
      lazymatch goal with |- getr _ (Z_to_bv 5 ?z) = _ =>
        let Q := fresh "Q" in es_reg0 HS (Z_to_bv 5 z) Q; rewrite Q, es_den0 end;
      first [ exact (ES 1%nat ltac:(lia)) | exact (ES 2%nat ltac:(lia)) | exact (ES 3%nat ltac:(lia))
            | exact (ES 4%nat ltac:(lia)) | exact (ES 5%nat ltac:(lia)) | exact (ES 6%nat ltac:(lia))
            | exact (ES 7%nat ltac:(lia)) | exact (ES 8%nat ltac:(lia)) | exact (ES 9%nat ltac:(lia))
            | exact (ES 10%nat ltac:(lia)) | exact (ES 11%nat ltac:(lia)) | exact (ES 12%nat ltac:(lia)) ] ]
  | ] end.

(* ---- CUT_FAIL: B 0x847c0, return -1 ---- *)
Lemma es_cut_fail : forall E, CUT_FAIL B ARx SK E.
Proof.
intros E. unfold CUT_FAIL. intros lyc Sc Hpc regs memc mdc k HP HB HD.
pose proof (es_geom B ARx LAWS E HP) as G. unfold ES_GEOM in G. cbv zeta in G.
destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19).
pose proof HP as HP0. unfold ES_PRE in HP0. cbv zeta in HP0.
destruct HP0 as ((HFN & HROD & HTOP) & _).
pose proof HFN as (HAR0 & Hra & Hra4 & Hgp & Htp & _).
pose proof HB as (HJ & HWIN & HQP & HHp & HAB & HRK & HLED & HSAV & HC8 & HC16 & HC24 & R2 & R8 & R9 & R21 & R22 &
  R23 & R24 & R25 & R26 & R27 & R3 & R4 & HSc & HMN).
pose proof (es_cur_ar B ARx SK E lyc Sc Hpc regs memc mdc k HB) as HAR.
unfold es_SP in *.
remember (es_xE regs (e_regs E) []) as Ex eqn:HEx.
assert (HEI : img_env VAL A_LIM Ex) by (rewrite HEx; apply es_xE_env).
assert (HS : st_ok_pi rsegs VAL Ex ss_fail
  (restrict (w_H (e_W E)) (YK11.mkst regs (Z_to_bv 64 (BASE + (ES_PC + 0x470))) memc (YK11.seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_fail. apply (pa_entry_st_ok_full (fx := fx) (L := B_prog_listing) (PI := PI_prog_B)).
  - rewrite HEx. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. rewrite HEx.
    apply (es_savr_ok E (e_W E) regs memc []); [exact R2 | unfold es_SP; lia | unfold es_SP; lia | exact HSAV].
  - apply pairwise_disjoint_of_extents. cbn. repeat split.
  - cbn. repeat split. }
assert (SHOK : sh_ok rsegs (SLit 0) [] Ex (rdW (e_W E) memc)) by apply Forall_nil.
pose (RUN := paj_run_x_inv (SK := SK) (PL := PL_prog_B) (PI := PI_prog_B) B prh_pst ARx LAWS _ (es_plaw E)).
assert (HPM : es_P E memc) by exact HMN.
unfold cfg_at, w64. rewrite es_pc_eq.
paj_run_tok_x_inv RUN HS HJ SHOK HPM (0, 0).
{ intros a (rg & Hin & Har). cbn [ss_mem ss_fail In] in Hin. destruct Hin as [<- | []]. cbn in Har. lia. }
assert (MEQ : forall a, aview rsegs (w_H (e_W E)) (ms_mem ms) a = aview rsegs (w_H (e_W E)) memc a).
{ intros a. apply aview_eq_of. apply HFr. intros (rg & Hin & Har). cbn [ss_mem ss_fail In] in Hin.
  destruct Hin as [<- | []]. cbn in Har. lia. }
clear HF HG HFr.
es_reg0 HS (10%bv : bv 5) Ra0.
es_exit_regs HS E Ex HEx R2 R3 R4 Hra.
eapply (paj_ret_at (PL := PL_prog_B) (PI := PI_prog_B) (e_W E) _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. rewrite XRA.
apply (es_finish B ARx SK E lyc Sc Hpc (ms_regs ms) (ms_mem ms) _ k (-1)).
- apply (ajournal_x_materialize (SK := SK) rsegs B (@prh_pst prh_img_B) ARx LAWS B_prog_segs_low). exact HJ.
- intros a Ha Hn. rewrite MEQ. exact (HWIN a Ha Hn).
- exact XAR.
- exact HHp.
- exact HAB.
- exact HRK.
- exact HSc.
- exact HPM.
- apply (es_ledger_same B ARx LAWS lyc Sc Hpc (e_W E) memc mdc (ms_mem ms) _ _ _ _ _ _ _ HAR); [|exact HLED].
  intros a _. apply MEQ.
- rewrite Ra0. cbn [sv_denot]. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity.
- unfold ES_RES. rewrite exs_jr_decode, HD. split; [reflexivity|]. intros z Hz. rewrite MEQ. exact (HQP z Hz).
Qed.

(* ---- CUT_QUOTE: B 0x84800, the closing quote at p ---- *)
Lemma es_cut_quote : forall E, CUT_QUOTE B ARx SK E.
Proof.
intros E. unfold CUT_QUOTE. intros lyc Sc Hpc regs memc mdc k p acc HP HB HG GA Hpe Hq R18 R19.
pose proof (es_geom B ARx LAWS E HP) as G. unfold ES_GEOM in G. cbv zeta in G.
destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19).
pose proof HP as HP0. unfold ES_PRE in HP0. cbv zeta in HP0.
destruct HP0 as ((HFN & HROD & HTOP) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HINBs & _).
pose proof HFN as (HAR0 & Hra & Hra4 & Hgp & Htp & _).
pose proof HB as (HJ & HWIN & HQP & HHp & HAB & HRK & HLED & HSAV & HC8 & HC16 & HC24 & R2 & R8 & R9 & R21 & R22 &
  R23 & R24 & R25 & R26 & R27 & R3 & R4 & HSc & HMN).
pose proof (es_cur_ar B ARx SK E lyc Sc Hpc regs memc mdc k HB) as HAR.
pose proof HG as (HG1 & HG2 & HG3).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
unfold es_SP in *.
set (o := e_scr E + Z.of_nat (length acc)) in *.
(* the scratch block at the cut *)
destruct HINBs as (b & m & Hbm & Hbs & Hsm & Hhd).
assert (Hbm' : In (b, m) (ablocks B lyc Sc)) by (rewrite HAB; exact Hbm).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hbm') as (B1 & B2 & B3 & Bapp & Bpres & _).
assert (Hreq : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
assert (Ho : e_scr E <= o < e_scr E + es_len E + 1) by (unfold o; lia).
assert (HINBc : prhex_inblk B lyc Sc Hpc (e_scr E) (es_len E + 1)).
{ exists b, m. rewrite HAB, HHp. split; [exact Hbm|]. split; [exact Hbs|]. split; [exact Hsm | exact Hhd]. }
destruct (es_inblk_ra B ARx LAWS lyc Sc Hpc (e_W E) memc mdc _ _ _ _ _ _ _ (e_scr E) (es_len E + 1) HHEAD HAR HLED HINBc
  ltac:(lia)) as [HRAs _].
assert (HRAq : range_addressable (aview rsegs (w_H (e_W E)) memc) SHADOW_OFF (e_q E) 8).
{ apply (es_stk_ra B ARx LAWS lyc Sc Hpc (e_W E) memc mdc (e_q E) 8 HAR); lia. }
remember (es_xE regs (e_regs E) []) as Ex eqn:HEx.
assert (HEI : img_env VAL A_LIM Ex) by (rewrite HEx; apply es_xE_env).
assert (E2 : ew Ex 2 = Z_to_bv 64 (es_sp E - 144)) by (rewrite HEx, (es_xE_reg _ _ _ 2%bv 2) by reflexivity; exact R2).
assert (E8 : ew Ex 8 = Z_to_bv 64 (e_q E)) by (rewrite HEx, (es_xE_reg _ _ _ 8%bv 8) by reflexivity; exact R8).
assert (E18 : ew Ex 18 = Z_to_bv 64 o) by (rewrite HEx, (es_xE_reg _ _ _ 18%bv 18) by reflexivity; exact R18).
assert (E19 : ew Ex 19 = Z_to_bv 64 p) by (rewrite HEx, (es_xE_reg _ _ _ 19%bv 19) by reflexivity; exact R19).
assert (E22 : ew Ex 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite HEx, (es_xE_reg _ _ _ 22%bv 22) by reflexivity; exact R22).
assert (U2 : bv_unsigned (ew Ex 2) = es_sp E - 144) by (rewrite E2; apply unsigned_lit_small; lia).
assert (U8 : bv_unsigned (ew Ex 8) = e_q E) by (rewrite E8; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew Ex 18) = o) by (rewrite E18; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew Ex 19) = p) by (rewrite E19; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew Ex 22) = SHADOW_OFF) by (rewrite E22; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (HBx : U Ex (SOff 22 0) = SHADOW_OFF) by (rewrite (U_atom Ex 22 SHADOW_OFF E22) by (unfold SHADOW_OFF; lia); reflexivity).
assert (HS : st_ok_pi rsegs VAL Ex ss_quote
  (restrict (w_H (e_W E)) (YK11.mkst regs (Z_to_bv 64 (BASE + (ES_PC + 0x4b0))) memc (YK11.seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_quote. apply (pa_entry_st_ok_full (fx := fx) (L := B_prog_listing) (PI := PI_prog_B)).
  - apply regs_ok_pin; [rewrite HEx; apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
    unfold es_qshx. rewrite (es_denot_shx Ex 8 22 (e_q E) SHADOW_OFF E8 E22) by (unfold SHADOW_OFF; lia).
    exact R21.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + rewrite HEx. apply (es_savr_ok E (e_W E) regs memc []); [exact R2 | unfold es_SP; lia | unfold es_SP; lia | exact HSAV].
    + unfold region_ok, ES_RO. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U18. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros oo Hoo. apply (apresent_writable rsegs). apply (Bpres (o + oo)). lia.
    + unfold region_ok, ES_RQ. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U8. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros oo Hoo. apply (apresent_writable rsegs). apply HJpres. rewrite es_stk_val. lia.
  - apply pairwise_disjoint_of_extents. unfold extent_of_region, ES_SAVR, ES_RO, ES_RQ.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U8, U18.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U8, U18, U19, U22. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SHADOW_OFF, ES_CEIL. repeat split; lia. }
assert (SHOK : sh_ok rsegs (SOff 22 0) es_SHq Ex (rdW (e_W E) memc)).
{ unfold es_SHq. constructor; [|constructor; [|constructor]].
  - apply (shent_ok_of_range rsegs (w_H (e_W E)) memc Ex (SOff 22 0) 18 (e_scr E) (es_len E + 1) o 0 1 HRAs HBx);
      [rewrite (U_atom Ex 18 o E18) by lia; reflexivity | lia | lia |].
    intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Bapp. unfold SHADOW_OFF. lia.
  - apply (shent_ok_of_range rsegs (w_H (e_W E)) memc Ex (SOff 22 0) 8 (e_q E) 8 (e_q E) 0 8 HRAq HBx);
      [rewrite (U_atom Ex 8 (e_q E) E8) by lia; reflexivity | lia | lia |].
    intros x Hx. unfold SHADOW_OFF. lia. }
pose (RUN := paj_run_x_inv (SK := SK) (PL := PL_prog_B) (PI := PI_prog_B) B prh_pst ARx LAWS _ (es_plaw E)).
assert (HPM : es_P E memc) by exact HMN.
unfold cfg_at, w64. rewrite es_pc_eq.
paj_run_tok_x_inv RUN HS HJ SHOK HPM ES_SPAN.
{ intros a (rg & Hin & Har). cbn [ss_mem ss_quote In] in Hin.
  destruct Hin as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ES_SAVR ES_RO ES_RQ] in Har.
  - lia.
  - rewrite U18 in Har. right. left. split.
    + exists (e_scr E, e_scr E + es_len E + 1). split; [left; reflexivity | cbn [fst snd]; lia].
    + exists b, m. split; [exact Hbm' | lia].
  - rewrite U8 in Har. left. rewrite es_stk_val. lia. }
assert (KEPT : forall a, 0 <= a < 2 ^ 64 -> a <> o -> ~ (e_q E <= a < e_q E + 8) ->
  aview rsegs (w_H (e_W E)) (ms_mem ms) a = aview rsegs (w_H (e_W E)) memc a).
{ intros a Ha H1 H2. apply aview_eq_of. apply HFr. rewrite unsigned_lit_small by lia. intros (rg & Hin & Har).
  cbn [ss_mem ss_quote In] in Hin.
  destruct Hin as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ES_SAVR ES_RO ES_RQ] in Har;
    [lia | rewrite U18 in Har; lia | rewrite U8 in Har; lia]. }
clear HF HG HFr.
lazymatch type of HS with st_ok_pi _ _ ?Ef _ _ =>
  assert (EWf : forall n, (n < 512)%nat -> ew Ef n = ew Ex n)
    by (intros n Hn; repeat (rewrite ew_ewset_other by lia); reflexivity) end.
pose proof (es_region_nth _ _ _ 1 _ HS eq_refl) as RO. pose proof (es_region_nth _ _ _ 2 _ HS eq_refl) as RQ.
cbn [ms_mem restrict] in RO, RQ.
pose proof (es_field _ _ 18 o _ _ _ _ _ 0 1 (SLit 0) 0 RO ltac:(rewrite EWf by lia; exact U18)
  ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as VO.
pose proof (es_field _ _ 8 (e_q E) _ _ _ _ _ 0 8 (SOff 19 1) (p + 1) RQ ltac:(rewrite EWf by lia; exact U8)
  ltac:(left; reflexivity) ltac:(apply es_den_off; [rewrite EWf by lia; exact E19 | lia | lia])
  ltac:(cbn; lia) ltac:(cbn; lia)) as VQ.
clear RO RQ.
es_reg0 HS (10%bv : bv 5) Ra0.
es_exit_regs HS E Ex HEx R2 R3 R4 Hra.
eapply (paj_ret_at (PL := PL_prog_B) (PI := PI_prog_B) (e_W E) _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. rewrite XRA.
(* the grammar: the string ends at p *)
assert (HDX : PjGrammar.decode (es_xs E) = Some (acc, es_rest E (p + 1))).
{ rewrite HG3, (es_rest_cons E p) by lia. rewrite Hq, exs_dec_quote. cbn [PjGrammar.emit]. rewrite app_nil_r.
  reflexivity. }
destruct (exs_quote_scan (e_x E) (Z.to_nat (e_i0 E)) (Z.to_nat (p - e_x0 E)) acc) as (c & Hsc & Hrc & Hjc).
{ unfold es_xs, es_rest in HDX. replace (Z.to_nat (p + 1 - e_x0 E)) with (S (Z.to_nat (p - e_x0 E))) in HDX by lia.
  exact HDX. }
{ unfold es_len in *. lia. }
apply (es_finish B ARx SK E lyc Sc Hpc (ms_regs ms) (ms_mem ms) _ k 0).
- apply (ajournal_x_materialize (SK := SK) rsegs B (@prh_pst prh_img_B) ARx LAWS B_prog_segs_low). exact HJ.
- intros a Ha Hn. rewrite (KEPT a); [exact (HWIN a Ha Hn) | lia | |].
  + intros ->. apply Hn. exists (e_scr E, e_scr E + es_len E + 1). split; [left; reflexivity | cbn [fst snd]; lia].
  + intros Hqa. apply Hn. exists (e_q E, e_q E + 8). split; [right; left; reflexivity | cbn [fst snd]; lia].
- exact XAR.
- exact HHp.
- exact HAB.
- exact HRK.
- exact HSc.
- exact HPM.
- apply (es_ledger_keep B ARx LAWS lyc Sc Hpc (e_W E) memc mdc (ms_mem ms) _ _ _ _ _ _ _ (fun a => a = o) b m HHEAD HAR
    Hbm').
  + intros a ->. lia.
  + intros Hb a ->. rewrite HHp in Hb. specialize (Hhd Hb). lia.
  + intros a Ha Hn. apply KEPT; [lia | exact Hn | lia].
  + exact HLED.
- rewrite Ra0. reflexivity.
- unfold ES_RES. rewrite exs_jr_decode, HDX. split; [reflexivity|]. split.
  + exists c. split; [exact Hsc|]. split.
    * unfold es_rest. replace (Z.to_nat (p + 1 - e_x0 E)) with (S (Z.to_nat (p - e_x0 E))) by lia. exact Hrc.
    * replace (e_x0 E + e_i0 E + Z.of_nat c + 2) with (p + 1) by lia. rewrite Z.add_0_r in VQ. exact VQ.
  + unfold bytes_at. apply es_garr8_app.
    * apply (es_garr8_kept (w_H (e_W E)) memc (ms_mem ms)); [|exact GA]. intros a Ha. apply KEPT; unfold o in *; lia.
    * apply es_garr8_one; [|lia]. replace (e_scr E + Z.of_nat (length acc)) with (o + 0) by (unfold o; lia). exact VO.
Qed.
End c.
