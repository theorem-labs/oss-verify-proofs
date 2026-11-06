(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the kit of check_reply_answer's ASan walk (plugin-hostd/fuzz_command), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (the walk's kit: regions, facts, register files, seed lemma cl_seed) over fuzz_command's listing (lib/A/Prog/CmdList.v). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply_answer_k.v, with its module paths, module names and numbers changed; 313 of its 439 lines of code are new or changed and 303 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/check_provenance_lem.v, with its module paths and module names changed; 292 of its 325 lines of code are new or changed and 406 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/nl_error_puts.v; 426 of its 496 lines of code are new or changed and 255 lines of the source are left out. *)
(* nl_error on image A: the last phases of the walk (nl_error_defs.v).
   J7 -> J8 / J8c: nl_pad (+0x4e0..+0x54c): p := NL_ALIGN(n) (+0x4ec..+0x4f8); p = n: n := p, the join +0x550;
   p > n: checked_memset(w + n, 0, p - n) at +0x538 (link_ajkit.v aj_gx_intrin_at), its return J8c.
   J8c -> J8: n := n + (p - n) (+0x53c..+0x54c).
   J8 -> the Post: +0x550..+0x568 F's shadow + 4..6 := f8 and F's magic, +0x56c `beqz s2` (s2 = F >= 4096: the
   real-stack arm +0x5c0 is dead), +0x570..+0x5b0 F's shadow := f5, +0x5b4..+0x5b8 the inline release `sb zero`
   through the flag address at F + 0x78 (LinkWalkSide.v aj_gx_flag_store_pi), +0x5f0..+0x62c the epilogue and
   `ret` (paj_ret_at); the Post by LinkWalkSide.v apost_side.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j YI0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkNlw LinkWalkPi LinkWalkSide PcapRelro nl_error_c nl_error_defs
nl_error_kit nl_error_mid.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   0. NL_ALIGN
   ========================================================================== *)

(* p := ((n + 3) srliw 2) slli 2, and p - n *)
Definition ne_PADE : sv := SAlu ALU_SLL (SAluw ALU_SRL (SOff 33 3) (SLit 2)) (SLit 2).
Definition ne_PADS : sv := SAlu ALU_SUB ne_PADE (SOff 33 0).

Lemma ne_pad_rng : forall n, 0 <= n <= 4096 -> n <= ne_pad n <= n + 3 /\ ne_pad n <= 4096.
Proof. intros n Hn. unfold ne_pad. split; [split|]; lia. Qed.

Lemma ne_U_pad : forall E n, ew E 33 = Z_to_bv 64 n -> 0 <= n <= 4096 -> U E ne_PADE = ne_pad n.
Proof.
  intros E n H Hn. unfold ne_PADE.
  assert (H3 : U E (SOff 33 3) = n + 3) by (apply (U_atom_off E 33 n 3 H); lia).
  assert (Hq : 0 <= (n + 3) / 4 <= 1025) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  assert (Hw : U E (SAluw ALU_SRL (SOff 33 3) (SLit 2)) = (n + 3) / 4).
  { rewrite U_of_S, S_SAluw, H3, U_SLit, (zcanon_id 2) by (rewrite M64_val; lia).
    cbn [zalu_raw]. rewrite (Z.mod_small (n + 3)) by lia. change (2 mod 2 ^ 32) with 2. change (Z.land 2 31) with 2.
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4.
    rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31); lia).
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
  rewrite U_SAlu, Hw, U_SLit, (zcanon_id 2) by (rewrite M64_val; lia). cbn [zalu_raw]. change (Z.land 2 63) with 2.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite zcanon_id by (rewrite M64_val; lia).
  unfold ne_pad. lia.
Qed.

Lemma ne_U_pads : forall E n, ew E 33 = Z_to_bv 64 n -> 0 <= n <= 4096 -> U E ne_PADS = ne_pad n - n.
Proof.
  intros E n H Hn. pose proof (ne_pad_rng n Hn) as Hp. unfold ne_PADS.
  rewrite U_SAlu, (ne_U_pad E n H Hn), (U_atom E 33 n H) by lia. cbn [zalu_raw].
  apply zcanon_id. rewrite M64_val. lia.
Qed.

Lemma ne_denot_pads : forall E n, ew E 33 = Z_to_bv 64 n -> 0 <= n <= 4096 ->
  sv_denot E ne_PADS = w64 (ne_pad n - n).
Proof. intros E n H Hn. rewrite denot_lit_U, (ne_U_pads E n H Hn). reflexivity. Qed.

Lemma ne_denot_pads0 : forall E n, ew E 33 = Z_to_bv 64 n -> 0 <= n <= 4096 ->
  sv_denot E (SAlu ALU_ADD ne_PADS (SLit 0)) = w64 (ne_pad n - n).
Proof.
  intros E n H Hn. pose proof (ne_pad_rng n Hn) as Hp. rewrite denot_lit_U, U_SAlu, (ne_U_pads E n H Hn), U_SLit.
  rewrite (zcanon_id 0) by (rewrite M64_val; lia). cbn [zalu_raw]. rewrite Z.add_0_r.
  rewrite zcanon_id by (rewrite M64_val; lia). reflexivity.
Qed.

Lemma ne_denot_padsum : forall E n, ew E 33 = Z_to_bv 64 n -> 0 <= n <= 4096 ->
  sv_denot E (SAlu ALU_ADD (SOff 33 0) ne_PADS) = w64 (ne_pad n).
Proof.
  intros E n H Hn. pose proof (ne_pad_rng n Hn) as Hp.
  rewrite denot_lit_U, U_SAlu, (ne_U_pads E n H Hn), (U_atom E 33 n H) by lia. cbn [zalu_raw].
  rewrite zcanon_id by (rewrite M64_val; lia). f_equal. lia.
Qed.

Lemma ne_acond_pad_eq : forall E n, ew E 33 = Z_to_bv 64 n -> 0 <= n <= 4096 -> ne_pad n = n ->
  acond_ok E (mkAC BC_EQ ne_PADE (SOff 33 0)).
Proof.
  intros E n H Hn Hp. unfold acond_ok. cbn [ac_c ac_a ac_b].
  rewrite branch_eq_U, (ne_U_pad E n H Hn), (U_atom E 33 n H) by lia. apply Z.eqb_eq. exact Hp.
Qed.

Lemma ne_acond_pad_ne : forall E n, ew E 33 = Z_to_bv 64 n -> 0 <= n <= 4096 -> ne_pad n <> n ->
  acond_ok E (mkAC BC_NE ne_PADE (SOff 33 0)).
Proof.
  intros E n H Hn Hp. unfold acond_ok. cbn [ac_c ac_a ac_b].
  rewrite branch_ne_U, (ne_U_pad E n H Hn), (U_atom E 33 n H) by lia. apply negb_true_iff. apply Z.eqb_neq. exact Hp.
Qed.

(* a byte the runtime owns after frame_alloc_1 it owned before (the state differs in its frames only) *)
Lemma ne_aowned_back : forall B ly f Sc a,
  aowned B ly (set_fs f Sc) a -> (forall x, In x (frames Sc) -> In x (frames (set_fs f Sc))) -> aowned B ly Sc a.
Proof.
  intros B ly f Sc a [Hst Hnc] Hinc. split; [exact Hst|].
  intros Hc. apply Hnc. destruct Hc as [Hk | (cp & Hcp & Hr)]; [left; exact Hk|].
  right. exists cp. split; [apply Hinc; exact Hcp | exact Hr].
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
(* checked_memset (0x53214): link's link-a/plan/PLAN.md (internal record, sha256 2ce66196196e) callee table *)
Hypothesis AMEMSET : aintrin_realizes pa_segs B OSet (pa_sigma LS___asan_memset).
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Ltac ne_rv6_t HS :=
  unfold ne_rv6; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
  [ ne_reg HS (18%bv : bv 5); apply sv_off0; apply ne_E36
  | ne_reg HS (20%bv : bv 5); apply sv_off0; apply ne_E35
  | ne_reg HS (22%bv : bv 5); apply sv_off0; apply ne_E41
  | ne_reg HS (19%bv : bv 5); apply ne_den19
  | ne_reg HS (24%bv : bv 5); apply sv_off0; apply ne_E38
  | ne_reg HS (25%bv : bv 5); apply sv_off0; apply ne_E36
  | ne_reg HS (27%bv : bv 5); eapply ne_den27; eassumption ].

Definition ne_upd8c : list (bv 5 * sv) :=
  [(18%bv, SOff 36 0); (20%bv, SOff 35 0); (21%bv, ne_PADS); (22%bv, SOff 41 0);
   (19%bv, SOff 35 4096); (24%bv, SOff 38 0); (25%bv, SOff 36 0); (27%bv, ne_s11sv)].

Lemma ne_upd8c_ok : forall cx pos regs3 n f, ne_base SK B cx ->
  Forall (fun rw : bv 5 * word => getr regs3 (fst rw) = snd rw) (ne_rv6 cx pos) ->
  getr regs3 21 = w64 (ne_pad n - n) -> 0 <= n <= 4096 ->
  Forall (fun eu : bv 5 * sv => bv_eqb (fst eu) 0 = false /\
            getr regs3 (fst eu) = sv_denot (ne_E cx pos regs3 n f) (snd eu)) ne_upd8c.
Proof.
  intros cx pos regs3 n f HB HR R21 Hn. unfold ne_rv6 in HR.
  inversion HR as [|? ? R18 HR1]; subst; inversion HR1 as [|? ? R20 HR2]; subst;
  inversion HR2 as [|? ? R22 HRx]; subst;
  inversion HRx as [|? ? Q19 HRy]; subst; inversion HRy as [|? ? Q24 HRz]; subst;
  inversion HRz as [|? ? Q25 HRw]; subst; inversion HRw as [|? ? Q27 _]; subst. cbn [fst snd] in *.
  unfold ne_upd8c. repeat apply Forall_cons; try apply Forall_nil; (split; [reflexivity|]); cbn [fst snd].
  - rewrite R18. symmetry. apply sv_off0. apply ne_E36.
  - rewrite R20. symmetry. apply sv_off0. apply ne_E35.
  - rewrite R21. symmetry. apply ne_denot_pads; [apply ne_E33 | exact Hn].
  - rewrite R22. symmetry. apply sv_off0. apply ne_E41.
  - rewrite Q19. symmetry. apply ne_den19.
  - rewrite Q24. symmetry. apply sv_off0. apply ne_E38.
  - rewrite Q25. symmetry. apply sv_off0. apply ne_E36.
  - rewrite Q27. symmetry. exact (ne_den27 SK B cx pos regs3 n f HB).
Qed.

(* PHASE J7 -> J8 / J8c: nl_pad *)
Lemma ne_ph_J7 : forall POST, ne_from SK B POST NE_J8 (ne_J6i SK B) -> ne_from SK B POST NE_J8c (ne_J8ci SK B) ->
  ne_from SK B POST NE_J7 (ne_J6i SK B).
Proof.
  intros POST HN8 HN8c cx pos S3 memA regs3 mem3 md3 HB HFc (n & f & HJ & HRV).
  pose proof (ne_base_facts SK B cx HB) as (Hw0 & Hw47 & Hwapp & Hal16 & Hceil & Hsp47 & Hwin0 & Hwin1 & Hap &
    Hn0 & Hcut' & Hcut64 & Hs1r & Hs1a).
  pose proof HFc as (_ & _ & _ & HF4096 & HF64 & HFceil & HFapp & HFL & HwF & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HB as ((HJ0 & HGok & _ & _ & _ & Hgp & Htp & _) & _).
  pose proof HJ as (HJX & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNW & Hn0n & _).
  pose proof HNW as (_ & _ & _ & _ & _ & Hnr & Hfr). unfold NL_CHUNK_MAX in Hnr.
  assert (HU := ne_upd6_ok SK B cx pos regs3 n f HB HRV).
  assert (E33 := ne_E33 cx pos regs3 n f).
  assert (HX : ne_xr_ok cx n (@nil YP09.region)) by (left; reflexivity).
  assert (Hef : sv_denot (ne_E cx pos regs3 n f) (SOff 34 0) = w64 f) by (apply sv_off0; apply ne_E34).
  pose proof (ne_pad_rng n ltac:(lia)) as Hp.
  destruct (Z.eq_dec (ne_pad n) n) as [Hpe|Hpn].
  - (* p = n: no fill *)
    destruct (ne_seat SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ NE_J7 ne_upd6 false []
      [mkAC BC_EQ ne_PADE (SOff 33 0)] HB HFc HJ HU HX
      ltac:(split; [apply (ne_acond_pad_eq _ n E33); lia | exact I])) as (HEI & HS & SHOK).
    pose proof HS as HS0.
    pose (RUN := paj_run_to_x SK B LAWS (n_G cx) HGok (n_XO cx) (n_OUT cx)).
    paj_run_to_tok RUN HS HJX SHOK ne_span (AF_nl_error + NE_J8).
    + exact (ne_awr SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ false [] HB HFc HJ HX).
    + pmkst HS. apply (HN8 cx pos S3 memA); [exact HB | exact HFc |].
      exists n, f. split.
      * assert (Hen : sv_denot (ne_E cx pos regs3 n f) (SAlu ALU_ADD (SOff 33 0) ne_PADS) = w64 n)
          by (rewrite (ne_denot_padsum _ n E33) by lia; rewrite Hpe; reflexivity).
        assert (Hn' : n <= n <= NL_CHUNK_MAX) by (unfold NL_CHUNK_MAX; lia).
        ne_after_run SK B cx pos S3 memA regs3 mem3 md3 n f NE_J7 ne_upd6 false (@nil YP09.region)
          [mkAC BC_EQ ne_PADE (SOff 33 0)] HB HFc HJ HX HS0 HS HJX HFr HG n f
          (SAlu ALU_ADD (SOff 33 0) ne_PADS) (SOff 34 0) Hen Hef Hn' Hfr.
        -- intros _; reflexivity.
        -- intros Hcc; discriminate Hcc.
      * ne_rv6_t HS.
  - (* p > n: checked_memset(w + n, 0, p - n) *)
    destruct (ne_seat SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ NE_J7 ne_upd6 false []
      [mkAC BC_NE ne_PADE (SOff 33 0)] HB HFc HJ HU HX
      ltac:(split; [apply (ne_acond_pad_ne _ n E33); lia | exact I])) as (HEI & HS & SHOK).
    pose proof HS as HS0.
    pose (RUN := paj_run_x SK B LAWS (n_G cx) HGok (n_XO cx) (n_OUT cx)).
    paj_run_tok RUN HS HJX SHOK ne_span.
    + exact (ne_awr SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ false [] HB HFc HJ HX).
    + lazymatch type of HJX with ajournal_gx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ =>
        set (md4 := mdx) in * end.
      assert (HJc : ne_j SK B cx pos S3 memA (ms_regs ms) (ms_mem ms) md4 n f ne_shB).
      { assert (Hen : sv_denot (ne_E cx pos regs3 n f) (SOff 33 0) = w64 n) by (apply sv_off0; exact E33).
        assert (Hn' : n <= n <= NL_CHUNK_MAX) by (unfold NL_CHUNK_MAX; lia).
        ne_after_run SK B cx pos S3 memA regs3 mem3 md3 n f NE_J7 ne_upd6 false (@nil YP09.region)
          [mkAC BC_NE ne_PADE (SOff 33 0)] HB HFc HJ HX HS0 HS HJX HFr HG n f (SOff 33 0) (SOff 34 0) Hen Hef Hn' Hfr.
        - intros _; reflexivity.
        - intros Hcc; discriminate Hcc. }
      pose proof HJc as (HJXc & _ & _ & R2c & R3c & R4c & _ & _ & _ & _ & _ & HNWc & _ & HSWc &
        HHVc & _ & HFpc & _ & Hshc & _).
      pose proof HNWc as (_ & _ & Hpresc & _).
      set (d := ne_pad n - n) in *.
      assert (A0 : getr (ms_regs ms) 10 = w64 (ne_w cx + n)) by (ne_reg HS (10%bv : bv 5); apply sv_off0; apply ne_E58).
      assert (A1 : getr (ms_regs ms) 11 = w64 0) by (ne_reg HS (11%bv : bv 5); reflexivity).
      assert (A2 : getr (ms_regs ms) 12 = w64 d) by (ne_reg HS (12%bv : bv 5); apply (ne_denot_pads0 _ n E33); lia).
      assert (RA : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (AF_nl_error + NE_J8c))).
      { ne_reg HS (1%bv : bv 5). cbn [sv_denot]. rewrite (img_env_codeptr _ HEI). reflexivity. }
      assert (SP : spZ (ms_regs ms) = ne_sp1 cx).
      { unfold spZ. rewrite R2c. unfold w64. apply unsigned_lit_small.
        unfold NL_ERROR_AK, NL_ERROR_AFRAME, ESTACK in *. lia. }
      pmkst HS.
      eapply (SRr_bind SEGS).
      * apply (aj_gx_intrin_at SK SEGS B LAWS pa_segs_low OSet _ AMEMSET (n_G cx) (n_XO cx) (n_OUT cx) (n_W cx)
          (ms_regs ms) (ms_mem ms) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
          ((1, pos) :: n_own cx) (n_lyc cx) S3 md4 (n_k cx) (ne_w cx + n) 0 d (getr (ms_regs ms) 1)
          HGok HJXc A0 A1 A2).
        -- lia.
        -- lia.
        -- unfold NW_SIZE in *. lia.
        -- rewrite SP. lia.
        -- rewrite SP. unfold NL_ERROR_AK, NL_ERROR_AFRAME, ESTACK in *. lia.
        -- rewrite SP. unfold NL_ERROR_AK, NL_ERROR_AFRAME, ESTACK in *. lia.
        -- rewrite R3c. exact Hgp.
        -- rewrite R4c. exact Htp.
        -- reflexivity.
        -- rewrite RA. apply ret_ok_codeptr_v; [cbv [AF_nl_error NE_J8c]; lia | reflexivity].
        -- intros a Ha.
           destruct (ne_w_ajw SK B cx pos S3 memA a HB HFc ltac:(unfold NW_SIZE, d in *; lia)) as [[Haw Hxo]|[HGa|HOa]].
           ++ left. split; [exact Haw|]. split; [exact Hxo|]. rewrite SP.
              unfold NW_SIZE, NL_ERROR_AK, NL_ERROR_AFRAME, ESTACK, d in *. lia.
           ++ right; left. split; [exact HGa|]. replace a with (ne_w cx + (a - ne_w cx)) by lia.
              exact (proj2 (Hpresc (a - ne_w cx) ltac:(unfold NW_SIZE, d in *; lia))).
           ++ right; right. exact HOa.
        -- unfold amem_range, kLowMemEnd, kHighMemEnd, NW_SIZE, SHADOW_OFF, d in *. rewrite C3 in *. lia.
        -- apply (range_addressable_sub _ _ (ne_w cx) NW_SIZE); [exact HSWc | lia | unfold NW_SIZE, d in *; lia].
        -- intros Hpos. apply (ne_hull_sub _ (ne_w cx) NW_SIZE); [exact HHVc | lia | unfold NW_SIZE, d in *; lia | exact Hpos].
        -- exact I.
      * intros W' c'' _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HAP & _ & _ & UN2 & HP2 & Hsbm).
        rewrite RA.
        apply (HN8c cx pos S3 memA regs2 mem2 md2 HB HFc).
        exists n, f. split; [|split; [|split]].
        -- apply (ne_call_after SK B cx pos S3 memA (ms_regs ms) (ms_mem ms) md4 n f ne_shB regs2 mem2 md2
             (ne_w cx + n) d HB HFc HJc HJ2 Hsbm HAP UN2 HP2). left. unfold d. lia.
        -- unfold ne_rv6. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
             (rewrite (ne_preserved_r _ _ HAP); [|cbn [ne_saved_regs In]; repeat (first [left; reflexivity | right])]).
           ++ ne_reg HS (18%bv : bv 5). apply sv_off0. apply ne_E36.
           ++ ne_reg HS (20%bv : bv 5). apply sv_off0. apply ne_E35.
           ++ ne_reg HS (22%bv : bv 5). apply sv_off0. apply ne_E41.
           ++ ne_reg HS (19%bv : bv 5). apply ne_den19.
           ++ ne_reg HS (24%bv : bv 5). apply sv_off0. apply ne_E38.
           ++ ne_reg HS (25%bv : bv 5). apply sv_off0. apply ne_E36.
           ++ ne_reg HS (27%bv : bv 5). exact (ne_den27 SK B cx pos regs3 n f HB).
        -- rewrite (ne_preserved_r _ _ HAP) by (cbn [ne_saved_regs In]; repeat (first [left; reflexivity | right])).
           ne_reg HS (21%bv : bv 5). apply (ne_denot_pads _ n E33). lia.
        -- lia.
Qed.

(* PHASE J8c -> J8: n := n + (p - n) *)
Lemma ne_ph_J8c : forall POST, ne_from SK B POST NE_J8 (ne_J6i SK B) -> ne_from SK B POST NE_J8c (ne_J8ci SK B).
Proof.
  intros POST HN cx pos S3 memA regs3 mem3 md3 HB HFc (n & f & HJ & HRV & R21 & Hpd).
  pose proof (ne_base_facts SK B cx HB) as (Hw0 & Hw47 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
  pose proof HFc as (_ & _ & _ & HF4096 & _ & HFceil & _ & _ & _ & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HB as ((HJ0 & HGok & _) & _).
  pose proof HJ as (HJX & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNW & _).
  pose proof HNW as (_ & _ & _ & _ & _ & Hnr & Hfr). unfold NL_CHUNK_MAX in Hnr.
  assert (HU := ne_upd8c_ok cx pos regs3 n f HB HRV R21 ltac:(lia)).
  assert (E33 := ne_E33 cx pos regs3 n f).
  assert (HX : ne_xr_ok cx n (@nil YP09.region)) by (left; reflexivity).
  pose proof (ne_pad_rng n ltac:(lia)) as Hp.
  destruct (ne_seat SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ NE_J8c ne_upd8c false [] [] HB HFc HJ HU HX I)
    as (HEI & HS & SHOK).
  pose proof HS as HS0.
  pose (RUN := paj_run_to_x SK B LAWS (n_G cx) HGok (n_XO cx) (n_OUT cx)).
  paj_run_to_tok RUN HS HJX SHOK ne_span (AF_nl_error + NE_J8).
  - exact (ne_awr SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ false [] HB HFc HJ HX).
  - pmkst HS. apply (HN cx pos S3 memA); [exact HB | exact HFc |].
    exists (ne_pad n), f. split.
    + assert (Hen : sv_denot (ne_E cx pos regs3 n f) (SAlu ALU_ADD (SOff 33 0) ne_PADS) = w64 (ne_pad n))
        by (apply (ne_denot_padsum _ n E33); lia).
      assert (Hef : sv_denot (ne_E cx pos regs3 n f) (SOff 34 0) = w64 f) by (apply sv_off0; apply ne_E34).
      assert (Hn' : n <= ne_pad n <= NL_CHUNK_MAX) by (unfold NL_CHUNK_MAX; lia).
      ne_after_run SK B cx pos S3 memA regs3 mem3 md3 n f NE_J8c ne_upd8c false (@nil YP09.region) (@nil acond)
        HB HFc HJ HX HS0 HS HJX HFr HG (ne_pad n) f (SAlu ALU_ADD (SOff 33 0) ne_PADS) (SOff 34 0) Hen Hef Hn' Hfr.
      * intros _; reflexivity.
      * intros Hcc; discriminate Hcc.
    + ne_rv6_t HS.
Qed.


(* ==========================================================================
   THE EXIT: J8 -> the Post
   ========================================================================== *)

(* F's flag byte: present, apart from F, F's shadow and w (the runtime owns it, and owned it at the call, where
   every byte of w is the caller's: link_amem.v ajw, YCbq.v awr_byte_present, AR_owned_image_law) *)
Lemma ne_FL_facts : forall cx pos S3 memA mem3 md3,
  ne_base SK B cx -> ne_fctx B cx pos S3 memA ->
  ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((1, pos) :: n_own cx) (n_lyc cx) S3 (n_W cx) mem3 md3 (n_k cx) ->
  AR SEGS B (n_lyc cx) S3 (n_W cx) mem3 md3 /\ apresent (w_H (n_W cx)) mem3 (ne_FL cx pos) /\
  (ne_FL cx pos + 1 <= ne_F cx pos \/ ne_F cx pos + 128 <= ne_FL cx pos) /\
  (ne_FL cx pos + 1 <= ne_Fsh cx pos \/ ne_Fsh cx pos + 16 <= ne_FL cx pos) /\
  (ne_FL cx pos + 1 <= ne_w cx \/ ne_w cx + NW_SIZE <= ne_FL cx pos).
Proof.
  intros cx pos S3 memA mem3 md3 HB HF HJX.
  pose proof HF as (Hfree & Hfrs3 & (f0 & HS3) & HF4096 & HF64 & HFceil & HFapp & HFL & HwF & _).
  pose proof HJX as (_ & _ & (memS3 & HJi3 & _) & _). pose proof HJi3 as (HAR3 & _).
  assert (Hin3 : In (1, pos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
  destruct (al_flag _ _ LAWS _ _ _ _ _ 1 pos HAR3 Hin3) as (Hflp & Hflo & _ & Hflc).
  destruct (al_frames _ _ LAWS _ _ _ _ _ 1 pos HAR3 Hin3) as (_ & _ & Hfb & Hfsh).
  change (flag_addr (n_lyc cx) 1 pos) with (ne_FL cx pos) in *.
  change (frame_addr (n_lyc cx) 1 pos) with (ne_F cx pos) in *.
  change (shadow_addr (ne_F cx pos)) with (ne_Fsh cx pos) in *.
  change (fs_frame_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
  split; [exact HAR3|]. split; [exact Hflp|].
  split.
  { destruct (Z_lt_le_dec (ne_FL cx pos) (ne_F cx pos)) as [H1|H1]; [left; lia|].
    destruct (Z_lt_le_dec (ne_FL cx pos) (ne_F cx pos + 128)) as [H2|H2]; [|right; lia].
    exfalso. exact (proj2 (Hfb _ (conj H1 H2)) Hflo). }
  split.
  { destruct (Z_lt_le_dec (ne_FL cx pos) (ne_Fsh cx pos)) as [H1|H1]; [left; lia|].
    destruct (Z_lt_le_dec (ne_FL cx pos) (ne_Fsh cx pos + 16)) as [H2|H2]; [|right; lia].
    exfalso. specialize (Hfsh (ne_FL cx pos - ne_Fsh cx pos) ltac:(lia)).
    replace (ne_Fsh cx pos + (ne_FL cx pos - ne_Fsh cx pos)) with (ne_FL cx pos) in Hfsh by lia.
    exact (proj2 Hfsh Hflo). }
  destruct (Z_lt_le_dec (ne_FL cx pos) (ne_w cx)) as [H1|H1]; [left; lia|].
  destruct (Z_lt_le_dec (ne_FL cx pos) (ne_w cx + NW_SIZE)) as [H2|H2]; [|right; lia].
  exfalso.
  pose proof HB as (HPRE & _). pose proof HPRE as (HJ0 & HGok & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hajw & _).
  pose proof HJ0 as (HSTK & HXO & (memS & HJi & _) & _). pose proof HJi as (HAR & _).
  assert (Hceil0 : alloc_ceiling <= n_sp0 cx - n_STK cx) by (eapply (aj_stk_ceiling SK SEGS B); exact HJ0).
  assert (Hown : aowned B (n_lyc cx) (n_Sc cx) (ne_FL cx pos)).
  { apply (ne_aowned_back B (n_lyc cx) f0 (n_Sc cx)); rewrite <- HS3; [exact Hflo|].
    intros x Hx. rewrite Hfrs3. right. exact Hx. }
  assert (Hin' : inFP (ne_Wr cx) (ne_FL cx pos)).
  { exists (ne_w cx, ne_w cx + NW_SIZE). split; [left; reflexivity | cbn [fst snd]; lia]. }
  destruct (Hajw _ Hin') as [[Haw Hnout] | [HGa | [Hout Hwin]]].
  - destruct Haw as [Hs | Hrest]; [lia|].
    assert (Haw' : awr_byte (n_STK cx + n_XO cx) (n_sp0 cx + n_XO cx) (n_FP cx) (ablocks B (n_ly cx) (n_S cx))
                     (ablocks B (n_lyc cx) (n_Sc cx)) (n_lyc cx) (n_own cx) (ne_FL cx pos)) by (right; exact Hrest).
    destruct (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJi Haw') as [_ Hno]. exact (Hno Hown).
  - destruct (HGok _ HGa) as [Hi Hns]. apply Hns. exact (proj1 (al_owned_image _ _ LAWS _ _ _ _ _ _ HAR Hi) Hown).
  - lia.
Qed.

Definition ne_flag_region : YP09.region := YP09.mkRegion (Some 37%nat) 0 1 0 1 [].

(* the bytes the exit run may write *)
Definition ne_XW (cx : necx) (pos a : Z) : Prop :=
  (ne_FL cx pos <= a < ne_FL cx pos + 1) \/ (ne_F cx pos <= a < ne_F cx pos + 128) \/
  (ne_Fsh cx pos <= a < ne_Fsh cx pos + 16) \/ (ne_sp1 cx + 48 <= a < ne_sp1 cx + 56).

Lemma ne_sv_save : forall cx pos regs3 n f i, (i < 13)%nat ->
  sv_denot (ne_E cx pos regs3 n f) (SOff (44 + i) 0) = getr (n_regs cx) (snd (nth i ne_saves (0, 0%bv))).
Proof.
  intros cx pos regs3 n f i Hi. cbn [sv_denot]. rewrite (ne_Esave cx pos regs3 n f i Hi), Z.add_0_r.
  apply Z_to_bv_bv_unsigned.
Qed.

(* PHASE J8 -> THE POST *)
Lemma ne_ph_J8 : ne_from SK B (ne_post SK B) NE_J8 (ne_J6i SK B).
Proof.
  intros cx pos S3 memA regs3 mem3 md3 HB HFc (n & f & HJ & HRV).
  pose proof (ne_base_facts SK B cx HB) as (Hw0 & Hw47 & Hwapp & Hal16 & Hceil & Hsp47 & Hwin0 & Hwin1 & Hap &
    Hn0 & Hcut' & Hcut64 & Hs1r & Hs1a).
  pose proof HFc as (Hfree & Hfrs3 & HS3 & HF4096 & HF64 & HFceil & HFapp & HFL & HwF & HK0).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HB as (HPRE & HNLW & HWF & _).
  pose proof HPRE as (HJ0 & HGok & HROD & Hraw & Hra4 & Hgp & Htp & _).
  pose proof HJ as (HJX & Hfds3 & Hfs3 & R2 & R3 & R4 & R8 & R9 & R26 & HSV & HSL & HNW &
    Hn0n & HSW & HHV & HFLv & HFp & Hshl & Hsh & HFsp & UN & HG).
  destruct (ne_FL_facts cx pos S3 memA mem3 md3 HB HFc HJX) as (HAR3 & HFLp & HFLF & HFLS & HFLW).
  assert (HU := ne_upd6_ok SK B cx pos regs3 n f HB HRV).
  destruct (ne_seat SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ NE_J8 ne_upd6 true [] [] HB HFc HJ HU
    ltac:(left; reflexivity) I) as (HEI & HS & _).
  set (E := ne_E cx pos regs3 n f) in *.
  assert (HF8 : 0 <= ne_F cx pos / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (HFsh : ne_Fsh cx pos = SHADOW_OFF + ne_F cx pos / 8) by reflexivity.
  assert (U36 : bv_unsigned (ew E 36) = ne_F cx pos) by (unfold E; rewrite ne_E36; apply unsigned_lit_small; lia).
  assert (U37 : bv_unsigned (ew E 37) = ne_FL cx pos) by (unfold E; rewrite ne_E37; apply unsigned_lit_small; lia).
  assert (U38 : bv_unsigned (ew E 38) = ne_Fsh cx pos)
    by (unfold E; rewrite ne_E38; apply unsigned_lit_small; rewrite HFsh; unfold SHADOW_OFF; lia).
  assert (U39 : bv_unsigned (ew E 39) = ne_sp cx)
    by (unfold E; rewrite ne_E39; apply unsigned_lit_small; unfold NL_ERROR_AK, NL_ERROR_AFRAME, ESTACK in *; lia).
  assert (U40 : bv_unsigned (ew E 40) = ne_sp1 cx)
    by (unfold E; rewrite ne_E40; apply unsigned_lit_small; unfold NL_ERROR_AK, NL_ERROR_AFRAME, ESTACK in *; lia).
  (* the exit's regions: w's fields dropped (no step after J8 reads or writes w), F's flag byte added *)
  pose proof (st_ok_pi_submem E _ _ (tl (ne_regions true ne_shB ++ [])) HS) as HS1.
  lazymatch type of HS1 with ?t1 -> ?t2 -> _ =>
    assert (Hsub : t1) by (vm_compute; apply submem_drop; submem_to);
    assert (Hwf : t2) by (vm_compute; reflexivity) end.
  specialize (HS1 Hsub Hwf). clear Hsub Hwf HS.
  pose proof (st_ok_pi_add_region E _ _ ne_flag_region HS1 eq_refl) as HS2.
  lazymatch type of HS2 with ?t1 -> ?t2 -> _ => assert (Hrok : t1); [|assert (Hdis : t2); [|specialize (HS2 Hrok Hdis)]] end.
  { unfold region_ok, ne_flag_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U37. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. cbn [ms_mem restrict mkst]. apply (apresent_writable SEGS).
    replace (ne_FL cx pos + o) with (ne_FL cx pos) by lia. exact HFLp. }
  { cbv [ss_mem tl ne_regions app all_disjoint extent_disjoint ne_flag_region YP09.r_base YP09.r_lo YP09.r_hi].
    cbn [base_val]. rewrite U36, U37, U38, U39, U40.
    unfold NL_ERROR_AK, NL_ERROR_AFRAME, ESTACK, SHADOW_OFF in *. rewrite HFsh in *.
    repeat split; lia. }
  clear HS1 Hrok Hdis. norm_pi HS2.
  (* +0x550 .. +0x62c, the release `sb zero` through F + 0x78 at +0x5b8, up to the `ret` *)
  pose (RUNF := paj_flag_plain_x SK B LAWS (n_G cx) HGok (n_XO cx) (n_OUT cx)).
  lazymatch type of HS2 with st_ok_pi _ _ _ ?ss (restrict _ ?ms) =>
  lazymatch type of RUNF with context [sym_runN_pi ?tpi _ _] =>
    let r := eval vm_compute in (sym_runN_pi tpi FUEL ss) in
    lazymatch r with (?ss', ?st) =>
      assert (Hrun : sym_runN_pi tpi FUEL ss = (ss', st)) by (vm_compute; reflexivity);
      eapply (RUNF (n_W cx) FUEL E ss ss' st ms _ _ _ _ _ _ _ _ (n_own cx) (n_lyc cx) S3 _ _ 1 pos _ HEI HS2 Hrun I HJX
        ltac:(lia)); clear Hrun
    end end end.
  - (* the write obligation: F, its shadow, the spill slot, the flag byte *)
    intros a Ha. destruct (in_wrange_windows _ _ _ Ha) as (b & wlo & whi & Hin & Hab). vm_compute in Hin.
    repeat (destruct Hin as [Hq|Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hab;
      rewrite ?U36, ?U37, ?U38, ?U39, ?U40 in Hab |]); [| | | | | destruct Hin].
    + right; right; right. change (flag_addr (n_lyc cx) 1 pos) with (ne_FL cx pos). lia.
    + left. eapply (aj_gx_awr_frame SK SEGS B LAWS pa_segs_low); [exact HJX | left; reflexivity |].
      left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 1) with 128.
      change (frame_addr (n_lyc cx) 1 pos) with (ne_F cx pos). lia.
    + left. eapply (aj_gx_awr_frame SK SEGS B LAWS pa_segs_low); [exact HJX | left; reflexivity |].
      right. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 1 / 8) with 16.
      change (shadow_addr (frame_addr (n_lyc cx) 1 pos)) with (ne_Fsh cx pos). lia.
    + left. split; [left | ]; unfold NL_ERROR_AK, NL_ERROR_AFRAME, ESTACK in *; lia.
    + lia.
  - (* the flag byte is 0 at the run's end *)
    intros msr HSr. change (flag_addr (n_lyc cx) 1 pos) with (ne_FL cx pos).
    pose proof (st_ok_pi_region_nth E _ msr 0 _ HSr eq_refl) as HR.
    assert (Hb37 : base_val E (Some 37%nat) = ne_FL cx pos) by (cbn [base_val]; exact U37).
    destruct HR as (_ & _ & _ & Hcs). cbv beta zeta in Hcs. cbn [YP09.r_chunks YP09.r_base] in Hcs.
    rewrite Hb37 in Hcs.
    inversion Hcs as [|? ? Hc0 _]; subst.
    pose proof (val_of_chunk_ok SEGS E _ (ne_FL cx pos) 0 1%N (SLit 0) 0 Hc0 eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V.
    specialize (V 0%nat ltac:(lia)). rewrite !Z.add_0_r in V. exact V.
  - (* after the run: the `ret`, then the Post *)
    intros ms' mat' HS' HJ' HF HF' HGr. cbn [ms_mem restrict mkst] in HF', HGr.
    set (md5 := with_vm_backing (m_vm_lazy md3) mat' md3) in *.
    pose proof (kept_of_frame (segs := SEGS) E _ (w_H (n_W cx)) mem3 (ms_mem ms') (ne_XW cx pos) HF') as KV.
    lazymatch type of KV with ?t -> _ => assert (HWX : t); [|specialize (KV HWX); clear HWX] end.
    { intros bb wlo whi aa Hin Hab. vm_compute in Hin.
      repeat (destruct Hin as [Hq|Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hab;
        rewrite ?U36, ?U37, ?U38, ?U39, ?U40 in Hab |]); [| | | | | destruct Hin]; unfold ne_XW;
      unfold NL_ERROR_AK, NL_ERROR_AFRAME, ESTACK in *; lia. }
    eapply (paj_ret_at (PL := PL_link) (PI := PI) (n_W cx) E _ ms' md5 _ HS' eq_refl ltac:(vm_compute; reflexivity)).
    intros mat2. set (md6 := with_vm_backing (m_vm_lazy md5) mat2 md5).
    assert (R1 : getr (ms_regs ms') 1 = getr (n_regs cx) 1)
      by (ne_reg HS' (1%bv : bv 5); exact (ne_sv_save cx pos regs3 n f 0 ltac:(lia))).
    assert (HARP : aregs_preserved (n_regs cx) (ms_regs ms')).
    { apply aregs_preserved_eqs.
      - ne_reg HS' (2%bv : bv 5). unfold E. rewrite (sv_off0 _ 39 (ne_sp cx) (ne_E39 cx pos regs3 n f)). apply w64_bv_unsigned.
      - ne_reg HS' (3%bv : bv 5). unfold E. cbn [sv_denot]. rewrite (ne_E_reg cx pos regs3 n f 3 3%bv eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned. exact R3.
      - ne_reg HS' (4%bv : bv 5). unfold E. cbn [sv_denot]. rewrite (ne_E_reg cx pos regs3 n f 4 4%bv eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned. exact R4.
      - ne_reg HS' (8%bv : bv 5). exact (ne_sv_save cx pos regs3 n f 1 ltac:(lia)).
      - ne_reg HS' (9%bv : bv 5). exact (ne_sv_save cx pos regs3 n f 2 ltac:(lia)).
      - ne_reg HS' (18%bv : bv 5). exact (ne_sv_save cx pos regs3 n f 3 ltac:(lia)).
      - ne_reg HS' (19%bv : bv 5). exact (ne_sv_save cx pos regs3 n f 4 ltac:(lia)).
      - ne_reg HS' (20%bv : bv 5). exact (ne_sv_save cx pos regs3 n f 5 ltac:(lia)).
      - ne_reg HS' (21%bv : bv 5). exact (ne_sv_save cx pos regs3 n f 6 ltac:(lia)).
      - ne_reg HS' (22%bv : bv 5). exact (ne_sv_save cx pos regs3 n f 7 ltac:(lia)).
      - ne_reg HS' (23%bv : bv 5). exact (ne_sv_save cx pos regs3 n f 8 ltac:(lia)).
      - ne_reg HS' (24%bv : bv 5). exact (ne_sv_save cx pos regs3 n f 9 ltac:(lia)).
      - ne_reg HS' (25%bv : bv 5). exact (ne_sv_save cx pos regs3 n f 10 ltac:(lia)).
      - ne_reg HS' (26%bv : bv 5). exact (ne_sv_save cx pos regs3 n f 11 ltac:(lia)).
      - ne_reg HS' (27%bv : bv 5). exact (ne_sv_save cx pos regs3 n f 12 ltac:(lia)). }
    (* w's bytes: no step after J8 wrote them *)
    assert (KW : forall i, 0 <= i < NW_SIZE ->
              aview SEGS (w_H (n_W cx)) (ms_mem ms') (ne_w cx + i) = aview SEGS (w_H (n_W cx)) mem3 (ne_w cx + i)).
    { intros i Hi. apply KV; [unfold NW_SIZE in *; lia|]. unfold ne_XW. rewrite HFsh.
      unfold NW_SIZE, NL_ERROR_AK, NL_ERROR_AFRAME, ESTACK, SHADOW_OFF, kHighMemBeg in *. rewrite HFsh in HFLS. lia. }
    assert (HFIN : nlw_fields SEGS (rdW (n_W cx) (ms_mem ms')) (ne_w cx) n f).
    { apply (nlw_fields_agree SEGS (rdW (n_W cx) mem3) _ _ _ _ HNW). intros i Hi. split.
      - apply (mbyte_of_aview SEGS). exact (KW i Hi).
      - intros Hwb. exact (writable_at_grows SEGS _ _ _ HGr Hwb). }
    destruct (fields_of_anlw SEGS (rdW (n_W cx) (n_memc cx)) (ne_w cx) (n_bs cx) HNLW HWF)
      as (VN0 & _ & (Hn0a & Hn0b) & _).
    cbn [cfg_ms cfg_model]. rewrite R1, Hraw. unfold ne_post.
    eapply (apost_side SK SEGS B LAWS pa_segs_low NL_ERROR_AK 0 (fun a => inFP (ne_Wr cx) a)
      (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx)
      (n_md0 cx) (n_own cx) (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) (n_k cx) (n_regs cx) (ms_regs ms')
      (stack_free_state 1 pos S3) (ms_mem ms') md6 (n_k cx) 1 pos S3 (n_W cx) mem3 md3).
    + exact HJ0.
    + unfold md6. apply (ajournal_gx_materialize SEGS B LAWS pa_segs_low). exact HJ'.
    + lia.
    + unfold md6, md5. repeat rewrite (proj1 (wvb_fds_fs _ _ _)). exact Hfds3.
    + unfold md6, md5. repeat rewrite (proj2 (wvb_fds_fs _ _ _)). exact Hfs3.
    + exact HARP.
    + exact HAR3.
    + exact Hfrs3.
    + destruct HS3 as (f0 & ->). apply ablocks_set_fs.
    + (* the kept clause: memc -> memA (frame_alloc_1's), memA -> mem3 (the joins'), mem3 -> the end (the exit's) *)
      pose proof HJ0 as (_ & _ & (memS & HJi & _) & _).
      apply (akept_step SK SEGS B LAWS pa_segs_low (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx)
        (n_W cx) memA (n_W cx) (ms_mem ms') _ _ (fun _ => False) _ (fun a => ne_Z cx pos a \/ a = ne_FL cx pos)).
      * exact (proj1 HJi).
      * fold (ne_sp cx). lia.
      * fold (ne_sp cx). lia.
      * exact HK0.
      * intros a Ha HnX. rewrite (KV a Ha).
        -- apply UN; [exact Ha|]. intros HZ. exact (HnX (or_introl HZ)).
        -- intros HXa. apply HnX. unfold ne_XW in HXa. unfold ne_Z.
           destruct HXa as [Hq|[Hq|[Hq|Hq]]]; [right; lia | left; right; right; left; exact Hq
             | left; right; right; right; exact Hq | left; left; unfold NL_ERROR_AK, NL_ERROR_AFRAME, ESTACK in *; lia].
      * intros a _ Hp. eapply apresent_grows; [exact HGr | exact (HG a Hp)].
      * intros a [].
      * intros a [HZ | Hq].
        -- destruct HZ as [Hq|[Hq|[Hq|Hq]]].
           ++ right. exact Hq.
           ++ left. left. exists (ne_w cx, ne_w cx + NW_SIZE). split; [left; reflexivity | exact Hq].
           ++ left. right. left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 1) with 128. exact Hq.
           ++ left. right. right. left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 1 / 8) with 16. exact Hq.
        -- left. right. right. right. exact Hq.
    + cbv beta. split; [|split].
      * apply (set_fs_trans S3); [apply set_fs_of_exists; exact HS3 | apply stack_free_state_set_fs].
      * assert (EabF : ablocks B (n_lyc cx) (stack_free_state 1 pos S3) = ablocks B (n_lyc cx) (n_Sc cx)).
        { unfold ablocks. rewrite blocks_stack_free_state. destruct HS3 as (f0 & ->). rewrite blocks_set_fs. reflexivity. }
        rewrite EabF. apply Permutation_refl.
      * unfold nl_error_apost. intros bs Hbs.
        exact (nlw_post_of_fields SEGS (rdW (n_W cx) (n_memc cx)) (rdW (n_W cx) (ms_mem ms')) (ne_w cx) (ne_n0 cx) n f
          VN0 Hn0a Hn0n HFIN bs Hbs).
Qed.

End b.
End a.
