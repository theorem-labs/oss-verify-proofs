(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the kit of check_reply_answer's ASan walk (plugin-hostd/fuzz_command), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (the walk's kit: regions, facts, register files, seed lemma cl_seed) over fuzz_command's listing (lib/A/Prog/CmdList.v). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply_answer_k.v, with its module paths, module names and numbers changed; 313 of its 439 lines of code are new or changed and 303 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/check_provenance_lem.v, with its module paths and module names changed; 292 of its 325 lines of code are new or changed and 406 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/nl_error_puts.v, with its numbers changed; 493 of its 598 lines of code are new or changed and 220 lines of the source are left out. *)
(* nl_error on image A: the middle phases of the walk (nl_error_defs.v).
   J5 -> J5c: +0x3e0..+0x400 (s7 := F + 32; the body's shadow bytes F's shadow + 4, + 5, + 6 := 0, 0, 4), the call
   checked_memset(F + 36, 0, 16) at +0x400 (link_ajkit.v aj_gx_intrin_at), its return at +0x404.

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
nl_error_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* the body's 20 bytes are addressable once F's shadow + 4, + 5, + 6 hold 0, 0, 4 *)
Lemma ne_body_ra : forall (rd : Z -> option Z) F, F mod 64 = 0 -> 0 <= F ->
  rd (SHADOW_OFF + F / 8 + 4) = Some 0 -> rd (SHADOW_OFF + F / 8 + 5) = Some 0 ->
  rd (SHADOW_OFF + F / 8 + 6) = Some 4 ->
  range_addressable rd SHADOW_OFF (F + 32) 20.
Proof.
  intros rd F HF64 HF0 H4 H5 H6 x Hx. unfold shadow_of_addr.
  assert (Hq : F = 64 * (F / 64)) by (pose proof (Z_div_mod_eq_full F 64); lia).
  destruct (Z_lt_dec x (F + 40)) as [H1|H1]; [|destruct (Z_lt_dec x (F + 48)) as [H2|H2]].
  - exists 0. split; [|left; reflexivity].
    replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + F / 8 + 4) by lia. exact H4.
  - exists 0. split; [|left; reflexivity].
    replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + F / 8 + 5) by lia. exact H5.
  - exists 4. split.
    + replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + F / 8 + 6) by lia. exact H6.
    + right. lia.
Qed.

(* the shadow hull of a range inside F is inside F's 16 shadow bytes *)
Lemma ne_F_hull : forall (rd : Z -> option Z) F d n sh, F mod 64 = 0 -> 0 <= F ->
  (forall i, (i < 16)%nat -> rd (SHADOW_OFF + F / 8 + Z.of_nat i) = Some (nth i sh 0)) ->
  F <= d -> d + n <= F + 128 -> 0 < n -> shadow_hull_vis rd d n.
Proof.
  intros rd F d n sh HF64 HF0 Hsh Hd1 Hd2 Hn s Hs. unfold shadow_addr, SHADOW_OFF in Hs.
  assert (Hq : F = 64 * (F / 64)) by (pose proof (Z_div_mod_eq_full F 64); lia).
  assert (Hi : (Z.to_nat (s - (SHADOW_OFF + F / 8)) < 16)%nat /\
               s = SHADOW_OFF + F / 8 + Z.of_nat (Z.to_nat (s - (SHADOW_OFF + F / 8)))).
  { unfold SHADOW_OFF. split; [|rewrite Z2Nat.id]; lia. }
  destruct Hi as [Hi ->]. rewrite (Hsh _ Hi). discriminate.
Qed.

(* a plain run (no instrumented check: the run writes F's shadow, which the token engine refuses) from a seated
   state to a call: leaves the write obligation and the continuation at the callee's entry *)
Ltac ne_run_plain_call RUNP HS HJ :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
  lazymatch type of RUNP with
  | context [sym_runN_pi ?tpi _ _] =>
    let r := eval vm_compute in (sym_runN_pi tpi FUEL ss) in
    lazymatch r with
    | (?ss', PRS_call ?s) =>
      let Hrun := fresh "Hrun" in
      assert (Hrun : sym_runN_pi tpi FUEL ss = (ss', PRS_call s)) by (vm_compute; reflexivity);
      let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI end in
      eapply (RUNP W FUEL E ss ss' s ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun HJ); clear Hrun
    | _ => fail "ne_run_plain_call: the run does not stop at a call:" r
    end end end.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
(* checked_memset (0x53214) and checked_memcpy (0x52d78): link's link-a/plan/PLAN.md (internal record, sha256 2ce66196196e) callee table *)
Hypothesis AMEMSET : aintrin_realizes pa_segs B OSet (pa_sigma LS___asan_memset).
Hypothesis AMEMCPY : aintrin_realizes pa_segs B OCpy (pa_sigma LS___asan_memcpy).
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Lemma ne_upd5_ok : forall cx pos regs3 n f, ne_base SK B cx ->
  Forall (fun rw : bv 5 * word => getr regs3 (fst rw) = snd rw) (ne_rv5 cx pos) ->
  Forall (fun eu : bv 5 * sv => bv_eqb (fst eu) 0 = false /\
            getr regs3 (fst eu) = sv_denot (ne_E cx pos regs3 n f) (snd eu)) ne_upd5.
Proof.
  intros cx pos regs3 n f HB HR. unfold ne_rv5 in HR.
  inversion HR as [|? ? R18 HR1]; subst; inversion HR1 as [|? ? R20 HR2]; subst;
  inversion HR2 as [|? ? R21 HR3]; subst; inversion HR3 as [|? ? R23 HR4]; subst;
  inversion HR4 as [|? ? R22 HRx]; subst;
  inversion HRx as [|? ? Q19 HRy]; subst; inversion HRy as [|? ? Q24 HRz]; subst;
  inversion HRz as [|? ? Q25 HRw]; subst; inversion HRw as [|? ? Q27 _]; subst. cbn [fst snd] in *.
  unfold ne_upd5. repeat apply Forall_cons; try apply Forall_nil; (split; [reflexivity|]); cbn [fst snd].
  - rewrite R18. symmetry. cbn [sv_denot]. rewrite ne_E42, Z.add_0_r. apply Z_to_bv_bv_unsigned.
  - rewrite R20. symmetry. apply sv_off0. apply ne_E36.
  - rewrite R21. symmetry. apply sv_off0. apply ne_E35.
  - rewrite R23. symmetry. cbn [sv_denot]. rewrite ne_E42, Z.add_0_r. apply Z_to_bv_bv_unsigned.
  - rewrite R22. symmetry. apply sv_off0. apply ne_E41.
  - rewrite Q19. symmetry. apply ne_den19.
  - rewrite Q24. symmetry. apply sv_off0. apply ne_E38.
  - rewrite Q25. symmetry. apply sv_off0. apply ne_E36.
  - rewrite Q27. symmetry. exact (ne_den27 SK B cx pos regs3 n f HB).
Qed.

(* PHASE J5 -> J5c *)
Lemma ne_ph_J5 : forall POST, ne_from SK B POST NE_J5c (ne_J5ci SK B) -> ne_from SK B POST NE_J5 (ne_J5i SK B).
Proof.
  intros POST HN cx pos S3 memA regs3 mem3 md3 HB HFc (n & f & HJ & HRV).
  pose proof (ne_base_facts SK B cx HB) as (Hw0 & Hw47 & Hwapp & Hal16 & Hceil & Hsp47 & Hwin0 & Hwin1 & Hap &
    Hn0 & _ & _ & Hs1r & Hs1a).
  pose proof HFc as (_ & _ & _ & HF4096 & HF64 & HFceil & HFapp & HFL & HwF & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HB as ((HJ0 & HGok & _ & _ & _ & Hgp & Htp & _) & _).
  pose proof HJ as (HJX & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNW & Hn0n & _).
  pose proof HNW as (_ & _ & _ & _ & _ & Hnr & Hfr). unfold NL_CHUNK_MAX in Hnr.
  assert (HU := ne_upd5_ok cx pos regs3 n f HB HRV).
  destruct (ne_seat SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ NE_J5 ne_upd5 true [] []
    HB HFc HJ HU ltac:(left; reflexivity) I) as (HEI & HS & SHOK).
  pose proof HS as HS0.
  pose (RUNP := paj_run_call_plain_x SK B LAWS (n_G cx) HGok (n_XO cx) (n_OUT cx)).
  ne_run_plain_call RUNP HS HJX.
  - exact (ne_awr SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ true [] HB HFc HJ ltac:(left; reflexivity)).
  - (* at checked_memset's entry: the join there *)
    clear HS. intros ms mat HS HJX' HF HFr HG. clear HJX. rename HJX' into HJX.
    set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *.
    assert (HJc : ne_j SK B cx pos S3 memA (ms_regs ms) (ms_mem ms) md4 n f ne_shB).
    { assert (HX : ne_xr_ok cx n (@nil YP09.region)) by (left; reflexivity).
      assert (Hen : sv_denot (ne_E cx pos regs3 n f) (SOff 33 0) = w64 n) by (apply sv_off0; apply ne_E33).
      assert (Hef : sv_denot (ne_E cx pos regs3 n f) (SOff 34 0) = w64 f) by (apply sv_off0; apply ne_E34).
      assert (Hn' : n <= n <= NL_CHUNK_MAX) by (unfold NL_CHUNK_MAX; lia).
      ne_after_run SK B cx pos S3 memA regs3 mem3 md3 n f NE_J5 ne_upd5 true (@nil YP09.region) (@nil acond)
        HB HFc HJ HX HS0 HS HJX HFr HG n f (SOff 33 0) (SOff 34 0) Hen Hef Hn' Hfr.
      - intros Hc; discriminate Hc.
      - intros _. eapply ne_sh_after; [exact HS | vm_compute; reflexivity |].
        rewrite ne_E38. apply unsigned_lit_small. unfold ne_Fsh, shadow_addr, SHADOW_OFF.
        assert (0 <= ne_F cx pos / 8 <= 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
        lia. }
    pose proof HJc as (HJXc & _ & _ & R2c & R3c & R4c & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      _ & _ & Hshc & _).
    (* the registers of the call *)
    assert (A0 : getr (ms_regs ms) 10 = w64 (ne_F cx pos + 36)).
    { ne_reg HS (10%bv : bv 5). apply (sv_offc _ 36 (ne_F cx pos) 36 (ne_E36 _ _ _ _ _)). lia. }
    assert (A1 : getr (ms_regs ms) 11 = w64 0) by (ne_reg HS (11%bv : bv 5); reflexivity).
    assert (A2 : getr (ms_regs ms) 12 = w64 16) by (ne_reg HS (12%bv : bv 5); reflexivity).
    assert (RA : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (AF_nl_error + NE_J5c))).
    { ne_reg HS (1%bv : bv 5). cbn [sv_denot]. rewrite (img_env_codeptr _ HEI). reflexivity. }
    assert (SP : spZ (ms_regs ms) = ne_sp1 cx).
    { unfold spZ. rewrite R2c. unfold w64. apply unsigned_lit_small.
      unfold NL_ERROR_AK, NL_ERROR_AFRAME, ESTACK in *. lia. }
    assert (Hsh4 : forall i, (i < 16)%nat ->
              aview SEGS (w_H (n_W cx)) (ms_mem ms) (SHADOW_OFF + ne_F cx pos / 8 + Z.of_nat i) = Some (nth i ne_shB 0))
      by exact Hshc.
    pmkst HS.
    eapply (SRr_bind SEGS).
    + apply (aj_gx_intrin_at SK SEGS B LAWS pa_segs_low OSet _ AMEMSET (n_G cx) (n_XO cx) (n_OUT cx) (n_W cx)
        (ms_regs ms) (ms_mem ms) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
        ((1, pos) :: n_own cx) (n_lyc cx) S3 md4 (n_k cx) (ne_F cx pos + 36) 0 16 (getr (ms_regs ms) 1)
        HGok HJXc A0 A1 A2).
      * lia.
      * lia.
      * lia.
      * rewrite SP. lia.
      * rewrite SP. unfold NL_ERROR_AK, NL_ERROR_AFRAME, ESTACK in *. lia.
      * rewrite SP. unfold NL_ERROR_AK, NL_ERROR_AFRAME, ESTACK in *. lia.
      * rewrite R3c. exact Hgp.
      * rewrite R4c. exact Htp.
      * reflexivity.
      * rewrite RA. apply ret_ok_codeptr_v; [cbv [AF_nl_error NE_J5c]; lia | reflexivity].
      * intros a Ha. left.
        destruct (aj_gx_awr_frame SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1 pos a HJXc
          ltac:(left; reflexivity)
          ltac:(left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 1) with 128;
                change (frame_addr (n_lyc cx) 1 pos) with (ne_F cx pos); lia))
          as [Haw Hxo].
        split; [exact Haw|]. split; [exact Hxo|]. rewrite SP. unfold NL_ERROR_AK, NL_ERROR_AFRAME, ESTACK in *. lia.
      * unfold amem_range, kLowMemEnd, kLowShadowBeg, kHighMemEnd in *. rewrite C3 in *. lia.
      * apply (range_addressable_sub _ _ (ne_F cx pos + 32) 20); [|lia|lia].
        apply ne_body_ra; [exact HF64 | lia | | |].
        -- exact (Hsh4 4%nat ltac:(lia)).
        -- exact (Hsh4 5%nat ltac:(lia)).
        -- exact (Hsh4 6%nat ltac:(lia)).
      * intros _. apply (ne_F_hull _ (ne_F cx pos) _ _ ne_shB HF64 ltac:(lia) Hsh4); lia.
      * exact I.
    + (* the memset returned: the join J5c *)
      intros W' c' _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HAP & _ & _ & UN2 & HP2 & Hsbm).
      rewrite RA.
      apply (HN cx pos S3 memA regs2 mem2 md2 HB HFc).
      exists n, f. split.
      * apply (ne_call_after SK B cx pos S3 memA (ms_regs ms) (ms_mem ms) md4 n f ne_shB regs2 mem2 md2
          (ne_F cx pos + 36) 16 HB HFc HJc HJ2 Hsbm HAP UN2 HP2). right. lia.
      * unfold ne_rv5c. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
          (rewrite (ne_preserved_r _ _ HAP); [|cbn [ne_saved_regs In]; repeat (first [left; reflexivity | right])]).
        -- ne_reg HS (18%bv : bv 5). cbn [sv_denot]. rewrite ne_E42, Z.add_0_r. apply Z_to_bv_bv_unsigned.
        -- ne_reg HS (20%bv : bv 5). apply sv_off0. apply ne_E36.
        -- ne_reg HS (21%bv : bv 5). apply sv_off0. apply ne_E35.
        -- ne_reg HS (23%bv : bv 5). apply (sv_offc _ 36 (ne_F cx pos) 32 (ne_E36 _ _ _ _ _)). lia.
        -- ne_reg HS (22%bv : bv 5). apply sv_off0. apply ne_E41.
        -- ne_reg HS (19%bv : bv 5). apply ne_den19.
        -- ne_reg HS (24%bv : bv 5). apply sv_off0. apply ne_E38.
        -- ne_reg HS (25%bv : bv 5). apply sv_off0. apply ne_E36.
        -- ne_reg HS (27%bv : bv 5). exact (ne_den27 SK B cx pos regs3 n f HB).
Qed.


(* the registers of a seated state, from the join's registers *)
Lemma ne_upd5c_ok : forall cx pos regs3 n f, ne_base SK B cx ->
  Forall (fun rw : bv 5 * word => getr regs3 (fst rw) = snd rw) (ne_rv5c cx pos) -> 0 <= ne_F cx pos < 2 ^ 63 ->
  Forall (fun eu : bv 5 * sv => bv_eqb (fst eu) 0 = false /\
            getr regs3 (fst eu) = sv_denot (ne_E cx pos regs3 n f) (snd eu)) ne_upd5c.
Proof.
  intros cx pos regs3 n f HB HR HF. unfold ne_rv5c in HR.
  inversion HR as [|? ? R18 HR1]; subst; inversion HR1 as [|? ? R20 HR2]; subst;
  inversion HR2 as [|? ? R21 HR3]; subst; inversion HR3 as [|? ? R23 HR4]; subst;
  inversion HR4 as [|? ? R22 HRx]; subst;
  inversion HRx as [|? ? Q19 HRy]; subst; inversion HRy as [|? ? Q24 HRz]; subst;
  inversion HRz as [|? ? Q25 HRw]; subst; inversion HRw as [|? ? Q27 _]; subst. cbn [fst snd] in *.
  unfold ne_upd5c. repeat apply Forall_cons; try apply Forall_nil; (split; [reflexivity|]); cbn [fst snd].
  - rewrite R18. symmetry. cbn [sv_denot]. rewrite ne_E42, Z.add_0_r. apply Z_to_bv_bv_unsigned.
  - rewrite R20. symmetry. apply sv_off0. apply ne_E36.
  - rewrite R21. symmetry. apply sv_off0. apply ne_E35.
  - rewrite R23. symmetry. apply (sv_offc _ 36 (ne_F cx pos) 32 (ne_E36 _ _ _ _ _)). lia.
  - rewrite R22. symmetry. apply sv_off0. apply ne_E41.
  - rewrite Q19. symmetry. apply ne_den19.
  - rewrite Q24. symmetry. apply sv_off0. apply ne_E38.
  - rewrite Q25. symmetry. apply sv_off0. apply ne_E36.
  - rewrite Q27. symmetry. exact (ne_den27 SK B cx pos regs3 n f HB).
Qed.

Lemma ne_upd5b_ok : forall cx pos regs3 n f, ne_base SK B cx ->
  Forall (fun rw : bv 5 * word => getr regs3 (fst rw) = snd rw) (ne_rv5b cx pos) -> 0 <= ne_F cx pos < 2 ^ 63 ->
  Forall (fun eu : bv 5 * sv => bv_eqb (fst eu) 0 = false /\
            getr regs3 (fst eu) = sv_denot (ne_E cx pos regs3 n f) (snd eu)) ne_upd5b.
Proof.
  intros cx pos regs3 n f HB HR HF. unfold ne_rv5b in HR.
  inversion HR as [|? ? R12 HR1]; subst; inversion HR1 as [|? ? R20 HR2]; subst;
  inversion HR2 as [|? ? R21 HR3]; subst; inversion HR3 as [|? ? R23 HR4]; subst;
  inversion HR4 as [|? ? R22 HRx]; subst;
  inversion HRx as [|? ? Q19 HRy]; subst; inversion HRy as [|? ? Q24 HRz]; subst;
  inversion HRz as [|? ? Q25 HRw]; subst; inversion HRw as [|? ? Q27 _]; subst. cbn [fst snd] in *.
  unfold ne_upd5b. repeat apply Forall_cons; try apply Forall_nil; (split; [reflexivity|]); cbn [fst snd].
  - rewrite R12. symmetry. apply sv_off0. apply ne_E43.
  - rewrite R20. symmetry. apply sv_off0. apply ne_E36.
  - rewrite R21. symmetry. apply sv_off0. apply ne_E35.
  - rewrite R23. symmetry. apply (sv_offc _ 36 (ne_F cx pos) 32 (ne_E36 _ _ _ _ _)). lia.
  - rewrite R22. symmetry. apply sv_off0. apply ne_E41.
  - rewrite Q19. symmetry. apply ne_den19.
  - rewrite Q24. symmetry. apply sv_off0. apply ne_E38.
  - rewrite Q25. symmetry. apply sv_off0. apply ne_E36.
  - rewrite Q27. symmetry. exact (ne_den27 SK B cx pos regs3 n f HB).
Qed.

Lemma ne_upd6c_ok : forall cx pos regs3 n f, ne_base SK B cx ->
  Forall (fun rw : bv 5 * word => getr regs3 (fst rw) = snd rw) (ne_rv6c cx pos) ->
  Forall (fun eu : bv 5 * sv => bv_eqb (fst eu) 0 = false /\
            getr regs3 (fst eu) = sv_denot (ne_E cx pos regs3 n f) (snd eu)) ne_upd6c.
Proof.
  intros cx pos regs3 n f HB HR. unfold ne_rv6c in HR.
  inversion HR as [|? ? R18 HR1]; subst; inversion HR1 as [|? ? R20 HR2]; subst;
  inversion HR2 as [|? ? R21 HR3]; subst; inversion HR3 as [|? ? R22 HRx]; subst;
  inversion HRx as [|? ? Q19 HRy]; subst; inversion HRy as [|? ? Q24 HRz]; subst;
  inversion HRz as [|? ? Q25 HRw]; subst; inversion HRw as [|? ? Q27 _]; subst. cbn [fst snd] in *.
  unfold ne_upd6c. repeat apply Forall_cons; try apply Forall_nil; (split; [reflexivity|]); cbn [fst snd].
  - rewrite R18. symmetry. apply sv_off0. apply ne_E36.
  - rewrite R20. symmetry. apply sv_off0. apply ne_E35.
  - rewrite R21. symmetry. apply sv_off0. apply ne_E43.
  - rewrite R22. symmetry. apply sv_off0. apply ne_E41.
  - rewrite Q19. symmetry. apply ne_den19.
  - rewrite Q24. symmetry. apply sv_off0. apply ne_E38.
  - rewrite Q25. symmetry. apply sv_off0. apply ne_E36.
  - rewrite Q27. symmetry. exact (ne_den27 SK B cx pos regs3 n f HB).
Qed.

Lemma ne_upd6_ok : forall cx pos regs3 n f, ne_base SK B cx ->
  Forall (fun rw : bv 5 * word => getr regs3 (fst rw) = snd rw) (ne_rv6 cx pos) ->
  Forall (fun eu : bv 5 * sv => bv_eqb (fst eu) 0 = false /\
            getr regs3 (fst eu) = sv_denot (ne_E cx pos regs3 n f) (snd eu)) ne_upd6.
Proof.
  intros cx pos regs3 n f HB HR. unfold ne_rv6 in HR.
  inversion HR as [|? ? R18 HR1]; subst; inversion HR1 as [|? ? R20 HR2]; subst;
  inversion HR2 as [|? ? R22 HRx]; subst;
  inversion HRx as [|? ? Q19 HRy]; subst; inversion HRy as [|? ? Q24 HRz]; subst;
  inversion HRz as [|? ? Q25 HRw]; subst; inversion HRw as [|? ? Q27 _]; subst. cbn [fst snd] in *.
  unfold ne_upd6. repeat apply Forall_cons; try apply Forall_nil; (split; [reflexivity|]); cbn [fst snd].
  - rewrite R18. symmetry. apply sv_off0. apply ne_E36.
  - rewrite R20. symmetry. apply sv_off0. apply ne_E35.
  - rewrite R22. symmetry. apply sv_off0. apply ne_E41.
  - rewrite Q19. symmetry. apply ne_den19.
  - rewrite Q24. symmetry. apply sv_off0. apply ne_E38.
  - rewrite Q25. symmetry. apply sv_off0. apply ne_E36.
  - rewrite Q27. symmetry. exact (ne_den27 SK B cx pos regs3 n f HB).
Qed.

Ltac ne_rv6_after HS :=
  unfold ne_rv6; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
  [ ne_reg HS (18%bv : bv 5); apply sv_off0; apply ne_E36
  | ne_reg HS (20%bv : bv 5); apply sv_off0; apply ne_E35
  | ne_reg HS (22%bv : bv 5); apply sv_off0; apply ne_E41
  | ne_reg HS (19%bv : bv 5); apply ne_den19
  | ne_reg HS (24%bv : bv 5); apply sv_off0; apply ne_E38
  | ne_reg HS (25%bv : bv 5); apply sv_off0; apply ne_E36
  | ne_reg HS (27%bv : bv 5); eapply ne_den27; eassumption ].

(* PHASE J5c -> J5b: `sw s2, 0(s7)` (the code into body[0..4)), the cut reloaded from the frame, `bgez` *)
Lemma ne_ph_J5c : forall POST, ne_from SK B POST NE_J5b (ne_J5bi SK B) -> ne_from SK B POST NE_J5c (ne_J5ci SK B).
Proof.
  intros POST HN cx pos S3 memA regs3 mem3 md3 HB HFc (n & f & HJ & HRV).
  pose proof (ne_base_facts SK B cx HB) as (Hw0 & Hw47 & _ & _ & _ & _ & _ & _ & _ & _ & Hcut' & Hcut64 & _ & _).
  pose proof HFc as (_ & _ & _ & HF4096 & _ & HFceil & _ & _ & _ & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HB as ((HJ0 & HGok & _) & _).
  pose proof HJ as (HJX & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNW & _).
  pose proof HNW as (_ & _ & _ & _ & _ & Hnr & Hfr). unfold NL_CHUNK_MAX in Hnr.
  assert (HU := ne_upd5c_ok cx pos regs3 n f HB HRV ltac:(lia)).
  assert (E57 := ne_E57 cx pos regs3 n f).
  assert (HX : ne_xr_ok cx n (@nil YP09.region)) by (left; reflexivity).
  assert (Hen : sv_denot (ne_E cx pos regs3 n f) (SOff 33 0) = w64 n) by (apply sv_off0; apply ne_E33).
  assert (Hef : sv_denot (ne_E cx pos regs3 n f) (SOff 34 0) = w64 f) by (apply sv_off0; apply ne_E34).
  assert (Hn' : n <= n <= NL_CHUNK_MAX) by (unfold NL_CHUNK_MAX; lia).
  destruct (Z_lt_le_dec (ne_cut cx) (2 ^ 63)) as [Hc|Hc].
  - (* the cut stays *)
    destruct (ne_seat SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ NE_J5c ne_upd5c false []
      [mkAC BC_GE (SOff 57 0) (SLit 0)] HB HFc HJ HU HX
      ltac:(split; [apply (ne_acond_ge0 _ 57 (ne_cut cx)); [exact E57 | lia] | exact I])) as (HEI & HS & SHOK).
    pose proof HS as HS0.
    pose (RUN := paj_run_to_x SK B LAWS (n_G cx) HGok (n_XO cx) (n_OUT cx)).
    paj_run_to_tok RUN HS HJX SHOK ne_span (AF_nl_error + NE_J5b).
    + exact (ne_awr SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ false [] HB HFc HJ HX).
    + pmkst HS. apply (HN cx pos S3 memA); [exact HB | exact HFc |].
      exists n, f. split.
      * ne_after_run SK B cx pos S3 memA regs3 mem3 md3 n f NE_J5c ne_upd5c false (@nil YP09.region)
          [mkAC BC_GE (SOff 57 0) (SLit 0)] HB HFc HJ HX HS0 HS HJX HFr HG n f (SOff 33 0) (SOff 34 0) Hen Hef Hn' Hfr.
        -- intros _; reflexivity.
        -- intros Hcc; discriminate Hcc.
      * unfold ne_rv5b. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
        -- ne_reg HS (12%bv : bv 5). unfold ne_cutv. rewrite (proj2 (Z.ltb_lt _ _) Hc). apply sv_off0. exact E57.
        -- ne_reg HS (20%bv : bv 5). apply sv_off0. apply ne_E36.
        -- ne_reg HS (21%bv : bv 5). apply sv_off0. apply ne_E35.
        -- ne_reg HS (23%bv : bv 5). apply (sv_offc _ 36 (ne_F cx pos) 32 (ne_E36 _ _ _ _ _)). lia.
        -- ne_reg HS (22%bv : bv 5). apply sv_off0. apply ne_E41.
        -- ne_reg HS (19%bv : bv 5). apply ne_den19.
        -- ne_reg HS (24%bv : bv 5). apply sv_off0. apply ne_E38.
        -- ne_reg HS (25%bv : bv 5). apply sv_off0. apply ne_E36.
        -- ne_reg HS (27%bv : bv 5). exact (ne_den27 SK B cx pos regs3 n f HB).
  - (* a cut with bit 63 set becomes 20 *)
    destruct (ne_seat SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ NE_J5c ne_upd5c false []
      [mkAC BC_LT (SOff 57 0) (SLit 0)] HB HFc HJ HU HX
      ltac:(split; [apply (ne_acond_lt0 _ 57 (ne_cut cx)); [exact E57 | lia] | exact I])) as (HEI & HS & SHOK).
    pose proof HS as HS0.
    pose (RUN := paj_run_to_x SK B LAWS (n_G cx) HGok (n_XO cx) (n_OUT cx)).
    paj_run_to_tok RUN HS HJX SHOK ne_span (AF_nl_error + NE_J5b).
    + exact (ne_awr SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ false [] HB HFc HJ HX).
    + pmkst HS. apply (HN cx pos S3 memA); [exact HB | exact HFc |].
      exists n, f. split.
      * ne_after_run SK B cx pos S3 memA regs3 mem3 md3 n f NE_J5c ne_upd5c false (@nil YP09.region)
          [mkAC BC_LT (SOff 57 0) (SLit 0)] HB HFc HJ HX HS0 HS HJX HFr HG n f (SOff 33 0) (SOff 34 0) Hen Hef Hn' Hfr.
        -- intros _; reflexivity.
        -- intros Hcc; discriminate Hcc.
      * unfold ne_rv5b. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
        -- ne_reg HS (12%bv : bv 5). unfold ne_cutv. rewrite (proj2 (Z.ltb_ge _ _) Hc). reflexivity.
        -- ne_reg HS (20%bv : bv 5). apply sv_off0. apply ne_E36.
        -- ne_reg HS (21%bv : bv 5). apply sv_off0. apply ne_E35.
        -- ne_reg HS (23%bv : bv 5). apply (sv_offc _ 36 (ne_F cx pos) 32 (ne_E36 _ _ _ _ _)). lia.
        -- ne_reg HS (22%bv : bv 5). apply sv_off0. apply ne_E41.
        -- ne_reg HS (19%bv : bv 5). apply ne_den19.
        -- ne_reg HS (24%bv : bv 5). apply sv_off0. apply ne_E38.
        -- ne_reg HS (25%bv : bv 5). apply sv_off0. apply ne_E36.
        -- ne_reg HS (27%bv : bv 5). exact (ne_den27 SK B cx pos regs3 n f HB).
Qed.

(* PHASE J5b -> J6 / J6c: the cut put. No room: full := 1. Room and cut' = 0: n := n + 0. Room and cut' > 0:
   checked_memcpy(w + n, F + 32, cut') at +0x468, to its return J6c. *)
Lemma ne_ph_J5b : forall POST, ne_from SK B POST NE_J6 (ne_J6i SK B) -> ne_from SK B POST NE_J6c (ne_J6ci SK B) ->
  ne_from SK B POST NE_J5b (ne_J5bi SK B).
Proof.
  intros POST HN6 HN6c cx pos S3 memA regs3 mem3 md3 HB HFc (n & f & HJ & HRV).
  pose proof (ne_base_facts SK B cx HB) as (Hw0 & Hw47 & Hwapp & Hal16 & Hceil & Hsp47 & Hwin0 & Hwin1 & Hap &
    Hn0 & Hcut' & Hcut64 & Hs1r & Hs1a).
  pose proof HFc as (_ & _ & _ & HF4096 & HF64 & HFceil & HFapp & HFL & HwF & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HB as ((HJ0 & HGok & _ & _ & _ & Hgp & Htp & _) & _).
  pose proof HJ as (HJX & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNW & Hn0n & _).
  pose proof HNW as (_ & _ & _ & _ & _ & Hnr & Hfr). unfold NL_CHUNK_MAX in Hnr.
  assert (HU := ne_upd5b_ok cx pos regs3 n f HB HRV ltac:(lia)).
  assert (E33 := ne_E33 cx pos regs3 n f). assert (E43 := ne_E43 cx pos regs3 n f).
  assert (HX : ne_xr_ok cx n (@nil YP09.region)) by (left; reflexivity).
  assert (Hef : sv_denot (ne_E cx pos regs3 n f) (SOff 34 0) = w64 f) by (apply sv_off0; apply ne_E34).
  destruct (Z_le_gt_dec (n + ne_cutv (ne_cut cx)) 4096) as [Hroom|Hfull].
  2:{ (* no room: full := 1 *)
    destruct (ne_seat SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ NE_J5b ne_upd5b false []
      [mkAC BC_GEU (SAlu ALU_ADD (SOff 33 0) (SOff 43 0)) (SLit 4097)] HB HFc HJ HU HX
      ltac:(split; [apply (ne_acond_sum_geu _ 33 43 n (ne_cutv (ne_cut cx))); [exact E33 | exact E43 | lia..] | exact I]))
      as (HEI & HS & SHOK).
    pose proof HS as HS0.
    pose (RUN := paj_run_to_x SK B LAWS (n_G cx) HGok (n_XO cx) (n_OUT cx)).
    paj_run_to_tok RUN HS HJX SHOK ne_span (AF_nl_error + NE_J6).
    - exact (ne_awr SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ false [] HB HFc HJ HX).
    - pmkst HS. apply (HN6 cx pos S3 memA); [exact HB | exact HFc |].
      exists n, 1. split.
      + assert (Hen : sv_denot (ne_E cx pos regs3 n f) (SOff 33 0) = w64 n) by (apply sv_off0; exact E33).
        assert (Hef1 : sv_denot (ne_E cx pos regs3 n f) (SLit 1) = w64 1) by reflexivity.
        assert (Hn' : n <= n <= NL_CHUNK_MAX) by (unfold NL_CHUNK_MAX; lia).
        assert (Hf' : 0 <= 1 <= 1) by lia.
        ne_after_run SK B cx pos S3 memA regs3 mem3 md3 n f NE_J5b ne_upd5b false (@nil YP09.region)
          [mkAC BC_GEU (SAlu ALU_ADD (SOff 33 0) (SOff 43 0)) (SLit 4097)] HB HFc HJ HX HS0 HS HJX HFr HG
          n 1 (SOff 33 0) (SLit 1) Hen Hef1 Hn' Hf'.
        * intros _; reflexivity.
        * intros Hcc; discriminate Hcc.
      + ne_rv6_after HS. }
  assert (HLT : acond_ok (ne_E cx pos regs3 n f) (mkAC BC_LTU (SAlu ALU_ADD (SOff 33 0) (SOff 43 0)) (SLit 4097)))
    by (apply (ne_acond_sum_ltu _ 33 43 n (ne_cutv (ne_cut cx))); [exact E33 | exact E43 | lia..]).
  destruct (Z.eq_dec (ne_cutv (ne_cut cx)) 0) as [Hc0|Hc0].
  - (* cut' = 0: no copy *)
    destruct (ne_seat SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ NE_J5b ne_upd5b false []
      [mkAC BC_LTU (SAlu ALU_ADD (SOff 33 0) (SOff 43 0)) (SLit 4097); mkAC BC_EQ (SOff 43 0) (SLit 0)] HB HFc HJ HU HX
      ltac:(split; [exact HLT | split; [apply (ne_acond_eq0 _ 43 (ne_cutv (ne_cut cx))); [exact E43 | lia | exact Hc0] | exact I]]))
      as (HEI & HS & SHOK).
    pose proof HS as HS0.
    pose (RUN := paj_run_to_x SK B LAWS (n_G cx) HGok (n_XO cx) (n_OUT cx)).
    paj_run_to_tok RUN HS HJX SHOK ne_span (AF_nl_error + NE_J6).
    + exact (ne_awr SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ false [] HB HFc HJ HX).
    + pmkst HS. apply (HN6 cx pos S3 memA); [exact HB | exact HFc |].
      exists (n + ne_cutv (ne_cut cx)), f. split.
      * assert (Hen : sv_denot (ne_E cx pos regs3 n f) (SAlu ALU_ADD (SOff 33 0) (SOff 43 0))
                      = w64 (n + ne_cutv (ne_cut cx))).
        { rewrite denot_lit_U, (ne_U_add2 _ 33 43 n (ne_cutv (ne_cut cx)) E33 E43) by lia. reflexivity. }
        assert (Hn' : n <= n + ne_cutv (ne_cut cx) <= NL_CHUNK_MAX) by (unfold NL_CHUNK_MAX; lia).
        ne_after_run SK B cx pos S3 memA regs3 mem3 md3 n f NE_J5b ne_upd5b false (@nil YP09.region)
          [mkAC BC_LTU (SAlu ALU_ADD (SOff 33 0) (SOff 43 0)) (SLit 4097); mkAC BC_EQ (SOff 43 0) (SLit 0)]
          HB HFc HJ HX HS0 HS HJX HFr HG (n + ne_cutv (ne_cut cx)) f (SAlu ALU_ADD (SOff 33 0) (SOff 43 0))
          (SOff 34 0) Hen Hef Hn' Hfr.
        -- intros _; reflexivity.
        -- intros Hcc; discriminate Hcc.
      * ne_rv6_after HS.
  - (* the copy: checked_memcpy(w + n, F + 32, cut') *)
    destruct (ne_seat SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ NE_J5b ne_upd5b false []
      [mkAC BC_LTU (SAlu ALU_ADD (SOff 33 0) (SOff 43 0)) (SLit 4097); mkAC BC_NE (SOff 43 0) (SLit 0)] HB HFc HJ HU HX
      ltac:(split; [exact HLT | split; [apply (ne_acond_ne0 _ 43 (ne_cutv (ne_cut cx))); [exact E43 | lia | exact Hc0] | exact I]]))
      as (HEI & HS & SHOK).
    pose proof HS as HS0.
    pose (RUN := paj_run_x SK B LAWS (n_G cx) HGok (n_XO cx) (n_OUT cx)).
    paj_run_tok RUN HS HJX SHOK ne_span.
    + exact (ne_awr SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ false [] HB HFc HJ HX).
    + lazymatch type of HJX with ajournal_gx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ =>
        set (md4 := mdx) in * end.
      assert (HJc : ne_j SK B cx pos S3 memA (ms_regs ms) (ms_mem ms) md4 n f ne_shB).
      { assert (Hen : sv_denot (ne_E cx pos regs3 n f) (SOff 33 0) = w64 n) by (apply sv_off0; exact E33).
        assert (Hn' : n <= n <= NL_CHUNK_MAX) by (unfold NL_CHUNK_MAX; lia).
        ne_after_run SK B cx pos S3 memA regs3 mem3 md3 n f NE_J5b ne_upd5b false (@nil YP09.region)
          [mkAC BC_LTU (SAlu ALU_ADD (SOff 33 0) (SOff 43 0)) (SLit 4097); mkAC BC_NE (SOff 43 0) (SLit 0)]
          HB HFc HJ HX HS0 HS HJX HFr HG n f (SOff 33 0) (SOff 34 0) Hen Hef Hn' Hfr.
        - intros _; reflexivity.
        - intros Hcc; discriminate Hcc. }
      pose proof HJc as (HJXc & _ & _ & R2c & R3c & R4c & _ & _ & _ & _ & _ & HNWc & _ & HSWc &
        HHVc & _ & HFpc & _ & Hshc & _).
      pose proof HNWc as (_ & _ & Hpresc & _).
      set (c' := ne_cutv (ne_cut cx)) in *.
      assert (A0 : getr (ms_regs ms) 10 = w64 (ne_w cx + n)) by (ne_reg HS (10%bv : bv 5); apply sv_off0; apply ne_E58).
      assert (A1 : getr (ms_regs ms) 11 = w64 (ne_F cx pos + 32)).
      { ne_reg HS (11%bv : bv 5). apply (sv_offc _ 36 (ne_F cx pos) 32 (ne_E36 _ _ _ _ _)). lia. }
      assert (A2 : getr (ms_regs ms) 12 = w64 c') by (ne_reg HS (12%bv : bv 5); apply sv_off0; apply ne_E43).
      assert (RA : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (AF_nl_error + NE_J6c))).
      { ne_reg HS (1%bv : bv 5). cbn [sv_denot]. rewrite (img_env_codeptr _ HEI). reflexivity. }
      assert (SP : spZ (ms_regs ms) = ne_sp1 cx).
      { unfold spZ. rewrite R2c. unfold w64. apply unsigned_lit_small.
        unfold NL_ERROR_AK, NL_ERROR_AFRAME, ESTACK in *. lia. }
      assert (Hsh4 : forall i, (i < 16)%nat ->
                aview SEGS (w_H (n_W cx)) (ms_mem ms) (SHADOW_OFF + ne_F cx pos / 8 + Z.of_nat i) =
                Some (nth i ne_shB 0)) by exact Hshc.
      pmkst HS.
      eapply (SRr_bind SEGS).
      * apply (aj_gx_intrin_at SK SEGS B LAWS pa_segs_low OCpy _ AMEMCPY (n_G cx) (n_XO cx) (n_OUT cx) (n_W cx)
          (ms_regs ms) (ms_mem ms) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
          ((1, pos) :: n_own cx) (n_lyc cx) S3 md4 (n_k cx) (ne_w cx + n) (ne_F cx pos + 32) c' (getr (ms_regs ms) 1)
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
        -- rewrite RA. apply ret_ok_codeptr_v; [cbv [AF_nl_error NE_J6c]; lia | reflexivity].
        -- intros a Ha.
           destruct (ne_w_ajw SK B cx pos S3 memA a HB HFc ltac:(unfold NW_SIZE; lia)) as [[Haw Hxo]|[HGa|HOa]].
           ++ left. split; [exact Haw|]. split; [exact Hxo|]. rewrite SP.
              unfold NW_SIZE, NL_ERROR_AK, NL_ERROR_AFRAME, ESTACK in *. lia.
           ++ right; left. split; [exact HGa|]. replace a with (ne_w cx + (a - ne_w cx)) by lia.
              exact (proj2 (Hpresc (a - ne_w cx) ltac:(unfold NW_SIZE; lia))).
           ++ right; right. exact HOa.
        -- unfold amem_range, kLowMemEnd, kHighMemEnd, NW_SIZE, SHADOW_OFF in *. rewrite C3 in *. lia.
        -- apply (range_addressable_sub _ _ (ne_w cx) NW_SIZE); [exact HSWc | lia | unfold NW_SIZE; lia].
        -- intros Hpos. apply (ne_hull_sub _ (ne_w cx) NW_SIZE); [exact HHVc | lia | unfold NW_SIZE; lia | exact Hpos].
        -- split; [lia|]. split; [lia|]. split.
           { intros a Ha. split.
             - destruct (HFpc (a - ne_F cx pos) ltac:(lia)) as [Hh (b & Hb)].
               replace (ne_F cx pos + (a - ne_F cx pos)) with a in Hh, Hb by lia.
               unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
             - rewrite SP. unfold NL_ERROR_AK, NL_ERROR_AFRAME, ESTACK in *. lia. }
           split; [unfold NW_SIZE in *; lia|]. split.
           { unfold amem_range, kLowMemEnd, kLowShadowBeg, kHighMemEnd in *. rewrite C3 in *. lia. }
           split.
           { apply (range_addressable_sub _ _ (ne_F cx pos + 32) 20); [|lia|lia].
             apply ne_body_ra; [exact HF64 | lia | | |].
             - exact (Hsh4 4%nat ltac:(lia)).
             - exact (Hsh4 5%nat ltac:(lia)).
             - exact (Hsh4 6%nat ltac:(lia)). }
           intros Hpos. apply (ne_F_hull _ (ne_F cx pos) _ _ ne_shB HF64 ltac:(lia) Hsh4); lia.
      * intros W' c'' _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HAP & _ & _ & UN2 & HP2 & Hsbm).
        rewrite RA.
        apply (HN6c cx pos S3 memA regs2 mem2 md2 HB HFc).
        exists n, f. split; [|split].
        -- apply (ne_call_after SK B cx pos S3 memA (ms_regs ms) (ms_mem ms) md4 n f ne_shB regs2 mem2 md2
             (ne_w cx + n) c' HB HFc HJc HJ2 Hsbm HAP UN2 HP2). left. lia.
        -- unfold ne_rv6c. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
             (rewrite (ne_preserved_r _ _ HAP); [|cbn [ne_saved_regs In]; repeat (first [left; reflexivity | right])]).
           ++ ne_reg HS (18%bv : bv 5). apply sv_off0. apply ne_E36.
           ++ ne_reg HS (20%bv : bv 5). apply sv_off0. apply ne_E35.
           ++ ne_reg HS (21%bv : bv 5). apply sv_off0. apply ne_E43.
           ++ ne_reg HS (22%bv : bv 5). apply sv_off0. apply ne_E41.
           ++ ne_reg HS (19%bv : bv 5). apply ne_den19.
           ++ ne_reg HS (24%bv : bv 5). apply sv_off0. apply ne_E38.
           ++ ne_reg HS (25%bv : bv 5). apply sv_off0. apply ne_E36.
           ++ ne_reg HS (27%bv : bv 5). exact (ne_den27 SK B cx pos regs3 n f HB).
        -- exact Hroom.
Qed.

(* PHASE J6c -> J6: n := n + cut' after the copy *)
Lemma ne_ph_J6c : forall POST, ne_from SK B POST NE_J6 (ne_J6i SK B) -> ne_from SK B POST NE_J6c (ne_J6ci SK B).
Proof.
  intros POST HN cx pos S3 memA regs3 mem3 md3 HB HFc (n & f & HJ & HRV & Hroom).
  pose proof (ne_base_facts SK B cx HB) as (Hw0 & Hw47 & _ & _ & _ & _ & _ & _ & _ & _ & Hcut' & Hcut64 & _ & _).
  pose proof HFc as (_ & _ & _ & HF4096 & _ & HFceil & _ & _ & _ & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HB as ((HJ0 & HGok & _) & _).
  pose proof HJ as (HJX & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNW & _).
  pose proof HNW as (_ & _ & _ & _ & _ & Hnr & Hfr). unfold NL_CHUNK_MAX in Hnr.
  assert (HU := ne_upd6c_ok cx pos regs3 n f HB HRV).
  assert (HX : ne_xr_ok cx n (@nil YP09.region)) by (left; reflexivity).
  destruct (ne_seat SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ NE_J6c ne_upd6c false [] [] HB HFc HJ HU HX I)
    as (HEI & HS & SHOK).
  pose proof HS as HS0.
  pose (RUN := paj_run_to_x SK B LAWS (n_G cx) HGok (n_XO cx) (n_OUT cx)).
  paj_run_to_tok RUN HS HJX SHOK ne_span (AF_nl_error + NE_J6).
  - exact (ne_awr SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ false [] HB HFc HJ HX).
  - pmkst HS. apply (HN cx pos S3 memA); [exact HB | exact HFc |].
    exists (n + ne_cutv (ne_cut cx)), f. split.
    + assert (Hen : sv_denot (ne_E cx pos regs3 n f) (SAlu ALU_ADD (SOff 33 0) (SOff 43 0))
                    = w64 (n + ne_cutv (ne_cut cx))).
      { rewrite denot_lit_U, (ne_U_add2 _ 33 43 n (ne_cutv (ne_cut cx)) (ne_E33 _ _ _ _ _) (ne_E43 _ _ _ _ _)) by lia.
        reflexivity. }
      assert (Hef : sv_denot (ne_E cx pos regs3 n f) (SOff 34 0) = w64 f) by (apply sv_off0; apply ne_E34).
      assert (Hn' : n <= n + ne_cutv (ne_cut cx) <= NL_CHUNK_MAX) by (unfold NL_CHUNK_MAX; lia).
      ne_after_run SK B cx pos S3 memA regs3 mem3 md3 n f NE_J6c ne_upd6c false (@nil YP09.region) (@nil acond)
        HB HFc HJ HX HS0 HS HJX HFr HG (n + ne_cutv (ne_cut cx)) f (SAlu ALU_ADD (SOff 33 0) (SOff 43 0)) (SOff 34 0)
        Hen Hef Hn' Hfr.
      * intros _; reflexivity.
      * intros Hcc; discriminate Hcc.
    + ne_rv6_after HS.
Qed.

(* PHASE J6 -> J7: nl_end (`bltu n, at + 4`; the length n - at at w + at) *)
Lemma ne_ph_J6 : forall POST, ne_from SK B POST NE_J7 (ne_J6i SK B) -> ne_from SK B POST NE_J6 (ne_J6i SK B).
Proof.
  intros POST HN cx pos S3 memA regs3 mem3 md3 HB HFc (n & f & HJ & HRV).
  pose proof (ne_base_facts SK B cx HB) as (Hw0 & Hw47 & _ & _ & _ & _ & _ & _ & _ & Hn0 & _ & _ & _ & _).
  pose proof HFc as (_ & _ & _ & HF4096 & _ & HFceil & _ & _ & _ & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HB as ((HJ0 & HGok & _) & _).
  pose proof HJ as (HJX & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNW & Hn0n & _).
  pose proof HNW as (_ & _ & _ & _ & _ & Hnr & Hfr). unfold NL_CHUNK_MAX in Hnr.
  assert (HU := ne_upd6_ok cx pos regs3 n f HB HRV).
  assert (E33 := ne_E33 cx pos regs3 n f). assert (E41 := ne_E41 cx pos regs3 n f).
  assert (Hen : sv_denot (ne_E cx pos regs3 n f) (SOff 33 0) = w64 n) by (apply sv_off0; exact E33).
  assert (Hef : sv_denot (ne_E cx pos regs3 n f) (SOff 34 0) = w64 f) by (apply sv_off0; apply ne_E34).
  assert (Hn' : n <= n <= NL_CHUNK_MAX) by (unfold NL_CHUNK_MAX; lia).
  destruct (Z_lt_le_dec n (ne_n0 cx + 4)) as [Hlt|Hge].
  - (* no room for the length: nothing stored *)
    assert (HX : ne_xr_ok cx n (@nil YP09.region)) by (left; reflexivity).
    destruct (ne_seat SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ NE_J6 ne_upd6 false []
      [mkAC BC_LTU (SOff 33 0) (SOff 41 4)] HB HFc HJ HU HX
      ltac:(split; [apply (ne_acond_atoms_ltu _ 33 41 n (ne_n0 cx) 4 E33 E41); lia | exact I]))
      as (HEI & HS & SHOK).
    pose proof HS as HS0.
    pose (RUN := paj_run_to_x SK B LAWS (n_G cx) HGok (n_XO cx) (n_OUT cx)).
    paj_run_to_tok RUN HS HJX SHOK ne_span (AF_nl_error + NE_J7).
    + exact (ne_awr SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ false [] HB HFc HJ HX).
    + pmkst HS. apply (HN cx pos S3 memA); [exact HB | exact HFc |].
      exists n, f. split.
      * ne_after_run SK B cx pos S3 memA regs3 mem3 md3 n f NE_J6 ne_upd6 false (@nil YP09.region)
          [mkAC BC_LTU (SOff 33 0) (SOff 41 4)] HB HFc HJ HX HS0 HS HJX HFr HG n f (SOff 33 0) (SOff 34 0)
          Hen Hef Hn' Hfr.
        -- intros _; reflexivity.
        -- intros Hcc; discriminate Hcc.
      * ne_rv6_after HS.
  - (* the length n - at, little-endian, at w + at *)
    assert (HX : ne_xr_ok cx n [ne_end_region]) by (right; right; right; split; [reflexivity | lia]).
    destruct (ne_seat SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ NE_J6 ne_upd6 false [ne_end_region]
      [mkAC BC_GEU (SOff 33 0) (SOff 41 4)] HB HFc HJ HU HX
      ltac:(split; [apply (ne_acond_atoms_geu _ 33 41 n (ne_n0 cx) 4 E33 E41); lia | exact I]))
      as (HEI & HS & SHOK).
    pose proof HS as HS0.
    pose (RUN := paj_run_to_x SK B LAWS (n_G cx) HGok (n_XO cx) (n_OUT cx)).
    paj_run_to_tok RUN HS HJX SHOK ne_span (AF_nl_error + NE_J7).
    + exact (ne_awr SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ false [ne_end_region] HB HFc HJ HX).
    + pmkst HS. apply (HN cx pos S3 memA); [exact HB | exact HFc |].
      exists n, f. split.
      * ne_after_run SK B cx pos S3 memA regs3 mem3 md3 n f NE_J6 ne_upd6 false [ne_end_region]
          [mkAC BC_GEU (SOff 33 0) (SOff 41 4)] HB HFc HJ HX HS0 HS HJX HFr HG n f (SOff 33 0) (SOff 34 0)
          Hen Hef Hn' Hfr.
        -- intros _; reflexivity.
        -- intros Hcc; discriminate Hcc.
      * ne_rv6_after HS.
Qed.

End b.
End a.
