(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v, with its module names changed; 259 of its 330 lines of code are new or changed and 1302 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_strkit.v, with its module paths and module names changed; 240 of its 267 lines of code are new or changed and 303 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMW_ex_head.v; 259 of its 305 lines of code are new or changed and 221 lines of the source are left out. *)
(* G4.ExTok.TokE: tk_seg_E (FMW_ex_tok_base.v): expected's ex_token right boundary test (fuzz_manifest.c:109-111) at
   TK_E 0x81648 .. 0x816b4 of fm.asan (expected.dis lines 327-354): a0 = s1 + s10 = text + j + nl + 1 + ll, the ASan
   check of its shadow byte, a0 = F+0 + s10 (the same address), lb a0, 0(a0), then eight class branches: c >= 128,
   '\\', '%', ':', '-', '_', a digit, a letter go to TK_N 0x815c4 (no token at j); else a0 = 1 (0x81700) and EX_R
   0x81704 (token true: expected answers 1).
   The run writes nothing. Its symbolic state keeps every register as its own atom (sr_atoms) except s9 = extra atom
   32 (the shadow base); the byte = extra atom 33, its address = extra atom 34 (a 1-byte region based there), and the
   alias s1 + s10 = atom 34 makes both address computations one atom. The frame chunk F+0 holds s1's atom 9.
   The class branches are decided on the byte alone by closed evaluation (FMW_plain.v pl_D pattern), generically: a
   leaf proves name_char c from the branch outcomes on its path by one forallb over the 256 byte values. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC20 YI16 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v ACeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMPstat FMH_Base FMH_Rt FMH_Fn FMW_lib FMW_ex_base FMW_ex_tok_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel expected_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ---- the symbolic state at TK_E ---- *)
Definition te_regs : list sv := sr_set sr_atoms 25%bv (SOff 32 0).
Definition te_frame : YP09.region := YP09.mkRegion (Some 2%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 9 0))].
Definition te_byte : YP09.region := YP09.mkRegion (Some 34%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition te_facts : facts :=
  mkFacts [(32%nat, mkAF FW_SB FW_SB 0); (33%nat, mkAF 0 255 0); (34%nat, mkAF 4096 (2 ^ 47 - 16) 0)] []
    [(SAlu ALU_ADD (SOff 9 0) (SOff 26 0), SOff 34 0)].
Definition ss_E : sstate := mkSS TK_E te_regs [te_frame; te_byte] None te_facts.
Definition TE_SH : list shent := [mkSHE 34 0 1].
Definition te_extra (q c : Z) : list word := [Z_to_bv 64 FW_SB; Z_to_bv 64 c; Z_to_bv 64 q].

(* ---- the class branches, decided on the byte c (atom 33) by closed evaluation (FMW_plain.v pl_D) ---- *)
Definition te_E00 : env := mkEnv (fun _ => Z_to_bv 64 0) (fun _ => []).
Definition te_Ec (c : Z) : env := ewset te_E00 33 (Z_to_bv 64 c).
Definition te_D (cnd : branch_cond) (a b : sv) (c : Z) : bool :=
  branch_taken cnd (sv_denot (te_Ec c) a) (sv_denot (te_Ec c) b).
Lemma te_D_of : forall E c cnd a b, ew E 33 = Z_to_bv 64 c ->
  sv_atoms_in (Nat.eqb 33) a = true -> sv_atoms_in (Nat.eqb 33) b = true ->
  branch_taken cnd (sv_denot E a) (sv_denot E b) = te_D cnd a b c.
Proof.
  intros E c cnd a b HE Ha Hb. unfold te_D.
  assert (HA : env_agree_on (Nat.eqb 33) E (te_Ec c)).
  { intros n Hn. apply Nat.eqb_eq in Hn. subst n. unfold te_Ec. rewrite ew_ewset_same. symmetry. exact HE. }
  rewrite (sv_denot_agree_on _ _ _ a HA Ha), (sv_denot_agree_on _ _ _ b HA Hb). reflexivity.
Qed.
Lemma te_all : forall f : Z -> bool, forallb f (map Z.of_nat (seq 0 256)) = true ->
  forall c, 0 <= c < 256 -> f c = true.
Proof.
  intros f H c Hc. rewrite forallb_forall in H. apply H. apply in_map_iff.
  exists (Z.to_nat c). split; [apply Z2Nat.id; lia | apply in_seq; lia].
Qed.
Lemma te_nth_app0 : forall (l : list Z) k, (k <= length l)%nat -> nth k (l ++ [0]) 0 = nth k l 0.
Proof.
  intros l k Hk. destruct (Nat.lt_ge_cases k (length l)) as [H|H].
  - apply app_nth1. exact H.
  - assert (Hk' : k = length l) by lia. subst k. rewrite app_nth2 by lia. rewrite Nat.sub_diag.
    rewrite (nth_overflow l) by lia. reflexivity.
Qed.

(* the boolean form of a leaf goal  D1 = v1 -> .. -> name_char c = X *)
Ltac te_bool g :=
  lazymatch g with
  | (?l = ?v) -> ?r => let r' := te_bool r in constr:(implb (Bool.eqb l v) r')
  | ?l = ?v => constr:(Bool.eqb l v)
  end.
(* a leaf: name_char c from the branch outcomes D_i on its path *)
Ltac te_leaf c Hcr :=
  repeat match goal with H : te_D _ _ _ c = _ |- _ => revert H end;
  let g := lazymatch goal with |- ?g => g end in
  let b := te_bool g in
  let F := lazymatch eval pattern c in b with ?F c => F end in
  let X := fresh "X" in
  pose proof (te_all F ltac:(vm_compute; reflexivity) c Hcr) as X; cbv beta in X;
  intros;
  repeat match goal with H : te_D _ _ _ c = _ |- _ => rewrite H in X; clear H end;
  cbn [implb Bool.eqb] in X;
  lazymatch goal with |- ManifestModel.name_char c = _ =>
    destruct (ManifestModel.name_char c); cbn in X; first [reflexivity | discriminate X] end.

(* FMW_plain.v's fw_reg / pl_mk / pl_g / pl_av, renamed *)
Ltac te_reg HS r :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    rewrite (st_ok_restrict_reg segs H E ss ms r HS); change (sr_get (ss_regs ss) r) with e end.
Ltac te_g HS :=
  lazymatch goal with |- getr _ ?r = _ => te_reg HS r end;
  cbn [sv_denot ew ewset Nat.eqb]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned.
Ltac te_mk HS := rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl);
  lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?x)] =>
    let v := eval vm_compute in (ss_pc x) in change (ss_pc x) with v end.
Ltac te_av W mem1 :=
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) |- _ =>
    let AVn := fresh "AVn" in
    pose proof (fw_nowin tfibsegs _ _ _ _ _ HFr ltac:(vm_compute; reflexivity)) as AVn;
    lazymatch goal with AV : forall a, _ -> aview _ _ m0 a = aview _ _ mem1 a |- _ =>
      let AV2 := fresh "AV" in
      assert (AV2 : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) m1 a = aview tfibsegs (w_H W) mem1 a)
        by (intros a Ha; rewrite (AVn a Ha); exact (AV a Ha));
      clear AV AVn; rename AV2 into AV end end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  repeat match goal with H : context [with_vm_backing (m_vm_lazy (with_vm_backing _ _ _)) _ _] |- _ =>
    rewrite wvb_collapse in H end.
(* a branch outcome Hc as  te_D cnd a b c = v *)
Ltac te_dec HS E33 c :=
  lazymatch goal with Hc : branch_taken _ _ _ = _ |- _ =>
    let H33 := fresh "H33" in
    lazymatch type of HS with st_ok _ ?Ex _ _ =>
      assert (H33 : ew Ex 33 = Z_to_bv 64 c) by (cbn [ew ewset Nat.eqb]; exact E33) end;
    erewrite (te_D_of _ _ _ _ _ H33) in Hc by reflexivity; clear H33;
    let D := fresh "D" in rename Hc into D end.
(* the walk: run to TK_N; stop there or at EX_R, else split on the class branch and go on *)
Ltac te_go HS HJ SHOK W mem1 E33 c :=
  aj_run_to_tok EX_tbl_ok HS HJ SHOK EX_Bspan TK_N; [awr_ok_tac|];
  te_av W mem1;
  lazymatch type of HS with st_ok _ _ ?ss _ =>
    let b := eval vm_compute in (orb (Z.eqb (ss_pc ss) TK_N) (Z.eqb (ss_pc ss) EX_R)) in
    lazymatch b with
    | true => idtac
    | false =>
      srr_branch_tok EX_tbl_ok HS SHOK EX_Bspan;
      [ te_dec HS E33 c; te_go HS HJ SHOK W mem1 E33 c | te_dec HS E33 c; te_go HS HJ SHOK W mem1 E33 c ]
    end end.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Lemma te_entry : forall regs3 (W3 : world tfibsegs) mem3 F s1v jz q c,
  getr regs3 2 = w64 F -> getr regs3 9 = w64 s1v -> getr regs3 26 = w64 jz -> getr regs3 25 = w64 SHADOW_OFF ->
  q = s1v + jz -> 0 <= s1v -> 0 <= jz -> 4096 <= q -> q + 8 <= F -> F + 8 <= 2 ^ 47 -> 0 <= c <= 255 ->
  val_mem tfibsegs (rdW W3 mem3) F 8 s1v -> val_mem tfibsegs (rdW W3 mem3) q 1 c ->
  st_ok tfibsegs (Ereg regs3 (te_extra q c)) ss_E
    (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 TK_E) mem3 (seg_rom tfibsegs))).
Proof.
  intros regs3 W3 mem3 F s1v jz q c R2 R9 R26 R25 Hq Hs1 Hj Hq4 HqF HF47 Hc VF Vc.
  rewrite restrict_mkst_fx.
  set (E := Ereg regs3 (te_extra q c)).
  assert (E2 : ew E 2 = Z_to_bv 64 F) by (subst E; rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl); exact R2).
  assert (E9 : ew E 9 = Z_to_bv 64 s1v) by (subst E; rewrite (ew_Ereg_nat regs3 _ 9 9%bv eq_refl); exact R9).
  assert (E26 : ew E 26 = Z_to_bv 64 jz) by (subst E; rewrite (ew_Ereg_nat regs3 _ 26 26%bv eq_refl); exact R26).
  assert (E32 : ew E 32 = Z_to_bv 64 FW_SB) by (subst E; exact (ew_Ereg_extra regs3 _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 c) by (subst E; exact (ew_Ereg_extra regs3 _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 q) by (subst E; exact (ew_Ereg_extra regs3 _ 2)).
  unfold ss_E. apply (entry_st_ok_full tfibsegs); change (Ereg regs3 (te_extra q c)) with E.
  - unfold te_regs. apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X |].
    cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E32, R25. reflexivity.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok, te_frame, te_byte;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite E2, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs E _ F 0 8 (SOff 9 0) s1v);
        [cbn [sv_denot]; rewrite E9, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact VF.
    + rewrite E34, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs E _ q 0 1 (SOff 33 0) c);
        [cbn [sv_denot]; rewrite E33, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact Vc.
  - apply pairwise_disjoint_of_extents. unfold te_frame, te_byte, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, E34, !unsigned_lit_small by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert HqF Hq4 HF47. clear. intros. repeat split; lia.
  - split; [|split; [exact I|]].
    + cbn [f_atoms atoms_ok te_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E32, E33, E34, !unsigned_lit_small by (unfold FW_SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. unfold FW_SB. repeat split; lia.
    + cbn [f_alias te_facts alias_ok]. split; [|exact I].
      assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite E9; apply unsigned_lit_small; lia).
      assert (U26 : bv_unsigned (ew E 26) = jz) by (rewrite E26; apply unsigned_lit_small; lia).
      apply U_inj. rewrite U_add_off_atom by (rewrite ?U9, ?U26; unfold M64; lia).
      rewrite U9, U26, (U_atom E 34 q E34) by lia. lia.
Qed.

(* TK_N: tk_mem moves across the run (it writes nothing), the token is absent at j (the right byte is a name char) *)
Lemma te_exit_N : forall cx p j ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4,
  tk_k B cx TK_N (tk_at_N B cx p j) ->
  tk_at_E B cx p j ly3 S3 W3 regs3 mem3 md3 ->
  ajournal tfibsegs B STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
    [] ly3 S3 W3 mem4 md4 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem4 a = aview tfibsegs (w_H W3) mem3 a) ->
  getr regs4 2 = getr regs3 2 -> getr regs4 3 = getr regs3 3 -> getr regs4 4 = getr regs3 4 ->
  getr regs4 25 = getr regs3 25 ->
  getr regs4 8 = getr regs3 8 -> getr regs4 18 = getr regs3 18 -> getr regs4 22 = getr regs3 22 ->
  getr regs4 20 = getr regs3 20 -> getr regs4 21 = getr regs3 21 -> getr regs4 24 = getr regs3 24 ->
  getr regs4 27 = getr regs3 27 -> getr regs4 19 = getr regs3 19 -> getr regs4 9 = getr regs3 9 ->
  getr regs4 26 = getr regs3 26 ->
  ManifestModel.name_char (ManifestModel.byte_at (cx_tb cx) (j + tk_nl p + 1 + tk_ll cx p)) = true ->
  SRr tfibsegs W3 (mkCfg (mkst regs4 (Z_to_bv 64 TK_N) mem4 (seg_rom tfibsegs)) md4) (ex_post B cx).
Proof.
  intros cx p j ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 KN HA HJ4 AV R2 R3 R4 R25 R8 R18 R22 R20 R21 R24 R27 R19
    R9 R26 NC.
  pose proof HA as (HM & HR & G26 & Hb & Hn & Hmid & Hlb).
  pose proof HM as (HX & HC & _).
  pose proof HC as (_ & _ & _ & Rsp & Rgp & Rtp & G25 & _).
  pose proof HX as (HB & _).
  pose proof HB as ((HPRE & _) & _).
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  assert (HSTK : STK_expected = 208 + 8224) by reflexivity.
  apply (KN ly3 S3 W3 regs4 mem4 md4).
  split; [|split; [|split; [|split]]].
  - apply (tk_mem_move B cx p ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 (cx_F cx) HM HJ4).
    + unfold cx_F, cx_sp. lia.
    + intros a Ha _. exact (AV a Ha).
    + rewrite R2. exact Rsp.
    + rewrite R3. exact Rgp.
    + rewrite R4. exact Rtp.
    + rewrite R25. exact G25.
  - unfold tk_regs in *. rewrite R8, R18, R22, R20, R21, R24, R27, R19, R9. exact HR.
  - rewrite R26. exact G26.
  - exact Hb.
  - apply tk_none_S; [exact Hn|]. rewrite (tk_at_mid B cx p j HX Hb Hmid), NC. apply andb_false_r.
Qed.

(* EX_R: the token is present at j (left boundary held, the right byte is not a name char): a0 = 1 = cx_res *)
Lemma te_exit_R : forall cx p j ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4,
  ex_seg_R B ->
  tk_at_E B cx p j ly3 S3 W3 regs3 mem3 md3 ->
  ajournal tfibsegs B STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
    [] ly3 S3 W3 mem4 md4 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem4 a = aview tfibsegs (w_H W3) mem3 a) ->
  getr regs4 2 = getr regs3 2 -> getr regs4 3 = getr regs3 3 -> getr regs4 4 = getr regs3 4 ->
  getr regs4 25 = getr regs3 25 -> getr regs4 10 = w64 1 ->
  ManifestModel.name_char (ManifestModel.byte_at (cx_tb cx) (j + tk_nl p + 1 + tk_ll cx p)) = false ->
  SRr tfibsegs W3 (mkCfg (mkst regs4 (Z_to_bv 64 EX_R) mem4 (seg_rom tfibsegs)) md4) (ex_post B cx).
Proof.
  intros cx p j ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 SEGR HA HJ4 AV R2 R3 R4 R25 R10 NC.
  pose proof HA as (HM & HR & G26 & Hb & Hn & Hmid & Hlb).
  pose proof HM as (HX & HC & _).
  pose proof HC as (_ & _ & _ & Rsp & Rgp & Rtp & G25 & _).
  pose proof HX as (HB & _).
  pose proof HB as ((HPRE & _) & _).
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  assert (HSTK : STK_expected = 208 + 8224) by reflexivity.
  assert (HM4 : tk_mem B cx p ly3 S3 W3 regs4 mem4 md4).
  { apply (tk_mem_move B cx p ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 (cx_F cx) HM HJ4).
    - unfold cx_F, cx_sp. lia.
    - intros a Ha _. exact (AV a Ha).
    - rewrite R2. exact Rsp.
    - rewrite R3. exact Rgp.
    - rewrite R4. exact Rtp.
    - rewrite R25. exact G25. }
  destruct HM4 as (_ & HC4 & _).
  assert (Htok : ManifestModel.token (cx_tb cx) (tk_pre cx p) (tk_loc cx p) = true).
  { apply (tk_true cx p j). rewrite (tk_at_mid B cx p j HX Hb Hmid), NC, Hlb. reflexivity. }
  apply (SEGR cx ly3 S3 W3 regs4 mem4 md4 HB HC4).
  rewrite R10, (tk_scan_one B cx p HX Htok). reflexivity.
Qed.

Ltac te_greg HS EE E32 R25 :=
  te_g HS;
  first [ apply EE; reflexivity | rewrite E32, R25; reflexivity | reflexivity | apply bv_eq; vm_compute; reflexivity ].
Ltac te_fin HS HJ AV EE E32 R25 KN SEGR HA Ec c Rc :=
  te_mk HS;
  lazymatch goal with
  | |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 ?pc) _ _) _) _ =>
    let b := eval vm_compute in (Z.eqb pc TK_N) in
    lazymatch b with
    | true =>
      eapply te_exit_N; [exact KN | exact HA | exact HJ | exact AV | te_greg HS EE E32 R25 .. |
        rewrite Ec; te_leaf c Rc]
    | false =>
      eapply te_exit_R; [exact SEGR | exact HA | exact HJ | exact AV | te_greg HS EE E32 R25 .. |
        rewrite Ec; te_leaf c Rc]
    end
  end.

Theorem tk_seg_E_holds : tk_seg_E B.
Proof.
  intros cx p j SEGR KN ly3 S3 W3 regs3 mem3 md3 HA.
  pose proof LAWS as HL. pose proof fmw_segs_low as Hsegs. pose proof fmw_wx as Hwx.
  pose proof HA as (HM & HR & R26 & Hb & Hn & Hmid & Hlb).
  pose proof HM as (HX & HC & HSL & V8 & V28 & V10 & V0).
  pose proof HC as (HJ & Hbl & HGL & Rsp & Rgp & Rtp & R25 & HSV & HRO & HCt & HCu & HKt & HKu).
  pose proof HCt as ((HGa & HNZ) & H4096 & Hcl & H32 & Ham & HRA & HHV & HT).
  pose proof HR as (R8 & R18 & R22 & R20 & R21 & R24 & R27 & R19 & R9).
  pose proof HX as (HB & _).
  pose proof HB as ((HPRE & _) & _).
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HSTK : STK_expected = 208 + 8224) by reflexivity.
  unfold tk_bound in Hb.
  destruct (HGa (j + tk_nl p + 1 + tk_ll cx p)%nat ltac:(rewrite length_app; cbn [length]; lia)) as [Vc Rc].
  assert (Ec : ManifestModel.byte_at (cx_tb cx) (j + tk_nl p + 1 + tk_ll cx p) =
    nth (j + tk_nl p + 1 + tk_ll cx p) (cx_tb cx ++ [0]) 0)
    by (unfold ManifestModel.byte_at; symmetry; apply te_nth_app0; exact Hb).
  set (c := nth (j + tk_nl p + 1 + tk_ll cx p) (cx_tb cx ++ [0]) 0) in *. clearbody c.
  set (q := cx_t cx + Z.of_nat (j + tk_nl p + 1 + tk_ll cx p)) in *.
  set (s1v := cx_t cx + 1 + Z.of_nat (tk_nl p) + Z.of_nat (tk_ll cx p)) in *.
  assert (Hq8 : q + 8 <= cx_F cx) by (unfold q, cx_F, cx_sp in *; lia).
  pose proof (te_entry regs3 W3 mem3 (cx_F cx) s1v (Z.of_nat j) q c Rsp R9 R26 R25
    ltac:(unfold q, s1v; lia) ltac:(unfold s1v; lia) ltac:(lia) ltac:(unfold q; lia) Hq8
    ltac:(unfold cx_F, cx_sp in *; lia) ltac:(lia) V0 Vc) as HS.
  remember (Ereg regs3 (te_extra q c)) as E eqn:HE.
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs3 r)
    by (intros n r Hnr; rewrite HE; apply ew_Ereg_nat; exact Hnr).
  assert (E32 : ew E 32 = Z_to_bv 64 FW_SB) by (rewrite HE; exact (ew_Ereg_extra regs3 _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 c) by (rewrite HE; exact (ew_Ereg_extra regs3 _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 q) by (rewrite HE; exact (ew_Ereg_extra regs3 _ 2)).
  clear HE.
  assert (SHOK : sh_ok tfibsegs EX_Bx TE_SH E
    (mrestrict (w_H W3) (ms_mem (mkst regs3 (Z_to_bv 64 TK_E) mem3 (seg_rom tfibsegs))))).
  { constructor; [|constructor].
    apply (shent_ok_of_range tfibsegs (w_H W3) mem3 E EX_Bx 34 (cx_t cx) (Z.of_nat (length (cx_tb cx)) + 1) q 0 1).
    - exact HRA.
    - unfold EX_Bx. rewrite (U_atom E 32 FW_SB E32) by (unfold FW_SB; lia). reflexivity.
    - rewrite (U_atom E 34 q E34) by (unfold q; lia). reflexivity.
    - unfold q; lia.
    - unfold q; lia.
    - intros x Hx. cbn [Z.min Z.max] in Hx. unfold amem_range in Ham. unfold SHADOW_OFF. unfold q in *. lia. }
  assert (AV : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W3) mem3 a)
    by reflexivity.
  change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 TK_E) mem3 (seg_rom tfibsegs))) in HJ.
  unfold cfg_at. change (w64 TK_E) with (Z_to_bv 64 TK_E).
  te_go HS HJ SHOK W3 mem3 E33 c.
  all: te_fin HS HJ AV EE E32 R25 KN SEGR HA Ec c Rc.
Qed.
End W.

Print Assumptions tk_seg_E_holds.
