(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v, with its module names changed; 259 of its 330 lines of code are new or changed and 1302 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_strkit.v, with its module paths and module names changed; 240 of its 267 lines of code are new or changed and 303 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMW_ex_head.v; 259 of its 305 lines of code are new or changed and 221 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMW_ex_tok_e.v, with its numbers changed; 225 of its 286 lines of code are new or changed and 244 lines of the source are left out. *)
(* G4.ExTok.TokLH, kit for tk_seg_LH (FMW_ex_tok_base.v): expected's ex_token loop body (fuzz_manifest.c:103-108) at
   TK_LH 0x81574 .. 0x815dc of fm.asan (expected.dis lines 274-299): s7 = text + j; bcmp (text + j, text + name, nl);
   the ASan check and the load of text[j + nl] (':' or not); bcmp (text + j + nl + 1, local, ll); then j = 0 goes to
   TK_E, j > 0 to TK_B; every mismatch goes to TK_N.
   The walk's symbolic state at TK_LH: registers are their own atoms, s9 = extra atom 32 (the shadow base); the frame
   (based at sp = F) holds F+8 = local (atom 34) and F+0x10 = text + nl, written q - j with q = text + nl + j (atom 33)
   and j = s10 (atom 26), so that `ld a0, 0x10(sp); add a0, a0, s10` normalizes to atom 33; the byte text[j + nl] is
   atom 35 in a 1-byte region at q. The run writes nothing; the two bcmp calls (aj_bcmp_at) write only [F - 8192, F). *)
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

(* ---- the symbolic state at TK_LH ---- *)
Definition tl_frame : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 208 0 0
    [YP09.mkChunk 8 (CVal 8 (SOff 34 0)); YP09.mkChunk 0x10 (CVal 8 (SAlu ALU_SUB (SOff 33 0) (SOff 26 0)))].
Definition tl_byte : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 35 0))].
Definition tl_regs : list sv := sr_set sr_atoms 25%bv (SOff 32 0).
Definition tl_facts : facts :=
  mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF FW_SB FW_SB 0); (33%nat, mkAF 4096 (2 ^ 47 - 16) 0);
           (35%nat, mkAF 0 255 0)] [] [].
Definition ss_LH : sstate := mkSS TK_LH tl_regs [tl_frame; tl_byte] None tl_facts.
Definition TL_SH : list shent := [mkSHE 33 0 1].
Definition tl_extra (q l c : Z) : list word := [Z_to_bv 64 FW_SB; Z_to_bv 64 q; Z_to_bv 64 l; Z_to_bv 64 c].

(* FMW_plain.v's fw_reg / pl_mk / pl_g, renamed (as G4.ExTok.TokN's tkn_reg / tkn_mk / tkn_g) *)
Ltac tl_reg HS r :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    rewrite (st_ok_restrict_reg segs H E ss ms r HS); change (sr_get (ss_regs ss) r) with e end.
Ltac tl_mk HS := rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl);
  lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?x)] =>
    let v := eval vm_compute in (ss_pc x) in change (ss_pc x) with v end.
Ltac tl_g HS :=
  lazymatch goal with |- getr _ ?r = _ => tl_reg HS r end;
  cbn [sv_denot ew ewset Nat.eqb]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned.
(* an atom below every havoc floor: back to the entry environment *)
Ltac tl_old := repeat first [rewrite ew_havoc_old by lia | progress cbn [ew ewset Nat.eqb]].
(* a run's frame names no writable window: the view outside [lo, hi) keeps its relation to mem0 (FMW_plain.v pl_avw) *)
Ltac tl_av W lo hi :=
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) |- _ =>
    let AVn := fresh "AVn" in
    pose proof (fw_nowin tfibsegs _ _ _ _ _ HFr ltac:(vm_compute; reflexivity)) as AVn;
    lazymatch goal with AV : forall a, _ -> _ -> aview _ _ m0 a = aview _ _ ?mem0 a |- _ =>
      let AV2 := fresh "AVw" in
      assert (AV2 : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
        aview tfibsegs (w_H W) m1 a = aview tfibsegs (w_H W) mem0 a)
        by (intros a Ha Hn; rewrite (AVn a Ha); exact (AV a Ha Hn));
      clear AV AVn; rename AV2 into AVw end end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  repeat match goal with H : context [with_vm_backing (m_vm_lazy (with_vm_backing _ _ _)) _ _] |- _ =>
    rewrite wvb_collapse in H end.

(* ---- list facts ---- *)
Lemma tl_nth_firstn : forall (l : list Z) n i, (i < n)%nat -> nth i (firstn n l) 0 = nth i l 0.
Proof.
  induction l as [|x l IH]; intros n i Hi; destruct n as [|n]; try lia.
  - reflexivity.
  - destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.
Lemma tl_nth_skipn : forall (l : list Z) a i, nth i (skipn a l) 0 = nth (a + i) l 0.
Proof.
  induction l as [|x l IH]; intros a i; destruct a as [|a]; cbn [skipn]; try reflexivity;
    first [destruct i; reflexivity | cbn [Nat.add nth]; apply IH].
Qed.
Lemma tl_firstn_eq : forall (l1 l2 : list Z) a1 a2 n, (a1 + n <= length l1)%nat -> (a2 + n <= length l2)%nat ->
  (firstn n (skipn a1 l1) = firstn n (skipn a2 l2) <->
   forall i, (i < n)%nat -> nth (a1 + i) l1 0 = nth (a2 + i) l2 0).
Proof.
  intros l1 l2 a1 a2 n H1 H2. split.
  - intros Heq i Hi.
    rewrite <- (tl_nth_skipn l1 a1 i), <- (tl_nth_skipn l2 a2 i).
    rewrite <- (tl_nth_firstn (skipn a1 l1) n i Hi), <- (tl_nth_firstn (skipn a2 l2) n i Hi).
    rewrite Heq. reflexivity.
  - intros Hall. apply nth_ext with (d := 0) (d' := 0).
    + rewrite !length_firstn, !length_skipn. lia.
    + intros i Hi. rewrite length_firstn, length_skipn in Hi.
      rewrite (tl_nth_firstn (skipn a1 l1) n i ltac:(lia)), (tl_nth_firstn (skipn a2 l2) n i ltac:(lia)).
      rewrite !tl_nth_skipn. apply Hall. lia.
Qed.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.

(* the bytes of a C string as aview reads them *)
Lemma tl_cstr_byte : forall (W : world tfibsegs) mem p l i, cstr_ok tfibsegs W mem p l -> (i < length l)%nat ->
  aview tfibsegs (w_H W) mem (p + Z.of_nat i) = Some (nth i l 0).
Proof.
  intros W mem p l i ((HG & _) & _) Hi.
  destruct (HG i ltac:(rewrite length_app; cbn [length]; lia)) as [Hv Hr].
  rewrite app_nth1 in Hv, Hr by lia.
  exact (tk_aview_byte W mem _ _ Hv Hr).
Qed.

(* bcmp's answer on two windows of C strings as a list equation *)
Lemma tl_cmp_iff : forall (W : world tfibsegs) mem p1 l1 a1 p2 l2 a2 n,
  cstr_ok tfibsegs W mem p1 l1 -> cstr_ok tfibsegs W mem p2 l2 ->
  (a1 + n <= length l1)%nat -> (a2 + n <= length l2)%nat ->
  ((forall i, 0 <= i < Z.of_nat n ->
      aview tfibsegs (w_H W) mem (p1 + Z.of_nat a1 + i) = aview tfibsegs (w_H W) mem (p2 + Z.of_nat a2 + i)) <->
   firstn n (skipn a1 l1) = firstn n (skipn a2 l2)).
Proof.
  intros W mem p1 l1 a1 p2 l2 a2 n H1 H2 Hn1 Hn2. rewrite (tl_firstn_eq l1 l2 a1 a2 n Hn1 Hn2). split.
  - intros H i Hi. specialize (H (Z.of_nat i) ltac:(lia)).
    replace (p1 + Z.of_nat a1 + Z.of_nat i) with (p1 + Z.of_nat (a1 + i)) in H by lia.
    replace (p2 + Z.of_nat a2 + Z.of_nat i) with (p2 + Z.of_nat (a2 + i)) in H by lia.
    rewrite (tl_cstr_byte W mem p1 l1 (a1 + i) H1 ltac:(lia)),
      (tl_cstr_byte W mem p2 l2 (a2 + i) H2 ltac:(lia)) in H.
    injection H as H. exact H.
  - intros H i Hi.
    replace (p1 + Z.of_nat a1 + i) with (p1 + Z.of_nat (a1 + Z.to_nat i)) by lia.
    replace (p2 + Z.of_nat a2 + i) with (p2 + Z.of_nat (a2 + Z.to_nat i)) by lia.
    rewrite (tl_cstr_byte W mem p1 l1 (a1 + Z.to_nat i) H1 ltac:(lia)),
      (tl_cstr_byte W mem p2 l2 (a2 + Z.to_nat i) H2 ltac:(lia)).
    f_equal. apply H. lia.
Qed.

Lemma tl_src : forall (W : world tfibsegs) mem regs p l a n, cstr_ok tfibsegs W mem p l -> (a + n <= length l)%nat ->
  alloc_ceiling <= spZ regs - ESTACK -> src_ok tfibsegs W regs mem (p + Z.of_nat a) (Z.of_nat n).
Proof.
  intros W mem regs p l a n H Hn Hlo x Hx. pose proof H as (_ & _ & Hc & _).
  split; [|lia].
  replace x with (p + Z.of_nat (Z.to_nat (x - p))) by lia.
  rewrite (tl_cstr_byte W mem p l (Z.to_nat (x - p)) H ltac:(lia)). discriminate.
Qed.

Lemma tl_U_atom_w : forall E n (w : word), ew E n = w -> U E (SOff n 0) = bv_unsigned w.
Proof.
  intros E n w H. rewrite U_SOff, H, Z.add_0_r. apply zcanon_id.
  pose proof (bv_unsigned_in_range 64 w) as R. change (bv_modulus 64) with (2 ^ 64) in R. unfold M64. lia.
Qed.
End k.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* the entry values: q = text + nl + j, local = uri + nl2, c = text[j + nl] *)
Definition tl_q (cx : ecx) (p : tkp) (j : nat) : Z := cx_t cx + Z.of_nat (tk_nl p) + Z.of_nat j.
Definition tl_l (cx : ecx) (p : tkp) : Z := cx_u cx + Z.of_nat (tk_nl2 p).
Definition tl_c (cx : ecx) (p : tkp) (j : nat) : Z := nth (j + tk_nl p) (cx_tb cx) 0.
Definition tl_E (cx : ecx) (p : tkp) (j : nat) (regs3 : bvmap 5 word) : env :=
  Ereg regs3 (tl_extra (tl_q cx p j) (tl_l cx p) (tl_c cx p j)).

Lemma tl_entry : forall cx p j ly3 S3 W3 regs3 mem3 md3,
  tk_at_LH B cx p j ly3 S3 W3 regs3 mem3 md3 ->
  st_ok tfibsegs (tl_E cx p j regs3) ss_LH
    (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 TK_LH) mem3 (seg_rom tfibsegs))).
Proof.
  intros cx p j ly3 S3 W3 regs3 mem3 md3 (HM & HR & R23 & R26 & Hb & Hn).
  pose proof HM as (HX & HC & HSL & V8 & V28 & V10 & V0).
  pose proof HX as (HB & _).
  pose proof HB as ((HPRE & _) & _).
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HC as (HJ & Hbl & HGL & Rsp & Rgp & Rtp & R25 & HSV & HRO & HCt & HCu & HKt & HKu).
  pose proof HCt as ((HGt & _) & Ht4096 & Htc & Ht32 & Htam & _).
  pose proof HCu as (_ & Hu4096 & Huc & _).
  pose proof (tk_decl_facts B cx p HX) as (D1 & D2 & D3 & D4 & D5).
  unfold tk_bound in Hb.
  assert (HSTK : STK_expected = 208 + 8224) by reflexivity.
  destruct (HGt (j + tk_nl p)%nat ltac:(rewrite length_app; cbn [length]; lia)) as [Vc Rc].
  rewrite app_nth1 in Vc, Rc by lia.
  rewrite restrict_mkst_fx.
  unfold tl_E. set (q := tl_q cx p j). set (lv := tl_l cx p). set (c := tl_c cx p j).
  assert (Hq : q = cx_t cx + Z.of_nat (j + tk_nl p)) by (unfold q, tl_q; lia).
  assert (Hlv : lv = cx_u cx + Z.of_nat (tk_nl2 p)) by reflexivity.
  assert (Hcd : c = nth (j + tk_nl p) (cx_tb cx) 0) by reflexivity.
  clearbody q lv c. rewrite <- Hcd in Vc, Rc.
  set (E := Ereg regs3 (tl_extra q lv c)).
  assert (Usp : bv_unsigned (ew E 2) = cx_F cx).
  { subst E. rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl), Rsp. apply unsigned_lit_small.
    unfold cx_F, cx_sp. lia. }
  assert (E26 : ew E 26 = Z_to_bv 64 (Z.of_nat j)) by (subst E; rewrite (ew_Ereg_nat regs3 _ 26 26%bv eq_refl); exact R26).
  assert (E32 : ew E 32 = Z_to_bv 64 FW_SB) by (subst E; exact (ew_Ereg_extra regs3 _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 q) by (subst E; exact (ew_Ereg_extra regs3 _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 lv) by (subst E; exact (ew_Ereg_extra regs3 _ 2)).
  assert (E35 : ew E 35 = Z_to_bv 64 c) by (subst E; exact (ew_Ereg_extra regs3 _ 3)).
  assert (U33 : bv_unsigned (ew E 33) = q) by (rewrite E33; apply unsigned_lit_small; lia).
  assert (U34 : bv_unsigned (ew E 34) = lv) by (rewrite E34; apply unsigned_lit_small; lia).
  unfold ss_LH. apply (entry_st_ok_full tfibsegs); change (Ereg regs3 (tl_extra q lv c)) with E.
  - unfold tl_regs. apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X |].
    cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E32, R25. reflexivity.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok, tl_frame, tl_byte;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite Usp. unfold cx_F, cx_sp in *. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val tfibsegs E _ (spZ (cx_regs cx) - 208) 8 8 (SOff 34 0) lv);
          [cbn [sv_denot]; rewrite Z.add_0_r, U34; reflexivity | cbn; lia | cbn; lia | rewrite Hlv; exact V8].
      * apply (chunk_ok_val tfibsegs E _ (spZ (cx_regs cx) - 208) 0x10 8 (SAlu ALU_SUB (SOff 33 0) (SOff 26 0))
          (cx_t cx + Z.of_nat (tk_nl p))); [| cbn; lia | cbn; lia | exact V10].
        rewrite denot_lit_U, U_SAlu. cbn [zalu_raw].
        rewrite (U_atom E 33 q E33) by lia. rewrite (U_atom E 26 (Z.of_nat j) E26) by lia.
        rewrite zcanon_id by (unfold M64; lia). f_equal. lia.
    + rewrite U33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs E _ q 0 1 (SOff 35 0) c);
        [cbn [sv_denot]; rewrite E35, unsigned_lit_small, Z.add_0_r by lia; reflexivity
        | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r, Hq. exact Vc.
  - apply pairwise_disjoint_of_extents. unfold tl_frame, tl_byte, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U33.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold cx_F, cx_sp in *. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok tl_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, U33, E35, !unsigned_lit_small by (unfold FW_SB; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold cx_F, cx_sp in *.
    replace (spZ (cx_regs cx) - 208) with (spZ (cx_regs cx) + (-13) * 16) by lia. rewrite Z_mod_plus_full.
    unfold FW_SB. repeat split; lia.
Qed.

Hypothesis BCMP : abcmp_realizes tfibsegs B PC_bcmp.

(* a bcmp call at sp = F = sp0 - 208 on two windows of C strings below alloc_ceiling *)
Lemma tl_bcmp : forall W regsT memT ly S W0 mem md lyc Sc mdc sp0 p1 l1 a1 p2 l2 a2 n raw,
  ajournal tfibsegs B STK_expected sp0 [] ly S W0 mem md [] lyc Sc W memT mdc 0 ->
  cstr_ok tfibsegs W memT p1 l1 -> cstr_ok tfibsegs W memT p2 l2 ->
  (a1 + n <= length l1)%nat -> (a2 + n <= length l2)%nat ->
  getr regsT 10 = w64 (p1 + Z.of_nat a1) -> getr regsT 11 = w64 (p2 + Z.of_nat a2) ->
  getr regsT 12 = w64 (Z.of_nat n) ->
  spZ regsT = sp0 - 208 -> alloc_ceiling <= sp0 - 208 - 2 * ESTACK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  SRr tfibsegs W (mkCfg (mkst regsT (Z_to_bv 64 PC_bcmp) memT (seg_rom tfibsegs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : word),
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom tfibsegs)) md2 /\
       ajournal tfibsegs B STK_expected sp0 [] ly S W0 mem md [] lyc Sc W mem2 md2 0 /\
       aregs_preserved regsT regs2 /\ getr regs2 10 = v /\
       (v = w64 0 <-> firstn n (skipn a1 l1) = firstn n (skipn a2 l2)) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 208 - 2 * ESTACK <= a < sp0 - 208) ->
          aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
  intros W regsT memT ly S W0 mem md lyc Sc mdc sp0 p1 l1 a1 p2 l2 a2 n raw
    HJ H1 H2 Hn1 Hn2 Ra0 Ra1 Ra2 Hsp Hlo Hgp Htp Hra Hraw.
  pose proof H1 as (_ & H14096 & H1c & H132 & H1am & H1RA & H1HV & _).
  pose proof H2 as (_ & H24096 & H2c & H232 & H2am & H2RA & H2HV & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (ESTACK = 4096) as Hes by reflexivity.
  assert (HSTK : STK_expected = 208 + 8224) by reflexivity.
  eapply SRr_mono.
  { apply (aj_bcmp_at tfibsegs B LAWS fmw_segs_low PC_bcmp BCMP W regsT memT STK_expected sp0 [] ly S W0 mem md []
      lyc Sc mdc 0 (p1 + Z.of_nat a1) (p2 + Z.of_nat a2) (Z.of_nat n) (-208) raw HJ Ra0 Ra1 Ra2
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
      ltac:(rewrite Hes, HSTK; lia) Hgp Htp Hra Hraw).
    - apply (tl_src W memT regsT p1 l1 a1 n H1 Hn1). lia.
    - apply (tl_src W memT regsT p2 l2 a2 n H2 Hn2). lia.
    - intros q Hq. lia.
    - intros q Hq. lia.
    - unfold amem_range in *. lia.
    - unfold amem_range in *. lia.
    - intros q Hq. apply H1RA. lia.
    - intros Hpos. apply (tk_hull_sub _ p1 (Z.of_nat (length l1) + 1)); [exact H1HV | lia | lia | lia].
    - intros q Hq. apply H2RA. lia.
    - intros Hpos. apply (tk_hull_sub _ p2 (Z.of_nat (length l2) + 1)); [exact H2HV | lia | lia | lia]. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP & Hv & Hcmp & Hfr & Hpres2).
  split; [reflexivity|]. exists regs2, mem2, md2, v.
  split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP|]. split; [exact Hv|].
  split; [exact (iff_trans Hcmp (tl_cmp_iff W memT p1 l1 a1 p2 l2 a2 n H1 H2 Hn1 Hn2))|].
  split; [intros a Ha Hn; apply Hfr; [exact Ha | lia]|].
  exact Hpres2.
Qed.

(* the cuts after the walk: tk_mem and tk_regs carry over from TK_LH *)
Lemma tl_exit : forall cx p ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4,
  tk_mem B cx p ly3 S3 W3 regs3 mem3 md3 -> tk_regs cx p regs3 ->
  ajournal tfibsegs B STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
    [] ly3 S3 W3 mem4 md4 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (cx_F cx - 2 * ESTACK <= a < cx_F cx) ->
     aview tfibsegs (w_H W3) mem4 a = aview tfibsegs (w_H W3) mem3 a) ->
  getr regs4 25 = w64 SHADOW_OFF ->
  getr regs4 2 = getr regs3 2 -> getr regs4 3 = getr regs3 3 -> getr regs4 4 = getr regs3 4 ->
  getr regs4 8 = getr regs3 8 -> getr regs4 18 = getr regs3 18 -> getr regs4 22 = getr regs3 22 ->
  getr regs4 20 = getr regs3 20 -> getr regs4 21 = getr regs3 21 -> getr regs4 24 = getr regs3 24 ->
  getr regs4 27 = getr regs3 27 -> getr regs4 19 = getr regs3 19 -> getr regs4 9 = getr regs3 9 ->
  tk_mem B cx p ly3 S3 W3 regs4 mem4 md4 /\ tk_regs cx p regs4.
Proof.
  intros cx p ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 HM HR HJ4 AV R25 K2 K3 K4 K8 K18 K22 K20 K21 K24 K27 K19 K9.
  pose proof HM as (HX & HC & _).
  pose proof HX as (HB & _).
  pose proof HB as ((HPRE & _) & _).
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof HC as (_ & _ & _ & Rsp & Rgp & Rtp & _).
  assert (HSTK : STK_expected = 208 + 8224) by reflexivity.
  assert (ESTACK = 4096) as Hes by reflexivity.
  split.
  - apply (tk_mem_move B cx p ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 (cx_F cx - 2 * ESTACK) HM HJ4).
    + unfold cx_F, cx_sp. lia.
    + exact AV.
    + rewrite K2. exact Rsp.
    + rewrite K3. exact Rgp.
    + rewrite K4. exact Rtp.
    + exact R25.
  - destruct HR as (R8 & R18 & R22 & R20 & R21 & R24 & R27 & R19 & R9). unfold tk_regs.
    rewrite K8, K18, K22, K20, K21, K24, K27, K19, K9. tauto.
Qed.
End W.
