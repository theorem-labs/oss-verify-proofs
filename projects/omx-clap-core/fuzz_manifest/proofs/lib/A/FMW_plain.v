(* G4: plain 0x81778 (fuzz_manifest.c:71-81) on fm.asan, the ASan walk of FMH_Fn.v plain_spec. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC20 YI16 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v ACeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMH_Base FMH_Rt FMH_Fn FMW_lib.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Definition PL_tbl : ctable := Eval vm_compute in fmw_ranges [(A_plain, 66%nat)] TEmpty.
Lemma PL_tbl_ok : table_ok tfibsegs PL_tbl.
Proof.
  change PL_tbl with (fmw_ranges [(A_plain, 66%nat)] TEmpty).
  apply fmw_ranges_ok; [repeat constructor; cbn; unfold A_plain; lia | apply table_ok_empty].
Qed.

Definition PL_Bx : sv := SOff 32 0.
Definition PL_Bspan : Z * Z := (FW_SB, FW_SB + 2 ^ 44 - 1).
Definition P0_facts : facts := mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF FW_SB FW_SB 0)] [] [].
Definition ss_P0 : sstate := mkSS A_plain sr_atoms [fw_stack 32; fw_got; fw_cell 32] None P0_facts.
(* the shared exit 0x81858: a0 = a2, restore ra/s0/s1 from the frame, return *)
Definition PL_R : Z := 0x81858.
Definition pl_frameR : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 32 0 0
    [YP09.mkChunk 8 (CVal 8 (SOff 34 0)); YP09.mkChunk 16 (CVal 8 (SOff 33 0)); YP09.mkChunk 24 (CVal 8 (SOff 32 0))].
Definition ss_R : sstate := mkSS PL_R sr_atoms [pl_frameR] None (mkFacts [(2%nat, mkAF (2^46) (2^47) 4)] [] []).
Ltac fw_reg HS r :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    rewrite (st_ok_restrict_reg segs H E ss ms r HS); change (sr_get (ss_regs ss) r) with e end.
(* the loop head 0x817f0 (fuzz_manifest.c:77-78): s0 = a1 = p (atom 33), a0 = count (atom 34), the byte at p (atom 35),
   a3..a6 the class constants, s1 the shadow base (atom 32); the frame holds ra/s0/s1 of the entry (atoms 36..38) *)
Definition PL_L : Z := 0x817f0.
Definition PL_C6 : Z := 1125899906850819.
Definition pl_regsL : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
    8%bv (SOff 33 0)) 9%bv (SOff 32 0)) 10%bv (SOff 34 0)) 11%bv (SOff 33 0))
    13%bv (SLit (-27))) 14%bv (SLit (-11))) 15%bv (SLit 50)) 16%bv (SLit PL_C6).
Definition pl_frameL : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 32 0 0
    [YP09.mkChunk 8 (CVal 8 (SOff 38 0)); YP09.mkChunk 16 (CVal 8 (SOff 37 0)); YP09.mkChunk 24 (CVal 8 (SOff 36 0))].
Definition pl_byteL : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 35 0))].
Definition pl_factsL : facts :=
  mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF FW_SB FW_SB 0); (33%nat, mkAF 4096 (2^47 - 16) 0);
           (34%nat, mkAF 1 255 0); (35%nat, mkAF 0 255 0)] [] [].
Definition ss_L : sstate := mkSS PL_L pl_regsL [pl_frameL; pl_byteL] None pl_factsL.
Definition PL_SHL : list shent := [mkSHE 33 0 1].
(* the four class branches of the loop body (0x8180c, 0x81814, 0x81820, 0x8182c) as the walk stops at them, decided on
   the byte c alone: a closed valuation with c at atom 35 *)
Definition pl_a1 : sv := SLit (-27).
Definition pl_b1 : sv := SAlu ALU_ADD (SAlu ALU_AND (SOff 35 0) (SLit 223)) (SLit (-91)).
Definition pl_a2 : sv := SLit (-11).
Definition pl_b2 : sv := SOff 35 (-58).
Definition pl_a3 : sv := SLit 50.
Definition pl_b3 : sv := SOff 35 (-45).
Definition pl_a4 : sv := SAlu ALU_AND (SAlu ALU_SRL (SLit PL_C6) (SOff 35 (-45))) (SLit 1).
Definition pl_E00 : env := mkEnv (fun _ => Z_to_bv 64 0) (fun _ => []).
Definition pl_Ec (c : Z) : env := ewset pl_E00 35 (Z_to_bv 64 c).
Definition pl_D (cnd : branch_cond) (a b : sv) (c : Z) : bool := branch_taken cnd (sv_denot (pl_Ec c) a) (sv_denot (pl_Ec c) b).
Definition pl_cls_ok (c : Z) : bool :=
  let d1 := pl_D BC_LTU pl_a1 pl_b1 c in let d2 := pl_D BC_LTU pl_a2 pl_b2 c in
  let d3 := pl_D BC_LTU pl_a3 pl_b3 c in let d4 := pl_D BC_EQ pl_a4 (SLit 0) c in
  implb d1 (ManifestModel.plain_ok c) &&
  implb (negb d1 && d2) (ManifestModel.plain_ok c) &&
  implb (negb d1 && negb d2 && d3) (negb (ManifestModel.plain_ok c)) &&
  implb (negb d1 && negb d2 && negb d3 && d4) (negb (ManifestModel.plain_ok c)) &&
  implb (negb d1 && negb d2 && negb d3 && negb d4) (ManifestModel.plain_ok c).
Lemma pl_cls_all : forall c, 0 <= c < 256 -> pl_cls_ok c = true.
Proof.
  intros c Hc.
  assert (H : forallb pl_cls_ok (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. apply H. apply in_map_iff.
  exists (Z.to_nat c). split; [apply Z2Nat.id; lia | apply in_seq; lia].
Qed.
Lemma pl_D_of : forall E c cnd a b, ew E 35 = Z_to_bv 64 c ->
  sv_atoms_in (Nat.eqb 35) a = true -> sv_atoms_in (Nat.eqb 35) b = true ->
  branch_taken cnd (sv_denot E a) (sv_denot E b) = pl_D cnd a b c.
Proof.
  intros E c cnd a b HE Ha Hb. unfold pl_D.
  assert (HA : env_agree_on (Nat.eqb 35) E (pl_Ec c)).
  { intros n Hn. apply Nat.eqb_eq in Hn. subst n. unfold pl_Ec. rewrite ew_ewset_same. symmetry. exact HE. }
  rewrite (sv_denot_agree_on _ _ _ a HA Ha), (sv_denot_agree_on _ _ _ b HA Hb). reflexivity.
Qed.
Ltac pl_cls_tac c Hc :=
  intros; pose proof (pl_cls_all c Hc) as X; unfold pl_cls_ok in X;
  repeat match goal with H : pl_D _ _ _ c = _ |- _ => rewrite H in X; clear H end;
  cbn [negb andb implb] in X; destruct (ManifestModel.plain_ok c); first [reflexivity | discriminate X].
Lemma pl_cls1 : forall c, 0 <= c < 256 -> pl_D BC_LTU pl_a1 pl_b1 c = true -> ManifestModel.plain_ok c = true.
Proof. intros c Hc. pl_cls_tac c Hc. Qed.
Lemma pl_cls2 : forall c, 0 <= c < 256 -> pl_D BC_LTU pl_a1 pl_b1 c = false -> pl_D BC_LTU pl_a2 pl_b2 c = true ->
  ManifestModel.plain_ok c = true.
Proof. intros c Hc. pl_cls_tac c Hc. Qed.
Lemma pl_cls3 : forall c, 0 <= c < 256 -> pl_D BC_LTU pl_a1 pl_b1 c = false -> pl_D BC_LTU pl_a2 pl_b2 c = false ->
  pl_D BC_LTU pl_a3 pl_b3 c = true -> ManifestModel.plain_ok c = false.
Proof. intros c Hc. pl_cls_tac c Hc. Qed.
Lemma pl_cls4 : forall c, 0 <= c < 256 -> pl_D BC_LTU pl_a1 pl_b1 c = false -> pl_D BC_LTU pl_a2 pl_b2 c = false ->
  pl_D BC_LTU pl_a3 pl_b3 c = false -> pl_D BC_EQ pl_a4 (SLit 0) c = true -> ManifestModel.plain_ok c = false.
Proof. intros c Hc. pl_cls_tac c Hc. Qed.
Lemma pl_cls5 : forall c, 0 <= c < 256 -> pl_D BC_LTU pl_a1 pl_b1 c = false -> pl_D BC_LTU pl_a2 pl_b2 c = false ->
  pl_D BC_LTU pl_a3 pl_b3 c = false -> pl_D BC_EQ pl_a4 (SLit 0) c = false -> ManifestModel.plain_ok c = true.
Proof. intros c Hc. pl_cls_tac c Hc. Qed.

(* 0x817a8 (fuzz_manifest.c:75, s[n - 1]): s0 = s (atom 33), a0 = n (atom 34), a1 = s + n - 1 (atom 36) holding the
   last byte (atom 35); the frame holds ra/s0/s1 of the entry (atoms 37..39) *)
Definition PL_N : Z := 0x817a8.
Definition pl_regsN : list sv :=
  sr_set (sr_set (sr_set (sr_set sr_atoms 8%bv (SOff 33 0)) 9%bv (SOff 32 0)) 10%bv (SOff 34 0)) 11%bv (SOff 36 0).
Definition pl_frameN : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 32 0 0
    [YP09.mkChunk 8 (CVal 8 (SOff 39 0)); YP09.mkChunk 16 (CVal 8 (SOff 38 0)); YP09.mkChunk 24 (CVal 8 (SOff 37 0))].
Definition pl_byteN : YP09.region := YP09.mkRegion (Some 36%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 35 0))].
Definition pl_factsN : facts :=
  mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF FW_SB FW_SB 0); (33%nat, mkAF 4096 (2^47 - 16) 0);
           (34%nat, mkAF 1 255 0); (35%nat, mkAF 0 255 0); (36%nat, mkAF 4096 (2^47 - 16) 0)] [] [].
Definition ss_N : sstate := mkSS PL_N pl_regsN [pl_frameN; pl_byteN] None pl_factsN.
Definition PL_SHN : list shent := [mkSHE 36 0 1].
(* the stack region of the walk right after strlen returns (0x8179c) *)
Definition pl_frameP : YP09.region :=
  YP09.mkRegion (Some 2%nat) (-32) 0 (-32) 0
    [YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].

Lemma pl_last_nth : forall (l : list Z) d, l <> [] -> last l d = nth (pred (length l)) l d.
Proof.
  induction l as [|x l IH]; intros d H; [congruence|]. destruct l as [|y l']; [reflexivity|].
  change (last (x :: y :: l') d) with (last (y :: l') d). rewrite IH by discriminate. reflexivity.
Qed.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis TL : TfibLib B.
Let CELLS : fw_cells B := conj (tl_got_shadow B TL) (tl_shadow_cell B TL).
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

Lemma P0_entry : forall ly S W regs mem md ch,
  afn_pre tfibsegs B STK_plain ly S W regs mem md ch ->
  st_ok tfibsegs (Ereg regs [Z_to_bv 64 FW_SB]) ss_P0 (restrict (w_H W) (mkst regs (Z_to_bv 64 A_plain) mem (seg_rom tfibsegs))).
Proof.
  intros ly S W regs mem md ch HPRE.
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct CELLS as [HBgot HBcell].
  destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
  rewrite restrict_mkst_fx.
  set (E := Ereg regs [Z_to_bv 64 FW_SB]).
  assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E32 : ew E 32 = Z_to_bv 64 FW_SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (HSTK : STK_plain = 32 + 2 * ESTACK) by reflexivity. assert (ESTACK = 4096) as Hes by reflexivity.
  unfold ss_P0. apply (entry_st_ok_full tfibsegs); change (Ereg regs [Z_to_bv 64 FW_SB]) with E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold fw_stack, fw_got, fw_cell.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable tfibsegs). apply Hpres. lia.
    + cbn [base_val]. unfold FW_GOT. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor]. rewrite <- (Z.add_0_l 0x999b0) at 1.
      apply (chunk_ok_val tfibsegs E _ 0 0x999b0 8 (SLit FW_CELL) FW_CELL);
        [reflexivity | unfold FW_CELL; zside | zside |].
      exact (val_mem_of_rdword tfibsegs (w_H W) mem _ _ Kgot).
    + cbn [base_val]. unfold FW_CELL. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor]. rewrite <- (Z.add_0_l 0xa1d78) at 1.
      apply (chunk_ok_val tfibsegs E _ 0 0xa1d78 8 (SOff 32 0) FW_SB);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold FW_SB; zside | zside |].
      exact (val_mem_of_rdword tfibsegs (w_H W) mem _ _ Kcell).
  - apply pairwise_disjoint_of_extents. unfold fw_stack, fw_got, fw_cell, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite Usp.
    unfold FW_GOT, FW_CELL.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil Hstk0 C1. clear. intros. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok P0_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, !unsigned_lit_small by (unfold FW_SB; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hslo Hshi H47 Hceil Hstk0 C1 Hal16. clear. unfold FW_SB. intros. repeat split; lia.
Qed.

Definition pl_frame (W : world tfibsegs) (m : word -> option byte) (sp0 : Z) (regs : bvmap 5 word) : Prop :=
  val_mem tfibsegs (mrestrict (w_H W) m) (sp0 - 8) 8 (bv_unsigned (getr regs 1)) /\
  val_mem tfibsegs (mrestrict (w_H W) m) (sp0 - 16) 8 (bv_unsigned (getr regs 8)) /\
  val_mem tfibsegs (mrestrict (w_H W) m) (sp0 - 24) 8 (bv_unsigned (getr regs 9)).

Lemma R_entry : forall ly S W regs mem md ch mem1 regs1,
  afn_pre tfibsegs B STK_plain ly S W regs mem md ch ->
  pl_frame W mem1 (spZ regs) regs -> getr regs1 2 = w64 (spZ regs - 32) ->
  st_ok tfibsegs (Ereg regs1 [getr regs 1; getr regs 8; getr regs 9]) ss_R
    (restrict (w_H W) (mkst regs1 (Z_to_bv 64 PL_R) mem1 (seg_rom tfibsegs))).
Proof.
  intros ly S W regs mem md ch mem1 regs1 HPRE (F1 & F2 & F3) Rsp.
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HSTK : STK_plain = 32 + 8192) by reflexivity.
  rewrite restrict_mkst_fx.
  set (E := Ereg regs1 [getr regs 1; getr regs 8; getr regs 9]).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs - 32)
    by (subst E; rewrite (ew_Ereg_nat regs1 _ 2 2%bv eq_refl), Rsp; apply unsigned_lit_small; lia).
  assert (E32 : ew E 32 = getr regs 1) by (subst E; exact (ew_Ereg_extra regs1 _ 0)).
  assert (E33 : ew E 33 = getr regs 8) by (subst E; exact (ew_Ereg_extra regs1 _ 1)).
  assert (E34 : ew E 34 = getr regs 9) by (subst E; exact (ew_Ereg_extra regs1 _ 2)).
  unfold ss_R. apply (entry_st_ok_full tfibsegs); change (Ereg regs1 [getr regs 1; getr regs 8; getr regs 9]) with E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold pl_frameR. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    + apply (chunk_ok_val tfibsegs E _ (spZ regs - 32) 8 8 (SOff 34 0) (bv_unsigned (getr regs 9)));
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
        | pose proof (bv_unsigned_in_range 64 (getr regs 9)) as R; change (bv_modulus 64) with (2 ^ 64) in R; exact R
        | cbn; lia |].
      replace (spZ regs - 32 + 8) with (spZ regs - 24) by lia. exact F3.
    + apply (chunk_ok_val tfibsegs E _ (spZ regs - 32) 16 8 (SOff 33 0) (bv_unsigned (getr regs 8)));
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
        | pose proof (bv_unsigned_in_range 64 (getr regs 8)) as R; change (bv_modulus 64) with (2 ^ 64) in R; exact R
        | cbn; lia |].
      replace (spZ regs - 32 + 16) with (spZ regs - 16) by lia. exact F2.
    + apply (chunk_ok_val tfibsegs E _ (spZ regs - 32) 24 8 (SOff 32 0) (bv_unsigned (getr regs 1)));
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
        | pose proof (bv_unsigned_in_range 64 (getr regs 1)) as R; change (bv_modulus 64) with (2 ^ 64) in R; exact R
        | cbn; lia |].
      replace (spZ regs - 32 + 24) with (spZ regs - 8) by lia. exact F1.
  - cbn. tauto.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp. change (2 ^ 4) with 16. split; [|exact I].
    split; [lia|]. replace (spZ regs - 32) with (spZ regs + (-2) * 16) by lia. rewrite Z_mod_plus_full.
    split; [exact Hal16 | lia].
Qed.

Lemma pl_ret : forall ly S W regs mem md ch live peak cnt fail mem1 md1 regs1 (r : Z),
  afn_pre tfibsegs B STK_plain ly S W regs mem md ch ->
  fm_glob tfibsegs W mem live peak cnt fail ->
  ajournal tfibsegs B STK_plain (spZ regs) [] ly S W mem md [] ly S W mem1 md1 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_plain <= a < spZ regs) ->
     aview tfibsegs (w_H W) mem1 a = aview tfibsegs (w_H W) mem a) ->
  pl_frame W mem1 (spZ regs) regs ->
  getr regs1 2 = w64 (spZ regs - 32) -> getr regs1 3 = getr regs 3 -> getr regs1 4 = getr regs 4 ->
  getr regs1 12 = w64 r -> 0 <= r < 2 ^ 64 ->
  (forall q, 18 <= q <= 27 -> getr regs1 (Z_to_bv 5 q) = getr regs (Z_to_bv 5 q)) ->
  SRr tfibsegs W (mkCfg (mkst regs1 (Z_to_bv 64 PL_R) mem1 (seg_rom tfibsegs)) md1)
    (fpost tfibsegs B STK_plain [] regs ly S W mem md 0 (fun ly' S' W' regs' mem' md' =>
       getr regs' 10 = w64 r /\ ablocks B ly' S' = ablocks B ly S /\ fm_glob tfibsegs W' mem' live peak cnt fail)).
Proof.
  intros ly S W regs mem md ch live peak cnt fail mem1 md1 regs1 r HPRE HGL HJ KE HFR Rsp Rgp Rtp R12 Hr Rs.
  pose proof LAWS as HL. pose proof fmw_segs_low as Hsegs. pose proof fmw_wx as Hwx.
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HSTK : STK_plain = 32 + 8192) by reflexivity.
  pose proof (R_entry ly S W regs mem md ch mem1 regs1 HPRE HFR Rsp) as HS.
  set (E := Ereg regs1 [getr regs 1; getr regs 8; getr regs 9]) in *.
  assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs1 q)
    by (intros n q Hn; subst E; apply ew_Ereg_nat; exact Hn).
  assert (E32 : ew E 32 = getr regs 1) by (subst E; exact (ew_Ereg_extra regs1 _ 0)).
  assert (E33 : ew E 33 = getr regs 8) by (subst E; exact (ew_Ereg_extra regs1 _ 1)).
  assert (E34 : ew E 34 = getr regs 9) by (subst E; exact (ew_Ereg_extra regs1 _ 2)).
  assert (SHOK : sh_ok tfibsegs PL_Bx [] E
    (mrestrict (w_H W) (ms_mem (mkst regs1 (Z_to_bv 64 PL_R) mem1 (seg_rom tfibsegs))))) by constructor.
  change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 PL_R) mem1 (seg_rom tfibsegs))) in HJ.
  aj_run_tok PL_tbl_ok HS HJ SHOK PL_Bspan.
  { awr_ok_tac. }
  assert (KL : fw_low tfibsegs (w_H W) mem (ms_mem ms)).
  { intros a Ha. rewrite (fw_aview_frame tfibsegs _ _ _ _ _ HFr a ltac:(lia)).
    - apply KE; lia.
    - intros (rg & Hin & Hrg). cbn [ss_R ss_mem In] in Hin. destruct Hin as [<-|[]].
      cbn [pl_frameR YP09.r_base YP09.r_wlo YP09.r_whi] in Hrg. lia. }
  eapply (SRr_ret_at tfibsegs PL_tbl PL_tbl_ok Hwx W); [exact HS | reflexivity | vm_compute; reflexivity |].
  intros mat'. unfold fpost, apost_base.
  exists ly, S, (ms_regs ms), (ms_mem ms). eexists.
  split.
  { fw_reg HS (1%bv : bv 5). cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned, Hra. reflexivity. }
  split; [apply (ajournal_materialize tfibsegs B HL Hsegs); exact HJ|].
  split.
  { intros q Hq. unfold acallee_saved in Hq.
    assert (Hq' : q = 2 \/ q = 3 \/ q = 4 \/ q = 8 \/ q = 9 \/ q = 18 \/ q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/
      q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27) by lia.
    repeat (destruct Hq' as [->|Hq']); try subst q;
      lazymatch goal with |- getr _ (Z_to_bv 5 ?z) = _ => fw_reg HS (Z_to_bv 5 z) end; cbn [sv_denot];
      rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
      first [ rewrite E33; reflexivity | rewrite E34; reflexivity
            | rewrite (EE 2%nat (Z_to_bv 5 2) eq_refl), (Rsp : getr regs1 (Z_to_bv 5 2) = _), unsigned_lit_small by lia;
              unfold spZ; rewrite Z.sub_add, Z_to_bv_bv_unsigned; reflexivity
            | rewrite (EE 3%nat (Z_to_bv 5 3) eq_refl); exact Rgp
            | rewrite (EE 4%nat (Z_to_bv 5 4) eq_refl); exact Rtp
            | lazymatch goal with |- ew E ?n = getr regs (Z_to_bv 5 ?z) =>
                rewrite (EE n (Z_to_bv 5 z) eq_refl); apply Rs; lia end ]. }
  split.
  { fw_reg HS (10%bv : bv 5). cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 12%nat 12%bv eq_refl). exact R12. }
  split; [reflexivity|].
  exact (fw_glob_low tfibsegs W mem _ live peak cnt fail KL HGL).
Qed.

Definition pl_extraL (regs : bvmap 5 word) (p k c : Z) : list word :=
  [Z_to_bv 64 FW_SB; Z_to_bv 64 p; Z_to_bv 64 k; Z_to_bv 64 c; getr regs 1; getr regs 8; getr regs 9].

Lemma L_entry : forall ly S W regs mem md ch mem1 regs1 p k c,
  afn_pre tfibsegs B STK_plain ly S W regs mem md ch ->
  pl_frame W mem1 (spZ regs) regs -> getr regs1 2 = w64 (spZ regs - 32) ->
  getr regs1 8 = w64 p -> getr regs1 9 = w64 FW_SB -> getr regs1 10 = w64 k -> getr regs1 11 = w64 p ->
  getr regs1 13 = Z_to_bv 64 (-27) -> getr regs1 14 = Z_to_bv 64 (-11) -> getr regs1 15 = Z_to_bv 64 50 ->
  getr regs1 16 = Z_to_bv 64 PL_C6 ->
  4096 <= p <= 2 ^ 47 - 16 -> p + 1 <= alloc_ceiling -> 1 <= k <= 255 -> 0 <= c <= 255 ->
  val_mem tfibsegs (mrestrict (w_H W) mem1) p 1 c ->
  st_ok tfibsegs (Ereg regs1 (pl_extraL regs p k c)) ss_L
    (restrict (w_H W) (mkst regs1 (Z_to_bv 64 PL_L) mem1 (seg_rom tfibsegs))).
Proof.
  intros ly S W regs mem md ch mem1 regs1 p k c HPRE (F1 & F2 & F3) Rsp R8 R9 R10 R11 R13 R14 R15 R16 Hp Hpc Hk Hc Vc.
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HSTK : STK_plain = 32 + 8192) by reflexivity.
  rewrite restrict_mkst_fx.
  set (E := Ereg regs1 (pl_extraL regs p k c)).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs - 32)
    by (subst E; rewrite (ew_Ereg_nat regs1 _ 2 2%bv eq_refl), Rsp; apply unsigned_lit_small; lia).
  assert (E32 : ew E 32 = Z_to_bv 64 FW_SB) by (subst E; exact (ew_Ereg_extra regs1 _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 p) by (subst E; exact (ew_Ereg_extra regs1 _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 k) by (subst E; exact (ew_Ereg_extra regs1 _ 2)).
  assert (E35 : ew E 35 = Z_to_bv 64 c) by (subst E; exact (ew_Ereg_extra regs1 _ 3)).
  assert (E36 : ew E 36 = getr regs 1) by (subst E; exact (ew_Ereg_extra regs1 _ 4)).
  assert (E37 : ew E 37 = getr regs 8) by (subst E; exact (ew_Ereg_extra regs1 _ 5)).
  assert (E38 : ew E 38 = getr regs 9) by (subst E; exact (ew_Ereg_extra regs1 _ 6)).
  unfold ss_L. apply (entry_st_ok_full tfibsegs); change (Ereg regs1 (pl_extraL regs p k c)) with E.
  - unfold pl_regsL.
    repeat (apply regs_ok_pin; [| intros X; discriminate X |]); [apply regs_ok_Ereg|..];
      cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, ?E32, ?E33, ?E34;
      first [exact R8 | exact R9 | exact R10 | exact R11 | exact R13 | exact R14 | exact R15 | exact R16].
  - vm_compute. reflexivity.
  - unfold pl_frameL, pl_byteL. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val tfibsegs E _ (spZ regs - 32) 8 8 (SOff 38 0) (bv_unsigned (getr regs 9)));
          [cbn [sv_denot]; rewrite E38, Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
          | pose proof (bv_unsigned_in_range 64 (getr regs 9)) as R; change (bv_modulus 64) with (2 ^ 64) in R; exact R
          | cbn; lia |].
        replace (spZ regs - 32 + 8) with (spZ regs - 24) by lia. exact F3.
      * apply (chunk_ok_val tfibsegs E _ (spZ regs - 32) 16 8 (SOff 37 0) (bv_unsigned (getr regs 8)));
          [cbn [sv_denot]; rewrite E37, Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
          | pose proof (bv_unsigned_in_range 64 (getr regs 8)) as R; change (bv_modulus 64) with (2 ^ 64) in R; exact R
          | cbn; lia |].
        replace (spZ regs - 32 + 16) with (spZ regs - 16) by lia. exact F2.
      * apply (chunk_ok_val tfibsegs E _ (spZ regs - 32) 24 8 (SOff 36 0) (bv_unsigned (getr regs 1)));
          [cbn [sv_denot]; rewrite E36, Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
          | pose proof (bv_unsigned_in_range 64 (getr regs 1)) as R; change (bv_modulus 64) with (2 ^ 64) in R; exact R
          | cbn; lia |].
        replace (spZ regs - 32 + 24) with (spZ regs - 8) by lia. exact F1.
    + rewrite E33, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs E _ p 0 1 (SOff 35 0) c);
        [cbn [sv_denot]; rewrite E35, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact Vc.
  - apply pairwise_disjoint_of_extents. unfold pl_frameL, pl_byteL, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, E33, unsigned_lit_small by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil Hstk0 C1 Hp Hpc HSTK. clear. intros. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok pl_factsL]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, E33, E34, E35, !unsigned_lit_small by (unfold FW_SB; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    replace (spZ regs - 32) with (spZ regs + (-2) * 16) by lia. rewrite Z_mod_plus_full.
    revert Hslo Hshi H47 Hceil Hstk0 C1 Hal16 Hp Hk Hc. clear. unfold FW_SB. intros. repeat split; lia.
Qed.

Lemma pl_skipn : forall (l : list Z) i, (i < length l)%nat -> skipn i l = nth i l 0 :: skipn (S i) l.
Proof.
  induction l as [|a l IHl]; intros [|i] Hi; cbn in *; try lia; [reflexivity|]. apply IHl. lia.
Qed.

Ltac pl_av W mem1 :=
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
Ltac pl_dec HS E35 c Hc :=
  let H35 := fresh "H35" in
  lazymatch type of HS with st_ok _ ?Ex _ _ =>
    assert (H35 : ew Ex 35 = Z_to_bv 64 c) by (cbn [ew ewset Nat.eqb]; exact E35) end;
  erewrite (pl_D_of _ _ _ _ _ H35) in Hc by reflexivity; clear H35.
Ltac pl_cnt HS E34 Hc :=
  rewrite branch_ne_U in Hc;
  rewrite (U_atom_off _ 34 _ (-1)) in Hc by (first [cbn [ew ewset Nat.eqb]; exact E34 | lia]);
  rewrite U_SLit, zcanon_id in Hc by (unfold M64; lia).
Ltac pl_mk HS := rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl);
  lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?x)] =>
    let v := eval vm_compute in (ss_pc x) in change (ss_pc x) with v end.
Ltac pl_g HS :=
  lazymatch goal with |- getr _ ?r = _ => fw_reg HS r end;
  cbn [sv_denot ew ewset Nat.eqb]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned.

Lemma pl_loop : forall k i ly As W regs mem md ch s l live peak cnt fail regs1 mem1 md1,
  afn_pre tfibsegs B STK_plain ly As W regs mem md ch ->
  fm_glob tfibsegs W mem live peak cnt fail -> cstr_ok tfibsegs W mem s l ->
  (i + S k = length l)%nat -> (length l <= 255)%nat ->
  ajournal tfibsegs B STK_plain (spZ regs) [] ly As W mem md [] ly As W mem1 md1 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_plain <= a < spZ regs) ->
     aview tfibsegs (w_H W) mem1 a = aview tfibsegs (w_H W) mem a) ->
  pl_frame W mem1 (spZ regs) regs ->
  getr regs1 2 = w64 (spZ regs - 32) -> getr regs1 3 = getr regs 3 -> getr regs1 4 = getr regs 4 ->
  getr regs1 8 = w64 (s + Z.of_nat i) -> getr regs1 9 = w64 FW_SB -> getr regs1 10 = w64 (Z.of_nat (S k)) ->
  getr regs1 11 = w64 (s + Z.of_nat i) ->
  getr regs1 13 = Z_to_bv 64 (-27) -> getr regs1 14 = Z_to_bv 64 (-11) -> getr regs1 15 = Z_to_bv 64 50 ->
  getr regs1 16 = Z_to_bv 64 PL_C6 ->
  (forall q, 18 <= q <= 27 -> getr regs1 (Z_to_bv 5 q) = getr regs (Z_to_bv 5 q)) ->
  SRr tfibsegs W (mkCfg (mkst regs1 (Z_to_bv 64 PL_L) mem1 (seg_rom tfibsegs)) md1)
    (fpost tfibsegs B STK_plain [] regs ly As W mem md 0 (fun ly' S' W' regs' mem' md' =>
       getr regs' 10 = w64 (if forallb ManifestModel.plain_ok (skipn i l) then 1 else 0) /\
       ablocks B ly' S' = ablocks B ly As /\ fm_glob tfibsegs W' mem' live peak cnt fail)).
Proof.
  induction k as [k IH] using lt_wf_ind.
  intros i ly As W regs mem md ch s l live peak cnt fail regs1 mem1 md1 HPRE HGL HC Hi Hlen HJ KE HFR
    Rsp Rgp Rtp R8 R9 R10 R11 R13 R14 R15 R16 Rs.
  pose proof LAWS as HL. pose proof fmw_segs_low as Hsegs. pose proof fmw_wx as Hwx.
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HSTK : STK_plain = 32 + 8192) by reflexivity.
  pose proof HC as ((HGa & HNZ) & H4096 & Hcl & H32 & Ham & HRA & HHV & HT).
  destruct (HGa i ltac:(rewrite length_app; cbn [length]; lia)) as [Vc Rc].
  rewrite app_nth1 in Vc, Rc by lia.
  rewrite (pl_skipn l i ltac:(lia)). cbn [forallb].
  set (c := nth i l 0) in *.
  set (p := s + Z.of_nat i) in *.
  assert (KL : fw_low tfibsegs (w_H W) mem mem1) by (intros a Ha; apply KE; lia).
  pose proof (fw_val_low tfibsegs _ mem mem1 p 1 c KL ltac:(lia) ltac:(cbn; lia) Vc) as Vc1.
  pose proof (fw_cstr_low tfibsegs W mem mem1 s l KL HC) as HC1.
  pose proof (L_entry ly As W regs mem md ch mem1 regs1 p (Z.of_nat (S k)) c HPRE HFR Rsp R8 R9 R10 R11 R13 R14 R15 R16
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Vc1) as HS.
  remember (Ereg regs1 (pl_extraL regs p (Z.of_nat (S k)) c)) as E eqn:HE.
  assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs1 q)
    by (intros n q Hn; rewrite HE; apply ew_Ereg_nat; exact Hn).
  assert (E32 : ew E 32 = Z_to_bv 64 FW_SB) by (rewrite HE; exact (ew_Ereg_extra regs1 _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 p) by (rewrite HE; exact (ew_Ereg_extra regs1 _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 (Z.of_nat (S k))) by (rewrite HE; exact (ew_Ereg_extra regs1 _ 2)).
  assert (E35 : ew E 35 = Z_to_bv 64 c) by (rewrite HE; exact (ew_Ereg_extra regs1 _ 3)).
  clear HE.
  assert (SHOK : sh_ok tfibsegs PL_Bx PL_SHL E
    (mrestrict (w_H W) (ms_mem (mkst regs1 (Z_to_bv 64 PL_L) mem1 (seg_rom tfibsegs))))).
  { constructor; [|constructor].
    apply (shent_ok_of_range tfibsegs (w_H W) mem1 E PL_Bx 33 s (Z.of_nat (length l) + 1) p 0 1).
    - destruct HC1 as (_ & _ & _ & _ & _ & HRA1 & _). exact HRA1.
    - unfold PL_Bx. rewrite (U_atom E 32 FW_SB E32) by (unfold FW_SB; lia). reflexivity.
    - rewrite (U_atom E 33 p E33) by lia. reflexivity.
    - lia.
    - lia.
    - intros x Hx. cbn [Z.min Z.max] in Hx. unfold amem_range in Ham. unfold SHADOW_OFF. lia. }
  assert (AV : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) mem1 a = aview tfibsegs (w_H W) mem1 a)
    by reflexivity.
  change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 PL_L) mem1 (seg_rom tfibsegs))) in HJ.
  aj_run_tok PL_tbl_ok HS HJ SHOK PL_Bspan.
  { awr_ok_tac. }
  pl_av W mem1.
  srr_branch_tok PL_tbl_ok HS SHOK PL_Bspan.
  { pl_dec HS E35 c Hc. pose proof (pl_cls1 c ltac:(lia) Hc) as OKc. clear Hc. rewrite OKc. cbn [andb].
    aj_run_tok PL_tbl_ok HS HJ SHOK PL_Bspan; [awr_ok_tac|]. pl_av W mem1.
    srr_branch_tok PL_tbl_ok HS SHOK PL_Bspan.
    { pl_cnt HS E34 Hc. apply Bool.negb_true_iff, Z.eqb_neq in Hc.
      destruct k as [|k']; [exfalso; lia|].
      aj_run_to_tok PL_tbl_ok HS HJ SHOK PL_Bspan PL_L; [awr_ok_tac|]. pl_av W mem1.
      pl_mk HS.
      eapply (IH k' (Nat.lt_succ_diag_r k') (S i) ly As W regs mem md ch s l live peak cnt fail _ _ _ HPRE HGL HC
        ltac:(lia) Hlen HJ).
      + intros a Ha Hn. rewrite (AV a Ha). exact (KE a Ha Hn).
      + destruct HFR as (F1 & F2 & F3). split; [|split]; (eapply fw_val_eqv; [exact AV | lia | cbn; lia | assumption]).
      + pl_g HS. rewrite (EE 2%nat 2%bv eq_refl). exact Rsp.
      + pl_g HS. rewrite (EE 3%nat 3%bv eq_refl). exact Rgp.
      + pl_g HS. rewrite (EE 4%nat 4%bv eq_refl). exact Rtp.
      + pl_g HS. rewrite E33, unsigned_lit_small by lia. unfold w64; f_equal; unfold p; lia.
      + pl_g HS. rewrite E32. reflexivity.
      + pl_g HS. rewrite E34, unsigned_lit_small by lia. unfold w64; f_equal; lia.
      + pl_g HS. rewrite E33, unsigned_lit_small by lia. unfold w64; f_equal; unfold p; lia.
      + pl_g HS. reflexivity.
      + pl_g HS. reflexivity.
      + pl_g HS. reflexivity.
      + pl_g HS. reflexivity.
      + intros q Hq. assert (Hq' : q = 18 \/ q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/ q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27) by lia.
        repeat (destruct Hq' as [->|Hq']); try subst q; pl_g HS;
          lazymatch goal with |- ew E ?n = getr regs (Z_to_bv 5 ?z) => rewrite (EE n (Z_to_bv 5 z) eq_refl); apply Rs; lia end. }
    { pl_cnt HS E34 Hc. apply Bool.negb_false_iff, Z.eqb_eq in Hc.
      destruct k as [|k']; [|exfalso; lia].
      rewrite skipn_all2 by lia. cbn [forallb].
      aj_run_to_tok PL_tbl_ok HS HJ SHOK PL_Bspan PL_R; [awr_ok_tac|]. pl_av W mem1.
      pl_mk HS.
      eapply (pl_ret ly As W regs mem md ch live peak cnt fail _ _ _ 1 HPRE HGL HJ).
      + intros a Ha Hn. rewrite (AV a Ha). exact (KE a Ha Hn).
      + destruct HFR as (F1 & F2 & F3). split; [|split]; (eapply fw_val_eqv; [exact AV | lia | cbn; lia | assumption]).
      + pl_g HS. rewrite (EE 2%nat 2%bv eq_refl). exact Rsp.
      + pl_g HS. rewrite (EE 3%nat 3%bv eq_refl). exact Rgp.
      + pl_g HS. rewrite (EE 4%nat 4%bv eq_refl). exact Rtp.
      + pl_g HS. reflexivity.
      + lia.
      + intros q Hq. assert (Hq' : q = 18 \/ q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/ q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27) by lia.
        repeat (destruct Hq' as [->|Hq']); try subst q; pl_g HS;
          lazymatch goal with |- ew E ?n = getr regs (Z_to_bv 5 ?z) => rewrite (EE n (Z_to_bv 5 z) eq_refl); apply Rs; lia end. } }
  { pl_dec HS E35 c Hc. rename Hc into D1.
    aj_run_tok PL_tbl_ok HS HJ SHOK PL_Bspan; [awr_ok_tac|]. pl_av W mem1.
    srr_branch_tok PL_tbl_ok HS SHOK PL_Bspan.
    { pl_dec HS E35 c Hc. pose proof (pl_cls2 c ltac:(lia) D1 Hc) as OKc. clear Hc. rewrite OKc. cbn [andb].
      aj_run_tok PL_tbl_ok HS HJ SHOK PL_Bspan; [awr_ok_tac|]. pl_av W mem1.
      srr_branch_tok PL_tbl_ok HS SHOK PL_Bspan.
      { pl_cnt HS E34 Hc. apply Bool.negb_true_iff, Z.eqb_neq in Hc.
        destruct k as [|k']; [exfalso; lia|].
        aj_run_to_tok PL_tbl_ok HS HJ SHOK PL_Bspan PL_L; [awr_ok_tac|]. pl_av W mem1.
        pl_mk HS.
        eapply (IH k' (Nat.lt_succ_diag_r k') (S i) ly As W regs mem md ch s l live peak cnt fail _ _ _ HPRE HGL HC
          ltac:(lia) Hlen HJ).
        + intros a Ha Hn. rewrite (AV a Ha). exact (KE a Ha Hn).
        + destruct HFR as (F1 & F2 & F3). split; [|split]; (eapply fw_val_eqv; [exact AV | lia | cbn; lia | assumption]).
        + pl_g HS. rewrite (EE 2%nat 2%bv eq_refl). exact Rsp.
        + pl_g HS. rewrite (EE 3%nat 3%bv eq_refl). exact Rgp.
        + pl_g HS. rewrite (EE 4%nat 4%bv eq_refl). exact Rtp.
        + pl_g HS. rewrite E33, unsigned_lit_small by lia. unfold w64; f_equal; unfold p; lia.
        + pl_g HS. rewrite E32. reflexivity.
        + pl_g HS. rewrite E34, unsigned_lit_small by lia. unfold w64; f_equal; lia.
        + pl_g HS. rewrite E33, unsigned_lit_small by lia. unfold w64; f_equal; unfold p; lia.
        + pl_g HS. reflexivity.
        + pl_g HS. reflexivity.
        + pl_g HS. reflexivity.
        + pl_g HS. reflexivity.
        + intros q Hq. assert (Hq' : q = 18 \/ q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/ q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27) by lia.
          repeat (destruct Hq' as [->|Hq']); try subst q; pl_g HS;
            lazymatch goal with |- ew E ?n = getr regs (Z_to_bv 5 ?z) => rewrite (EE n (Z_to_bv 5 z) eq_refl); apply Rs; lia end. }
      { pl_cnt HS E34 Hc. apply Bool.negb_false_iff, Z.eqb_eq in Hc.
        destruct k as [|k']; [|exfalso; lia].
        rewrite skipn_all2 by lia. cbn [forallb].
        aj_run_to_tok PL_tbl_ok HS HJ SHOK PL_Bspan PL_R; [awr_ok_tac|]. pl_av W mem1.
        pl_mk HS.
        eapply (pl_ret ly As W regs mem md ch live peak cnt fail _ _ _ 1 HPRE HGL HJ).
        + intros a Ha Hn. rewrite (AV a Ha). exact (KE a Ha Hn).
        + destruct HFR as (F1 & F2 & F3). split; [|split]; (eapply fw_val_eqv; [exact AV | lia | cbn; lia | assumption]).
        + pl_g HS. rewrite (EE 2%nat 2%bv eq_refl). exact Rsp.
        + pl_g HS. rewrite (EE 3%nat 3%bv eq_refl). exact Rgp.
        + pl_g HS. rewrite (EE 4%nat 4%bv eq_refl). exact Rtp.
        + pl_g HS. reflexivity.
        + lia.
        + intros q Hq. assert (Hq' : q = 18 \/ q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/ q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27) by lia.
          repeat (destruct Hq' as [->|Hq']); try subst q; pl_g HS;
            lazymatch goal with |- ew E ?n = getr regs (Z_to_bv 5 ?z) => rewrite (EE n (Z_to_bv 5 z) eq_refl); apply Rs; lia end. } }
    { pl_dec HS E35 c Hc. rename Hc into D2.
      aj_run_tok PL_tbl_ok HS HJ SHOK PL_Bspan; [awr_ok_tac|]. pl_av W mem1.
      srr_branch_tok PL_tbl_ok HS SHOK PL_Bspan.
      { pl_dec HS E35 c Hc. pose proof (pl_cls3 c ltac:(lia) D1 D2 Hc) as BADc. rewrite BADc. cbn [andb].
        aj_run_to_tok PL_tbl_ok HS HJ SHOK PL_Bspan PL_R; [awr_ok_tac|]. pl_av W mem1.
        pl_mk HS.
        eapply (pl_ret ly As W regs mem md ch live peak cnt fail _ _ _ 0 HPRE HGL HJ).
        + intros a Ha Hn. rewrite (AV a Ha). exact (KE a Ha Hn).
        + destruct HFR as (F1 & F2 & F3). split; [|split]; (eapply fw_val_eqv; [exact AV | lia | cbn; lia | assumption]).
        + pl_g HS. rewrite (EE 2%nat 2%bv eq_refl). exact Rsp.
        + pl_g HS. rewrite (EE 3%nat 3%bv eq_refl). exact Rgp.
        + pl_g HS. rewrite (EE 4%nat 4%bv eq_refl). exact Rtp.
        + pl_g HS. reflexivity.
        + lia.
        + intros q Hq. assert (Hq' : q = 18 \/ q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/ q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27) by lia.
          repeat (destruct Hq' as [->|Hq']); try subst q; pl_g HS;
            lazymatch goal with |- ew E ?n = getr regs (Z_to_bv 5 ?z) => rewrite (EE n (Z_to_bv 5 z) eq_refl); apply Rs; lia end. }
      { pl_dec HS E35 c Hc. rename Hc into D3.
        aj_run_tok PL_tbl_ok HS HJ SHOK PL_Bspan; [awr_ok_tac|]. pl_av W mem1.
        srr_branch_tok PL_tbl_ok HS SHOK PL_Bspan.
        { pl_dec HS E35 c Hc. pose proof (pl_cls4 c ltac:(lia) D1 D2 D3 Hc) as BADc. rewrite BADc. cbn [andb].
          aj_run_to_tok PL_tbl_ok HS HJ SHOK PL_Bspan PL_R; [awr_ok_tac|]. pl_av W mem1.
          pl_mk HS.
          eapply (pl_ret ly As W regs mem md ch live peak cnt fail _ _ _ 0 HPRE HGL HJ).
          + intros a Ha Hn. rewrite (AV a Ha). exact (KE a Ha Hn).
          + destruct HFR as (F1 & F2 & F3). split; [|split]; (eapply fw_val_eqv; [exact AV | lia | cbn; lia | assumption]).
          + pl_g HS. rewrite (EE 2%nat 2%bv eq_refl). exact Rsp.
          + pl_g HS. rewrite (EE 3%nat 3%bv eq_refl). exact Rgp.
          + pl_g HS. rewrite (EE 4%nat 4%bv eq_refl). exact Rtp.
          + pl_g HS. reflexivity.
          + lia.
          + intros q Hq. assert (Hq' : q = 18 \/ q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/ q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27) by lia.
            repeat (destruct Hq' as [->|Hq']); try subst q; pl_g HS;
              lazymatch goal with |- ew E ?n = getr regs (Z_to_bv 5 ?z) => rewrite (EE n (Z_to_bv 5 z) eq_refl); apply Rs; lia end. }
        { pl_dec HS E35 c Hc. pose proof (pl_cls5 c ltac:(lia) D1 D2 D3 Hc) as OKc. clear Hc. rewrite OKc. cbn [andb].
          aj_run_tok PL_tbl_ok HS HJ SHOK PL_Bspan; [awr_ok_tac|]. pl_av W mem1.
          srr_branch_tok PL_tbl_ok HS SHOK PL_Bspan.
          { pl_cnt HS E34 Hc. apply Bool.negb_true_iff, Z.eqb_neq in Hc.
            destruct k as [|k']; [exfalso; lia|].
            aj_run_to_tok PL_tbl_ok HS HJ SHOK PL_Bspan PL_L; [awr_ok_tac|]. pl_av W mem1.
            pl_mk HS.
            eapply (IH k' (Nat.lt_succ_diag_r k') (S i) ly As W regs mem md ch s l live peak cnt fail _ _ _ HPRE HGL HC
              ltac:(lia) Hlen HJ).
            + intros a Ha Hn. rewrite (AV a Ha). exact (KE a Ha Hn).
            + destruct HFR as (F1 & F2 & F3). split; [|split]; (eapply fw_val_eqv; [exact AV | lia | cbn; lia | assumption]).
            + pl_g HS. rewrite (EE 2%nat 2%bv eq_refl). exact Rsp.
            + pl_g HS. rewrite (EE 3%nat 3%bv eq_refl). exact Rgp.
            + pl_g HS. rewrite (EE 4%nat 4%bv eq_refl). exact Rtp.
            + pl_g HS. rewrite E33, unsigned_lit_small by lia. unfold w64; f_equal; unfold p; lia.
            + pl_g HS. rewrite E32. reflexivity.
            + pl_g HS. rewrite E34, unsigned_lit_small by lia. unfold w64; f_equal; lia.
            + pl_g HS. rewrite E33, unsigned_lit_small by lia. unfold w64; f_equal; unfold p; lia.
            + pl_g HS. reflexivity.
            + pl_g HS. reflexivity.
            + pl_g HS. reflexivity.
            + pl_g HS. reflexivity.
            + intros q Hq. assert (Hq' : q = 18 \/ q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/ q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27) by lia.
              repeat (destruct Hq' as [->|Hq']); try subst q; pl_g HS;
                lazymatch goal with |- ew E ?n = getr regs (Z_to_bv 5 ?z) => rewrite (EE n (Z_to_bv 5 z) eq_refl); apply Rs; lia end. }
          { pl_cnt HS E34 Hc. apply Bool.negb_false_iff, Z.eqb_eq in Hc.
            destruct k as [|k']; [|exfalso; lia].
            rewrite skipn_all2 by lia. cbn [forallb].
            aj_run_to_tok PL_tbl_ok HS HJ SHOK PL_Bspan PL_R; [awr_ok_tac|]. pl_av W mem1.
            pl_mk HS.
            eapply (pl_ret ly As W regs mem md ch live peak cnt fail _ _ _ 1 HPRE HGL HJ).
            + intros a Ha Hn. rewrite (AV a Ha). exact (KE a Ha Hn).
            + destruct HFR as (F1 & F2 & F3). split; [|split]; (eapply fw_val_eqv; [exact AV | lia | cbn; lia | assumption]).
            + pl_g HS. rewrite (EE 2%nat 2%bv eq_refl). exact Rsp.
            + pl_g HS. rewrite (EE 3%nat 3%bv eq_refl). exact Rgp.
            + pl_g HS. rewrite (EE 4%nat 4%bv eq_refl). exact Rtp.
            + pl_g HS. reflexivity.
            + lia.
            + intros q Hq. assert (Hq' : q = 18 \/ q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/ q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27) by lia.
              repeat (destruct Hq' as [->|Hq']); try subst q; pl_g HS;
                lazymatch goal with |- ew E ?n = getr regs (Z_to_bv 5 ?z) => rewrite (EE n (Z_to_bv 5 z) eq_refl); apply Rs; lia end. } } } } }
Qed.

Lemma pl_frame_of : forall E ss W ms regs,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> nth_error (ss_mem ss) 0 = Some pl_frameP ->
  bv_unsigned (ew E 2) = spZ regs -> ew E 1 = getr regs 1 -> ew E 8 = getr regs 8 -> ew E 9 = getr regs 9 ->
  pl_frame W (ms_mem ms) (spZ regs) regs.
Proof.
  intros E ss W ms regs HS Hn E2 E1 E8 E9.
  pose proof (fw_region_nth tfibsegs E ss _ 0 _ HS Hn) as HR. rewrite restrict_mem in HR. unfold pl_frameP in HR.
  unfold pl_frame. split; [|split].
  - replace (spZ regs - 8) with (spZ regs + (-8)) by lia.
    apply (fw_field tfibsegs E _ 2 (spZ regs) _ (-32) 0 (-32) 0 (-8) 8 (SOff 1 0) (bv_unsigned (getr regs 1)) HR E2);
      [cbn; tauto | cbn [sv_denot]; rewrite E1, Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
      | pose proof (bv_unsigned_in_range 64 (getr regs 1)) as R; change (bv_modulus 64) with (2 ^ 64) in R; exact R
      | cbn; lia].
  - replace (spZ regs - 16) with (spZ regs + (-16)) by lia.
    apply (fw_field tfibsegs E _ 2 (spZ regs) _ (-32) 0 (-32) 0 (-16) 8 (SOff 8 0) (bv_unsigned (getr regs 8)) HR E2);
      [cbn; tauto | cbn [sv_denot]; rewrite E8, Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
      | pose proof (bv_unsigned_in_range 64 (getr regs 8)) as R; change (bv_modulus 64) with (2 ^ 64) in R; exact R
      | cbn; lia].
  - replace (spZ regs - 24) with (spZ regs + (-24)) by lia.
    apply (fw_field tfibsegs E _ 2 (spZ regs) _ (-32) 0 (-32) 0 (-24) 8 (SOff 9 0) (bv_unsigned (getr regs 9)) HR E2);
      [cbn; tauto | cbn [sv_denot]; rewrite E9, Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
      | pose proof (bv_unsigned_in_range 64 (getr regs 9)) as R; change (bv_modulus 64) with (2 ^ 64) in R; exact R
      | cbn; lia].
Qed.

Definition pl_extraN (regs : bvmap 5 word) (s n c q : Z) : list word :=
  [Z_to_bv 64 FW_SB; Z_to_bv 64 s; Z_to_bv 64 n; Z_to_bv 64 c; Z_to_bv 64 q; getr regs 1; getr regs 8; getr regs 9].

Lemma N_entry : forall ly S W regs mem md ch mem1 regs1 s n c,
  afn_pre tfibsegs B STK_plain ly S W regs mem md ch ->
  pl_frame W mem1 (spZ regs) regs -> getr regs1 2 = w64 (spZ regs - 32) ->
  getr regs1 8 = w64 s -> getr regs1 9 = w64 FW_SB -> getr regs1 10 = w64 n -> getr regs1 11 = w64 (s + n - 1) ->
  4096 <= s -> s + n + 8 <= alloc_ceiling -> 1 <= n <= 255 -> 0 <= c <= 255 ->
  val_mem tfibsegs (mrestrict (w_H W) mem1) (s + n - 1) 1 c ->
  st_ok tfibsegs (Ereg regs1 (pl_extraN regs s n c (s + n - 1))) ss_N
    (restrict (w_H W) (mkst regs1 (Z_to_bv 64 PL_N) mem1 (seg_rom tfibsegs))).
Proof.
  intros ly S W regs mem md ch mem1 regs1 s n c HPRE (F1 & F2 & F3) Rsp R8 R9 R10 R11 Hs Hsn Hn Hc Vc.
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HSTK : STK_plain = 32 + 8192) by reflexivity.
  rewrite restrict_mkst_fx.
  set (q := s + n - 1) in *.
  set (E := Ereg regs1 (pl_extraN regs s n c q)).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs - 32)
    by (subst E; rewrite (ew_Ereg_nat regs1 _ 2 2%bv eq_refl), Rsp; apply unsigned_lit_small; lia).
  assert (E32 : ew E 32 = Z_to_bv 64 FW_SB) by (subst E; exact (ew_Ereg_extra regs1 _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 s) by (subst E; exact (ew_Ereg_extra regs1 _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 n) by (subst E; exact (ew_Ereg_extra regs1 _ 2)).
  assert (E35 : ew E 35 = Z_to_bv 64 c) by (subst E; exact (ew_Ereg_extra regs1 _ 3)).
  assert (E36 : ew E 36 = Z_to_bv 64 q) by (subst E; exact (ew_Ereg_extra regs1 _ 4)).
  assert (E37 : ew E 37 = getr regs 1) by (subst E; exact (ew_Ereg_extra regs1 _ 5)).
  assert (E38 : ew E 38 = getr regs 8) by (subst E; exact (ew_Ereg_extra regs1 _ 6)).
  assert (E39 : ew E 39 = getr regs 9) by (subst E; exact (ew_Ereg_extra regs1 _ 7)).
  unfold ss_N. apply (entry_st_ok_full tfibsegs); change (Ereg regs1 (pl_extraN regs s n c q)) with E.
  - unfold pl_regsN.
    repeat (apply regs_ok_pin; [| intros X; discriminate X |]); [apply regs_ok_Ereg|..];
      cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, ?E32, ?E33, ?E34, ?E36;
      first [exact R8 | exact R9 | exact R10 | exact R11].
  - vm_compute. reflexivity.
  - unfold pl_frameN, pl_byteN. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val tfibsegs E _ (spZ regs - 32) 8 8 (SOff 39 0) (bv_unsigned (getr regs 9)));
          [cbn [sv_denot]; rewrite E39, Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
          | pose proof (bv_unsigned_in_range 64 (getr regs 9)) as R; change (bv_modulus 64) with (2 ^ 64) in R; exact R
          | cbn; lia |].
        replace (spZ regs - 32 + 8) with (spZ regs - 24) by lia. exact F3.
      * apply (chunk_ok_val tfibsegs E _ (spZ regs - 32) 16 8 (SOff 38 0) (bv_unsigned (getr regs 8)));
          [cbn [sv_denot]; rewrite E38, Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
          | pose proof (bv_unsigned_in_range 64 (getr regs 8)) as R; change (bv_modulus 64) with (2 ^ 64) in R; exact R
          | cbn; lia |].
        replace (spZ regs - 32 + 16) with (spZ regs - 16) by lia. exact F2.
      * apply (chunk_ok_val tfibsegs E _ (spZ regs - 32) 24 8 (SOff 37 0) (bv_unsigned (getr regs 1)));
          [cbn [sv_denot]; rewrite E37, Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
          | pose proof (bv_unsigned_in_range 64 (getr regs 1)) as R; change (bv_modulus 64) with (2 ^ 64) in R; exact R
          | cbn; lia |].
        replace (spZ regs - 32 + 24) with (spZ regs - 8) by lia. exact F1.
    + rewrite E36, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs E _ q 0 1 (SOff 35 0) c);
        [cbn [sv_denot]; rewrite E35, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact Vc.
  - apply pairwise_disjoint_of_extents. unfold pl_frameN, pl_byteN, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, E36, unsigned_lit_small by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil Hstk0 C1 Hs Hsn Hn HSTK. clear. unfold q. intros. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok pl_factsN]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, E33, E34, E35, E36, !unsigned_lit_small by (unfold FW_SB, q; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    replace (spZ regs - 32) with (spZ regs + (-2) * 16) by lia. rewrite Z_mod_plus_full.
    revert Hslo Hshi H47 Hceil Hstk0 C1 Hal16 Hs Hsn Hn Hc. clear. unfold FW_SB, q. intros. repeat split; lia.
Qed.

Lemma pl_N_run : forall ly As W regs mem md ch s l live peak cnt fail regs1 mem1 md1,
  afn_pre tfibsegs B STK_plain ly As W regs mem md ch ->
  fm_glob tfibsegs W mem live peak cnt fail -> cstr_ok tfibsegs W mem s l ->
  (1 <= length l <= 255)%nat ->
  ajournal tfibsegs B STK_plain (spZ regs) [] ly As W mem md [] ly As W mem1 md1 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_plain <= a < spZ regs) ->
     aview tfibsegs (w_H W) mem1 a = aview tfibsegs (w_H W) mem a) ->
  pl_frame W mem1 (spZ regs) regs ->
  getr regs1 2 = w64 (spZ regs - 32) -> getr regs1 3 = getr regs 3 -> getr regs1 4 = getr regs 4 ->
  getr regs1 8 = w64 s -> getr regs1 9 = w64 FW_SB -> getr regs1 10 = w64 (Z.of_nat (length l)) ->
  getr regs1 11 = w64 (s + Z.of_nat (length l) - 1) ->
  (forall q, 18 <= q <= 27 -> getr regs1 (Z_to_bv 5 q) = getr regs (Z_to_bv 5 q)) ->
  SRr tfibsegs W (mkCfg (mkst regs1 (Z_to_bv 64 PL_N) mem1 (seg_rom tfibsegs)) md1)
    (fpost tfibsegs B STK_plain [] regs ly As W mem md 0 (fun ly' S' W' regs' mem' md' =>
       getr regs' 10 = w64 (if ManifestModel.plain_name l then 1 else 0) /\
       ablocks B ly' S' = ablocks B ly As /\ fm_glob tfibsegs W' mem' live peak cnt fail)).
Proof.
  intros ly As W regs mem md ch s l live peak cnt fail regs1 mem1 md1 HPRE HGL HC Hlen HJ KE HFR
    Rsp Rgp Rtp R8 R9 R10 R11 Rs.
  pose proof LAWS as HL. pose proof fmw_segs_low as Hsegs. pose proof fmw_wx as Hwx.
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HSTK : STK_plain = 32 + 8192) by reflexivity.
  pose proof HC as ((HGa & HNZ) & H4096 & Hcl & H32 & Ham & HRA & HHV & HT).
  set (n := Z.of_nat (length l)) in *.
  destruct (HGa (pred (length l)) ltac:(rewrite length_app; cbn [length]; lia)) as [Vc Rc].
  rewrite app_nth1 in Vc, Rc by lia.
  set (c := nth (pred (length l)) l 0) in *.
  replace (s + Z.of_nat (pred (length l))) with (s + n - 1) in Vc by (unfold n; lia).
  assert (KL : fw_low tfibsegs (w_H W) mem mem1) by (intros a Ha; apply KE; lia).
  pose proof (fw_val_low tfibsegs _ mem mem1 (s + n - 1) 1 c KL ltac:(lia) ltac:(cbn; unfold n; lia) Vc) as Vc1.
  pose proof (fw_cstr_low tfibsegs W mem mem1 s l KL HC) as HC1.
  pose proof (N_entry ly As W regs mem md ch mem1 regs1 s n c HPRE HFR Rsp R8 R9 R10 R11
    ltac:(lia) ltac:(unfold n; lia) ltac:(unfold n; lia) ltac:(lia) Vc1) as HS.
  remember (Ereg regs1 (pl_extraN regs s n c (s + n - 1))) as E eqn:HE.
  assert (EE : forall k (q : bv 5), Z.of_nat k = bv_unsigned q -> ew E k = getr regs1 q)
    by (intros k q Hk; rewrite HE; apply ew_Ereg_nat; exact Hk).
  assert (E32 : ew E 32 = Z_to_bv 64 FW_SB) by (rewrite HE; exact (ew_Ereg_extra regs1 _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 s) by (rewrite HE; exact (ew_Ereg_extra regs1 _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 n) by (rewrite HE; exact (ew_Ereg_extra regs1 _ 2)).
  assert (E35 : ew E 35 = Z_to_bv 64 c) by (rewrite HE; exact (ew_Ereg_extra regs1 _ 3)).
  assert (E36 : ew E 36 = Z_to_bv 64 (s + n - 1)) by (rewrite HE; exact (ew_Ereg_extra regs1 _ 4)).
  clear HE.
  assert (SHOK : sh_ok tfibsegs PL_Bx PL_SHN E
    (mrestrict (w_H W) (ms_mem (mkst regs1 (Z_to_bv 64 PL_N) mem1 (seg_rom tfibsegs))))).
  { constructor; [|constructor].
    apply (shent_ok_of_range tfibsegs (w_H W) mem1 E PL_Bx 36 s (n + 1) (s + n - 1) 0 1).
    - destruct HC1 as (_ & _ & _ & _ & _ & HRA1 & _). exact HRA1.
    - unfold PL_Bx. rewrite (U_atom E 32 FW_SB E32) by (unfold FW_SB; lia). reflexivity.
    - rewrite (U_atom E 36 (s + n - 1) E36) by (unfold n in *; lia). reflexivity.
    - unfold n in *; lia.
    - unfold n in *; lia.
    - intros x Hx. cbn [Z.min Z.max] in Hx. unfold amem_range in Ham. unfold SHADOW_OFF. unfold n in *; lia. }
  assert (AV : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) mem1 a = aview tfibsegs (w_H W) mem1 a)
    by reflexivity.
  change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 PL_N) mem1 (seg_rom tfibsegs))) in HJ.
  aj_run_tok PL_tbl_ok HS HJ SHOK PL_Bspan.
  { awr_ok_tac. }
  pl_av W mem1.
  assert (LASTc : last l 0 = c).
  { unfold c. apply pl_last_nth. intros ->. cbn in Hlen. lia. }
  srr_branch_tok PL_tbl_ok HS SHOK PL_Bspan.
  { rewrite branch_ne_U in Hc.
    rewrite (U_atom _ 35 c) in Hc by (first [cbn [ew ewset Nat.eqb]; exact E35 | lia]).
    rewrite U_SLit, zcanon_id in Hc by (unfold M64; lia).
    apply Bool.negb_true_iff, Z.eqb_neq in Hc.
    assert (PN : ManifestModel.plain_name l = forallb ManifestModel.plain_ok (skipn 0 l)).
    { destruct l as [|x l']; [cbn in Hlen; lia|]. cbn [ManifestModel.plain_name skipn].
      rewrite LASTc. destruct (Z.eqb_spec c 46); [lia|]. reflexivity. }
    rewrite PN. clear PN.
    aj_run_to_tok PL_tbl_ok HS HJ SHOK PL_Bspan PL_L; [awr_ok_tac|]. pl_av W mem1.
    pl_mk HS.
    eapply (pl_loop (pred (length l)) 0 ly As W regs mem md ch s l live peak cnt fail _ _ _ HPRE HGL HC
      ltac:(lia) ltac:(lia) HJ).
    + intros a Ha Hn. rewrite (AV a Ha). exact (KE a Ha Hn).
    + destruct HFR as (F1 & F2 & F3). split; [|split]; (eapply fw_val_eqv; [exact AV | lia | cbn; lia | assumption]).
    + pl_g HS. rewrite (EE 2%nat 2%bv eq_refl). exact Rsp.
    + pl_g HS. rewrite (EE 3%nat 3%bv eq_refl). exact Rgp.
    + pl_g HS. rewrite (EE 4%nat 4%bv eq_refl). exact Rtp.
    + pl_g HS. rewrite E33. unfold w64; f_equal; lia.
    + pl_g HS. rewrite E32. reflexivity.
    + pl_g HS. rewrite E34. unfold w64; f_equal; unfold n; lia.
    + pl_g HS. rewrite E33. unfold w64; f_equal; lia.
    + pl_g HS. first [reflexivity | apply bv_eq; vm_compute; reflexivity].
    + pl_g HS. first [reflexivity | apply bv_eq; vm_compute; reflexivity].
    + pl_g HS. first [reflexivity | apply bv_eq; vm_compute; reflexivity].
    + pl_g HS. first [reflexivity | apply bv_eq; vm_compute; reflexivity].
    + intros q Hq. assert (Hq' : q = 18 \/ q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/ q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27) by lia.
      repeat (destruct Hq' as [->|Hq']); try subst q; pl_g HS;
        lazymatch goal with |- ew E ?k = getr regs (Z_to_bv 5 ?z) => rewrite (EE k (Z_to_bv 5 z) eq_refl); apply Rs; lia end. }
  { rewrite branch_ne_U in Hc.
    rewrite (U_atom _ 35 c) in Hc by (first [cbn [ew ewset Nat.eqb]; exact E35 | lia]).
    rewrite U_SLit, zcanon_id in Hc by (unfold M64; lia).
    apply Bool.negb_false_iff, Z.eqb_eq in Hc.
    assert (PN : ManifestModel.plain_name l = false).
    { destruct l as [|x l']; [cbn in Hlen; lia|]. cbn [ManifestModel.plain_name].
      rewrite LASTc, Hc. reflexivity. }
    rewrite PN. clear PN.
    aj_run_to_tok PL_tbl_ok HS HJ SHOK PL_Bspan PL_R; [awr_ok_tac|]. pl_av W mem1.
    pl_mk HS.
    eapply (pl_ret ly As W regs mem md ch live peak cnt fail _ _ _ 0 HPRE HGL HJ).
    + intros a Ha Hn. rewrite (AV a Ha). exact (KE a Ha Hn).
    + destruct HFR as (F1 & F2 & F3). split; [|split]; (eapply fw_val_eqv; [exact AV | lia | cbn; lia | assumption]).
    + pl_g HS. rewrite (EE 2%nat 2%bv eq_refl). exact Rsp.
    + pl_g HS. rewrite (EE 3%nat 3%bv eq_refl). exact Rgp.
    + pl_g HS. rewrite (EE 4%nat 4%bv eq_refl). exact Rtp.
    + pl_g HS. first [reflexivity | apply bv_eq; vm_compute; reflexivity].
    + lia.
    + intros q Hq. assert (Hq' : q = 18 \/ q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/ q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27) by lia.
      repeat (destruct Hq' as [->|Hq']); try subst q; pl_g HS;
        lazymatch goal with |- ew E ?k = getr regs (Z_to_bv 5 ?z) => rewrite (EE k (Z_to_bv 5 z) eq_refl); apply Rs; lia end. }
Qed.

(* the main path's runs write nothing, but their frame names the prologue's window [sp0 - 32, sp0) *)
Ltac pl_avw W mem0 lo hi E1o Usp :=
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) |- _ =>
    let AVn := fresh "AVn" in
    assert (AVn : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
      aview tfibsegs (w_H W) m1 a = aview tfibsegs (w_H W) m0 a)
      by (apply (fw_win tfibsegs _ _ _ _ _ lo hi HFr);
          lazymatch goal with |- Forall _ ?rs => let v := eval vm_compute in rs in change rs with v end;
          repeat apply Forall_cons; try apply Forall_nil;
          cbn [YP09.r_whi YP09.r_wlo YP09.r_base base_val];
          first [left; lia | right; cbn [ew ewset Nat.eqb]; rewrite ?E1o by lia; rewrite Usp; lia]);
    lazymatch goal with AV : forall a, _ -> _ -> aview _ _ m0 a = aview _ _ mem0 a |- _ =>
      let AV2 := fresh "AVw" in
      assert (AV2 : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
        aview tfibsegs (w_H W) m1 a = aview tfibsegs (w_H W) mem0 a)
        by (intros a Ha Hn; rewrite (AVn a Ha Hn); exact (AV a Ha Hn));
      clear AV AVn; rename AV2 into AVw end end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  repeat match goal with H : context [with_vm_backing (m_vm_lazy (with_vm_backing _ _ _)) _ _] |- _ =>
    rewrite wvb_collapse in H end.
Ltac pl_fr HS E1o EE Usp :=
  lazymatch type of HS with st_ok _ ?Ex ?ss (restrict _ ?ms) =>
    let HF := fresh "HFR" in
    pose proof (pl_frame_of Ex ss _ ms _ HS ltac:(vm_compute; reflexivity)
      ltac:(cbn [ew ewset Nat.eqb]; rewrite E1o by lia; exact Usp)
      ltac:(cbn [ew ewset Nat.eqb]; rewrite E1o by lia; apply EE; reflexivity)
      ltac:(cbn [ew ewset Nat.eqb]; rewrite E1o by lia; apply EE; reflexivity)
      ltac:(cbn [ew ewset Nat.eqb]; rewrite E1o by lia; apply EE; reflexivity)) as HF end.

Hypothesis IMG : fm_img_facts tfibsegs B.
Hypothesis STRLEN : astrlen_realizes tfibsegs B PC_strlen.

Theorem plain_spec_holds : plain_spec tfibsegs B.
Proof.
  unfold plain_spec.
  intros ly S W regs mem md ch s l live peak cnt fail [HPRE HRO] HGL Hs HC Hlen.
  pose proof LAWS as HL. pose proof fmw_segs_low as Hsegs. pose proof fmw_wx as Hwx.
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HSTK : STK_plain = 32 + 8192) by reflexivity.
  set (sp0 := spZ regs) in *.
  pose proof (P0_entry ly S W regs mem md ch HPRE) as HS.
  assert (SHOK : sh_ok tfibsegs PL_Bx [] (Ereg regs [Z_to_bv 64 FW_SB])
    (mrestrict (w_H W) (ms_mem (mkst regs (Z_to_bv 64 A_plain) mem (seg_rom tfibsegs))))) by constructor.
  pose proof (ajournal_init tfibsegs B STK_plain [] ly S W regs mem md ch HPRE) as HJ.
  set (E0 := Ereg regs [Z_to_bv 64 FW_SB]) in *.
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = getr regs r)
    by (intros n r Hn; subst E0; apply ew_Ereg_nat; exact Hn).
  assert (Usp : bv_unsigned (ew E0 2) = sp0) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
  unfold cfg_at. change (w64 A_plain) with (Z_to_bv 64 A_plain).
  change mem with (ms_mem (mkst regs (Z_to_bv 64 A_plain) mem (seg_rom tfibsegs))) in HJ at 2.
  aj_run_tok PL_tbl_ok HS HJ SHOK PL_Bspan.
  { awr_ok_tac. exact Usp. }
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - STK_plain <= a < sp0) ->
     aview tfibsegs (w_H W) (ms_mem ms) a = aview tfibsegs (w_H W) mem a).
  { intros a Ha Hn. apply (fw_aview_frame tfibsegs _ _ _ _ _ HFr a Ha).
    intros (r & Hin & Hr). cbn [ss_P0 ss_mem In fw_stack fw_got fw_cell] in Hin.
    pose proof Usp as Usp'. unfold E0 in Usp'.
    destruct Hin as [<-|[<-|[<-|[]]]];
      cbn [fw_stack fw_got fw_cell YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      [first [rewrite Usp in Hr | rewrite Usp' in Hr]; lia | lia | lia]. }
  assert (KL : fw_low tfibsegs (w_H W) mem (ms_mem ms)) by (intros a Ha; apply KE; lia).
  clear HF HFr.
  rreg HS (10%bv : bv 5) Ra0. rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp.
  rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
  eapply SRr_bind.
  { eapply (aj_ro_at tfibsegs B HL Hsegs PC_strlen STK_RT_STR (fun v => v = Z.of_nat (length l))
      W (ms_regs ms) (ms_mem ms) STK_plain sp0 [] ly S W mem md [] ly S _ 0 (-32) (Z_to_bv 64 0x8179c) HJ).
    - unfold spZ. rewrite Rsp. cbn [sv_denot]. rewrite Usp. apply unsigned_lit_small. lia.
    - reflexivity.
    - lia.
    - unfold STK_RT_STR, ESTACK. lia.
    - unfold STK_RT_STR, ESTACK. lia.
    - rewrite Rgp, (EE 3%nat 3%bv eq_refl). exact Hgp.
    - rewrite Rtp, (EE 4%nat 4%bv eq_refl). exact Htp.
    - exact Rra.
    - vm_compute. reflexivity.
    - intros HPK. apply (STRLEN ly S W (ms_regs ms) (ms_mem ms) _ s l HPK).
      + exact (proj1 (IMG ly S W (ms_mem ms) _ (proj1 HJ) (fw_rodata_low tfibsegs B _ mem _ Hsegs KL HRO))).
      + rewrite Ra0, (EE 10%nat 10%bv eq_refl). exact Hs.
      + exact (fw_cstr_low tfibsegs W mem _ s l KL HC). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hvr & Hvl & Hfr2 & Hpres2).
  lazymatch type of HS with st_ok _ _ ?ss _ =>
    let K := eval vm_compute in (run_K 0 PL_Bx [] ss) in
    jafter_call_keep HS K regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2 end.
  match type of HS2 with ?tt -> _ => assert (HK : tt) end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
    eapply (fw_region_kept tfibsegs E0 (w_H W) (ms_mem ms) mem2 2 sp0); [exact Usp | | exact Hpres2].
    intros a Ha. apply Hfr2; [lia | unfold STK_RT_STR, ESTACK; lia]. }
  specialize (HS2 HK). clear HK HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  assert (KE2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - STK_plain <= a < sp0) ->
     aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) mem a).
  { intros a Ha Hn. rewrite Hfr2 by (unfold STK_RT_STR, ESTACK; lia). apply KE; assumption. }
  clear KE KL Hfr2. rename KE2 into KE.
  clear SHOK. lazymatch type of HS with st_ok _ ?Ex _ (restrict _ ?msx) =>
    assert (SHOK : sh_ok tfibsegs PL_Bx [] Ex (mrestrict (w_H W) (ms_mem msx))) by constructor end.
  change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 530332) mem2 (seg_rom tfibsegs))) in HJ2.
  clear HJ. rename HJ2 into HJ.
  set (E1 := havoc E0 33 (map (getr regs2) CLOB)) in *.
  assert (E1o : forall k, (k < 33)%nat -> ew E1 k = ew E0 k) by (intros k Hk; apply ew_havoc_old; exact Hk).
  assert (E37 : ew E1 37 = Z_to_bv 64 (Z.of_nat (length l))).
  { change 37%nat with (33 + 4)%nat. unfold E1. rewrite (ew_havoc_new E0 33 _ 4 (Z_to_bv 64 0)) by (cbn; lia).
    transitivity (getr regs2 10); [reflexivity|]. rewrite Hv, Hvl. reflexivity. }
  assert (E10 : ew E1 10 = Z_to_bv 64 s) by (rewrite E1o by lia; rewrite (EE 10%nat 10%bv eq_refl); exact Hs).
  assert (E32' : ew E1 32 = Z_to_bv 64 FW_SB) by (rewrite E1o by lia; unfold E0; exact (ew_Ereg_extra regs _ 0)).
  assert (AVw : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 32 <= a < sp0) ->
    aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) mem2 a) by reflexivity.
  srr_branch_tok PL_tbl_ok HS SHOK PL_Bspan.
  { rewrite branch_eq_U, (U_atom E1 37 (Z.of_nat (length l)) E37), U_SLit in Hc by lia.
    change (zcanon 0) with 0 in Hc. apply Z.eqb_eq in Hc.
    destruct l as [|x l']; [|cbn [length] in Hc; lia]. cbn [ManifestModel.plain_name].
    aj_run_to_tok PL_tbl_ok HS HJ SHOK PL_Bspan PL_R; [awr_ok_tac; try (rewrite ?E1o by lia; exact Usp)|].
    pl_avw W mem2 (sp0 - 32) sp0 E1o Usp. pl_fr HS E1o EE Usp.
    pl_mk HS.
    eapply (pl_ret ly S W regs mem md ch live peak cnt fail _ _ _ 0 HPRE HGL HJ).
    + intros a Ha Hn. rewrite (AVw a Ha ltac:(lia)). exact (KE a Ha Hn).
    + exact HFR.
    + pl_g HS. rewrite E1o, Usp by lia. unfold w64; f_equal; lia.
    + pl_g HS. rewrite E1o by lia. apply EE. reflexivity.
    + pl_g HS. rewrite E1o by lia. apply EE. reflexivity.
    + pl_g HS. first [reflexivity | apply bv_eq; vm_compute; reflexivity].
    + lia.
    + intros q Hq. assert (Hq' : q = 18 \/ q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/ q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27) by lia.
      repeat (destruct Hq' as [->|Hq']); try subst q; pl_g HS; rewrite E1o by lia; apply EE; reflexivity. }
  { rewrite branch_eq_U, (U_atom E1 37 (Z.of_nat (length l)) E37), U_SLit in Hc by lia.
    change (zcanon 0) with 0 in Hc. apply Z.eqb_neq in Hc.
    aj_run_to_tok PL_tbl_ok HS HJ SHOK PL_Bspan PL_N; [awr_ok_tac; try (rewrite ?E1o by lia; exact Usp)|].
    pl_avw W mem2 (sp0 - 32) sp0 E1o Usp. pl_fr HS E1o EE Usp.
    pl_mk HS.
    eapply (pl_N_run ly S W regs mem md ch s l live peak cnt fail _ _ _ HPRE HGL HC ltac:(lia) HJ).
    + intros a Ha Hn. rewrite (AVw a Ha ltac:(lia)). exact (KE a Ha Hn).
    + exact HFR.
    + pl_g HS. rewrite E1o, Usp by lia. unfold w64; f_equal; lia.
    + pl_g HS. rewrite E1o by lia. apply EE. reflexivity.
    + pl_g HS. rewrite E1o by lia. apply EE. reflexivity.
    + pl_g HS. exact E10.
    + pl_g HS. exact E32'.
    + pl_g HS. exact E37.
    + pose proof HC as (_ & Hs4 & Hsc & _). fw_reg HS (11%bv : bv 5). unfold w64. apply fw_sv_U.
      rewrite (U_add_off_atom E1 10 (-1) 37 0); rewrite ?E10, ?E37; rewrite ?unsigned_lit_small by lia; unfold M64; lia.
    + intros q Hq. assert (Hq' : q = 18 \/ q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/ q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27) by lia.
      repeat (destruct Hq' as [->|Hq']); try subst q; pl_g HS; rewrite E1o by lia; apply EE; reflexivity. }
Qed.
End W.

Print Assumptions plain_spec_holds.
