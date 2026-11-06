(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require ZArith NArith List Lia Bool Classical_Prop Sorting.Permutation.
From stdpp Require list.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Ubsan.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ZStores OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTail OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.U1Layout.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.LiveStats OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Facts.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsGrammar OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsNeeds.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablStmts.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.NumTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagVia OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagViaU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DRepU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagStmtsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.SbOverflowU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.XsputnU1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DFactsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DsRoom OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.PutU64U1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DsDtorU1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RunRandom.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module ExhLibU1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.Classical_Prop Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ZStores OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTail OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.U1Layout.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.LiveStats OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Facts.

Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsGrammar OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsNeeds.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.NumTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagVia OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagViaU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DRepU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DFactsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DsRoom OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagStmtsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.SbOverflowU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.XsputnU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.PutU64U1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DsDtorU1.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RunRandom.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module Ly := U1Layout.
Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition ro_byte (a : Z) : option Z :=
  match rdn SEGS (fun _ => None) (Z_to_bv 64 a) 1 with Some [b] => Some (bv_unsigned b) | _ => None end.
Definition zseq (lo n : Z) : list Z := map (fun i => lo + Z.of_nat i) (seq 0 (Z.to_nat n)).
Definition ro_cstr_chk (p n : Z) : bool :=
  (0x10008 <=? p) && (0 <=? n) && (p + n + 16 <=? 0xe8000) &&
  forallb (fun i => match ro_byte (p + i) with Some c => 0 <? c | None => false end) (zseq 0 n) &&
  (match ro_byte (p + n) with Some c => c =? 0 | None => false end) &&
  forallb (fun a => match ro_byte a with Some _ => true | None => false end)
          (zseq (p - p mod 8) (n + 1 + p mod 8 + (8 - (p + n + 1) mod 8) mod 8)).

Lemma in_zseq : forall lo n a, 0 <= n -> lo <= a < lo + n -> In a (zseq lo n).
Proof.
  intros lo n a Hn Ha. unfold zseq. apply in_map_iff. exists (Z.to_nat (a - lo)). split; [lia|]. apply in_seq. lia.
Qed.
Lemma ro_byte_range : forall a c, ro_byte a = Some c -> 0 <= c < 256.
Proof.
  intros a c. unfold ro_byte. destruct (rdn _ _ _ _) as [[|b [|]]|]; intros E; try discriminate E.
  injection E as <-. pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. cbn in Hb. lia.
Qed.
Lemma ro_rdn1 : forall M (a : Z) (k : nat), ro_clear Ly.L M -> 0x10000 <= a -> a + Z.of_nat k <= 0xe8000 ->
  rdn SEGS M (Z_to_bv 64 a) k = rdn SEGS (fun _ => None) (Z_to_bv 64 a) k.
Proof.
  intros M a k ROC H1 H2. symmetry. apply rdn_agree_win; [lia|lia|]. intros x Hx. unfold zwin in Hx.
  symmetry. apply ROC. rewrite u64_of_Z by lia. unfold ro_addr. cbn [ly_img ly_rw ly_relro Ly.L]. rewrite !in_ranges_1. lia.
Qed.
Lemma ro_byte_fld : forall M a c, ro_clear Ly.L M -> 0x10000 <= a -> a + 1 <= 0xe8000 -> ro_byte a = Some c -> fld SEGS M a 1 c.
Proof.
  intros M a c ROC H1 H2. unfold ro_byte, CRep.fld. rewrite (ro_rdn1 M a 1 ROC H1 ltac:(cbn; lia)).
  destruct (rdn _ _ _ _) as [[|b [|]]|]; intros E; try discriminate E. injection E as <-.
  rewrite N_to_le_bytes_1_small. do 2 f_equal. apply bv_eq. pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. cbn in Hb.
  rewrite (u64_of_Z (bv_unsigned b)) by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap. symmetry. apply Z.mod_small. exact (bv_unsigned_in_range 8 b).
Qed.
Lemma ro_cstr_of_chk : forall p n, ro_cstr_chk p n = true -> ro_cstr SEGS Ly.L p n.
Proof.
  intros p n H. unfold ro_cstr_chk in H. apply andb_prop in H. destruct H as [H H6]. apply andb_prop in H. destruct H as [H H5].
  apply andb_prop in H. destruct H as [H H4]. apply andb_prop in H. destruct H as [H H3]. apply andb_prop in H. destruct H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
  pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as Hm8. pose proof (Z.mod_pos_bound (p + n + 1) 8 ltac:(lia)) as Hm8'.
  pose proof (Z.mod_pos_bound (8 - (p + n + 1) mod 8) 8 ltac:(lia)) as Hm8''.
  split; [lia|]. split; [lia|]. split; [lia|]. intros M ROC. split; [|split].
  - intros i Hi. pose proof (proj1 (forallb_forall _ _) H4 i (in_zseq 0 n i ltac:(lia) ltac:(lia))) as Hc. cbn beta in Hc.
    destruct (ro_byte (p + i)) as [c|] eqn:E; [|discriminate Hc]. exists c. pose proof (ro_byte_range _ _ E). apply Z.ltb_lt in Hc.
    split; [lia|]. apply (ro_byte_fld M (p + i) c ROC); [lia|lia|exact E].
  - destruct (ro_byte (p + n)) as [c|] eqn:E; [|discriminate H5]. apply Z.eqb_eq in H5. subst c.
    apply (ro_byte_fld M (p + n) 0 ROC); [lia|lia|exact E].
  - intros a Ha. pose proof (proj1 (forallb_forall _ _) H6 a (in_zseq (p - p mod 8) (n + 1 + p mod 8 + (8 - (p + n + 1) mod 8) mod 8) a ltac:(lia) ltac:(lia))) as Hc. cbn beta in Hc.
    destruct (ro_byte a) as [c|] eqn:E; [|discriminate Hc]. exists c. pose proof (ro_byte_range _ _ E).
    split; [lia|]. apply (ro_byte_fld M a c ROC); [lia|lia|exact E].
Qed.

Lemma ro_11738 : ro_cstr SEGS Ly.L 0x11738 38. Proof. apply ro_cstr_of_chk. vm_compute. reflexivity. Qed.
Lemma ro_11599 : ro_cstr SEGS Ly.L 0x11599 18. Proof. apply ro_cstr_of_chk. vm_compute. reflexivity. Qed.
Lemma ro_13b59 : ro_cstr SEGS Ly.L 0x13af3 12. Proof. apply ro_cstr_of_chk. vm_compute. reflexivity. Qed.
Lemma ro_1414b : ro_cstr SEGS Ly.L 0x140e5 10. Proof. apply ro_cstr_of_chk. vm_compute. reflexivity. Qed.
Lemma ro_1064a : ro_cstr SEGS Ly.L 0x1064a 24. Proof. apply ro_cstr_of_chk. vm_compute. reflexivity. Qed.
Lemma ro_11098 : ro_cstr SEGS Ly.L 0x11098 1. Proof. apply ro_cstr_of_chk. vm_compute. reflexivity. Qed.
Lemma ro_1109c : ro_cstr SEGS Ly.L 0x1109c 7. Proof. apply ro_cstr_of_chk. vm_compute. reflexivity. Qed.

Section Algebra.
Context {AC : AllocCeiling}.
  Variable MI : MallocIface SEGS Ly.L.

  Definition blkpart (B : list (Z * Z)) (a : Z) : Prop := exists q k, In (q, k) B /\ q <= a < q + k.

  Lemma blk_xfer_nil_trans : forall B1 B2 lv lv1 lv2,
    blk_xfer [] B1 lv lv1 -> blk_xfer B1 B2 lv1 lv2 -> blk_xfer [] B2 lv lv2.
  Proof using.
    intros B1 B2 lv lv1 lv2 (_ & F1 & E1) (L2 & F2 & E2).
    assert (NB1 : forall x, In x lv -> ~ In x B1).
    { intros x Hx HB. exact (F1 x x HB Hx ltac:(intros []) eq_refl). }
    split; [intros b []|]. split.
    - intros b x Hb Hx _. apply (F2 b x Hb); [apply (proj2 (E1 x)); right; split; [exact Hx | intros []] | exact (NB1 x Hx)].
    - intros x. rewrite (E2 x). split.
      + intros [H|[H Hn]]; [left; exact H|]. apply (proj1 (E1 x)) in H. destruct H as [H|[H _]]; [exfalso; exact (Hn H)|]. right. split; [exact H | intros []].
      + intros [H|[H _]]; [left; exact H|]. right. split; [apply (proj2 (E1 x)); right; split; [exact H | intros []] | exact (NB1 x H)].
  Qed.

  Lemma blk_xfer_nil_in : forall B lv lv' x, blk_xfer [] B lv lv' -> In x lv -> In x lv'.
  Proof using. intros B lv lv' x (_ & _ & E) Hx. apply (proj2 (E x)). right. split; [exact Hx | intros []]. Qed.

  Lemma blk_xfer_nil_perm : forall A A' M M' model model',
    ainv MI A M model -> ainv MI A' M' model' -> blk_xfer [] [] (live MI A) (live MI A') ->
    Permutation (live MI A') (live MI A).
  Proof using AC MI.
    intros A A' M M' model model' AI AI' (_ & _ & E). apply live_equiv_perm.
    - exact (ai_live_nodup MI A' M' model' AI').
    - exact (ai_live_nodup MI A M model AI).
    - intros q k. rewrite (E (q, k)). split; [intros [[]|[H _]]; exact H | intros H; right; split; [exact H | intros []]].
  Qed.

  Lemma junk_ok_anti : forall A A' (J : Z -> Prop),
    (forall x, In x (live MI A) -> In x (live MI A')) -> junk_ok MI A' J -> junk_ok MI A J.
  Proof using AC MI.
    intros A A' J HL HJ a Ha. destruct (HJ a Ha) as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
    intros q k Hq. apply H3. apply HL. exact Hq.
  Qed.

  Lemma junk_ok_or : forall A (J1 J2 : Z -> Prop), junk_ok MI A J1 -> junk_ok MI A J2 -> junk_ok MI A (fun a => J1 a \/ J2 a).
  Proof using AC MI. intros A J1 J2 H1 H2 a [Ha|Ha]; [exact (H1 a Ha) | exact (H2 a Ha)]. Qed.

  Lemma junk_ok_false : forall A, junk_ok MI A (fun _ => False).
  Proof using AC MI. intros A a []. Qed.

  Lemma blkpart_junk : forall A A' M' model' B,
    ainv MI A' M' model' -> blk_xfer [] B (live MI A) (live MI A') ->
    (forall b, In b B -> In b (live MI A')) -> junk_ok MI A (blkpart B).
  Proof using AC MI.
    intros A A' M' model' B AI' XF BL a (q & k & Hin & Hqa).
    pose proof (ai_live_block MI A' M' model' q k AI' (BL _ Hin)) as (Hk & _ & Hq0 & Hqc & Hcell).
    destruct (Hcell a Hqa) as (_ & Hni & _).
    split; [lia|]. split; [exact Hni|].
    intros q' k' Hx Hov. pose proof XF as (_ & F & _).
    pose proof (F (q, k) (q', k') Hin Hx ltac:(intros [])) as Hne. cbn in Hne.
    pose proof (ai_live_block MI A' M' model' q' k' AI' (blk_xfer_nil_in _ _ _ _ XF Hx)) as (Hk' & _).
    destruct (ai_live_disjoint MI A' M' model' q k q' k' AI' (BL _ Hin) (blk_xfer_nil_in _ _ _ _ XF Hx) ltac:(lia)); lia.
  Qed.

  Lemma eff_drop_window : forall A A' M M' (W : Z * Z) (F F' : Z -> Prop),
    eff MI A A' M M' W F ->
    (forall a, F a -> F' a \/ (W_of W a /\ M' (Z_to_bv 64 a) <> None /\ ~ owned MI A' a)) ->
    eff MI A A' M M' W F'.
  Proof using AC MI.
    intros A A' M M' W F F' E HF. destruct E as [C Bc O FR D OI]. constructor.
    - exact C. - exact Bc.
    - intros a Ho. destruct (O a Ho) as [H|[H|H]]; [left; exact H | right; left; exact H |].
      destruct (HF a H) as [H'|(_ & _ & Hno)]; [right; right; exact H' | exfalso; exact (Hno Ho)].
    - intros a Hn. apply FR. intros [H|[H|[H|[H|[H|H]]]]]; apply Hn; try tauto.
      destruct (HF _ H) as [H'|(Hw & _)]; tauto.
    - intros a Ha Hd. destruct (D a Ha Hd) as [H|[H|[H|H]]]; [left; exact H | right; left; exact H | | right; right; right; exact H].
      destruct (HF a H) as [H'|(_ & Hd' & _)]; [right; right; left; exact H' | left; exact Hd'].
    - exact OI.
  Qed.

  #[local] Notation ds_room1 := (PrsNeeds.ds_room1 SEGS Ly.L MI).

  Lemma count_cons_ge : forall cls big b (l : list (Z * Z)) c, count_class_f cls big l c <= count_class_f cls big (b :: l) c.
  Proof using. intros cls big [q k] l c. cbn. destruct (_ : bool); lia. Qed.
  Lemma big_cons_ge : forall rb big b (l : list (Z * Z)),
    (forall n, 0 <= n -> 0 <= rb n) -> 0 <= snd b -> big_bytes_f rb big l <= big_bytes_f rb big (b :: l).
  Proof using. intros rb big [q k] l Hrb Hk. cbn. cbn in Hk. destruct (_ : bool); [pose proof (Hrb k Hk); lia | lia]. Qed.

  Lemma ds_room_of_room1 : forall A A' M M' model model' B (W : Z * Z) (F : Z -> Prop),
    ds_room1 A -> ainv MI A M model -> ainv MI A' M' model' ->
    blk_xfer [] B (live MI A) (live MI A') -> (forall b, In b B -> In b (live MI A')) ->
    Zlength B <= 1 -> (forall q k, In (q, k) B -> 0 < k <= DS_MAXBLK) ->
    eff MI A A' M M' W F ->
    ds_room SEGS Ly.L MI A'.
  Proof using AC MI.
    intros A A' M M' model model' B W F [HN R1] AI AI' XF BL HB1 HBsz EF. split; [exact HN|].
    intros n Hn. pose proof (ef_caps _ _ _ _ _ _ _ _ _ EF) as HC. pose proof (ef_bigcap _ _ _ _ _ _ _ _ _ EF) as HBC.
    pose proof (ai_live_nodup MI A M model AI) as ND. pose proof (ai_live_nodup MI A' M' model' AI') as ND'.
    pose proof XF as (_ & FR & E).
    destruct B as [|[q k] [|b2 B']]; [| | cbn in HB1; unfold Zlength in HB1; cbn in HB1; lia].
    -
      assert (EQC : forall c, count_class_f (size_class MI) (BIG MI) (live MI A') c = count_class_f (size_class MI) (BIG MI) (live MI A) c).
      { intros c. apply live_equiv_count; [exact ND' | exact ND |]. intros q k. rewrite (E (q, k)). cbn. tauto. }
      assert (EQB : big_bytes_f (round_big MI) (BIG MI) (live MI A') = big_bytes_f (round_big MI) (BIG MI) (live MI A)).
      { apply live_equiv_big; [exact ND' | exact ND |]. intros q k. rewrite (E (q, k)). cbn. tauto. }
      destruct (R1 0 1 n ltac:(unfold DS_MAXBLK; lia) Hn) as [RS RB]. split.
      + intros Hs. destruct (RS Hs) as [X1 X2]. rewrite HC, !EQC.
        pose proof (count_cons_ge (size_class MI) (BIG MI) (0, 1) (live MI A) (size_class MI n)).
        pose proof (count_cons_ge (size_class MI) (BIG MI) (0, 1) (live MI A) (size_class MI n + 1)). lia.
      + intros Hb. rewrite HBC, EQB. pose proof (RB Hb).
        pose proof (big_cons_ge (round_big MI) (BIG MI) (0, 1) (live MI A) (ai_round_big_nonneg MI) ltac:(cbn; lia)). lia.
    -
      pose proof (HBsz q k ltac:(left; reflexivity)) as Hk.
      assert (NDc : NoDup (map fst ((q, k) :: live MI A))).
      { cbn [map fst]. apply NoDup_cons_2; [|exact ND]. intros Hin. apply list_elem_of_In in Hin. apply in_map_iff in Hin.
        destruct Hin as ([q' k'] & Hq & Hin). cbn in Hq. exact (FR (q, k) (q', k') ltac:(left; reflexivity) Hin ltac:(intros []) Hq). }
      assert (EQV : forall q' k', In (q', k') (live MI A') <-> In (q', k') ((q, k) :: live MI A)).
      { intros q' k'. rewrite (E (q', k')). cbn. split; [intros [[H|[]]|[H _]]; [left; exact H | right; exact H] | intros [H|H]; [left; left; exact H | right; split; [exact H | intros []]]]. }
      assert (EQC : forall c, count_class_f (size_class MI) (BIG MI) (live MI A') c = count_class_f (size_class MI) (BIG MI) ((q, k) :: live MI A) c).
      { intros c. apply live_equiv_count; [exact ND' | exact NDc | exact EQV]. }
      assert (EQB : big_bytes_f (round_big MI) (BIG MI) (live MI A') = big_bytes_f (round_big MI) (BIG MI) ((q, k) :: live MI A)).
      { apply live_equiv_big; [exact ND' | exact NDc | exact EQV]. }
      destruct (R1 q k n Hk Hn) as [RS RB]. split.
      + intros Hs. rewrite HC, !EQC. exact (RS Hs).
      + intros Hb. rewrite HBC, EQB. exact (RB Hb).
  Qed.

End Algebra.

Section OpsS.
Context {AC : AllocCeiling}.
Context {RRND : RunRandom}.
  Variable MI : MallocIface SEGS Ly.L.
  Variable ST : StaticsIface SEGS Ly.L.
  Hypothesis DN : diag_needs MI ST.
  #[local] Notation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).

  Lemma put_u64_S : forall (fx : FPState) A (s : SX ST) R M model (sp ret S ds err len x : Z) (B : list (Z * Z)) (K : TSet),
    callB MI ST A s R M model sp ret S -> 1600 <= S /\ 336 + XS_STK MI <= S -> ro_clear Ly.L M ->
    getr R 10%bv = Z_to_bv 64 ds -> getr R 11%bv = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
    ds_rep MI A M ds err len B -> above_sp MI A sp ds DS_SIZE ->
    len + 24 <= DS_MAXLEN -> ds_room SEGS Ly.L MI A ->
    (forall A' R' M' model' B' (J : Z -> Prop),
        retB MI ST A' s R R' M' model model' -> getr R' 10%bv = Z_to_bv 64 ds ->
        ds_rep MI A' M' ds err (len + 24) B' -> blk_xfer B B' (live MI A) (live MI A') -> junk_ok MI A J ->
        eff MI A A' M M' (sp - S, sp) (fun a => ds_foot ds B a \/ ds_foot ds B' a \/ J a) ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R A_PUT_U64 M model) K.
  Proof using AC RRND MI ST DN.
    intros fx A s R M model sp ret S ds err len x B K CB HS ROC Ha0 Ha1 Hx (m0 & pp0 & hm0 & fl & fill & DI) ABOVE BUD ROOM POST.
    unfold DS_SIZE in ABOVE.
    exact (PutU64U1.put_main MI ST DN A s R M model sp ret S ds err len x B K m0 pp0 hm0 fl fill CB HS ROC Ha0 Ha1 Hx DI ABOVE BUD ROOM POST).
  Qed.

  Lemma ds_dtor_S : forall (fx : FPState) A (s : SX ST) R M model (sp ret S ds err len : Z) (B : list (Z * Z)) (K : TSet),
    callB MI ST A s R M model sp ret S -> 336 + MALLOC_STACK MI <= S -> ro_clear Ly.L M ->
    getr R 10%bv = Z_to_bv 64 ds ->
    ds_rep MI A M ds err len B -> above_sp MI A sp ds DS_SIZE ->
    (forall A' R' M' model',
        retB MI ST A' s R R' M' model model' ->
        blk_xfer B [] (live MI A) (live MI A') -> mdef M' ds DS_SIZE ->
        eff MI A A' M M' (sp - S, sp) (ds_foot ds B) ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R A_DS_DTOR M model) K.
  Proof using AC RRND MI ST DN.
    intros fx A s R M model sp ret S ds err len B K CB HS ROC Ha0 (m0 & pp0 & hm0 & fl & fill & DI) ABOVE CONT.
    unfold DS_SIZE in *.
    exact (DsDtorU1.dtor_main MI ST DN A s R M model sp ret ds err len B K m0 pp0 hm0 fl fill S CB HS ROC Ha0 DI ABOVE CONT).
  Qed.
End OpsS.
End ExhLibU1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagOpsSU1.

From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop Sorting.Permutation.
From stdpp Require list.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac StoreOk MemSplit Hoare ShapeAlg SRealizes MmapSim
  RefMemcpyLib LibIface LibEff LibMaskBits ZStores SymExec3 SymExec3Sound SymRun3 LibTail U1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib ContStmts LiveStats U1Facts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar PrsNeeds.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag Require Import DiagTac NumTac DiagVia DiagViaU1 DiagU1 DRepU1 DiagStmtsU1 SbOverflowU1 XsputnU1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.Exhausted1U1.ExhLibU1. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag Require Import DiagOpsSU1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import RunRandom.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module Ly := U1Layout.
Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition EXH_FRAME : Z := 448.
Definition EXH_S : Z := 11840.

Lemma seg_rom_high : forall (x : word), 0x124000 <= bv_unsigned x -> seg_rom SEGS x = None.
Proof.
  intros x Hx. unfold seg_rom, memory_read.
  unfold SEGS, Ubsan.M.loaded_segments, Ubsan.Ubsan_loaded_segments.
  cbn [find_segment seg_base seg_size Ubsan.Ubsan_segment_000 Ubsan.Ubsan_segment_001 Ubsan.Ubsan_segment_002 Ubsan.Ubsan_segment_003].
  repeat (match goal with |- context [if ?c then _ else _] =>
            replace c with false by (symmetry; apply Bool.andb_false_iff; right; apply Z.leb_gt; cbn; lia) end).
  reflexivity.
Qed.
Lemma rdn_defined_high : forall M n a bs, rdn SEGS M (Z_to_bv 64 a) n = Some bs -> 0x124000 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  defined M a (Z.of_nat n).
Proof.
  intros M n. induction n as [|n IH]; intros a bs Hr Ha Han i Hi; [lia|].
  cbn [rdn] in Hr. destruct (M (Z_to_bv 64 a)) as [b|] eqn:HM.
  - destruct (Z.eq_dec i 0) as [->|Hnz]; [rewrite Z.add_0_r, HM; discriminate|].
    destruct (rdn SEGS M (Z_to_bv 64 a + 1) n) as [rest|] eqn:Hr'; [|discriminate Hr].
    rewrite SymExec3Sound.SX2S.w_add_1, u64_of_Z in Hr' by lia.
    replace (a + i) with ((a + 1) + (i - 1)) by lia. apply (IH (a + 1) rest Hr'); lia.
  - rewrite seg_rom_high in Hr; [discriminate Hr | rewrite u64_of_Z by lia; lia].
Qed.
Lemma fld_defined_high : forall M a (k : nat) v, fld SEGS M a k v -> 0x124000 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
  forall i, 0 <= i < Z.of_nat k -> M (Z_to_bv 64 (a + i)) <> None.
Proof. intros M a k v HF Ha Hk. exact (rdn_defined_high M k a _ HF Ha Hk). Qed.

Section Exh.
Context {AC : AllocCeiling}.
Context {RRND : RunRandom}.
  Variable MI : MallocIface SEGS Ly.L.
  Variable ST : StaticsIface SEGS Ly.L.
  Hypothesis DN : diag_needs MI ST.
  Hypothesis PCS : put_cstrS_stmt MI ST.

  #[local] Notation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
  Let MSP : 0 <= MALLOC_STACK MI <= 8192. Proof. exact (dn_mstack MI ST DN). Qed.
  Let DL : ds_rep_laws SEGS Ly.L MI ST dcU1 (ds_rep MI). Proof. exact (diag_laws MI ST). Qed.

  Section Call.
    Context {fx : FPState}.
    Variables (A : AS MI) (s : LibIface.SX ST) (R : bvmap 5 word) (M : mem) (model : Model).
    Variables (sp ret this pcons nwords widx icount inst_offset opcode type : Z) (K : TSet).
    Hypothesis CB : callB MI ST A s R M model sp ret 12288.
    Hypothesis ROC : ro_clear Ly.L M.
    Hypothesis PL : placed MI A this 288.
    Hypothesis Hthis : this + 288 <= 2 ^ 47.
    Hypothesis THW : forall a, zwin this (this + 288) a -> ~ zwin (sp - 12288) sp a.
    Hypothesis F56 : fld SEGS M (this + 56) 8 nwords.
    Hypothesis F72 : fld SEGS M (this + 72) 8 widx.
    Hypothesis Hnw : 0 <= nwords < 2 ^ 63.
    Hypothesis Hwi : 0 <= widx < 2 ^ 63.
    Hypothesis ROOM1 : ds_room1 SEGS Ly.L MI A.
    Hypothesis POST : forall A' R' M' model' (J : Z -> Prop),
        retB MI ST A' s R R' M' model model' ->
        getr R' 10%bv = Z_to_bv 64 (2 ^ 64 - 4) ->
        Permutation (live MI A') (live MI A) ->
        junk_ok MI A J ->
        eff MI A A' M M' (sp - 12288, sp) (fun a => J a) ->
        srealizes SEGS (cfg fx R' ret M' model') K.

    #[local] Notation sp' := (sp - 448).

    Record xinv (A1 : AS MI) (M1 : mem) (model1 : Model) (len : Z) (B1 : list (Z * Z)) (JJ : Z -> Prop) : Prop := XINV {
      xi_ai : ainv MI A1 M1 model1;
      xi_ms : mstd model1;
      xi_fs : m_fs model1 = m_fs model;
      xi_fds : m_fds model1 = m_fds model;
      xi_sx : sx_inv ST s M1;
      xi_ds : ds_rep MI A1 M1 sp' (-4) len B1;
      xi_xfer : blk_xfer [] B1 (live MI A) (live MI A1);
      xi_jj : junk_ok MI A JJ;
      xi_eff : eff MI A A1 M M1 (sp - 12288, sp) (fun a => ds_foot sp' B1 a \/ JJ a);
      xi_fr : slots SEGS M1 sp [Z_to_bv 64 ret; getr R 8%bv; getr R 9%bv; getr R 18%bv; getr R 19%bv];
      xi_frdef : mdef M1 (sp - 56) 56;
      xi_stk : mdef M1 (sp - 12288) EXH_S }.

    Definition xregs (R1 : bvmap 5 word) (s0 s2 s3 : Z) : Prop :=
      getr R1 2%bv = Z_to_bv 64 sp' /\ getr R1 3%bv = getr R 3%bv /\ getr R1 4%bv = getr R 4%bv /\
      getr R1 8%bv = Z_to_bv 64 s0 /\ getr R1 9%bv = Z_to_bv 64 this /\
      getr R1 18%bv = Z_to_bv 64 s2 /\ getr R1 19%bv = Z_to_bv 64 s3 /\
      (forall r, In r [20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr R1 r = getr R r).

    Lemma xregs_kept : forall R1 R2 s0 s2 s3, xregs R1 s0 s2 s3 -> kept R1 R2 -> xregs R2 s0 s2 s3.
    Proof using AC RRND MI ST DN R sp this nwords widx Hnw Hwi.
      intros R1 R2 s0 s2 s3 (X2 & X3 & X4 & X8 & X9 & X18 & X19 & XCS) KP. unfold xregs.
      rewrite !(KP 2%bv), !(KP 3%bv), !(KP 4%bv), !(KP 8%bv), !(KP 9%bv), !(KP 18%bv), !(KP 19%bv) by inl.
      repeat split; try assumption. intros r Hr. rewrite (KP r) by (cbn in Hr |- *; tauto). exact (XCS r Hr).
    Qed.

    Lemma ctx : alloc_ceiling + 12288 <= sp /\ sp < 2 ^ 47 /\ sp mod 16 = 0 /\ 0 <= ret < 2 ^ 64 /\
                getr R 2%bv = Z_to_bv 64 sp /\ getr R 1%bv = Z_to_bv 64 ret /\ ret_ok (Z_to_bv 64 ret) /\
                getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) /\ getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L).
    Proof using AC MI ST A s R M model sp ret CB.
      clear Hnw Hwi Hthis. destruct CB as [AI MS ROC' SXI SXH [Hra Hret Hretr Hsp Hsp16 Hsphi Hgp Htp] Hceil HROOM Hwin Hown_sx Herr_sx].
      repeat split; try assumption; lia.
    Qed.

    Lemma xinv_foot : forall A1 M1 model1 len B1 JJ a,
      xinv A1 M1 model1 len B1 JJ -> ds_foot sp' B1 a \/ JJ a -> a < alloc_ceiling \/ (sp' <= a < sp' + 392).
    Proof using AC MI ST A s R M model sp ret.
      intros A1 M1 model1 len B1 JJ a X [Hf|Hj].
      - unfold ds_foot, DS_SIZE in Hf. destruct Hf as [Hz|(q & k & Hin & Hqa)]; [right; unfold zwin in Hz; lia|].
        destruct (dl_blocks _ _ _ _ _ _ DL _ _ _ _ _ _ (xi_ds _ _ _ _ _ _ X)) as [_ HB].
        destruct (HB q k Hin) as [HL Hk]. pose proof (ai_live_block MI A1 M1 model1 q k (xi_ai _ _ _ _ _ _ X) HL) as (_ & _ & _ & Hc & _). left; lia.
      - destruct (xi_jj _ _ _ _ _ _ X a Hj) as (H & _). left; lia.
    Qed.

    Lemma xinv_foot_offimg : forall A1 M1 model1 len B1 JJ a,
      xinv A1 M1 model1 len B1 JJ -> ds_foot sp' B1 a \/ JJ a -> ~ in_ranges (ly_img Ly.L) a.
    Proof using AC MI ST A s R M model sp ret CB.
      intros A1 M1 model1 len B1 JJ a X [Hf|Hj].
      - unfold ds_foot, DS_SIZE in Hf. pose proof ctx as (Hceil & _). pose proof ac_bounds_lit.
        destruct Hf as [Hz|(q & k & Hin & Hqa)]; [apply hi_offimg; unfold zwin in Hz; lia|].
        destruct (dl_blocks _ _ _ _ _ _ DL _ _ _ _ _ _ (xi_ds _ _ _ _ _ _ X)) as [_ HB].
        destruct (HB q k Hin) as [HL Hk]. pose proof (ai_live_block MI A1 M1 model1 q k (xi_ai _ _ _ _ _ _ X) HL) as (_ & _ & _ & _ & Hc).
        exact (proj1 (proj2 (Hc a Hqa))).
      - exact (proj1 (proj2 (xi_jj _ _ _ _ _ _ X a Hj))).
    Qed.

    Lemma xinv_roc : forall A1 M1 model1 len B1 JJ, xinv A1 M1 model1 len B1 JJ -> ro_clear Ly.L M1.
    Proof using AC MI ST A s R M model sp ret CB ROC.
      intros A1 M1 model1 len B1 JJ X. pose proof ctx as (Hceil & _). pose proof ac_bounds_lit.
      destruct CB as [AI _ _ _ _ _ _ _ _ _ _].
      eapply (ro_clear_via_eff MI A A1 M M1 model); [exact ROC | exact AI | exact (xi_eff _ _ _ _ _ _ X) | | cbn; lia].
      intros a Ha. exact (xinv_foot_offimg _ _ _ _ _ _ a X Ha).
    Qed.

    Lemma xinv_callB : forall A1 M1 model1 len B1 JJ R1 (retk : Z),
      xinv A1 M1 model1 len B1 JJ ->
      getr R1 1%bv = Z_to_bv 64 retk -> ret_ok (Z_to_bv 64 retk) -> 0 <= retk < 2 ^ 64 ->
      getr R1 2%bv = Z_to_bv 64 sp' -> getr R1 3%bv = getr R 3%bv -> getr R1 4%bv = getr R 4%bv ->
      callB MI ST A1 s R1 M1 model1 sp' retk EXH_S.
    Proof using AC MI ST A s R M model sp ret nwords widx CB ROC Hnw Hwi.
      intros A1 M1 model1 len B1 JJ R1 retk X Y1 Yok Yr Y2 Y3 Y4.
      pose proof ctx as (Hceil & Hsphi & Hsp16 & Hretr & Hsp & Hra & Hret & Hgp & Htp). pose proof ac_bounds_lit as Hcv.
      pose proof CB as CB0. destruct CB0 as [AI MS ROC' SXI SXH _ _ HROOM Hwin Hown_sx Herr_sx].
      pose proof (xinv_roc _ _ _ _ _ _ X) as ROC1. destruct X. unfold EXH_S in *.
      constructor.
      - exact xi_ai0. - exact xi_ms0. - exact (img_ro_clear_of' ST s M1 ROC1 xi_sx0). - exact xi_sx0. - exact SXH.
      - constructor; [exact Y1 | exact Yok | exact Yr | exact Y2 | mlia | lia | rewrite Y3; exact Hgp | rewrite Y4; exact Htp].
      - lia.
      - unfold stack_room. replace (Z_to_bv 64 (sp' - 11840)) with (Z_to_bv 64 (sp - 12288 + 0)) by (f_equal; lia).
        apply (mdef_store_ok_off SEGS M1 (sp - 12288) 11840); [exact xi_stk0 | lia | lia | lia | lia].
      - intros a Ha. split; [apply (hi_unowned MI A1 M1 model1); [exact xi_ai0 | unfold zwin in Ha; lia] | apply (proj2 (Hwin a ltac:(unfold zwin in *; lia)))].
      - exact (own_sx_via_eff MI ST _ _ _ _ _ _ xi_eff0 Hown_sx).
      - exact Herr_sx.
    Qed.

    Lemma xinv_above : forall A1 M1 model1 len B1 JJ, xinv A1 M1 model1 len B1 JJ -> above_sp MI A1 sp' sp' DS_SIZE.
    Proof using AC MI ST A s R M model sp ret CB.
      intros A1 M1 model1 len B1 JJ X. pose proof ctx as (Hceil & Hsphi & _). pose proof ac_bounds_lit. unfold DS_SIZE.
      split; [lia|]. split; [lia|]. intros i Hi. apply (hi_unowned MI A1 M1 model1); [exact (xi_ai _ _ _ _ _ _ X) | lia].
    Qed.

    Lemma xinv_room : forall A1 M1 model1 len B1 JJ, xinv A1 M1 model1 len B1 JJ -> ds_room SEGS Ly.L MI A1.
    Proof using AC MI ST A s R M model sp ret CB ROOM1.
      intros A1 M1 model1 len B1 JJ X. destruct CB as [AI _ _ _ _ _ _ _ _ _ _].
      destruct (dl_blocks _ _ _ _ _ _ DL _ _ _ _ _ _ (xi_ds _ _ _ _ _ _ X)) as [HB1 HB].
      eapply (ds_room_of_room1 MI A A1 M M1 model model1 B1); [exact ROOM1 | exact AI | exact (xi_ai _ _ _ _ _ _ X) | exact (xi_xfer _ _ _ _ _ _ X) | | exact HB1 | | exact (xi_eff _ _ _ _ _ _ X)].
      - intros [q k] Hb. exact (proj1 (HB q k Hb)).
      - intros q k Hb. exact (proj2 (HB q k Hb)).
    Qed.

    Lemma xinv_len : forall A1 M1 model1 len B1 JJ, xinv A1 M1 model1 len B1 JJ -> 0 <= len.
    Proof using AC MI ST A s R M model sp ret. intros A1 M1 model1 len B1 JJ X. exact (proj2 (proj2 (proj2 (dl_def _ _ _ _ _ _ DL _ _ _ _ _ _ (xi_ds _ _ _ _ _ _ X))))). Qed.

    Lemma xinv_this : forall A1 M1 model1 len B1 JJ, xinv A1 M1 model1 len B1 JJ ->
      fld SEGS M1 (this + 56) 8 nwords /\ fld SEGS M1 (this + 72) 8 widx.
    Proof using AC MI ST A s R M model sp ret this nwords widx CB PL Hthis THW F56 F72.
      intros A1 M1 model1 len B1 JJ X. pose proof ctx as (Hceil & Hsphi & _). pose proof ac_bounds_lit as Hcv.
      destruct CB as [AI _ _ _ _ _ _ _ _ _ _]. pose proof (xi_ai _ _ _ _ _ _ X) as AI1.
      destruct (dl_blocks _ _ _ _ _ _ DL _ _ _ _ _ _ (xi_ds _ _ _ _ _ _ X)) as [_ HB].
      assert (AG : agree_on (fun a => this + 56 <= a < this + 64 \/ this + 72 <= a < this + 80) M M1).
      { eapply (agree_via_eff MI A A1 M M1); [exact (xi_eff _ _ _ _ _ _ X)|]. intros a Ha.
        assert (Hdef : M (Z_to_bv 64 a) <> None \/ exists q k, In (q, k) (live MI A) /\ q <= a < q + k).
        { destruct PL as [Hhi | (q & k & Hin & Hq & Hqk)]; [left | right; exists q, k; split; [exact Hin | lia]].
          destruct Ha as [Ha|Ha].
          - replace a with (this + 56 + (a - (this + 56))) by lia. apply (fld_defined_high M (this + 56) 8 nwords F56); cbn; lia.
          - replace a with (this + 72 + (a - (this + 72))) by lia. apply (fld_defined_high M (this + 72) 8 widx F72); cbn; lia. }
        assert (NW : ~ W_of (sp - 12288, sp) a) by (unfold W_of; cbn; intros Hw; apply (THW a ltac:(unfold zwin; lia)); unfold zwin; lia).
        assert (NF : ~ (ds_foot sp' B1 a \/ JJ a)).
        { intros HF. destruct HF as [Hf | Hj].
          - unfold ds_foot, DS_SIZE in Hf. destruct Hf as [Hz | (q & k & Hin & Hqa)]; [apply (THW a ltac:(unfold zwin in *; lia)); unfold zwin in *; lia|].
            destruct (HB q k Hin) as [HL Hk]. pose proof (ai_live_block MI A1 M1 model1 q k AI1 HL) as (_ & _ & _ & Hqc & _).
            destruct PL as [Hhi | (q' & k' & Hin' & Hq' & Hqk')]; [lia|].
            pose proof (proj1 (proj2 (xi_xfer _ _ _ _ _ _ X)) (q, k) (q', k') Hin Hin' ltac:(intros [])) as Hne. cbn in Hne.
            pose proof (blk_xfer_nil_in _ _ _ _ (xi_xfer _ _ _ _ _ _ X) Hin') as HL'.
            pose proof (ai_live_block MI A1 M1 model1 q' k' AI1 HL') as (Hk' & _).
            destruct (ai_live_disjoint MI A1 M1 model1 q k q' k' AI1 HL HL' ltac:(lia)); lia.
          - destruct (xi_jj _ _ _ _ _ _ X a Hj) as (Hlo & _ & Hdis).
            destruct PL as [Hhi | (q' & k' & Hin' & Hq' & Hqk')]; [lia|]. exact (Hdis q' k' Hin' ltac:(lia)). }
        destruct PL as [Hhi | (q & k & Hin & Hq & Hqk)].
        - split; [lia|]. split; [apply (hi_unowned MI A M model); [exact AI | lia]|]. split; [apply (hi_unowned MI A1 M1 model1); [exact AI1 | lia]|].
          split; [destruct Hdef as [Hd|(q & k & Hin & Hqa)]; [exact Hd | exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (ai_live_block MI A M model q k AI Hin)))) a Hqa)))]|].
          split; [exact NF|]. split; [exact NW|]. apply hi_not_errno. lia.
        - pose proof (ai_live_block MI A M model q k AI Hin) as (_ & _ & Hq0 & Hqc & HC).
          pose proof (ai_live_block MI A1 M1 model1 q k AI1 (blk_xfer_nil_in _ _ _ _ (xi_xfer _ _ _ _ _ _ X) Hin)) as (_ & _ & _ & _ & HC1).
          destruct (HC a ltac:(lia)) as (Ho & Hni & Hd). destruct (HC1 a ltac:(lia)) as (Ho1 & _ & _).
          split; [lia|]. split; [exact Ho|]. split; [exact Ho1|]. split; [exact Hd|]. split; [exact NF|]. split; [exact NW|].
          intros He. exact (Hni (HErw _ _ He)). }
      assert (Hth0 : 0 <= this).
      { destruct PL as [H|(q & k & Hin & Hq & _)]; [lia | pose proof (ai_live_block MI A M model q k AI Hin); lia]. }
      split.
      - apply (fld_agree SEGS M M1 (this + 56) 8 nwords); [lia | cbn; lia | exact F56 | eapply agree_on_weaken; [exact AG | intros a Ha; cbn beta; unfold zwin in Ha; cbn in Ha; lia]].
      - apply (fld_agree SEGS M M1 (this + 72) 8 widx); [lia | cbn; lia | exact F72 | eapply agree_on_weaken; [exact AG | intros a Ha; cbn beta; unfold zwin in Ha; cbn in Ha; lia]].
    Qed.

    Lemma xinv_step : forall A1 M1 model1 len B1 JJ A2 M2 model2 len2 B2 (Jop : Z -> Prop),
      xinv A1 M1 model1 len B1 JJ ->
      ainv MI A2 M2 model2 -> mstd model2 -> m_fs model2 = m_fs model1 -> m_fds model2 = m_fds model1 -> sx_inv ST s M2 ->
      ds_rep MI A2 M2 sp' (-4) len2 B2 -> blk_xfer B1 B2 (live MI A1) (live MI A2) -> junk_ok MI A1 Jop ->
      eff MI A1 A2 M1 M2 (sp' - EXH_S, sp') (fun a => ds_foot sp' B1 a \/ ds_foot sp' B2 a \/ Jop a) ->
      xinv A2 M2 model2 len2 B2 (fun a => JJ a \/ Jop a \/ blkpart B1 a).
    Proof using AC RRND MI ST DN A s R M model sp ret nwords widx CB Hnw Hwi.
      intros A1 M1 model1 len B1 JJ A2 M2 model2 len2 B2 Jop X AI2 MS2 FS2 FDS2 SX2 DS2 XF JK EFF.
      pose proof ctx as (Hceil & Hsphi & _). pose proof ac_bounds_lit as Hcv. unfold EXH_S in EFF.
      pose proof X as [AI1 MS1 FS1 FDS1 SX1 DS1 XF1 JJ1 EFF1 FR1 FRD1 STK1].
      destruct (dl_blocks _ _ _ _ _ _ DL _ _ _ _ _ _ DS1) as [_ HB1]. destruct (dl_blocks _ _ _ _ _ _ DL _ _ _ _ _ _ DS2) as [_ HB2].
      assert (LOW : forall a, ds_foot sp' B1 a \/ ds_foot sp' B2 a \/ Jop a -> a < alloc_ceiling \/ (sp' <= a < sp' + 392)).
      { intros a [Hf|[Hf|Hj]].
        - exact (xinv_foot _ _ _ _ _ _ a X (or_introl Hf)).
        - unfold ds_foot, DS_SIZE in Hf. destruct Hf as [Hz|(q & k & Hin & Hqa)]; [right; unfold zwin in Hz; lia|].
          destruct (HB2 q k Hin) as [HL Hk]. pose proof (ai_live_block MI A2 M2 model2 q k AI2 HL) as (_ & _ & _ & Hc & _). left; lia.
        - destruct (JK a Hj) as (H & _). left; lia. }
      constructor.
      - exact AI2. - exact MS2. - rewrite FS2; exact FS1. - rewrite FDS2; exact FDS1. - exact SX2. - exact DS2.
      - exact (blk_xfer_nil_trans _ _ _ _ _ XF1 XF).
      - apply junk_ok_or; [exact JJ1|]. apply junk_ok_or.
        + eapply junk_ok_anti; [| exact JK]. intros x Hx. exact (blk_xfer_nil_in _ _ _ _ XF1 Hx).
        + eapply (blkpart_junk MI A A1 M1 model1 B1); [exact AI1 | exact XF1 | intros [q k] Hb; exact (proj1 (HB1 q k Hb))].
      - pose proof (eff_widen MI A1 A2 M1 M2 _ (sp - 12288, sp) _ EFF ltac:(cbn; lia) ltac:(cbn; lia)) as E12.
        assert (WUN : forall a, W_of (sp - 12288, sp) a -> ~ owned MI A2 a).
        { intros a Ha. unfold W_of in Ha. cbn in Ha. apply (hi_unowned MI A2 M2 model2); [exact AI2 | lia]. }
        pose proof (eff_trans _ _ _ _ _ _ _ _ _ _ EFF1 E12 WUN) as E02. cbn beta in E02.
        eapply eff_weaken; [exact E02|]. intros a Ha. unfold blkpart.
        destruct Ha as [[Hf|Hj]|[Hf|[Hf|Hj]]]; try tauto.
        + unfold ds_foot in Hf |- *. destruct Hf as [Hz|Hb]; [left; left; exact Hz | right; right; right; exact Hb].
        + unfold ds_foot in Hf |- *. destruct Hf as [Hz|Hb]; [left; left; exact Hz | right; right; right; exact Hb].
      - eapply slots_agree; [exact FR1 | cbn; lia | lia | cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul]].
        eapply agree_on_weaken; [eapply (agree_hi_via_eff MI A1 A2 M1 M2 model1 model2 _ _ (sp - 56) sp); [exact EFF | exact AI1 | exact AI2 | lia | lia | replace (sp - (sp - 56)) with 56 by lia; exact FRD1 | intros a Ha HF; destruct (LOW a HF); lia | cbn; lia] |].
        intros a Ha. unfold zwin in *. lia.
      - eapply (mdef_via_eff MI A1 A2 M1 M2); [exact EFF | left; lia | lia | lia | intros j Hj; apply (hi_unowned MI A1 M1 model1); [exact AI1 | lia] | intros j Hj HF; destruct (LOW _ HF); lia | exact FRD1].
      - unfold EXH_S in *. eapply (mdef_via_eff MI A1 A2 M1 M2); [exact EFF | left; lia | lia | lia | intros j Hj; apply (hi_unowned MI A1 M1 model1); [exact AI1 | lia] | intros j Hj HF; destruct (LOW _ HF); lia | exact STK1].
    Qed.

    Lemma xinv_stores : forall A1 M1 model1 len B1 JJ M2 lo,
      xinv A1 M1 model1 len B1 JJ -> stores_in (zwin lo sp') M1 M2 -> sp - 12288 <= lo ->
      xinv A1 M2 model1 len B1 JJ.
    Proof using AC MI ST A s R M model sp ret CB.
      intros A1 M1 model1 len B1 JJ M2 lo X STW Hlo.
      pose proof ctx as (Hceil & Hsphi & _). pose proof ac_bounds_lit as Hcv.
      pose proof CB as CB0. destruct CB0 as [AI _ _ _ _ _ _ _ Hwin _ _].
      pose proof X as [AI1 MS1 FS1 FDS1 SX1 DS1 XF1 JJ1 EFF1 FR1 FRD1 STK1].
      destruct (dl_blocks _ _ _ _ _ _ DL _ _ _ _ _ _ DS1) as [_ HB1].
      assert (WNO : forall a, zwin lo sp' a -> ~ owned MI A1 a /\ ~ in_ranges (ly_img Ly.L) a /\ ~ sx_region ST a).
      { intros a Ha. unfold zwin in Ha. split; [apply (hi_unowned MI A1 M1 model1); [exact AI1 | lia]|].
        split; [apply hi_offimg; lia | apply (proj2 (Hwin a ltac:(unfold zwin; lia)))]. }
      constructor.
      - eapply stores_in_ainv; [exact AI1 | exact STW | intros a Ha; exact (proj1 (WNO a Ha))].
      - exact MS1. - exact FS1. - exact FDS1.
      - eapply stores_in_sx; [exact SX1 | exact STW |]. intros a Ha. pose proof (WNO a Ha) as (_ & Hni & Hns).
        split; [exact Hns | intros Hr; apply Hni; apply ly_relro_img; exact Hr].
      - eapply (dl_frame _ _ _ _ _ _ DL A1 A1 M1 M2); [exact DS1 | | intros blk Hb; destruct blk as [q k]; exact (proj1 (HB1 q k Hb))].
        eapply stores_in_agree; [exact STW|]. intros a Ha. unfold DS_SIZE, zwin in *.
        destruct Ha as [Hz | (q & k & Hin & Hqa)]; [lia|].
        destruct (HB1 q k Hin) as [HL Hk]. pose proof (ai_live_block MI A1 M1 model1 q k AI1 HL) as (_ & _ & Hq0 & Hc & _). lia.
      - exact XF1. - exact JJ1.
      - assert (E12 : eff MI A1 A1 M1 M2 (sp - 12288, sp) (fun _ => False)).
        { eapply (eff_of_stores MI); [exact STW|]. intros a Ha. right. unfold W_of, zwin in *. cbn. lia. }
        assert (WUN : forall a, W_of (sp - 12288, sp) a -> ~ owned MI A1 a).
        { intros a Ha. unfold W_of in Ha. cbn in Ha. apply (hi_unowned MI A1 M1 model1); [exact AI1 | lia]. }
        pose proof (eff_trans _ _ _ _ _ _ _ _ _ _ EFF1 E12 WUN) as E02. cbn beta in E02.
        eapply eff_weaken; [exact E02|]. intros a Ha. cbn beta in Ha. destruct Ha as [Ha|Ha]; [exact Ha | destruct Ha].
      - eapply slots_agree; [exact FR1 | cbn; lia | lia | cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul]].
        eapply stores_in_agree; [exact STW|]. intros a Ha. unfold zwin in *. lia.
      - eapply stores_in_mdef; [exact STW | exact FRD1].
      - eapply stores_in_mdef; [exact STW | exact STK1].
    Qed.

    Lemma stage_cstr : forall A1 M1 model1 len B1 JJ R1 (s0 s2 s3 p n retk : Z),
      xinv A1 M1 model1 len B1 JJ -> xregs R1 s0 s2 s3 ->
      getr R1 1%bv = Z_to_bv 64 retk -> ret_ok (Z_to_bv 64 retk) -> 0 <= retk < 2 ^ 64 ->
      getr R1 10%bv = Z_to_bv 64 sp' -> getr R1 11%bv = Z_to_bv 64 p -> getr R1 12%bv = Z_to_bv 64 n ->
      ro_cstr SEGS Ly.L p n -> len + n <= DS_MAXLEN ->
      (forall A2 M2 model2 B2 JJ2 R2,
          xinv A2 M2 model2 (len + n) B2 JJ2 -> xregs R2 s0 s2 s3 -> getr R2 10%bv = Z_to_bv 64 sp' ->
          srealizes SEGS (cfg fx R2 retk M2 model2) K) ->
      srealizes SEGS (cfg fx R1 A_PUT_CSTR M1 model1) K.
    Proof using AC RRND MI ST DN PCS fx A s R M model sp ret this nwords widx K CB ROC Hnw Hwi ROOM1.
      intros A1 M1 model1 len B1 JJ R1 s0 s2 s3 p n retk X XR Y1 Yok Yr Y10 Y11 Y12 ROS BUD NEXT.
      pose proof XR as (X2 & X3 & X4 & _). pose proof ROS as (_ & Hn0 & _).
      eapply (PCS fx A1 s R1 M1 model1 sp' retk EXH_S sp' (-4) len p n n B1 K).
      - exact (xinv_callB _ _ _ _ _ _ R1 retk X Y1 Yok Yr X2 X3 X4).
      - unfold EXH_S, XS_STK, OVF_STK, NEW_STACK. lia.
      - exact (xinv_roc _ _ _ _ _ _ X).
      - exact Y10. - exact Y11. - exact Y12.
      - exact (xi_ds _ _ _ _ _ _ X).
      - exact (xinv_above _ _ _ _ _ _ X).
      - exact ROS. - lia. - exact BUD.
      - exact (xinv_room _ _ _ _ _ _ X).
      - intros A2 R2 M2 model2 B2 Jop RB Z10 DS2 XF JK EFF. destruct RB as [AI2 MS2 FS2 FDS2 SX2 KP].
        apply (NEXT A2 M2 model2 B2 (fun a => JJ a \/ Jop a \/ blkpart B1 a) R2).
        + eapply xinv_step; [exact X | exact AI2 | exact MS2 | exact FS2 | exact FDS2 | exact SX2 | exact DS2 | exact XF | exact JK | exact EFF].
        + exact (xregs_kept _ _ _ _ _ XR KP).
        + exact Z10.
    Qed.

    Lemma stage_u64 : forall A1 M1 model1 len B1 JJ R1 (s0 s2 s3 x retk : Z),
      xinv A1 M1 model1 len B1 JJ -> xregs R1 s0 s2 s3 ->
      getr R1 1%bv = Z_to_bv 64 retk -> ret_ok (Z_to_bv 64 retk) -> 0 <= retk < 2 ^ 64 ->
      getr R1 10%bv = Z_to_bv 64 sp' -> getr R1 11%bv = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
      len + 24 <= DS_MAXLEN ->
      (forall A2 M2 model2 B2 JJ2 R2,
          xinv A2 M2 model2 (len + 24) B2 JJ2 -> xregs R2 s0 s2 s3 -> getr R2 10%bv = Z_to_bv 64 sp' ->
          srealizes SEGS (cfg fx R2 retk M2 model2) K) ->
      srealizes SEGS (cfg fx R1 A_PUT_U64 M1 model1) K.
    Proof using AC RRND MI ST DN fx A s R M model sp ret this nwords widx K CB ROC Hnw Hwi ROOM1.
      intros A1 M1 model1 len B1 JJ R1 s0 s2 s3 x retk X XR Y1 Yok Yr Y10 Y11 Hx BUD NEXT.
      pose proof XR as (X2 & X3 & X4 & _).
      eapply (put_u64_S MI ST DN fx A1 s R1 M1 model1 sp' retk EXH_S sp' (-4) len x B1 K).
      - exact (xinv_callB _ _ _ _ _ _ R1 retk X Y1 Yok Yr X2 X3 X4).
      - unfold EXH_S, XS_STK, OVF_STK, NEW_STACK. lia.
      - exact (xinv_roc _ _ _ _ _ _ X).
      - exact Y10. - exact Y11. - exact Hx.
      - exact (xi_ds _ _ _ _ _ _ X).
      - exact (xinv_above _ _ _ _ _ _ X).
      - exact BUD.
      - exact (xinv_room _ _ _ _ _ _ X).
      - intros A2 R2 M2 model2 B2 Jop RB Z10 DS2 XF JK EFF. destruct RB as [AI2 MS2 FS2 FDS2 SX2 KP].
        apply (NEXT A2 M2 model2 B2 (fun a => JJ a \/ Jop a \/ blkpart B1 a) R2).
        + eapply xinv_step; [exact X | exact AI2 | exact MS2 | exact FS2 | exact FDS2 | exact SX2 | exact DS2 | exact XF | exact JK | exact EFF].
        + exact (xregs_kept _ _ _ _ _ XR KP).
        + exact Z10.
    Qed.
  End Call.
End Exh.
