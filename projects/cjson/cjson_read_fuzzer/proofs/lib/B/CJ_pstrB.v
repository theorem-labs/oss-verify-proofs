(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_skipws.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_skipws.CJ_band2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_skipws.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_skipws.CJ_band.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs CJ_iface AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.SO_shadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_tree CJ_conv ICPT_iface ICPT_musl ICPT_pcdefs ICPT_fmt_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_fmt_glue.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_fmt_glue.ICPT_fmt_iface2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_parse_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_pvalue_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_fuzz_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_fuzz_iface.CJ_print_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.CJ_print_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.CJ_print_lemmas2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_fmt_glue CJ_pstrA.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pstrA.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pstrA.CJ_shfast.
Local Ltac sh_resolve_if ::= sh_resolve_if_fast.
Local Ltac sh_join v Cv rdk ::= sh_join_fast v Cv rdk.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import StoreCache.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import LiaOn.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Ltac zs_wrap e ::= rewrite (unsigned_lit_wrap e).
Ltac zs_wrap_in e H ::= rewrite (unsigned_lit_wrap e) in H.
Ltac zs_idioms ::=
  match goal with
  | |- context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) by (first [lia | zrange_nonneg])
  end.
Ltac zs_idioms_in H ::=
  match type of H with
  | context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) in H by (first [lia | zrange_nonneg])
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma esc_extra_plain : forall c, 32 <= c -> c <> 34 -> c <> 92 -> esc_extra c = 0.
Proof.
  intros c H1 H2 H3. unfold esc_extra.
  destruct (Z.eqb_spec c 34), (Z.eqb_spec c 92), (Z.eqb_spec c 8), (Z.eqb_spec c 12), (Z.eqb_spec c 10), (Z.eqb_spec c 13), (Z.eqb_spec c 9); cbn [orb]; try (cut_to H1 e1 e e0 H2 H3 n n0 n1 n2 n3 n4; (cut_to H1 e1 e e0 H2 H3 n n0 n1 n2 n3 n4; lia)).
  destruct (Z.ltb_spec c 32); [lia| reflexivity].
Qed.

Lemma esc_extra_special : forall c, c < 32 \/ c = 34 \/ c = 92 -> 1 <= esc_extra c.
Proof.
  intros c H. unfold esc_extra. destruct (_ || _) eqn:EQ; [lia|].
  destruct (Z.ltb_spec c 32); [lia|]. exfalso.
  rewrite !Bool.orb_false_iff in EQ. destruct EQ as ((((((E1 & E2) & _) & _) & _) & _) & _).
  apply Z.eqb_neq in E1. apply Z.eqb_neq in E2. lia.
Qed.

Lemma land255 : forall c, 0 <= c < 256 -> Z.land c 255 = c.
Proof. intros c Hc. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.


(* [comment removed for export] *)
Ltac ugd := let G := fresh "G" in zstep; if_cases G; zify_cond G; try (exfalso; lia).

(* [comment removed for export] *)
Definition AEJT : Z := 0x2115c.
Definition EJT : list byte := map wb
  [48; 89; 6; 0; 228; 89; 6; 0; 156; 89; 6; 0; 124; 89; 6; 0; 204; 89; 6; 0; 252; 89; 6; 0; 124; 89; 6; 0; 124; 89; 6; 0;
   124; 89; 6; 0; 124; 89; 6; 0; 124; 89; 6; 0; 124; 89; 6; 0; 124; 89; 6; 0; 124; 89; 6; 0; 124; 89; 6; 0; 124; 89; 6; 0;
   124; 89; 6; 0; 124; 89; 6; 0; 124; 89; 6; 0; 124; 89; 6; 0; 124; 89; 6; 0; 124; 89; 6; 0; 124; 89; 6; 0; 124; 89; 6; 0;
   124; 89; 6; 0; 124; 89; 6; 0; 180; 89; 6; 0].

Definition ejt_sel (c : Z) : Z :=
  if c =? 8 then 0x65930 else if c =? 9 then 0x659e4 else if c =? 10 then 0x6599c
  else if c =? 12 then 0x659cc else if c =? 13 then 0x659fc else if c =? 34 then 0x659b4 else 0x6597c.

Lemma ejt_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m AEJT EJT.
Proof.
  intros m MI.
  pose proof (ro_cells_image bsegs m AEJT EJT MI ltac:(vm_compute; reflexivity) ltac:(unfold AEJT; lia) ltac:(cbn; unfold AEJT; lia)) as [_ H].
  cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H.
Qed.

Lemma byte_list_eq : forall l1 l2 : list byte, map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|b1 l1 IH]; intros [|b2 l2] H; cbn in H; try discriminate; [reflexivity|].
  inversion H. f_equal; [apply bv_eq; assumption| apply IH; assumption].
Qed.

Lemma ejt_entry : forall c, 8 <= c <= 34 ->
  firstn 4 (skipn (Z.to_nat (Z.shiftl (c - 8) 2)) EJT) = le4 (Z_to_bv 64 (ejt_sel c)).
Proof.
  intros c Hc.
  assert (H : exists n, c = 8 + Z.of_nat n /\ (n < 27)%nat) by (exists (Z.to_nat (c - 8)); lia).
  (nelim H 3%nat; intros n -> Hn).
  do 27 (destruct n as [|n]; [apply byte_list_eq; vm_compute; reflexivity|]). lia.
Qed.

Lemma ejt_read : forall m c, mem_inv bsegs m -> 8 <= c <= 34 ->
  ov_read_bytes bsegs m (wa (Z.shiftl (c - 8) 2 + AEJT)) 4 = Some (le4 (Z_to_bv 64 (ejt_sel c))).
Proof.
  intros m c MI Hc. rewrite Z.add_comm, <- ejt_entry by exact Hc.
  apply (bytes_at_read bsegs m AEJT EJT (Z.shiftl (c - 8) 2) 4 (ejt_bytes m MI)).
  - rewrite Z.shiftl_mul_pow2 by lia. lia.
  - change (length EJT) with 108%nat. rewrite Z.shiftl_mul_pow2 by lia. lia.
Qed.

Lemma ejt_sel_default : forall c, c <> 8 -> c <> 9 -> c <> 10 -> c <> 12 -> c <> 13 -> c <> 34 -> ejt_sel c = 0x6597c.
Proof.
  intros. unfold ejt_sel.
  repeat match goal with |- context [?x =? ?y] => destruct (Z.eqb_spec x y); [lia|] end. reflexivity.
Qed.

Lemma ejt_sel_range : forall c, 0 <= ejt_sel c < 2^20.
Proof. intros c. unfold ejt_sel. repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Section Emit.
  Variable AI : art_iface.
  Hypothesis SPRU : asprintf_u04x_stmt_b.

  Variables (S : Z) (str tail : list byte).
  Hypothesis NONUL : ~ In (wb 0) str.
  Notation full := (str ++ wb 0 :: tail).
  Notation L := (Z.of_nat (length str)).
  Notation E := (esc_count str).
  Notation ch i := (bv_unsigned (chb str tail i)).
  Notation pos i := (CJ_pstrA.pos str i).

  (* [comment removed for export] *)
  Variables (m2 : word -> option byte) (mo2 : Model) (g2 : lghost)
            (sp0 SPB : Z) (LB2 : list cblock) (LF : list fframe) (TRS2 : list (list Z)) (B2 : Z)
            (B off len' n lo : Z) (sp : word) (F0 : bvmap 5 word) (x3 x4 : word).
  Notation SPF := (bv_unsigned sp - 128).
  Notation OUT := (B + off).
  Definition WE : list (Z * Z) := [(lo, SPF); (OUT, OUT + (L + E + 3))].

  Hypothesis HART2 : ART AI sp0 SPB LB2 LF TRS2 B2 m2 mo2 g2.
  Hypothesis INB : In (B, len') LB2.
  Hypothesis INS : In (S, n) LB2.
  Hypothesis NBS : B <> S.
  Hypothesis STR2 : bytes_at bsegs m2 S full.
  Hypothesis LENN : L + 1 + Z.of_nat (length tail) = n.
  Hypothesis OFF : 0 <= off.
  Hypothesis ROOM : off + (L + E + 3) + 1 <= len'.
  Hypothesis LOF : alloc_ceiling <= lo /\ lo + AFORMAT_STACK <= SPF.
  Hypothesis SPB_hi : SPF + 128 <= SPB /\ SPB < 2^62.
  Hypothesis SP47 : SPF + 192 <= 2^47.
  Hypothesis SSZ2 : sh_zero m2 alloc_ceiling (2^47).
  (* [comment removed for export] *)
  Hypothesis FR3 : rw_cells bsegs m2 SPF [C8 (Z_to_bv 64 OUT); C8 (Z_to_bv 64 A_FMT_u04x); C8 (Z_to_bv 64 (L + E))].

  Definition EINV (mm : word -> option byte) (bsc : list byte) : Prop :=
    u8arr bsegs mm B bsc /\ Z.of_nat (length bsc) = len' /\ munch WE m2 mm /\ wmono bsegs m2 mm
    /\ mem_inv bsegs mm /\ stk bsegs mm lo SPF.
  Definition FAG (Fc : bvmap 5 word) : Prop := forall k : bv 5, bv_unsigned k <> 10 -> reg_get Fc k = reg_get F0 k.

  (* [comment removed for export] *)
  Lemma blkB : ablock_range B len'.
  Proof. exact (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HART2 INB). Qed.
  Lemma blkS : ablock_range S n.
  Proof. exact (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HART2 INS). Qed.
  Lemma disjBS : B + len' <= S \/ S + n <= B.
  Proof.
    pose proof (art_blocks_disjoint AI _ _ _ _ _ _ _ _ _ _ _ _ _ HART2 INB INS NBS) as D. pose proof (esc_count_range str) as ER. lia.
  Qed.

  Lemma S_bound2 : 0 <= S /\ S + L + 1 + Z.of_nat (length tail) <= 2^64.
  Proof. pose proof (bytes_at_bound _ _ _ _ STR2) as X. rewrite length_app in X. cbn [length] in X. lia. Qed.

  Ltac pre :=
    pose proof S_bound2 as SB; (nelimp blkB 4%nat; intros B1 B2' B3 B4); (nelimp blkS 4%nat; intros S1 S2' S3 S4); pose proof disjBS as DBS;
    pose proof LOF as [LO1 LO2]; pose proof SPB_hi as [PL2 PL3];
    pose proof (art_block_sclr AI _ _ _ _ _ _ _ _ _ B len' B (Z.max len' 1) HART2 INB ltac:(lia) ltac:(lia)) as BSC;   (* [comment removed for export] *)
    pose proof (art_block_sclr AI _ _ _ _ _ _ _ _ _ S n S (Z.max n 1) HART2 INS ltac:(lia) ltac:(lia)) as SSC;
    unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in BSC, SSC;
    unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in B1, S1; try rewrite alloc_ceiling_eq in *; unfold AFORMAT_STACK in LO2;
    pose proof (esc_count_range str) as ER.

  (* [comment removed for export] *)
  Lemma ART_at : forall mm, munch WE m2 mm -> wmono bsegs m2 mm -> ART AI sp0 SPB LB2 LF TRS2 B2 mm mo2 g2.
  Proof.
    intros mm MU WM. pre.
    eapply (art_frame AI); [exact HART2| exact MU| exact WM|]. unfold WE.
    constructor; [right; left; cbn [fst snd]; rewrite ?alloc_ceiling_eq; lia|]. constructor; [| constructor].
    do 7 right. left. exists B, len'. split; [exact INB| cbn [fst snd]; lia].
  Qed.

  Lemma SSZ_at : forall mm, munch WE m2 mm -> sh_zero mm alloc_ceiling (2^47).
  Proof.
    intros mm MU. pre. try rewrite <- alloc_ceiling_eq in *.
    eapply sh_zero_stack_munch; [exact SSZ2| exact MU|]. unfold WE.
    constructor; [cbn [fst snd]; sclr_tac2|]. constructor; [cbn [fst snd]; sclr_tac2| constructor].
  Qed.

  Lemma STR_at : forall mm, munch WE m2 mm -> bytes_at bsegs mm S full.
  Proof.
    intros mm MU. pre.
    eapply bytes_at_transport; [exact STR2| exact MU|]. unfold WE. rewrite length_app. cbn [disjoint_from length]. split; [lia|]. split; [(lia_on LENN OFF ROOM SB B1 B2' S2' DBS BSC SSC ER)| exact I].
  Qed.

  Lemma FR3_at : forall mm, munch WE m2 mm -> wmono bsegs m2 mm ->
    rw_cells bsegs mm SPF [C8 (Z_to_bv 64 OUT); C8 (Z_to_bv 64 A_FMT_u04x); C8 (Z_to_bv 64 (L + E))].
  Proof. intros mm MU WM. pre. eapply rw_cells_transport; [exact FR3| exact MU| exact WM|]. unfold WE. cbn. lia. Qed.

  (* [comment removed for export] *)
  Lemma out_chk : forall mm e, munch WE m2 mm -> wmono bsegs m2 mm -> 0 <= off + e < len' -> shchk mm (OUT + e) 1.
  Proof.
    intros mm e MU WM He. destruct (art_shadow AI _ _ _ _ _ _ _ _ _ _ _ (ART_at mm MU WM) INB) as [_ SO].
    eapply shadow_ok_shchk1; [exact SO| lia].
  Qed.

  Lemma str_chk : forall mm i, munch WE m2 mm -> wmono bsegs m2 mm -> 0 <= i <= L -> shchk mm (S + i) 1.
  Proof.
    intros mm i MU WM Hi. destruct (art_shadow AI _ _ _ _ _ _ _ _ _ _ _ (ART_at mm MU WM) INS) as [_ SO].
    eapply shadow_ok_shchk1; [exact SO| lia].
  Qed.

  (* [comment removed for export] *)
  Notation M1 := 18446744073709551615 (only parsing).
  Notation HST pc x1 x5 x6 x7 s0v x10 x11 x12 x13 x14 x15 x16 x17 x18 s3v s5v x28 x29 x30 x31 Fc fcc mm :=
    (MS (mkR x1 (Z_to_bv 64 SPF) x3 x4 x5 x6 x7 (Z_to_bv 64 s0v) (Z_to_bv 64 AEJT) x10 x11 x12 x13 x14 x15 x16 x17
             x18 (Z_to_bv 64 s3v) (Z_to_bv 64 26) (Z_to_bv 64 s5v) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 L) (Z_to_bv 64 E)
             (Z_to_bv 64 M1) (Z_to_bv 64 32) (Z_to_bv 64 92) x28 x29 x30 x31)
        Fc (Z_to_bv 64 pc) fcc None mm (seg_rom bsegs)).

  Definition emit_done : machine_state -> Prop :=
    fun ms' => exists mm bsc Fc fcc x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x18 x28 x29 x30 x31,
      ms' = HST 0x86c34 x1 x5 x6 x7 (S + L) x10 x11 x12 (Z_to_bv 64 34) x14 x15 x16 x17 x18 (S + L) (OUT + (L + E)) x28 x29 x30 x31 Fc fcc mm
      /\ EINV mm bsc /\ frm0 fcc /\ FAG Fc.

  (* [comment removed for export] *)
  Definition HEADK (i : Z) : Prop :=
    forall mm bsc Fc fcc x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x18 x28 x29 x30 x31,
      EINV mm bsc -> frm0 fcc -> FAG Fc ->
      evt bsegs emit_done (HST 0x86a1c x1 x5 x6 x7 (S + i) x10 x11 x12 (Z_to_bv 64 34) x14 x15 x16 x17 x18 (S + i) (OUT + pos i) x28 x29 x30 x31 Fc fcc mm).

  (* [comment removed for export] *)
  Lemma head_L : HEADK L.
  Proof.
    unfold HEADK. intros until x31. intros INV FRM FA. pre.
    (nelimp INV 6%nat; intros ARR LEN MU WM MI ST).
    pose proof (ch_read S str tail mm L (STR_at mm MU) ltac:(lia)) as RD.
    pose proof (str_chk mm L MU WM ltac:(lia)) as CK.
    zstep. zstep. sepM. asan_chk CK.
    zstep. cbv beta. rewrite (ch_L str tail). zstep. try rewrite (land255 0) by lia.
    zstep. if_cases Kz; zify_cond Kz; [| exfalso; lia].
    apply evt_done. unfold emit_done. rewrite (pos_L str).
    nexists 20%nat. split; [reflexivity|]. split; [exact INV|]. split; [exact FRM| exact FA].
  Qed.

  (* [comment removed for export] *)
  Lemma emit_tail : forall i, 0 <= i < L -> HEADK (i + 1) ->
    forall mm bsc Fc fcc x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x28 x29 x30 x31,
      EINV mm bsc -> frm0 fcc -> FAG Fc ->
      evt bsegs emit_done (HST 0x86b70 x1 x5 x6 x7 (S + i) x10 x11 x12 (Z_to_bv 64 34) x14 x15 x16 x17 (Z_to_bv 64 (OUT + pos (i + 1))) (S + i) (OUT + pos i) x28 x29 x30 x31 Fc fcc mm).
  Proof.
    intros i Hi K. intros until x31. intros INV FRM FA. pre.
    pose proof (pos_bound str i ltac:(lia)) as PB1. pose proof (pos_bound str (i + 1) ltac:(lia)) as PB2.
    ugd. zstep. zstep. zstep.
    zstep. if_cases Kw; zify_cond Kw; [| exfalso; lia].
    replace (S + i + 1) with (S + (i + 1)) by lia.
    unfold HEADK in K. eapply K; [exact INV| exact FRM| exact FA].
  Qed.

  (* [comment removed for export] *)
  Ltac ustore ea e b tac :=
    lazymatch goal with
    | ARR : u8arr bsegs ?m B ?buf |- _ =>
        let SOK := fresh "SOK" in let ARR' := fresh "ARR" in
        destruct (u8_store' m B buf ea (off + e) b ARR) as [SOK ARR'];
        [ lia | rewrite ?upd_length; lia
        | clear ARR; step;
          lazymatch goal with
          | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 ?a ?bs) _) =>
              replace (write_to_mem m1 a bs) with (write_to_mem m1 (wa ea) [b])
                by (f_equal; first [tac| unfold wa; f_equal; lia]);
              store_done; rename ARR' into ARR
          end ]
    end.

  (* [comment removed for export] *)
  Lemma emit_sprintf_call : forall i, 0 <= i < L -> esc_extra (ch i) = 5 ->
    forall mm bsc Fc fcc x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31,
      EINV mm bsc -> frm0 fcc -> FAG Fc ->
      evt bsegs (fun ms' => exists mm' bsc' Fc' fcc' x5' x6' x7' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31',
                   ms' = HST 0x86ae4 (Z_to_bv 64 0x86ae4) x5' x6' x7' (S + i) (Z_to_bv 64 5) x11' x12' x13' x14' x15' x16' x17' (Z_to_bv 64 (OUT + pos i + 2)) (S + i) (OUT + pos i) x28' x29' x30' x31' Fc' fcc' mm'
                   /\ EINV mm' bsc' /\ frm0 fcc' /\ FAG Fc')
        (HST ASPRINTF_T (Z_to_bv 64 0x86ae4) x5 x6 x7 (S + i) (Z_to_bv 64 (OUT + pos i + 2)) (Z_to_bv 64 A_FMT_u04x) (Z_to_bv 64 (ch i)) x13 x14 x15 x16 x17 (Z_to_bv 64 (OUT + pos i + 2)) (S + i) (OUT + pos i) x28 x29 x30 x31 Fc fcc mm).
  Proof.
    intros i Hi EX5. intros until x31. intros INV FRM FA. pre.
    (nelimp INV 6%nat; intros ARR LEN MU WM MI ST).
    destruct (ch_lt str tail NONUL i Hi) as [_ CR].
    pose proof (pos_bound str i ltac:(lia)) as PB1. pose proof (pos_next_bound str tail NONUL i Hi) as PB2.
    set (k := Z.to_nat (off + pos i + 2)).
    (nelim (u8arr_split3 mm B bsc k 6 ARR ltac:(lia)) 3%nat; intros A1 A2 A3).
    replace (B + Z.of_nat k) with (OUT + pos i + 2) in A2, A3 by lia.
    assert (SPE : bv_unsigned (Z_to_bv 64 SPF) = SPF) by (apply unsigned_lit; lia).
    pose proof (ART_at mm MU WM) as HL. pose proof (SSZ_at mm MU) as SSZ.
    (nelim (art_fmt_facts AI _ _ _ _ _ _ _ _ _ HL SSZ) 4%nat; intros FC MR LOW [canary ASSP]).
    (nelim (art_fmt_lits AI _ _ _ _ _ _ _ _ _ HL) 6%nat; intros _ _ _ _ _ SOF).
    destruct (art_shadow AI _ _ _ _ _ _ _ _ _ _ _ HL INB) as [_ SOB].
    eapply evt_cut.
    { eapply (SPRU (Z_to_bv 64 0x86ae4) (Z_to_bv 64 SPF)) with (dn := 6%nat) (lo := lo) (c := ch i) (canary := canary); rewrite ?SPE, ?unsigned_lit by lia;
        first [ exact A2 | reflexivity | exact SOF | (cut_to LENN OFF ROOM Hi EX5 SB B1 ER CR PB1 PB2; lia) | apply Z.mod_small; lia | idtac ].
      unfold asprintf_pre_b. rewrite SPE. split; [exact FC|]. split; [exact MR|]. split; [exact LOW|]. split; [exact MI|]. split; [exact FRM|].
      split; [exact ASSP|]. split; [exact ST|]. split; [try rewrite alloc_ceiling_eq; lia|]. split; [unfold AFMT_STACK; lia|]. split; [lia|].
      split; [left; lia|]. sepM. split; [split; [unfold AIMG_HI; lia| app_rng0]|].
      eapply shadow_ok_sub; [exact SOB| lia| lia| lia]. }
    cbv beta. intros ms' PO.
    (nelim PO 26%nat; intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ft fc' m' -> MUc WMc MI' FRM' FAc ST' SSP' OUTC).
    rewrite SPE in MUc, ST'.
    replace (ret_pc (Z_to_bv 64 0x86ae4)) with (Z_to_bv 64 0x86ae4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply evt_done. nexists 18%nat. split; [reflexivity|].
    apply (u8arr_transport bsegs _ mm m' _ _ A1) in MUc as A1'; [| exact WMc| cbn; rewrite firstn_length_le by lia; lia].
    apply (u8arr_transport bsegs _ mm m' _ _ A3) in MUc as A3'; [| exact WMc| cbn; rewrite skipn_length; lia].
    replace (OUT + pos i + 2) with (B + (off + pos i + 2)) in OUTC, A3' by lia.
    destruct (u8arr_join3' m' B _ (off + pos i + 2) _ _ _ A1' ltac:(rewrite firstn_length_le by lia; lia) OUTC A3') as [ARR' L6].
    split; [| split; [exact FRM'|]].
    - split; [exact ARR'|]. split.
      { revert L6. generalize (map (Z_to_bv 8) (117 :: F_printf_iface.hex4_lower (ch i)) ++ Z_to_bv 8 0 :: skipn (Datatypes.S (length (117 :: F_printf_iface.hex4_lower (ch i)))) (firstn 6 (skipn k bsc))) as mid.
        intros mid L6. rewrite !length_app, L6, firstn_length_le, length_skipn by lia. lia. }
      split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MUc]. unfold WE, sub_fp. cbn. intros a [X [Y _]]. (lia_on NBS LENN OFF ROOM Hi EX5 SB B1 B2' B4 S2' S4 DBS LO1 LO2 ER LEN PB1 PB2 X Y). }
      split; [eapply wmono_trans; [exact WM| exact WMc]|]. split; [exact MI'| exact ST'].
    - intros r Hr. rewrite (FAc r Hr). apply FA. exact Hr.
  Qed.

  (* [comment removed for export] *)
  Lemma emit_b8 : forall i, 0 <= i < L -> HEADK (i + 1) -> esc_extra (ch i) = 1 ->
    forall mm bsc Fc fcc x1 x5 x6 x7 (v : Z) x11 x12 x14 x15 x16 x17 x28 x29 x30 x31,
      EINV mm bsc -> frm0 fcc -> FAG Fc -> 0 <= v < 256 ->
      evt bsegs emit_done (HST 0x86b6c x1 x5 x6 x7 (S + i) (Z_to_bv 64 v) x11 x12 (Z_to_bv 64 34) x14 x15 x16 x17 (Z_to_bv 64 (OUT + pos i + 2)) (S + i) (OUT + pos i) x28 x29 x30 x31 Fc fcc mm).
  Proof.
    intros i Hi K EX1. intros until x31. intros INV FRM FA Hv. pre.
    (nelimp INV 6%nat; intros ARR LEN MU WM MI ST).
    pose proof (pos_bound str i ltac:(lia)) as PB1. pose proof (pos_next_bound str tail NONUL i Hi) as PB2.
    unfold WE in MU.
    ustore (OUT + pos i + 2) (pos i + 2) (wb v) ltac:(symmetry; apply le1_lit8; lia).
    replace (OUT + pos i + 2) with (OUT + pos (i + 1)) by (rewrite (pos_step str tail NONUL i Hi); lia).
    eapply (emit_tail i Hi K); [| exact FRM| exact FA].
    split; [exact ARR|]. split; [rewrite upd_length; exact LEN|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  Qed.

  (* [comment removed for export] *)
  Lemma emit_u : forall i, 0 <= i < L -> HEADK (i + 1) -> esc_extra (ch i) = 5 ->
    forall mm bsc Fc fcc x1 x5 x6 x7 x10 x11 x14 x15 x16 x17 x28 x29 x30 x31,
      EINV mm bsc -> frm0 fcc -> FAG Fc ->
      evt bsegs emit_done (HST 0x86ad8 x1 x5 x6 x7 (S + i) x10 x11 (Z_to_bv 64 (ch i)) (Z_to_bv 64 34) x14 x15 x16 x17 (Z_to_bv 64 (OUT + pos i + 2)) (S + i) (OUT + pos i) x28 x29 x30 x31 Fc fcc mm).
  Proof.
    intros i Hi K EX5. intros until x31. intros INV FRM FA. pre.
    (nelimp INV 6%nat; intros ARR LEN MU WM MI ST).
    pose proof (pos_bound str i ltac:(lia)) as PB1. pose proof (pos_next_bound str tail NONUL i Hi) as PB2.
    pose proof (FR3_at mm MU WM) as FR. unfold A_FMT_u04x in FR.
    zstep. zstep. zstep.
    eapply evt_cut; [eapply (emit_sprintf_call i Hi EX5); [exact INV| exact FRM| exact FA]|].
    cbv beta. intros ms' PO.
    (nelim PO 22%nat; intros mm' bsc' Fc' fcc' x5' x6' x7' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' -> INV' FRM' FA').
    clear ARR LEN MU WM MI ST INV FR.
    (nelimp INV' 6%nat; intros ARR LEN MU WM MI ST).
    zstep. zstep. ugd. zstep. zstep.
    replace (OUT + pos i + 6) with (OUT + pos (i + 1)) by (rewrite (pos_step str tail NONUL i Hi); lia).
    eapply (emit_tail i Hi K); [exact INV'| exact FRM'| exact FA'].
  Qed.

  Ltac dispatch := zstep; zstep; step; try rewrite sx32_lit by lia; zstep; step.

  (* [comment removed for export] *)
  Lemma emit_esc : forall i, 0 <= i < L -> HEADK (i + 1) ->
    forall mm bsc Fc fcc x1 x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31,
      EINV mm bsc -> frm0 fcc -> FAG Fc -> (ch i < 32 \/ ch i = 34 \/ ch i = 92) ->
      evt bsegs emit_done (HST 0x86a48 x1 x5 x6 x7 (S + i) (Z_to_bv 64 (Z.shiftr (S + i) 3 + 2147450880)) (Z_to_bv 64 (ch i)) (Z_to_bv 64 (ch i)) (Z_to_bv 64 34) x14 x15 x16 x17
                              (Z_to_bv 64 (OUT + pos i + 1)) (S + i) (OUT + pos i) x28 x29 x30 x31 Fc fcc mm).
  Proof.
    intros i Hi K. intros until x31. intros INV FRM FA HC. pre.
    (nelimp INV 6%nat; intros ARR LEN MU WM MI ST).
    destruct (ch_lt str tail NONUL i Hi) as [_ CR].
    pose proof (pos_bound str i ltac:(lia)) as PB1. pose proof (pos_next_bound str tail NONUL i Hi) as PB2.
    pose proof (esc_extra_range (ch i)) as EXR. pose proof (esc_extra_special (ch i) HC) as EX1.
    pose proof (out_chk mm (pos i + 1) MU WM ltac:(lia)) as CK1. replace (OUT + (pos i + 1)) with (OUT + pos i + 1) in CK1 by lia.
    unfold WE in MU.
    (* [comment removed for export] *)
    ugd.
    zstep. zstep. sepM. asan_chk CK1.
    ustore (OUT + pos i + 1) (pos i + 1) (wb 92) ltac:(reflexivity).
    assert (INV1 : EINV m (upd bsc (Z.to_nat (off + (pos i + 1))) (wb 92))).
    { split; [exact ARR|]. split; [rewrite upd_length; exact LEN|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST]. }
    (* [comment removed for export] *)
    pose proof (out_chk m (pos i + 2) MU WM ltac:(lia)) as CK2'. replace (OUT + (pos i + 2)) with (OUT + pos i + 2) in CK2' by lia.
    pose proof (str_chk m i MU WM ltac:(lia)) as CKS'.
    (* [comment removed for export] *)
    sepM. asan_chk CKS'.
    pose proof (ch_read S str tail m i (STR_at m ltac:(exact MU)) ltac:(lia)) as RD'.
    zstep. cbv beta. zstep. zstep. zstep. sepM. if_cases K4; zify_cond K4.
    - (* [comment removed for export] *)
      assert (HC2 : ch i < 8 \/ ch i = 92).
      { revert K4. destruct (Z_lt_le_dec (ch i) 8); [intros; lia|]. rewrite Z.mod_small by lia. intros; lia. }
      clear K4. zstep. if_cases K5; zify_cond K5.
      + (* [comment removed for export] *) eapply (emit_u i Hi K); [| exact INV1| exact FRM| exact FA].
        unfold esc_extra. replace (ch i <? 32) with true by (symmetry; apply Z.ltb_lt; lia).
        sepM. destruct (Z.eqb_spec (ch i) 34), (Z.eqb_spec (ch i) 92), (Z.eqb_spec (ch i) 8), (Z.eqb_spec (ch i) 12), (Z.eqb_spec (ch i) 10), (Z.eqb_spec (ch i) 13), (Z.eqb_spec (ch i) 9); cbn [orb]; (lia_on e HC2 K5).
      + (* [comment removed for export] *)
        zstep. zstep. sepM. asan_chk CK2'.
        ustore (OUT + pos i + 2) (pos i + 2) (wb 92) ltac:(reflexivity). zstep.
        replace (OUT + pos i + 2) with (OUT + pos (i + 1)) by (rewrite (pos_step str tail NONUL i Hi), esc_extra_gt34, K5, Z.eqb_refl by lia; lia).
        eapply (emit_tail i Hi K); [| exact FRM| exact FA].
        split; [exact ARR|]. split; [rewrite !upd_length; exact LEN|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
    - (* [comment removed for export] *)
      assert (HCR : 8 <= ch i <= 34).
      { revert K4. destruct (Z_lt_le_dec (ch i) 8).
        - replace (ch i + -8) with ((ch i + -8 + 2^64) + (-1) * 2^64) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. intros; lia.
        - rewrite Z.mod_small by lia. intros; lia. }
      clear K4.
      pose proof (ejt_read m (ch i) MI HCR) as RT. unfold AEJT in RT |- *. pose proof (ejt_sel_range (ch i)) as SR.
      (* [comment removed for export] *)
      assert (LET : forall (pc : Z) (v : Z) x10' x11', esc_extra (ch i) = 1 -> 0 <= v < 256 ->
        (pc = 0x86a8c /\ v = 98) \/ (pc = 0x86af8 /\ v = 110) \/ (pc = 0x86b28 /\ v = 102) \/ (pc = 0x86b40 /\ v = 116) \/ (pc = 0x86b58 /\ v = 114) ->
        evt bsegs emit_done (HST pc x1 x5 x6 x7 (S + i) x10' x11' (Z_to_bv 64 (ch i)) (Z_to_bv 64 34) x14 x15 x16 x17 (Z_to_bv 64 (OUT + pos i + 2)) (S + i) (OUT + pos i) x28 x29 x30 x31 Fc fcc m)).
      { intros pc v x10' x11' EXv Hv Hpc.
        sepM. sepM. destruct Hpc as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]];
          zstep; zstep; asan_chk CK2'; zstep;
          first [ eapply (emit_b8 i Hi K EXv); [exact INV1| exact FRM| exact FA| lia]
                | zstep; eapply (emit_b8 i Hi K EXv); [exact INV1| exact FRM| exact FA| lia] ]. }
      destruct (Z.eq_dec (ch i) 8) as [E8|N8]; [| destruct (Z.eq_dec (ch i) 9) as [E9|N9]; [| destruct (Z.eq_dec (ch i) 10) as [E10|N10];
        [| destruct (Z.eq_dec (ch i) 12) as [E12|N12]; [| destruct (Z.eq_dec (ch i) 13) as [E13|N13]; [| destruct (Z.eq_dec (ch i) 34) as [E34|N34]]]]]].
      + rewrite E8 in *. cbn [ejt_sel Z.eqb Pos.eqb] in RT. dispatch.
        eapply (LET 0x86a8c 98); [reflexivity| lia| tauto].
      + rewrite E9 in *. cbn [ejt_sel Z.eqb Pos.eqb] in RT. dispatch.
        sepM. eapply (LET 0x86b40 116); [reflexivity| lia| (cut_on [LOF SPB_hi Hi HC SB ER CR PB1 EXR SMf SMf0 SMf1 HCR SR] tauto)].
      + rewrite E10 in *. cbn [ejt_sel Z.eqb Pos.eqb] in RT. dispatch.
        sepM. eapply (LET 0x86af8 110); [reflexivity| lia| (cut_on [LOF SPB_hi Hi HC SB ER CR PB1 EXR SMf SMf0 SMf1 HCR SR] tauto)].
      + rewrite E12 in *. cbn [ejt_sel Z.eqb Pos.eqb] in RT. dispatch.
        sepM. eapply (LET 0x86b28 102); [reflexivity| lia| (cut_on [LOF SPB_hi Hi HC SB ER CR PB1 EXR SMf SMf0 SMf1 HCR SR] tauto)].
      + rewrite E13 in *. cbn [ejt_sel Z.eqb Pos.eqb] in RT. dispatch.
        sepM. eapply (LET 0x86b58 114); [reflexivity| lia| (cut_on [LOF SPB_hi Hi HC SB ER CR PB1 EXR SMf SMf0 SMf1 HCR SR] tauto)].
      + (* [comment removed for export] *)
        rewrite E34 in *. cbn [ejt_sel Z.eqb Pos.eqb] in RT. dispatch.
        zstep. zstep. sepM. asan_chk CK2'.
        ustore (OUT + pos i + 2) (pos i + 2) (wb 34) ltac:(reflexivity). zstep.
        replace (OUT + pos i + 2) with (OUT + pos (i + 1)) by (rewrite (pos_step str tail NONUL i Hi), resc1b_extra by lia; rewrite E34; cbn; lia).
        eapply (emit_tail i Hi K); [| exact FRM| exact FA].
        split; [exact ARR|]. split; [rewrite !upd_length; exact LEN|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
      + (* [comment removed for export] *)
        rewrite (ejt_sel_default (ch i)) in RT by assumption.
        dispatch. eapply (emit_u i Hi K); [| exact INV1| exact FRM| exact FA].
        unfold esc_extra. replace (ch i <? 32) with true by (symmetry; apply Z.ltb_lt; lia).
        sepM. destruct (Z.eqb_spec (ch i) 34), (Z.eqb_spec (ch i) 92), (Z.eqb_spec (ch i) 8), (Z.eqb_spec (ch i) 12), (Z.eqb_spec (ch i) 10), (Z.eqb_spec (ch i) 13), (Z.eqb_spec (ch i) 9); cbn [orb]; (lia_on e HCR N8 N9 N10 N12 N13 N34).
  Qed.

  Lemma emit_head : forall i, 0 <= i < L -> HEADK (i + 1) -> HEADK i.
  Proof.
    intros i Hi K. unfold HEADK. intros until x31. intros INV FRM FA. pre.
    (nelimp INV 6%nat; intros ARR LEN MU WM MI ST).
    destruct (ch_lt str tail NONUL i Hi) as [_ CR].
    pose proof (pos_bound str i ltac:(lia)) as PB1. pose proof (pos_next_bound str tail NONUL i Hi) as PB2.
    pose proof (esc_extra_range (ch i)) as EXR.
    pose proof (out_chk mm (pos i + 1) MU WM ltac:(lia)) as CK1. replace (OUT + (pos i + 1)) with (OUT + pos i + 1) in CK1 by lia.
    pose proof (ch_read S str tail mm i (STR_at mm MU) ltac:(lia)) as RD.
    pose proof (str_chk mm i MU WM ltac:(lia)) as CKS.
    (* [comment removed for export] *)
    zstep. zstep. sepM. asan_chk CKS.
    zstep. cbv beta. zstep. rewrite (land255 (ch i)) by lia.
    zstep. if_cases Kz; zify_cond Kz; [exfalso; lia|].
    zstep.
    zstep. if_cases K1; zify_cond K1.
    { eapply (emit_esc i Hi K); [exact INV| exact FRM| exact FA| lia]. }
    zstep. if_cases K2; zify_cond K2.
    { eapply (emit_esc i Hi K); [exact INV| exact FRM| exact FA| lia]. }
    zstep. if_cases K3; zify_cond K3.
    2: { eapply (emit_esc i Hi K); [exact INV| exact FRM| exact FA| lia]. }
    (* [comment removed for export] *)
    assert (EX0 : esc_extra (ch i) = 0).
    { apply esc_extra_plain; lia. }
    zstep. zstep. sepM. asan_chk CK1.
    unfold WE in MU.
    ustore (OUT + pos i + 1) (pos i + 1) (chb str tail i) ltac:(symmetry; apply le1_zxb).
    zstep.
    replace (OUT + pos i + 1) with (OUT + pos (i + 1)) by (rewrite (pos_step str tail NONUL i Hi); lia).
    eapply (emit_tail i Hi K); [| exact FRM| exact FA].
    split; [exact ARR|]. split; [rewrite upd_length; exact LEN|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  Qed.

  Lemma emit_loop : forall (k : nat) (i : Z), Z.of_nat k = L - i -> 0 <= i <= L -> HEADK i.
  Proof.
    induction k as [|k IH]; intros i Hk Hi.
    - replace i with L by lia. apply head_L.
    - apply emit_head; [lia|]. apply IH; lia.
  Qed.
End Emit.


End CeilWrap.
(* [comment removed for export] *)
Ltac zs_wrap e ::= rewrite (unsigned_lit_wrap e).
Ltac zs_wrap_in e H ::= rewrite (unsigned_lit_wrap e) in H.
Ltac zs_idioms ::=
  match goal with
  | |- context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) by (first [lia | zrange_nonneg])
  end.
Ltac zs_idioms_in H ::=
  match type of H with
  | context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) in H by (first [lia | zrange_nonneg])
  end.
Ltac ugd := let G := fresh "G" in zstep; if_cases G; zify_cond G; try (exfalso; lia).
