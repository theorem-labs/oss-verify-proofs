(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Stgw7 V_AKit V_Vsb V_World V_Ma6xg V_Lad4x Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_CrcLib.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.

Definition st0 (s : vstate) : Z :=
  match s with
  | S_Start => 0x10af1 | S_BOM => 0x116b4 | S_TestXml => 0x1133a | S_NotXml => 0x116ba | S_NotMyTag => 0x10d46
  | S_NxtTag => 0x11aa8 | S_StartTag => 0x118f5 | S_Comment => 0x12174 | S_CommentESI => 0x11344 | S_CDATA => 0x1059a
  | S_end_ESITag => 0x102cc | S_ESITag => 0x11c67 | S_ESI_Include => 0x116c3 | S_ESI_Remove => 0x10b4b
  | S_ESI_Comment => 0x10c21 | S_ESI_Bogon => 0x1148d | S_InTag => 0x10ec7 | S_TagError => 0x109b1 | S_Attr => 0x10d55
  | S_SkipAttribute => 0x116d1 | S_AttrGetValue => 0x10c2f | S_AttrDelim => 0x10fbd | S_AttrValue => 0x11ab1
  | S_Until => 0x124ea | S_Match => 0x1048c | S_MatchBuf => 0x1191a
  end.

Definition VI0 : vimg := {|
  vi_bss := 0x41830;
  vi_cb := 0x1bd48;
  vi_do_include := 0x1b0ec; vi_do_remove := 0x1b8b4; vi_do_comment := 0x1b9b8;
  vi_st := st0;
  vi_url := 0x1096b; vi_empty := 0x10ae6; vi_arrow := 0x1108d; vi_cdata_end := 0x10d51;
  vi_tbl_bom := TBL_bom; vi_tbl_starttag := TBL_starttag; vi_tbl_esi := TBL_esi; vi_tbl_attr_include := TBL_attr_include
|}.

(* [comment removed for export] *)
Definition GOT_vct    : Z := 0x303e0.   (* [comment removed for export] *)
Definition GOT_memset : Z := 0x303e8.   (* [comment removed for export] *)
Definition GOT_vsc    : Z := 0x303f0.   (* [comment removed for export] *)
Definition GOT_cp     : Z := 0x303f8.   (* [comment removed for export] *)
Definition GOT_ssp    : Z := 0x30428.   (* [comment removed for export] *)
Definition VCT_TYPTAB : Z := 0x12710.

(* [comment removed for export] *)
Definition vepvars0 : list cell :=
  [ C8 (Z_to_bv 64 (st0 S_Start)); C8 (Z_to_bv 64 (st0 S_BOM)); C8 (Z_to_bv 64 (st0 S_CommentESI));
    C8 (Z_to_bv 64 (st0 S_NxtTag)); C8 (Z_to_bv 64 (st0 S_Comment)); C8 (Z_to_bv 64 (st0 S_end_ESITag));
    C8 (Z_to_bv 64 (st0 S_ESITag)); C8 (Z_to_bv 64 (st0 S_CDATA)); C8 (Z_to_bv 64 (st0 S_NotMyTag));
    C8 (Z_to_bv 64 (st0 S_ESI_Include)); C8 (Z_to_bv 64 (st0 S_ESI_Remove)); C8 (Z_to_bv 64 (st0 S_ESI_Comment));
    C8 (Z_to_bv 64 (st0 S_ESI_Bogon)); C8 (Z_to_bv 64 (st0 S_AttrGetValue)); C8 (Z_to_bv 64 (st0 S_SkipAttribute)) ].
Definition VEPVARS0 : Z := 0x30278.

Definition img_ok0 (m : mem) : Prop :=
     ro_cells rsegs m GOT_vct [C8 (Z_to_bv 64 VCT_TYPTAB)]
  /\ ro_cells rsegs m GOT_memset [C8 (Z_to_bv 64 0x2b058)]
  /\ ro_cells rsegs m GOT_vsc [C8 (Z_to_bv 64 0x41830)]
  /\ ro_cells rsegs m GOT_cp [C8 (Z_to_bv 64 0x41838)]
  /\ ro_cells rsegs m GOT_ssp [C8 (Z_to_bv 64 0x623c8)]
  /\ ro_cells rsegs m VEPVARS0 vepvars0
  /\ ro_cells rsegs m TBL_bom (mtab_cells tbl_bom) /\ ro_cells rsegs m TBL_attr_include (mtab_cells tbl_attr_include)
  /\ ro_cells rsegs m TBL_esi (mtab_cells tbl_esi) /\ ro_cells rsegs m TBL_starttag (mtab_cells tbl_starttag).

(* [comment removed for export] *)
Definition IMG0_LO : Z := 0x30270.
Definition IMG0_HI : Z := 0x31580.

Lemma ro_cells_agree : forall m m' A cs,
  ro_cells rsegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  ro_cells rsegs m' A cs.
Proof.
  intros m m' A cs [Hwf (Ha & Hl & H)] EQ. split; [exact Hwf|]. split; [exact Ha|]. split; [exact Hl|].
  intros i Hi. unfold mrd, wa. rewrite cells_bytes_length in Hi, Hl by exact Hwf.
  rewrite EQ by lia. apply H. rewrite cells_bytes_length by exact Hwf. exact Hi.
Qed.

Lemma img_ok0_ext : forall m m',
  (forall a, IMG0_LO <= a < IMG0_HI -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) -> img_ok0 m -> img_ok0 m'.
Proof.
  (intros m m' EQ; (first [ intro dR_1; dand10 dR_1 as G1 G2 G3 G4 G5 VV T1 T2 T3 T4 | intros (G1 & G2 & G3 & G4 & G5 & VV & T1 & T2 & T3 & T4) ])).
  unfold IMG0_LO, IMG0_HI in EQ.
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; (eapply ro_cells_agree; [eassumption|]); intros a Ha; apply EQ;
    cbn [cells_size csize Nat.add mtab_cells tbl_bom tbl_attr_include tbl_esi tbl_starttag vepvars0 length] in Ha;
    unfold GOT_vct, GOT_memset, GOT_vsc, GOT_cp, GOT_ssp, VEPVARS0, TBL_bom, TBL_attr_include, TBL_esi, TBL_starttag in Ha; lia.
Qed.

(* [comment removed for export] *)
Lemma img_ok0_munch : forall W m m',
  munch W m m' -> (forall a, IMG0_LO <= a < IMG0_HI -> outside W a) -> img_ok0 m -> img_ok0 m'.
Proof.
  intros W m m' MU OUT IMG. eapply img_ok0_ext; [|exact IMG].
  intros a Ha. apply (MU (Z_to_bv 64 a)). unfold IMG0_LO, IMG0_HI in Ha. rewrite unsigned_lit by lia. apply OUT. unfold IMG0_LO, IMG0_HI. lia.
Qed.

(* [comment removed for export] *)
Section X.
  Context {Clg : Ceiling} {AI : AllocSpec LayoutP0}.   (* [comment removed for export] *)
  Lemma img_ok0_ccall : forall A A' m md m' sp win V N,
    ainv A m md -> cframe LayoutP0 (owned A) (owned A') sp win V N m m' ->
    IMG0_HI <= sp - win -> (forall a, IMG0_LO <= a < IMG0_HI -> ~ V a) ->
    img_ok0 m -> img_ok0 m'.
  Proof.
    (intros A A' m md m' sp win V N AI0; (first [ intro dR_2; dand3 dR_2 as C1 _ _ | intros (C1 & _ & _) ]); intros WIN NV IMG).
    eapply img_ok0_ext; [|exact IMG]. intros a Ha. unfold IMG0_LO, IMG0_HI in Ha, WIN.
    assert (NO : ~ owned A a).
    { intros O. destruct (as_owned_where A m md a AI0 O) as [Hs|[_ Hni]].
      - cbn in Hs. unfold p0_static in Hs. lia.
      - apply Hni. unfold in_image. cbn. lia. }
    apply (C1 a ltac:(lia) NO); [right; unfold in_image; cbn; lia | lia | | apply NV; unfold IMG0_LO, IMG0_HI; lia].
    change (al_errno LayoutP0) with 0x420b4. lia.
  Qed.
End X.

(* [comment removed for export] *)
Fixpoint rom_bytes_b (A : Z) (bs : list byte) : bool :=
  match bs with
  | [] => true
  | b :: bs' => match seg_rom rsegs (wa A) with
               | Some b' => bv_eqb b b' && rom_bytes_b (A + 1) bs'
               | None => false
               end
  end.

Lemma rom_bytes_b_sound : forall bs A i, rom_bytes_b A bs = true -> (i < length bs)%nat ->
  seg_rom rsegs (wa (A + Z.of_nat i)) = nth_error bs i.
Proof.
  induction bs as [|b bs IH]; intros A i H Hi; cbn in *; [lia|].
  destruct (seg_rom rsegs (wa A)) as [b'|] eqn:E; [|discriminate].
  apply andb_prop in H. destruct H as [H1 H2].
  unfold bv_eqb in H1. apply Z.eqb_eq in H1. apply bv_eq in H1. subst b'.
  destruct i as [|i].
  - cbn. rewrite Z.add_0_r. exact E.
  - cbn. rewrite <- (IH (A + 1) i H2) by lia. f_equal. f_equal. lia.
Qed.

Lemma ro_cells_of_image : forall m A cs,
  (forall i, A <= i < A + Z.of_nat (cells_size cs) -> m (Z_to_bv 64 i) = None) ->
  cells_wf cs -> rom_bytes_b A (cells_bytes cs) = true ->
  0 <= A -> A + Z.of_nat (cells_size cs) <= 2^64 ->
  ro_cells rsegs m A cs.
Proof.
  intros m A cs NONE WF IB H0 H1. split; [exact WF|].
  pose proof (cells_bytes_length cs WF) as L.
  split; [exact H0|]. split; [rewrite L; exact H1|].
  intros i Hi. unfold mrd, wa. rewrite NONE by (rewrite L in Hi; lia).
  apply rom_bytes_b_sound; [exact IB| exact Hi].
Qed.

Lemma img_ok0_intro : forall m, mem_inv rsegs m ->
  (forall i, IMG0_LO <= i < IMG0_HI -> m (Z_to_bv 64 i) = None) -> img_ok0 m.
Proof.
  intros m MI NONE. unfold IMG0_LO, IMG0_HI in NONE.
  unfold img_ok0.
  repeat (lazymatch goal with |- ro_cells _ _ _ _ => fail | |- _ /\ _ => split end);
    (apply ro_cells_of_image;
     [ intros i Hi; apply NONE;
       cbn [cells_size csize Nat.add mtab_cells tbl_bom tbl_attr_include tbl_esi tbl_starttag vepvars0 length] in Hi;
       unfold GOT_vct, GOT_memset, GOT_vsc, GOT_cp, GOT_ssp, VEPVARS0, TBL_bom, TBL_attr_include, TBL_esi, TBL_starttag in Hi; lia
     | cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity
     | vm_compute; reflexivity
     | unfold GOT_vct, GOT_memset, GOT_vsc, GOT_cp, GOT_ssp, VEPVARS0, TBL_bom, TBL_attr_include, TBL_esi, TBL_starttag; lia
     | cbn [cells_size csize Nat.add mtab_cells tbl_bom tbl_attr_include tbl_esi tbl_starttag vepvars0 length];
       unfold GOT_vct, GOT_memset, GOT_vsc, GOT_cp, GOT_ssp, VEPVARS0, TBL_bom, TBL_attr_include, TBL_esi, TBL_starttag; lia ]).
Qed.

(* [comment removed for export] *)
Definition wr_ok_b (a : Z) (n : nat) : bool :=
  forallb (fun i => match find_segment rsegs (a + Z.of_nat i) 1 with
                    | Some seg => seg_writable seg &&
                                  match segment_byte_at (seg_bytes seg) (Z.to_N (a + Z.of_nat i - Z.of_N (seg_base seg))) with
                                  | Some _ => true | None => false end
                    | None => false end) (seq 0 n).

Lemma wr_at_of_b : forall M a n, 0 <= a -> a + Z.of_nat n <= 2^64 -> wr_ok_b a n = true -> wr_at rsegs M a (Z.of_nat n).
Proof.
  intros M a n H0 H1 Hb. split; [lia|]. split; [lia|]. intros i Hi.
  unfold wr_ok_b in Hb. rewrite forallb_forall in Hb.
  specialize (Hb (Z.to_nat i) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in Hb by lia.
  unfold wview, wa. destruct (M (Z_to_bv 64 (a + i))); [discriminate|].
  rewrite unsigned_lit by lia.
  destruct (find_segment rsegs (a + i) 1) as [seg|]; [|discriminate].
  apply andb_prop in Hb. destruct Hb as [W B]. rewrite W.
  destruct (segment_byte_at (seg_bytes seg) (Z.to_N (a + i - Z.of_N (seg_base seg)))); [discriminate| discriminate].
Qed.

(* [comment removed for export] *)
Definition ov_bytes (M : mem) (a : Z) (rom : list byte) : list byte :=
  map (fun i => match M (Z_to_bv 64 (a + Z.of_nat i)) with Some b => b | None => nth i rom (Z_to_bv 8 0) end) (seq 0 (length rom)).
Lemma ov_bytes_length : forall M a rom, length (ov_bytes M a rom) = length rom.
Proof. intros. unfold ov_bytes. rewrite length_map, length_seq. reflexivity. Qed.

Lemma bytes_at_ov : forall M a rom,
  0 <= a -> a + Z.of_nat (length rom) <= 2^64 -> rom_bytes_b a rom = true ->
  bytes_at rsegs M a (ov_bytes M a rom).
Proof.
  intros M a rom H0 H1 RB. split; [lia|]. split; [rewrite ov_bytes_length; lia|].
  intros i Hi. rewrite ov_bytes_length in Hi. unfold mrd, wa, ov_bytes.
  rewrite nth_error_map, (nth_error_nth' (seq 0 (length rom)) 0%nat) by (rewrite length_seq; lia).
  rewrite seq_nth by lia. cbn [option_map Nat.add].
  destruct (M (Z_to_bv 64 (a + Z.of_nat i))) as [b|]; [reflexivity|].
  pose proof (rom_bytes_b_sound rom a i RB Hi) as E. unfold wa in E. rewrite E. apply nth_error_nth'. exact Hi.
Qed.

Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs Hl. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (bytes_le_to_Z_nonneg bs) as H0. pose proof (bytes_le_to_Z_bound bs) as H1. rewrite Hl in H1.
  change (256 ^ Z.of_nat 8)%Z with 18446744073709551616%Z in H1.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z.
  rewrite Z.mod_small by lia. rewrite <- Hl. apply Z_to_le_bytes_roundtrip.
Qed.

Lemma rw_C8_any : forall M a, 0 <= a -> a + 8 <= 2^64 ->
  rom_bytes_b a (repeat (Z_to_bv 8 0) 8) = true -> wr_ok_b a 8 = true ->
  exists w, rw_cells rsegs M a [C8 w].
Proof.
  intros M a H0 H1 RB WB. exists (le_bytes_to_word (ov_bytes M a (repeat (Z_to_bv 8 0) 8))). split.
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    rewrite le8_of_bytes by (rewrite ov_bytes_length; reflexivity).
    apply bytes_at_ov; [lia| cbn; lia| exact RB].
  - cbn [cells_size csize]. apply (wr_at_of_b M a 8); [lia| lia| exact WB].
Qed.

Lemma Z_to_le_bytes_firstn : forall n k z, Z_to_le_bytes n z = firstn n (Z_to_le_bytes (n + k) z).
Proof. induction n as [|n IH]; intros k z; cbn; [reflexivity|]. f_equal. apply IH. Qed.

Lemma le4_of_bytes4 : forall bs : list byte, length bs = 4%nat ->
  Z_to_le_bytes 4 (bv_unsigned (le_bytes_to_word (bs ++ repeat (Z_to_bv 8 0) 4))) = bs.
Proof.
  intros bs Hl.
  pose proof (le8_of_bytes (bs ++ repeat (Z_to_bv 8 0) 4) ltac:(rewrite length_app, Hl; reflexivity)) as E8.
  unfold le8, word_to_le_bytes in E8.
  rewrite (Z_to_le_bytes_firstn 4 4). cbn [Nat.add]. rewrite E8.
  rewrite firstn_app, Hl, Nat.sub_diag, firstn_O, app_nil_r. apply firstn_all2. lia.
Qed.

Lemma rw_errno_any : forall M, exists e, rw_cells rsegs M 0x420b4 [C4 e].
Proof.
  intros M. exists (le_bytes_to_word (ov_bytes M 0x420b4 (repeat (Z_to_bv 8 0) 4) ++ repeat (Z_to_bv 8 0) 4)). split.
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    unfold le4, word_to_le_bytes. rewrite le4_of_bytes4 by (apply ov_bytes_length).
    apply bytes_at_ov; [lia| cbn; lia| vm_compute; reflexivity].
  - cbn [cells_size csize]. apply (wr_at_of_b M 0x420b4 4); [lia| lia| vm_compute; reflexivity].
Qed.

Lemma rw_bss_any : forall M, exists v1 v2, rw_cells rsegs M 0x41830 [C8 v1; C8 v2].
Proof.
  intros M.
  destruct (rw_C8_any M 0x41830 ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as [v1 R1].
  destruct (rw_C8_any M 0x41838 ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as [v2 R2].
  exists v1, v2. change [C8 v1; C8 v2] with ([C8 v1] ++ [C8 v2]).
  apply (proj2 (CellsX.rw_cells_app rsegs M 0x41830 [C8 v1] [C8 v2])). split; [exact R1| exact R2].
Qed.

Lemma rw_guard_any : forall M, exists g, rw_cells rsegs M 0x623c8 [C8 g].
Proof. intros M. apply (rw_C8_any M 0x623c8); [lia| lia| vm_compute; reflexivity| vm_compute; reflexivity]. Qed.
