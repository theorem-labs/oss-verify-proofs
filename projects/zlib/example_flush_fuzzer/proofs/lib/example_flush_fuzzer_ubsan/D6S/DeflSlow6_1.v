(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import
  SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux DSLayout ZSLayout FillWinMem TreeMem BitsModel BitsModel2
  RomRead TreesRod FlushBlockModel BitsLib.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import
  ZIface DeflateState Trees TreeModel SendModel DeflateLz DeflateBlk LmatchModel FillWinModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Segs6 DS6 Callee6 TreesRod6 TreesApi6 DeflBlkApi6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


Lemma Z_to_le_bytes_mod_eq : forall n a b,
  a mod 2 ^ (8 * Z.of_nat n) = b mod 2 ^ (8 * Z.of_nat n) -> Z_to_le_bytes n a = Z_to_le_bytes n b.
Proof.
  intros n a b E. rewrite <- (SymExec.Z_to_le_bytes_mod n a), <- (SymExec.Z_to_le_bytes_mod n b), E. reflexivity.
Qed.

Lemma cells_ext' : forall segs m P st w n f g,
  cells segs m P st w n f -> (forall i, 0 <= i < n -> f i = g i) -> cells segs m P st w n g.
Proof. intros segs m P st w n f g H E i Hi. rewrite <- (E i Hi). exact (H i Hi). Qed.

Lemma cells16_set : forall segs m P (a : arr) i v v',
  cells segs m P 2 2 (arr_len a) (arr_get a) -> 0 <= i < arr_len a -> 0 <= P -> P + 2 * arr_len a <= 2 ^ 64 ->
  v' mod 2 ^ 16 = v mod 2 ^ 16 ->
  cells segs (wbytes m (zw (P + 2 * i)) (Z_to_le_bytes 2 v)) P 2 2 (arr_len (arr_set a i v')) (arr_get (arr_set a i v')).
Proof.
  intros segs m P a i v v' Hc Hi HP HPn Ev.
  rewrite (Z_to_le_bytes_mod_eq 2 v v') by (change (2 ^ (8 * Z.of_nat 2)) with (2 ^ 16); symmetry; exact Ev).
  pose proof (cells_write_cell segs m P 2 2 (arr_len a) (arr_get a) i v' Hc ltac:(cbn; lia) Hi HP HPn) as H.
  rewrite arr_len_set. refine (cells_ext' _ _ _ _ _ _ _ _ H _). intros j Hj. cbn beta.
  rewrite arr_get_set. unfold arr_inb.
  destruct (Z.eqb_spec i j), (Z.eqb_spec j i), (Z.leb_spec 0 i), (Z.ltb_spec i (arr_len a));
    cbn [andb]; subst; try reflexivity; lia.
Qed.


Lemma keeps_prev : keeps ds_prev true true.
Proof. constructor; intros; try match goal with tt : tree_id |- _ => destruct tt end; match goal with ss : deflate_state |- _ => destruct ss; reflexivity end. Qed.
Lemma keeps_head : keeps ds_head true true.
Proof. constructor; intros; try match goal with tt : tree_id |- _ => destruct tt end; match goal with ss : deflate_state |- _ => destruct ss; reflexivity end. Qed.
Lemma keeps_hash_size : keeps ds_hash_size true true.
Proof. constructor; intros; try match goal with tt : tree_id |- _ => destruct tt end; match goal with ss : deflate_state |- _ => destruct ss; reflexivity end. Qed.

Definition cs_io (c : cstrm) := (cs_input c, cs_next_in c, cs_avail_in c, cs_out_rev c, cs_avail_out c, cs_total_in c, cs_total_out c, cs_msg c, cs_adler c).
Definition ds_io (s : deflate_state) := cs_io (ds_strm s).
Lemma keeps_io : keeps ds_io true true.
Proof. constructor; intros; try match goal with tt : tree_id |- _ => destruct tt end; match goal with ss : deflate_state |- _ => destruct ss; reflexivity end. Qed.

Definition ds_sizes (s : deflate_state) := (ds_w_size s, ds_hash_size s, ds_lit_bufsize s).
Lemma keeps_sizes : keeps ds_sizes true true.
Proof. constructor; intros; try match goal with tt : tree_id |- _ => destruct tt end; match goal with ss : deflate_state |- _ => destruct ss; reflexivity end. Qed.

Lemma tfb_sizes : forall s buf len last, ds_sizes (tr_flush_block s buf len last) = ds_sizes s.
Proof. intros. rewrite (k_tr_flush_block ds_sizes keeps_sizes). unfold tfb_X0. destruct (_ && _); [destruct s|]; reflexivity. Qed.
Lemma tfb_window : forall s buf len last, ds_window (tr_flush_block s buf len last) = ds_window s.
Proof. exact tr_flush_block_window. Qed.
Lemma tfb_prev : forall s buf len last, ds_prev (tr_flush_block s buf len last) = ds_prev s.
Proof. intros. rewrite (k_tr_flush_block ds_prev keeps_prev). unfold tfb_X0. destruct (_ && _); [destruct s|]; reflexivity. Qed.
Lemma tfb_head : forall s buf len last, ds_head (tr_flush_block s buf len last) = ds_head s.
Proof. intros. rewrite (k_tr_flush_block ds_head keeps_head). unfold tfb_X0. destruct (_ && _); [destruct s|]; reflexivity. Qed.
Lemma tfb_io : forall s buf len last, ds_io (tr_flush_block s buf len last) = ds_io s.
Proof.
  intros. rewrite (k_tr_flush_block ds_io keeps_io). unfold tfb_X0. destruct (_ && _); [|reflexivity].
  unfold ds_io. rewrite set_strm_strm. destruct (ds_strm s); reflexivity.
Qed.

Lemma tfb_strm_eq : forall s buf len last,
  ds_strm (tr_flush_block s buf len last) = cset_data_type (ds_strm s) (cs_data_type (ds_strm (tr_flush_block s buf len last))).
Proof.
  intros. pose proof (tfb_io s buf len last) as E. unfold ds_io, cs_io in E.
  destruct (ds_strm (tr_flush_block s buf len last)), (ds_strm s). cbn in E |- *. unfold cset_data_type. cbn. congruence.
Qed.

Lemma zsl_vals_data_type : forall zp S st v, list_upd (zsl_vals zp S st) 11 v = zsl_vals zp S (cset_data_type st v).
Proof. intros zp S st v. destruct st; reflexivity. Qed.

Lemma tr_flush_bits_cases : forall s,
  tr_flush_bits s = s
  \/ tr_flush_bits s = set_bi_valid (set_bi_buf (put_byte s (ds_bi_buf s)) (Z.shiftr (ds_bi_buf s) 8)) (ds_bi_valid s - 8)
  \/ tr_flush_bits s = set_bi_valid (set_bi_buf (put_byte (put_byte s (Z.land (ds_bi_buf s) 255)) (Z.shiftr (wrap16 (ds_bi_buf s)) 8)) 0) 0.
Proof.
  intros s. unfold tr_flush_bits, bi_flush, put_short.
  destruct (ds_bi_valid s =? 16); [right; right; reflexivity|].
  destruct (8 <=? ds_bi_valid s); [right; left; reflexivity | left; reflexivity].
Qed.

Definition ds_nobits (s : deflate_state) :=
  (ds_window s, ds_prev s, ds_head s, ds_strm s, ds_sizes s, ds_pending_out s, arr_len (ds_pending_buf s)).

Lemma tr_flush_bits_nobits : forall s, ds_nobits (tr_flush_bits s) = ds_nobits s.
Proof.
  intros s. destruct (tr_flush_bits_cases s) as [E|[E|E]]; rewrite E; [reflexivity| |];
    unfold ds_nobits, put_byte; dsred; unfold ds_sizes; dsred; rewrite ?arr_len_set; reflexivity.
Qed.


Record DWF (ds : deflate_state) : Prop := {
  wf_wlen : arr_len (ds_window ds) = 2 * ds_w_size ds;
  wf_plen : arr_len (ds_prev ds) = ds_w_size ds;
  wf_hlen : arr_len (ds_head ds) = ds_hash_size ds;
  wf_blen : arr_len (ds_pending_buf ds) = ds_lit_bufsize ds * 4;
  wf_lbs : 1 <= ds_lit_bufsize ds < 2 ^ 16;
  wf_wsz : 512 <= ds_w_size ds <= 32768;
  wf_hsz : 1 <= ds_hash_size ds <= 65536;
  wf_ao : 0 <= cs_avail_out (ds_strm ds) < 2 ^ 32 }.


Record DSH (ROM : (word -> option byte) -> Prop) (mem : word -> option byte) (S : Z) (p : ds_ptrs) (zp : zs_ptrs)
           (ds : deflate_state) (flush : Z) (ra : word) (sp : Z) : Prop := {
  dsh_L : ZRH6 DSLOW_FRAME6 mem S sp p zp ds;
  dsh_ret : ret_ok ra;
  dsh_zr : ZR6 mem S p zp ds;
  dsh_flush : 0 <= flush <= 5;
  dsh_wf : DWF ds;
  dsh_rom : ROM mem;
  dsh_roml : rom_local6 ROM }.

Section Walk.
Variable ROM : (word -> option byte) -> Prop.
Variables (mem : word -> option byte) (S : Z) (p : ds_ptrs) (zp : zs_ptrs) (ds : deflate_state) (flush : Z) (ra : word) (sp : Z).
Local Abbreviation W := (p_window p).
Local Abbreviation PV := (p_prev p).
Local Abbreviation HD := (p_head p).
Local Abbreviation PB := (p_pending_buf p).
Local Abbreviation strm := (p_strm p).
Local Abbreviation INP := (zp_in zp).
Local Abbreviation OUTB := (zp_out zp).
Local Abbreviation ws := (ds_w_size ds).
Local Abbreviation hs := (ds_hash_size ds).
Local Abbreviation lbs := (ds_lit_bufsize ds).
Local Abbreviation PBL := (ds_lit_bufsize ds * 4).
Local Abbreviation ILEN := (arr_len (cs_input (ds_strm ds))).
Local Abbreviation OLEN0 := (Z.of_nat (length (cs_out_rev (ds_strm ds)))).
Local Abbreviation AV0 := (cs_avail_out (ds_strm ds)).
Local Abbreviation SP := (sp - 128).
Hypothesis HH : DSH ROM mem S p zp ds flush ra sp.

Let HL : ZRH6 DSLOW_FRAME6 mem S sp p zp ds := dsh_L _ _ _ _ _ _ _ _ _ HH.
Let HWF : DWF ds := dsh_wf _ _ _ _ _ _ _ _ _ HH.
Let HRL : rom_local6 ROM := dsh_roml _ _ _ _ _ _ _ _ _ HH.

Definition Fd : franges := ZRF DSLOW_FRAME6 S sp p zp ds.
Definition GD : franges := (sp - 336, 208) :: tl Fd.
Definition GDo (st : cstrm) : franges :=
  [(sp - 336, 208); (S, ds6_SIZE); (W, 2 * ws); (PV, 2 * ws); (HD, 2 * hs); (PB, PBL); (strm, zsl_SIZE);
   (OUTB, Z.of_nat (length (cs_out_rev st)))].

Local Abbreviation BRm := (BR s6_segs 168672 168704 168736 Fd mem S p PBL).


Lemma region_facts :
  336 <= sp <= 2 ^ 63
  /\ (0 <= S /\ S + 5968 <= 2 ^ 63) /\ (0 < W /\ W + 2 * ws <= 2 ^ 63)
  /\ (0 <= PV /\ PV + 2 * ws <= 2 ^ 63) /\ (0 <= HD /\ HD + 2 * hs <= 2 ^ 63)
  /\ (0 <= PB /\ PB + PBL <= 2 ^ 63) /\ (0 <= strm /\ strm + 112 <= 2 ^ 63)
  /\ (0 <= OUTB /\ OUTB + (OLEN0 + AV0) <= 2 ^ 63)
  /\ (0 <= INP /\ INP + ILEN < 2 ^ 63).
Proof.
  pose proof (zrh_sp _ _ _ _ _ _ _ HL) as Hsp. pose proof (zrh_W _ _ _ _ _ _ _ HL) as HW0. pose proof (zrh_in _ _ _ _ _ _ _ HL) as HI.
  pose proof (zrh_rng _ _ _ _ _ _ _ HL) as HR. unfold zr_regions, DSLOW_FRAME6, ds6_SIZE, zsl_SIZE in *.
  repeat match type of HR with Forall _ (_ :: _) => apply Forall_cons_iff in HR; destruct HR as [? HR]; cbn [fst snd] in * end.
  repeat split; lia.
Qed.

Lemma apart_ij : forall i j, (i < j)%nat -> (j < 9)%nat ->
  apart (nth i (zr_regions DSLOW_FRAME6 S sp p zp ds) (0, 0)) (nth j (zr_regions DSLOW_FRAME6 S sp p zp ds) (0, 0)).
Proof. intros i j Hij Hj. apply apart_get; [exact (zrh_apart _ _ _ _ _ _ _ HL) | exact Hij | cbn; lia]. Qed.

Ltac apartF i j H := pose proof (apart_ij i j ltac:(lia) ltac:(lia)) as H; unfold apart, zr_regions in H; cbn [nth fst snd] in H; unfold ds6_SIZE, zsl_SIZE, DSLOW_FRAME6 in H.

Lemma mapped_i : forall i, (i < 8)%nat ->
  mapped mem (fst (nth i (ZRF DSLOW_FRAME6 S sp p zp ds) (0, 0))) (snd (nth i (ZRF DSLOW_FRAME6 S sp p zp ds) (0, 0))).
Proof.
  intros i Hi. pose proof (zrh_map _ _ _ _ _ _ _ HL) as HM. unfold ZRF in HM |- *.
  do 8 (destruct i as [|i]; [apply Forall_inv in HM; exact HM | apply Forall_inv_tail in HM]). lia.
Qed.
Ltac mappedF i H := pose proof (mapped_i i ltac:(lia)) as H; unfold ZRF in H; cbn [nth fst snd] in H; unfold ds6_SIZE, zsl_SIZE, DSLOW_FRAME6 in H.

Lemma BRH_d : BRH Fd S p PBL.
Proof.
  pose proof region_facts as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN). apartF 1%nat 5%nat A15.
  unfold BRH, Fd, ZRF, ds6_SIZE, dsl_SIZE. split; [lia|]. split; [lia|]. split; [lia|].
  split; [apply sub_franges_later; apply sub_franges_here; unfold ds6_SIZE, dsl_SIZE; lia|].
  split; [apply sub_franges_later; apply sub_franges_here; unfold ds6_SIZE, dsl_SIZE; lia|].
  split; [apply sub_franges_later; apply sub_franges_here; unfold ds6_SIZE, dsl_SIZE; lia|].
  do 5 apply sub_franges_later. apply sub_franges_here; lia.
Qed.

Lemma HFS_d : sub_franges Fd S ds6_SIZE.
Proof. unfold Fd, ZRF. apply sub_franges_later; apply sub_franges_here; lia. Qed.

Lemma in_Fd : forall x,
  (sp - 336 <= x < sp \/ S <= x < S + 5968 \/ W <= x < W + 2 * ws \/ PV <= x < PV + 2 * ws \/ HD <= x < HD + 2 * hs
   \/ PB <= x < PB + PBL \/ strm <= x < strm + 112 \/ OUTB <= x < OUTB + (OLEN0 + AV0)) ->
  in_franges Fd x.
Proof. intros x Hx. unfold Fd, ZRF, ds6_SIZE, zsl_SIZE, DSLOW_FRAME6. cbn [in_franges]. lia. Qed.

Lemma in_GD : forall x,
  (sp - 336 <= x < sp - 128 \/ S <= x < S + 5968 \/ W <= x < W + 2 * ws \/ PV <= x < PV + 2 * ws \/ HD <= x < HD + 2 * hs
   \/ PB <= x < PB + PBL \/ strm <= x < strm + 112 \/ OUTB <= x < OUTB + (OLEN0 + AV0)) ->
  in_franges GD x.
Proof. intros x Hx. unfold GD, Fd, ZRF, ds6_SIZE, zsl_SIZE, DSLOW_FRAME6. cbn [in_franges tl]. lia. Qed.

Lemma GD_Fd : forall x, in_franges GD x -> in_franges Fd x.
Proof. intros x Hx. unfold GD, Fd, ZRF, ds6_SIZE, zsl_SIZE, DSLOW_FRAME6 in *. cbn [in_franges tl] in *. lia. Qed.

Lemma in_GDo : forall st x,
  (sp - 336 <= x < sp - 128 \/ S <= x < S + 5968 \/ W <= x < W + 2 * ws \/ PV <= x < PV + 2 * ws \/ HD <= x < HD + 2 * hs
   \/ PB <= x < PB + PBL \/ strm <= x < strm + 112 \/ OUTB <= x < OUTB + Z.of_nat (length (cs_out_rev st))) ->
  in_franges (GDo st) x.
Proof. intros st x Hx. unfold GDo, ds6_SIZE, zsl_SIZE. cbn [in_franges]. lia. Qed.

Lemma GDo_GD : forall st x, in_franges (GDo st) x -> Z.of_nat (length (cs_out_rev st)) <= OLEN0 + AV0 -> in_franges GD x.
Proof. intros st x Hx Hle. unfold GDo, GD, Fd, ZRF, ds6_SIZE, zsl_SIZE, DSLOW_FRAME6 in *. cbn [in_franges tl] in *. lia. Qed.

Lemma GDo_mono : forall st st' x, in_franges (GDo st) x ->
  Z.of_nat (length (cs_out_rev st)) <= Z.of_nat (length (cs_out_rev st')) -> in_franges (GDo st') x.
Proof. intros st st' x Hx Hle. unfold GDo, ds6_SIZE, zsl_SIZE in *. cbn [in_franges] in *. lia. Qed.

Lemma out_GD : forall x, in_franges GD x -> ~ (sp - 128 <= x < sp).
Proof.
  intros x Hx. pose proof region_facts as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN).
  apartF 0%nat 1%nat A01. apartF 0%nat 2%nat A02. apartF 0%nat 3%nat A03. apartF 0%nat 4%nat A04.
  apartF 0%nat 5%nat A05. apartF 0%nat 6%nat A06. apartF 0%nat 7%nat A07.
  unfold GD, Fd, ZRF, ds6_SIZE, zsl_SIZE, DSLOW_FRAME6 in Hx. cbn [in_franges tl] in Hx. lia.
Qed.


Lemma GD_img : forall x, in_franges GD x -> IMG6_LO <= x < IMG6_HI -> False.
Proof. intros x Hx Hi. exact (zrh_img _ _ _ _ _ _ _ HL x (GD_Fd x Hx) Hi). Qed.

Lemma GDo_img : forall st x, in_franges (GDo st) x -> Z.of_nat (length (cs_out_rev st)) <= OLEN0 + AV0 ->
  IMG6_LO <= x < IMG6_HI -> False.
Proof. intros st x Hx Hle Hi. exact (GD_img x (GDo_GD st x Hx Hle) Hi). Qed.

Lemma out_GDo : forall st x, in_franges (GDo st) x -> Z.of_nat (length (cs_out_rev st)) <= OLEN0 + AV0 -> ~ (sp - 128 <= x < sp).
Proof. intros st x Hx Hle. exact (out_GD x (GDo_GD st x Hx Hle)). Qed.

Definition CST (w pv hd : arr) (st : cstrm) : Prop :=
  arr_len w = 2 * ws /\ arr_len pv = ws /\ arr_len hd = hs /\ cs_input st = cs_input (ds_strm ds)
  /\ Z.of_nat (length (cs_out_rev st)) + cs_avail_out st = OLEN0 + AV0
  /\ 0 <= cs_avail_out st /\ OLEN0 <= Z.of_nat (length (cs_out_rev st)).

Definition RZmisc (m1 m : word -> option byte) (st : cstrm) : Prop :=
  rod6 m /\ ROM m /\ agree_out (GDo st) m1 m /\ mapped m (sp - 336) 336 /\ (forall x, mem x <> None -> m x <> None).

Definition RZ (m1 m : word -> option byte) (w pv hd : arr) (st : cstrm) : Prop :=
  cells s6_segs m W 1 1 (arr_len w) (arr_get w)
  /\ cells s6_segs m PV 2 2 (arr_len pv) (arr_get pv)
  /\ cells s6_segs m HD 2 2 (arr_len hd) (arr_get hd)
  /\ zsl_scalars s6_segs m strm zp S st /\ zsl_input s6_segs m zp st /\ zsl_outA m zp st
  /\ RZmisc m1 m st
  /\ CST w pv hd st.

Definition DI (m1 m : word -> option byte) (X : deflate_state) : Prop :=
  BRm m X /\ RZ m1 m (ds_window X) (ds_prev X) (ds_head X) (ds_strm X)
  /\ (ds_w_size X = ws /\ ds_hash_size X = hs /\ ds_lit_bufsize X = lbs).


Lemma RZmisc_st : forall m1 m (b : Z) bs st,
  RZmisc m1 m st ->
  0 <= b -> b + Z.of_nat (length bs) <= 2 ^ 64 ->
  sub_franges (GDo st) b (Z.of_nat (length bs)) ->
  Z.of_nat (length (cs_out_rev st)) <= OLEN0 + AV0 ->
  (forall x : word, b <= bv_unsigned x < b + Z.of_nat (length bs) -> m x <> None) ->
  RZmisc m1 (wbytes m (zw b) bs) st.
Proof.
  intros m1 m b bs st (HRC & HRD & HAG & MF & HGR) Hb0 Hb1 HG Hol Hm. unfold RZmisc.
  split; [split; [apply (trees_rod_clear_wr R6 _ _ (proj1 HRC)) | apply (rom_clear_wr _ _ _ _ (proj2 HRC))];
         (apply wr_ok_wbytes; [apply wr_ok_refl | exact Hm | lia | lia])|].
  split.
  { apply (HRL m _ HRD). intros x Hx.
    assert (Hag1 : agree_out [(b, Z.of_nat (length bs))] m (wbytes m (zw b) bs)).
    { apply agree_out_wbytes; try lia; [apply agree_out_refl | apply sub_franges_here; lia]. }
    apply Hag1. intros Hin. cbn in Hin. apply (GDo_img st (bv_unsigned x)); [apply HG; cbn; lia | exact Hol | exact Hx]. }
  split; [apply agree_out_wbytes; try lia; [exact HAG | exact HG]|].
  split; [apply mapped_wbytes; exact MF|].
  intros x Hx; apply wbytes_grows; exact (HGR x Hx).
Qed.

Lemma RZmisc_mono : forall m1 m st st',
  RZmisc m1 m st -> Z.of_nat (length (cs_out_rev st)) <= Z.of_nat (length (cs_out_rev st')) -> RZmisc m1 m st'.
Proof.
  intros m1 m st st' (HRC & HRD & HAG & MF & HGR) Hle. unfold RZmisc.
  split; [exact HRC|]. split; [exact HRD|]. split; [| split; [exact MF | exact HGR]].
  intros x Hx. apply HAG. intros Hin. apply Hx. exact (GDo_mono st st' _ Hin Hle).
Qed.

Lemma RZmisc_eqo : forall m1 m st st',
  RZmisc m1 m st -> cs_out_rev st' = cs_out_rev st -> RZmisc m1 m st'.
Proof. intros m1 m st st' H E. apply (RZmisc_mono m1 m st st' H). rewrite E. lia. Qed.

Lemma RZ_st_S : forall m1 m w pv hd st (b : Z) bs X,
  RZ m1 m w pv hd st -> BRm m X ->
  S <= b -> b + Z.of_nat (length bs) <= S + 5968 ->
  RZ m1 (wbytes m (zw b) bs) w pv hd st.
Proof.
  intros m1 m w pv hd st b bs X HR HB Hb0 Hb1.
  pose proof HR as (Cw & Cp & Ch & Zs & Zi & Zo & HM & HC).
  pose proof region_facts as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN).
  pose proof HC as (Lw & Lp & Lh & Ein & Eout & Hao & Hol).
  unfold RZ.
  split; [apartF 1%nat 2%nat A2; apply cells_write_other; try lia; exact Cw|].
  split; [apartF 1%nat 3%nat A3; apply cells_write_other; try lia; exact Cp|].
  split; [apartF 1%nat 4%nat A4; apply cells_write_other; try lia; exact Ch|].
  split; [apartF 1%nat 6%nat A5; apply zsl_scalars_frame; unfold zsl_SIZE; try lia; exact Zs|].
  split; [apartF 1%nat 8%nat A8; unfold zsl_input in *; rewrite Ein in *; apply cells_write_other; try lia; exact Zi|].
  split; [apartF 1%nat 7%nat A6; unfold zsl_outA in *; apply cells_write_other; try lia; exact Zo|].
  split; [| exact HC].
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & _ & _ & MS & _ & _).
  apply RZmisc_st; [exact HM | lia | lia | intros x Hx; apply in_GDo; lia | lia | intros x Hx; apply MS; unfold ds6_SIZE, dsl_SIZE; lia].
Qed.

Lemma RZ_st_PB : forall m1 m w pv hd st (b : Z) bs X,
  RZ m1 m w pv hd st -> BRm m X ->
  PB <= b -> b + Z.of_nat (length bs) <= PB + PBL ->
  RZ m1 (wbytes m (zw b) bs) w pv hd st.
Proof.
  intros m1 m w pv hd st b bs X HR HB Hb0 Hb1.
  pose proof HR as (Cw & Cp & Ch & Zs & Zi & Zo & HM & HC).
  pose proof region_facts as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN).
  pose proof HC as (Lw & Lp & Lh & Ein & Eout & Hao & Hol).
  unfold RZ.
  split; [apartF 2%nat 5%nat A2; apply cells_write_other; try lia; exact Cw|].
  split; [apartF 3%nat 5%nat A3; apply cells_write_other; try lia; exact Cp|].
  split; [apartF 4%nat 5%nat A4; apply cells_write_other; try lia; exact Ch|].
  split; [apartF 5%nat 6%nat A5; apply zsl_scalars_frame; unfold zsl_SIZE; try lia; exact Zs|].
  split; [apartF 5%nat 8%nat A8; unfold zsl_input in *; rewrite Ein in *; apply cells_write_other; try lia; exact Zi|].
  split; [apartF 5%nat 7%nat A6; unfold zsl_outA in *; apply cells_write_other; try lia; exact Zo|].
  split; [| exact HC].
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & _ & _ & _ & MP & _).
  apply RZmisc_st; [exact HM | lia | lia | intros x Hx; apply in_GDo; lia | lia | intros x Hx; apply MP; lia].
Qed.

Lemma RZ_st_frame : forall m1 m w pv hd st (b : Z) bs,
  RZ m1 m w pv hd st ->
  sp - 336 <= b -> b + Z.of_nat (length bs) <= sp - 128 ->
  RZ m1 (wbytes m (zw b) bs) w pv hd st.
Proof.
  intros m1 m w pv hd st b bs HR Hb0 Hb1.
  pose proof HR as (Cw & Cp & Ch & Zs & Zi & Zo & HM & HC).
  pose proof region_facts as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN).
  pose proof HC as (Lw & Lp & Lh & Ein & Eout & Hao & Hol).
  unfold RZ.
  split; [apartF 0%nat 2%nat A2; apply cells_write_other; try lia; exact Cw|].
  split; [apartF 0%nat 3%nat A3; apply cells_write_other; try lia; exact Cp|].
  split; [apartF 0%nat 4%nat A4; apply cells_write_other; try lia; exact Ch|].
  split; [apartF 0%nat 6%nat A5; apply zsl_scalars_frame; unfold zsl_SIZE; try lia; exact Zs|].
  split; [apartF 0%nat 8%nat A8; unfold zsl_input in *; rewrite Ein in *; apply cells_write_other; try lia; exact Zi|].
  split; [apartF 0%nat 7%nat A6; unfold zsl_outA in *; apply cells_write_other; try lia; exact Zo|].
  split; [| exact HC].
  pose proof HM as (_ & _ & _ & MF & _).
  apply RZmisc_st; [exact HM | lia | lia | intros x Hx; apply in_GDo; lia | lia | intros x Hx; apply MF; lia].
Qed.

Lemma BR_st_far : forall m X (b : Z) bs,
  BRm m X -> 0 <= b -> b + Z.of_nat (length bs) <= 2 ^ 64 ->
  (S + 5968 <= b \/ b + Z.of_nat (length bs) <= S) ->
  (PB + PBL <= b \/ b + Z.of_nat (length bs) <= PB) ->
  sub_franges Fd b (Z.of_nat (length bs)) ->
  BRm (wbytes m (zw b) bs) X.
Proof.
  intros m X b bs HB Hb0 Hb1 DS DP HF.
  apply (BR_st_other s6_segs 168672 168704 168736 Fd mem S p PBL BRH_d m X b bs HB Hb0 Hb1); [unfold ds6_SIZE, dsl_SIZE; exact DS | exact DP | exact HF].
Qed.


Lemma RZ_st_prev : forall m1 m w pv hd st i v v',
  RZ m1 m w pv hd st -> 0 <= i < ws -> v' mod 2 ^ 16 = v mod 2 ^ 16 ->
  RZ m1 (wbytes m (zw (PV + 2 * i)) (Z_to_le_bytes 2 v)) w (arr_set pv i v') hd st.
Proof.
  intros m1 m w pv hd st i v v' HR Hi Ev.
  pose proof HR as (Cw & Cp & Ch & Zs & Zi & Zo & HM & HC).
  pose proof region_facts as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN).
  pose proof HC as (Lw & Lp & Lh & Ein & Eout & Hao & Hol).
  mappedF 3%nat M3. pose proof HM as (_ & _ & _ & _ & HGR).
  unfold RZ. rewrite arr_len_set.
  split; [apartF 2%nat 3%nat A2; apply cells_write_other; rewrite ?length_Z_to_le_bytes; try lia; exact Cw|].
  split; [rewrite <- (arr_len_set pv i v'); apply cells16_set; try lia; try exact Cp; try exact Ev|].
  split; [apartF 3%nat 4%nat A4; apply cells_write_other; rewrite ?length_Z_to_le_bytes; try lia; exact Ch|].
  split; [apartF 3%nat 6%nat A5; apply zsl_scalars_frame; rewrite ?length_Z_to_le_bytes; unfold zsl_SIZE; try lia; exact Zs|].
  split; [apartF 3%nat 8%nat A8; unfold zsl_input in *; rewrite Ein in *; apply cells_write_other; rewrite ?length_Z_to_le_bytes; try lia; exact Zi|].
  split; [apartF 3%nat 7%nat A6; unfold zsl_outA in *; apply cells_write_other; rewrite ?length_Z_to_le_bytes; try lia; exact Zo|].
  split; [| unfold CST in *; rewrite arr_len_set; exact HC].
  apply RZmisc_st; rewrite ?length_Z_to_le_bytes; [exact HM | lia | lia | intros x Hx; apply in_GDo; lia | lia | intros x Hx; apply HGR; apply M3; lia].
Qed.

Lemma RZ_st_head : forall m1 m w pv hd st i v v',
  RZ m1 m w pv hd st -> 0 <= i < hs -> v' mod 2 ^ 16 = v mod 2 ^ 16 ->
  RZ m1 (wbytes m (zw (HD + 2 * i)) (Z_to_le_bytes 2 v)) w pv (arr_set hd i v') st.
Proof.
  intros m1 m w pv hd st i v v' HR Hi Ev.
  pose proof HR as (Cw & Cp & Ch & Zs & Zi & Zo & HM & HC).
  pose proof region_facts as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN).
  pose proof HC as (Lw & Lp & Lh & Ein & Eout & Hao & Hol).
  mappedF 4%nat M4. pose proof HM as (_ & _ & _ & _ & HGR).
  unfold RZ. rewrite arr_len_set.
  split; [apartF 2%nat 4%nat A2; apply cells_write_other; rewrite ?length_Z_to_le_bytes; try lia; exact Cw|].
  split; [apartF 3%nat 4%nat A3; apply cells_write_other; rewrite ?length_Z_to_le_bytes; try lia; exact Cp|].
  split; [rewrite <- (arr_len_set hd i v'); apply cells16_set; try lia; try exact Ch; try exact Ev|].
  split; [apartF 4%nat 6%nat A5; apply zsl_scalars_frame; rewrite ?length_Z_to_le_bytes; unfold zsl_SIZE; try lia; exact Zs|].
  split; [apartF 4%nat 8%nat A8; unfold zsl_input in *; rewrite Ein in *; apply cells_write_other; rewrite ?length_Z_to_le_bytes; try lia; exact Zi|].
  split; [apartF 4%nat 7%nat A6; unfold zsl_outA in *; apply cells_write_other; rewrite ?length_Z_to_le_bytes; try lia; exact Zo|].
  split; [| unfold CST in *; rewrite arr_len_set; exact HC].
  apply RZmisc_st; rewrite ?length_Z_to_le_bytes; [exact HM | lia | lia | intros x Hx; apply in_GDo; lia | lia | intros x Hx; apply HGR; apply M4; lia].
Qed.

Lemma RZ_st_strm : forall m1 m w pv hd st st' (o : Z) (n : nat) v,
  RZ m1 m w pv hd st ->
  zsl_scalars s6_segs (wbytes m (zw (strm + o)) (Z_to_le_bytes n v)) strm zp S st' ->
  cs_input st' = cs_input st -> cs_out_rev st' = cs_out_rev st ->
  Z.of_nat (length (cs_out_rev st')) + cs_avail_out st' = OLEN0 + AV0 -> 0 <= cs_avail_out st' ->
  0 <= o -> o + Z.of_nat n <= 112 ->
  RZ m1 (wbytes m (zw (strm + o)) (Z_to_le_bytes n v)) w pv hd st'.
Proof.
  intros m1 m w pv hd st st' o n v HR Hz' Ein' Eor' Esum' Hao' Ho0 Ho1.
  pose proof HR as (Cw & Cp & Ch & Zs & Zi & Zo & HM & HC).
  pose proof region_facts as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN).
  pose proof HC as (Lw & Lp & Lh & Ein & Eout & Hao & Hol).
  mappedF 6%nat M6. pose proof HM as (_ & _ & _ & _ & HGR).
  unfold RZ.
  split; [apartF 2%nat 6%nat A2; apply cells_write_other; rewrite ?length_Z_to_le_bytes; try lia; exact Cw|].
  split; [apartF 3%nat 6%nat A3; apply cells_write_other; rewrite ?length_Z_to_le_bytes; try lia; exact Cp|].
  split; [apartF 4%nat 6%nat A4; apply cells_write_other; rewrite ?length_Z_to_le_bytes; try lia; exact Ch|].
  split; [exact Hz'|].
  split; [apartF 6%nat 8%nat A8; unfold zsl_input in *; rewrite Ein', Ein in *; apply cells_write_other; rewrite ?length_Z_to_le_bytes; try lia; exact Zi|].
  split; [apartF 6%nat 7%nat A6; unfold zsl_outA, cs_output in *; rewrite Eor'; apply cells_write_other; rewrite ?length_Z_to_le_bytes; try lia; exact Zo|].
  split; [apply (RZmisc_eqo m1 _ st st'); [| exact Eor'];
          apply RZmisc_st; rewrite ?length_Z_to_le_bytes; [exact HM | lia | lia | intros x Hx; apply in_GDo; lia | lia | intros x Hx; apply HGR; apply M6; lia]|].
  unfold CST. rewrite Eor' in Esum'. rewrite Ein', Eor'. repeat (split; [first [assumption | lia]|]). lia.
Qed.

Lemma BR_st_strm : forall m X (o : Z) (n : nat) v,
  BRm m X -> 0 <= o -> o + Z.of_nat n <= 112 ->
  BRm (wbytes m (zw (strm + o)) (Z_to_le_bytes n v)) X.
Proof.
  intros m X o n v HB Ho0 Ho1.
  pose proof region_facts as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN).
  apply BR_st_far; rewrite ?length_Z_to_le_bytes; [exact HB | lia | lia | apartF 1%nat 6%nat A; lia | apartF 5%nat 6%nat A; lia | intros x Hx; apply in_Fd; lia].
Qed.

Lemma BR_st_prev : forall m X i v,
  BRm m X -> 0 <= i < ws -> BRm (wbytes m (zw (PV + 2 * i)) (Z_to_le_bytes 2 v)) X.
Proof.
  intros m X i v HB Hi.
  pose proof region_facts as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN).
  apply BR_st_far; rewrite ?length_Z_to_le_bytes; [exact HB | lia | lia | apartF 1%nat 3%nat A; lia | apartF 3%nat 5%nat A; lia | intros x Hx; apply in_Fd; lia].
Qed.

Lemma BR_st_head : forall m X i v,
  BRm m X -> 0 <= i < hs -> BRm (wbytes m (zw (HD + 2 * i)) (Z_to_le_bytes 2 v)) X.
Proof.
  intros m X i v HB Hi.
  pose proof region_facts as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN).
  apply BR_st_far; rewrite ?length_Z_to_le_bytes; [exact HB | lia | lia | apartF 1%nat 4%nat A; lia | apartF 4%nat 5%nat A; lia | intros x Hx; apply in_Fd; lia].
Qed.

Lemma BR_st_frame : forall m X (b : Z) bs,
  BRm m X -> sp - 336 <= b -> b + Z.of_nat (length bs) <= sp ->
  BRm (wbytes m (zw b) bs) X.
Proof.
  intros m X b bs HB Hb0 Hb1.
  pose proof region_facts as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN).
  apply BR_st_far; [exact HB | lia | lia | apartF 0%nat 1%nat A; lia | apartF 0%nat 5%nat A; lia | intros x Hx; apply in_Fd; lia].
Qed.


Local Ltac other9 A :=
  apply cells_write_other; rewrite ?length_Z_to_le_bytes; try (cbn; lia); exact A.

Local Ltac scalar_head UPD :=
  intros m s v HB; pose proof HB as (A & B & C & D & E & G & H & I & J);
  pose proof BRH_d as (HS & HPB & Hdisj & _); unfold BitsLib.BR, ds6_SIZE, dsl_SIZE in *;
  split; [apply UPD; unfold ds6_SIZE, dsl_SIZE; try lia; exact A|];
  split; [unfold ds6_arrays in *; apply arrays_write_gap; rewrite ?length_Z_to_le_bytes; unfold dsl_SIZE; try (cbn; lia); exact B|];
  split; [exact C|];
  split; [dsred; other9 D|];
  split; [dsred; exact E|];
  split; [apply agree_out_wbytes; rewrite ?length_Z_to_le_bytes; try (cbn; lia); [exact G | intros x Hx; apply HFS_d; cbn in Hx; unfold ds6_SIZE, dsl_SIZE; lia]|];
  split; [apply mapped_wbytes; exact H|]; split; [apply mapped_wbytes; exact I|];
  intros x Hx; apply wbytes_grows; exact (J x Hx).

Lemma BR_st_ins_h : forall m s v, BRm m s -> BRm (wbytes m (zw (S + 128)) (Z_to_le_bytes 4 v)) (set_ins_h s v).
Proof. scalar_head (dsl_upd_ins_h s6_segs 168672 168704 168736). Qed.
Lemma BR_st_block_start : forall m s v, BRm m s -> BRm (wbytes m (zw (S + 152)) (Z_to_le_bytes 8 v)) (set_block_start s v).
Proof. scalar_head (dsl_upd_block_start s6_segs 168672 168704 168736). Qed.
Lemma BR_st_match_length : forall m s v, BRm m s -> BRm (wbytes m (zw (S + 160)) (Z_to_le_bytes 4 v)) (set_match_length s v).
Proof. scalar_head (dsl_upd_match_length s6_segs 168672 168704 168736). Qed.
Lemma BR_st_strstart : forall m s v, BRm m s -> BRm (wbytes m (zw (S + 172)) (Z_to_le_bytes 4 v)) (set_strstart s v).
Proof. scalar_head (dsl_upd_strstart s6_segs 168672 168704 168736). Qed.
Lemma BR_st_lookahead : forall m s v, BRm m s -> BRm (wbytes m (zw (S + 180)) (Z_to_le_bytes 4 v)) (set_lookahead s v).
Proof. scalar_head (dsl_upd_lookahead s6_segs 168672 168704 168736). Qed.
Lemma BR_st_insert : forall m s v, BRm m s -> BRm (wbytes m (zw (S + 5932)) (Z_to_le_bytes 4 v)) (set_insert s v).
Proof. scalar_head (dsl_upd_insert s6_segs 168672 168704 168736). Qed.
Lemma BR_st_prev_length : forall m s v, BRm m s -> BRm (wbytes m (zw (S + 184)) (Z_to_le_bytes 4 v)) (set_prev_length s v).
Proof. scalar_head (dsl_upd_prev_length s6_segs 168672 168704 168736). Qed.
Lemma BR_st_prev_match : forall m s v, BRm m s -> BRm (wbytes m (zw (S + 164)) (Z_to_le_bytes 4 v)) (set_prev_match s v).
Proof. scalar_head (dsl_upd_prev_match s6_segs 168672 168704 168736). Qed.
Lemma BR_st_match_available : forall m s v, BRm m s -> BRm (wbytes m (zw (S + 168)) (Z_to_le_bytes 4 v)) (set_match_available s v).
Proof. scalar_head (dsl_upd_match_available s6_segs 168672 168704 168736). Qed.
Lemma BR_st_sym_next' : forall m s v, BRm m s -> BRm (wbytes m (zw (S + 5900)) (Z_to_le_bytes 4 v)) (set_sym_next s v).
Proof. intros m s v HB. apply (BR_st_sym_next s6_segs 168672 168704 168736 Fd mem S p PBL BRH_d HFS_d). exact HB. Qed.
Lemma BR_st_pending' : forall m s v, BRm m s -> BRm (wbytes m (zw (S + 40)) (Z_to_le_bytes 8 v)) (set_pending s v).
Proof. intros m s v HB. apply (BR_st_pending s6_segs 168672 168704 168736 Fd mem S p PBL BRH_d). exact HB. Qed.

Lemma dsR_upd_pending_out : forall m0 S0 p0 s v,
  ds6_scalars m0 S0 p0 s -> 0 <= S0 -> S0 + ds6_SIZE <= 2 ^ 64 ->
  ds6_scalars (wbytes m0 (zw (S0 + 32)) (Z_to_le_bytes 8 (p_pending_buf p0 + v))) S0 p0 (set_pending_out s v).
Proof.
  intros m0 S0 p0 s v H HS0 HS1. unfold ds6_scalars in *.
  pose proof (fields_write_field s6_segs m0 S0 _ _ ds6_SIZE 4 32 8%nat (p_pending_buf p0 + v) H eq_refl
                ltac:(vm_compute; reflexivity) ds6_layout_within HS0 HS1) as H'.
  replace (ds6_vals (set_pending_out s v) p0 S0) with (list_upd (ds6_vals s p0 S0) 4 (p_pending_buf p0 + v)) by (destruct s; reflexivity).
  exact H'.
Qed.

Lemma BR_st_pending_out : forall m s v, BRm m s -> BRm (wbytes m (zw (S + 32)) (Z_to_le_bytes 8 (PB + v))) (set_pending_out s v).
Proof. scalar_head dsR_upd_pending_out. Qed.

Lemma BR_st_fc' : forall m s t i v,
  BRm m s -> 0 <= i < tsize t ->
  BRm (wbytes m (zw (S + toff t + 4 * i)) (Z_to_le_bytes 2 v)) (set_tree_fc s t (arr_set (tree_fc s t) i (wrap16 v))).
Proof. intros m s t i v HB Hi. apply (BR_st_fc s6_segs 168672 168704 168736 Fd mem S p PBL BRH_d HFS_d); assumption. Qed.

Lemma BR_st_pb' : forall m s (a i c : Z),
  BRm m s -> a = PB + i -> 0 <= i < PBL ->
  BRm (wbytes m (zw a) (Z_to_le_bytes 1 c)) (set_pending_buf s (arr_set (ds_pending_buf s) i (wrap8 c))).
Proof. intros m s a i c HB Ha Hi. apply (BR_st_pb s6_segs 168672 168704 168736 Fd mem S p PBL BRH_d); assumption. Qed.



Local Ltac di_scalar BRL :=
  intros m1 m X v a HDI Ea; subst a; destruct HDI as (HB & HR & HS3); split;
  [ apply BRL; exact HB
  | split; [ dsred; eapply RZ_st_S; [exact HR | exact HB | lia | rewrite length_Z_to_le_bytes; lia] | dsred; exact HS3 ] ].

Lemma DI_st_ins_h : forall m1 m X v a, DI m1 m X -> a = S + 128 -> DI m1 (wbytes m (zw a) (Z_to_le_bytes 4 v)) (set_ins_h X v).
Proof. di_scalar BR_st_ins_h. Qed.
Lemma DI_st_block_start : forall m1 m X v a, DI m1 m X -> a = S + 152 -> DI m1 (wbytes m (zw a) (Z_to_le_bytes 8 v)) (set_block_start X v).
Proof. di_scalar BR_st_block_start. Qed.
Lemma DI_st_match_length : forall m1 m X v a, DI m1 m X -> a = S + 160 -> DI m1 (wbytes m (zw a) (Z_to_le_bytes 4 v)) (set_match_length X v).
Proof. di_scalar BR_st_match_length. Qed.
Lemma DI_st_strstart : forall m1 m X v a, DI m1 m X -> a = S + 172 -> DI m1 (wbytes m (zw a) (Z_to_le_bytes 4 v)) (set_strstart X v).
Proof. di_scalar BR_st_strstart. Qed.
Lemma DI_st_lookahead : forall m1 m X v a, DI m1 m X -> a = S + 180 -> DI m1 (wbytes m (zw a) (Z_to_le_bytes 4 v)) (set_lookahead X v).
Proof. di_scalar BR_st_lookahead. Qed.
Lemma DI_st_insert : forall m1 m X v a, DI m1 m X -> a = S + 5932 -> DI m1 (wbytes m (zw a) (Z_to_le_bytes 4 v)) (set_insert X v).
Proof. di_scalar BR_st_insert. Qed.
Lemma DI_st_prev_length : forall m1 m X v a, DI m1 m X -> a = S + 184 -> DI m1 (wbytes m (zw a) (Z_to_le_bytes 4 v)) (set_prev_length X v).
Proof. di_scalar BR_st_prev_length. Qed.
Lemma DI_st_prev_match : forall m1 m X v a, DI m1 m X -> a = S + 164 -> DI m1 (wbytes m (zw a) (Z_to_le_bytes 4 v)) (set_prev_match X v).
Proof. di_scalar BR_st_prev_match. Qed.
Lemma DI_st_match_available : forall m1 m X v a, DI m1 m X -> a = S + 168 -> DI m1 (wbytes m (zw a) (Z_to_le_bytes 4 v)) (set_match_available X v).
Proof. di_scalar BR_st_match_available. Qed.
Lemma DI_st_sym_next : forall m1 m X v a, DI m1 m X -> a = S + 5900 -> DI m1 (wbytes m (zw a) (Z_to_le_bytes 4 v)) (set_sym_next X v).
Proof. di_scalar BR_st_sym_next'. Qed.
Lemma DI_st_pending : forall m1 m X v a, DI m1 m X -> a = S + 40 -> DI m1 (wbytes m (zw a) (Z_to_le_bytes 8 v)) (set_pending X v).
Proof. di_scalar BR_st_pending'. Qed.
Lemma DI_st_pending_out' : forall m1 m X v a, DI m1 m X -> a = S + 32 -> DI m1 (wbytes m (zw a) (Z_to_le_bytes 8 (PB + v))) (set_pending_out X v).
Proof. di_scalar BR_st_pending_out. Qed.
Lemma DI_st_pending_out : forall m1 m X v a pv, DI m1 m X -> a = S + 32 -> pv = PB + v ->
  DI m1 (wbytes m (zw a) (Z_to_le_bytes 8 pv)) (set_pending_out X v).
Proof. intros m1 m X v a pv HDI Ha ->. apply DI_st_pending_out'; assumption. Qed.

Lemma DI_st_pb : forall m1 m X a i c c', DI m1 m X -> a = PB + i -> 0 <= i < PBL -> c' mod 2 ^ 8 = c mod 2 ^ 8 ->
  DI m1 (wbytes m (zw a) (Z_to_le_bytes 1 c)) (set_pending_buf X (arr_set (ds_pending_buf X) i (wrap8 c'))).
Proof.
  intros m1 m X a i c c' (HB & HR & HS3) Ha Hi Ec.
  rewrite (Z_to_le_bytes_mod_eq 1 c c') by (change (2 ^ (8 * Z.of_nat 1)) with (2 ^ 8); symmetry; exact Ec).
  split; [apply BR_st_pb'; assumption|].
  split; [dsred; subst a; eapply RZ_st_PB; [exact HR | exact HB | lia | rewrite length_Z_to_le_bytes; lia] | dsred; exact HS3].
Qed.

Lemma DI_st_fc : forall m1 m X a t i v v', DI m1 m X -> a = S + toff t + 4 * i -> 0 <= i < tsize t -> v' mod 2 ^ 16 = v mod 2 ^ 16 ->
  DI m1 (wbytes m (zw a) (Z_to_le_bytes 2 v)) (set_tree_fc X t (arr_set (tree_fc X t) i (wrap16 v'))).
Proof.
  intros m1 m X a t i v v' (HB & HR & HS3) Ha Hi Ev.
  rewrite (Z_to_le_bytes_mod_eq 2 v v') by (change (2 ^ (8 * Z.of_nat 2)) with (2 ^ 16); symmetry; exact Ev).
  subst a. pose proof (toff_tsize t) as Ht.
  split; [apply BR_st_fc'; assumption|].
  split; [| destruct t; dsred; exact HS3].
  replace (ds_window (set_tree_fc X t (arr_set (tree_fc X t) i (wrap16 v')))) with (ds_window X) by (destruct t; reflexivity).
  replace (ds_prev (set_tree_fc X t (arr_set (tree_fc X t) i (wrap16 v')))) with (ds_prev X) by (destruct t; reflexivity).
  replace (ds_head (set_tree_fc X t (arr_set (tree_fc X t) i (wrap16 v')))) with (ds_head X) by (destruct t; reflexivity).
  replace (ds_strm (set_tree_fc X t (arr_set (tree_fc X t) i (wrap16 v')))) with (ds_strm X) by (destruct t; reflexivity).
  eapply RZ_st_S; [exact HR | exact HB | lia | rewrite length_Z_to_le_bytes; lia].
Qed.

Lemma DI_st_prev : forall m1 m X a i v v', DI m1 m X -> a = PV + 2 * i -> 0 <= i < ws -> v' mod 2 ^ 16 = v mod 2 ^ 16 ->
  DI m1 (wbytes m (zw a) (Z_to_le_bytes 2 v)) (set_prev X (arr_set (ds_prev X) i v')).
Proof.
  intros m1 m X a i v v' (HB & HR & HS3) -> Hi Ev.
  split; [apply BR_st_prev; assumption|].
  split; [dsred; apply RZ_st_prev; assumption | dsred; exact HS3].
Qed.

Lemma DI_st_head : forall m1 m X a i v v', DI m1 m X -> a = HD + 2 * i -> 0 <= i < hs -> v' mod 2 ^ 16 = v mod 2 ^ 16 ->
  DI m1 (wbytes m (zw a) (Z_to_le_bytes 2 v)) (set_head X (arr_set (ds_head X) i v')).
Proof.
  intros m1 m X a i v v' (HB & HR & HS3) -> Hi Ev.
  split; [apply BR_st_head; assumption|].
  split; [dsred; apply RZ_st_head; assumption | dsred; exact HS3].
Qed.

Lemma DI_st_frame : forall m1 m X (a : Z) bs, DI m1 m X -> sp - 336 <= a -> a + Z.of_nat (length bs) <= sp - 128 ->
  DI m1 (wbytes m (zw a) bs) X.
Proof.
  intros m1 m X a bs (HB & HR & HS3) Ha0 Ha1.
  split; [apply BR_st_frame; [exact HB | lia | lia]|].
  split; [apply RZ_st_frame; assumption | exact HS3].
Qed.

Lemma BR_set_strm' : forall m X c, BRm m X -> BRm m (set_strm X c).
Proof. intros m X c H. exact H. Qed.

Lemma DI_st_strm : forall m1 m X st' (o : Z) (n : nat) v,
  DI m1 m X ->
  zsl_scalars s6_segs (wbytes m (zw (strm + o)) (Z_to_le_bytes n v)) strm zp S st' ->
  cs_input st' = cs_input (ds_strm X) -> cs_out_rev st' = cs_out_rev (ds_strm X) ->
  Z.of_nat (length (cs_out_rev st')) + cs_avail_out st' = OLEN0 + AV0 -> 0 <= cs_avail_out st' ->
  0 <= o -> o + Z.of_nat n <= 112 ->
  DI m1 (wbytes m (zw (strm + o)) (Z_to_le_bytes n v)) (set_strm X st').
Proof.
  intros m1 m X st' o n v (HB & HR & HS3) Hz Ein Eor Esum Hao Ho0 Ho1.
  split; [apply BR_set_strm'; apply BR_st_strm; [exact HB | lia | lia]|].
  split; [dsred; eapply RZ_st_strm; eassumption | dsred; exact HS3].
Qed.




Definition HREGS (R : bvmap 5 word) : Prop :=
  getr R 8 = zw S /\ getr R 2 = zw SP /\ getr R 21 = zw (S + 5888) /\ getr R 22 = zw (S + 212)
  /\ getr R 27 = zw (S + 2504) /\ getr R 20 = zw 65535 /\ getr R 23 = zw 18446744073709551615
  /\ getr R 24 = zw 262 /\ getr R 26 = zw 3.

Lemma HREGS_via : forall R R' L,
  HREGS R -> (forall r : reg, reg_in r L = false -> getr R' r = getr R r) ->
  forallb (fun r : reg => negb (reg_in r L)) [8; 2; 21; 22; 27; 20; 23; 24; 26]%bv = true ->
  HREGS R'.
Proof.
  intros R R' L (A8 & A2 & A21 & A22 & A27 & A20 & A23 & A24 & A26) Hfr Hl.
  cbn [forallb] in Hl. rewrite !Bool.andb_true_iff, !Bool.negb_true_iff in Hl.
  destruct Hl as (X8 & X2 & X21 & X22 & X27 & X20 & X23 & X24 & X26 & _).
  unfold HREGS. rewrite !Hfr by assumption.
  repeat split; assumption.
Qed.

Definition LOC (m : word -> option byte) : Prop :=
  cell s6_segs m (SP + 16) 8 flush /\ cell s6_segs m (SP + 8) 8 4294967295 /\ cell s6_segs m SP 8 4097.

Lemma LOC_DI : forall m1 m X, LOC m1 -> DI m1 m X -> LOC m.
Proof.
  intros m1 m X (L1 & L2 & L3) (_ & (_ & _ & _ & _ & _ & _ & (_ & _ & HAG & _) & (_ & _ & _ & _ & Eout & Hao & Hol)) & _).
  pose proof region_facts as (Hsp & _).
  unfold LOC. split; [|split];
    (eapply (cell_agree_out s6_segs (GDo (ds_strm X)) m1 m); [exact HAG | intros x Hx Hin; exact (out_GDo _ _ Hin ltac:(lia) ltac:(lia)) | lia | cbn; lia | assumption]).
Qed.

Definition HPINS : list (Z * expr) :=
  [(8, EVar 32%nat); (2, EVar 33%nat); (21, EAdd (EVar 32%nat) (ELit 5888)); (22, EAdd (EVar 32%nat) (ELit 212));
   (27, EAdd (EVar 32%nat) (ELit 2504)); (20, ELit 65535); (23, ELit 18446744073709551615); (24, ELit 262); (26, ELit 3)].

Definition HPINST : list (Z * expr) :=
  [(8, EVar 32%nat); (2, EVar 33%nat);
   (20, ELit 65535); (23, ELit 18446744073709551615); (24, ELit 262); (26, ELit 3)].

Inductive skind :=
  | KInsH | KBlockStart | KMatchLength | KStrstart | KLookahead | KInsert | KSymNext | KPending
  | KPrevLength | KPrevMatch | KMatchAvailable
  | KPendingOut (off : Z)
  | KPb (i c' : Z)
  | KFc (t : tree_id) (i v' : Z)
  | KPrev (i v' : Z) | KHead (i v' : Z)
  | KFrame.

Lemma DI_eqst : forall m1 m s1 s2, DI m1 m s1 -> s1 = s2 -> DI m1 m s2.
Proof. intros m1 m s1 s2 H <-. exact H. Qed.

End Walk.



Lemma cell_write_same_at : forall M a b (w : nat) v,
  b = a -> 0 <= a -> a + Z.of_nat w <= 2 ^ 64 ->
  cell s6_segs (wbytes M (zw b) (Z_to_le_bytes w v)) a w v.
Proof. intros M a b w v -> Ha Hw. apply cell_write_same; assumption. Qed.

Lemma pb_read2 : forall segs mem P n (t : arr) i a,
  cells segs mem P 2 2 n (arr_get t) -> 0 <= i < n -> 0 <= arr_get t i < 65536 -> a = P + 2 * i ->
  exists bs, rdn segs mem (zw a) 2 = Some bs /\ bytes_le_to_Z bs = pb t i.
Proof.
  intros segs mem P n t i a Hc Hi Hr ->. unfold pb. rewrite Z.mod_small by exact Hr.
  apply (cells_read_small segs mem P 2 2 n (arr_get t) i Hc Hi). cbn. lia.
Qed.

Lemma szwrap32_u64_le : forall d k, - 2 ^ 31 <= d < 2 ^ 31 -> 0 <= k < 2 ^ 31 ->
  (szwrap 32 d mod 2 ^ 64 <= k <-> wrap32 d <= k).
Proof.
  intros d k Hd Hk. rewrite (szwrap_small 32 d) by lia. rewrite wrap32_mod.
  destruct (Z_lt_le_dec d 0).
  - rewrite <- (Z.mod_add d 1 (2 ^ 64)) by lia. rewrite (Z.mod_small (d + 1 * 2 ^ 64)) by lia.
    rewrite <- (Z.mod_add d 1 (2 ^ 32)) by lia. rewrite (Z.mod_small (d + 1 * 2 ^ 32)) by lia. lia.
  - rewrite !Z.mod_small by lia. lia.
Qed.

Definition dfF (w hd fc fdc : arr) (f : nat) (x : Z) : Z :=
  match f with 0%nat => wb w x | 1%nat => pb hd x | 2%nat => pb fc x | 3%nat => pb fdc x | _ => 0 end.

Lemma dfF_0 : forall w hd fc fdc x, dfF w hd fc fdc 0%nat x = wb w x. Proof. reflexivity. Qed.
Lemma dfF_1 : forall w hd fc fdc x, dfF w hd fc fdc 1%nat x = pb hd x. Proof. reflexivity. Qed.
Lemma dfF_2 : forall w hd fc fdc x, dfF w hd fc fdc 2%nat x = pb fc x. Proof. reflexivity. Qed.
Lemma dfF_3 : forall w hd fc fdc x, dfF w hd fc fdc 3%nat x = pb fdc x. Proof. reflexivity. Qed.

Definition dfFB : list (nat * Z) := [(0%nat, 256); (1%nat, 65536); (2%nat, 65536); (3%nat, 65536)].

Definition dfVB : bounds := [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 6)].

Lemma mm16_8 : forall x, (x mod 65536) mod 256 = x mod 256.
Proof. intros x. change 65536 with (2 ^ 16). change 256 with (2 ^ 8). apply mod_pow2_mod_pow2. lia. Qed.
Lemma mm32_16 : forall x, (x mod 4294967296) mod 65536 = x mod 65536.
Proof. intros x. change 4294967296 with (2 ^ 32). change 65536 with (2 ^ 16). apply mod_pow2_mod_pow2. lia. Qed.
Lemma mm32_8 : forall x, (x mod 4294967296) mod 256 = x mod 256.
Proof. intros x. change 4294967296 with (2 ^ 32). change 256 with (2 ^ 8). apply mod_pow2_mod_pow2. lia. Qed.
Lemma mm16_16 : forall x, (x mod 65536) mod 65536 = x mod 65536.
Proof. intros x. apply Z.mod_mod. lia. Qed.
Lemma mm8_8 : forall x, (x mod 256) mod 256 = x mod 256.
Proof. intros x. apply Z.mod_mod. lia. Qed.
Lemma addm16 : forall a b, (a mod 65536 + b) mod 65536 = (a + b) mod 65536.
Proof. intros. apply Zplus_mod_idemp_l. Qed.
Lemma addm8 : forall a b, (a mod 256 + b) mod 256 = (a + b) mod 256.
Proof. intros. apply Zplus_mod_idemp_l. Qed.
Lemma sxaddm16 : forall a b, (szwrap 16 a + b) mod 65536 = (a + b) mod 65536.
Proof. intros a b. rewrite <- (Zplus_mod_idemp_l (szwrap 16 a)). change 65536 with (2 ^ 16). rewrite szwrap_eqm by lia. apply Zplus_mod_idemp_l. Qed.
Lemma sxaddm8 : forall a b, (szwrap 8 a + b) mod 256 = (a + b) mod 256.
Proof. intros a b. rewrite <- (Zplus_mod_idemp_l (szwrap 8 a)). change 256 with (2 ^ 8). rewrite szwrap_eqm by lia. apply Zplus_mod_idemp_l. Qed.


Definition dsC : cfg :=
  CFG dfFB [] [EVar 1%nat; EVar 35%nat]
      [0x195dc; 0x19600; 0x19610; 0x19620; 0x19644; 0x1964c; 0x196ec; 0x19704; 0x1972c; 0x19730; 0x19738; 0x19850; 0x198c0; 0x198c8; 0x1994c; 0x1997c;
       0x19968; 0x19998; 0x199d8; 0x199a8; 0x199d4; 0x19a5c; 0x19a84; 0x19a5c; 0x19a88; 0x19b0c; 0x19b14;
       0x19b98; 0x19bd4; 0x19c0c; 0x19bf0; 0x19c1c; 0x19c90; 0x19cd0; 0x19ca4; 0x19cd0; 0x19d54; 0x19d60; 0x19d64;
       0x16768; 0x19da0; 0x1af98; 0x1ad94; 0x27800] [].
End FXG.
