(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import
  SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux DSLayout ZSLayout FillWinMem TreeMem BitsModel BitsModel2
  RomRead TreesRod FlushBlockModel BitsLib DeflM.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import
  ZIface ZChkAdl DeflateState Trees TreeModel SendModel DeflateLz DeflateBlk LmatchModel FillWinModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6S Require Import Segs6 DS6 Callee6 TreesRod6 TreesApi6 DeflBlkApi6 DeflSlow6_1 DeflSlow6_4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.


Record DKH (ROM : (word -> option byte) -> Prop) (mem : word -> option byte) (S : Z) (p : ds_ptrs) (zp : zs_ptrs)
           (ds : deflate_state) (flush : Z) (ra : word) (sp K FR : Z) : Prop := {
  dsh_L : ZRH6 K mem S sp p zp ds;
  dsh_ret : ret_ok ra;
  dsh_zr : ZR6 mem S p zp ds;
  dsh_flush : 0 <= flush <= 5;
  dsh_wf : DWF ds;
  dsh_rom : ROM mem;
  dsh_roml : rom_local6 ROM;
  dsh_K : 0 <= FR <= K }.

Section Walk.
Variable ROM : (word -> option byte) -> Prop.
Variables (mem : word -> option byte) (S : Z) (p : ds_ptrs) (zp : zs_ptrs) (ds : deflate_state) (flush : Z) (ra : word) (sp K FR : Z).
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
Local Abbreviation SP := (sp - FR).
Hypothesis HH : DKH ROM mem S p zp ds flush ra sp K FR.

Let HL : ZRH6 K mem S sp p zp ds := dsh_L _ _ _ _ _ _ _ _ _ _ _ HH.
Let HWF : DWF ds := dsh_wf _ _ _ _ _ _ _ _ _ _ _ HH.
Let HRL : rom_local6 ROM := dsh_roml _ _ _ _ _ _ _ _ _ _ _ HH.
Let HKF : 0 <= FR <= K := dsh_K _ _ _ _ _ _ _ _ _ _ _ HH.

Definition Fd : franges := ZRF K S sp p zp ds.
Definition GD : franges := (sp - K, K - FR) :: tl Fd.
Definition GDo (st : cstrm) : franges :=
  [(sp - K, K - FR); (S, ds6_SIZE); (W, 2 * ws); (PV, 2 * ws); (HD, 2 * hs); (PB, PBL); (strm, zsl_SIZE);
   (OUTB, Z.of_nat (length (cs_out_rev st)))].

Local Abbreviation BRm := (BR s6_segs 168672 168704 168736 Fd mem S p PBL).


Lemma region_facts :
  K <= sp <= 2 ^ 63
  /\ (0 <= S /\ S + 5968 <= 2 ^ 63) /\ (0 < W /\ W + 2 * ws <= 2 ^ 63)
  /\ (0 <= PV /\ PV + 2 * ws <= 2 ^ 63) /\ (0 <= HD /\ HD + 2 * hs <= 2 ^ 63)
  /\ (0 <= PB /\ PB + PBL <= 2 ^ 63) /\ (0 <= strm /\ strm + 112 <= 2 ^ 63)
  /\ (0 <= OUTB /\ OUTB + (OLEN0 + AV0) <= 2 ^ 63)
  /\ (0 <= INP /\ INP + ILEN < 2 ^ 63).
Proof.
  pose proof (zrh_sp _ _ _ _ _ _ _ HL) as Hsp. pose proof (zrh_W _ _ _ _ _ _ _ HL) as HW0. pose proof (zrh_in _ _ _ _ _ _ _ HL) as HI.
  pose proof (zrh_rng _ _ _ _ _ _ _ HL) as HR. unfold zr_regions, ds6_SIZE, zsl_SIZE in *.
  repeat match type of HR with Forall _ (_ :: _) => apply Forall_cons_iff in HR; destruct HR as [? HR]; cbn [fst snd] in * end.
  repeat split; lia.
Qed.

Lemma apart_ij : forall i j, (i < j)%nat -> (j < 9)%nat ->
  apart (nth i (zr_regions K S sp p zp ds) (0, 0)) (nth j (zr_regions K S sp p zp ds) (0, 0)).
Proof. intros i j Hij Hj. apply apart_get; [exact (zrh_apart _ _ _ _ _ _ _ HL) | exact Hij | cbn; lia]. Qed.

Ltac apartF i j H := pose proof (apart_ij i j ltac:(lia) ltac:(lia)) as H; unfold apart, zr_regions in H; cbn [nth fst snd] in H; unfold ds6_SIZE, zsl_SIZE in H.

Lemma mapped_i : forall i, (i < 8)%nat ->
  mapped mem (fst (nth i (ZRF K S sp p zp ds) (0, 0))) (snd (nth i (ZRF K S sp p zp ds) (0, 0))).
Proof.
  intros i Hi. pose proof (zrh_map _ _ _ _ _ _ _ HL) as HM. unfold ZRF in HM |- *.
  do 8 (destruct i as [|i]; [apply Forall_inv in HM; exact HM | apply Forall_inv_tail in HM]). lia.
Qed.
Ltac mappedF i H := pose proof (mapped_i i ltac:(lia)) as H; unfold ZRF in H; cbn [nth fst snd] in H; unfold ds6_SIZE, zsl_SIZE in H.

Lemma BRH_d : BRH Fd S p PBL.
Proof.
  pose proof region_facts as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN). apartF 1%nat 5%nat Ap15.
  unfold BRH, Fd, ZRF, ds6_SIZE, dsl_SIZE. split; [lia|]. split; [lia|]. split; [lia|].
  split; [apply sub_franges_later; apply sub_franges_here; unfold ds6_SIZE, dsl_SIZE; lia|].
  split; [apply sub_franges_later; apply sub_franges_here; unfold ds6_SIZE, dsl_SIZE; lia|].
  split; [apply sub_franges_later; apply sub_franges_here; unfold ds6_SIZE, dsl_SIZE; lia|].
  do 5 apply sub_franges_later. apply sub_franges_here; lia.
Qed.

Lemma HFS_d : sub_franges Fd S ds6_SIZE.
Proof. unfold Fd, ZRF. apply sub_franges_later; apply sub_franges_here; lia. Qed.

Lemma in_Fd : forall x,
  (sp - K <= x < sp \/ S <= x < S + 5968 \/ W <= x < W + 2 * ws \/ PV <= x < PV + 2 * ws \/ HD <= x < HD + 2 * hs
   \/ PB <= x < PB + PBL \/ strm <= x < strm + 112 \/ OUTB <= x < OUTB + (OLEN0 + AV0)) ->
  in_franges Fd x.
Proof. intros x Hx. unfold Fd, ZRF, ds6_SIZE, zsl_SIZE. cbn [in_franges]. lia. Qed.

Lemma in_GD : forall x,
  (sp - K <= x < sp - FR \/ S <= x < S + 5968 \/ W <= x < W + 2 * ws \/ PV <= x < PV + 2 * ws \/ HD <= x < HD + 2 * hs
   \/ PB <= x < PB + PBL \/ strm <= x < strm + 112 \/ OUTB <= x < OUTB + (OLEN0 + AV0)) ->
  in_franges GD x.
Proof. intros x Hx. unfold GD, Fd, ZRF, ds6_SIZE, zsl_SIZE. cbn [in_franges tl]. lia. Qed.

Lemma GD_Fd : forall x, in_franges GD x -> in_franges Fd x.
Proof. intros x Hx. unfold GD, Fd, ZRF, ds6_SIZE, zsl_SIZE in *. cbn [in_franges tl] in *. lia. Qed.

Lemma in_GDo : forall st x,
  (sp - K <= x < sp - FR \/ S <= x < S + 5968 \/ W <= x < W + 2 * ws \/ PV <= x < PV + 2 * ws \/ HD <= x < HD + 2 * hs
   \/ PB <= x < PB + PBL \/ strm <= x < strm + 112 \/ OUTB <= x < OUTB + Z.of_nat (length (cs_out_rev st))) ->
  in_franges (GDo st) x.
Proof. intros st x Hx. unfold GDo, ds6_SIZE, zsl_SIZE. cbn [in_franges]. lia. Qed.

Lemma GDo_GD : forall st x, in_franges (GDo st) x -> Z.of_nat (length (cs_out_rev st)) <= OLEN0 + AV0 -> in_franges GD x.
Proof. intros st x Hx Hle. unfold GDo, GD, Fd, ZRF, ds6_SIZE, zsl_SIZE in *. cbn [in_franges tl] in *. lia. Qed.

Lemma GDo_mono : forall st st' x, in_franges (GDo st) x ->
  Z.of_nat (length (cs_out_rev st)) <= Z.of_nat (length (cs_out_rev st')) -> in_franges (GDo st') x.
Proof. intros st st' x Hx Hle. unfold GDo, ds6_SIZE, zsl_SIZE in *. cbn [in_franges] in *. lia. Qed.

Lemma out_GD : forall x, in_franges GD x -> ~ (sp - FR <= x < sp).
Proof.
  intros x Hx. pose proof region_facts as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN).
  apartF 0%nat 1%nat Ap01. apartF 0%nat 2%nat Ap02. apartF 0%nat 3%nat Ap03. apartF 0%nat 4%nat Ap04.
  apartF 0%nat 5%nat Ap05. apartF 0%nat 6%nat Ap06. apartF 0%nat 7%nat Ap07.
  unfold GD, Fd, ZRF, ds6_SIZE, zsl_SIZE in Hx. cbn [in_franges tl] in Hx. lia.
Qed.


Lemma GD_img : forall x, in_franges GD x -> IMG6_LO <= x < IMG6_HI -> False.
Proof. intros x Hx Hi. exact (zrh_img _ _ _ _ _ _ _ HL x (GD_Fd x Hx) Hi). Qed.

Lemma GDo_img : forall st x, in_franges (GDo st) x -> Z.of_nat (length (cs_out_rev st)) <= OLEN0 + AV0 ->
  IMG6_LO <= x < IMG6_HI -> False.
Proof. intros st x Hx Hle Hi. exact (GD_img x (GDo_GD st x Hx Hle) Hi). Qed.

Lemma out_GDo : forall st x, in_franges (GDo st) x -> Z.of_nat (length (cs_out_rev st)) <= OLEN0 + AV0 -> ~ (sp - FR <= x < sp).
Proof. intros st x Hx Hle. exact (out_GD x (GDo_GD st x Hx Hle)). Qed.

Definition CST (w pv hd : arr) (st : cstrm) : Prop :=
  arr_len w = 2 * ws /\ arr_len pv = ws /\ arr_len hd = hs /\ cs_input st = cs_input (ds_strm ds)
  /\ Z.of_nat (length (cs_out_rev st)) + cs_avail_out st = OLEN0 + AV0
  /\ 0 <= cs_avail_out st /\ OLEN0 <= Z.of_nat (length (cs_out_rev st)).

Definition RZmisc (m1 m : word -> option byte) (st : cstrm) : Prop :=
  rod6 m /\ ROM m /\ agree_out (GDo st) m1 m /\ mapped m (sp - K) K /\ (forall x, mem x <> None -> m x <> None).

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
  split; [apartF 1%nat 2%nat Ap2; apply cells_write_other; try lia; exact Cw|].
  split; [apartF 1%nat 3%nat Ap3; apply cells_write_other; try lia; exact Cp|].
  split; [apartF 1%nat 4%nat Ap4; apply cells_write_other; try lia; exact Ch|].
  split; [apartF 1%nat 6%nat Ap5; apply zsl_scalars_frame; unfold zsl_SIZE; try lia; exact Zs|].
  split; [apartF 1%nat 8%nat Ap8; unfold zsl_input in *; rewrite Ein in *; apply cells_write_other; try lia; exact Zi|].
  split; [apartF 1%nat 7%nat Ap6; unfold zsl_outA in *; apply cells_write_other; try lia; exact Zo|].
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
  split; [apartF 2%nat 5%nat Ap2; apply cells_write_other; try lia; exact Cw|].
  split; [apartF 3%nat 5%nat Ap3; apply cells_write_other; try lia; exact Cp|].
  split; [apartF 4%nat 5%nat Ap4; apply cells_write_other; try lia; exact Ch|].
  split; [apartF 5%nat 6%nat Ap5; apply zsl_scalars_frame; unfold zsl_SIZE; try lia; exact Zs|].
  split; [apartF 5%nat 8%nat Ap8; unfold zsl_input in *; rewrite Ein in *; apply cells_write_other; try lia; exact Zi|].
  split; [apartF 5%nat 7%nat Ap6; unfold zsl_outA in *; apply cells_write_other; try lia; exact Zo|].
  split; [| exact HC].
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & _ & _ & _ & MP & _).
  apply RZmisc_st; [exact HM | lia | lia | intros x Hx; apply in_GDo; lia | lia | intros x Hx; apply MP; lia].
Qed.

Lemma RZ_st_frame : forall m1 m w pv hd st (b : Z) bs,
  RZ m1 m w pv hd st ->
  sp - K <= b -> b + Z.of_nat (length bs) <= sp - FR ->
  RZ m1 (wbytes m (zw b) bs) w pv hd st.
Proof.
  intros m1 m w pv hd st b bs HR Hb0 Hb1.
  pose proof HR as (Cw & Cp & Ch & Zs & Zi & Zo & HM & HC).
  pose proof region_facts as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN).
  pose proof HC as (Lw & Lp & Lh & Ein & Eout & Hao & Hol).
  unfold RZ.
  split; [apartF 0%nat 2%nat Ap2; apply cells_write_other; try lia; exact Cw|].
  split; [apartF 0%nat 3%nat Ap3; apply cells_write_other; try lia; exact Cp|].
  split; [apartF 0%nat 4%nat Ap4; apply cells_write_other; try lia; exact Ch|].
  split; [apartF 0%nat 6%nat Ap5; apply zsl_scalars_frame; unfold zsl_SIZE; try lia; exact Zs|].
  split; [apartF 0%nat 8%nat Ap8; unfold zsl_input in *; rewrite Ein in *; apply cells_write_other; try lia; exact Zi|].
  split; [apartF 0%nat 7%nat Ap6; unfold zsl_outA in *; apply cells_write_other; try lia; exact Zo|].
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
  split; [apartF 2%nat 3%nat Ap2; apply cells_write_other; rewrite ?length_Z_to_le_bytes; try lia; exact Cw|].
  split; [rewrite <- (arr_len_set pv i v'); apply cells16_set; try lia; try exact Cp; try exact Ev|].
  split; [apartF 3%nat 4%nat Ap4; apply cells_write_other; rewrite ?length_Z_to_le_bytes; try lia; exact Ch|].
  split; [apartF 3%nat 6%nat Ap5; apply zsl_scalars_frame; rewrite ?length_Z_to_le_bytes; unfold zsl_SIZE; try lia; exact Zs|].
  split; [apartF 3%nat 8%nat Ap8; unfold zsl_input in *; rewrite Ein in *; apply cells_write_other; rewrite ?length_Z_to_le_bytes; try lia; exact Zi|].
  split; [apartF 3%nat 7%nat Ap6; unfold zsl_outA in *; apply cells_write_other; rewrite ?length_Z_to_le_bytes; try lia; exact Zo|].
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
  split; [apartF 2%nat 4%nat Ap2; apply cells_write_other; rewrite ?length_Z_to_le_bytes; try lia; exact Cw|].
  split; [apartF 3%nat 4%nat Ap3; apply cells_write_other; rewrite ?length_Z_to_le_bytes; try lia; exact Cp|].
  split; [rewrite <- (arr_len_set hd i v'); apply cells16_set; try lia; try exact Ch; try exact Ev|].
  split; [apartF 4%nat 6%nat Ap5; apply zsl_scalars_frame; rewrite ?length_Z_to_le_bytes; unfold zsl_SIZE; try lia; exact Zs|].
  split; [apartF 4%nat 8%nat Ap8; unfold zsl_input in *; rewrite Ein in *; apply cells_write_other; rewrite ?length_Z_to_le_bytes; try lia; exact Zi|].
  split; [apartF 4%nat 7%nat Ap6; unfold zsl_outA in *; apply cells_write_other; rewrite ?length_Z_to_le_bytes; try lia; exact Zo|].
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
  split; [apartF 2%nat 6%nat Ap2; apply cells_write_other; rewrite ?length_Z_to_le_bytes; try lia; exact Cw|].
  split; [apartF 3%nat 6%nat Ap3; apply cells_write_other; rewrite ?length_Z_to_le_bytes; try lia; exact Cp|].
  split; [apartF 4%nat 6%nat Ap4; apply cells_write_other; rewrite ?length_Z_to_le_bytes; try lia; exact Ch|].
  split; [exact Hz'|].
  split; [apartF 6%nat 8%nat Ap8; unfold zsl_input in *; rewrite Ein', Ein in *; apply cells_write_other; rewrite ?length_Z_to_le_bytes; try lia; exact Zi|].
  split; [apartF 6%nat 7%nat Ap6; unfold zsl_outA, cs_output in *; rewrite Eor'; apply cells_write_other; rewrite ?length_Z_to_le_bytes; try lia; exact Zo|].
  split; [eapply RZmisc_eqo; [| exact Eor'];
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
  BRm m X -> sp - K <= b -> b + Z.of_nat (length bs) <= sp ->
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

Lemma DI_st_frame : forall m1 m X (a : Z) bs, DI m1 m X -> sp - K <= a -> a + Z.of_nat (length bs) <= sp - FR ->
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


Lemma DI_eqst : forall m1 m s1 s2, DI m1 m s1 -> s1 = s2 -> DI m1 m s2.
Proof. intros m1 m s1 s2 H <-. exact H. Qed.

End Walk.


Section Glue.
Variable ROM : (word -> option byte) -> Prop.
Variables (mem : word -> option byte) (S : Z) (p : ds_ptrs) (zp : zs_ptrs) (ds : deflate_state) (flush : Z) (ra : word) (sp K FR : Z).
Hypothesis MEMCPY : memcpy_run6.
Hypothesis TFBITS : tr_flush_bits_run6.
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
Local Abbreviation SP := (sp - FR).
Hypothesis HH : DKH ROM mem S p zp ds flush ra sp K FR.
Local Abbreviation DI := (DI ROM mem S p zp ds sp K FR).
Local Abbreviation BRm := (BR s6_segs 168672 168704 168736 (Fd S p zp ds sp K) mem S p PBL).
Local Abbreviation Fd := (Fd S p zp ds sp K).
Local Abbreviation GD := (GD S p zp ds sp K FR).
Local Abbreviation GDo := (GDo S p zp ds sp K FR).
Local Abbreviation RZ := (RZ ROM mem S p zp ds sp K FR).
Local Abbreviation RZmisc := (RZmisc ROM mem S p zp ds sp K FR).
Local Abbreviation CST := (CST ds).

Let HL : ZRH6 K mem S sp p zp ds := dsh_L _ _ _ _ _ _ _ _ _ _ _ HH.
Let HWF : DWF ds := dsh_wf _ _ _ _ _ _ _ _ _ _ _ HH.
Let HRL : rom_local6 ROM := dsh_roml _ _ _ _ _ _ _ _ _ _ _ HH.
Let HKF : 0 <= FR <= K := dsh_K _ _ _ _ _ _ _ _ _ _ _ HH.

Let GDI : forall x, in_franges GD x -> IMG6_LO <= x < IMG6_HI -> False := GD_img _ _ _ _ _ _ _ _ _ _ _ HH.
Let GDoI : forall st x, in_franges (GDo st) x -> Z.of_nat (length (cs_out_rev st)) <= OLEN0 + AV0 -> IMG6_LO <= x < IMG6_HI -> False
  := GDo_img _ _ _ _ _ _ _ _ _ _ _ HH.

Local Ltac apartF i j H :=
  pose proof (apart_ij _ _ _ _ _ _ _ _ _ _ _ HH i j ltac:(lia) ltac:(lia)) as H;
  unfold apart, zr_regions in H; cbn [nth fst snd] in H; unfold ds6_SIZE, dsl_SIZE, zsl_SIZE in H.
Local Ltac mappedF i H :=
  pose proof (mapped_i _ _ _ _ _ _ _ _ _ _ _ HH i ltac:(lia)) as H; unfold ZRF in H; cbn [nth fst snd] in H; unfold ds6_SIZE, dsl_SIZE, zsl_SIZE in H.


Lemma RZ_agree : forall m1 m m' w pv hd st (Fc : franges),
  RZ m1 m w pv hd st -> agree_out Fc m m' ->
  (forall x, in_franges Fc x -> in_franges (GDo st) x) ->
  (forall x : word, in_franges Fc (bv_unsigned x) -> m x <> None) ->
  disj_franges Fc W (2 * ws) -> disj_franges Fc PV (2 * ws) -> disj_franges Fc HD (2 * hs) ->
  disj_franges Fc strm 112 -> disj_franges Fc INP ILEN -> disj_franges Fc OUTB (OLEN0 + AV0) ->
  (forall x, m x <> None -> m' x <> None) ->
  RZ m1 m' w pv hd st.
Proof.
  intros m1 m m' w pv hd st Fc HR Hag HG HM DW DP DH DS DI DO HGR'.
  pose proof HR as (Cw & Cp & Ch & Zs & Zi & Zo & (HRC & HRD & HAG & MF & HGR) & HC).
  pose proof (region_facts _ _ _ _ _ _ _ _ _ _ _ HH) as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN).
  pose proof HC as (Lw & Lp & Lh & Ein & Eout & Hao & Hol).
  unfold RZ.
  split; [eapply cells_agree_out; [exact Hag | rewrite Lw; intros x Hx; apply DW; lia | cbn; lia | lia | rewrite Lw; lia | exact Cw]|].
  split; [eapply cells_agree_out; [exact Hag | rewrite Lp; exact DP | cbn; lia | lia | rewrite Lp; lia | exact Cp]|].
  split; [eapply cells_agree_out; [exact Hag | rewrite Lh; exact DH | cbn; lia | lia | rewrite Lh; lia | exact Ch]|].
  split; [eapply zsl_scalars_agree; [exact Zs | exact Hag | unfold zsl_SIZE; exact DS | lia | unfold zsl_SIZE; lia]|].
  split; [eapply zsl_input_agree; [exact Zi | exact Hag | rewrite Ein; exact DI | lia | rewrite Ein; lia]|].
  split.
  { unfold zsl_outA in *. eapply cells_agree_out; [exact Hag | intros x Hx; apply DO; lia | cbn; lia | lia | lia | exact Zo]. }
  split; [| exact HC].
  unfold RZmisc. split; [split; [exact (trees_rod_clear_agree R6 Fc m m' (proj1 HRC) Hag HM) | exact (got_agree Fc m m' (proj2 HRC) Hag HM)]|].
  split; [exact (rom_agree ROM Fc m m' HRL HRD Hag ltac:(intros x Hx; exact (GDoI st x (HG x Hx) ltac:(lia))))|].
  split; [eapply agree_out_trans; [exact HAG | eapply agree_out_weaken; [exact Hag | exact HG]]|].
  split; [intros x Hx; apply HGR'; apply MF; exact Hx|].
  intros x Hx. apply HGR'. apply HGR. exact Hx.
Qed.


Definition Fbits : franges := [(S, ds6_SIZE); (PB, PBL)].

Lemma call_bits : forall regs m1 m X (ra' : word),
  DI m1 m X -> ret_ok ra' -> BINV PBL X -> ds_pending (tr_flush_bits X) <= PBL ->
  getr regs 10 = zw S -> getr regs 1 = ra' ->
  exists R m',
    msteps s6_segs (mkst regs (0x1ad94 : word) m s6_rom) (mkst R ra' m' s6_rom)
    /\ DI m1 m' (tr_flush_bits X)
    /\ (forall r : reg, reg_in r FB_CLOB = false -> getr R r = getr regs r)
    /\ agree_out Fbits m m'.
Proof.
  intros regs m1 m X ra' HDI Hret HBI Hroom P10 P1.
  pose proof HDI as (HB & HR & (Ews & Ehs & Elbs)).
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (Hsc & Har & Hlens & Hpend & HagF & MS & MP & HGR0).
  pose proof HR as (Cw & Cp & Ch & Zs & Zi & Zo & (HRC & HRD & HAG & MF & HGR) & HC).
  pose proof (region_facts _ _ _ _ _ _ _ _ _ _ _ HH) as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN).
  assert (HLc : BRH Fbits S p PBL).
  { pose proof (BRH_d _ _ _ _ _ _ _ _ _ _ _ HH) as (Ap1 & Ap2 & Ap3 & _). unfold BRH, Fbits.
    split; [exact Ap1|]. split; [exact Ap2|]. split; [exact Ap3|]. unfold ds6_SIZE, dsl_SIZE.
    split; [apply sub_franges_here; lia|]. split; [apply sub_franges_here; lia|]. split; [apply sub_franges_here; lia|].
    apply sub_franges_later; apply sub_franges_here; lia. }
  destruct (TFBITS Fbits m m S p PBL X ra' regs HLc Hret (BR_self s6_segs 168672 168704 168736 _ Fbits _ _ _ _ _ _ HB) HBI Hroom P10 P1)
    as (R & m' & Hms & HB' & Hfr). unfold A6_TR_FLUSH_BITS in Hms. symex_pc_lit_in Hms.
  destruct (BR_back s6_segs 168672 168704 168736 Fd Fbits mem S p PBL m m' X _ HB HB') as [HB2 Hag].
  { unfold Fbits. intros x [Hx|[Hx|[]]]; cbn in Hx; apply in_Fd; unfold ds6_SIZE, dsl_SIZE in Hx; lia. }
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB') as (_ & _ & _ & _ & _ & _ & _ & HGR').
  exists R, m'. split; [exact Hms|]. split; [| split; [exact Hfr | exact Hag]].
  pose proof (tr_flush_bits_nobits X) as En. unfold ds_nobits, ds_sizes in En.
  injection En as Ew Ep Eh Est Esz1 Esz2 Esz3 _ _.
  split; [exact HB2|]. split; [| rewrite Esz1, Esz2, Esz3; exact (conj Ews (conj Ehs Elbs))].
  rewrite Ew, Ep, Eh, Est.
  eapply (RZ_agree m1 m m' _ _ _ _ Fbits HR Hag); try exact HGR'.
  - unfold Fbits. intros x [Hx|[Hx|[]]]; cbn in Hx; apply in_GDo; unfold ds6_SIZE, dsl_SIZE in Hx; lia.
  - unfold Fbits. intros x [Hx|[Hx|[]]]; cbn in Hx; [apply MS; exact Hx | apply MP; exact Hx].
  - apartF 1%nat 2%nat Ap12. apartF 2%nat 5%nat Ap25. unfold Fbits, ds6_SIZE, dsl_SIZE. intros x Hx [Hin|[Hin|[]]]; cbn in Hin; lia.
  - apartF 1%nat 3%nat Ap13. apartF 3%nat 5%nat Ap35. unfold Fbits, ds6_SIZE, dsl_SIZE. intros x Hx [Hin|[Hin|[]]]; cbn in Hin; lia.
  - apartF 1%nat 4%nat Ap14. apartF 4%nat 5%nat Ap45. unfold Fbits, ds6_SIZE, dsl_SIZE. intros x Hx [Hin|[Hin|[]]]; cbn in Hin; lia.
  - apartF 1%nat 6%nat Ap16. apartF 5%nat 6%nat Ap56. unfold Fbits, ds6_SIZE, dsl_SIZE. intros x Hx [Hin|[Hin|[]]]; cbn in Hin; lia.
  - apartF 1%nat 8%nat Ap18. apartF 5%nat 8%nat Ap58. unfold Fbits, ds6_SIZE, dsl_SIZE. intros x Hx [Hin|[Hin|[]]]; cbn in Hin; lia.
  - apartF 1%nat 7%nat Ap17. apartF 5%nat 7%nat Ap57. unfold Fbits, ds6_SIZE, dsl_SIZE. intros x Hx [Hin|[Hin|[]]]; cbn in Hin; lia.
Qed.


Lemma fbytes_nth_mod : forall f k a j, (j < k)%nat -> bnth (fbytes f a k) j = (f (a + Z.of_nat j)) mod 2 ^ 8.
Proof.
  induction k as [|k IH]; intros a j Hj; [lia|].
  destruct j as [|j].
  - cbn [fbytes bnth nth]. unfold bnth. cbn [nth]. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (2 ^ Z.of_N 8) with (2 ^ 8). rewrite Z.add_0_r. reflexivity.
  - cbn [fbytes]. unfold bnth. cbn [nth]. fold (bnth (fbytes f (a + 1) k) j).
    rewrite IH by lia. f_equal. f_equal. lia.
Qed.

Lemma cs_output_emit : forall st l, cs_output (cs_emit st l) = cs_output st ++ l.
Proof.
  intros st l. unfold cs_output, cs_emit. destruct st; cbn -[rev_append].
  rewrite !List.rev_append_rev, !app_nil_r, rev_app_distr, rev_involutive. reflexivity.
Qed.

Lemma length_cs_output : forall st, length (cs_output st) = length (cs_out_rev st).
Proof. intros st. unfold cs_output. rewrite List.rev_append_rev, app_nil_r, length_rev. reflexivity. Qed.

Lemma DI_out_write : forall m1 m X bs,
  DI m1 m X ->
  Z.of_nat (length bs) <= cs_avail_out (ds_strm X) ->
  let st := ds_strm X in
  let M' := wbytes m (zw (OUTB + Z.of_nat (length (cs_out_rev st)))) bs in
  BRm M' X
  /\ cells s6_segs M' W 1 1 (arr_len (ds_window X)) (arr_get (ds_window X))
  /\ cells s6_segs M' PV 2 2 (arr_len (ds_prev X)) (arr_get (ds_prev X))
  /\ cells s6_segs M' HD 2 2 (arr_len (ds_head X)) (arr_get (ds_head X))
  /\ zsl_scalars s6_segs M' strm zp S st /\ zsl_input s6_segs M' zp st /\ zsl_outA M' zp st
  /\ (forall st', Z.of_nat (length (cs_out_rev st')) = Z.of_nat (length (cs_out_rev st)) + Z.of_nat (length bs) -> RZmisc m1 M' st')
  /\ RZmisc M' M' st.
Proof.
  intros m1 m X bs (HB & HR & HS3) Hlen.
  pose proof HR as (Cw & Cp & Ch & Zs & Zi & Zo & HM & HC).
  pose proof HC as (Lw & Lp & Lh & Ein & Eout & Hao & Hol).
  pose proof (region_facts _ _ _ _ _ _ _ _ _ _ _ HH) as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN).
  pose proof HM as (HRC & HRD & HAG & MF & HGR). mappedF 7%nat M7.
  set (olen := Z.of_nat (length (cs_out_rev (ds_strm X)))) in *. cbv zeta.
  split.
  { apply (BR_st_far _ _ _ _ _ _ _ _ _ _ _ HH); [exact HB | lia | lia | apartF 1%nat 7%nat A; lia | apartF 5%nat 7%nat A; lia | intros x Hx; apply in_Fd; lia]. }
  split; [apartF 2%nat 7%nat A; apply cells_write_other; try lia; exact Cw|].
  split; [apartF 3%nat 7%nat A; apply cells_write_other; try lia; exact Cp|].
  split; [apartF 4%nat 7%nat A; apply cells_write_other; try lia; exact Ch|].
  split; [apartF 6%nat 7%nat A; apply zsl_scalars_frame; unfold zsl_SIZE; try lia; exact Zs|].
  split; [apartF 7%nat 8%nat A; unfold zsl_input in *; rewrite Ein in *; apply cells_write_other; try lia; exact Zi|].
  split; [unfold zsl_outA in *; apply cells_write_other; try lia; exact Zo|].
  split.
  { intros st' Eol'.
    apply (RZmisc_st _ _ _ _ _ _ _ _ _ _ _ HH); [ | lia | lia | intros x Hx; apply in_GDo; lia | lia | intros x Hx; apply HGR; apply M7; lia].
    eapply RZmisc_mono; [exact HM | lia]. }
  unfold RZmisc.
  split; [split; [apply (trees_rod_clear_wr R6 _ _ (proj1 HRC)) | apply (rom_clear_wr _ _ _ _ (proj2 HRC))];
         (apply wr_ok_wbytes; [apply wr_ok_refl | intros x Hx; apply HGR; apply M7; lia | lia | lia])|].
  split.
  { refine (rom_agree ROM [(OUTB + olen, Z.of_nat (length bs))] m _ HRL HRD _ _).
    - apply agree_out_wbytes; try lia; [apply agree_out_refl | apply sub_franges_here; lia].
    - intros x Hx. cbn in Hx. apply (zrh_img _ _ _ _ _ _ _ HL x). unfold ZRF. cbn [in_franges]. lia. }
  split; [apply agree_out_refl|]. split; [apply mapped_wbytes; exact MF|].
  intros x Hx. apply wbytes_grows. exact (HGR x Hx).
Qed.

Lemma DI_out_self : forall m1 m X bs,
  DI m1 m X ->
  Z.of_nat (length bs) <= cs_avail_out (ds_strm X) ->
  let M' := wbytes m (zw (OUTB + Z.of_nat (length (cs_out_rev (ds_strm X))))) bs in
  DI M' M' X.
Proof.
  intros m1 m X bs HDI Hlen. pose proof HDI as (_ & (_ & _ & _ & _ & _ & _ & _ & HC) & HS3).
  destruct (DI_out_write m1 m X bs HDI Hlen) as (HB & Cw & Cp & Ch & Zs & Zi & Zo & _ & HMs). cbv zeta.
  split; [exact HB|]. split; [| exact HS3]. unfold RZ.
  repeat (split; [assumption|]). exact HC.
Qed.

Lemma fp_finish : forall m1 m X (n : nat) (vtot : Z),
  DI m1 m X ->
  let len := Z.of_nat n in
  let olen := Z.of_nat (length (cs_out_rev (ds_strm X))) in
  let l := arr_slice (ds_pending_buf X) (ds_pending_out X) len in
  let M0 := wbytes m (zw (OUTB + olen)) (fbytes (arr_get (ds_pending_buf X)) (ds_pending_out X) n) in
  let M1 := wbytes M0 (zw (strm + 24)) (Z_to_le_bytes 8 (OUTB + olen + len)) in
  let M2 := wbytes M1 (zw (strm + 32)) (Z_to_le_bytes 4 (cs_avail_out (ds_strm X) - len)) in
  let M3 := wbytes M2 (zw (strm + 40)) (Z_to_le_bytes 8 vtot) in
  let M4 := wbytes M3 (zw (S + 32)) (Z_to_le_bytes 8 (PB + ds_pending_out X + len)) in
  let M5 := wbytes M4 (zw (S + 40)) (Z_to_le_bytes 8 (ds_pending X - len)) in
  let M6 := if ds_pending X - len =? 0 then wbytes M5 (zw (S + 32)) (Z_to_le_bytes 8 PB) else M5 in
  0 < len -> len <= cs_avail_out (ds_strm X) -> len <= ds_pending X -> 0 <= ds_pending_out X -> ds_pending_out X + len <= PBL ->
  0 <= cs_total_out (ds_strm X) -> vtot mod 2 ^ 64 = (cs_total_out (ds_strm X) + len) mod 2 ^ 64 ->
  DI m1 M6 (fp_tail X len).
Proof.
  intros m1 m X n vtot HDI len olen l M0 M1 M2 M3 M4 M5 M6 Hlen0 Hla Hlp Hpo0 Hpo1 Htot Evt.
  pose proof (region_facts _ _ _ _ _ _ _ _ _ _ _ HH) as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN).
  pose proof (wf_lbs _ HWF) as Wlbs.
  pose proof HDI as (HB & HR & HS3). pose proof HR as (_ & _ & _ & Zs & _ & Zo & HM & HC).
  pose proof HC as (Lw & Lp & Lh & Ein & Eout & Hao & Hol).
  pose proof HB as (_ & _ & _ & Hpb & Epbl & _).
  assert (Hl : Z.of_nat (length l) = len) by (subst l; unfold arr_slice; rewrite arr_slice_nat_length; lia).
  set (st' := cs_emit (ds_strm X) l).
  assert (Eol' : Z.of_nat (length (cs_out_rev st')) = olen + len).
  { subst st' olen. unfold cs_emit. dsred. rewrite List.rev_append_rev, length_app, length_rev. lia. }
  destruct (DI_out_write m1 m X (fbytes (arr_get (ds_pending_buf X)) (ds_pending_out X) n) HDI
              ltac:(rewrite fbytes_length; fold len; lia)) as (HB0 & Cw0 & Cp0 & Ch0 & Zs0 & Zi0 & Zo0 & HMf & _).
  fold olen M0 in HB0, Cw0, Cp0, Ch0, Zs0, Zi0, Zo0, HMf.
  pose proof (HMf st' ltac:(rewrite Eol', fbytes_length; fold len; lia)) as HM0. clear HMf.
  pose proof (memcpy_dst_cells' m (OUTB + olen) (fbytes (arr_get (ds_pending_buf X)) (ds_pending_out X) n)) as Cnew0. fold M0 in Cnew0.
  pose proof HM0 as (_ & _ & _ & _ & HGR0). mappedF 6%nat M6'. mappedF 7%nat M7.
  pose proof (zsl_upd_next_out_emit s6_segs M0 strm zp S (ds_strm X) l Zs0 ltac:(lia) ltac:(unfold zsl_SIZE; lia)) as Zs1.
  rewrite Hl in Zs1. fold olen in Zs1. change (wbytes M0 (zw (strm + 24)) (Z_to_le_bytes 8 (OUTB + olen + len))) with M1 in Zs1.
  assert (HB1 : BRm M1 X) by (apply (BR_st_strm _ _ _ _ _ _ _ _ _ _ _ HH); [exact HB0 | lia | cbn; lia]).
  assert (HM1 : RZmisc m1 M1 st').
  { apply (RZmisc_st _ _ _ _ _ _ _ _ _ _ _ HH); rewrite ?length_Z_to_le_bytes; [exact HM0 | lia | cbn; lia | intros x Hx; apply in_GDo; cbn in Hx; lia | lia | intros x Hx; apply HGR0; apply M6'; cbn in Hx; lia]. }
  pose proof (zsl_upd_avail_out s6_segs M1 strm zp S (cs_emit (ds_strm X) l) (cs_avail_out (ds_strm X) - len) Zs1 ltac:(lia) ltac:(unfold zsl_SIZE; lia)) as Zs2.
  change (wbytes M1 _ _) with M2 in Zs2.
  assert (HB2 : BRm M2 X) by (apply (BR_st_strm _ _ _ _ _ _ _ _ _ _ _ HH); [exact HB1 | lia | cbn; lia]).
  assert (HM2 : RZmisc m1 M2 st').
  { apply (RZmisc_st _ _ _ _ _ _ _ _ _ _ _ HH); rewrite ?length_Z_to_le_bytes; [exact HM1 | lia | cbn; lia | intros x Hx; apply in_GDo; cbn in Hx; lia | lia | intros x Hx; apply wbytes_grows; apply HGR0; apply M6'; cbn in Hx; lia]. }
  assert (EM3 : M3 = wbytes M2 (zw (strm + 40)) (Z_to_le_bytes 8 (wrap64 (cs_total_out (ds_strm X) + len)))).
  { subst M3. f_equal. apply Z_to_le_bytes_mod_eq. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64).
    rewrite Evt, wrap64_mod, Z.mod_mod by lia. reflexivity. }
  pose proof (zsl_upd_total_out s6_segs M2 strm zp S (cset_avail_out (cs_emit (ds_strm X) l) (cs_avail_out (ds_strm X) - len)) (wrap64 (cs_total_out (ds_strm X) + len)) Zs2 ltac:(lia) ltac:(unfold zsl_SIZE; lia)) as Zs3.
  rewrite <- EM3 in Zs3.
  assert (HB3 : BRm M3 X) by (apply (BR_st_strm _ _ _ _ _ _ _ _ _ _ _ HH); [exact HB2 | lia | cbn; lia]).
  assert (HM3 : RZmisc m1 M3 st').
  { apply (RZmisc_st _ _ _ _ _ _ _ _ _ _ _ HH); rewrite ?length_Z_to_le_bytes; [exact HM2 | lia | cbn; lia | intros x Hx; apply in_GDo; cbn in Hx; lia | lia | intros x Hx; do 2 apply wbytes_grows; apply HGR0; apply M6'; cbn in Hx; lia]. }
  pose proof (BR_st_pending_out _ _ _ _ _ _ _ _ _ _ _ HH M3 X (ds_pending_out X + len) HB3) as HB4.
  replace (PB + (ds_pending_out X + len)) with (PB + ds_pending_out X + len) in HB4 by lia. change (wbytes M3 _ _) with M4 in HB4.
  assert (Zs4 : zsl_scalars s6_segs M4 strm zp S (cset_total_out (cset_avail_out (cs_emit (ds_strm X) l) (cs_avail_out (ds_strm X) - len)) (wrap64 (cs_total_out (ds_strm X) + len)))).
  { apartF 1%nat 6%nat A. apply zsl_scalars_frame; rewrite ?length_Z_to_le_bytes; unfold zsl_SIZE; first [exact Zs3 | lia | cbn; lia]. }
  assert (HM4 : RZmisc m1 M4 st').
  { pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB3) as (_ & _ & _ & _ & _ & MS3 & _ & _).
    apply (RZmisc_st _ _ _ _ _ _ _ _ _ _ _ HH); rewrite ?length_Z_to_le_bytes; [exact HM3 | lia | cbn; lia | intros x Hx; apply in_GDo; cbn in Hx; lia | lia | intros x Hx; apply MS3; unfold ds6_SIZE, dsl_SIZE; cbn in Hx; lia]. }
  pose proof (BR_st_pending' _ _ _ _ _ _ _ _ _ _ _ HH M4 _ (ds_pending X - len) HB4) as HB5. change (wbytes M4 _ _) with M5 in HB5.
  assert (Zs5 : zsl_scalars s6_segs M5 strm zp S (cset_total_out (cset_avail_out (cs_emit (ds_strm X) l) (cs_avail_out (ds_strm X) - len)) (wrap64 (cs_total_out (ds_strm X) + len)))).
  { apartF 1%nat 6%nat A. apply zsl_scalars_frame; rewrite ?length_Z_to_le_bytes; unfold zsl_SIZE; first [exact Zs4 | lia | cbn; lia]. }
  assert (HM5 : RZmisc m1 M5 st').
  { pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB4) as (_ & _ & _ & _ & _ & MS4 & _ & _).
    apply (RZmisc_st _ _ _ _ _ _ _ _ _ _ _ HH); rewrite ?length_Z_to_le_bytes; [exact HM4 | lia | cbn; lia | intros x Hx; apply in_GDo; cbn in Hx; lia | lia | intros x Hx; apply MS4; unfold ds6_SIZE, dsl_SIZE; cbn in Hx; lia]. }
  assert (OTH : forall P nn (f : Z -> Z) (w : nat), Z.of_nat w <= Z.of_nat w ->
            (P = W /\ nn = 2 * ws /\ (w = 1)%nat) \/ (P = PV /\ nn = ws /\ (w = 2)%nat) \/ (P = HD /\ nn = hs /\ (w = 2)%nat) \/ (P = INP /\ nn = ILEN /\ (w = 1)%nat) ->
            cells s6_segs M0 P (Z.of_nat w) w nn f -> cells s6_segs M5 P (Z.of_nat w) w nn f).
  { intros P nn f w _ HP Hc. pose proof (wf_wsz _ HWF) as Wws. pose proof (wf_hsz _ HWF) as Whs.
    apartF 1%nat 2%nat Ap12. apartF 1%nat 3%nat Ap13. apartF 1%nat 4%nat Ap14. apartF 1%nat 8%nat Ap18.
    apartF 2%nat 6%nat Ap26. apartF 3%nat 6%nat Ap36. apartF 4%nat 6%nat Ap46. apartF 6%nat 8%nat Ap68.
    destruct HP as [(-> & -> & ->)|[(-> & -> & ->)|[(-> & -> & ->)|(-> & -> & ->)]]]; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *;
      (do 5 (apply cells_write_other; rewrite ?length_Z_to_le_bytes; [| cbn; lia | lia | lia | lia | cbn; lia | cbn; lia]); exact Hc). }
  pose proof HC as HC'. pose proof Cw0 as Cw0'. pose proof Cp0 as Cp0'. pose proof Ch0 as Ch0'. pose proof Zi0 as Zi0'.
  rewrite Lw in Cw0'. rewrite Lp in Cp0'. rewrite Lh in Ch0'. unfold zsl_input in Zi0'. rewrite Ein in Zi0'.
  pose proof (OTH W (2 * ws) _ 1%nat ltac:(lia) ltac:(left; auto) Cw0') as Cw5.
  pose proof (OTH PV ws _ 2%nat ltac:(lia) ltac:(right; left; auto) Cp0') as Cp5.
  pose proof (OTH HD hs _ 2%nat ltac:(lia) ltac:(right; right; left; auto) Ch0') as Ch5.
  pose proof (OTH INP ILEN _ 1%nat ltac:(lia) ltac:(right; right; right; auto) Zi0') as Zi5.
  assert (Zo5 : cells s6_segs M5 OUTB 1 1 (olen + len) (fun i => nth (Z.to_nat i) (cs_output (cs_emit (ds_strm X) l)) 0)).
  { assert (Zo0' : cells s6_segs M0 OUTB 1 1 (olen + len) (fun i => nth (Z.to_nat i) (cs_output (cs_emit (ds_strm X) l)) 0)).
    { intros i Hi. rewrite cs_output_emit. cbn beta.
      destruct (Z_lt_le_dec i olen) as [Hlo|Hhi].
      - rewrite app_nth1 by (rewrite length_cs_output; lia). apply Zo0. lia.
      - rewrite app_nth2 by (rewrite length_cs_output; lia). rewrite length_cs_output.
        specialize (Cnew0 ltac:(lia) ltac:(rewrite fbytes_length; fold len; lia) (i - olen) ltac:(rewrite fbytes_length; fold len; lia)).
        cbn beta in Cnew0. rewrite fbytes_nth_mod in Cnew0 by lia.
        replace (Z.of_nat (Z.to_nat (i - olen))) with (i - olen) in Cnew0 by lia.
        replace (OUTB + olen + 1 * (i - olen)) with (OUTB + 1 * i) in Cnew0 by lia.
        replace (Z.to_nat i - length (cs_out_rev (ds_strm X)))%nat with (Z.to_nat (i - olen)) by lia.
        subst l. unfold arr_slice. rewrite arr_slice_nat_nth by lia.
        replace (ds_pending_out X + Z.of_nat (Z.to_nat (i - olen))) with (ds_pending_out X + (i - olen)) by lia.
        apply (proj1 (cell_mod s6_segs _ _ _ _)). change (2 ^ (8 * Z.of_nat 1)) with (2 ^ 8). exact Cnew0. }
    apartF 1%nat 7%nat Ap17. apartF 6%nat 7%nat Ap67.
    do 5 (apply cells_write_other; rewrite ?length_Z_to_le_bytes; [| cbn; lia | lia | lia | lia | cbn; lia | cbn; lia]). exact Zo0'. }
  assert (HD5 : DI m1 M5 (set_pending (set_strm (set_pending_out X (ds_pending_out X + len))
                                         (cset_total_out (cset_avail_out (cs_emit (ds_strm X) l) (cs_avail_out (ds_strm X) - len)) (wrap64 (cs_total_out (ds_strm X) + len))))
                               (ds_pending X - len))).
  { split; [exact HB5|]. split; [| dsred; exact HS3]. dsred. unfold RZ.
    rewrite Lw, Lp, Lh. split; [exact Cw5|]. split; [exact Cp5|]. split; [exact Ch5|]. split; [exact Zs5|].
    split; [unfold zsl_input; dsred; unfold cs_emit; dsred; rewrite Ein; exact Zi5|].
    split; [unfold zsl_outA; dsred; replace (Z.of_nat (length (cs_out_rev (cs_emit (ds_strm X) l)))) with (olen + len)
              by (unfold cs_emit; dsred; rewrite List.rev_append_rev, length_app, length_rev; lia); exact Zo5|].
    split; [eapply RZmisc_eqo; [exact HM5 | subst st'; dsred; reflexivity]|].
    unfold CST. dsred. unfold cs_emit; dsred. rewrite List.rev_append_rev, length_app, length_rev.
    repeat split; try assumption; lia. }
  unfold fp_tail. cbv zeta. subst M6.
  destruct (ds_pending X - len =? 0).
  - replace PB with (PB + 0) by lia. eapply DI_eqst; [apply (DI_st_pending_out' _ _ _ _ _ _ _ _ _ _ _ HH); [exact HD5 | reflexivity]|].
    dsred. reflexivity.
  - eapply DI_eqst; [exact HD5|]. dsred. reflexivity.
Qed.


Lemma call_mc : forall regs m1 m X (n : nat) (ra' : word),
  DI m1 m X -> ret_ok ra' ->
  let len := Z.of_nat n in
  let olen := Z.of_nat (length (cs_out_rev (ds_strm X))) in
  0 <= ds_pending_out X -> ds_pending_out X + len <= PBL -> len <= cs_avail_out (ds_strm X) ->
  getr regs 1 = ra' -> getr regs 10 = zw (OUTB + olen) -> getr regs 11 = zw (PB + ds_pending_out X) -> getr regs 12 = zw len ->
  exists R,
    msteps s6_segs (mkst regs (0x27800 : word) m s6_rom)
           (mkst R ra' (wbytes m (zw (OUTB + olen)) (fbytes (arr_get (ds_pending_buf X)) (ds_pending_out X) n)) s6_rom)
    /\ getr R 10 = zw (OUTB + olen)
    /\ (forall r : reg, reg_in r memcpy_clob = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X n ra' HDI Hret len olen Hpo0 Hpo1 Hla P1 P10 P11 P12.
  pose proof HDI as (HB & HR & HS3). pose proof HR as (_ & _ & _ & _ & _ & _ & HM & HC).
  pose proof HC as (Lw & Lp & Lh & Ein & Eout & Hao & Hol). pose proof HM as (_ & _ & _ & _ & HGR).
  pose proof HB as (_ & _ & _ & Hpb & Epbl & _).
  pose proof (region_facts _ _ _ _ _ _ _ _ _ _ _ HH) as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN).
  pose proof (wf_lbs _ HWF) as Wlbs. mappedF 7%nat M7. apartF 5%nat 7%nat Ap57.
  destruct (MEMCPY m regs (OUTB + olen) (PB + ds_pending_out X) n (fbytes (arr_get (ds_pending_buf X)) (ds_pending_out X) n) ra'
              ltac:(apply (cells_rdn s6_segs m PB PBL); [exact Hpb | lia | fold len; lia | lia | lia])
              ltac:(lia) ltac:(fold len; lia) ltac:(lia) ltac:(fold len; lia) ltac:(fold len; lia)
              ltac:(intros x Hx; apply HGR; apply M7; fold len in Hx; lia) Hret P1 P10 P11 P12)
    as (R & Hms & R10 & Hfr). symex_pc_lit_in Hms.
  exists R. split; [exact Hms|]. split; [exact R10 | exact Hfr].
Qed.

Lemma DI_init : DI mem mem ds.
Proof.
  pose proof (dsh_zr _ _ _ _ _ _ _ _ _ _ _ HH) as (Hsc & Har & Hlens & HwA & HpA & HhA & HbA & Hzs & Hzi & Hzo).
  pose proof (region_facts _ _ _ _ _ _ _ _ _ _ _ HH) as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN).
  mappedF 0%nat M0. mappedF 1%nat M1. mappedF 5%nat M5.
  split.
  { apply (BR_init s6_segs 168672 168704 168736 _ mem S p PBL ds Hsc Har Hlens HbA (wf_blen _ HWF)); [exact M1 | exact M5]. }
  split; [| repeat split; reflexivity].
  unfold RZ. split; [exact HwA|]. split; [exact HpA|]. split; [exact HhA|]. split; [exact Hzs|]. split; [exact Hzi|]. split; [exact Hzo|].
  split.
  { unfold RZmisc. split; [exact (zrh_rod _ _ _ _ _ _ _ HL)|]. split; [exact (dsh_rom _ _ _ _ _ _ _ _ _ _ _ HH)|].
    split; [apply agree_out_refl|]. split; [exact M0 | intros x Hx; exact Hx]. }
  unfold CST. pose proof (wf_ao _ HWF).
  repeat split; first [exact (wf_wlen _ HWF) | exact (wf_plen _ HWF) | exact (wf_hlen _ HWF) | reflexivity | lia].
Qed.


Lemma DI_st_top : forall m X (a : Z) bs,
  DI m m X -> sp - FR <= a -> a + Z.of_nat (length bs) <= sp -> DI (wbytes m (zw a) bs) (wbytes m (zw a) bs) X.
Proof.
  intros m X a bs (HB & HR & HS3) Ha0 Ha1.
  pose proof HR as (Cw & Cp & Ch & Zs & Zi & Zo & (HRC & HRD & HAG & MF & HGR) & HC).
  pose proof HC as (Lw & Lp & Lh & Ein & Eout & Hao & Hol).
  pose proof (region_facts _ _ _ _ _ _ _ _ _ _ _ HH) as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN).
  split; [apply (BR_st_frame _ _ _ _ _ _ _ _ _ _ _ HH); [exact HB | lia | lia]|].
  split; [| exact HS3]. unfold RZ.
  split; [apartF 0%nat 2%nat A; apply cells_write_other; try lia; exact Cw|].
  split; [apartF 0%nat 3%nat A; apply cells_write_other; try lia; exact Cp|].
  split; [apartF 0%nat 4%nat A; apply cells_write_other; try lia; exact Ch|].
  split; [apartF 0%nat 6%nat A; apply zsl_scalars_frame; unfold zsl_SIZE; try lia; exact Zs|].
  split; [apartF 0%nat 8%nat A; unfold zsl_input in *; rewrite Ein in *; apply cells_write_other; try lia; exact Zi|].
  split; [apartF 0%nat 7%nat A; unfold zsl_outA in *; apply cells_write_other; try lia; exact Zo|].
  split; [| exact HC].
  unfold RZmisc.
  split; [split; [apply (trees_rod_clear_wr R6 _ _ (proj1 HRC)) | apply (rom_clear_wr _ _ _ _ (proj2 HRC))]; (apply wr_ok_wbytes; [apply wr_ok_refl | intros x Hx; apply MF; lia | lia | lia])|].
  split.
  { refine (rom_agree ROM [(a, Z.of_nat (length bs))] m _ HRL HRD _ _).
    - apply agree_out_wbytes; try lia; [apply agree_out_refl | apply sub_franges_here; lia].
    - intros x Hx. cbn in Hx. apply (zrh_img _ _ _ _ _ _ _ HL x). unfold ZRF. cbn [in_franges]. lia. }
  split; [apply agree_out_refl|]. split; [apply mapped_wbytes; exact MF|].
  intros x Hx. apply wbytes_grows. exact (HGR x Hx).
Qed.

Lemma top_keep : forall m1 m X a (w : nat) v,
  DI m1 m X -> cell s6_segs m1 a w v -> sp - FR <= a -> a + Z.of_nat w <= sp -> cell s6_segs m a w v.
Proof.
  intros m1 m X a w v (_ & (_ & _ & _ & _ & _ & _ & (_ & _ & HAG & _) & (_ & _ & _ & _ & Eout & Hao & Hol)) & _) Hc Ha0 Ha1.
  pose proof (region_facts _ _ _ _ _ _ _ _ _ _ _ HH) as (Hsp & _).
  apply (cell_agree_out s6_segs (GDo (ds_strm X)) m1 m a w v HAG); [| lia | lia | exact Hc].
  intros x Hx Hin. exact (out_GDo _ _ _ _ _ _ _ _ _ _ _ HH _ x Hin ltac:(lia) ltac:(lia)).
Qed.

End Glue.
End FXG.
