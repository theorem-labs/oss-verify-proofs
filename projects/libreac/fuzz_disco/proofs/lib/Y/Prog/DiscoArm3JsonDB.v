(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YChd.v, with its module paths and module names changed; 759 of its 797 lines of code are new or changed and 507 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoYEntExit.v, with its module names changed; 648 of its 702 lines of code are new or changed and 743 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0p YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YC44 YC1h YC1i YCjr YCj1 YCja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoArm3TailK DiscoYEntBodyStmt DiscoArm3 DiscoArm3JsonModel DiscoArm3JsonCut
DiscoArm3JsonDDefs DiscoArm3JsonMs DiscoArm3JsonMsStep DiscoArm3JsonK.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv disco_jscalar_model disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require slot_ser_defs slot_ser_tokb.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition JDB_STOP : Z := 0x16cc.
Definition JDB_BX : sv := SOff 19 0.
Definition jdb_rB : YP09.region := YP09.mkRegion (Some 33%nat) 0 2 0 0 [YP09.mkChunk 1 (CVal 1 (SLit 123))].
Definition jdb_atoms : list (nat * afact) :=
  [(19%nat, mkAF SB SB 0); (20%nat, mkAF 32 32 0); (33%nat, mkAF 4096 (2 ^ 47 - 16) 0)].
Definition jdb_alias : sv * sv := (SAlu ALU_ADD (SOff 24 0) (SOff 11 0), SOff 33 0).
Definition jdb_lt : acond := mkAC BC_LTU (SOff 11 1) (SOff 26 0).
Definition jdb_ge : acond := mkAC BC_GEU (SOff 25 0) (SOff 11 1).
Definition jdb_ssA : sstate :=
  mkSS MID_OFF sr_atoms [jdb_rB] None (mkFacts jdb_atoms [jdb_lt; jdb_ge] [jdb_alias]).
Definition jdb_SH : list shent := [mkSHE 33 0 2].
Definition jdb_acs : list YP09.chunk := [YP09.mkChunk 232 (CVal 8 (SOff 563 0))].
Definition jdb_fa : list (nat * afact) :=
  [(553%nat, mkAF 0 7 0); (563%nat, mkAF (2 ^ 64 - 2 ^ 48) (2 ^ 64 - 1) 0)].
Definition jdb_rsB : smem :=
  [YP09.mkRegion (Some AT_STK) (-104) 0 0 0 dsave_chunks;
   YP09.mkRegion (Some AT_A) 0 472 0 0 (dslot_chunks ++ jdb_acs);
   YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 0 0 (dfhdr_chunks ++ []);
   fshadow_region AT_SH DFRAME_CLASS 4 22 (dsh_chunks dsh_scr);
   got_regionP; bcell_regionP 32].

Lemma jdb_subregion : forall b lo hi wlo whi wlo' whi' cs,
  whi' <= wlo' \/ (wlo <= wlo' /\ whi' <= whi) ->
  subregion (YP09.mkRegion b lo hi wlo' whi' cs) (YP09.mkRegion b lo hi wlo whi cs).
Proof.
  intros b lo hi wlo whi wlo' whi' cs Hw. unfold subregion.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact Hw|]. intros c Hc. exact Hc.
Qed.

Lemma jdb_subrefl : forall r, subregion r r.
Proof. intros [b lo hi wlo whi cs]. apply jdb_subregion. lia. Qed.

Lemma jdb_rsB_sub : submem jdb_rsB (d_kregions dsh_scr jdb_acs [] ++ []).
Proof.
  unfold jdb_rsB, d_kregions, fshadow_region. rewrite app_nil_r.
  apply submem_keep; [apply jdb_subrefl|].
  apply submem_keep; [apply jdb_subregion; lia|].
  apply submem_keep; [apply jdb_subregion; lia|].
  apply submem_keep; [apply jdb_subregion; unfold DFRAME_SH; lia|].
  apply submem_keep; [apply jdb_subrefl|].
  apply submem_keep; [apply jdb_subrefl|].
  apply submem_nil.
Qed.

Lemma jdb_slot24_len : forall buf vpad t, length vpad = 4%nat -> length (slot_ser_defs.slot24 buf vpad t) = 24%nat.
Proof.
  intros buf vpad t L. unfold slot_ser_defs.slot24. destruct (_ =? 0); [apply repeat_length|].
  rewrite !length_app, L. reflexivity.
Qed.

Lemma jdb_concat_len : forall {A} (f : A -> list byte) L l, Forall (fun x => length (f x) = L) l ->
  length (concat (map f l)) = (L * length l)%nat.
Proof.
  intros A f L l H. induction H as [|x l Hx H IH]; cbn [map concat length]; [lia|].
  rewrite length_app, Hx, IH. lia.
Qed.

Lemma jdb_objs_len : forall buf vpad os, length vpad = 4%nat -> Forall (fun o => length o = 6%nat) os ->
  length (slot_ser_defs.objs_bytes buf vpad os) = (144 * length os)%nat.
Proof.
  intros buf vpad os L H. unfold slot_ser_defs.objs_bytes. apply jdb_concat_len. eapply Forall_impl; [|exact H].
  intros o Ho. unfold slot_ser_defs.obj_bytes. rewrite (jdb_concat_len _ 24); [rewrite Ho; reflexivity|].
  apply Forall_forall. intros t _. apply jdb_slot24_len. exact L.
Qed.

Lemma jdb_obj_empty : forall buf vpad, slot_ser_defs.obj_bytes buf vpad jobj_empty = repeat (Z_to_bv 8 0) 144.
Proof. intros buf vpad. reflexivity. Qed.

Lemma jdb_objs_app_empty : forall buf vpad l,
  slot_ser_defs.objs_bytes buf vpad (l ++ [jobj_empty]) =
  slot_ser_defs.objs_bytes buf vpad l ++ repeat (Z_to_bv 8 0) 144.
Proof.
  intros buf vpad l. unfold slot_ser_defs.objs_bytes. rewrite map_app, concat_app.
  cbn [map concat]. rewrite app_nil_r. rewrite jdb_obj_empty. reflexivity.
Qed.

Lemma jdb_map_zeros : map (fun b : byte => bv_unsigned b) (repeat (Z_to_bv 8 0) 144) = repeat 0 144.
Proof. reflexivity. Qed.

Lemma jdb_len6 : length jobj_empty = 6%nat.
Proof. reflexivity. Qed.

Lemma jdb_getr_kept : forall rg rg' (r : bv 5), aregs_preserved rg rg' -> acallee_saved (bv_unsigned r) ->
  getr rg' r = getr rg r.
Proof.
  intros rg rg' r HP Hr. pose proof (HP _ Hr) as E. rewrite Z_to_bv_bv_unsigned in E. exact E.
Qed.

Lemma jdb_cs : forall z, (z = 2 \/ z = 3 \/ z = 4 \/ z = 8 \/ z = 9 \/ (18 <= z <= 27)) -> acallee_saved z.
Proof. intros z H. exact H. Qed.

Lemma JDBV21 : bv_unsigned (21%bv : bv 5) = 21. Proof. vm_compute. reflexivity. Qed.
Lemma JDBV22 : bv_unsigned (22%bv : bv 5) = 22. Proof. vm_compute. reflexivity. Qed.
Lemma JDBV23 : bv_unsigned (23%bv : bv 5) = 23. Proof. vm_compute. reflexivity. Qed.

Lemma jdb_mul_U : forall (E : env) (nf nc : nat) (fb cnt : Z),
  ew E nf = Z_to_bv 64 fb -> ew E nc = Z_to_bv 64 cnt ->
  0 <= fb < 2 ^ 64 -> 0 <= cnt -> 0 <= fb + 384 + 144 * cnt < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SOff nf 384) (SMd M_MUL (SOff nc 0) (SLit 144))) = fb + 384 + 144 * cnt.
Proof.
  intros E nf nc fb cnt Hf Hc Hfb Hcnt Hsum.
  rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom_off E nf fb 384 Hf Hfb ltac:(lia)).
  rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom E nc cnt Hc ltac:(lia)), U_SLit.
  change (zcanon 144) with 144. rewrite (zcanon_id (cnt * 144)) by (unfold M64; lia).
  rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Definition jdb_R (cx : dcx) (ii cnt : Z) : bvmap 5 word -> Prop :=
  fun regs => getr regs 21 = w64 ii /\ getr regs 22 = w64 cnt /\ getr regs 23 = w64 (jcur cx cnt).

Definition jdb_X (cx : dcx) (T1 : list byte) (now buf p count : Z) (fin : Z * list jobj)
  (acc : list jobj) (cur : jobj) (vpad : list byte) : world SEGS -> (word -> option byte) -> Prop :=
  fun W m => jfin_ok T1 now fin /\ 0 <= p /\ p + 2 < a3_r T1 now /\ 0 <= count <= 7 /\
    length acc = Z.to_nat count /\ length vpad = 4%nat /\
    jobjs_from (a3_text T1 now) fin (p + 2) (count + 1) (acc ++ [cur]) /\
    Forall (fun o : jobj => length o = 6%nat) (acc ++ [cur]) /\
    0 <= d_FB cx /\ d_FB cx + 4096 <= d_A cx - ESTACK /\ d_A cx + 472 <= d_S cx /\ d_S cx <= 2 ^ 47 /\
    garr8 SEGS (rd W m) (d_A cx + 444) (map (fun b : byte => bv_unsigned b) vpad) /\
    garr8 SEGS (rd W m) (d_obj cx OO)
      (map (fun b : byte => bv_unsigned b) (slot_ser_defs.objs_bytes buf vpad (acc ++ [cur]))).

Lemma jdb_R_pres : forall cx ii cnt rg rg', aregs_preserved rg rg' -> jdb_R cx ii cnt rg -> jdb_R cx ii cnt rg'.
Proof.
  intros cx ii cnt rg rg' HP (A21 & A22 & A23).
  split; [rewrite (jdb_getr_kept rg rg' 21 HP ltac:(apply jdb_cs; rewrite JDBV21; lia)); exact A21|].
  split; [rewrite (jdb_getr_kept rg rg' 22 HP ltac:(apply jdb_cs; rewrite JDBV22; lia)); exact A22|].
  rewrite (jdb_getr_kept rg rg' 23 HP ltac:(apply jdb_cs; rewrite JDBV23; lia)); exact A23.
Qed.

Lemma jdb_X_kept : forall cx T1 now buf p count fin acc cur vpad W1 m1 W2 m2,
  jdb_X cx T1 now buf p count fin acc cur vpad W1 m1 ->
  ms_kept cx (count + 1) W1 m1 W2 m2 ->
  jdb_X cx T1 now buf p count fin acc cur vpad W2 m2.
Proof.
  intros cx T1 now buf p count fin acc cur vpad W1 m1 W2 m2 HX (-> & HK).
  destruct HX as (HF & Hp & Hpr & Hc7 & Hla & Hvp & HFROM & H6 & GF0 & GFA & GAS & GS47 & M444 & MOO).
  unfold ESTACK in GFA.
  assert (HjcE : jcur cx (count + 1) = d_FB cx + 240 + 144 * (count + 1))
    by (unfold jcur, d_obj, dobj_off; lia).
  assert (HOE : d_obj cx OO = d_FB cx + 240) by (unfold d_obj, dobj_off; lia).
  assert (KVa : forall a, d_A cx <= a < d_A cx + 472 ->
    aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m1 a).
  { intros a Ha. apply HK; [lia | unfold ESTACK; rewrite HjcE; lia]. }
  assert (KVo : forall a, d_FB cx + 240 <= a < d_FB cx + 240 + 144 * (count + 1) ->
    aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m1 a).
  { intros a Ha. apply HK; [lia | unfold ESTACK; rewrite HjcE; lia]. }
  split; [exact HF|]. split; [exact Hp|]. split; [exact Hpr|]. split; [exact Hc7|].
  split; [exact Hla|]. split; [exact Hvp|]. split; [exact HFROM|]. split; [exact H6|].
  split; [exact GF0|]. split; [unfold ESTACK; lia|]. split; [exact GAS|]. split; [exact GS47|].
  split.
  { apply (garr8_frame SEGS (rd W1 m1) (rd W1 m2) (d_A cx + 444) _ M444).
    intros a Ha. rewrite length_map, Hvp in Ha. cbn [Z.of_nat] in Ha.
    apply (mbyte_of_aview SEGS). apply KVa. lia. }
  apply (garr8_frame SEGS (rd W1 m1) (rd W1 m2) (d_obj cx OO) _ MOO).
  intros a Ha. rewrite length_map, (jdb_objs_len buf vpad (acc ++ [cur]) Hvp H6) in Ha.
  rewrite length_app, Hla in Ha. cbn [length] in Ha. rewrite HOE in Ha.
  apply (mbyte_of_aview SEGS). apply KVo. lia.
Qed.

Lemma jdb_pi_of_call : forall (fq : YK11.FPState) E ss ms t,
  st_ok (fx := fq) SEGS E (setpc ss t) ms ->
  st_ok_pi (fx := fq) SEGS VAL E (mkSS (t - BASE) (ss_regs ss) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
  intros fq E ss ms t (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts setpc] in H2, H4, H7, H8, H9.
  unfold st_ok_pi, abs_ss, st_ok.
  cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem
       ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts setpc].
  replace (BASE + (t - BASE)) with t by lia.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  split; [exact H5|]. split; [exact H6|]. split; [exact H7|]. split; [exact H8 | exact H9].
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis PAL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis DSEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DFACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DLAND : d_land_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis AMEMSET : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OSet (SIGMA AS___asan_memset).
Hypothesis DBRT : d_body_rt_stmt B.

Lemma jdb_shent : forall ly S (W : world SEGS) mem md (E : env) (Bx : sv) (q : nat) (bp len lo hi : Z),
  AR SEGS B ly S W mem md -> In (bp, len) (ablocks B ly S) ->
  U E Bx = SHADOW_OFF -> 0 <= lo <= hi ->
  bp <= U E (SOff q 0) + lo -> U E (SOff q 0) + hi <= bp + req_size len ->
  shent_ok SEGS Bx E (rd W mem) (mkSHE q lo hi).
Proof.
  intros ly S W mem md E Bx q bp len lo hi HAR Hin HB Hlh Hlo Hhi.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H4096 & Hceil & Happ & _ & _ & _).
  eapply (shent_ok_of_range SEGS (w_H W) mem E Bx q bp (req_size len) (U E (SOff q 0)) lo hi).
  - exact (range_addressable_of_block SEGS B LAWS ly S W mem md bp len bp (req_size len) HAR Hin
             ltac:(lia) ltac:(lia)).
  - exact HB.
  - reflexivity.
  - lia.
  - lia.
  - intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
Qed.

Theorem jd_B : jd_B_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op W0 c0 T0 T1 buf fin p cur count acc vpad W c Hb44 Hfrom HM.
destruct HM as (HFROM & fq & ly3 & S3 & regs & mem3 & md3 & k & accm & -> & Hfrm0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo &
  Hacc & HP).
destruct HP as (Hi & Hn & Hnow & HrL & (R26 & R24 & R25 & R10 & R11 & R22) & (Hsp1 & Htab & Hbuf & HXm) & Hsp0 & Hbody).
destruct HXm as (HFIN & Hp0 & Hp1r & Hcnt & Hlen & HAF & Hcur6 & Hcurin & HJM).
destruct HJM as (Hvpad & M444 & MOO & M6).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj Hbase (conj HJ Hfrs)).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & GFpres & GSHpres & GSTKpres & HAR3 & HFin3 & EFA3 & EFL3).
pose proof alloc_ceiling_value as Hceil0.
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
pose proof Hbody as (Tb & Gb & Lkb & Hb & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFFF & HGEO & HCAN & HSTKF & HAWRF).
pose proof HFRM as (E & HdE & Hregs & Hflag & H184 & H120 & H136 & H376 & H280 & H232 & H264).
pose proof HBLK as (HPerm0 & _ & _ & HOFFb).
pose proof HrL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs19 & Rs18 & Rs20 & Rs27).
pose proof HFIN as (Hjr & Hfinb & HNWS & HTLEN & HTOKS).
pose proof Hbuf as (Hcap & HGARR).
assert (Hinbuf : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HPerm0)). unfold a3_xb. cbn [app]. left. reflexivity. }
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinbuf) as (Hbuf16 & Hbuf4096 & Hbufceil & Hbufapp & _ & _ & _).
assert (Hreq : req_size (Z.max (slot_ser_defs.ser_cap op) 1) = Z.max (slot_ser_defs.ser_cap op) 1).
{ unfold req_size. destruct (Z.eqb_spec (Z.max (slot_ser_defs.ser_cap op) 1) 0); lia. }
rewrite Hreq in Hbufceil, Hbufapp.
assert (Hrle : a3_r T1 now <= 969) by (unfold a3_r; lia).
pose proof (jobjs_from_step (a3_text T1 now) fin (p + 2) (count + 1) (acc ++ [cur]) Hfrom) as (Hb123 & _).
pose proof (at_byte_true _ _ _ Hb123) as (Hlt123 & Hby123).
assert (Hp2r : p + 2 < a3_r T1 now) by (unfold a3_r, jlen in *; lia).
remember (Eimg (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 (buf + (p + 1))])) as E0 eqn:HE0.
assert (HEI0 : img_env VAL A_LIM E0) by (rewrite HE0; apply Eimg_env).
assert (EE0 : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E0 nn = getr regs r)
  by (intros nn r Hr; rewrite HE0; apply ew_Eimg_Ereg_nat; exact Hr).
assert (ENB : ew E0 33 = Z_to_bv 64 (buf + (p + 1))).
{ rewrite HE0, Eimg_low by (unfold A_TEXT; lia). change 33%nat with (32 + 1)%nat. rewrite ew_Ereg_extra. reflexivity. }
assert (U19 : U E0 (SOff 19 0) = SHADOW_OFF).
{ apply (U_atom E0 19%nat SHADOW_OFF); [rewrite (EE0 19%nat 19%bv eq_refl); exact Rs19 | unfold SHADOW_OFF; lia]. }
assert (U11 : U E0 (SOff 11 0) = p + 1).
{ apply (U_atom E0 11%nat (p + 1)); [rewrite (EE0 11%nat 11%bv eq_refl); exact R11 | lia]. }
assert (U26 : U E0 (SOff 26 0) = a3_r T1 now).
{ apply (U_atom E0 26%nat (a3_r T1 now)); [rewrite (EE0 26%nat 26%bv eq_refl); exact R26 | lia]. }
assert (U24 : U E0 (SOff 24 0) = buf).
{ apply (U_atom E0 24%nat buf); [rewrite (EE0 24%nat 24%bv eq_refl); exact R24 | lia]. }
assert (U33 : U E0 (SOff 33 0) = buf + (p + 1)).
{ apply (U_atom E0 33%nat (buf + (p + 1))); [exact ENB | lia]. }
assert (U25 : U E0 (SOff 25 0) = 2 ^ 64 - 1 - buf).
{ apply (U_atom E0 25%nat (2 ^ 64 - 1 - buf)); [rewrite (EE0 25%nat 25%bv eq_refl), R25; apply jk_lnot; lia | lia]. }
assert (B33 : base_val E0 (Some 33%nat) = buf + (p + 1)).
{ cbn [base_val]. rewrite ENB. apply unsigned_lit_small. lia. }
assert (Hbyp2 : val_mem SEGS (rd W mem3) (buf + (p + 2)) 1 123).
{ destruct (jk_byte W mem3 buf (a3_text T1 now ++ [0]) (p + 2) HGARR
    ltac:(rewrite length_app; cbn [length]; unfold a3_r in *; lia)) as (Hv & _).
  rewrite (jk_nth_app (a3_text T1 now) (p + 2) ltac:(unfold jlen, a3_r in *; lia)) in Hv.
  rewrite Hby123 in Hv. exact Hv. }
assert (HG : facts_ok E0 (mkFacts jdb_atoms [jdb_lt; jdb_ge] [jdb_alias])).
{ unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [|split].
  - unfold jdb_atoms. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (EE0 19%nat 19%bv eq_refl), (EE0 20%nat 20%bv eq_refl), ENB.
    rewrite Rs19, Rs20. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF, SB in *; lia).
    rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB, SHADOW_OFF. repeat split; lia.
  - cbn [conds_ok]. unfold jdb_lt, jdb_ge, acond_ok. cbn [ac_c ac_a ac_b].
    assert (U111 : U E0 (SOff 11 1) = p + 1 + 1)
      by (apply (U_atom_off E0 11%nat (p + 1) 1); [rewrite (EE0 11%nat 11%bv eq_refl); exact R11 | lia | lia]).
    rewrite branch_ltu_U, branch_geu_U, U111, U26, U25.
    split; [apply Z.ltb_lt; lia|]. split; [apply negb_true_iff, Z.ltb_ge; lia | exact I].
  - unfold jdb_alias. cbn [alias_ok]. split; [|exact I].
    rewrite (denot_lit_U E0 (SAlu ALU_ADD (SOff 24 0) (SOff 11 0))), (denot_lit_U E0 (SOff 33 0)).
    f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite U11, U24, U33. apply zcanon_id. unfold M64. lia. }
assert (HROK : Forall (region_ok SEGS E0 (rd W mem3)) [jdb_rB]).
{ constructor; [|constructor].
  unfold region_ok, jdb_rB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite B33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E0 _ (buf + (p + 1)) 1 1 (SLit 123) 123).
  - cbn [sv_denot]. reflexivity.
  - cbn [Z.of_N]. lia.
  - cbn [Z.of_N]. lia.
  - replace (buf + (p + 1) + 1) with (buf + (p + 2)) by lia. exact Hbyp2. }
assert (HSpA0 : st_ok_pi (fx := fq) SEGS VAL E0 jdb_ssA
  (restrict (w_H W) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + MID_OFF)) mem3 (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - rewrite HE0. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - exact HROK.
  - cbn [pairwise_disjoint all_disjoint]. repeat split.
  - exact HG. }
pose proof (at_byte_true _ _ _ Hb44) as (_ & Hby44).
assert (HR10 : getr regs 10 = Z_to_bv 64 44) by (rewrite R10, Hby44; reflexivity).
pose proof (st_ok_pi_pin_reg' E0 jdb_ssA _ (10%bv : bv 5) 44 HSpA0
  ltac:(cbn [ms_regs restrict YK11.mkst]; exact HR10) ltac:(vm_compute; reflexivity)) as HSpA.
norm_ss HSpA. clear HSpA0.
assert (SHOKA : sh_ok SEGS JDB_BX jdb_SH E0 (rd W mem3)).
{ constructor; [|constructor].
  apply (jdb_shent ly3 S3 W mem3 md3 E0 JDB_BX 33%nat buf (Z.max (slot_ser_defs.ser_cap op) 1) 0 2 HAR3 Hinbuf);
    [exact U19 | lia | rewrite U33; lia | rewrite U33, Hreq; lia]. }
pose proof (paj_run_to (fx := fq) (PI := PI) B LAWS) as RUNTO.
unfold cfg_at, w64.
paj_run_to_tok RUNTO HSpA HJ SHOKA Bspan JDB_STOP.
{ lazymatch goal with |- awr_ok ?Ey ?rs ?a1 ?b1 ?c1 ?d1 ?e1 ?f1 ?g1 =>
    let rs' := eval vm_compute in rs in change (awr_ok Ey rs' a1 b1 c1 d1 e1 f1 g1) end.
  intros a Ha. exfalso. revert Ha. apply jk_nowin. vm_compute. reflexivity. }
assert (EmemA : ms_mem ms = mem3).
{ apply functional_extensionality. intros x. apply HF. apply jk_nowin. vm_compute. reflexivity. }
rewrite EmemA in HJ.
prreg HSpA (2%bv : bv 5) Q2. prreg HSpA (3%bv : bv 5) Q3. prreg HSpA (4%bv : bv 5) Q4.
prreg HSpA (8%bv : bv 5) Q8. prreg HSpA (9%bv : bv 5) Q9. prreg HSpA (18%bv : bv 5) Q18.
prreg HSpA (19%bv : bv 5) Q19. prreg HSpA (20%bv : bv 5) Q20. prreg HSpA (22%bv : bv 5) Q22.
prreg HSpA (24%bv : bv 5) Q24. prreg HSpA (25%bv : bv 5) Q25. prreg HSpA (26%bv : bv 5) Q26.
prreg HSpA (27%bv : bv 5) Q27.
rewrite (EE0 2%nat 2%bv eq_refl) in Q2. rewrite (EE0 3%nat 3%bv eq_refl) in Q3.
rewrite (EE0 4%nat 4%bv eq_refl) in Q4. rewrite (EE0 8%nat 8%bv eq_refl) in Q8.
rewrite (EE0 9%nat 9%bv eq_refl) in Q9. rewrite (EE0 18%nat 18%bv eq_refl) in Q18.
rewrite (EE0 19%nat 19%bv eq_refl) in Q19. rewrite (EE0 20%nat 20%bv eq_refl) in Q20.
rewrite (EE0 22%nat 22%bv eq_refl) in Q22. rewrite (EE0 24%nat 24%bv eq_refl) in Q24.
rewrite (EE0 25%nat 25%bv eq_refl) in Q25. rewrite (EE0 26%nat 26%bv eq_refl) in Q26.
rewrite (EE0 27%nat 27%bv eq_refl) in Q27.
assert (R121 : getr (ms_regs ms) 21 = w64 (p + 2)).
{ lazymatch type of HSpA with st_ok_pi _ _ ?Ex ?ssx _ =>
    rewrite (st_ok_pi_restrict_reg (w_H W) Ex ssx ms (21%bv : bv 5) HSpA);
    let e := eval vm_compute in (sr_get (ss_regs ssx) (21%bv : bv 5)) in
    change (sr_get (ss_regs ssx) (21%bv : bv 5)) with e;
    assert (EXa : ew Ex 11 = Z_to_bv 64 (p + 1))
      by (cbn [ew ewset Nat.eqb]; rewrite (EE0 11%nat 11%bv eq_refl); exact R11);
    rewrite denot_lit_U, (U_atom_off Ex 11%nat (p + 1) 1 EXa ltac:(lia) ltac:(lia));
    clear EXa
  end. unfold w64. f_equal. lia. }
assert (HrL1 : d_rL B cx (ms_regs ms)).
{ split; [unfold spZ; rewrite Q2; exact Rsp|].
  split; [rewrite Q3; exact Rgp|]. split; [rewrite Q4; exact Rtp|]. split; [rewrite Q8; exact Rs0|].
  split; [rewrite Q9; exact Rs1|]. split; [rewrite Q19; exact Rs19|]. split; [rewrite Q18; exact Rs18|].
  split; [rewrite Q20; exact Rs20|]. rewrite Q27; exact Rs27. }
assert (R122 : getr (ms_regs ms) 22 = w64 count) by (rewrite Q22; exact R22).
assert (R124 : getr (ms_regs ms) 24 = w64 buf) by (rewrite Q24; exact R24).
assert (R125 : getr (ms_regs ms) 25 = w64 (Z.lnot buf)) by (rewrite Q25; exact R25).
assert (R126 : getr (ms_regs ms) 26 = w64 (a3_r T1 now)) by (rewrite Q26; exact R26).
set (vals := jk_vals (ms_regs ms) [Z_to_bv 64 (dnot (d_obj cx OO))]).
assert (EV553 : ew (d_env cx E vals) 553 = w64 count).
{ change 553%nat with (AT_X + 22)%nat. unfold vals. rewrite jk_x by lia. exact R122. }
assert (EV563 : ew (d_env cx E vals) 563 = Z_to_bv 64 (dnot (d_obj cx OO))).
{ change 563%nat with (AT_X + (32 + 0))%nat. unfold vals. rewrite jk_xe by (cbn; lia). reflexivity. }
assert (HdnOO : 2 ^ 64 - 2 ^ 48 <= dnot (d_obj cx OO) < 2 ^ 64) by (unfold dnot, d_obj, dobj_off; lia).
assert (HAT : atoms_ok (d_env cx E vals) jdb_fa).
{ unfold jdb_fa. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite EV553, EV563. unfold w64. rewrite !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat split; lia. }
assert (HCTXB : exists mdx, d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 mdx k)
  by (eexists; exact (conj Hbase (conj HJ Hfrs))).
destruct HCTXB as (mdB & HCTXB).
assert (Hacs : Forall (YP09.chunk_ok SEGS (d_env cx E vals) (rd W mem3) (d_A cx)) jdb_acs).
{ unfold jdb_acs. apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ (d_A cx) 232 8%N (SOff 563 0) (dnot (d_obj cx OO)));
    [rewrite (jk_den0 _ 563 (dnot (d_obj cx OO)) EV563 ltac:(lia)); reflexivity
    | cbn; lia | cbn; lia | exact H232]. }
pmkst HSpA.
rewrite EmemA.
pose proof (DSEAT LAWS PAL fq cx dsh_scr ly3 S3 W (ms_regs ms) mem3 mdB k E JDB_STOP jk_sr vals
  jdb_acs [] [] (d_facts jdb_fa []) HCTXB HdE Hregs Hflag
  (jk_regs_ok B cx E (ms_regs ms) _ HdE HrL1)
  (DFACTS LAWS cx ly3 S3 W mem3 mdB k E vals jdb_fa [] HCTXB HdE HAT I)
  Hacs (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0B.
pose proof (st_ok_pi_submem _ _ _ jdb_rsB HS0B jdb_rsB_sub ltac:(vm_compute; reflexivity)) as HSB.
clear HS0B.
pose proof HdE as (HER & HE32 & HEIE & HE60 & HE516 & HE529).
remember (d_env cx E vals) as E1 eqn:HE1 in HSB, EV553, EV563, HAT.
assert (E1sh : ew E1 529 = Z_to_bv 64 (shadow_addr (d_FB cx))).
{ rewrite HE1, d_env_old by (cbv; lia). exact HE529. }
assert (E1a : ew E1 60 = Z_to_bv 64 (d_A cx)).
{ rewrite HE1, d_env_old by (cbv; lia). exact HE60. }
assert (E1f : ew E1 516 = Z_to_bv 64 (d_FB cx)).
{ rewrite HE1, d_env_old by (cbv; lia). exact HE516. }
assert (E1s : ew E1 2 = Z_to_bv 64 (d_S cx)).
{ rewrite HE1, d_env_old by (cbv; lia). rewrite (HER 2%nat 2%bv eq_refl). unfold d_S, spZ.
  rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (E132 : ew E1 32 = Z_to_bv 64 SHADOW_OFF).
{ rewrite HE1, d_env_old by (cbv; lia). exact HE32. }
assert (HEI1 : img_env VAL A_LIM E1) by (rewrite HE1; exact (proj1 (proj2 (proj2 (d_E_env cx E vals HdE))))).
assert (HdE1 : d_E cx E1) by (rewrite HE1; apply d_E_env; exact HdE).
assert (HFL1 : ew E1 AT_FL = Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx))) by (rewrite HE1; apply d_env_fl).
norm_ss HSB.
assert (SHOKB : sh_ok SEGS (SOff 32 0) (@nil shent) E1 (rd W mem3)) by constructor.
pose proof (paj_run (fx := fq) (PI := PI) B LAWS) as RUN.
pose proof YCbq.asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSHr : kLowMemEnd <= shadow_addr (d_FB cx) /\ shadow_addr (d_FB cx) + 512 <= kHighShadowEnd).
{ pose proof (YCbq.shadow_addr_bounds (d_FB cx) ltac:(lia)) as QS1.
  pose proof (YCbq.shadow_addr_bounds (d_FB cx + 4096) ltac:(lia)) as QS2.
  pose proof (YCbq.shadow_range_end (d_FB cx) 4096 ltac:(lia)) as QS3. change (4096 / 8) with 512 in QS3. lia. }
paj_run_tok RUN HSB HJ SHOKB (0, 0).
{ lazymatch goal with |- awr_ok ?Ey ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ey rs' stk sp0 fpp b0 bc lyy own) end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  eapply (YCbq.awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 529%nat (shadow_addr (d_FB cx))).
  - reflexivity.
  - rewrite E1sh. apply unsigned_lit_small. unfold shadow_addr, SHADOW_OFF. lia.
  - cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right. right. right.
    exists DFRAME_CLASS, (c_fpos cx). split; [left; reflexivity|]. right.
    unfold in_zr. cbn [fst snd]. rewrite EFA3. change (fs_frame_bytes DFRAME_CLASS / 8) with 512. lia.
  - apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HFr0 with frame_of _ ?rsw _ _ =>
  assert (HWR : forall a, in_wrange E1 rsw a ->
    shadow_addr (d_FB cx) + 4 <= a < shadow_addr (d_FB cx) + 22) end.
{ intros a (r & Hin & Ha).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    try lia.
  rewrite E1sh, unsigned_lit_small in Ha by (unfold shadow_addr, SHADOW_OFF; lia). lia. }
assert (HK1 : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr (d_FB cx) + 4 <= a < shadow_addr (d_FB cx) + 22) ->
  aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem3 a).
{ intros a Ha Hn'. unfold aview, mbyte. rewrite (HFr0 (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by lia. intros Hw. exact (Hn' (HWR a Hw)). }
assert (HKA : forall a, 0 <= a < 2 ^ 64 -> (a < kLowMemEnd \/ kHighShadowEnd <= a) ->
  aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem3 a).
{ intros a Ha Hz. apply HK1; [exact Ha | lia]. }
assert (HAPP : forall lo len a, in_app lo len -> lo <= a < lo + len ->
  aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem3 a).
{ intros lo len a Hap Ha. apply HKA; zlia. }
assert (HVM : forall off v, 0 <= off -> off + 8 <= 472 ->
  val_mem SEGS (rd W mem3) (d_A cx + off) 8 v -> val_mem SEGS (rd W (ms_mem ms0)) (d_A cx + off) 8 v).
{ intros off v Ho1 Ho2 Hv. apply (val_mem_kept SEGS (w_H W) (w_H W) mem3 (ms_mem ms0)); [|exact Hv].
  intros kk Hkk. cbn in Hkk. apply HKA; zlia. }
assert (HPR : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) (ms_mem ms0) a)
  by (intros a Ha; exact (jk_apres_grow _ _ _ _ HG1 Ha)).
pose proof (jdb_pi_of_call fq E1 _ _ _ HSB) as HSpiB.
assert (HCTXm : exists mdx, d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms0) mdx k)
  by (eexists; exact (conj Hbase (conj HJ Hfrs))).
destruct HCTXm as (mdC & HCTX0).
assert (HSL0 : d_hslots cx h W (ms_mem ms0)).
{ apply (d_hslots_kept cx h W W mem3 (ms_mem ms0));
    [intros a Ha; apply HKA; zlia | exact (d_hslots_of_frame cx h dsh_scr W mem3 HFRM)]. }
pose proof (d_land_hs B MT XM_LIB RLO RHI tfib_K DLAND LAWS FFL fq cx h dsh_scr ly3 S3 W mdC k
  E1 _ ms0 HCTX0 HdE1 HFL1 HSpiB ltac:(vm_compute; reflexivity) HSL0) as (HFRM0 & HSHD0).
assert (Hro : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> 0 <= a < kLowMemEnd).
{ intros a [(s & Hs & _ & Hsa) | Hr]; apply pa_segs_low; [exists s; split; [exact Hs | exact Hsa] | exact (pa_relro_img a Hr)]. }
assert (HhA : in_app h (req_size HUNT_SIZE)).
{ assert (Hinh : In (h, HUNT_SIZE) (ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HPerm0)). apply in_or_app. right. left. reflexivity. }
  exact (proj1 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinh))))). }
assert (HpA : 0 < c_n cx -> in_app (c_p cx) (req_size (c_n cx))).
{ intros Hc. pose proof Hbase as ((HPRE & _ & _ & _ & Hpn & _) & _). pose proof HPRE as (HAR0 & _).
  destruct Hpn as [(Hn0 & _) | (_ & Hin0)]; [lia|].
  exact (proj1 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hin0))))). }
assert (HBODY0 : d_body B cx h n (a3_xb buf op) dsh_scr ly3 S3 W (ms_mem ms0)).
{ apply (DBRT cx h n n (a3_xb buf op) dsh_scr dsh_scr ly3 S3 W mem3 (ms_mem ms0) (d_S cx) (d_S cx)
    (fun a => shadow_addr (d_FB cx) + 4 <= a < shadow_addr (d_FB cx) + 22) Hbody).
  - unfold LLVMF_STK. lia.
  - lia.
  - intros a Ha. right. intros Hr.
    unfold d_rdset, d_objr, d_obj, dobj_off, dobj_size in Hr.
    change (req_size HUNT_SIZE) with 480 in HhA. unfold HUNT_SIZE in Hr.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HhA, Hbufapp.
    destruct Hr as [Hr | [Hr | [Hr | [Hr | [Hr | [(Hcn & Hr) | [Hr | Hr]]]]]]].
    + zlia.
    + zlia.
    + zlia.
    + zlia.
    + zlia.
    + specialize (HpA Hcn). unfold req_size in HpA. destruct (Z.eqb_spec (c_n cx) 0); [lia|].
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HpA. zlia.
    + specialize (Hro a (proj1 Hr)). zlia.
    + unfold FF_canary in Hr. zlia.
  - intros a Ha Hn'. exact (HK1 a Ha Hn').
  - intros a _ Ha. exact (HPR a Ha).
  - exact HFRM0.
  - exact HSHD0.
  - lia. }
assert (GEO1 : 0 <= d_FB cx) by lia.
assert (GEO2 : d_FB cx + 4096 <= d_A cx - ESTACK) by (unfold ESTACK; lia).
assert (GEO3 : d_A cx + 472 <= d_S cx) by lia.
assert (GEO4 : d_S cx <= 2 ^ 47) by lia.
pose proof Hsp1 as ((H208 & H320) & H192 & H200).
assert (HXB : jdb_X cx T1 now buf p count fin acc cur vpad W (ms_mem ms0)).
{ split; [exact HFIN|]. split; [exact Hp0|]. split; [exact Hp2r|]. split; [exact Hcnt|].
  split; [exact Hlen|]. split; [exact Hvpad|]. split; [exact Hfrom|]. split; [exact M6|].
  split; [exact GEO1|]. split; [exact GEO2|]. split; [exact GEO3|]. split; [exact GEO4|].
  split.
  { apply (garr8_frame SEGS (rd W mem3) (rd W (ms_mem ms0)) (d_A cx + 444) _ M444).
    intros a Ha. rewrite length_map, Hvpad in Ha. cbn [Z.of_nat] in Ha.
    apply (mbyte_of_aview SEGS). apply HKA; zlia. }
  apply (garr8_frame SEGS (rd W mem3) (rd W (ms_mem ms0)) (d_obj cx OO) _ MOO).
  intros a Ha. rewrite length_map, (jdb_objs_len buf vpad (acc ++ [cur]) Hvpad M6) in Ha.
  rewrite length_app, Hlen in Ha. cbn [length] in Ha.
  apply (mbyte_of_aview SEGS). apply (HAPP (d_FB cx) 4096). exact GFapp.
  unfold d_obj, dobj_off in Ha. lia. }
assert (HTABB : a3_tab cx now T0 T1 W (ms_mem ms0)).
{ destruct Htab as (Hage & HT1). split; [exact Hage|].
  destruct Hage as (removed & Hm & Hpost). pose proof (proj1 Hpost) as HL1.
  apply (garr8_frame SEGS (rd W mem3) (rd W (ms_mem ms0)) (d_obj cx OT) _ HT1).
  intros a Ha. rewrite length_map, HL1 in Ha.
  apply (mbyte_of_aview SEGS). apply (HAPP (d_FB cx) 4096). exact GFapp.
  unfold d_obj, dobj_off in Ha. lia. }
assert (HBUFB : a3_buf op T1 now buf W (ms_mem ms0)).
{ destruct Hbuf as (Hbr & HbG). split; [exact Hbr|].
  apply (garr8_frame SEGS (rd W mem3) (rd W (ms_mem ms0)) buf _ HbG).
  intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. unfold a3_r in Hbr.
  apply (mbyte_of_aview SEGS).
  apply (HAPP buf (Z.max (slot_ser_defs.ser_cap op) 1)); [exact Hbufapp | lia]. }
assert (HSP1B : d_sp1 cx i n now W (ms_mem ms0)).
{ split; [split|split].
  - exact (HVM 208 i ltac:(lia) ltac:(lia) H208).
  - exact (HVM 320 now ltac:(lia) ltac:(lia) H320).
  - exact (HVM 192 n ltac:(lia) ltac:(lia) H192).
  - exact (HVM 200 (d_cur cx n) ltac:(lia) ltac:(lia) H200). }
assert (HSP0B : d_sp0 cx i now W (ms_mem ms0)).
{ split; [exact (HVM 208 i ltac:(lia) ltac:(lia) H208) | exact (HVM 320 now ltac:(lia) ltac:(lia) H320)]. }
assert (BUN : forall (rb : bv 5) (sv0 : sv) (j : nat) (v : Z), (j < 32)%nat -> Z.of_nat j = bv_unsigned rb ->
  getr (ms_regs ms) rb = w64 v -> getr (ms_regs ms0) rb = sv_denot E1 sv0 -> sv0 = SOff (AT_X + j) 0 ->
  getr (ms_regs ms0) rb = w64 v).
{ intros rb sv0 j v Hj Hjb Hv Hrr Hsv. rewrite Hrr, Hsv, sv_denot_SOff0, HE1.
  unfold vals. rewrite jk_x by lia. rewrite Hjb, Z_to_bv_bv_unsigned. exact Hv. }
assert (X3 : getr (ms_regs ms0) 3 = w64 (as_gp B)).
{ apply (BUN (3%bv : bv 5) (SOff (AT_X + 3) 0) 3%nat (as_gp B) ltac:(lia) ltac:(vm_compute; reflexivity)
    ltac:(rewrite Q3; exact Rgp));
    [rewrite (st_ok_restrict_reg SEGS (w_H W) E1 _ ms0 (3%bv : bv 5) HSB); reflexivity | reflexivity]. }
assert (X4 : getr (ms_regs ms0) 4 = w64 (as_tp B)).
{ apply (BUN (4%bv : bv 5) (SOff (AT_X + 4) 0) 4%nat (as_tp B) ltac:(lia) ltac:(vm_compute; reflexivity)
    ltac:(rewrite Q4; exact Rtp));
    [rewrite (st_ok_restrict_reg SEGS (w_H W) E1 _ ms0 (4%bv : bv 5) HSB); reflexivity | reflexivity]. }
assert (X18 : getr (ms_regs ms0) 18 = w64 WS_MASK).
{ apply (BUN (18%bv : bv 5) (SOff (AT_X + 18) 0) 18%nat WS_MASK ltac:(lia) ltac:(vm_compute; reflexivity)
    ltac:(rewrite Q18; exact Rs18));
    [rewrite (st_ok_restrict_reg SEGS (w_H W) E1 _ ms0 (18%bv : bv 5) HSB); reflexivity | reflexivity]. }
assert (X20 : getr (ms_regs ms0) 20 = w64 32).
{ apply (BUN (20%bv : bv 5) (SOff (AT_X + 20) 0) 20%nat 32 ltac:(lia) ltac:(vm_compute; reflexivity)
    ltac:(rewrite Q20; exact Rs20));
    [rewrite (st_ok_restrict_reg SEGS (w_H W) E1 _ ms0 (20%bv : bv 5) HSB); reflexivity | reflexivity]. }
assert (X21 : getr (ms_regs ms0) 21 = w64 (p + 2)).
{ apply (BUN (21%bv : bv 5) (SOff (AT_X + 21) 0) 21%nat (p + 2) ltac:(lia) ltac:(vm_compute; reflexivity) R121);
    [rewrite (st_ok_restrict_reg SEGS (w_H W) E1 _ ms0 (21%bv : bv 5) HSB); reflexivity | reflexivity]. }
assert (X24 : getr (ms_regs ms0) 24 = w64 buf).
{ apply (BUN (24%bv : bv 5) (SOff (AT_X + 24) 0) 24%nat buf ltac:(lia) ltac:(vm_compute; reflexivity) R124);
    [rewrite (st_ok_restrict_reg SEGS (w_H W) E1 _ ms0 (24%bv : bv 5) HSB); reflexivity | reflexivity]. }
assert (X25 : getr (ms_regs ms0) 25 = w64 (Z.lnot buf)).
{ apply (BUN (25%bv : bv 5) (SOff (AT_X + 25) 0) 25%nat (Z.lnot buf) ltac:(lia) ltac:(vm_compute; reflexivity) R125);
    [rewrite (st_ok_restrict_reg SEGS (w_H W) E1 _ ms0 (25%bv : bv 5) HSB); reflexivity | reflexivity]. }
assert (X26 : getr (ms_regs ms0) 26 = w64 (a3_r T1 now)).
{ apply (BUN (26%bv : bv 5) (SOff (AT_X + 26) 0) 26%nat (a3_r T1 now) ltac:(lia) ltac:(vm_compute; reflexivity) R126);
    [rewrite (st_ok_restrict_reg SEGS (w_H W) E1 _ ms0 (26%bv : bv 5) HSB); reflexivity | reflexivity]. }
assert (X2 : getr (ms_regs ms0) 2 = w64 (d_A cx)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) E1 _ ms0 (2%bv : bv 5) HSB).
  match goal with |- sv_denot E1 (sr_get (ss_regs ?s) _) = _ =>
    let e := eval vm_compute in (sr_get (ss_regs s) (2%bv : bv 5)) in
    change (sr_get (ss_regs s) (2%bv : bv 5)) with e end.
  rewrite sv_denot_SOff0, E1a. reflexivity. }
assert (X8 : getr (ms_regs ms0) 8 = w64 (d_S cx)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) E1 _ ms0 (8%bv : bv 5) HSB).
  match goal with |- sv_denot E1 (sr_get (ss_regs ?s) _) = _ =>
    let e := eval vm_compute in (sr_get (ss_regs s) (8%bv : bv 5)) in
    change (sr_get (ss_regs s) (8%bv : bv 5)) with e end.
  rewrite sv_denot_SOff0, E1s. reflexivity. }
assert (X9 : getr (ms_regs ms0) 9 = w64 (d_A cx)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) E1 _ ms0 (9%bv : bv 5) HSB).
  match goal with |- sv_denot E1 (sr_get (ss_regs ?s) _) = _ =>
    let e := eval vm_compute in (sr_get (ss_regs s) (9%bv : bv 5)) in
    change (sr_get (ss_regs s) (9%bv : bv 5)) with e end.
  rewrite sv_denot_SOff0, E1a. reflexivity. }
assert (X19 : getr (ms_regs ms0) 19 = w64 SHADOW_OFF).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) E1 _ ms0 (19%bv : bv 5) HSB).
  match goal with |- sv_denot E1 (sr_get (ss_regs ?s) _) = _ =>
    let e := eval vm_compute in (sr_get (ss_regs s) (19%bv : bv 5)) in
    change (sr_get (ss_regs s) (19%bv : bv 5)) with e end.
  rewrite sv_denot_SOff0, E132. reflexivity. }
assert (X27 : getr (ms_regs ms0) 27 = w64 (shadow_addr (d_FB cx))).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) E1 _ ms0 (27%bv : bv 5) HSB).
  match goal with |- sv_denot E1 (sr_get (ss_regs ?s) _) = _ =>
    let e := eval vm_compute in (sr_get (ss_regs s) (27%bv : bv 5)) in
    change (sr_get (ss_regs s) (27%bv : bv 5)) with e end.
  rewrite sv_denot_SOff0, E1sh. reflexivity. }
assert (X11 : getr (ms_regs ms0) 11 = w64 0).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) E1 _ ms0 (11%bv : bv 5) HSB).
  match goal with |- sv_denot E1 (sr_get (ss_regs ?s) _) = _ =>
    let e := eval vm_compute in (sr_get (ss_regs s) (11%bv : bv 5)) in
    change (sr_get (ss_regs s) (11%bv : bv 5)) with e end.
  rewrite denot_lit_U, U_lit by lia. reflexivity. }
assert (X12 : getr (ms_regs ms0) 12 = w64 144).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) E1 _ ms0 (12%bv : bv 5) HSB).
  match goal with |- sv_denot E1 (sr_get (ss_regs ?s) _) = _ =>
    let e := eval vm_compute in (sr_get (ss_regs s) (12%bv : bv 5)) in
    change (sr_get (ss_regs s) (12%bv : bv 5)) with e end.
  rewrite denot_lit_U, U_lit by lia. reflexivity. }
assert (X1 : getr (ms_regs ms0) 1 = w64 (BASE + OBJ_OFF)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) E1 _ ms0 (1%bv : bv 5) HSB).
  match goal with |- sv_denot E1 (sr_get (ss_regs ?s) _) = _ =>
    let e := eval vm_compute in (sr_get (ss_regs s) (1%bv : bv 5)) in
    change (sr_get (ss_regs s) (1%bv : bv 5)) with e end.
  change 240%nat with A_TEXT. change 4572 with OBJ_OFF. rewrite (codeptr_val E1 OBJ_OFF HEI1). reflexivity. }
assert (E1c22 : ew E1 553 = Z_to_bv 64 count) by (rewrite EV553; reflexivity).
assert (Hjc : jcur cx (count + 1) = d_FB cx + 384 + 144 * count) by (unfold jcur, d_obj, dobj_off; lia).
assert (X10 : getr (ms_regs ms0) 10 = w64 (jcur cx (count + 1))).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) E1 _ ms0 (10%bv : bv 5) HSB).
  match goal with |- sv_denot E1 (sr_get (ss_regs ?s) _) = _ =>
    let e := eval vm_compute in (sr_get (ss_regs s) (10%bv : bv 5)) in
    change (sr_get (ss_regs s) (10%bv : bv 5)) with e end.
  rewrite denot_lit_U, (jdb_mul_U E1 516 553 (d_FB cx) count E1f E1c22 ltac:(lia) ltac:(lia) ltac:(lia)).
  rewrite Hjc. reflexivity. }
assert (X23 : getr (ms_regs ms0) 23 = w64 (jcur cx (count + 1))).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) E1 _ ms0 (23%bv : bv 5) HSB).
  match goal with |- sv_denot E1 (sr_get (ss_regs ?s) _) = _ =>
    let e := eval vm_compute in (sr_get (ss_regs s) (23%bv : bv 5)) in
    change (sr_get (ss_regs s) (23%bv : bv 5)) with e end.
  rewrite denot_lit_U, (jdb_mul_U E1 516 553 (d_FB cx) count E1f E1c22 ltac:(lia) ltac:(lia) ltac:(lia)).
  rewrite Hjc. reflexivity. }
assert (X22 : getr (ms_regs ms0) 22 = w64 (count + 1)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) E1 _ ms0 (22%bv : bv 5) HSB).
  match goal with |- sv_denot E1 (sr_get (ss_regs ?s) _) = _ =>
    let e := eval vm_compute in (sr_get (ss_regs s) (22%bv : bv 5)) in
    change (sr_get (ss_regs s) (22%bv : bv 5)) with e end.
  rewrite denot_lit_U, (U_atom_off E1 553%nat count 1 E1c22 ltac:(lia) ltac:(lia)). reflexivity. }
try clear HF HFr HG0 HF0 HFr0 HG1 EmemA.
pmkst HSB.
eapply SRr_mono.
{ apply (ms_step B MT XM_LIB RLO RHI tfib_K LAWS AMEMSET DBRT cx h i n now op W0 c0 T0 T1 buf OBJ_OFF (count + 1)
    (jdb_R cx (p + 2) (count + 1)) (jdb_X cx T1 now buf p count fin acc cur vpad) W _).
  - unfold OBJ_OFF. lia.
  - unfold OBJ_OFF. reflexivity.
  - lia.
  - intros rg rg' HPp HRr. exact (jdb_R_pres cx (p + 2) (count + 1) rg rg' HPp HRr).
  - intros W1x m1x W2x m2x HXx HKk.
    exact (jdb_X_kept cx T1 now buf p count fin acc cur vpad W1x m1x W2x m2x HXx HKk).
  - unfold ms_in, jcut. split; [exact HFROM|].
    unfold d_arm_at_pf, d_at.
    exists fq, ly3, S3, (ms_regs ms0), (ms_mem ms0). eexists. exists k, accm.
    split.
    { unfold cfg_at, w64.
      replace (BASE + (SIGMA AS___asan_memset - BASE)) with (SIGMA AS___asan_memset) by lia.
      reflexivity. }
    split; [exact Hfrm0|]. split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
    split; [exact Hnev|]. split; [exact Hmo|]. split; [exact Hacc|].
    split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
    split.
    { split; [unfold spZ; rewrite X2; unfold w64; apply unsigned_lit_small; lia|].
      split; [exact X3|]. split; [exact X4|]. split; [exact X8|]. split; [exact X9|].
      split; [exact X19|]. split; [exact X18|]. split; [exact X20|]. exact X27. }
    split.
    { split; [exact X26|]. split; [exact X24|]. split; [exact X25|].
      split; [exact X1|]. split; [exact X10|]. split; [exact X11|]. split; [exact X12|].
      split; [exact X21|]. split; [exact X22 | exact X23]. }
    split.
    { split; [exact HSP1B|]. split; [exact HTABB|]. split; [exact HBUFB | exact HXB]. }
    split; [exact HSP0B | exact HBODY0]. }
cbv beta. intros W4 c4 HW4 HOUT.
unfold ms_out, jcut, d_arm_at_pf, d_at in HOUT.
destruct HOUT as (HFROM4 & fq4 & ly4 & S4 & regs4 & mem4 & md4 & k4 & acc4 & -> & Hfrm04 & Hbase4 & HJ4 & Hfrs4 & Hk4 &
  Hnev4 & Hmo4 & Hacc4 & Hi4 & Hn4 & Hnow4 & HrL4 & (R426 & R424 & R425 & R410 & (R421 & R422 & R423)) &
  (Hsp14 & Htab4 & Hbuf4 & HX4 & HZ144) & Hsp04 & Hbody4).
destruct HX4 as (HFIN4 & Hp04 & Hp2r4 & Hcnt4 & Hlen4 & Hvpad4 & Hfrom4 & M64' & _ & _ & _ & _ & M4444 & MOO4).
assert (HLEN2 : Z.of_nat (length (map (fun b : byte => bv_unsigned b)
  (slot_ser_defs.objs_bytes buf vpad (acc ++ [cur])))) = 144 * (count + 1)).
{ rewrite length_map, (jdb_objs_len buf vpad (acc ++ [cur]) Hvpad4 M64'), length_app, Hlen4.
  cbn [length]. lia. }
unfold jobj_in, jcut. split; [exact HFROM4|].
unfold d_arm_at_pf, d_at.
exists fq4, ly4, S4, regs4, mem4, md4, k4, acc4.
split; [reflexivity|].
split; [exact Hfrm04|]. split; [exact Hbase4|]. split; [exact HJ4|]. split; [exact Hfrs4|]. split; [exact Hk4|].
split; [exact Hnev4|]. split; [exact Hmo4|]. split; [exact Hacc4|].
split; [exact Hi4|]. split; [exact Hn4|]. split; [exact Hnow4|].
split; [exact HrL4|].
split.
{ split; [exact R426|]. split; [exact R424|]. split; [exact R425|].
  split; [exact R421|]. split; [exact R422 | exact R423]. }
split.
{ split; [exact Hsp14|]. split; [exact Htab4|]. split; [exact Hbuf4|].
  split; [exact HFIN4|]. split; [lia|]. split; [lia|].
  split; [rewrite length_app, Hlen4; cbn [length]; lia|].
  split; [exact Hfrom4|].
  split; [exact Hvpad4|].
  split; [exact M4444|].
  split.
  { rewrite (jdb_objs_app_empty buf vpad (acc ++ [cur])), map_app, jdb_map_zeros.
    apply (proj2 (garr8_app SEGS (rd W4 mem4) (d_obj cx OO) _ _)).
    split; [exact MOO4|].
    rewrite HLEN2.
    replace (d_obj cx OO + 144 * (count + 1)) with (jcur cx (count + 1)) by (unfold jcur; lia).
    exact HZ144. }
  apply Forall_app. split; [exact M64' | apply Forall_cons; [exact jdb_len6 | apply Forall_nil]]. }
split; [exact Hsp04 | exact Hbody4].
Qed.

End h.
End f.
End d.
