(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 1960 of its 2024 lines of code are new or changed and 1214 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI04 YI09 YI08 YI00 YN3v YG0v YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09 YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YC88 YCkd YC1i ACbf ACj1 DiscoACjr DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoEntBody DiscoSites
FindEntry CheckTable CheckSighting ReacHuntObserve ClassifyCore.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c disco_classify_c hunt_c SightModel slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_hunt_observe_c reac_frame_clean_len_c disco_table slot_classify slot_hunt.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition hb_rx (r : nat) : sv :=
  match r with
  | 0%nat => SLit 0 | 2%nat => SOff AT_A 0 | 8%nat => SOff AT_STK 0 | 9%nat => SOff AT_A 0 | 18%nat => SOff 32 0
  | _ => SOff (AT_X + r) 0
  end.
Definition hb_sr : list sv := map hb_rx (seq 0 32).
Definition hb_vals (regs : bvmap 5 word) : list word := map (fun r => getr regs (Z_to_bv 5 (Z.of_nat r))) (seq 0 32).
Definition HB_RA1 : Z := 0x16bc.
Definition HB_RA2 : Z := 0x1714.
Definition HB_RA3 : Z := 0x177c.
Definition HB_RA4 : Z := 0x1798.
Definition HBspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

Ltac hb_ro_base HS n :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs n in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Ltac hb_cs := unfold acallee_saved; cbn [bv_unsigned];
  repeat (first [left; reflexivity | right]); split; apply (proj1 (Z.leb_le _ _)); reflexivity.
Lemma hb_tho_facts : forall (H FB O : list byte) len now out r H' (OUT : list byte -> Prop),
  length H = 480%nat -> hunt_ok H -> length FB = 50%nat -> out <> 0 ->
  hunt_ok H' -> (r = -1 \/ r = 0 \/ r = 1) -> tho_model H FB O len now out r H' OUT ->
  sub H' 412 6 = sub H 412 6 /\
  (0 <= r -> exists A, length A = 24%nat /\ OUT A /\
     reac_hunt_observe_c.ho_facts H FB (reac_frame_clean_len_c.reac_frame_clean_len_model len) (sub H 0 400) A).
Proof.
intros H FB O len now out r H' OUT LH HOK LFB Hout HOK' Hr HM.
unfold tho_model in HM. cbv zeta in HM. destruct HM as [P1 P2].
set (L := reac_frame_clean_len_c.reac_frame_clean_len_model len) in *.
pose proof HOK as (_ & (T1 & _ & _ & _) & _ & _).
change (firstn 400 H) with (sub H 0 400) in T1.
assert (LLk : length (match cm_lock FB L (sub H 412 6) (Some (sub H 400 12)) with Some x => x | None => sub H 400 12 end) = 12%nat).
{ apply slot_hunt.lk_len; [apply disco_table.length_sub; lia | intros _; exact LFB]. }
assert (L12 : firstn 6 (sub H 412 12) = sub H 412 6) by (unfold sub; rewrite firstn_firstn; reflexivity).
destruct (Z.eq_dec (cm_ret FB L (sub H 412 6) (Some (sub H 400 12))) 0) as [C0|C0].
- destruct (P2 C0) as (T' & c & OM & Erc & EH & PA).
  destruct (slot_classify.sc_sight FB L (sub H 412 6) (Some (sub H 400 12)) LFB C0) as (_ & LS & _).
  pose proof (slot_hunt.obs_len (sub H 0 400) (sight FB L) 0 now T' c ltac:(apply disco_table.length_sub; lia) LS T1 OM) as LT'.
  split.
  + rewrite EH. apply slot_hunt.sub412; [exact LT' | exact LLk |].
    rewrite firstn_app, disco_table.length_sub by lia. replace (6 - 12)%nat with 0%nat by reflexivity.
    rewrite firstn_O, app_nil_r. exact L12.
  + intros Hr0. destruct (PA Hout) as (A & HA & OA & HF). exists A. split; [|split; [exact OA | exact HF]].
    destruct HA as (ri & FRi & EA).
    assert (ET' : firstn 400 H' = T') by (rewrite EH, firstn_app, LT', Nat.sub_diag, firstn_O, app_nil_r; apply firstn_all2; lia).
    pose proof HOK' as (_ & (T1' & _ & _ & _) & _ & _). rewrite ET' in T1'. unfold tbl_T1 in T1'.
    rewrite EA. destruct (Z.ltb_spec ri 0) as [Hn | Hp]; [exact LS|].
    destruct FRi as [[E1 _] | (Hri & _)]; [lia|].
    unfold reac_hunt_observe_c.ho_entry. rewrite !length_app, !disco_table.length_sub; try lia.
- destruct (P1 C0) as (Er & EH & _). split.
  + rewrite EH. apply slot_hunt.sub412; [apply disco_table.length_sub; lia | exact LLk | reflexivity].
  + intros Hr0. lia.
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.

Lemma hb_regs_ok : forall cx E regs, d_E cx E -> d_rL B cx regs ->
  0 <= d_A cx < 2 ^ 64 ->
  regs_ok (d_env cx E (hb_vals regs)) hb_sr regs.
Proof.
intros cx E regs HE HL HA.
destruct HE as (HER & H32 & _ & HA60 & _ & _).
destruct HL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25).
apply regs_ok_by_cases. intros r Hr.
cbv [all_regs In] in Hr.
assert (H2 : getr regs 2 = Z_to_bv 64 (d_A cx)) by (rewrite <- Hsp; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (HS2 : ew E 2 = Z_to_bv 64 (d_S cx)).
{ rewrite (HER 2%nat 2%bv eq_refl). unfold d_S, spZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
change AT_A with 60%nat in HA60.
repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<-|Hx] end; [ .. | contradiction ].
all: try (match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r) =>
  let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
  cbn [sv_denot];
  first
  [ rewrite getr_zero; reflexivity
  | rewrite Z.add_0_r; unfold d_env; rewrite ew_havoc_old by (cbv; lia);
    first [ rewrite HA60, Z_to_bv_bv_unsigned; first [exact H2 | exact H9]
          | rewrite HS2, Z_to_bv_bv_unsigned; exact H8
          | rewrite H32; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H18 ]
  | rewrite Z.add_0_r; unfold d_env, havoc; cbn [ew Nat.ltb Nat.leb Nat.sub nth hb_vals map seq Nat.add AT_X AT_FL];
    match goal with |- getr ?rg _ = Z_to_bv 64 (bv_unsigned (getr ?rg ?x)) =>
      let y := eval vm_compute in x in change x with y end;
    rewrite Z_to_bv_bv_unsigned; reflexivity ]).
Qed.

Lemma hb_A_range : forall cx ly3 S3 W3 mem3 md3 k,
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W3 mem3 md3 k ->
  alloc_ceiling + LLVMF_STK <= d_S cx <= 2 ^ 47 /\ d_S cx mod 16 = 0 /\
  d_S cx - 592 <= d_A cx <= d_S cx - 576 /\ d_A cx mod 32 = 0.
Proof.
intros cx ly3 S3 W3 mem3 md3 k HJ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
unfold d_A. pose proof (Z.div_mod (d_S cx - MFRAME) 32 ltac:(lia)) as D.
pose proof (Z.mod_pos_bound (d_S cx - MFRAME) 32 ltac:(lia)) as M.
unfold MFRAME in *. split; [lia|]. split; [exact Hal|]. split; [|rewrite Z.mul_comm; apply Z_mod_mult].
assert ((d_S cx - 576) mod 32 = 0 \/ (d_S cx - 576) mod 32 = 16).
{ assert (E16 : (d_S cx - 576) mod 16 = 0) by (rewrite Zminus_mod, Hal; reflexivity).
  pose proof (Z.div_mod (d_S cx - 576) 16 ltac:(lia)). lia. }
lia.
Qed.

Lemma hb_frame_ro_pt : forall E rs (m m' : word -> option byte), frame_of E rs m m' ->
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> forall x, m' x = m x.
Proof.
intros E rs m m' HF Hro x. apply HF. intros (r & Hin & Ha).
rewrite forallb_forall in Hro. specialize (Hro r Hin). apply Z.leb_le in Hro. lia.
Qed.
Lemma hb_val_mem_pt : forall (m m' : word -> option byte) a n v, (forall x, m' x = m x) ->
  val_mem SEGS m a n v -> val_mem SEGS m' a n v.
Proof. intros m m' a n v Hpt H kk Hk. pose proof (H kk Hk) as H1. unfold mbyte in H1 |- *. rewrite Hpt. exact H1. Qed.
Lemma hb_garr8_pt : forall (m m' : word -> option byte) a l, (forall x, m' x = m x) ->
  garr8 SEGS m a l -> garr8 SEGS m' a l.
Proof. intros m m' a l Hpt H j Hj. destruct (H j Hj) as [H1 H2]. split; [exact (hb_val_mem_pt m m' _ _ _ Hpt H1) | exact H2]. Qed.
Lemma hb_w64_add : forall a b, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 a) + b) = Z_to_bv 64 (a + b).
Proof.
intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
rewrite Z.add_mod_idemp_l by (unfold bv_modulus; cbn; lia). reflexivity.
Qed.
Lemma hb_garr8_kept : forall (H H' : word -> bool) (m m' : word -> option byte) a l,
  garr8 SEGS (mrestrict H m) a l ->
  (forall j, 0 <= j < Z.of_nat (length l) -> aview SEGS H' m' (a + j) = aview SEGS H m (a + j)) ->
  garr8 SEGS (mrestrict H' m') a l.
Proof.
intros H H' m m' a l G K j Hj. destruct (G j Hj) as [V R]. split; [|exact R].
apply (val_mem_kept SEGS H H' m m' (a + Z.of_nat j) 1 _); [|exact V].
intros q Hq. replace (a + Z.of_nat j + q) with (a + (Z.of_nat j + q)) by lia. apply K. lia.
Qed.
Lemma hb_vm_kept : forall (H H' : word -> bool) (m m' : word -> option byte) a (w : nat) v,
  val_mem SEGS (mrestrict H m) a w v ->
  (forall j, 0 <= j < Z.of_nat w -> aview SEGS H' m' (a + j) = aview SEGS H m (a + j)) ->
  val_mem SEGS (mrestrict H' m') a w v.
Proof. intros H H' m m' a w v V K. exact (val_mem_kept SEGS H H' m m' a w v K V). Qed.
Lemma hb_region_tr : forall E (m m' : word -> option byte) (nb : nat) lo hi wlo whi cs lo' hi',
  region_ok SEGS E m (YP09.mkRegion (Some nb) lo hi wlo whi cs) ->
  forallb (fun c => (lo' <=? YP09.c_off c) && (YP09.c_off c + YP09.c_len c <=? hi')) cs = true ->
  (forall a, bv_unsigned (ew E nb) + lo' <= a < bv_unsigned (ew E nb) + hi' -> mbyte SEGS m' a = mbyte SEGS m a) ->
  (forall o, wlo <= o < whi -> writable_at SEGS m' (bv_unsigned (ew E nb) + o)) ->
  region_ok SEGS E m' (YP09.mkRegion (Some nb) lo hi wlo whi cs).
Proof.
intros E m m' nb lo hi wlo whi cs lo' hi' HR Hcs Hm Hw.
unfold region_ok in *. cbv zeta in *. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in *.
destruct HR as (H1 & H2 & H3 & H4).
split; [exact H1|]. split; [exact H2|]. split; [exact Hw|].
rewrite Forall_forall in H4 |- *. intros c Hc i Hi.
destruct (H4 c Hc i Hi) as (b & Hb1 & Hb2). exists b. split; [exact Hb1|].
rewrite forallb_forall in Hcs. specialize (Hcs c Hc). apply andb_prop in Hcs as [Hc1 Hc2]. apply Z.leb_le in Hc1, Hc2.
rewrite Hm; [exact Hb2 | lia].
Qed.

#[local] Notation DAT := (d_at B MT XM_LIB RLO RHI tfib_K).

Definition macb (cx : dcx) (nb len : Z) : list byte :=
  if 11 <? len then firstn 6 (skipn 6 (firstn (Z.to_nat len) (rest_of (c_pl cx) nb))) else our_of (c_pl cx).
Definition hfb (cx : dcx) (nb len : Z) : list byte :=
  firstn 50 (firstn (Z.to_nat len) (rest_of (c_pl cx) nb) ++ repeat (Z_to_bv 8 0) 50).
Definition hflag (T P : list byte) (idx : Z) : Z := Z.b2z ((0 <=? idx) && (role_of_e T idx =? 1)).

Definition hoc (cx : dcx) (h i n now op nb fr len : Z) (regs : bvmap 5 word)
  (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (mem3 : word -> option byte) : Prop :=
  0 <= i < MAX_OPS /\ 0 <= n /\ 0 <= now < 2 ^ 64 /\ op mod 4 = 2 /\ 0 <= op < 256 /\
  d_rL B cx regs /\ d_sp0 cx i now W3 mem3 /\ d_frm cx nb fr len W3 mem3 /\
  0 <= reac_frame_clean_len_c.reac_frame_clean_len_model len <= len /\
  val_mem SEGS (rd W3 mem3) (d_A cx + 248) 8 (d_cur cx nb) /\ len <= nb /\ nb - len <= Z.max 0 (c_n cx - 7) /\
  nb <= c_n cx /\
  getr regs 22 = w64 (d_obj cx OS) /\ getr regs 23 = w64 nb /\ getr regs 24 = w64 len /\
  getr regs 26 = w64 (d_obj cx OOUR) /\ getr regs 27 = w64 fr /\
  d_body B cx h n (dxb fr len) dsh_rec ly3 S3 W3 mem3.
Definition hH (cx : dcx) (h : Z) (H : list byte) (W3 : world SEGS) (mem3 : word -> option byte) : Prop :=
  length H = 480%nat /\ garr8 SEGS (rd W3 mem3) h (map (fun b : byte => bv_unsigned b) H) /\ hunt_ok H /\
  firstn 6 (skipn 412 H) = our_of (c_pl cx).
Definition hb_regb (cx : dcx) (a : Z) : Prop :=
  (d_S cx - 104 <= a < d_S cx) \/ (d_A cx <= a < d_A cx + 472) \/ (d_FB cx <= a < d_FB cx + 24) \/
  (d_FB cx + 4088 <= a < d_FB cx + 4096) \/ (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512).

Lemma hb_frame_tr : AR_laws SEGS B -> forall cx h shf (W : world SEGS) m ly4 S4 (W' : world SEGS) m' md4 k4,
  d_frame cx h shf W m -> d_shadow cx shf W m ->
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly4 S4 W' m' md4 k4 ->
  (forall a, hb_regb cx a -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  d_frame cx h shf W' m' /\ d_shadow cx shf W' m'.
Proof.
intros LAWS cx h shf W m ly4 S4 W' m' md4 k4 (E & HE & HR & Hfl & V216 & V152) Hsh Hctx K.
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly4 S4 W' m' md4 k4 Hctx)
  as (HSmod & HSlo & HShi & HFB1 & HFB2 & HFBapp & HFBimg & HFBmod & HFpres & HSHpres & HWpres & _).
pose proof HE as (EE & E32 & HEI & E60 & E516 & E529).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & HAmod).
assert (U2 : bv_unsigned (ew E AT_STK) = d_S cx) by (unfold AT_STK; rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (U60 : bv_unsigned (ew E AT_A) = d_A cx) by (rewrite E60; unfold w64; apply unsigned_lit_small; unfold MFRAME, LLVMF_STK in *; lia).
assert (U516 : bv_unsigned (ew E AT_F) = d_FB cx) by (rewrite E516; unfold w64; apply unsigned_lit_small; lia).
assert (HSH : 0 <= shadow_addr (d_FB cx) /\ shadow_addr (d_FB cx) + 512 < alloc_ceiling).
{ unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos (d_FB cx) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_upper_bound (d_FB cx) 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
assert (U529 : bv_unsigned (ew E AT_SH) = shadow_addr (d_FB cx)) by (rewrite E529; unfold w64; apply unsigned_lit_small; lia).
assert (MB : forall a, hb_regb cx a -> mbyte SEGS (rd W' m') a = mbyte SEGS (rd W m) a)
  by (intros a Ha; apply mbyte_of_aview; apply K; exact Ha).
split.
- exists E. split; [exact HE|]. split; [|split; [|split]].
  + unfold d_regions in HR |- *.
    apply Forall_cons_iff in HR as [R1 HR]. apply Forall_cons_iff in HR as [R2 HR].
    apply Forall_cons_iff in HR as [R3 HR]. apply Forall_cons_iff in HR as [R4 _].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
    * apply (hb_region_tr E _ _ AT_STK (-104) 0 0 0 dsave_chunks (-104) 0 R1 ltac:(vm_compute; reflexivity)).
      -- intros a Ha. apply MB. unfold hb_regb. left. rewrite U2 in Ha. lia.
      -- intros o Ho. lia.
    * apply (hb_region_tr E _ _ AT_A 0 472 0 472 dslot_chunks 0 472 R2 ltac:(vm_compute; reflexivity)).
      -- intros a Ha. apply MB. unfold hb_regb. right; left. rewrite U60 in Ha. lia.
      -- intros o Ho. rewrite U60. apply apresent_writable. apply HWpres. unfold LLVMF_STK, MFRAME in *. lia.
    * apply (hb_region_tr E _ _ AT_F 0 (fs_frame_bytes DFRAME_CLASS) 0 DFRAME_SIZE _ 0 24 R3 ltac:(vm_compute; reflexivity)).
      -- intros a Ha. apply MB. unfold hb_regb. right; right; left. rewrite U516 in Ha. lia.
      -- intros o Ho. rewrite U516. apply apresent_writable. apply HFpres. unfold DFRAME_SIZE in Ho. lia.
    * unfold fshadow_region in R4 |- *.
      apply (hb_region_tr E _ _ AT_SH 0 (fs_frame_bytes DFRAME_CLASS / 8) 0 DFRAME_SH (dsh_chunks shf) 0 384 R4
        ltac:(vm_compute; reflexivity)).
      -- intros a Ha. apply MB. unfold hb_regb. right; right; right; right. rewrite U529 in Ha. lia.
      -- intros o Ho. rewrite U529. apply apresent_writable. apply HSHpres. unfold DFRAME_SH in Ho. lia.
  + rewrite (rdword_ext (aview SEGS (w_H W) m) (aview SEGS (w_H W') m')); [exact Hfl|].
    intros q Hq. apply K. unfold hb_regb. right; right; right; left. change (fs_frame_bytes DFRAME_CLASS) with 4096. lia.
  + apply (hb_vm_kept (w_H W) (w_H W') m m' _ 8 h V216). intros j Hj. apply K. unfold hb_regb. right; left. lia.
  + apply (hb_vm_kept (w_H W) (w_H W') m m' _ 8 (h + 440) V152). intros j Hj. apply K. unfold hb_regb. right; left. lia.
- intros q Hq. rewrite K; [apply Hsh; exact Hq|]. unfold hb_regb. right; right; right; right. unfold DFRAME_SH in Hq. lia.
Qed.

Lemma hb_fr_in : forall cx h n fr len shf ly3 S3 (W3 : world SEGS) mem3,
  d_body B cx h n (dxb fr len) shf ly3 S3 W3 mem3 -> fr <> 0 -> In (fr, len) (ablocks B ly3 S3).
Proof.
intros cx h n fr len shf ly3 S3 W3 mem3 HB Hfr.
destruct HB as (T & G & Lk & H & _ & _ & _ & (HP & _) & _).
apply (Permutation_in _ (Permutation_sym HP)). unfold dxb. replace (fr =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hfr).
left. reflexivity.
Qed.
Lemma hb_h_in : forall cx h n xb shf ly3 S3 (W3 : world SEGS) mem3,
  d_body B cx h n xb shf ly3 S3 W3 mem3 -> In (h, HUNT_SIZE) (ablocks B ly3 S3).
Proof.
intros cx h n xb shf ly3 S3 W3 mem3 HB.
destruct HB as (T & G & Lk & H & _ & _ & _ & (HP & _) & _).
apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. left. reflexivity.
Qed.

Lemma hb_frm0_post : forall (fq fx' : YK11.FPState), lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  (@YK11.fp_csr fx' = @YK11.fp_csr fq \/ Z.land (Z.shiftr (bv_unsigned (@YK11.fp_csr fx')) 5) 7 = 0) ->
  lib.Lib.FP.frm0 (@YK11.fp_csr fx').
Proof. intros fq fx' H [E | E]; [rewrite E; exact H | exact E]. Qed.

Lemma hb_ret_A : AR_laws SEGS B -> MT = ameter_triv ->
  forall cx h i n now op nb fr len kmax accmax (Px : bvmap 5 word -> world SEGS -> (word -> option byte) -> Prop)
    (fq : YK11.FPState) ly3 S3 (W : world SEGS) regs mem3 md3 k acc STK1 retk ly' S' (W' : world SEGS) regs' mem' md',
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) -> d_base B MT XM_LIB RLO RHI tfib_K cx ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W mem3 md3 k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] -> 0 <= k <= kmax -> acc <= accmax ->
  hoc cx h i n now op nb fr len regs ly3 S3 W mem3 ->
  0 <= STK1 -> STK1 + 592 <= LLVMF_STK ->
  ajournal SEGS B STK1 (spZ regs) [] ly3 S3 W mem3 md3 [] ly' S' W' mem' md' 0 ->
  aregs_preserved regs regs' -> Permutation (ablocks B ly' S') (ablocks B ly3 S3) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK1 <= a < spZ regs) ->
     aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem3 a) ->
  Px regs' W' mem' ->
  DAT cx retk kmax accmax (fun regs ly S W m md => hoc cx h i n now op nb fr len regs ly S W m /\ Px regs W m)
    W' (cfg_at (fx := fq) SEGS (BASE + retk) regs' mem' md').
Proof.
intros LAWS MTT cx h i n now op nb fr len kmax accmax Px fq ly3 S3 W regs mem3 md3 k acc STK1 retk ly' S' W' regs' mem' md'
  HF0 HB HJ Hfrs Hk Hacc HO Hs1 Hs2 HJ1 HP Hperm K HPx.
pose proof HO as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & Hcl & H248 & Hlen & Hnb & Hnc & R22 & R23 & R24 & R26 & R27 & Hbody).
pose proof HrL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25).
destruct (hb_A_range cx ly3 S3 W mem3 md3 k HJ) as (HSr & HS16 & HAr & HA32).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HJ2 : ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly' S' W' mem' md' k).
{ pose proof (ajournal_sub_tok SEGS B LAWS pa_segs_low LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W mem3 md3 k STK1 (spZ regs) [] [] ly' S' W' mem' md' 0 HJ HJ1) as X.
  rewrite Z.add_0_r in X. cbn [app] in X. apply X.
  - rewrite Hsp. unfold LLVMF_STK in *. lia.
  - rewrite Hsp. lia.
  - intros a (r & Hr & _). destruct Hr. }
assert (Hfrs' : frames S' = [(DFRAME_CLASS, c_fpos cx)]).
{ pose proof HJ2 as (_ & _ & _ & _ & _ & Hf & _). rewrite Hf.
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & Hf0 & _). rewrite Hf0. reflexivity. }
assert (Hctx : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact HB | split; [exact HJ | exact Hfrs]]).
assert (Hctx' : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly' S' W' mem' md' k) by (split; [exact HB | split; [exact HJ2 | exact Hfrs']]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k Hctx)
  as (HSmod & HSlo & HShi & HFB1 & HFB2 & HFBapp & HFBimg & HFBmod & _).
assert (PR : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs' r = getr regs r).
{ intros r Hr. pose proof (HP _ Hr) as X. rewrite !Z_to_bv_bv_unsigned in X. exact X. }
assert (KS : forall a, 0 <= a < 2 ^ 64 -> (a < d_S cx - LLVMF_STK \/ d_A cx <= a) -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem3 a).
{ intros a Ha Hb. apply K; [exact Ha|]. rewrite Hsp. unfold LLVMF_STK in *. lia. }
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & Hcan & Hstk & Hawr).
destruct (hb_frame_tr LAWS cx h dsh_rec W mem3 ly' S' W' mem' md' k Hframe Hshadow Hctx') as [Hframe' Hshadow'].
{ intros a Ha. apply KS; unfold hb_regb in Ha; unfold shadow_addr, SHADOW_OFF in *;
  pose proof (Z.div_pos (d_FB cx) 8 ltac:(lia) ltac:(lia));
  pose proof (Z.div_le_upper_bound (d_FB cx) 8 (2 ^ 44) ltac:(lia) ltac:(lia)); unfold LLVMF_STK in *; lia. }
assert (Hbody' : d_body B cx h n (dxb fr len) dsh_rec ly' S' W' mem').
{ apply (d_body_call_keep B MT XM_LIB RLO RHI tfib_K LAWS cx h n (dxb fr len) dsh_rec dsh_rec ly3 S3 W mem3 ly' S' W' mem' md' k
    (spZ regs - STK1) (spZ regs) Hbody (conj HB HJ2)).
  - rewrite Hsp. unfold LLVMF_STK in *. lia.
  - rewrite Hsp. lia.
  - exact K.
  - exact Hperm.
  - exact Hframe'.
  - exact Hshadow'. }
exists fq, ly', S', regs', mem', md', k, acc.
split; [reflexivity|]. split; [exact HF0|]. split; [exact HB|]. split; [exact HJ2|]. split; [exact Hfrs'|]. split; [exact Hk|].
split; [pose proof HJ2 as (_ & _ & _ & _ & _ & _ & Hnev & _); lia|].
split; [rewrite MTT; exact I|]. split; [exact Hacc|].
split; [|exact HPx].
unfold hoc.
refine (conj Hi (conj Hn (conj Hnow (conj Hop (conj Hop2 (conj _ (conj _ (conj _ (conj Hcl (conj _ (conj Hlen (conj Hnb (conj Hnc
  (conj _ (conj _ (conj _ (conj _ (conj _ Hbody')))))))))))))))))).
- unfold d_rL, spZ in *. rewrite !PR by hb_cs. repeat split; assumption.
- destruct Hsp0 as (Hs1' & Hs2'). split.
  + apply (hb_vm_kept (w_H W) (w_H W') mem3 mem' _ 8 i Hs1'). intros j Hj. apply KS; unfold LLVMF_STK, MFRAME in *; lia.
  + apply (hb_vm_kept (w_H W) (w_H W') mem3 mem' _ 8 now Hs2'). intros j Hj. apply KS; unfold LLVMF_STK, MFRAME in *; lia.
- destruct Hfrm as (F1 & F2 & Fnc & F3). split; [exact F1|]. split; [exact F2|]. split; [exact Fnc|].
  apply (hb_garr8_kept (w_H W) (w_H W') mem3 mem' fr _ F3). intros j Hj.
  rewrite length_map, length_firstn in Hj.
  destruct (Z.eq_dec fr 0) as [E0|E0]; [specialize (F2 E0); lia|].
  destruct (al_blocks _ _ LAWS ly3 S3 W mem3 md3 fr len (proj1 HJ) (hb_fr_in cx h n fr len dsh_rec ly3 S3 W mem3 Hbody E0))
    as (Hb16 & Hb4096 & Hbc & _).
  pose proof (req_size_pos0 len ltac:(lia)) as RQ.
  apply KS; unfold LLVMF_STK in *; lia.
- apply (hb_vm_kept (w_H W) (w_H W') mem3 mem' _ 8 _ H248). intros j Hj. apply KS; unfold LLVMF_STK, MFRAME in *; lia.
- rewrite PR by hb_cs. exact R22.
- rewrite PR by hb_cs. exact R23.
- rewrite PR by hb_cs. exact R24.
- rewrite PR by hb_cs. exact R26.
- rewrite PR by hb_cs. exact R27.
Qed.

Definition saddr_okb (x s : Z) : bool := (s =? 0) || ((x mod 8 <? s) && (s <? 8)).
Lemma hb_ra_obj : forall cx shf (W : world SEGS) m off n,
  d_shadow cx shf W m -> d_FB cx mod 8 = 0 -> 0 <= off -> 0 <= n -> off + n <= 3072 ->
  forallb (fun j => saddr_okb (Z.of_nat j + off) (shf ((Z.of_nat j + off) / 8))) (seq 0 (Z.to_nat n)) = true ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF (d_FB cx + off) n.
Proof.
intros cx shf W m off n Hsh H8 Ho Hn Hon Hck x Hx.
set (j := x - d_FB cx).
assert (Hj : off <= j < off + n) by (unfold j; lia).
rewrite forallb_forall in Hck.
specialize (Hck (Z.to_nat (j - off)) ltac:(apply in_seq; lia)).
rewrite Z2Nat.id in Hck by lia. replace (j - off + off) with j in Hck by lia.
assert (Hj8 : 0 <= j / 8 < 384) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
exists (shf (j / 8)). split.
- replace x with (d_FB cx + j) by (unfold j; lia). rewrite shadow_of_addr_aligned_off by exact H8.
  pose proof (Hsh (j / 8) Hj8) as X. unfold shadow_addr in X. unfold shadow_of_addr. exact X.
- unfold saddr_okb in Hck. apply orb_prop in Hck as [Hz | Hc]; [left; apply Z.eqb_eq; exact Hz | right].
  apply andb_prop in Hc as [H1 H2]. apply Z.ltb_lt in H1, H2. split; [|exact H2].
  replace x with (d_FB cx + j) by (unfold j; lia). rewrite Z.add_mod, H8 by lia. rewrite Z.add_0_l, Z.mod_mod by lia. exact H1.
Qed.

Definition hc1 (cx : dcx) (h i n now op nb fr len : Z) : world SEGS -> config -> Prop :=
  DAT cx AF_find_entry (EV_HEAD i + 1) (ACC_HEAD MT i + mo_malloc MT REC_MAX) (fun regs ly3 S3 W3 mem3 md3 =>
    hoc cx h i n now op nb fr len regs ly3 S3 W3 mem3 /\
    getr regs 1 = w64 (BASE + HB_RA1) /\ getr regs 10 = w64 h /\ getr regs 19 = w64 h /\
    getr regs 11 = w64 (if 11 <? len then fr + 6 else d_obj cx OOUR)).

Lemma hb_s01 : AR_laws SEGS B -> PALib B -> frame_flag_lawP SEGS B ->
  forall cx h i n now op nb fr len W c,
  hobs_in B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len W c -> SRr SEGS W c (hc1 cx h i n now op nb fr len).
Proof.
intros LAWS TL FFL cx h i n now op nb fr len W c H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HF0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  Hi & Hn & Hnow & HrL & HrO & HX & Hsp0 & Hbody).
pose proof HX as (Hop & Hop2 & Hfrm & Hcl & H248 & Hlen & Hnb).
pose proof Hfrm as (_ & _ & Hnc & _).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & Hcan & Hstk & Hawr).
pose proof Hframe as (E & HdE & Hregs & Hflag & Hh216 & Hh152).
destruct (hb_A_range cx ly3 S3 W mem3 md3 k HJ) as (HSr & HS16 & HAr & HA32).
assert (HctxD : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold LLVMF_STK in HSr; lia).
pose proof (d_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E HOBS_OFF hb_sr (hb_vals regs) [] [] [] (d_facts [] [])
  HctxD HdE Hregs Hflag (hb_regs_ok cx E regs HdE HrL HAr2)
  (d_facts_ok B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k E (hb_vals regs) [] [] HctxD HdE I I)
  (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_d in HS.
hb_ro_base HS 516%nat. hb_ro_base HS 529%nat. hb_ro_base HS 60%nat.
assert (HEI : img_env VAL A_LIM (d_env cx E (hb_vals regs))).
{ destruct HdE as (_ & _ & HI & _). intros a Ha. unfold d_env. rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia). exact (HI a Ha). }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (hb_vals regs)) (rd W mem3)) by constructor.
pose (RUN := paj_run (fx := fq) B LAWS).
unfold cfg_at. change (w64 (BASE + HOBS_OFF)) with (Z_to_bv 64 (BASE + HOBS_OFF)).
paj_run_tok RUN HS HJ SHOK HBspan.
{ cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
assert (Hpt := hb_frame_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)).
assert (Hptr := hb_frame_ro_pt _ _ _ _ HFr ltac:(vm_compute; reflexivity)).
clear HF HFr HG.
rewrite (pa_sigma_find_entry (PI := PI)) in HS.
assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 11; 18; 19; 20; 22; 23; 24; 25; 26; 27]%bv -> getr (ms_regs ms) r = getr regs r).
{ intros r Hr. rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms r HS). rewrite (hb_regs_ok cx E regs HdE HrL HAr2 r).
  cbv [In] in Hr. repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]). destruct Hr. }
pose proof (st_ok_restrict_mkst SEGS (w_H W) _ _ ms HS eq_refl) as Hms.
cbn [ss_pc setpc] in Hms.
lazymatch type of HS with st_ok _ ?Ex (setpc ?ssx _) ?msx =>
  assert (HSpi : st_ok_pi SEGS VAL Ex (setpc ssx AF_find_entry) msx) by exact HS end.
set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *.
assert (Hctx4 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms) md4 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
assert (H216' := hb_val_mem_pt _ _ _ _ _ Hptr Hh216).
assert (H152' := hb_val_mem_pt _ _ _ _ _ Hptr Hh152).
destruct (d_land B MT XM_LIB RLO RHI tfib_K LAWS FFL fq cx h dsh_rec ly3 S3 W md4 k (d_env cx E (hb_vals regs)) _ ms Hctx4 (d_E_env cx E _ HdE)
  (d_env_fl cx E _) HSpi ltac:(vm_compute; reflexivity) H216' H152') as [Hframe4 Hshadow4].
assert (Hbody4 : d_body B cx h n (dxb fr len) dsh_rec ly3 S3 W (ms_mem ms)).
{ apply (d_body_rt B cx h n n (dxb fr len) dsh_rec dsh_rec ly3 S3 W mem3 (ms_mem ms) (d_A cx) (d_A cx) (fun _ => False) Hbody).
  - unfold LLVMF_STK; lia.
  - lia.
  - intros a [].
  - intros a Ha _. apply aview_eq_of. apply Hptr.
  - intros a _ [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite Hpt. exact Hb.
  - exact Hframe4.
  - exact Hshadow4.
  - lia. }
destruct HrO as (H19 & H11 & H27 & H24 & H23 & H22 & H26).
apply SRr_ret. unfold hc1, d_at.
exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md4, k, acc.
split; [unfold cfg_at, w64; rewrite <- Hms; reflexivity|].
split; [exact HF0|]. split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
split; [exact Hnev|]. split; [exact Hmo|]. split; [exact Hacc|].
split; [|split; [|split; [|split]]].
- unfold hoc.
  refine (conj Hi (conj Hn (conj Hnow (conj Hop (conj Hop2 (conj _ (conj _ (conj _ (conj Hcl (conj _ (conj Hlen (conj Hnb (conj Hnc
    (conj _ (conj _ (conj _ (conj _ (conj _ Hbody4)))))))))))))))))).
  + destruct HrL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25). unfold d_rL, spZ in *.
    rewrite !RG by (cbv; tauto). repeat split; assumption.
  + destruct Hsp0 as (Hs1 & Hs2). split; eapply hb_val_mem_pt; [exact Hptr | exact Hs1 | exact Hptr | exact Hs2].
  + destruct Hfrm as (F1 & F2 & Fnc & F3). split; [exact F1|]. split; [exact F2|]. split; [exact Fnc|]. exact (hb_garr8_pt _ _ _ _ Hptr F3).
  + exact (hb_val_mem_pt _ _ _ _ _ Hptr H248).
  + rewrite RG by (cbv; tauto). exact H22.
  + rewrite RG by (cbv; tauto). exact H23.
  + rewrite RG by (cbv; tauto). exact H24.
  + rewrite RG by (cbv; tauto). exact H26.
  + rewrite RG by (cbv; tauto). exact H27.
- rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 1%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  unfold w64. replace HB_RA1 with (HOBS_OFF + 8) by reflexivity. exact (codeptr_val _ (HOBS_OFF + 8) HEI).
- rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 10%bv HS).
  transitivity (getr regs 19); [|exact H19].
  rewrite (hb_regs_ok cx E regs HdE HrL HAr2 19%bv). f_equal; try (vm_compute; reflexivity).
- rewrite RG by (cbv; tauto). exact H19.
- rewrite RG by (cbv; tauto). exact H11.
Qed.

Definition hp2 (cx : dcx) (h nb len : Z) (regs : bvmap 5 word) (W3 : world SEGS) (mem3 : word -> option byte) : Prop :=
  getr regs 19 = w64 h /\
  exists H idx, hH cx h H W3 mem3 /\ getr regs 10 = w64 idx /\ find_res (sub H 0 400) (macb cx nb len) idx.
Definition hc2 (cx : dcx) (h i n now op nb fr len : Z) : world SEGS -> config -> Prop :=
  DAT cx HB_RA1 (EV_HEAD i + 1) (ACC_HEAD MT i + mo_malloc MT REC_MAX) (fun regs ly3 S3 W3 mem3 md3 =>
    hoc cx h i n now op nb fr len regs ly3 S3 W3 mem3 /\ hp2 cx h nb len regs W3 mem3).
Definition hp3 (cx : dcx) (h nb fr len now : Z) (regs : bvmap 5 word) (W3 : world SEGS) (mem3 : word -> option byte) : Prop :=
  getr regs 1 = w64 (BASE + HB_RA2) /\ getr regs 10 = w64 h /\ getr regs 11 = w64 fr /\ getr regs 12 = w64 len /\
  getr regs 13 = w64 now /\ getr regs 14 = w64 (d_obj cx OS) /\
  exists H idx, hH cx h H W3 mem3 /\ find_res (sub H 0 400) (macb cx nb len) idx /\
    getr regs 19 = w64 (hflag (sub H 0 400) (macb cx nb len) idx).
Definition hc3 (cx : dcx) (h i n now op nb fr len : Z) : world SEGS -> config -> Prop :=
  DAT cx AF_reac_hunt_observe (EV_HEAD i + 1) (ACC_HEAD MT i + mo_malloc MT REC_MAX) (fun regs ly3 S3 W3 mem3 md3 =>
    hoc cx h i n now op nb fr len regs ly3 S3 W3 mem3 /\ hp3 cx h nb fr len now regs W3 mem3).
Definition hp4 (cx : dcx) (h nb fr len : Z) (regs : bvmap 5 word) (W3 : world SEGS) (mem3 : word -> option byte) : Prop :=
  exists H idx r H', length H = 480%nat /\ hunt_ok H /\ firstn 6 (skipn 412 H) = our_of (c_pl cx) /\
    find_res (sub H 0 400) (macb cx nb len) idx /\
    getr regs 19 = w64 (hflag (sub H 0 400) (macb cx nb len) idx) /\
    getr regs 10 = w64 r /\ (r = -1 \/ r = 0 \/ r = 1) /\ hH cx h H' W3 mem3 /\
    (0 <= r -> exists A, length A = 24%nat /\
       garr8 SEGS (rd W3 mem3) (d_obj cx OS) (map (fun b : byte => bv_unsigned b) A) /\
       reac_hunt_observe_c.ho_facts H (hfb cx nb len) (reac_frame_clean_len_c.reac_frame_clean_len_model len) (sub H 0 400) A).
Definition hc4 (cx : dcx) (h i n now op nb fr len : Z) : world SEGS -> config -> Prop :=
  DAT cx HB_RA2 (EV_HEAD i + 1) (ACC_HEAD MT i + mo_malloc MT REC_MAX) (fun regs ly3 S3 W3 mem3 md3 =>
    hoc cx h i n now op nb fr len regs ly3 S3 W3 mem3 /\ hp4 cx h nb fr len regs W3 mem3).
Definition hp5 (cx : dcx) (h nb fr len : Z) (regs : bvmap 5 word) (W3 : world SEGS) (mem3 : word -> option byte) : Prop :=
  getr regs 1 = w64 (BASE + HB_RA3) /\ getr regs 10 = w64 (d_obj cx OS) /\ getr regs 11 = w64 fr /\
  getr regs 12 = w64 (reac_frame_clean_len_c.reac_frame_clean_len_model len) /\
  getr regs 13 = w64 (d_obj cx OOUR) /\ getr regs 14 = w64 1 /\ 50 <= len /\
  exists A H' fl, length A = 24%nat /\
    garr8 SEGS (rd W3 mem3) (d_obj cx OS) (map (fun b : byte => bv_unsigned b) A) /\
    sighting_facts A (hfb cx nb len) (our_of (c_pl cx)) (reac_frame_clean_len_c.reac_frame_clean_len_model len) 1 /\
    getr regs 19 = w64 fl /\ (fl <> 0 -> s_role A = 1) /\ hH cx h H' W3 mem3.
Definition hc5 (cx : dcx) (h i n now op nb fr len : Z) : world SEGS -> config -> Prop :=
  DAT cx AF_check_sighting (EV_HEAD i + 1) (ACC_HEAD MT i + mo_malloc MT REC_MAX) (fun regs ly3 S3 W3 mem3 md3 =>
    hoc cx h i n now op nb fr len regs ly3 S3 W3 mem3 /\ hp5 cx h nb fr len regs W3 mem3).
Definition hp6 (cx : dcx) (h : Z) (regs : bvmap 5 word) (W3 : world SEGS) (mem3 : word -> option byte) : Prop :=
  exists A H' fl, length A = 24%nat /\
    garr8 SEGS (rd W3 mem3) (d_obj cx OS) (map (fun b : byte => bv_unsigned b) A) /\
    getr regs 19 = w64 fl /\ (fl <> 0 -> s_role A = 1) /\ hH cx h H' W3 mem3.
Definition hc6 (cx : dcx) (h i n now op nb fr len : Z) : world SEGS -> config -> Prop :=
  DAT cx HB_RA3 (EV_HEAD i + 1) (ACC_HEAD MT i + mo_malloc MT REC_MAX) (fun regs ly3 S3 W3 mem3 md3 =>
    hoc cx h i n now op nb fr len regs ly3 S3 W3 mem3 /\ hp6 cx h regs W3 mem3).
Definition hp7 (cx : dcx) (h : Z) (regs : bvmap 5 word) (W3 : world SEGS) (mem3 : word -> option byte) : Prop :=
  getr regs 1 = w64 (BASE + HB_RA4) /\ getr regs 10 = w64 h /\ exists H', hH cx h H' W3 mem3.
Definition hc7 (cx : dcx) (h i n now op nb fr len : Z) : world SEGS -> config -> Prop :=
  DAT cx AF_check_table (EV_HEAD i + 1) (ACC_HEAD MT i + mo_malloc MT REC_MAX) (fun regs ly3 S3 W3 mem3 md3 =>
    hoc cx h i n now op nb fr len regs ly3 S3 W3 mem3 /\ hp7 cx h regs W3 mem3).
Definition hc8 (cx : dcx) (h i n now op nb fr len : Z) : world SEGS -> config -> Prop :=
  DAT cx HB_RA4 (EV_HEAD i + 1) (ACC_HEAD MT i + mo_malloc MT REC_MAX) (fun regs ly3 S3 W3 mem3 md3 =>
    hoc cx h i n now op nb fr len regs ly3 S3 W3 mem3 /\ (fun (_ : bvmap 5 word) (_ : world SEGS) (_ : word -> option byte) => True) regs W3 mem3).

Lemma hb_regupd8 : forall (regs : bvmap 5 word) v (r : bv 5), r <> 8%bv -> getr (regupd regs 8 v) r = getr regs r.
Proof. intros regs v r Hr. unfold getr. destruct (bv_eqb r 0); [reflexivity|]. exact (regupd_other regs 8 v r Hr). Qed.

Lemma hb_c12 : AR_laws SEGS B -> PALib B ->
  (forall fq : YK11.FPState, abcmp_realizes (fx := fq) SEGS B (SIGMA DS___interceptor_trampoline_bcmp)) ->
  MT = ameter_triv ->
  forall cx h i n now op nb fr len W c, hc1 cx h i n now op nb fr len W c -> SRr SEGS W c (hc2 cx h i n now op nb fr len).
Proof.
intros LAWS TL ABCMP MTT cx h i n now op nb fr len W c Hc.
destruct Hc as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HF0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc & HO & R1 & R10 & R19 & R11).
pose proof HO as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & Hcl & H248 & Hlen & Hnb & Hnc & R22 & R23 & R24 & R26 & R27 & Hbody).
pose proof HrL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & Hcan & Hstk & Hawr).
pose proof Hobjs as (LT & GT & QT & LG & GG & QG & LL & GL & QL & GO & LH & GH & QH & EO).
assert (Hctx : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k Hctx)
  as (HSmod & HSlo & HShi & HFB1 & HFB2 & HFBapp & HFBimg & HFBmod & HFpres & HSHpres & HWpres & HAR3 & Hin3 & EFB3 & EFL3).
destruct (hb_A_range cx ly3 S3 W mem3 md3 k HJ) as (HSr & HS16 & HAr & HA32).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hgeo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
pose proof (hb_h_in cx h n _ dsh_rec ly3 S3 W mem3 Hbody) as Hhin.
destruct (al_blocks _ _ LAWS ly3 S3 W mem3 md3 h HUNT_SIZE HAR3 Hhin) as (Hh16 & Hh4096 & Hhc & Hhapp & _).
assert (RQH : req_size HUNT_SIZE = 480) by reflexivity.
pose proof Hblocks as (_ & _ & _ & Hboff). apply Forall_inv in Hboff. cbn [fst snd] in Hboff. rewrite RQH in Hboff.
set (T := sub H0 0 400). set (P := macb cx nb len). set (p := if 11 <? len then fr + 6 else d_obj cx OOUR).
assert (ET : T = firstn 400 H0) by reflexivity.
assert (LTT : length T = 400%nat) by (rewrite ET, length_firstn; lia).
assert (GT' : garr8 SEGS (rd W mem3) h (map (fun b : byte => bv_unsigned b) T)).
{ pose proof (garr8_sub_x SEGS _ h _ 0 400 GH ltac:(rewrite length_map; lia)) as X.
  rewrite Z.add_0_r in X. cbn [skipn] in X. rewrite ET, <- firstn_map. exact X. }
assert (T1 : tbl_T1 T) by (rewrite ET; destruct QH as (_ & (HT1 & _) & _); exact HT1).
assert (Hp : (0 < p /\ p + 6 <= 2 ^ 63) /\ length P = 6%nat /\
  garr8 SEGS (rd W mem3) p (map (fun b : byte => bv_unsigned b) P) /\ amem_range p 6 /\
  range_addressable (aview SEGS (w_H W) mem3) SHADOW_OFF p 6 /\ shadow_hull_vis (aview SEGS (w_H W) mem3) p 6 /\
  (p + 6 <= spZ regs - TFIND_ENTRY_STK \/ spZ regs <= p)).
{ unfold p, P, macb. destruct (Z.ltb_spec 11 len) as [L11 | L11].
  - destruct Hfrm as (F1 & F2 & Fnc & F3).
    assert (Efr : fr <> 0) by (intros E0; specialize (F2 E0); lia).
    pose proof (hb_fr_in cx h n fr len dsh_rec ly3 S3 W mem3 Hbody Efr) as Hfin.
    destruct (al_blocks _ _ LAWS ly3 S3 W mem3 md3 fr len HAR3 Hfin) as (Hf16 & Hf4096 & Hfc & Hfapp & _).
    assert (RQF : req_size len = len) by (unfold req_size; destruct (Z.eqb_spec len 0); lia).
    set (FR := firstn (Z.to_nat len) (rest_of (c_pl cx) nb)) in *.
    assert (LFR : length FR = Z.to_nat len).
    { unfold FR. rewrite length_firstn. unfold rest_of. rewrite length_skipn. lia. }
    split; [lia|]. split; [rewrite length_firstn, length_skipn; lia|].
    split.
    { pose proof (garr8_sub_x SEGS _ fr _ 6 6 F3 ltac:(rewrite length_map; lia)) as X.
      rewrite skipn_map, firstn_map in X. exact X. }
    split; [apply (amem_range_of_block SEGS B LAWS ly3 S3 W mem3 md3 fr len); [exact HAR3 | exact Hfin | lia | lia]|].
    split; [apply (range_addressable_of_block SEGS B LAWS ly3 S3 W mem3 md3 fr len); [exact HAR3 | exact Hfin | lia | lia]|].
    split; [apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W mem3 md3 fr len); [exact HAR3 | exact Hfin | lia | lia | lia]|].
    left. rewrite Hsp. unfold TFIND_ENTRY_STK, ESTACK, LLVMF_STK in *. lia.
  - split; [unfold d_obj, dobj_off; lia|]. split; [apply length_our|]. split; [exact GO|].
    split; [apply (amem_range_sub_app (d_FB cx) 4096); [exact HFBapp | lia | unfold d_obj, dobj_off; lia | unfold d_obj, dobj_off; lia | lia]|].
    split; [unfold d_obj, dobj_off; apply (hb_ra_obj cx dsh_rec W mem3 2128 6 Hshadow); [lia | lia | lia | lia | vm_compute; reflexivity]|].
    split; [apply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W mem3 md3 DFRAME_CLASS (c_fpos cx)); [exact HAR3 | exact Hin3 | rewrite EFB3; unfold d_obj, dobj_off; lia | rewrite EFB3; change (fs_frame_bytes DFRAME_CLASS) with 4096; unfold d_obj, dobj_off; lia | lia]|].
    left. rewrite Hsp. unfold d_obj, dobj_off, TFIND_ENTRY_STK, ESTACK, LLVMF_STK in *. lia. }
destruct Hp as ((Hp0 & Hp1) & LPP & GP & AMp & RAp & HVp & SPp).
assert (RU : forall r : bv 5, bv_unsigned r <> 8 -> getr (regupd regs 8 (Z_to_bv 64 0)) r = getr regs r).
{ intros r Hr. apply hb_regupd8. intros X. apply Hr. rewrite X. reflexivity. }
assert (E8 : getr (regupd regs 8 (Z_to_bv 64 0)) 8 = Z_to_bv 64 0) by (getr_resolve; reflexivity).
eapply SRr_mono.
{ apply (pb_find_entry B LAWS TL ABCMP fq ly3 S3 W regs mem3 md3 [] h p T P).
  - apply (afn_pre_at SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W mem3 md3 k (regupd regs 8 (Z_to_bv 64 0)) TFIND_ENTRY_STK (d_A cx - d_S cx) [] HJ).
    + unfold spZ. rewrite RU by (vm_compute; congruence). fold (spZ regs). rewrite Hsp. lia.
    + pose proof (Z.div_mod (d_A cx) 32 ltac:(lia)). pose proof (Z.div_mod (d_S cx) 16 ltac:(lia)). lia.
    + lia.
    + unfold TFIND_ENTRY_STK, ESTACK; lia.
    + unfold TFIND_ENTRY_STK, ESTACK, LLVMF_STK; lia.
    + rewrite RU by (vm_compute; congruence). rewrite R1. unfold w64. apply ret_ok_codeptr_v; unfold HB_RA1; lia.
    + unfold raZ. rewrite RU by (vm_compute; congruence). rewrite R1. unfold w64. pose proof pa_B_ok as (HB0 & HB1 & _).
      pose proof pa_base_lo as HBL. unfold IMG_LO in HBL. rewrite unsigned_lit_small by (unfold HB_RA1; lia). unfold HB_RA1. lia.
    + rewrite RU by (vm_compute; congruence). exact Hgp.
    + rewrite RU by (vm_compute; congruence). exact Htp.
    + apply achain_low. unfold s0Z. rewrite E8, unsigned_lit_small by lia. lia.
  - exact Himg.
  - exact R10.
  - exact R11.
  - lia.
  - lia.
  - lia.
  - exact Hp0.
  - exact Hp1.
  - exact LTT.
  - exact GT'.
  - exact LPP.
  - exact GP.
  - apply (amem_range_of_block SEGS B LAWS ly3 S3 W mem3 md3 h HUNT_SIZE); [exact HAR3 | exact Hhin | lia | rewrite RQH; lia].
  - exact AMp.
  - apply (range_addressable_of_block SEGS B LAWS ly3 S3 W mem3 md3 h HUNT_SIZE); [exact HAR3 | exact Hhin | lia | rewrite RQH; lia].
  - apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W mem3 md3 h HUNT_SIZE); [exact HAR3 | exact Hhin | lia | rewrite RQH; lia | lia].
  - exact RAp.
  - exact HVp.
  - left. rewrite Hsp. unfold TFIND_ENTRY_STK, ESTACK, LLVMF_STK in *. lia.
  - unfold off_img in *. lia.
  - exact SPp.
  - exact T1. }
intros W2 c2 Hle (fx' & ly' & S' & regs' & mem' & md' & -> & _ & Hcsr & HJ1 & HP & Hperm & (r & Hr & Hfind) & K).
rewrite R1.
apply (hb_ret_A LAWS MTT cx h i n now op nb fr len _ _ (hp2 cx h nb len) fx' ly3 S3 W regs mem3 md3 k acc TFIND_ENTRY_STK HB_RA1
  ly' S' W2 regs' mem' md' (hb_frm0_post fq fx' HF0 Hcsr) Hbase HJ Hfrs Hk Hacc HO); [unfold TFIND_ENTRY_STK, ESTACK; lia | unfold TFIND_ENTRY_STK, ESTACK, LLVMF_STK; lia
  | exact HJ1 | exact HP | exact Hperm | exact K |].
split.
- pose proof (HP 19 ltac:(unfold acallee_saved; lia)) as X. exact (eq_trans X R19).
- exists H0, r. split; [|split; [exact Hr | exact Hfind]].
  split; [exact LH|]. split; [|split; [exact QH | exact EO]].
  apply (hb_garr8_kept (w_H W) (w_H W2) mem3 mem' h _ GH). intros j Hj. rewrite length_map in Hj.
  apply K; [lia|]. rewrite Hsp. unfold TFIND_ENTRY_STK, ESTACK, LLVMF_STK in *. lia.
Qed.

Lemma hb_chain : AR_laws SEGS B -> forall cx h shf ly3 S3 (W : world SEGS) mem3 md3 k (regs : bvmap 5 word),
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k -> d_frame cx h shf W mem3 -> d_rL B cx regs ->
  exists ch, achain ly3 (aview SEGS (w_H W) mem3) (spZ regs) (s0Z regs) ch.
Proof.
intros LAWS cx h shf ly3 S3 W mem3 md3 k regs HC Hfr HrL.
pose proof HC as (HB & HJ & HFR).
pose proof HrL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25).
destruct (hb_A_range cx ly3 S3 W mem3 md3 k HJ) as (HSr & HS16 & HAr & HA32).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hs0 : s0Z regs = d_S cx) by (unfold s0Z; rewrite H8; unfold w64; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
rewrite Hs0, Hsp.
pose proof HB as ((HAFN & HraZ & _) & _).
pose proof HAFN as (_ & _ & _ & _ & _ & (Hal0 & _ & _ & _ & _ & H47 & _ & Htop0 & Htop1) & _ & Hch0 & _).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
change (spZ (c_regs cx)) with (d_S cx) in *.
destruct (Z_lt_le_dec (d_S cx) (ly_top ly3 - 16)) as [Hlt | Hge]; [|exists []; left; split; [right; left; lia | reflexivity]].
destruct Hfr as (E & HE & Hregs & _ & _ & _).
pose proof HE as (EE & _ & _ & _ & _ & _).
pose proof (Forall_inv Hregs) as HRSAVE.
assert (USP2 : bv_unsigned (ew E 2) = d_S cx) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (E1v : ew E 1 = Z_to_bv 64 RA_LLVMF)
  by (rewrite (EE 1%nat 1%bv eq_refl); unfold raZ in HraZ; rewrite <- HraZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (E8v : ew E 8 = Z_to_bv 64 (s0Z (c_regs cx)))
  by (rewrite (EE 8%nat 8%bv eq_refl); unfold s0Z; symmetry; apply Z_to_bv_bv_unsigned).
assert (HRD8 : rdword (aview SEGS (w_H W) mem3) (d_S cx - 8) = Some RA_LLVMF).
{ apply rdword_of_val_mem; [| unfold RA_LLVMF; lia].
  replace (d_S cx - 8) with (d_S cx + (-8)) by lia.
  apply (field_of_region E (rd W mem3) AT_STK (d_S cx) dsave_chunks (-104) 0 0 0 (-8) 8%N (SOff 1 0) RA_LLVMF HRSAVE
    USP2 ltac:(vm_compute; tauto) ltac:(cbn [sv_denot]; rewrite E1v, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
    ltac:(cbn; unfold RA_LLVMF; lia) ltac:(cbn; lia)). }
assert (HRD16 : rdword (aview SEGS (w_H W) mem3) (d_S cx - 16) = Some (s0Z (c_regs cx))).
{ apply rdword_of_val_mem; [| unfold s0Z; apply bv_unsigned_in_range].
  replace (d_S cx - 16) with (d_S cx + (-16)) by lia.
  apply (field_of_region E (rd W mem3) AT_STK (d_S cx) dsave_chunks (-104) 0 0 0 (-16) 8%N (SOff 8 0)
    (s0Z (c_regs cx)) HRSAVE USP2 ltac:(vm_compute; tauto)
    ltac:(cbn [sv_denot]; rewrite E8v, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
    ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Rr; change (bv_modulus 64) with (2 ^ 64) in Rr; cbn [Z.of_N Z.mul]; clear - Rr; lia)
    ltac:(cbn; lia)). }
set (V0 := s0Z (c_regs cx)) in *.
exists [(d_S cx, RA_LLVMF, V0)]. right.
split; [lia|]. split; [exact Hlt|]. split; [pose proof (Z.div_mod (d_S cx) 16 ltac:(lia)); lia|].
split; [|apply Forall_cons; [cbn; lia | apply Forall_nil]].
cbn [fpchain]. split; [reflexivity|]. split; [pose proof (Z.div_mod (d_S cx) 16 ltac:(lia)); lia|].
split; [exact HRD8|]. split; [exact HRD16|]. split; [unfold RA_LLVMF; lia|].
destruct (bad_next (d_S cx) (ly_top ly3) V0) eqn:Hbn; [reflexivity|].
unfold bad_next in Hbn. apply Bool.orb_false_elim in Hbn as [Hbn Hbn3]. apply Bool.orb_false_elim in Hbn as [Hbn1 Hbn2].
apply Z.leb_gt in Hbn1. apply Z.leb_gt in Hbn2. apply Bool.negb_false_iff, Z.eqb_eq in Hbn3.
destruct Hch0 as [(Hc & _) | (Hc1 & Hc2 & Hc3 & Hc4 & _)].
- exfalso. rewrite Etop in Hbn2. unfold LLVMF_STK in *. lia.
- cbn [fpchain] in Hc4 |- *. destruct Hc4 as (rv & Hrv & Hrv4). exists rv. split; [|exact Hrv4].
  rewrite <- Hrv. apply rdword_ext. intros q Hq. apply F1; [|unfold LLVMF_STK in *; lia]. split; [unfold LLVMF_STK in *; lia|].
  unfold LLVMF_STK in *; lia.
Qed.

Lemma hb_blk2 : AR_laws SEGS B -> forall ly S (W : world SEGS) mem md x y l,
  AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (x :: y :: l) ->
  zdisjoint (fst x, req_size (snd x)) (fst y, req_size (snd y)).
Proof.
intros LAWS ly S W mem md x y l HAR HP.
destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
apply (pairwise_zdisjoint_split _ _ _ Hp).
apply (map_split_2 (fun b0 : Z * Z => (fst b0, req_size (snd b0)))).
assert (Hx : In x (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
apply in_split in Hx as (a & b & Eab).
rewrite Eab in HP. apply Permutation_sym in HP. apply Permutation_cons_app_inv in HP.
assert (Hy : In y (a ++ b)) by (apply (Permutation_in _ HP); left; reflexivity).
apply in_app_or in Hy as [Hy | Hy].
- apply in_split in Hy as (c & d & ->). exists c, d, b. right. rewrite Eab, <- app_assoc. reflexivity.
- apply in_split in Hy as (c & d & ->). exists a, c, d. left. rewrite Eab. reflexivity.
Qed.

Lemma hb_nth_map_seq : forall (f : nat -> Z) n j d, (j < n)%nat -> nth j (map f (seq 0 n)) d = f j.
Proof.
intros f n j d Hj. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; lia).
rewrite map_nth, seq_nth by lia. reflexivity.
Qed.

Lemma hb_bytes : forall (W : world SEGS) (m : word -> option byte) a (n : nat),
  (forall j, 0 <= j < Z.of_nat n -> apresent (w_H W) m (a + j)) ->
  exists O : list byte, length O = n /\ garr8 SEGS (rd W m) a (map (fun b : byte => bv_unsigned b) O).
Proof.
intros W m a n HP.
set (g := fun j : nat => match m (Z_to_bv 64 (a + Z.of_nat j)) with Some b => b | None => Z_to_bv 8 0 end).
exists (map g (seq 0 n)). split; [rewrite length_map, length_seq; reflexivity|].
intros j Hj. rewrite !length_map, length_seq in Hj.
assert (E : nth j (map (fun b : byte => bv_unsigned b) (map g (seq 0 n))) 0 = bv_unsigned (g j)).
{ rewrite map_map. apply (hb_nth_map_seq (fun x => bv_unsigned (g x))). exact Hj. }
rewrite E. destruct (HP (Z.of_nat j) ltac:(lia)) as (Hh & b & Hb).
assert (Eg : g j = b) by (unfold g; rewrite Hb; reflexivity). rewrite Eg.
pose proof (bv_unsigned_in_range 8 b) as Rb. change (bv_modulus 8) with 256 in Rb.
split; [|lia].
intros q Hq. assert (q = 0%nat) by lia. subst q. cbn [Z.of_nat]. rewrite Z.add_0_r.
unfold mbyte, mrestrict. rewrite Hh, Hb. f_equal. rewrite le_byte_1 by lia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma hb_c34 : AR_laws SEGS B -> PALib B -> MT = ameter_triv -> treac_hunt_observe_spec B ->
  d_ro_hyps B -> d_can_hyps B tfib_K -> dimg_consts_of_ro_stmt B ->
  forall cx h i n now op nb fr len W c, hc3 cx h i n now op nb fr len W c -> SRr SEGS W c (hc4 cx h i n now op nb fr len).
Proof.
intros LAWS TL MTT THOBS HRO HCAN HDCRO cx h i n now op nb fr len W c Hc.
destruct Hc as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HF0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc & HO & HP3).
destruct HP3 as (R1 & R10 & R11 & R12 & R13 & R14 & H0 & idx & HH0 & Hfind & R19).
pose proof HH0 as (LH & GH & QH & EO).
pose proof HO as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & Hcl & H248 & Hlen & Hnb & Hnc & R22 & R23 & R24 & R26 & R27 & Hbody).
pose proof HrL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25).
pose proof Hbody as (T0 & G0 & Lk0 & H1 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & Hcan & Hstk & Hawr).
pose proof Hobjs as (LT & GT & QT & LG & GG & QG & LL & GL & QL & GO & LH1 & GH1 & QH1 & EO1).
assert (Hctx : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k Hctx)
  as (HSmod & HSlo & HShi & HFB1 & HFB2 & HFBapp & HFBimg & HFBmod & HFpres & HSHpres & HWpres & HAR3 & Hin3 & EFB3 & EFL3).
destruct (hb_A_range cx ly3 S3 W mem3 md3 k HJ) as (HSr & HS16 & HAr & HA32).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hgeo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). rewrite fs6 in G2, G7.
pose proof (hb_h_in cx h n _ dsh_rec ly3 S3 W mem3 Hbody) as Hhin.
destruct (al_blocks _ _ LAWS ly3 S3 W mem3 md3 h HUNT_SIZE HAR3 Hhin) as (Hh16 & Hh4096 & Hhc & Hhapp & _).
assert (RQH : req_size HUNT_SIZE = 480) by reflexivity.
pose proof Hblocks as (HPb & HNb & _ & Hboff).
destruct (hb_chain LAWS cx h dsh_rec ly3 S3 W mem3 md3 k regs Hctx Hframe HrL) as (ch & Hch).
destruct (hb_bytes W mem3 (d_obj cx OS) 24) as (O & LO & GOs).
{ intros j Hj. apply (proj2 (Hawr (d_obj cx OS + j) ltac:(unfold d_obj, dobj_off, DFRAME_SIZE; cbn in Hj; lia))). }
set (FBl := hfb cx nb len).
assert (LFB : length FBl = 50%nat) by (unfold FBl, hfb; rewrite length_firstn, length_app, repeat_length; lia).
assert (RHS : 0 <= REAC_HUNT_OBSERVE_STK <= 32000) by (split; vm_compute; congruence).
assert (DEP : 1 <= REAC_HUNT_OBSERVE_DEPTH) by (vm_compute; congruence).
destruct (HDCRO LAWS HRO ly3 S3 W mem3 md3 HAR3 Himg) as (_ & _ & _ & _ & (VKM & VKT & _ & _) & _).
set (FR := firstn (Z.to_nat len) (rest_of (c_pl cx) nb)) in *.
assert (LFR : length FR = Z.to_nat len).
{ unfold FR. rewrite length_firstn. unfold rest_of. rewrite length_skipn. pose proof Hfrm as (F1 & _). lia. }
eapply SRr_mono.
{ apply (THOBS fq LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)]
    ly3 S3 W mem3 md3 k regs ch h fr len now (d_obj cx OS) h HUNT_SIZE H0 FBl O); try assumption.
  - rewrite R1. unfold w64. apply ret_ok_codeptr_v; unfold HB_RA2; lia.
  - unfold raZ. rewrite R1. unfold w64. pose proof pa_B_ok as (HB0 & HB1 & _).
    pose proof pa_base_lo as HBL. unfold IMG_LO in HBL. rewrite unsigned_lit_small by (unfold HB_RA2; lia). unfold HB_RA2. lia.
  - rewrite Hsp. pose proof (Z.div_mod (d_A cx) 32 ltac:(lia)). lia.
  - rewrite Hsp. unfold LLVMF_STK in *. lia.
  - rewrite Hsp. lia.
  - rewrite Hfrs. cbn. lia.
  - pose proof Hfrm as (F1 & _). unfold REC_MAX in F1. lia.
  - unfold d_obj, dobj_off. lia.
  - lia.
  - pose proof (Z.div_mod h 16 ltac:(lia)). lia.
  - lia.
  - rewrite RQH. lia.
  - intros a Ha. right; right; left. exists h, HUNT_SIZE. split; [exact Hhin|]. split; [|rewrite RQH; lia].
    exact (Forall_inv HNb).
  - intros L50. pose proof Hfrm as (F1 & F2 & Fnc & F3).
    assert (Efr : fr <> 0) by (intros E0; specialize (F2 E0); lia).
    pose proof (hb_fr_in cx h n fr len dsh_rec ly3 S3 W mem3 Hbody Efr) as Hfin.
    destruct (al_blocks _ _ LAWS ly3 S3 W mem3 md3 fr len HAR3 Hfin) as (Hf16 & Hf4096 & Hfc & Hfapp & _).
    assert (RQF : req_size len = len) by (unfold req_size; destruct (Z.eqb_spec len 0); lia).
    split; [lia|]. split; [exists fr, len; split; [exact Hfin | lia]|]. split.
    + unfold dxb in HPb. replace (fr =? 0) with false in HPb by (symmetry; apply Z.eqb_neq; exact Efr). cbn [app] in HPb.
      pose proof (hb_blk2 LAWS ly3 S3 W mem3 md3 _ _ _ HAR3 HPb) as D. unfold zdisjoint in D. cbn [fst snd] in D.
      rewrite RQF, RQH in D. lia.
    + unfold FBl, hfb. change (firstn (Z.to_nat len) (rest_of (c_pl cx) nb)) with FR.
      rewrite firstn_app, LFR. replace (50 - Z.to_nat len)%nat with 0%nat by lia.
      rewrite firstn_O, app_nil_r.
      change (firstn (Z.to_nat len) (rest_of (c_pl cx) nb)) with FR in F3.
      pose proof (garr8_sub_x SEGS _ fr _ 0 50 F3 ltac:(rewrite length_map, LFR; change (0 + 50)%nat with (Z.to_nat 50); apply Z2Nat.inj_le; lia)) as X.
      rewrite Z.add_0_r in X. cbn [skipn] in X. rewrite <- firstn_map. exact X.
  - intros _. split; [|split].
    + unfold tho_out. split; [unfold d_obj, dobj_off; pose proof (Z.div_mod (d_FB cx) 32 ltac:(lia)); lia|].
      split; [unfold d_obj, dobj_off; lia|].
      split; [apply (amem_range_sub_app (d_FB cx) 4096); [exact HFBapp | lia | unfold d_obj, dobj_off; lia | unfold d_obj, dobj_off; lia | lia]|].
      split; [right; rewrite Hsp; unfold d_obj, dobj_off, LLVMF_STK in *; lia|].
      split; [left; exists DFRAME_CLASS, (c_fpos cx); split; [exact Hin3|]; rewrite EFB3; change (fs_frame_bytes DFRAME_CLASS) with 4096; unfold d_obj, dobj_off; lia|].
      split; [unfold d_obj, dobj_off; apply (hb_ra_obj cx dsh_rec W mem3 2992 24 Hshadow); [lia | lia | lia | lia | vm_compute; reflexivity]|].
      split; [apply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W mem3 md3 DFRAME_CLASS (c_fpos cx)); [exact HAR3 | exact Hin3 | rewrite EFB3; unfold d_obj, dobj_off; lia | rewrite EFB3; change (fs_frame_bytes DFRAME_CLASS) with 4096; unfold d_obj, dobj_off; lia | lia]|].
      split; [intros a Ha; apply Hawr; unfold d_obj, dobj_off, DFRAME_SIZE in *; lia|].
      split; [exact LO|]. split; [exact GOs|].
      left. exists DFRAME_CLASS, (c_fpos cx). split; [exact Hin3|]. rewrite EFB3. change (fs_frame_bytes DFRAME_CLASS) with 4096.
      unfold d_obj, dobj_off. lia.
    + unfold d_obj, dobj_off, HUNT_SIZE in *. lia.
    + intros L50. pose proof Hfrm as (F1 & F2 & Fnc & F3).
      assert (Efr : fr <> 0) by (intros E0; specialize (F2 E0); lia).
      pose proof (hb_fr_in cx h n fr len dsh_rec ly3 S3 W mem3 Hbody Efr) as Hfin.
      pose proof (sep_block_frame SEGS B LAWS ly3 S3 W mem3 md3 fr len DFRAME_CLASS (c_fpos cx) HAR3 Hfin Hin3) as D.
      unfold zdisjoint in D. cbn [fst snd] in D. rewrite EFB3 in D. change (fs_frame_bytes DFRAME_CLASS) with 4096 in D.
      assert (RQF : req_size len = len) by (unfold req_size; destruct (Z.eqb_spec len 0); lia). rewrite RQF in D.
      unfold d_obj, dobj_off. lia. }
intros W2 c2 Hle (fx' & ly2 & S2 & regs2 & mem2 & md2 & r & H' & -> & _ & Hcsr & HJ2 & HP & R10' & Hfr2 & Hperm & K & GH' & QH' & Hr & HM).
rewrite R1.
destruct K as (K1 & K2 & K3 & K4 & K5 & K6).
assert (Hfrs2 : frames S2 = [(DFRAME_CLASS, c_fpos cx)]) by (rewrite Hfr2; exact Hfrs).
assert (Hctx2 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly2 S2 W2 mem2 md2 k) by (split; [exact Hbase | split; [exact HJ2 | exact Hfrs2]]).
destruct (hb_tho_facts H0 FBl O len now (d_obj cx OS) r H'
  (fun A => garr8 SEGS (mrestrict (w_H W2) mem2) (d_obj cx OS) (map (fun b : byte => bv_unsigned b) A))
  LH QH LFB ltac:(unfold d_obj, dobj_off; lia) QH' Hr HM) as (EH' & HA).
assert (EO' : firstn 6 (skipn 412 H') = our_of (c_pl cx)).
{ change (firstn 6 (skipn 412 H')) with (sub H' 412 6). rewrite EH'. exact EO. }
assert (LH' : length H' = 480%nat) by (destruct QH' as (L' & _); exact L').
assert (FBr : 0 <= d_FB cx /\ d_FB cx + 4096 <= alloc_ceiling) by lia.
assert (SHb : 2147450880 <= shadow_addr (d_FB cx) /\ shadow_addr (d_FB cx) + 512 <= 17594333495296).
{ unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos (d_FB cx) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_upper_bound (d_FB cx + 4096) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
  assert ((d_FB cx + 4096) / 8 = d_FB cx / 8 + 512)
    by (replace (d_FB cx + 4096) with (d_FB cx + 512 * 8) by lia; rewrite Z.div_add by lia; reflexivity). lia. }
assert (Happ : forall a, in_app a 1 -> ~ (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512)).
{ intros a Ha Hs. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Ha. lia. }
assert (KF : forall a, d_FB cx <= a < d_FB cx + 4096 -> ~ (d_obj cx OS <= a < d_obj cx OS + 24) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha Hs. apply (K4 DFRAME_CLASS (c_fpos cx) a Hin3).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFB3. change (fs_frame_bytes DFRAME_CLASS) with 4096. lia.
  - unfold tho_wr. intros [Hh | (_ & Hs')]; [unfold HUNT_SIZE in *; lia | exact (Hs Hs')]. }
assert (KSH : forall a, shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512 ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha. apply (K4 DFRAME_CLASS (c_fpos cx) a Hin3).
  - right. unfold in_zr. cbn [fst snd]. rewrite EFB3. change (fs_frame_bytes DFRAME_CLASS / 8) with 512. lia.
  - unfold tho_wr. intros [Hh | (_ & Hs')].
    + apply (Happ a); [apply (in_app_sub h (req_size HUNT_SIZE)); [exact Hhapp | lia | lia | rewrite RQH; lia] | exact Ha].
    + apply (Happ a); [apply (in_app_sub (d_FB cx) 4096); [exact HFBapp | unfold d_obj, dobj_off in Hs'; lia | lia | unfold d_obj, dobj_off in Hs'; lia] | exact Ha]. }
assert (KS : forall a, (d_S cx - 104 <= a < d_S cx) \/ (d_A cx <= a < d_A cx + 472) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha. apply K1.
  - unfold LLVMF_STK in *. lia.
  - rewrite Hsp. lia.
  - unfold tho_wr, d_obj, dobj_off. intros [Hh | (_ & Hs')]; unfold LLVMF_STK in *; lia. }
destruct (hb_frame_tr LAWS cx h dsh_rec W mem3 ly2 S2 W2 mem2 md2 k Hframe Hshadow Hctx2) as [Hframe2 Hshadow2].
{ intros a Ha. unfold hb_regb in Ha. destruct Ha as [Ha | [Ha | [Ha | [Ha | Ha]]]].
  - apply KS. left. exact Ha.
  - apply KS. right. exact Ha.
  - apply KF; unfold d_obj, dobj_off; lia.
  - apply KF; unfold d_obj, dobj_off; lia.
  - apply KSH. exact Ha. }
assert (KFR : forall j, 0 <= j < len -> fr <> 0 -> aview SEGS (w_H W2) mem2 (fr + j) = aview SEGS (w_H W) mem3 (fr + j)).
{ intros j Hj Efr. pose proof Hfrm as (F1 & F2 & Fnc & F3).
  pose proof (hb_fr_in cx h n fr len dsh_rec ly3 S3 W mem3 Hbody Efr) as Hfin.
  assert (RQF : req_size len = len) by (unfold req_size; destruct (Z.eqb_spec len 0); lia).
  apply (K2 fr len j Hfin); [rewrite RQF; lia|].
  unfold dxb in HPb. replace (fr =? 0) with false in HPb by (symmetry; apply Z.eqb_neq; exact Efr). cbn [app] in HPb.
  pose proof (hb_blk2 LAWS ly3 S3 W mem3 md3 _ _ _ HAR3 HPb) as D1. unfold zdisjoint in D1. cbn [fst snd] in D1.
  pose proof (sep_block_frame SEGS B LAWS ly3 S3 W mem3 md3 fr len DFRAME_CLASS (c_fpos cx) HAR3 Hfin Hin3) as D2.
  unfold zdisjoint in D2. cbn [fst snd] in D2. rewrite EFB3 in D2. change (fs_frame_bytes DFRAME_CLASS) with 4096 in D2.
  rewrite RQF, RQH in *. unfold tho_wr, d_obj, dobj_off. lia. }
assert (Hobjs2 : d_objs cx h T0 G0 Lk0 H' W2 mem2).
{ unfold d_objs.
  refine (conj LT (conj _ (conj QT (conj LG (conj _ (conj QG (conj LL (conj _ (conj QL (conj _ (conj LH' (conj GH' (conj QH' EO')))))))))))));
  [ apply (hb_garr8_kept (w_H W) (w_H W2) mem3 mem2 _ _ GT); rewrite length_map
  | apply (hb_garr8_kept (w_H W) (w_H W2) mem3 mem2 _ _ GG); rewrite length_map
  | apply (hb_garr8_kept (w_H W) (w_H W2) mem3 mem2 _ _ GL); rewrite length_map
  | apply (hb_garr8_kept (w_H W) (w_H W2) mem3 mem2 _ _ GO); rewrite length_map, length_our ];
  intros j Hj; apply KF; unfold d_obj, dobj_off in *; lia. }
assert (Hbody2 : d_body B cx h n (dxb fr len) dsh_rec ly2 S2 W2 mem2).
{ apply (d_body_step B MT XM_LIB RLO RHI tfib_K LAWS HRO HCAN cx h n (dxb fr len) (dxb fr len) dsh_rec dsh_rec ly3 S3 W mem3
    ly2 S2 W2 mem2 md2 k T0 G0 Lk0 H' Hbody (conj Hbase HJ2) (d_blocks_perm B cx h (dxb fr len) ly3 S3 ly2 S2 Hblocks Hperm)
    Hobjs2).
  - intros a Hc Ha. destruct (G8 Hc) as (P1 & P2 & P3 & P4).
    pose proof Hbase as ((_ & _ & _ & _ & Hpn & _) & _).
    assert (Hpin : In (c_p cx, c_n cx) (ablocks B (c_ly cx) (c_S cx))) by (destruct Hpn as [(E0 & _) | (_ & Hin)]; [lia | exact Hin]).
    assert (Hpin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3)).
    { apply (Permutation_in _ (Permutation_sym HPb)). apply in_or_app. right. right. exact Hpin. }
    assert (RQP : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
    replace a with (c_p cx + (a - c_p cx)) by lia.
    apply (K2 (c_p cx) (c_n cx) (a - c_p cx) Hpin3); [rewrite RQP; lia|].
    rewrite fs6 in P3. unfold tho_wr, d_obj, dobj_off, HUNT_SIZE in *. lia.
  - intros a Hro Ho He. apply K3; [exact (in_roP_img a Hro) | exact Ho | exact He].
  - exact Hframe2.
  - exact Hshadow2. }
assert (PR : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr regs2 rr = getr regs rr).
{ intros rr Hrr. pose proof (HP _ Hrr) as X. rewrite !Z_to_bv_bv_unsigned in X. exact X. }
unfold hc4, d_at.
exists fx', ly2, S2, regs2, mem2, md2, k, acc.
split; [reflexivity|]. split; [exact (hb_frm0_post fq fx' HF0 Hcsr)|]. split; [exact Hbase|]. split; [exact HJ2|]. split; [exact Hfrs2|]. split; [exact Hk|].
split; [pose proof HJ2 as (_ & _ & _ & _ & _ & _ & Hnev2 & _); lia|].
split; [rewrite MTT; exact I|]. split; [exact Hacc|].
split.
- unfold hoc.
  refine (conj Hi (conj Hn (conj Hnow (conj Hop (conj Hop2 (conj _ (conj _ (conj _ (conj Hcl (conj _ (conj Hlen (conj Hnb (conj Hnc
    (conj _ (conj _ (conj _ (conj _ (conj _ Hbody2)))))))))))))))))).
  + unfold d_rL, spZ in *. rewrite !PR by hb_cs. repeat split; assumption.
  + destruct Hsp0 as (Hs1' & Hs2'). split.
    * apply (hb_vm_kept (w_H W) (w_H W2) mem3 mem2 _ 8 i Hs1'). intros j Hj. apply KS. right. unfold MFRAME, LLVMF_STK in *. lia.
    * apply (hb_vm_kept (w_H W) (w_H W2) mem3 mem2 _ 8 now Hs2'). intros j Hj. apply KS. right. unfold MFRAME, LLVMF_STK in *. lia.
  + destruct Hfrm as (F1 & F2 & Fnc & F3). split; [exact F1|]. split; [exact F2|]. split; [exact Fnc|].
    apply (hb_garr8_kept (w_H W) (w_H W2) mem3 mem2 fr _ F3). intros j Hj.
    rewrite length_map, length_firstn in Hj.
    destruct (Z.eq_dec fr 0) as [E0|E0]; [specialize (F2 E0); lia|].
    apply KFR; [lia | exact E0].
  + apply (hb_vm_kept (w_H W) (w_H W2) mem3 mem2 _ 8 _ H248). intros j Hj. apply KS. right. lia.
  + rewrite PR by hb_cs. exact R22.
  + rewrite PR by hb_cs. exact R23.
  + rewrite PR by hb_cs. exact R24.
  + rewrite PR by hb_cs. exact R26.
  + rewrite PR by hb_cs. exact R27.
- exists H0, idx, r, H'. split; [exact LH|]. split; [exact QH|]. split; [exact EO|]. split; [exact Hfind|].
  split; [rewrite PR by hb_cs; exact R19|]. split; [exact R10'|]. split; [exact Hr|].
  split; [exact (conj LH' (conj GH' (conj QH' EO')))|].
  exact HA.
Qed.


Lemma hb_c56 : AR_laws SEGS B -> PALib B -> MT = ameter_triv -> tcheck_sighting_spec B ->
  forall cx h i n now op nb fr len W c, hc5 cx h i n now op nb fr len W c -> SRr SEGS W c (hc6 cx h i n now op nb fr len).
Proof.
intros LAWS TL MTT CS cx h i n now op nb fr len W c Hc.
destruct Hc as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HF0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc & HO & HP5).
destruct HP5 as (R1 & R10 & R11 & R12 & R13 & R14 & L50 & A & H' & fl & LA & GA & SF & R19 & Hfl & HH').
pose proof HO as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & Hcl & H248 & Hlen & Hnb & Hnc & R22 & R23 & R24 & R26 & R27 & Hbody).
pose proof HrL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & Hcan & Hstk & Hawr).
pose proof Hobjs as (LT & GT & QT & LG & GG & QG & LL & GL & QL & GO & LH & GH & QH & EO).
assert (Hctx : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k Hctx)
  as (HSmod & HSlo & HShi & HFB1 & HFB2 & HFBapp & HFBimg & HFBmod & HFpres & HSHpres & HWpres & HAR3 & Hin3 & EFB3 & EFL3).
destruct (hb_A_range cx ly3 S3 W mem3 md3 k HJ) as (HSr & HS16 & HAr & HA32).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hgeo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
pose proof Hfrm as (F1 & F2 & Fnc & F3).
assert (Efr : fr <> 0) by (intros E0; specialize (F2 E0); lia).
pose proof (hb_fr_in cx h n fr len dsh_rec ly3 S3 W mem3 Hbody Efr) as Hfin.
destruct (al_blocks _ _ LAWS ly3 S3 W mem3 md3 fr len HAR3 Hfin) as (Hf16 & Hf4096 & Hfc & Hfapp & _).
assert (RQF : req_size len = len) by (unfold req_size; destruct (Z.eqb_spec len 0); lia).
assert (LFR : length (firstn (Z.to_nat len) (rest_of (c_pl cx) nb)) = Z.to_nat len).
{ rewrite length_firstn. unfold rest_of. rewrite length_skipn. lia. }
assert (EFB : hfb cx nb len = firstn 50 (firstn (Z.to_nat len) (rest_of (c_pl cx) nb))).
{ unfold hfb. rewrite firstn_app. replace (50 - length (firstn (Z.to_nat len) (rest_of (c_pl cx) nb)))%nat with 0%nat by lia.
  cbn [firstn]. apply app_nil_r. }
assert (GF : garr8 SEGS (rd W mem3) fr (map (fun b : byte => bv_unsigned b) (hfb cx nb len))).
{ rewrite EFB. pose proof (garr8_sub_x SEGS _ fr _ 0 50 F3 ltac:(rewrite length_map; lia)) as X.
  rewrite skipn_map, firstn_map in X. replace (fr + Z.of_nat 0) with fr in X by lia. exact X. }
assert (LFB : length (hfb cx nb len) = 50%nat) by (rewrite EFB, length_firstn; lia).
assert (OIF : off_img fr 50).
{ pose proof Hblocks as (_ & _ & _ & Hboff). unfold dxb in Hboff.
  replace (fr =? 0) with false in Hboff by (symmetry; apply Z.eqb_neq; exact Efr).
  apply Forall_inv_tail, Forall_inv in Hboff. cbn [fst snd] in Hboff. rewrite RQF in Hboff. unfold off_img in *. lia. }
assert (DSF : d_obj cx OS + 24 <= fr \/ fr + 50 <= d_obj cx OS).
{ pose proof (sep_block_frame SEGS B LAWS ly3 S3 W mem3 md3 fr len DFRAME_CLASS (c_fpos cx) HAR3 Hfin Hin3) as X.
  unfold zdisjoint in X. cbn [fst snd] in X. rewrite EFB3, RQF in X. change (fs_frame_bytes DFRAME_CLASS) with 4096 in X.
  unfold d_obj, dobj_off. lia. }
assert (RU : forall r : bv 5, bv_unsigned r <> 8 -> getr (regupd regs 8 (Z_to_bv 64 0)) r = getr regs r).
{ intros r Hr. apply hb_regupd8. intros X. apply Hr. rewrite X. reflexivity. }
assert (E8 : getr (regupd regs 8 (Z_to_bv 64 0)) 8 = Z_to_bv 64 0) by (getr_resolve; reflexivity).
eapply SRr_mono.
{ apply (CS fq ly3 S3 W regs mem3 md3 [] (d_obj cx OS) fr (reac_frame_clean_len_c.reac_frame_clean_len_model len)
    (d_obj cx OOUR) 1 A (hfb cx nb len) (our_of (c_pl cx))).
  - apply (afn_pre_at SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W mem3 md3 k (regupd regs 8 (Z_to_bv 64 0)) TCHECK_SIGHTING_STK (d_A cx - d_S cx) [] HJ).
    + unfold spZ. rewrite RU by (vm_compute; congruence). fold (spZ regs). rewrite Hsp. lia.
    + pose proof (Z.div_mod (d_A cx) 32 ltac:(lia)). pose proof (Z.div_mod (d_S cx) 16 ltac:(lia)). lia.
    + lia.
    + unfold TCHECK_SIGHTING_STK, ESTACK; lia.
    + unfold TCHECK_SIGHTING_STK, ESTACK, LLVMF_STK; lia.
    + rewrite RU by (vm_compute; congruence). rewrite R1. unfold w64. apply ret_ok_codeptr_v; unfold HB_RA3; lia.
    + unfold raZ. rewrite RU by (vm_compute; congruence). rewrite R1. unfold w64. pose proof pa_B_ok as (HB0 & HB1 & _).
      pose proof pa_base_lo as HBL. unfold IMG_LO in HBL. rewrite unsigned_lit_small by (unfold HB_RA3; lia). unfold HB_RA3. lia.
    + rewrite RU by (vm_compute; congruence). exact Hgp.
    + rewrite RU by (vm_compute; congruence). exact Htp.
    + apply achain_low. unfold s0Z. rewrite E8, unsigned_lit_small by lia. lia.
  - exact Himg.
  - exact R10.
  - exact R11.
  - exact R12.
  - exact R13.
  - exact R14.
  - unfold d_obj, dobj_off; lia.
  - unfold d_obj, dobj_off; lia.
  - unfold d_obj, dobj_off; lia.
  - lia.
  - rewrite RQF in Hfc. lia.
  - unfold d_obj, dobj_off; lia.
  - unfold d_obj, dobj_off; lia.
  - unfold REC_MAX in F1. lia.
  - lia.
  - unfold REC_MAX in F1. lia.
  - exact LA.
  - exact GA.
  - exact LFB.
  - exact GF.
  - apply length_our.
  - exact GO.
  - apply (amem_range_sub_app (d_FB cx) 4096); [exact HFBapp | lia | unfold d_obj, dobj_off; lia | unfold d_obj, dobj_off; lia | lia].
  - apply (amem_range_of_block SEGS B LAWS ly3 S3 W mem3 md3 fr len); [exact HAR3 | exact Hfin | lia | lia].
  - apply (amem_range_sub_app (d_FB cx) 4096); [exact HFBapp | lia | unfold d_obj, dobj_off; lia | unfold d_obj, dobj_off; lia | lia].
  - unfold d_obj, dobj_off. apply (hb_ra_obj cx dsh_rec W mem3 2992 24 Hshadow); [lia | lia | lia | lia | vm_compute; reflexivity].
  - apply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W mem3 md3 DFRAME_CLASS (c_fpos cx)); [exact HAR3 | exact Hin3 | rewrite EFB3; unfold d_obj, dobj_off; lia | rewrite EFB3; change (fs_frame_bytes DFRAME_CLASS) with 4096; unfold d_obj, dobj_off; lia | lia].
  - apply (range_addressable_of_block SEGS B LAWS ly3 S3 W mem3 md3 fr len); [exact HAR3 | exact Hfin | lia | lia].
  - apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W mem3 md3 fr len); [exact HAR3 | exact Hfin | lia | lia | lia].
  - unfold d_obj, dobj_off. apply (hb_ra_obj cx dsh_rec W mem3 2128 6 Hshadow); [lia | lia | lia | lia | vm_compute; reflexivity].
  - apply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W mem3 md3 DFRAME_CLASS (c_fpos cx)); [exact HAR3 | exact Hin3 | rewrite EFB3; unfold d_obj, dobj_off; lia | rewrite EFB3; change (fs_frame_bytes DFRAME_CLASS) with 4096; unfold d_obj, dobj_off; lia | lia].
  - left. rewrite Hsp. unfold d_obj, dobj_off, TCHECK_SIGHTING_STK, ESTACK, LLVMF_STK in *. lia.
  - left. rewrite Hsp. unfold TCHECK_SIGHTING_STK, ESTACK, LLVMF_STK in *. lia.
  - unfold off_img in *. unfold d_obj, dobj_off. lia.
  - exact OIF.
  - exact DSF.
  - left. rewrite Hsp. unfold d_obj, dobj_off, TCHECK_SIGHTING_STK, ESTACK, LLVMF_STK in *. lia.
  - exact SF. }
intros W2 c2 Hle (fx' & ly' & S' & regs' & mem' & md' & -> & _ & Hcsr & HJ1 & HP & Hperm & K).
rewrite R1.
apply (hb_ret_A LAWS MTT cx h i n now op nb fr len _ _ (hp6 cx h) fx' ly3 S3 W regs mem3 md3 k acc TCHECK_SIGHTING_STK HB_RA3
  ly' S' W2 regs' mem' md' (hb_frm0_post fq fx' HF0 Hcsr) Hbase HJ Hfrs Hk Hacc HO); [unfold TCHECK_SIGHTING_STK, ESTACK; lia | unfold TCHECK_SIGHTING_STK, ESTACK, LLVMF_STK; lia
  | exact HJ1 | exact HP | exact Hperm | exact K |].
exists A, H', fl. split; [exact LA|]. split.
{ apply (hb_garr8_kept (w_H W) (w_H W2) mem3 mem' _ _ GA). intros j Hj. rewrite length_map, LA in Hj.
  apply K; [unfold d_obj, dobj_off; lia|]. rewrite Hsp. unfold d_obj, dobj_off, TCHECK_SIGHTING_STK, ESTACK, LLVMF_STK in *. lia. }
split; [pose proof (HP 19 ltac:(unfold acallee_saved; lia)) as X; exact (eq_trans X R19)|].
split; [exact Hfl|].
destruct HH' as (LH' & GH' & QH' & EO'). split; [exact LH'|]. split; [|split; [exact QH' | exact EO']].
apply (hb_garr8_kept (w_H W) (w_H W2) mem3 mem' h _ GH'). intros j Hj. rewrite length_map, LH' in Hj.
unfold HUNT_SIZE in G4. apply K; [lia|]. rewrite Hsp. unfold TCHECK_SIGHTING_STK, ESTACK, LLVMF_STK in *. lia.
Qed.

Definition hb_s67_rx (r : nat) : sv :=
  match r with 22%nat => SOff 516 2992 | 26%nat => SOff 516 2128 | _ => hb_rx r end.
Definition hb_s67_sr : list sv := map hb_s67_rx (seq 0 32).
Definition hb_s67_acs : list YP09.chunk := [YP09.mkChunk 216 (CVal 8 (SOff 564 0))].
Definition hb_s67_fcs : list YP09.chunk := [YP09.mkChunk 3000 (CVal 4 (SOff 563 0))].

Lemma hb_s67_regs_ok : forall cx E regs xs, d_E cx E -> d_rL B cx regs ->
  0 <= d_A cx < 2 ^ 64 -> getr regs 22 = w64 (d_obj cx OS) -> getr regs 26 = w64 (d_obj cx OOUR) ->
  regs_ok (d_env cx E (hb_vals regs ++ xs)) hb_s67_sr regs.
Proof.
intros cx E regs xs HE HL HA R22 R26.
destruct HE as (HER & H32 & _ & HA60 & HF516 & _).
destruct HL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25).
apply regs_ok_by_cases. intros r Hr.
cbv [all_regs In] in Hr.
assert (H2 : getr regs 2 = Z_to_bv 64 (d_A cx)) by (rewrite <- Hsp; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (HS2 : ew E 2 = Z_to_bv 64 (d_S cx)).
{ rewrite (HER 2%nat 2%bv eq_refl). unfold d_S, spZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
change AT_A with 60%nat in HA60. change AT_F with 516%nat in HF516.
repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<-|Hx] end; [ .. | contradiction ].
all: try (match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r) =>
  let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
  cbn [sv_denot];
  first
  [ rewrite getr_zero; reflexivity
  | unfold d_env; rewrite ew_havoc_old by (cbv; lia); rewrite HF516; unfold w64; rewrite hb_w64_add;
    first [ refine (eq_trans R22 _) | refine (eq_trans R26 _) ]; unfold w64, d_obj, dobj_off; reflexivity
  | rewrite Z.add_0_r; unfold d_env; rewrite ew_havoc_old by (cbv; lia);
    first [ rewrite HA60, Z_to_bv_bv_unsigned; first [exact H2 | exact H9]
          | rewrite HS2, Z_to_bv_bv_unsigned; exact H8
          | rewrite H32; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H18 ]
  | rewrite Z.add_0_r; unfold d_env, havoc; cbn [ew Nat.ltb Nat.leb Nat.sub nth hb_vals map seq Nat.add AT_X AT_FL app];
    match goal with |- getr ?rg _ = Z_to_bv 64 (bv_unsigned (getr ?rg ?x)) =>
      let y := eval vm_compute in x in change x with y end;
    rewrite Z_to_bv_bv_unsigned; reflexivity ]).
Qed.


Lemma hb_s67_le4 : forall (b0 b1 b2 b3 : byte) (j : nat), (j < 4)%nat ->
  YO0f.le_byte (bytes_le_to_Z [b0; b1; b2; b3]) 4 j = bv_unsigned (nth j [b0; b1; b2; b3] (Z_to_bv 8 0)).
Proof.
intros b0 b1 b2 b3 j Hj. rewrite Bytes.bytes_le_to_Z_le_val. cbn [map Bytes.le_val].
pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
change (bv_modulus 8) with 256 in R0, R1, R2, R3.
unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 4)) with 4294967296.
destruct j as [|[|[|[|j]]]]; [| | | | lia]; cbn [nth];
  [change (8 * Z.of_nat 0) with 0 | change (8 * Z.of_nat 1) with 8 | change (8 * Z.of_nat 2) with 16 | change (8 * Z.of_nat 3) with 24];
  rewrite Z.shiftr_div_pow2 by lia;
  [change (2 ^ 0) with 1 | change (2 ^ 8) with 256 | change (2 ^ 16) with 65536 | change (2 ^ 24) with 16777216];
  Z.div_mod_to_equations; lia.
Qed.
Lemma hb_s67_val4 : forall segs (m : word -> option byte) a (A : list byte) k,
  garr8 segs m a (map (fun b : byte => bv_unsigned b) A) -> 0 <= k -> k + 4 <= Z.of_nat (length A) ->
  val_mem segs m (a + k) 4 (u_at A k 4).
Proof.
intros segs m a A k HG Hk Hl j Hj.
assert (Hn : forall i, (i < 4)%nat -> nth_error (sub A k 4) i = nth_error A (Z.to_nat k + i))
  by (intros i Hi; unfold sub; rewrite disco_table.nth_firstn by exact Hi; apply disco_table.nth_skipn).
assert (L4 : length (sub A k 4) = 4%nat) by (apply disco_table.length_sub; lia).
replace (a + k + Z.of_nat j) with (a + Z.of_nat (Z.to_nat k + j)) by lia.
rewrite (garr8_mbyte segs m a _ (Z.to_nat k + j) HG) by (rewrite length_map; lia).
unfold u_at. pose proof (Hn j Hj) as Hnj.
destruct (sub A k 4) as [|b0 [|b1 [|b2 [|b3 [|b4 t]]]]] eqn:Hs; cbn [length] in L4; try discriminate L4.
rewrite (hb_s67_le4 b0 b1 b2 b3 j Hj).
assert (HX : nth_error (map (fun b : byte => bv_unsigned b) A) (Z.to_nat k + j) =
  Some (bv_unsigned (nth j [b0; b1; b2; b3] (Z_to_bv 8 0)))).
{ rewrite nth_error_map, <- Hnj.
  destruct j as [|[|[|[|j]]]]; [reflexivity | reflexivity | reflexivity | reflexivity | lia]. }
erewrite nth_error_nth; [reflexivity | exact HX].
Qed.


Lemma hb_s67_u4 : forall (A : list byte), 0 <= u_at A 8 4 < 2 ^ 32.
Proof.
intros A. unfold u_at. pose proof (disco_table.ble_range (sub A 8 4)) as X.
assert (L : (length (sub A 8 4) <= 4)%nat) by (unfold sub; rewrite length_firstn; lia).
split; [lia|]. eapply Z.lt_le_trans; [apply X|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma hb_s67_bad : forall E fl (A : list byte),
  sv_denot E (SOff 550 0) = w64 fl -> ew E 563 = w64 (u_at A 8 4) -> (fl <> 0 -> s_role A = 1) ->
  branch_taken BC_EQ (sv_denot E (SOff 550 0)) (sv_denot E (SLit 0)) = false ->
  branch_taken BC_NE (sv_denot E (SExt true 32 (SOff 563 0))) (sv_denot E (SLit 2)) = false -> False.
Proof.
intros E fl A H550 H563 Hfl B1 B2.
pose proof (hb_s67_u4 A) as Hu.
destruct (Z.eq_dec fl 0) as [E0 | N0].
- subst fl. rewrite H550 in B1. vm_compute in B1. discriminate B1.
- specialize (Hfl N0). unfold s_role, s32_at in Hfl.
  rewrite branch_ne_U, U_SExt, (U_atom E 563 (u_at A 8 4) H563), U_SLit in B2 by lia.
  change (2 ^ Z.of_N 32) with 4294967296 in B2. rewrite (Z.mod_small (u_at A 8 4)) in B2 by lia.
  rewrite Hfl in B2. vm_compute in B2. discriminate B2.
Qed.

Lemma hb_s67 : AR_laws SEGS B -> PALib B -> frame_flag_lawP SEGS B ->
  forall cx h i n now op nb fr len W c, hc6 cx h i n now op nb fr len W c -> SRr SEGS W c (hc7 cx h i n now op nb fr len).
Proof.
intros LAWS TL FFL cx h i n now op nb fr len W c Hc.
destruct Hc as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HF0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc & HO & HP6).
pose proof HO as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & Hcl & H248 & Hlen & Hnb & Hnc & R22 & R23 & R24 & R26 & R27 & Hbody).
destruct HP6 as (A & H' & fl & LA & GA & R19 & Hfl & HH').
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & Hcan & Hstk & Hawr).
pose proof Hframe as (E & HdE & Hregs & Hflag & Hh216 & Hh152).
destruct (hb_A_range cx ly3 S3 W mem3 md3 k HJ) as (HSr & HS16 & HAr & HA32).
assert (HctxD : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HctxD)
  as (HSmod & HSlo & HShi & HFB1 & HFB2 & HFBapp & HFBimg & HFBmod & HFpres & HSHpres & HWpres & HAR3 & Hin3 & EFB3 & EFL3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold LLVMF_STK in HSr; lia).
pose proof (hb_h_in cx h n _ dsh_rec ly3 S3 W mem3 Hbody) as Hhin.
destruct (al_blocks _ _ LAWS ly3 S3 W mem3 md3 h HUNT_SIZE HAR3 Hhin) as (Hh16 & Hh4096 & Hhc & Hhapp & _).
assert (RQH : req_size HUNT_SIZE = 480) by reflexivity. rewrite RQH in Hhc.
set (rv := u_at A 8 4).
pose proof (hb_s67_u4 A) as Rv. fold rv in Rv.
set (vals := hb_vals regs ++ [w64 rv; w64 h]).
assert (EV63 : ew (d_env cx E vals) 563 = w64 rv).
{ unfold d_env. change 563%nat with (AT_FL + 33)%nat.
  rewrite (ew_havoc_new E AT_FL _ 33 (Z_to_bv 64 0)) by (apply Nat.ltb_lt; vm_compute; reflexivity). reflexivity. }
assert (EV64 : ew (d_env cx E vals) 564 = w64 h).
{ unfold d_env. change 564%nat with (AT_FL + 34)%nat.
  rewrite (ew_havoc_new E AT_FL _ 34 (Z_to_bv 64 0)) by (apply Nat.ltb_lt; vm_compute; reflexivity). reflexivity. }
pose proof (hb_s67_regs_ok cx E regs [w64 rv; w64 h] HdE HrL HAr2 R22 R26) as ROK.
assert (D50 : sv_denot (d_env cx E vals) (SOff 550 0) = w64 fl).
{ rewrite <- R19, (ROK 19%bv). f_equal; vm_compute; reflexivity. }
assert (ACS : Forall (YP09.chunk_ok SEGS (d_env cx E vals) (rd W mem3) (d_A cx)) hb_s67_acs).
{ apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ _ _ 8 _ h).
  - cbn [sv_denot]. rewrite EV64, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - lia.
  - exact Hh216. }
assert (FCS : Forall (YP09.chunk_ok SEGS (d_env cx E vals) (rd W mem3) (d_FB cx)) hb_s67_fcs).
{ apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ _ _ 4 _ rv).
  - cbn [sv_denot]. rewrite EV63, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  - change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). lia.
  - lia.
  - change (N.to_nat 4) with 4%nat.
    pose proof (hb_s67_val4 SEGS (rd W mem3) (d_obj cx OS) A 8 GA ltac:(lia) ltac:(rewrite LA; lia)) as X.
    unfold d_obj, dobj_off in X. replace (d_FB cx + 3000) with (d_FB cx + 2992 + 8) by lia. exact X. }
assert (FA : facts_ok (d_env cx E vals) (d_facts [] []))
  by exact (d_facts_ok B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k E vals [] [] HctxD HdE I I).
pose proof (d_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E HB_RA3 hb_s67_sr vals
  hb_s67_acs hb_s67_fcs [] (d_facts [] []) HctxD HdE Hregs Hflag ROK FA ACS FCS
  (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_d in HS.
hb_ro_base HS 516%nat. hb_ro_base HS 529%nat. hb_ro_base HS 60%nat.
assert (HEI : img_env VAL A_LIM (d_env cx E vals)).
{ destruct HdE as (_ & _ & HI & _). intros a Ha. unfold d_env. rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia). exact (HI a Ha). }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E vals) (rd W mem3)) by constructor.
pose (RUN := paj_run (fx := fq) B LAWS).
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
unfold cfg_at. change (w64 (BASE + HB_RA3)) with (Z_to_bv 64 (BASE + HB_RA3)).
psrr_branch_tok RUN BR HS SHOK HBspan.
2: paj_run_tok RUN HS HJ SHOK HBspan.
2: cbn [ss_mem]; repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
2: assert (Hpt1 := hb_frame_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity));
   assert (Hptr1 := hb_frame_ro_pt _ _ _ _ HFr ltac:(vm_compute; reflexivity));
   clear HF HFr HG;
   psrr_branch_tok RUN BR HS SHOK HBspan.
3: exfalso; lazymatch goal with B1 : branch_taken BC_EQ _ _ = false, B2 : branch_taken BC_NE _ _ = false |- _ =>
     exact (hb_s67_bad _ fl A D50 EV63 Hfl B1 B2) end.
2: paj_run_tok RUN HS HJ SHOK HBspan.
2: cbn [ss_mem]; repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
2: assert (Hpt2 := hb_frame_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity));
   assert (Hptr2 := hb_frame_ro_pt _ _ _ _ HFr ltac:(vm_compute; reflexivity));
   clear HF HFr HG;
   lazymatch type of Hpt2 with forall x, ms_mem ?m2 x = ms_mem ?m1 x =>
     assert (Hpt : forall x, ms_mem m2 x = mem3 x) by (intros x; rewrite Hpt2; apply Hpt1);
     assert (Hptr : forall x, rd W (ms_mem m2) x = rd W mem3 x) by (intros x; rewrite Hptr2; apply Hptr1);
     clear Hpt1 Hptr1 Hpt2 Hptr2; clear m1; rename m2 into ms end.
1: paj_run_tok RUN HS HJ SHOK HBspan.
1: cbn [ss_mem]; repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
1: assert (Hpt := hb_frame_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity));
   assert (Hptr := hb_frame_ro_pt _ _ _ _ HFr ltac:(vm_compute; reflexivity));
   clear HF HFr HG.
all: rewrite (pa_sigma_check_table (PI := PI)) in HS.
all: assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 20; 22; 23; 24; 25; 26; 27]%bv -> getr (ms_regs ms) r = getr regs r)
  by (intros r Hr; rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms r HS), (ROK r);
      cbv [In] in Hr; repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]); destruct Hr).
all: pose proof (st_ok_restrict_mkst SEGS (w_H W) _ _ ms HS eq_refl) as Hms.
all: cbn [ss_pc setpc] in Hms.
all: lazymatch type of HS with st_ok _ ?Ex (setpc ?ssx _) ?msx =>
  assert (HSpi : st_ok_pi SEGS VAL Ex (setpc ssx AF_check_table) msx) by exact HS end.
all: lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md4 := mdx) in * end.
all: assert (Hctx4 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms) md4 k)
  by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
all: assert (H216' := hb_val_mem_pt _ _ _ _ _ Hptr Hh216).
all: assert (H152' := hb_val_mem_pt _ _ _ _ _ Hptr Hh152).
all: destruct (d_land B MT XM_LIB RLO RHI tfib_K LAWS FFL fq cx h dsh_rec ly3 S3 W md4 k (d_env cx E vals) _ ms Hctx4
  (d_E_env cx E _ HdE) (d_env_fl cx E _) HSpi ltac:(vm_compute; reflexivity) H216' H152') as [Hframe4 Hshadow4].
all: assert (Hbody4 : d_body B cx h n (dxb fr len) dsh_rec ly3 S3 W (ms_mem ms))
  by (apply (d_body_rt B cx h n n (dxb fr len) dsh_rec dsh_rec ly3 S3 W mem3 (ms_mem ms) (d_A cx) (d_A cx) (fun _ => False) Hbody);
      [ unfold LLVMF_STK; lia | lia | intros a [] | intros a Ha _; apply aview_eq_of; apply Hptr
      | intros a _ [Hh [b Hb]]; split; [exact Hh|]; exists b; rewrite Hpt; exact Hb | exact Hframe4 | exact Hshadow4 | lia ]).
all: apply SRr_ret; unfold hc7, d_at.
all: exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md4, k, acc.
all: split; [unfold cfg_at, w64; rewrite <- Hms; reflexivity|].
all: split; [exact HF0|]; split; [exact Hbase|]; split; [exact HJ|]; split; [exact Hfrs|]; split; [exact Hk|].
all: split; [exact Hnev|]; split; [exact Hmo|]; split; [exact Hacc|].
all: split; [|split; [|split]].
all: lazymatch goal with
  | |- hoc _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    unfold hoc;
    refine (conj Hi (conj Hn (conj Hnow (conj Hop (conj Hop2 (conj _ (conj _ (conj _ (conj Hcl (conj _ (conj Hlen (conj Hnb (conj Hnc
      (conj _ (conj _ (conj _ (conj _ (conj _ Hbody4))))))))))))))))));
    [ destruct HrL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25); unfold d_rL, spZ in *;
      rewrite !RG by (cbv; tauto); repeat split; assumption
    | destruct Hsp0 as (Hs1 & Hs2); split; eapply hb_val_mem_pt; [exact Hptr | exact Hs1 | exact Hptr | exact Hs2]
    | destruct Hfrm as (F1 & F2 & Fnc & F3); split; [exact F1|]; split; [exact F2|]; split; [exact Fnc|]; exact (hb_garr8_pt _ _ _ _ Hptr F3)
    | exact (hb_val_mem_pt _ _ _ _ _ Hptr H248)
    | rewrite RG by (cbv; tauto); exact R22
    | rewrite RG by (cbv; tauto); exact R23
    | rewrite RG by (cbv; tauto); exact R24
    | rewrite RG by (cbv; tauto); exact R26
    | rewrite RG by (cbv; tauto); exact R27 ]
  | |- getr _ 1 = _ =>
    rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 1%bv HS);
    match goal with |- context [sr_get ?sr ?r] => let y := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with y end;
    unfold w64; exact (codeptr_val _ HB_RA4 HEI)
  | |- getr _ 10 = _ =>
    rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 10%bv HS);
    match goal with |- context [sr_get ?sr ?r] => let y := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with y end;
    cbn [sv_denot]; rewrite EV64, Z.add_0_r; unfold w64; apply Z_to_bv_bv_unsigned
  | |- exists _, _ =>
    exists H'; destruct HH' as (LH & GH & QH & EO); split; [exact LH|]; split; [exact (hb_garr8_pt _ _ _ _ Hptr GH)|];
    split; [exact QH | exact EO]
  end.
Qed.

Lemma hb_c78 : AR_laws SEGS B -> PALib B ->
  (forall fq : YK11.FPState, abcmp_realizes (fx := fq) SEGS B (SIGMA DS___interceptor_trampoline_bcmp)) ->
  MT = ameter_triv ->
  forall cx h i n now op nb fr len W c, hc7 cx h i n now op nb fr len W c -> SRr SEGS W c (hc8 cx h i n now op nb fr len).
Proof.
intros LAWS TL ABCMP MTT cx h i n now op nb fr len W c Hc.
destruct Hc as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HF0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc & HO & R1 & R10 & H' & HH).
pose proof HO as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & Hcl & H248 & Hlen & Hnb & Hnc & R22 & R23 & R24 & R26 & R27 & Hbody).
pose proof HrL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & Hcan & Hstk & Hawr).
destruct HH as (LH & GH & QH & EO).
assert (Hctx : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k Hctx)
  as (HSmod & HSlo & HShi & HFB1 & HFB2 & HFBapp & HFBimg & HFBmod & HFpres & HSHpres & HWpres & HAR3 & Hin3 & EFB3 & EFL3).
destruct (hb_A_range cx ly3 S3 W mem3 md3 k HJ) as (HSr & HS16 & HAr & HA32).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hgeo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
pose proof (hb_h_in cx h n _ dsh_rec ly3 S3 W mem3 Hbody) as Hhin.
destruct (al_blocks _ _ LAWS ly3 S3 W mem3 md3 h HUNT_SIZE HAR3 Hhin) as (Hh16 & Hh4096 & Hhc & Hhapp & _).
assert (RQH : req_size HUNT_SIZE = 480) by reflexivity.
pose proof Hblocks as (_ & _ & _ & Hboff). apply Forall_inv in Hboff. cbn [fst snd] in Hboff. rewrite RQH in Hboff.
set (T := sub H' 0 400).
assert (ET : T = firstn 400 H') by reflexivity.
assert (LTT : length T = 400%nat) by (rewrite ET, length_firstn; lia).
assert (GT' : garr8 SEGS (rd W mem3) h (map (fun b : byte => bv_unsigned b) T)).
{ pose proof (garr8_sub_x SEGS _ h _ 0 400 GH ltac:(rewrite length_map; lia)) as X.
  rewrite Z.add_0_r in X. cbn [skipn] in X. rewrite ET, <- firstn_map. exact X. }
destruct QH as (_ & (T1 & T2 & T3 & _) & _).
assert (RU : forall r : bv 5, bv_unsigned r <> 8 -> getr (regupd regs 8 (Z_to_bv 64 0)) r = getr regs r).
{ intros r Hr. apply hb_regupd8. intros X. apply Hr. rewrite X. reflexivity. }
assert (E8 : getr (regupd regs 8 (Z_to_bv 64 0)) 8 = Z_to_bv 64 0) by (getr_resolve; reflexivity).
eapply SRr_mono.
{ apply (pb_check_table B LAWS TL ABCMP fq ly3 S3 W regs mem3 md3 [] h T).
  - apply (afn_pre_at SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W mem3 md3 k (regupd regs 8 (Z_to_bv 64 0)) TCHECK_TABLE_STK (d_A cx - d_S cx) [] HJ).
    + unfold spZ. rewrite RU by (vm_compute; congruence). fold (spZ regs). rewrite Hsp. lia.
    + pose proof (Z.div_mod (d_A cx) 32 ltac:(lia)). pose proof (Z.div_mod (d_S cx) 16 ltac:(lia)). lia.
    + lia.
    + unfold TCHECK_TABLE_STK, ESTACK; lia.
    + unfold TCHECK_TABLE_STK, ESTACK, LLVMF_STK; lia.
    + rewrite RU by (vm_compute; congruence). rewrite R1. unfold w64. apply ret_ok_codeptr_v; unfold HB_RA4; lia.
    + unfold raZ. rewrite RU by (vm_compute; congruence). rewrite R1. unfold w64. pose proof pa_B_ok as (HB0 & HB1 & _).
      pose proof pa_base_lo as HBL. unfold IMG_LO in HBL. rewrite unsigned_lit_small by (unfold HB_RA4; lia). unfold HB_RA4. lia.
    + rewrite RU by (vm_compute; congruence). exact Hgp.
    + rewrite RU by (vm_compute; congruence). exact Htp.
    + apply achain_low. unfold s0Z. rewrite E8, unsigned_lit_small by lia. lia.
  - exact Himg.
  - exact R10.
  - lia.
  - lia.
  - lia.
  - exact LTT.
  - exact GT'.
  - apply (amem_range_of_block SEGS B LAWS ly3 S3 W mem3 md3 h HUNT_SIZE); [exact HAR3 | exact Hhin | lia | rewrite RQH; lia].
  - apply (range_addressable_of_block SEGS B LAWS ly3 S3 W mem3 md3 h HUNT_SIZE); [exact HAR3 | exact Hhin | lia | rewrite RQH; lia].
  - apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W mem3 md3 h HUNT_SIZE); [exact HAR3 | exact Hhin | lia | rewrite RQH; lia | lia].
  - left. rewrite Hsp. unfold TCHECK_TABLE_STK, ESTACK, LLVMF_STK in *. lia.
  - unfold off_img in *. lia.
  - rewrite ET. exact T1.
  - rewrite ET. exact T2.
  - rewrite ET. exact T3. }
intros W2 c2 Hle (fx' & ly' & S' & regs' & mem' & md' & -> & _ & Hcsr & HJ1 & HP & Hperm & K).
rewrite R1.
apply (hb_ret_A LAWS MTT cx h i n now op nb fr len _ _ (fun _ _ _ => True) fx' ly3 S3 W regs mem3 md3 k acc TCHECK_TABLE_STK HB_RA4
  ly' S' W2 regs' mem' md' (hb_frm0_post fq fx' HF0 Hcsr) Hbase HJ Hfrs Hk Hacc HO); [unfold TCHECK_TABLE_STK, ESTACK; lia | unfold TCHECK_TABLE_STK, ESTACK, LLVMF_STK; lia
  | exact HJ1 | exact HP | exact Hperm | exact K | exact I].
Qed.

Lemma hb_s8e_regs_ok : forall cx E regs ex, d_E cx E -> d_rL B cx regs ->
  0 <= d_A cx < 2 ^ 64 ->
  regs_ok (d_env cx E (hb_vals regs ++ ex)) hb_sr regs.
Proof.
intros cx E regs ex HE HL HA.
destruct HE as (HER & H32 & _ & HA60 & _ & _).
destruct HL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25).
apply regs_ok_by_cases. intros r Hr.
cbv [all_regs In] in Hr.
assert (H2 : getr regs 2 = Z_to_bv 64 (d_A cx)) by (rewrite <- Hsp; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (HS2 : ew E 2 = Z_to_bv 64 (d_S cx)).
{ rewrite (HER 2%nat 2%bv eq_refl). unfold d_S, spZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
change AT_A with 60%nat in HA60.
repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<-|Hx] end; [ .. | contradiction ].
all: try (match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r) =>
  let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
  cbn [sv_denot];
  first
  [ rewrite getr_zero; reflexivity
  | rewrite Z.add_0_r; unfold d_env; rewrite ew_havoc_old by (cbv; lia);
    first [ rewrite HA60, Z_to_bv_bv_unsigned; first [exact H2 | exact H9]
          | rewrite HS2, Z_to_bv_bv_unsigned; exact H8
          | rewrite H32; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H18 ]
  | rewrite Z.add_0_r; unfold d_env, havoc; cbn [ew Nat.ltb Nat.leb Nat.sub nth hb_vals map seq Nat.add app AT_X AT_FL];
    match goal with |- getr ?rg _ = Z_to_bv 64 (bv_unsigned (getr ?rg ?x)) =>
      let y := eval vm_compute in x in change x with y end;
    rewrite Z_to_bv_bv_unsigned; reflexivity ]).
Qed.

Lemma hb_s8e_body_n : forall cx h n n' xb shf ly S (W : world SEGS) m,
  d_body B cx h n xb shf ly S W m -> 0 <= n' <= Z.max 0 (c_n cx - 7) -> d_body B cx h n' xb shf ly S W m.
Proof.
intros cx h n n' xb shf ly S W m (T & G & Lk & H & F & Sh & O & Bl & (I1 & I2 & I3) & Im & Of & Ge & Cn & St & Aw) Hn'.
exists T, G, Lk, H.
refine (conj F (conj Sh (conj O (conj Bl (conj (conj Hn' (conj I2 I3)) (conj Im (conj Of (conj Ge (conj Cn (conj St Aw)))))))))).
Qed.

Lemma hb_s8e : AR_laws SEGS B -> PALib B -> frame_flag_lawP SEGS B ->
  forall cx h i n now op nb fr len W c, hc8 cx h i n now op nb fr len W c ->
  SRr SEGS W c (r27_in B MT XM_LIB RLO RHI tfib_K cx h i (nb - len) now nb fr len).
Proof.
intros LAWS TL FFL cx h i n now op nb fr len W c Hc.
destruct Hc as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HF0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc & HO & _).
pose proof HO as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & Hcl & H248 & Hlen & Hnb & Hnc & R22 & R23 & R24 & R26 & R27 & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & Hcan & Hstk & Hawr).
pose proof Hframe as (E & HdE & Hregs & Hflag & Hh216 & Hh152).
destruct (hb_A_range cx ly3 S3 W mem3 md3 k HJ) as (HSr & HS16 & HAr & HA32).
assert (HctxD : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold LLVMF_STK in HSr; lia).
assert (Hcur : 0 <= d_cur cx nb < 2 ^ 64).
{ pose proof Hbase as ((_ & _ & _ & _ & Hpn & _) & _). pose proof Hgeo as (_ & _ & _ & _ & G5 & _ & _ & G8).
  destruct Hfrm as (F1 & _). unfold d_cur.
  destruct Hpn as [(Hn0 & Hp0) | (Hn0 & _)].
  - rewrite Hp0. unfold A_EMPTY. lia.
  - specialize (G8 ltac:(lia)). unfold LLVMF_STK in *. lia. }
assert (E563 : ew (d_env cx E (hb_vals regs ++ [Z_to_bv 64 (d_cur cx nb)])) 563 = Z_to_bv 64 (d_cur cx nb)).
{ unfold d_env, havoc. cbn [ew Nat.ltb Nat.leb Nat.sub nth hb_vals map seq Nat.add app]. reflexivity. }
assert (CK : Forall (YP09.chunk_ok SEGS (d_env cx E (hb_vals regs ++ [Z_to_bv 64 (d_cur cx nb)])) (rd W mem3) (d_A cx))
  [YP09.mkChunk 248 (CVal 8 (SOff 563 0))]).
{ apply Forall_cons; [|apply Forall_nil].
  eapply YI04.chunk_ok_val with (v := d_cur cx nb).
  - rewrite sv_denot_SOff0. exact E563.
  - cbn. lia.
  - cbn. lia.
  - exact H248. }
pose proof (d_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E HB_RA4 hb_sr
  (hb_vals regs ++ [Z_to_bv 64 (d_cur cx nb)]) [YP09.mkChunk 248 (CVal 8 (SOff 563 0))] [] [] (d_facts [] [])
  HctxD HdE Hregs Hflag (hb_s8e_regs_ok cx E regs _ HdE HrL HAr2)
  (d_facts_ok B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k E _ [] [] HctxD HdE I I)
  CK (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_d in HS.
hb_ro_base HS 516%nat. hb_ro_base HS 529%nat. hb_ro_base HS 60%nat.
assert (HEI : img_env VAL A_LIM (d_env cx E (hb_vals regs ++ [Z_to_bv 64 (d_cur cx nb)]))).
{ destruct HdE as (_ & _ & HI & _). intros a Ha. unfold d_env. rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia). exact (HI a Ha). }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (hb_vals regs ++ [Z_to_bv 64 (d_cur cx nb)])) (rd W mem3)) by constructor.
pose (RUNTO := paj_run_to (fx := fq) B LAWS).
unfold cfg_at. change (w64 (BASE + HB_RA4)) with (Z_to_bv 64 (BASE + HB_RA4)).
paj_run_to_tok RUNTO HS HJ SHOK HBspan R27_OFF.
{ cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
assert (Hpt := hb_frame_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)).
assert (Hptr := hb_frame_ro_pt _ _ _ _ HFr ltac:(vm_compute; reflexivity)).
clear HF HFr HG.
assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 20; 22; 23; 24; 25; 26; 27]%bv -> getr (ms_regs ms) r = getr regs r).
{ intros r Hr. rewrite (st_ok_pi_restrict_reg (w_H W) _ _ ms r HS). rewrite (hb_s8e_regs_ok cx E regs [Z_to_bv 64 (d_cur cx nb)] HdE HrL HAr2 r).
  cbv [In] in Hr. repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]). destruct Hr. }
pose proof (st_ok_pi_restrict_mkst (w_H W) _ _ ms HS eq_refl) as Hms.
cbn [ss_pc] in Hms.
set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *.
assert (Hctx4 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms) md4 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
assert (H216' := hb_val_mem_pt _ _ _ _ _ Hptr Hh216).
assert (H152' := hb_val_mem_pt _ _ _ _ _ Hptr Hh152).
destruct (d_land B MT XM_LIB RLO RHI tfib_K LAWS FFL fq cx h dsh_rec ly3 S3 W md4 k
  (d_env cx E (hb_vals regs ++ [Z_to_bv 64 (d_cur cx nb)])) _ ms Hctx4 (d_E_env cx E _ HdE)
  (d_env_fl cx E _) HS ltac:(vm_compute; reflexivity) H216' H152') as [Hframe4 Hshadow4].
assert (Hbody4 : d_body B cx h (nb - len) (dxb fr len) dsh_rec ly3 S3 W (ms_mem ms)).
{ apply (hb_s8e_body_n cx h n); [|lia].
  apply (d_body_rt B cx h n n (dxb fr len) dsh_rec dsh_rec ly3 S3 W mem3 (ms_mem ms) (d_A cx) (d_A cx) (fun _ => False) Hbody).
  - unfold LLVMF_STK; lia.
  - lia.
  - intros a [].
  - intros a Ha _. apply aview_eq_of. apply Hptr.
  - intros a _ [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite Hpt. exact Hb.
  - exact Hframe4.
  - exact Hshadow4.
  - lia. }
apply SRr_ret. unfold r27_in, d_arm_at_pf, d_at.
exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md4, k, acc.
split; [unfold cfg_at; rewrite Hms at 1; reflexivity|].
split; [exact HF0|]. split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
split; [exact Hnev|]. split; [exact Hmo|]. split; [exact Hacc|].
refine (conj Hi (conj _ (conj Hnow (conj _ (conj _ (conj _ (conj _ Hbody4))))))).
- lia.
- destruct HrL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25). unfold d_rL, spZ in *.
  rewrite !RG by (cbv; tauto). repeat split; assumption.
- refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
  + rewrite (st_ok_pi_restrict_reg (w_H W) _ _ ms 14%bv HS).
    match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
    rewrite sv_denot_SOff0. exact E563.
  + rewrite RG by (cbv; tauto). exact R24.
  + rewrite RG by (cbv; tauto). exact R23.
  + rewrite RG by (cbv; tauto). exact R27.
  + rewrite RG by (cbv; tauto). exact R22.
  + rewrite RG by (cbv; tauto). exact R26.
- split; [|split; [exact Hlen | reflexivity]].
  destruct Hfrm as (F1 & F2 & Fnc & F3). split; [exact F1|]. split; [exact F2|]. split; [exact Fnc|]. exact (hb_garr8_pt _ _ _ _ Hptr F3).
- destruct Hsp0 as (Hs1 & Hs2). split; eapply hb_val_mem_pt; [exact Hptr | exact Hs1 | exact Hptr | exact Hs2].
Qed.


Definition hb_s23_sr (idx : Z) : list sv := map (fun r => if Nat.eqb r 10 then SLit idx else hb_rx r) (seq 0 32).
Definition hb_s23_vals (regs : bvmap 5 word) (now v : Z) : list word := hb_vals regs ++ [w64 now; w64 v].
Definition hb_s23_acs : list YP09.chunk := [YP09.mkChunk 216 (CVal 8 (SOff 550 0)); YP09.mkChunk 344 (CVal 8 (SOff 563 0))].
Definition hb_s23_R (idx : Z) : YP09.region :=
  YP09.mkRegion (Some 550%nat) (48 * idx + 8) (48 * idx + 12) 0 0 [YP09.mkChunk (48 * idx + 8) (CVal 4 (SOff 564 0))].
Definition hb_s23_ex (idx : Z) : smem := if idx <? 0 then [] else [hb_s23_R idx].
Definition hb_s23_fa : list (nat * afact) := [(550%nat, mkAF 4096 140737479966720 3); (564%nat, mkAF 0 4294967295 0)].
Definition hb_s23_SH : list shent := [mkSHE 550 0 480].

Lemma hb_s23_regs_ok : forall cx E regs idx ex, d_E cx E -> d_rL B cx regs -> 0 <= d_A cx < 2 ^ 64 ->
  getr regs 10 = w64 idx -> regs_ok (d_env cx E (hb_vals regs ++ ex)) (hb_s23_sr idx) regs.
Proof.
intros cx E regs idx ex HE HL HA H10.
destruct HE as (HER & H32 & _ & HA60 & _ & _).
destruct HL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25).
apply regs_ok_by_cases. intros r Hr.
cbv [all_regs In] in Hr.
assert (H2 : getr regs 2 = Z_to_bv 64 (d_A cx)) by (rewrite <- Hsp; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (HS2 : ew E 2 = Z_to_bv 64 (d_S cx)).
{ rewrite (HER 2%nat 2%bv eq_refl). unfold d_S, spZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
change AT_A with 60%nat in HA60.
repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<-|Hx] end; [ .. | contradiction ].
all: try (match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r) =>
  let w := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with w end;
  cbn [sv_denot];
  first
  [ rewrite getr_zero; reflexivity
  | exact H10
  | rewrite Z.add_0_r; unfold d_env; rewrite ew_havoc_old by (cbv; lia);
    first [ rewrite HA60, Z_to_bv_bv_unsigned; first [exact H2 | exact H9]
          | rewrite HS2, Z_to_bv_bv_unsigned; exact H8
          | rewrite H32; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H18 ]
  | rewrite Z.add_0_r; unfold d_env, havoc; cbn [ew Nat.ltb Nat.leb Nat.sub nth hb_vals map seq Nat.add AT_X AT_FL app];
    match goal with |- getr ?rg _ = Z_to_bv 64 (bv_unsigned (getr ?rg ?x)) =>
      let y := eval vm_compute in x in change x with y end;
    rewrite Z_to_bv_bv_unsigned; reflexivity ]).
Qed.

Lemma hb_s23_val : forall E v, ew E 564 = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
  U E (SAlu ALU_SLTU (SAlu ALU_ADD (SExt true 32 (SOff 564 0)) (SLit (-1))) (SLit 1)) =
  if bv_swrap 32 v =? 1 then 1 else 0.
Proof.
intros E v H33 Hv.
rewrite !U_SAlu, U_SExt. rewrite (U_atom E 564 v H33) by lia. rewrite !U_SLit. cbn [zalu_raw].
change (2 ^ Z.of_N 32) with 4294967296. rewrite (Z.mod_small v) by lia.
assert (HM : bv_half_modulus 32 = 2147483648) by reflexivity.
assert (HMM : bv_modulus 32 = 4294967296) by reflexivity.
assert (Hs : -2147483648 <= bv_swrap 32 v < 2147483648).
{ unfold bv_swrap, bv_wrap. rewrite HM, HMM. pose proof (Z.mod_pos_bound (v + 2147483648) 4294967296 ltac:(lia)). lia. }
set (s := bv_swrap 32 v) in *. unfold zcanon, M64. change (2 ^ 64) with 18446744073709551616.
destruct (Z.eqb_spec s 1) as [E2 | N2].
- rewrite E2. reflexivity.
- match goal with |- context [(?a <? ?b)] => replace (a <? b) with false end; [reflexivity|].
  symmetry. apply Z.ltb_ge. Z.div_mod_to_equations. lia.
Qed.

Lemma hb_s23_flag : forall E (T P : list byte) idx, 0 <= idx -> ew E 564 = Z_to_bv 64 (u_at T (48 * idx + 8) 4) ->
  sv_denot E (SAlu ALU_SLTU (SAlu ALU_ADD (SExt true 32 (SOff 564 0)) (SLit (-1))) (SLit 1)) = w64 (hflag T P idx).
Proof.
intros E T P idx Hi H564.
rewrite denot_lit_U, (hb_s23_val E _ H564 (ct_u4_range T _)).
unfold hflag, role_of_e, s32_at. replace (0 <=? idx) with true by (symmetry; apply Z.leb_le; lia).
cbn [andb]. unfold w64. destruct (bv_swrap 32 (u_at T (48 * idx + 8) 4) =? 1); reflexivity.
Qed.

Lemma hb_s23_flag0 : forall E (T P : list byte), sv_denot E (SLit 0) = w64 (hflag T P (-1)).
Proof. intros E T P. reflexivity. Qed.

Lemma hb_s23 : AR_laws SEGS B -> PALib B -> frame_flag_lawP SEGS B ->
  forall cx h i n now op nb fr len W c, hc2 cx h i n now op nb fr len W c -> SRr SEGS W c (hc3 cx h i n now op nb fr len).
Proof.
intros LAWS TL FFL cx h i n now op nb fr len W c Hc.
destruct Hc as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HF0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc & HO &
  R19 & H & idx & HH & R10 & Hfind).
pose proof HO as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & Hcl & H248 & Hlen & Hnb & Hnc & R22 & R23 & R24 & R26 & R27 & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & Hcan & Hstk & Hawr).
pose proof Hframe as (E & HdE & Hregs & Hflag & Hh216 & Hh152).
pose proof HH as (LH & GH & QH & EO).
assert (HctxD : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HctxD)
  as (HSmod & HSlo & HShi & HFB1 & HFB2 & HFBapp & HFBimg & HFBmod & HFpres & HSHpres & HWpres & HAR3 & Hin3 & EFB3 & EFL3).
destruct (hb_A_range cx ly3 S3 W mem3 md3 k HJ) as (HSr & HS16 & HAr & HA32).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hgeo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
pose proof (hb_h_in cx h n _ dsh_rec ly3 S3 W mem3 Hbody) as Hhin.
destruct (al_blocks _ _ LAWS ly3 S3 W mem3 md3 h HUNT_SIZE HAR3 Hhin) as (Hh16 & Hh4096 & Hhc & Hhapp & _).
assert (RQH : req_size HUNT_SIZE = 480) by reflexivity. rewrite RQH in Hhc, Hhapp.
pose proof Hblocks as (_ & _ & _ & Hboff). apply Forall_inv in Hboff. cbn [fst snd] in Hboff. rewrite RQH in Hboff.
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold LLVMF_STK in HSr; lia).
assert (T1 : tbl_T1 (sub H 0 400)) by (destruct QH as (_ & (HT1 & _) & _); exact HT1).
assert (Hidx : idx = -1 \/ 0 <= idx < 8) by (unfold tbl_T1 in T1; destruct Hfind as [[-> _] | [? _]]; lia).
assert (Hcase : idx = -1 \/ idx = 0 \/ idx = 1 \/ idx = 2 \/ idx = 3 \/ idx = 4 \/ idx = 5 \/ idx = 6 \/ idx = 7) by lia.
assert (ET : sub H 0 400 = firstn 400 H) by reflexivity.
assert (LT4 : length (sub H 0 400) = 400%nat) by (rewrite ET, length_firstn, LH; reflexivity).
assert (GT : garr8 SEGS (rd W mem3) h (map (fun b : byte => bv_unsigned b) (sub H 0 400))).
{ pose proof (garr8_sub_x SEGS _ h _ 0 400 GH ltac:(rewrite length_map; lia)) as X.
  rewrite Z.add_0_r in X. cbn [skipn] in X. rewrite ET, <- firstn_map. exact X. }
remember (u_at (sub H 0 400) (48 * idx + 8) 4) as v eqn:Ev.
assert (Rv : 0 <= v < 2 ^ 32) by (rewrite Ev; apply ct_u4_range).
assert (HRG : regs_ok (d_env cx E (hb_s23_vals regs now v)) (hb_s23_sr idx) regs)
  by exact (hb_s23_regs_ok cx E regs idx [w64 now; w64 v] HdE HrL HAr2 R10).
assert (E550 : ew (d_env cx E (hb_s23_vals regs now v)) 550 = w64 h).
{ pose proof (HRG 19%bv) as X. change (sr_get (hb_s23_sr idx) 19%bv) with (SOff 550 0) in X.
  rewrite sv_denot_SOff0, R19 in X. symmetry. exact X. }
assert (E563 : ew (d_env cx E (hb_s23_vals regs now v)) 563 = w64 now) by reflexivity.
assert (E564 : ew (d_env cx E (hb_s23_vals regs now v)) 564 = w64 v) by reflexivity.
assert (U550 : bv_unsigned (ew (d_env cx E (hb_s23_vals regs now v)) 550) = h) by (rewrite E550; unfold w64; apply unsigned_lit_small; lia).
assert (U564 : bv_unsigned (ew (d_env cx E (hb_s23_vals regs now v)) 564) = v) by (rewrite E564; unfold w64; apply unsigned_lit_small; lia).
pose proof HdE as (EE & E32 & HI0 & E60 & E516 & E529).
assert (HSH : 0 <= shadow_addr (d_FB cx) /\ shadow_addr (d_FB cx) + 512 < alloc_ceiling).
{ unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos (d_FB cx) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_upper_bound (d_FB cx) 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
assert (U2 : bv_unsigned (ew (d_env cx E (hb_s23_vals regs now v)) AT_STK) = d_S cx)
  by (rewrite d_env_old by (cbv; lia); unfold AT_STK; rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (U60 : bv_unsigned (ew (d_env cx E (hb_s23_vals regs now v)) AT_A) = d_A cx)
  by (rewrite d_env_old by (cbv; lia); rewrite E60; unfold w64; apply unsigned_lit_small; lia).
assert (U516 : bv_unsigned (ew (d_env cx E (hb_s23_vals regs now v)) AT_F) = d_FB cx)
  by (rewrite d_env_old by (cbv; lia); rewrite E516; unfold w64; apply unsigned_lit_small; lia).
assert (U529 : bv_unsigned (ew (d_env cx E (hb_s23_vals regs now v)) AT_SH) = shadow_addr (d_FB cx))
  by (rewrite d_env_old by (cbv; lia); rewrite E529; unfold w64; apply unsigned_lit_small; lia).
assert (HEI : img_env VAL A_LIM (d_env cx E (hb_s23_vals regs now v))).
{ intros a Ha. unfold d_env. rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia). exact (HI0 a Ha). }
assert (UO1 : bv_unsigned (ew (d_env cx E (hb_s23_vals regs now v)) (A_OBJ 1)) = VAL (A_OBJ 1))
  by (apply HEI; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (UO66 : bv_unsigned (ew (d_env cx E (hb_s23_vals regs now v)) (A_OBJ 66)) = VAL (A_OBJ 66))
  by (apply HEI; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 1 ltac:(vm_compute; lia)) as Ho1. pose proof (pa_obj_img 66 ltac:(vm_compute; lia)) as Ho66.
assert (HFACTS : facts_ok (d_env cx E (hb_s23_vals regs now v)) (d_facts hb_s23_fa [])).
{ apply (d_facts_ok B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k E (hb_s23_vals regs now v) hb_s23_fa [] HctxD HdE); [|exact I].
  cbn [hb_s23_fa atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U550, U564.
  change (2 ^ 3) with 8. rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia. }
assert (HACS : Forall (YP09.chunk_ok SEGS (d_env cx E (hb_s23_vals regs now v)) (rd W mem3) (d_A cx)) hb_s23_acs).
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (chunk_ok_val SEGS _ _ (d_A cx) 216 8 (SOff 550 0) h); [rewrite sv_denot_SOff0, E550; reflexivity | cbn; lia | cbn; lia | exact Hh216].
  - apply (chunk_ok_val SEGS _ _ (d_A cx) 344 8 (SOff 563 0) now); [rewrite sv_denot_SOff0, E563; reflexivity | cbn; lia | cbn; lia | exact (proj2 Hsp0)]. }
assert (HEXT : Forall (region_ok SEGS (d_env cx E (hb_s23_vals regs now v)) (rd W mem3)) (hb_s23_ex idx)).
{ unfold hb_s23_ex. destruct (Z.ltb_spec idx 0) as [Lt|Ge]; [apply Forall_nil|].
  apply Forall_cons; [|apply Forall_nil]. unfold region_ok, hb_s23_R.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U550.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ h (48 * idx + 8) 4 (SOff 564 0) v); [rewrite sv_denot_SOff0, E564; reflexivity | cbn; lia | cbn; lia |].
  rewrite Ev. pose proof (ct_u_val (w_H W) mem3 h (sub H 0 400) (Z.to_nat (48 * idx + 8)) LT4 GT ltac:(lia)) as X.
  rewrite Z2Nat.id in X by lia. exact X. }
assert (HPD : pairwise_disjoint (d_env cx E (hb_s23_vals regs now v)) (hb_s23_ex idx))
  by (unfold hb_s23_ex; destruct (idx <? 0); cbn; tauto).
assert (HAD : Forall (fun r => all_disjoint (d_env cx E (hb_s23_vals regs now v)) r (d_kregions dsh_rec hb_s23_acs [])) (hb_s23_ex idx)).
{ unfold hb_s23_ex. destruct (Z.ltb_spec idx 0) as [Lt|Ge]; [apply Forall_nil|].
  apply Forall_cons; [|apply Forall_nil].
  apply all_disjoint_of_extents. unfold extent_of_region, hb_s23_R, d_kregions, fshadow_region, got_regionP, bcell_regionP.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zall_disjoint]. unfold zdisj. cbn [fst snd].
  rewrite U550, U2, U60, U516, U529, UO1, UO66.
  change (fs_frame_bytes DFRAME_CLASS) with 4096 in *. change (4096 / 8) with 512.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, shadow_addr, SHADOW_OFF, HUNT_SIZE, LLVMF_STK in *.
  pose proof (Z.div_mod (d_FB cx) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (d_FB cx) 8 ltac:(lia)).
  repeat split; lia. }
assert (HWF : regions_wf (d_kregions dsh_rec hb_s23_acs [] ++ hb_s23_ex idx) = true)
  by (destruct Hcase as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]; vm_compute; reflexivity).
assert (SHOK0 : sh_ok SEGS (SOff 32 0) hb_s23_SH (d_env cx E (hb_s23_vals regs now v)) (rd W mem3)).
{ unfold sh_ok, hb_s23_SH. apply Forall_cons; [|apply Forall_nil].
  eapply shent_ok_of_range.
  - exact (range_addressable_of_block SEGS B LAWS ly3 S3 W mem3 md3 h HUNT_SIZE h 480 HAR3 Hhin ltac:(lia) ltac:(rewrite RQH; lia)).
  - unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. rewrite d_env_old by (cbv; lia). rewrite E32.
    unfold w64. apply unsigned_lit_small. unfold SHADOW_OFF. lia.
  - unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U550.
  - lia.
  - lia.
  - intros x Hx. cbn [Z.min Z.max] in Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hhapp. unfold SHADOW_OFF. lia. }
pose proof (d_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E HB_RA1 (hb_s23_sr idx)
  (hb_s23_vals regs now v) hb_s23_acs [] (hb_s23_ex idx) (d_facts hb_s23_fa [])
  HctxD HdE Hregs Hflag HRG HFACTS HACS (Forall_nil _) HEXT HPD HAD HWF) as HS.
unfold ss_d in HS.
destruct Hcase as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]].
all: hb_ro_base HS 516%nat.
all: hb_ro_base HS 529%nat.
all: hb_ro_base HS 60%nat.
all: pose proof SHOK0 as SHOK.
all: pose (RUN := paj_run (fx := fq) B LAWS).
all: unfold cfg_at; change (w64 (BASE + HB_RA1)) with (Z_to_bv 64 (BASE + HB_RA1)).
all: paj_run_tok RUN HS HJ SHOK HBspan; [cbn [ss_mem]; repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil | ].
all: assert (Hpt := hb_frame_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)).
all: assert (Hptr := hb_frame_ro_pt _ _ _ _ HFr ltac:(vm_compute; reflexivity)).
all: clear HF HFr HG.
all: rewrite (pa_sigma_reac_hunt_observe (PI := PI)) in HS.
all: assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 20; 22; 23; 24; 25; 26; 27]%bv -> getr (ms_regs ms) r = getr regs r)
  by (intros r Hr; rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms r HS), (HRG r);
      cbv [In] in Hr; repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]); destruct Hr).
all: pose proof (st_ok_restrict_mkst SEGS (w_H W) _ _ ms HS eq_refl) as Hms.
all: cbn [ss_pc setpc] in Hms.
all: lazymatch type of HS with st_ok _ ?Ex (setpc ?ssx _) ?msx =>
  assert (HSpi : st_ok_pi SEGS VAL Ex (setpc ssx AF_reac_hunt_observe) msx) by exact HS end.
all: set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *.
all: assert (Hctx4 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms) md4 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
all: assert (H216' := hb_val_mem_pt _ _ _ _ _ Hptr Hh216).
all: assert (H152' := hb_val_mem_pt _ _ _ _ _ Hptr Hh152).
all: destruct (d_land B MT XM_LIB RLO RHI tfib_K LAWS FFL fq cx h dsh_rec ly3 S3 W md4 k (d_env cx E (hb_s23_vals regs now v)) _ ms
  Hctx4 (d_E_env cx E _ HdE) (d_env_fl cx E _) HSpi ltac:(vm_compute; reflexivity) H216' H152') as [Hframe4 Hshadow4].
all: assert (Hbody4 : d_body B cx h n (dxb fr len) dsh_rec ly3 S3 W (ms_mem ms))
  by (apply (d_body_rt B cx h n n (dxb fr len) dsh_rec dsh_rec ly3 S3 W mem3 (ms_mem ms) (d_A cx) (d_A cx) (fun _ => False) Hbody);
      [ unfold LLVMF_STK; lia | lia | intros a [] | intros a Ha _; apply aview_eq_of; apply Hptr
      | intros a _ [Hh [b Hb]]; split; [exact Hh|]; exists b; rewrite Hpt; exact Hb | exact Hframe4 | exact Hshadow4 | lia ]).
all: apply SRr_ret; unfold hc3, d_at.
all: exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md4, k, acc.
all: split; [unfold cfg_at, w64; rewrite <- Hms; reflexivity|].
all: split; [exact HF0|]; split; [exact Hbase|]; split; [exact HJ|]; split; [exact Hfrs|]; split; [exact Hk|];
  split; [exact Hnev|]; split; [exact Hmo|]; split; [exact Hacc|].
all: split; [unfold hoc; refine (conj Hi (conj Hn (conj Hnow (conj Hop (conj Hop2 (conj _ (conj _ (conj _ (conj Hcl (conj _
    (conj Hlen (conj Hnb (conj Hnc (conj _ (conj _ (conj _ (conj _ (conj _ Hbody4))))))))))))))))));
  [ destruct HrL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25); unfold d_rL, spZ in *;
    rewrite !RG by (cbv; tauto); repeat split; assumption
  | destruct Hsp0 as (Hs1 & Hs2); split; eapply hb_val_mem_pt; [exact Hptr | exact Hs1 | exact Hptr | exact Hs2]
  | destruct Hfrm as (F1 & F2 & Fnc & F3); split; [exact F1|]; split; [exact F2|]; split; [exact Fnc|]; exact (hb_garr8_pt _ _ _ _ Hptr F3)
  | exact (hb_val_mem_pt _ _ _ _ _ Hptr H248)
  | rewrite RG by (cbv; tauto); exact R22
  | rewrite RG by (cbv; tauto); exact R23
  | rewrite RG by (cbv; tauto); exact R24
  | rewrite RG by (cbv; tauto); exact R26
  | rewrite RG by (cbv; tauto); exact R27 ] | unfold hp3 ].
all: split; [rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 1%bv HS);
  match goal with |- context [sr_get ?sr ?r] => let w := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with w end;
  unfold w64; exact (codeptr_val _ HB_RA2 HEI)|].
all: split; [rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 10%bv HS);
  match goal with |- context [sr_get ?sr ?r] => let w := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with w end;
  rewrite sv_denot_SOff0; exact E550|].
all: split; [rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 11%bv HS); transitivity (getr regs 27); [|exact R27];
  rewrite (HRG 27%bv); f_equal; try (vm_compute; reflexivity)|].
all: split; [rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 12%bv HS); transitivity (getr regs 24); [|exact R24];
  rewrite (HRG 24%bv); f_equal; try (vm_compute; reflexivity)|].
all: split; [rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 13%bv HS);
  match goal with |- context [sr_get ?sr ?r] => let w := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with w end;
  rewrite sv_denot_SOff0; exact E563|].
all: split; [rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 14%bv HS); transitivity (getr regs 22); [|exact R22];
  rewrite (HRG 22%bv); f_equal; try (vm_compute; reflexivity)|].
all: exists H; eexists; split; [split; [exact LH|]; split; [exact (hb_garr8_pt _ _ _ _ Hptr GH)|]; split; [exact QH | exact EO]
  | split; [exact Hfind|] ].
all: rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 19%bv HS);
  match goal with |- context [sr_get ?sr ?r] => let w := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with w end.
all: first [ apply hb_s23_flag0 | apply hb_s23_flag; [lia | rewrite E564, Ev; reflexivity] ].
Qed.

Lemma hb_s45_regs_ok : forall cx E regs xs, d_E cx E -> d_rL B cx regs ->
  0 <= d_A cx < 2 ^ 64 ->
  regs_ok (d_env cx E (hb_vals regs ++ xs)) hb_sr regs.
Proof.
intros cx E regs xs HE HL HA.
destruct HE as (HER & H32 & _ & HA60 & _ & _).
destruct HL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25).
apply regs_ok_by_cases. intros r Hr.
cbv [all_regs In] in Hr.
assert (H2 : getr regs 2 = Z_to_bv 64 (d_A cx)) by (rewrite <- Hsp; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (HS2 : ew E 2 = Z_to_bv 64 (d_S cx)).
{ rewrite (HER 2%nat 2%bv eq_refl). unfold d_S, spZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
change AT_A with 60%nat in HA60.
repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<-|Hx] end; [ .. | contradiction ].
all: try (match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r) =>
  let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
  cbn [sv_denot];
  first
  [ rewrite getr_zero; reflexivity
  | rewrite Z.add_0_r; unfold d_env; rewrite ew_havoc_old by (cbv; lia);
    first [ rewrite HA60, Z_to_bv_bv_unsigned; first [exact H2 | exact H9]
          | rewrite HS2, Z_to_bv_bv_unsigned; exact H8
          | rewrite H32; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H18 ]
  | rewrite Z.add_0_r; unfold d_env, havoc; cbn [ew Nat.ltb Nat.leb Nat.sub nth hb_vals map seq Nat.add AT_X AT_FL app];
    match goal with |- getr ?rg _ = Z_to_bv 64 (bv_unsigned (getr ?rg ?x)) =>
      let y := eval vm_compute in x in change x with y end;
    rewrite Z_to_bv_bv_unsigned; reflexivity ]).
Qed.

Definition hb_s45_x12 : sv :=
  SAlu ALU_ADD (SOff 555 0)
  (SAlu ALU_AND
    (SAlu ALU_SUB (SLit 0)
      (SAlu ALU_SLTU
        (SAlu ALU_AND
          (SAlu ALU_OR
            (SAlu ALU_SRL
              (SAlu ALU_ADD (SMd M_MUL (SOff 555 0) (SLit 5192296858534819430008849677942784)) (SLit (-1688849860263936)))
              (SLit 50))
            (SAlu ALU_ADD (SMd M_MUL (SOff 555 0) (SLit 302231454903656816459776)) (SLit (-98304))))
          (SLit 65535))
        (SLit 1821)))
    (SLit (-2))).
Fixpoint hb_s45_chk (k : nat) (x : Z) : bool :=
  match k with
  | O => true
  | S k' => (bv_unsigned (sv_denot (mkEnv (fun _ => Z_to_bv 64 x) (fun _ => [])) hb_s45_x12) =?
              reac_frame_clean_len_c.reac_frame_clean_len_model x) && hb_s45_chk k' (x + 1)
  end.
Lemma hb_s45_chk_ok : hb_s45_chk 65482 54 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma hb_s45_chk_sound : forall k x, hb_s45_chk k x = true -> forall y, x <= y < x + Z.of_nat k ->
  bv_unsigned (sv_denot (mkEnv (fun _ => Z_to_bv 64 y) (fun _ => [])) hb_s45_x12) =
  reac_frame_clean_len_c.reac_frame_clean_len_model y.
Proof.
induction k as [|k IH]; intros x Hc y Hy; [lia|].
cbn [hb_s45_chk] in Hc. apply andb_prop in Hc as [H1 H2].
destruct (Z.eq_dec y x) as [->|Ne]; [apply Z.eqb_eq; exact H1|].
apply (IH (x + 1) H2). lia.
Qed.
Lemma hb_s45_cl : forall E len, 54 <= len < 65536 -> ew E 555 = w64 len ->
  sv_denot E hb_s45_x12 = w64 (reac_frame_clean_len_c.reac_frame_clean_len_model len).
Proof.
intros E len Hl He.
assert (X : sv_denot E hb_s45_x12 = sv_denot (mkEnv (fun _ => Z_to_bv 64 len) (fun _ => [])) hb_s45_x12).
{ cbn [sv_denot hb_s45_x12 ew]. rewrite He. reflexivity. }
rewrite X. apply bv_eq.
assert (RNG : 54 <= len < 54 + Z.of_nat 65482) by (change (Z.of_nat 65482) with 65482; lia).
rewrite (hb_s45_chk_sound 65482 54 hb_s45_chk_ok len RNG).
assert (R : 0 <= reac_frame_clean_len_c.reac_frame_clean_len_model len <= len).
{ unfold reac_frame_clean_len_c.reac_frame_clean_len_model. destruct (_ && _); lia. }
unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
Qed.
Lemma hb_s45_sf : forall cx nb len (H A : list byte) idx,
  firstn 6 (skipn 412 H) = our_of (c_pl cx) ->
  find_res (sub H 0 400) (macb cx nb len) idx -> length A = 24%nat ->
  reac_frame_clean_len_c.reac_frame_clean_len_model len <= len ->
  (Z.to_nat len <= length (rest_of (c_pl cx) nb))%nat ->
  reac_hunt_observe_c.ho_facts H (hfb cx nb len) (reac_frame_clean_len_c.reac_frame_clean_len_model len) (sub H 0 400) A ->
  50 <= len /\
  sighting_facts A (hfb cx nb len) (our_of (c_pl cx)) (reac_frame_clean_len_c.reac_frame_clean_len_model len) 1 /\
  (hflag (sub H 0 400) (macb cx nb len) idx <> 0 -> s_role A = 1).
Proof.
intros cx nb len H A idx EO Hf LA Hcl HL HF.
pose proof HF as (L50 & EM & _ & _ & _ & _ & _ & _ & Hrole).
assert (L : 50 <= len) by lia.
assert (LR : length (hfb cx nb len) = 50%nat).
{ unfold hfb. rewrite length_firstn, length_app, repeat_length. lia. }
split; [exact L|]. split.
- pose proof (slot_hunt.ho_sf H (hfb cx nb len) _ (sub H 0 400) A (our_of (c_pl cx)) LA ltac:(lia) EO HF) as X.
  unfold hfb in X |- *. rewrite firstn_firstn, Nat.min_id in X. exact X.
- intros Hfl. apply Hrole. unfold hflag in Hfl.
  destruct (0 <=? idx) eqn:E0; [|cbn in Hfl; congruence].
  destruct (role_of_e (sub H 0 400) idx =? 1) eqn:E1; [|cbn in Hfl; congruence].
  apply Z.leb_le in E0. apply Z.eqb_eq in E1.
  destruct Hf as [(E & _) | (Hr & Hm & _)]; [lia|].
  exists idx. split; [exact Hr|]. split; [|exact E1].
  rewrite Hm, EM. unfold macb. replace (11 <? len) with true by (symmetry; apply Z.ltb_lt; lia).
  unfold hfb, sub. change (Z.to_nat 6) with 6%nat.
  set (FR := firstn (Z.to_nat len) (rest_of (c_pl cx) nb)).
  assert (LF : length FR = Z.to_nat len) by (unfold FR; rewrite length_firstn; lia).
  rewrite skipn_firstn_comm, firstn_firstn, Nat.min_l by lia.
  rewrite skipn_app, firstn_app, length_skipn, LF.
  replace (6 - (Z.to_nat len - 6))%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r. reflexivity.
Qed.
Lemma hb_s45_ptr : forall (W : world SEGS) (m m' : word -> option byte), (forall x, m' x = m x) ->
  forall x, rd W m' x = rd W m x.
Proof. intros W m m' Hpt x. cbv beta delta [mrestrict]. rewrite Hpt. reflexivity. Qed.
Lemma hb_s45_land : AR_laws SEGS B -> frame_flag_lawP SEGS B ->
  forall cx h i n now op nb fr len (fq : YK11.FPState) ly3 S3 (W : world SEGS) regs mem3 md k acc E xs ss ms pc kmax accmax
    (Px : bvmap 5 word -> world SEGS -> (word -> option byte) -> Prop),
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) -> d_base B MT XM_LIB RLO RHI tfib_K cx ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] -> 0 <= k <= kmax -> st_nev S3 <= st_nev (c_S cx) + kmax ->
  mo_le MT (c_S cx) S3 acc -> acc <= accmax ->
  hoc cx h i n now op nb fr len regs ly3 S3 W mem3 -> d_E cx E ->
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E (hb_vals regs ++ xs)) (setpc ss pc) (restrict (w_H W) ms) ->
  ss_resv ss = None -> d_land_chk dsh_rec (ss_mem ss) = true ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (sr_get hb_sr r))
    [2; 3; 4; 8; 9; 18; 20; 22; 23; 24; 25; 26; 27]%bv = true ->
  (forall x, ms_mem ms x = mem3 x) -> Px (ms_regs ms) W (ms_mem ms) ->
  DAT cx pc kmax accmax (fun regs ly S W m md => hoc cx h i n now op nb fr len regs ly S W m /\ Px regs W m)
    W (mkCfg ms md).
Proof.
intros LAWS FFL cx h i n now op nb fr len fq ly3 S3 W regs mem3 md k acc E xs ss ms pc kmax accmax Px
  HF0 Hbase HJ Hfrs Hk Hnev Hmo Hacc HO HdE HS Hrv Hchk Hsr Hpt HPx.
pose proof HO as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & Hcl & H248 & Hlen & Hnb & Hnc & R22 & R23 & R24 & R26 & R27 & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & _).
pose proof Hframe as (E0 & _ & _ & _ & Hh216 & Hh152).
destruct (hb_A_range cx ly3 S3 W (ms_mem ms) md k HJ) as (HSr & HS16 & HAr & HA32).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold LLVMF_STK in HSr; lia).
pose proof (hb_s45_ptr W mem3 (ms_mem ms) Hpt) as Hptr.
assert (Hctx : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms) md k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (d_land B MT XM_LIB RLO RHI tfib_K LAWS FFL fq cx h dsh_rec ly3 S3 W md k (d_env cx E (hb_vals regs ++ xs)) _ ms Hctx
  (d_E_env cx E _ HdE) (d_env_fl cx E _) HS Hchk (hb_val_mem_pt _ _ _ _ _ Hptr Hh216) (hb_val_mem_pt _ _ _ _ _ Hptr Hh152))
  as [Hframe4 Hshadow4].
assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 20; 22; 23; 24; 25; 26; 27]%bv -> getr (ms_regs ms) r = getr regs r).
{ intros r Hr. rewrite (st_ok_pi_restrict_reg (w_H W) _ _ ms r HS). rewrite (hb_s45_regs_ok cx E regs xs HdE HrL HAr2 r).
  rewrite forallb_forall in Hsr. specialize (Hsr r Hr). apply sv_eqb_eq in Hsr. cbn [setpc ss_regs]. rewrite Hsr. reflexivity. }
pose proof (st_ok_pi_restrict_mkst (w_H W) _ _ ms HS Hrv) as Hms. cbn [ss_pc setpc] in Hms.
assert (Hbody4 : d_body B cx h n (dxb fr len) dsh_rec ly3 S3 W (ms_mem ms)).
{ apply (d_body_rt B cx h n n (dxb fr len) dsh_rec dsh_rec ly3 S3 W mem3 (ms_mem ms) (d_A cx) (d_A cx) (fun _ => False) Hbody).
  - unfold LLVMF_STK in *; lia.
  - lia.
  - intros a [].
  - intros a Ha _. apply aview_eq_of. apply Hptr.
  - intros a _ [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite Hpt. exact Hb.
  - exact Hframe4.
  - exact Hshadow4.
  - lia. }
exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md, k, acc.
split; [unfold cfg_at, w64; rewrite <- Hms; reflexivity|].
split; [exact HF0|]. split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
split; [exact Hnev|]. split; [exact Hmo|]. split; [exact Hacc|].
split; [|exact HPx].
unfold hoc.
refine (conj Hi (conj Hn (conj Hnow (conj Hop (conj Hop2 (conj _ (conj _ (conj _ (conj Hcl (conj _ (conj Hlen (conj Hnb (conj Hnc
  (conj _ (conj _ (conj _ (conj _ (conj _ Hbody4)))))))))))))))))).
- destruct HrL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25). unfold d_rL, spZ in *.
  rewrite !RG by (cbv; tauto). repeat split; assumption.
- destruct Hsp0 as (Hs1 & Hs2). split; eapply hb_val_mem_pt; [exact Hptr | exact Hs1 | exact Hptr | exact Hs2].
- destruct Hfrm as (F1 & F2 & Fnc & F3). split; [exact F1|]. split; [exact F2|]. split; [exact Fnc|]. exact (hb_garr8_pt _ _ _ _ Hptr F3).
- exact (hb_val_mem_pt _ _ _ _ _ Hptr H248).
- rewrite RG by (cbv; tauto). exact R22.
- rewrite RG by (cbv; tauto). exact R23.
- rewrite RG by (cbv; tauto). exact R24.
- rewrite RG by (cbv; tauto). exact R26.
- rewrite RG by (cbv; tauto). exact R27.
Qed.

Lemma hb_s45_rr : forall cx E regs xs (fq : YK11.FPState) ss ms (Hw : word -> bool) (r r0 : bv 5) v,
  d_E cx E -> d_rL B cx regs -> 0 <= d_A cx < 2 ^ 64 ->
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E (hb_vals regs ++ xs)) ss (restrict Hw ms) ->
  sv_eqb (sr_get (ss_regs ss) r) (sr_get hb_sr r0) = true -> getr regs r0 = v -> getr (ms_regs ms) r = v.
Proof.
intros cx E regs xs fq ss ms Hw r r0 v HE HL HA HS Hq Hv.
rewrite (st_ok_pi_restrict_reg Hw _ _ ms r HS). apply sv_eqb_eq in Hq. rewrite Hq, <- Hv.
symmetry. exact (hb_s45_regs_ok cx E regs xs HE HL HA r0).
Qed.

Lemma hb_s45 : AR_laws SEGS B -> PALib B -> frame_flag_lawP SEGS B ->
  forall cx h i n now op nb fr len W c, hc4 cx h i n now op nb fr len W c ->
  SRr SEGS W c (fun W' c' => hc5 cx h i n now op nb fr len W' c' \/ hc7 cx h i n now op nb fr len W' c').
Proof.
intros LAWS TL FFL cx h i n now op nb fr len W c Hc.
destruct Hc as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HF0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc & HO & HP4).
pose proof HO as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & Hcl & H248 & Hlen & Hnb & Hnc & R22 & R23 & R24 & R26 & R27 & Hbody).
destruct HP4 as (H & idx & r & H' & LH & QH & EO & Hfind & R19 & R10 & Hr & HH' & Hpos).
pose proof Hfrm as (F1 & F2 & Fnc & F3). unfold REC_MAX in F1.
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & Hcan & Hstk & Hawr).
pose proof Hframe as (E & HdE & Hregs & Hflag & Hh216 & Hh152).
destruct (hb_A_range cx ly3 S3 W mem3 md3 k HJ) as (HSr & HS16 & HAr & HA32).
assert (HctxD : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hgeo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold LLVMF_STK in HSr; lia).
set (vals := hb_vals regs ++ [w64 h]).
assert (EAh : ew (d_env cx E vals) 563 = w64 h) by reflexivity.
assert (EA541 : ew (d_env cx E vals) 541 = w64 r).
{ rewrite <- R10. unfold vals, d_env, havoc. cbn [ew Nat.ltb Nat.leb Nat.sub nth hb_vals map seq Nat.add AT_FL app].
  match goal with |- getr ?rg ?x = getr ?rg ?z => let y := eval vm_compute in x in change x with y end. reflexivity. }
assert (EA555 : ew (d_env cx E vals) 555 = w64 len).
{ rewrite <- R24. unfold vals, d_env, havoc. cbn [ew Nat.ltb Nat.leb Nat.sub nth hb_vals map seq Nat.add AT_FL app].
  match goal with |- getr ?rg ?x = getr ?rg ?z => let y := eval vm_compute in x in change x with y end. reflexivity. }
assert (Hacs : Forall (YP09.chunk_ok SEGS (d_env cx E vals) (rd W mem3) (d_A cx)) [YP09.mkChunk 216 (CVal 8 (SOff 563 0))]).
{ apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ (d_A cx) 216 8 (SOff 563 0) h).
  - cbn [sv_denot]. rewrite EAh, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - unfold HUNT_SIZE in G4. cbn. lia.
  - lia.
  - exact Hh216. }
pose proof (d_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E HB_RA2 hb_sr vals
  [YP09.mkChunk 216 (CVal 8 (SOff 563 0))] [] [] (d_facts [] [])
  HctxD HdE Hregs Hflag (hb_s45_regs_ok cx E regs [w64 h] HdE HrL HAr2)
  (d_facts_ok B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k E vals [] [] HctxD HdE I I)
  Hacs (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_d in HS.
hb_ro_base HS 516%nat. hb_ro_base HS 529%nat. hb_ro_base HS 60%nat.
assert (HEI : img_env VAL A_LIM (d_env cx E vals)).
{ destruct HdE as (_ & _ & HI & _). intros a Ha. unfold d_env. rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia). exact (HI a Ha). }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E vals) (rd W mem3)) by constructor.
pose (RUN := paj_run (fx := fq) B LAWS).
pose (BR := paj_branch (fx := fq) (PI := PI)).
unfold cfg_at. change (w64 (BASE + HB_RA2)) with (Z_to_bv 64 (BASE + HB_RA2)).
paj_run_tok RUN HS HJ SHOK HBspan.
{ cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
pose proof (hb_frame_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)) as HptA. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK HBspan.
2: { exfalso. cbn [sv_denot] in Hc. rewrite EA541 in Hc. destruct Hr as [-> | [-> | ->]]; vm_compute in Hc; discriminate Hc. }
paj_run_tok RUN HS HJ SHOK HBspan.
{ cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
pose proof (hb_frame_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)) as Hq.
pose proof (fun x => eq_trans (Hq x) (HptA x)) as HptB. clear Hq HptA HF HFr HG. rename HptB into HptA.
psrr_branch_tok RUN BR HS SHOK HBspan.
- paj_run_tok RUN HS HJ SHOK HBspan.
  { cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  pose proof (hb_frame_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)) as Hq.
  pose proof (fun x => eq_trans (Hq x) (HptA x)) as HptB. clear Hq HptA HF HFr HG. rename HptB into HptA.
  rewrite (pa_sigma_check_table (PI := PI)) in HS.
  lazymatch type of HS with st_ok _ ?Ex (setpc ?ssx _) ?msx =>
    assert (HSpi : st_ok_pi SEGS VAL Ex (setpc ssx AF_check_table) msx) by exact HS end.
  apply SRr_ret. right.
  apply (hb_s45_land LAWS FFL cx h i n now op nb fr len fq ly3 S3 W regs mem3 _ k acc E [w64 h] _ _ AF_check_table _ _ (hp7 cx h)
    HF0 Hbase HJ Hfrs Hk Hnev Hmo Hacc HO HdE HSpi ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) HptA).
  unfold hp7. split; [|split].
  + rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ _ 1%bv HS).
    match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
    unfold w64. exact (codeptr_val _ HB_RA4 HEI).
  + rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ _ 10%bv HS).
    match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
    cbn [sv_denot]. rewrite EAh, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
  + exists H'. destruct HH' as (LH' & GH' & QH' & EH'). split; [exact LH'|].
    split; [exact (hb_garr8_pt _ _ _ _ (hb_s45_ptr W _ _ HptA) GH')|]. split; assumption.
- assert (Hr0 : 0 <= r).
  { cbn [sv_denot] in Hc0. rewrite EA541 in Hc0. destruct Hr as [-> | [-> | ->]]; [vm_compute in Hc0; discriminate Hc0 | lia | lia]. }
  destruct (Hpos Hr0) as (A & LA & GA & HFo).
  assert (HLR : (Z.to_nat len <= length (rest_of (c_pl cx) nb))%nat) by (unfold rest_of; rewrite length_skipn; lia).
  destruct (hb_s45_sf cx nb len H A idx EO Hfind LA ltac:(lia) HLR HFo) as (L50 & SF & FL).
  paj_run_tok RUN HS HJ SHOK HBspan.
  { cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  pose proof (hb_frame_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)) as Hq.
  pose proof (fun x => eq_trans (Hq x) (HptA x)) as HptB. clear Hq HptA HF HFr HG. rename HptB into HptA.
  psrr_branch_tok RUN BR HS SHOK HBspan.
  + rewrite branch_ltu_U, (U_atom _ 555 len EA555), U_lit in Hc1 by lia. apply Z.ltb_lt in Hc1.
    assert (EMl : reac_frame_clean_len_c.reac_frame_clean_len_model len = len).
    { unfold reac_frame_clean_len_c.reac_frame_clean_len_model. replace (54 <=? len) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
    paj_run_tok RUN HS HJ SHOK HBspan.
    { cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
    pose proof (hb_frame_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)) as Hq.
    pose proof (fun x => eq_trans (Hq x) (HptA x)) as HptB. clear Hq HptA HF HFr HG. rename HptB into HptA.
    rewrite (pa_sigma_check_sighting (PI := PI)) in HS.
    lazymatch type of HS with st_ok _ ?Ex (setpc ?ssx _) ?msx =>
      assert (HSpi : st_ok_pi SEGS VAL Ex (setpc ssx AF_check_sighting) msx) by exact HS end.
    apply SRr_ret. left.
    apply (hb_s45_land LAWS FFL cx h i n now op nb fr len fq ly3 S3 W regs mem3 _ k acc E [w64 h] _ _ AF_check_sighting _ _ (hp5 cx h nb fr len)
      HF0 Hbase HJ Hfrs Hk Hnev Hmo Hacc HO HdE HSpi ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) HptA).
    unfold hp5.
    split; [rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ _ 1%bv HS);
      match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
      unfold w64; exact (codeptr_val _ HB_RA3 HEI)|].
    split; [exact (hb_s45_rr cx E regs [w64 h] fq _ _ _ 10%bv 22%bv _ HdE HrL HAr2 HSpi ltac:(vm_compute; reflexivity) R22)|]. split; [exact (hb_s45_rr cx E regs [w64 h] fq _ _ _ 11%bv 27%bv _ HdE HrL HAr2 HSpi ltac:(vm_compute; reflexivity) R27)|].
    split; [rewrite EMl; exact (hb_s45_rr cx E regs [w64 h] fq _ _ _ 12%bv 24%bv _ HdE HrL HAr2 HSpi ltac:(vm_compute; reflexivity) R24)|].
    split; [exact (hb_s45_rr cx E regs [w64 h] fq _ _ _ 13%bv 26%bv _ HdE HrL HAr2 HSpi ltac:(vm_compute; reflexivity) R26)|].
    split; [rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ _ 14%bv HS);
      match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
      reflexivity|].
    split; [exact L50|].
    exists A, H', (hflag (sub H 0 400) (macb cx nb len) idx).
    split; [exact LA|]. split; [exact (hb_garr8_pt _ _ _ _ (hb_s45_ptr W _ _ HptA) GA)|]. split; [exact SF|].
    split; [exact (hb_s45_rr cx E regs [w64 h] fq _ _ _ 19%bv 19%bv _ HdE HrL HAr2 HSpi ltac:(vm_compute; reflexivity) R19)|]. split; [exact FL|].
    destruct HH' as (LH' & GH' & QH' & EH'). split; [exact LH'|].
    split; [exact (hb_garr8_pt _ _ _ _ (hb_s45_ptr W _ _ HptA) GH')|]. split; assumption.
  + rewrite branch_ltu_U, (U_atom _ 555 len EA555), U_lit in Hc1 by lia. apply Z.ltb_ge in Hc1.
    paj_run_tok RUN HS HJ SHOK HBspan.
    { cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
    pose proof (hb_frame_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)) as Hq.
    pose proof (fun x => eq_trans (Hq x) (HptA x)) as HptB. clear Hq HptA HF HFr HG. rename HptB into HptA.
    rewrite (pa_sigma_check_sighting (PI := PI)) in HS.
    lazymatch type of HS with st_ok _ ?Ex (setpc ?ssx _) ?msx =>
      assert (HSpi : st_ok_pi SEGS VAL Ex (setpc ssx AF_check_sighting) msx) by exact HS end.
    apply SRr_ret. left.
    apply (hb_s45_land LAWS FFL cx h i n now op nb fr len fq ly3 S3 W regs mem3 _ k acc E [w64 h] _ _ AF_check_sighting _ _ (hp5 cx h nb fr len)
      HF0 Hbase HJ Hfrs Hk Hnev Hmo Hacc HO HdE HSpi ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) HptA).
    unfold hp5.
    split; [rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ _ 1%bv HS);
      match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
      unfold w64; exact (codeptr_val _ HB_RA3 HEI)|].
    split; [exact (hb_s45_rr cx E regs [w64 h] fq _ _ _ 10%bv 22%bv _ HdE HrL HAr2 HSpi ltac:(vm_compute; reflexivity) R22)|]. split; [exact (hb_s45_rr cx E regs [w64 h] fq _ _ _ 11%bv 27%bv _ HdE HrL HAr2 HSpi ltac:(vm_compute; reflexivity) R27)|].
    split; [rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ _ 12%bv HS);
      match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
      exact (hb_s45_cl _ len ltac:(lia) EA555)|].
    split; [exact (hb_s45_rr cx E regs [w64 h] fq _ _ _ 13%bv 26%bv _ HdE HrL HAr2 HSpi ltac:(vm_compute; reflexivity) R26)|].
    split; [rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ _ 14%bv HS);
      match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
      reflexivity|].
    split; [exact L50|].
    exists A, H', (hflag (sub H 0 400) (macb cx nb len) idx).
    split; [exact LA|]. split; [exact (hb_garr8_pt _ _ _ _ (hb_s45_ptr W _ _ HptA) GA)|]. split; [exact SF|].
    split; [exact (hb_s45_rr cx E regs [w64 h] fq _ _ _ 19%bv 19%bv _ HdE HrL HAr2 HSpi ltac:(vm_compute; reflexivity) R19)|]. split; [exact FL|].
    destruct HH' as (LH' & GH' & QH' & EH'). split; [exact LH'|].
    split; [exact (hb_garr8_pt _ _ _ _ (hb_s45_ptr W _ _ HptA) GH')|]. split; assumption.
Qed.

Theorem hobs_spec_pf : AR_laws SEGS B -> PALib B -> frame_flag_lawP SEGS B ->
  (forall fq : YK11.FPState, abcmp_realizes (fx := fq) SEGS B (SIGMA DS___interceptor_trampoline_bcmp)) ->
  MT = ameter_triv -> treac_hunt_observe_spec B -> tcheck_sighting_spec B ->
  d_ro_hyps B -> d_can_hyps B tfib_K -> dimg_consts_of_ro_stmt B ->
  hobs_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
intros LAWS TL FFL ABCMP MTT THOBS TCHKS HRO HCAN HDCRO cx h i n now op nb fr len W c Hin.
eapply SRr_bind; [exact (hb_s01 LAWS TL FFL cx h i n now op nb fr len W c Hin)|]. intros W1 c1 _ H1.
eapply SRr_bind; [exact (hb_c12 LAWS TL ABCMP MTT cx h i n now op nb fr len W1 c1 H1)|]. intros W2 c2 _ H2.
eapply SRr_bind; [exact (hb_s23 LAWS TL FFL cx h i n now op nb fr len W2 c2 H2)|]. intros W3 c3 _ H3.
eapply SRr_bind; [exact (hb_c34 LAWS TL MTT THOBS HRO HCAN HDCRO cx h i n now op nb fr len W3 c3 H3)|]. intros W4 c4 _ H4.
eapply SRr_bind; [exact (hb_s45 LAWS TL FFL cx h i n now op nb fr len W4 c4 H4)|]. intros W5 c5 _ [H5 | H7].
- eapply SRr_bind; [exact (hb_c56 LAWS TL MTT TCHKS cx h i n now op nb fr len W5 c5 H5)|]. intros W6 c6 _ H6.
  eapply SRr_bind; [exact (hb_s67 LAWS TL FFL cx h i n now op nb fr len W6 c6 H6)|]. intros W7 c7 _ H7'.
  eapply SRr_bind; [exact (hb_c78 LAWS TL ABCMP MTT cx h i n now op nb fr len W7 c7 H7')|]. intros W8 c8 _ H8.
  exact (hb_s8e LAWS TL FFL cx h i n now op nb fr len W8 c8 H8).
- eapply SRr_bind; [exact (hb_c78 LAWS TL ABCMP MTT cx h i n now op nb fr len W5 c5 H7)|]. intros W8 c8 _ H8.
  exact (hb_s8e LAWS TL FFL cx h i n now op nb fr len W8 c8 H8).
Qed.

End h.
End f.
End d.
