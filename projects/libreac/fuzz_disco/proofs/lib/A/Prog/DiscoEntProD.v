(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 1700 of its 1728 lines of code are new or changed and 41 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
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
YC1g YC1h YC81 YC4b YC45 YC85 YCkd YC1i ACbf ACj1 DiscoACjr DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoEntProCuts DiscoEntProSeat.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
ReacDiscoTableInit ReacDiscoGateInit ReacDiscoPeerLockInit ReacHuntInit ReacHuntPin ReacHuntSilenceProven.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c disco_classify_c hunt_c slot_inv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_hunt_init_c reac_disco_table_init_c CtrlParsed.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition pd_srx (r : nat) : sv :=
  match r with
  | 0%nat => SLit 0 | 2%nat => SOff AT_A 0 | 8%nat => SOff AT_STK 0 | 9%nat => SOff AT_A 0 | 18%nat => SOff 32 0
  | 20%nat => SOff AT_F 32 | 22%nat => SOff AT_F 2992 | 24%nat => SOff AT_F 0 | 25%nat => SOff AT_F 0
  | 26%nat => SOff AT_F 2128
  | _ => SOff (AT_X + r) 0
  end.
Definition pd_sr : list sv := map pd_srx (seq 0 32).
Definition pd_vals (regs : bvmap 5 word) : list word := map (fun r => getr regs (Z_to_bv 5 (Z.of_nat r))) (seq 0 32).
Definition pd_cs : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition PDspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition RA_TI : Z := 0x730.
Definition RA_GI : Z := 0x738.
Definition RA_LI : Z := 0x740.
Definition RA_HI : Z := 0x758.
Definition RA_PIN : Z := 0x770.
Definition NOW0 : Z := 1000000000.

Lemma pd_w64_add : forall a b, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 a) + b) = Z_to_bv 64 (a + b).
Proof.
  intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Z.add_mod_idemp_l by (unfold bv_modulus; cbn; lia). reflexivity.
Qed.
Lemma pd_frame_of_ro : forall E rs (m m' : word -> option byte), frame_of E rs m m' ->
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> m' = m.
Proof.
  intros E rs m m' HF Hro. apply functional_extensionality. intros x. apply HF. intros (r & Hin & Ha).
  rewrite forallb_forall in Hro. specialize (Hro r Hin). apply Z.leb_le in Hro. lia.
Qed.
Ltac pd_ro_base HS n :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let i := idx_of_base rs n in let i := eval vm_compute in i in
  let r := eval vm_compute in (nth i rs got_regionP) in
  let HS3 := fresh "HS3" in
  pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl
    ltac:(vm_compute; reflexivity)
    (region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
      ltac:(intros o Ho; lia))) as HS3;
  clear HS; rename HS3 into HS; norm_ss HS end.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.

Definition pd_at (cx : dcx) (h pc : Z) (acs : list YP09.chunk) (R : bvmap 5 word -> Prop)
  (X : world SEGS -> (word -> option byte) -> Prop) : world SEGS -> config -> Prop :=
  d_at B MT XM_LIB RLO RHI tfib_K cx pc EV_PRO (ACC_PRO MT) (fun regs ly3 S3 W3 mem3 md3 =>
    0 <= c_canary cx < 2 ^ 64 /\ R regs /\ p_frame cx dsh_loop acs W3 mem3 /\ d_blocks B cx h [] ly3 S3 /\
    garr8 SEGS (rd W3 mem3) (d_obj cx OOUR) (map (fun b : byte => bv_unsigned b) (our_of (c_pl cx))) /\ X W3 mem3).
Definition pd_objs (cx : dcx) (os : list dobj) (W : world SEGS) (m : word -> option byte) : Prop :=
  Forall (fun o => d_obj_new cx o W m) os.
Definition pd_v216 (cx : dcx) (h : Z) (W : world SEGS) (m : word -> option byte) : Prop :=
  val_mem SEGS (rd W m) (d_A cx + 216) 8 h.
Definition pd_q1 (cx : dcx) (h : Z) : world SEGS -> config -> Prop :=
  pd_at cx h AF_reac_disco_table_init ps_C4
    (fun regs => p_rC4 cx h B regs /\ getr regs 1 = w64 (BASE + RA_TI) /\ getr regs 10 = w64 (d_obj cx OT))
    (pd_objs cx []).
Definition pd_q2 (cx : dcx) (h : Z) : world SEGS -> config -> Prop :=
  pd_at cx h RA_TI ps_C4 (p_rC4 cx h B) (pd_objs cx [OT]).
Definition pd_q3 (cx : dcx) (h : Z) : world SEGS -> config -> Prop :=
  pd_at cx h AF_reac_disco_gate_init ps_C4
    (fun regs => p_rC4 cx h B regs /\ getr regs 1 = w64 (BASE + RA_GI) /\ getr regs 10 = w64 (d_obj cx OG))
    (pd_objs cx [OT]).
Definition pd_q4 (cx : dcx) (h : Z) : world SEGS -> config -> Prop :=
  pd_at cx h RA_GI ps_C4 (p_rC4 cx h B) (pd_objs cx [OG; OT]).
Definition pd_q5 (cx : dcx) (h : Z) : world SEGS -> config -> Prop :=
  pd_at cx h AF_reac_disco_peer_lock_init ps_C4
    (fun regs => p_rC4 cx h B regs /\ getr regs 1 = w64 (BASE + RA_LI) /\ getr regs 10 = w64 (d_obj cx OLOCK))
    (pd_objs cx [OG; OT]).
Definition pd_q6 (cx : dcx) (h : Z) : world SEGS -> config -> Prop :=
  pd_at cx h RA_LI ps_C4 (p_rC4 cx h B) (pd_objs cx [OLOCK; OG; OT]).
Definition pd_X8 (cx : dcx) (h : Z) (W : world SEGS) (m : word -> option byte) : Prop :=
  pd_objs cx [OLOCK; OG; OT] W m /\ pd_v216 cx h W m /\ d_h_new cx h W m.
Definition pd_q7 (cx : dcx) (h : Z) : world SEGS -> config -> Prop :=
  pd_at cx h AF_reac_hunt_init ps_C4
    (fun regs => p_rC4 cx h B regs /\ getr regs 1 = w64 (BASE + RA_HI) /\ getr regs 10 = w64 h /\
       getr regs 11 = w64 (d_obj cx OOUR) /\ getr regs 12 = w64 NOW0)
    (fun W m => pd_objs cx [OLOCK; OG; OT] W m /\ pd_v216 cx h W m).
Definition pd_q8 (cx : dcx) (h : Z) : world SEGS -> config -> Prop :=
  pd_at cx h RA_HI ps_C4 (p_rC4 cx h B) (pd_X8 cx h).
Definition pd_q9 (cx : dcx) (h : Z) : world SEGS -> config -> Prop :=
  pd_at cx h AF_reac_hunt_pin ps_C4
    (fun regs => p_rC4 cx h B regs /\ getr regs 1 = w64 (BASE + RA_PIN) /\ getr regs 10 = w64 h) (pd_X8 cx h).
Definition pd_q10 (cx : dcx) (h : Z) : world SEGS -> config -> Prop :=
  pd_at cx h RA_PIN ps_C4 (p_rC4 cx h B) (pd_X8 cx h).
Definition pd_q11 (cx : dcx) (h : Z) : world SEGS -> config -> Prop :=
  pd_at cx h AF_reac_hunt_silence_proven ps_C5
    (fun regs => p_rC5 cx h B regs /\ getr regs 1 = w64 (BASE + POFF_C5) /\ getr regs 10 = w64 h) (pd_X8 cx h).
Definition pd_c216 : YP09.chunk := YP09.mkChunk 216 (CVal 8 (SOff (AT_X + 23) 0)).
Definition pd_wr60 (rs : smem) : bool :=
  forallb (fun r => (YP09.r_whi r <=? YP09.r_wlo r) ||
    (obase_eqb (YP09.r_base r) (Some 60%nat) && (0 <=? YP09.r_wlo r) && (YP09.r_whi r <=? 472))) rs.
Definition pd_inb (lo hi : Z) (cs : list YP09.chunk) : bool :=
  forallb (fun c => (lo <=? YP09.c_off c) && (YP09.c_off c + YP09.c_len c <=? hi)) cs.
Definition pd_fp (cx : dcx) (a : Z) : Prop :=
  (d_S cx - 104 <= a < d_S cx) \/ (d_A cx <= a < d_A cx + 472) \/ (d_FB cx <= a < d_FB cx + 24) \/
  (d_FB cx + 4088 <= a < d_FB cx + 4096) \/ (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512).
Definition pd_dom (cx : dcx) (h a : Z) : Prop :=
  (d_S cx - 104 <= a < d_S cx) \/ (d_A cx <= a < d_A cx + 472) \/ (d_FB cx <= a < d_FB cx + 4096) \/
  (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512) \/ (h <= a < h + HUNT_SIZE).
Definition pd_ikept (STK n : Z) (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte)
  (W2 : world SEGS) (mem2 : word -> option byte) (sp x : Z) : Prop :=
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - STK <= a < sp) -> ~ (x <= a < x + n) ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ (x <= b + i < x + n) ->
     aview SEGS (w_H W2) mem2 (b + i) = aview SEGS (w_H W) memc (b + i)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     ~ (x <= a < x + n) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - STK <= a < sp) ->
     apresent (w_H W) memc a -> apresent (w_H W2) mem2 a) /\
  (forall a, sp - STK <= a < sp -> apresent (w_H W2) mem2 a).
Definition pd_saddr_okb (x s : Z) : bool := (s =? 0) || ((x mod 8 <? s) && (s <? 8)).
Definition pd_obj_shb (o : dobj) : bool :=
  forallb (fun j => let x := dobj_off o + Z.of_nat j in pd_saddr_okb x (dsh_loop (x / 8)))
    (seq 0 (Z.to_nat (dobj_size o))).

Lemma pd_inb_ok : forall lo hi cs c i, pd_inb lo hi cs = true -> In c cs -> 0 <= i < YP09.c_len c ->
  lo <= YP09.c_off c + i < hi.
Proof.
  intros lo hi cs c i H Hc Hi. unfold pd_inb in H. rewrite forallb_forall in H.
  specialize (H c Hc). apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2. lia.
Qed.
Lemma pd_region_kept : forall E H H' (m m' : word -> option byte) r,
  region_ok SEGS E (mrestrict H m) r ->
  (forall c i, In c (YP09.r_chunks r) -> 0 <= i < YP09.c_len c ->
     aview SEGS H' m' (base_val E (YP09.r_base r) + YP09.c_off c + i) =
     aview SEGS H m (base_val E (YP09.r_base r) + YP09.c_off c + i)) ->
  (forall o, YP09.r_wlo r <= o < YP09.r_whi r -> apresent H' m' (base_val E (YP09.r_base r) + o)) ->
  region_ok SEGS E (mrestrict H' m') r.
Proof.
  intros E H H' m m' r HR Hc Hw. unfold region_ok in HR |- *. cbv zeta in HR |- *.
  destruct HR as (B1 & B2 & _ & C).
  split; [exact B1|]. split; [exact B2|]. split.
  - intros o Ho. apply (apresent_writable SEGS). apply Hw. exact Ho.
  - apply Forall_forall. intros c Hin. pose proof (proj1 (Forall_forall _ _) C c Hin) as Hck.
    intros i Hi. destruct (Hck i Hi) as (b & Hb1 & Hb2). exists b. split; [exact Hb1|].
    rewrite (mbyte_of_aview SEGS H H' m m' _ (Hc c i Hin Hi)). exact Hb2.
Qed.
Lemma pd_rdword_kept : forall (rd rd' : Z -> option Z) a, (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) ->
  rdword rd' a = rdword rd a.
Proof.
  intros rd rd' a H. unfold rdword.
  pose proof (H 0 ltac:(lia)) as E0. rewrite Z.add_0_r in E0.
  rewrite E0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.
Lemma pd_frame_kept : forall cx shf acs (W W' : world SEGS) m m',
  pd_inb 0 472 acs = true -> pd_inb 0 512 (dsh_chunks shf) = true ->
  0 <= d_A cx -> d_A cx + 472 <= d_S cx -> d_S cx <= 2 ^ 47 -> 0 <= d_FB cx -> d_FB cx + 4096 <= 2 ^ 47 ->
  p_frame cx shf acs W m ->
  (forall a, pd_fp cx a -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  (forall a, d_A cx <= a < d_A cx + 472 -> apresent (w_H W') m' a) ->
  (forall a, d_FB cx <= a < d_FB cx + 4096 -> apresent (w_H W') m' a) ->
  (forall i, 0 <= i < 512 -> apresent (w_H W') m' (shadow_addr (d_FB cx) + i)) ->
  p_frame cx shf acs W' m'.
Proof.
  intros cx shf acs W W' m m' Hacs Hsh HA0 HA1 HS1 HF0 HF1 (E & HE & HR & HFL) Hv HpA HpF HpS.
  pose proof HE as (EE & E32 & HEI & E60 & EF & ESH).
  assert (Hd0 : 0 <= d_FB cx / 8) by (apply Z.div_pos; lia).
  assert (Hd1 : d_FB cx / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
  assert (U2 : base_val E (Some AT_STK) = d_S cx).
  { cbn [base_val]. unfold AT_STK. rewrite (EE 2%nat 2%bv eq_refl). reflexivity. }
  assert (U60 : base_val E (Some AT_A) = d_A cx).
  { cbn [base_val]. rewrite E60. apply unsigned_lit_small. lia. }
  assert (U516 : base_val E (Some AT_F) = d_FB cx).
  { cbn [base_val]. rewrite EF. apply unsigned_lit_small. lia. }
  assert (U529 : base_val E (Some AT_SH) = shadow_addr (d_FB cx)).
  { cbn [base_val]. rewrite ESH. apply unsigned_lit_small. unfold shadow_addr, SHADOW_OFF. lia. }
  exists E. split; [exact HE|]. split.
  - unfold p_regions in HR |- *.
    pose proof (Forall_inv HR) as R1. apply Forall_inv_tail in HR.
    pose proof (Forall_inv HR) as R2. apply Forall_inv_tail in HR.
    pose proof (Forall_inv HR) as R3. apply Forall_inv_tail in HR.
    pose proof (Forall_inv HR) as R4. clear HR.
    repeat apply Forall_cons; try apply Forall_nil.
    + apply (pd_region_kept E (w_H W) (w_H W') m m' _ R1).
      * cbn [YP09.r_base YP09.r_chunks]. rewrite U2. intros c i Hc Hi. apply Hv. left.
        pose proof (pd_inb_ok (-104) 0 dsave_chunks c i ltac:(vm_compute; reflexivity) Hc Hi). lia.
      * cbn [YP09.r_wlo YP09.r_whi]. intros o Ho. lia.
    + apply (pd_region_kept E (w_H W) (w_H W') m m' _ R2).
      * cbn [YP09.r_base YP09.r_chunks]. rewrite U60. intros c i Hc Hi. apply Hv. right. left.
        pose proof (pd_inb_ok 0 472 acs c i Hacs Hc Hi). lia.
      * cbn [YP09.r_base YP09.r_wlo YP09.r_whi]. rewrite U60. intros o Ho. apply HpA. lia.
    + apply (pd_region_kept E (w_H W) (w_H W') m m' _ R3).
      * cbn [YP09.r_base YP09.r_chunks]. rewrite U516. intros c i Hc Hi. apply Hv. right. right. left.
        pose proof (pd_inb_ok 0 24 dfhdr3 c i ltac:(vm_compute; reflexivity) Hc Hi). lia.
      * cbn [YP09.r_base YP09.r_wlo YP09.r_whi]. rewrite U516. intros o Ho. apply HpF. unfold DFRAME_SIZE in Ho. lia.
    + apply (pd_region_kept E (w_H W) (w_H W') m m' _ R4).
      * unfold fshadow_region. cbn [YP09.r_base YP09.r_chunks]. rewrite U529. intros c i Hc Hi.
        apply Hv. right. right. right. right.
        pose proof (pd_inb_ok 0 512 (dsh_chunks shf) c i Hsh Hc Hi). lia.
      * unfold fshadow_region. cbn [YP09.r_base YP09.r_wlo YP09.r_whi]. rewrite U529. intros o Ho.
        apply HpS. unfold DFRAME_SH in Ho. lia.
  - rewrite (pd_rdword_kept (aview SEGS (w_H W) m) (aview SEGS (w_H W') m')); [exact HFL|].
    intros i Hi. apply Hv. right. right. right. left. change (fs_frame_bytes DFRAME_CLASS) with 4096. lia.
Qed.
Lemma pd_val_mem_kept : forall (W W' : world SEGS) m m' p n v, val_mem SEGS (rd W m) p n v ->
  (forall a, p <= a < p + Z.of_nat n -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  val_mem SEGS (rd W' m') p n v.
Proof.
  intros W W' m m' p n v H Hv k Hk.
  rewrite (mbyte_of_aview SEGS (w_H W) (w_H W') m m' (p + Z.of_nat k) (Hv (p + Z.of_nat k) ltac:(lia))). exact (H k Hk).
Qed.
Lemma pd_garr8_kept : forall (W W' : world SEGS) m m' p l, garr8 SEGS (rd W m) p l ->
  (forall a, p <= a < p + Z.of_nat (length l) -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  garr8 SEGS (rd W' m') p l.
Proof.
  intros W W' m m' p l H Hv j Hj. destruct (H j Hj) as [H1 H2]. split; [|exact H2].
  apply (pd_val_mem_kept W W' m m' _ _ _ H1). intros a Ha. apply Hv. lia.
Qed.
Lemma pd_our_len : forall pl, length (our_of pl) = 6%nat.
Proof. intros pl. unfold our_of. rewrite length_map, length_seq. reflexivity. Qed.
Lemma pd_obj_kept : forall cx o (W W' : world SEGS) m m', d_obj_new cx o W m ->
  (forall a, d_objr cx o a -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) -> d_obj_new cx o W' m'.
Proof.
  intros cx o W W' m m' H Hv. destruct o; cbn [d_obj_new] in H |- *; try exact I.
  - apply (pd_garr8_kept W W' m m' _ _ H). intros a Ha. apply Hv. unfold d_objr. rewrite length_map, pd_our_len in Ha.
    cbn [dobj_size]. lia.
  - destruct H as (T & HL & HG & Hok). exists T. split; [exact HL|]. split; [|exact Hok].
    apply (pd_garr8_kept W W' m m' _ _ HG). intros a Ha. apply Hv. unfold d_objr. rewrite length_map, HL in Ha.
    cbn [dobj_size]. lia.
  - destruct H as (T & HL & HG & Hok). exists T. split; [exact HL|]. split; [|exact Hok].
    apply (pd_garr8_kept W W' m m' _ _ HG). intros a Ha. apply Hv. unfold d_objr. rewrite length_map, HL in Ha.
    cbn [dobj_size]. lia.
  - destruct H as (T & HL & HG & Hok). exists T. split; [exact HL|]. split; [|exact Hok].
    apply (pd_garr8_kept W W' m m' _ _ HG). intros a Ha. apply Hv. unfold d_objr. rewrite length_map, HL in Ha.
    cbn [dobj_size]. lia.
Qed.
Lemma pd_objs_kept : forall cx os (W W' : world SEGS) m m', pd_objs cx os W m ->
  (forall o a, In o os -> d_objr cx o a -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) -> pd_objs cx os W' m'.
Proof.
  intros cx os W W' m m' H Hv. unfold pd_objs in *. apply Forall_forall. intros o Ho.
  apply (pd_obj_kept cx o W W' m m' (proj1 (Forall_forall _ _) H o Ho)). intros a Ha. exact (Hv o a Ho Ha).
Qed.
Lemma pd_hnew_kept : forall cx h (W W' : world SEGS) m m', d_h_new cx h W m ->
  (forall a, h <= a < h + HUNT_SIZE -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) -> d_h_new cx h W' m'.
Proof.
  intros cx h W W' m m' (H & HL & HG & Hok & Hour) Hv. exists H. split; [exact HL|]. split; [|split; [exact Hok | exact Hour]].
  apply (pd_garr8_kept W W' m m' _ _ HG). intros a Ha. apply Hv. rewrite length_map, HL in Ha. unfold HUNT_SIZE. lia.
Qed.
Lemma pd_blocks_kept : forall cx h ly S ly' S', d_blocks B cx h [] ly S ->
  Permutation (ablocks B ly' S') (ablocks B ly S) -> d_blocks B cx h [] ly' S'.
Proof.
  intros cx h ly S ly' S' (HP & Hn & Hbb & Hoff) HP'. split; [exact (perm_trans HP' HP)|]. split; [exact Hn|].
  split; [|exact Hoff].
  rewrite (blocks_bytes_bsum B ly' S'), (bsum_perm _ _ HP'), <- (blocks_bytes_bsum B ly S). exact Hbb.
Qed.
Lemma pd_ikept_view : forall cx h STK n lyc Sc W memc W2 mem2 x,
  pd_ikept STK n lyc Sc W memc W2 mem2 (d_A cx) x ->
  alloc_ceiling <= d_S cx - 1024 -> d_S cx <= 2 ^ 47 -> d_S cx - 592 <= d_A cx <= d_S cx - 576 ->
  In (DFRAME_CLASS, c_fpos cx) (frames Sc) -> frame_addr lyc DFRAME_CLASS (c_fpos cx) = d_FB cx ->
  In (h, HUNT_SIZE) (ablocks B lyc Sc) ->
  forall a, pd_dom cx h a -> ~ (x <= a < x + n) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a.
Proof.
  intros cx h STK n lyc Sc W memc W2 mem2 x (K1 & K2 & _ & K4 & _) Hc HS HA Hfin Efa Hhb a Ha Hx.
  destruct Ha as [Ha | [Ha | [Ha | [Ha | Ha]]]].
  - apply K1; [lia | lia | exact Hx].
  - apply K1; [lia | lia | exact Hx].
  - apply (K4 DFRAME_CLASS (c_fpos cx) a Hfin); [|exact Hx]. left. unfold in_zr, frame_rng. cbn [fst snd].
    rewrite Efa. change (fs_frame_bytes DFRAME_CLASS) with 4096. lia.
  - apply (K4 DFRAME_CLASS (c_fpos cx) a Hfin); [|exact Hx]. right. unfold in_zr. cbn [fst snd].
    rewrite Efa. change (fs_frame_bytes DFRAME_CLASS / 8) with 512. lia.
  - replace a with (h + (a - h)) by lia. apply (K2 h HUNT_SIZE (a - h) Hhb).
    + unfold req_size, HUNT_SIZE in *. cbn. lia.
    + replace (h + (a - h)) with a by lia. exact Hx.
Qed.
Lemma pd_aj_view : forall cx h STK FP lyc Sc (W : world SEGS) memc mdc ly2 S2 W2 mem2 md2 k,
  ajournal SEGS B STK (d_A cx) FP lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k ->
  alloc_ceiling <= d_S cx - 1024 -> d_S cx <= 2 ^ 47 -> d_S cx - 592 <= d_A cx <= d_S cx - 576 ->
  In (DFRAME_CLASS, c_fpos cx) (frames Sc) -> frame_addr lyc DFRAME_CLASS (c_fpos cx) = d_FB cx ->
  In (h, HUNT_SIZE) (ablocks B lyc Sc) -> In (h, HUNT_SIZE) (ablocks B ly2 S2) ->
  forall a, pd_dom cx h a -> ~ inFP FP a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a.
Proof.
  intros cx h STK FP lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k HJ Hc HS HA Hfin Efa Hh1 Hh2 a Ha Hx.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & _ & F4 & _).
  destruct Ha as [Ha | [Ha | [Ha | [Ha | Ha]]]].
  - apply F1; lia.
  - apply F1; lia.
  - apply (F4 DFRAME_CLASS (c_fpos cx) a Hfin); [|exact Hx]. left. unfold in_zr, frame_rng. cbn [fst snd].
    rewrite Efa. change (fs_frame_bytes DFRAME_CLASS) with 4096. lia.
  - apply (F4 DFRAME_CLASS (c_fpos cx) a Hfin); [|exact Hx]. right. unfold in_zr. cbn [fst snd].
    rewrite Efa. change (fs_frame_bytes DFRAME_CLASS / 8) with 512. lia.
  - replace a with (h + (a - h)) by lia. apply (F2 h HUNT_SIZE (a - h) Hh1 Hh2).
    + unfold req_size, HUNT_SIZE in *. cbn. lia.
    + replace (h + (a - h)) with a by lia. exact Hx.
Qed.
Lemma pd_dshadow : forall cx acs (W : world SEGS) m, 0 <= d_FB cx -> d_FB cx + 4096 <= 2 ^ 47 ->
  p_frame cx dsh_loop acs W m -> d_shadow cx dsh_loop W m.
Proof.
  intros cx acs W m HF0 HF1 (E & HE & HR & _).
  pose proof HE as (_ & _ & _ & _ & _ & ESH).
  assert (Hd0 : 0 <= d_FB cx / 8) by (apply Z.div_pos; lia).
  assert (Hd1 : d_FB cx / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
  assert (U529 : base_val E (Some AT_SH) = shadow_addr (d_FB cx)).
  { cbn [base_val]. rewrite ESH. apply unsigned_lit_small. unfold shadow_addr, SHADOW_OFF. lia. }
  unfold p_regions in HR. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HR)))) as R4.
  pose proof (sh_region_bytes SEGS E (rd W m) dsh_loop (fshadow_region AT_SH DFRAME_CLASS 0 DFRAME_SH (dsh_chunks dsh_loop))
    ltac:(vm_compute; reflexivity) R4) as HSB.
  unfold fshadow_region in HSB. cbn [YP09.r_base] in HSB. rewrite U529 in HSB.
  intros kk Hk. destruct (HSB kk Hk) as (Hr & Hm). unfold aview. rewrite Hm. cbn [option_map].
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. f_equal. apply Z.mod_small. exact Hr.
Qed.
Lemma pd_saddr_okb_ok : forall x s, pd_saddr_okb x s = true -> saddr_ok x s.
Proof.
  intros x s H. unfold pd_saddr_okb in H. unfold saddr_ok.
  apply orb_true_iff in H as [H | H]; [left; apply Z.eqb_eq; exact H|].
  apply andb_true_iff in H as [H1 H2]. right. apply Z.ltb_lt in H1, H2. lia.
Qed.
Lemma pd_obj_ra : forall cx (W : world SEGS) m o, d_shadow cx dsh_loop W m -> d_FB cx mod 8 = 0 -> 0 <= d_FB cx ->
  pd_obj_shb o = true -> range_addressable (aview SEGS (w_H W) m) SHADOW_OFF (d_obj cx o) (dobj_size o).
Proof.
  intros cx W m o Hsh Hal H0 Hb x Hx. unfold d_obj in Hx.
  assert (Hob : dobj_off o + dobj_size o <= 3072 /\ 0 <= dobj_off o) by (destruct o; cbn; lia).
  set (j := x - d_FB cx - dobj_off o).
  assert (Hj : 0 <= j < dobj_size o) by (subst j; lia).
  unfold pd_obj_shb in Hb. rewrite forallb_forall in Hb.
  specialize (Hb (Z.to_nat j) ltac:(apply in_seq; lia)). cbv zeta in Hb. rewrite Z2Nat.id in Hb by lia.
  assert (Ex : x = d_FB cx + (dobj_off o + j)) by (subst j; lia).
  assert (Hdiv : x / 8 = d_FB cx / 8 + (dobj_off o + j) / 8) by (rewrite Ex; lia).
  assert (Hmod : x mod 8 = (dobj_off o + j) mod 8) by (rewrite Ex; lia).
  exists (dsh_loop ((dobj_off o + j) / 8)). split.
  - unfold shadow_of_addr. rewrite Hdiv.
    assert (Hk : 0 <= (dobj_off o + j) / 8 < DFRAME_SH).
    { unfold DFRAME_SH. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    rewrite <- (Hsh _ Hk). unfold shadow_addr. f_equal. lia.
  - apply pd_saddr_okb_ok. unfold pd_saddr_okb in Hb |- *. rewrite Hmod. exact Hb.
Qed.
Lemma pd_obj_hull : forall cx (W : world SEGS) m o, d_shadow cx dsh_loop W m -> d_FB cx mod 8 = 0 -> 0 <= d_FB cx ->
  56 <= dobj_off o -> dobj_off o + dobj_size o <= 3000 -> 0 < dobj_size o ->
  shadow_hull_vis (aview SEGS (w_H W) m) (d_obj cx o) (dobj_size o).
Proof.
  intros cx W m o Hsh Hal H0 Hlo Hhi Hn s Hs. unfold d_obj, shadow_addr in Hs.
  assert (Hk : 0 <= s - shadow_addr (d_FB cx) < DFRAME_SH) by (unfold shadow_addr, DFRAME_SH; lia).
  replace s with (shadow_addr (d_FB cx) + (s - shadow_addr (d_FB cx))) by lia.
  rewrite (Hsh _ Hk). discriminate.
Qed.

Lemma pd_wr60_ok : forall E rs a, pd_wr60 rs = true -> in_wrange E rs a ->
  base_val E (Some 60%nat) <= a < base_val E (Some 60%nat) + 472.
Proof.
  intros E rs a Hb (r & Hin & Ha). unfold pd_wr60 in Hb. rewrite forallb_forall in Hb. specialize (Hb r Hin).
  apply orb_true_iff in Hb as [Hb | Hb]; [apply Z.leb_le in Hb; lia|].
  apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [Hb H1]. apply Z.leb_le in H1, H2.
  destruct (YP09.r_base r) as [n|] eqn:Eb; [|discriminate Hb]. cbn [obase_eqb] in Hb. apply Nat.eqb_eq in Hb. subst n.
  lia.
Qed.
Lemma pd_aview_frame : forall E rs H (m m' : word -> option byte) a,
  frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
  aview SEGS H m' a = aview SEGS H m a.
Proof.
  intros E rs H m m' a HF Ha Hn. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia. exact Hn.
Qed.
Lemma pd_nth_map_bv : forall (l : list byte) j, (j < length l)%nat ->
  nth j (map (fun b : byte => bv_unsigned b) l) 0 = bv_unsigned (nth j l (Z_to_bv 8 0)).
Proof.
  intros l j Hj. rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hj).
  apply (map_nth (fun b : byte => bv_unsigned b)).
Qed.

Lemma pd_regs_ok : forall cx E regs, d_E cx E -> p_rbase cx regs B ->
  0 <= d_A cx < 2 ^ 64 -> 0 <= d_FB cx < 2 ^ 64 ->
  regs_ok (d_env cx E (pd_vals regs)) pd_sr regs.
Proof.
  intros cx E regs HE HL HA HF.
  destruct HE as (HER & H32 & _ & HA60 & HF516 & _).
  destruct HL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H22 & H24 & H25 & H26).
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
    | unfold d_env; rewrite ew_havoc_old by (cbv; lia);
      first [ rewrite HA60, Z.add_0_r, Z_to_bv_bv_unsigned; first [exact H2 | exact H9]
            | rewrite HS2, Z.add_0_r, Z_to_bv_bv_unsigned; exact H8
            | rewrite H32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H18
            | rewrite HF516, pd_w64_add; first [exact H20 | exact H22 | exact H26
                | rewrite Z.add_0_r; first [exact H24 | exact H25]] ]
    | rewrite Z.add_0_r; unfold d_env, havoc; cbn [ew Nat.ltb Nat.leb Nat.sub nth pd_vals map seq Nat.add AT_X AT_FL];
      match goal with |- getr ?rg _ = Z_to_bv 64 (bv_unsigned (getr ?rg ?x)) =>
        let y := eval vm_compute in x in change x with y end;
      rewrite Z_to_bv_bv_unsigned; reflexivity ]).
Qed.

Lemma pd_regs_same : forall (fq : YK11.FPState) E ss ms regs (rl : list (bv 5)) H,
  st_ok (fx := fq) SEGS E ss (restrict H ms) -> regs_ok E pd_sr regs ->
  forallb (fun r => sv_eqb (sr_get (ss_regs ss) r) (sr_get pd_sr r)) rl = true ->
  forall r, In r rl -> getr (ms_regs ms) r = getr regs r.
Proof.
  intros fq E ss ms regs rl H HS Hok Hb r Hr.
  rewrite (st_ok_restrict_reg SEGS H E ss ms r HS), (Hok r).
  rewrite forallb_forall in Hb. rewrite (sv_eqb_eq _ _ (Hb r Hr)). reflexivity.
Qed.

Lemma p_rC4_eq : forall cx h regs regs', (forall r, In r pd_cs -> getr regs' r = getr regs r) ->
  p_rC4 cx h B regs -> p_rC4 cx h B regs'.
Proof.
  intros cx h regs regs' HR (((Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H22 & H24 & H25 & H26) & H19 & H21 & H27) & H23).
  unfold pd_cs in HR. cbv [In] in HR.
  unfold p_rC4, p_rC3, p_rbase, spZ.
  rewrite !HR by tauto. unfold spZ in Hsp. repeat split; assumption.
Qed.
Lemma p_rC5_eq : forall cx h regs regs', (forall r, In r pd_cs -> getr regs' r = getr regs r) ->
  p_rC5 cx h B regs -> p_rC5 cx h B regs'.
Proof.
  intros cx h regs regs' HR ((Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H22 & H24 & H25 & H26) & H19 & H21 & H27).
  unfold pd_cs in HR. cbv [In] in HR.
  unfold p_rC5, p_rbase, spZ.
  rewrite !HR by tauto. unfold spZ in Hsp. repeat split; assumption.
Qed.
Definition pd_cs2 : list (bv 5) := [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma p_rC5_build : forall cx h regs regs', (forall r, In r pd_cs2 -> getr regs' r = getr regs r) ->
  getr regs' 19 = w64 h -> p_rC4 cx h B regs -> p_rC5 cx h B regs'.
Proof.
  intros cx h regs regs' HR H19 (((Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H22 & H24 & H25 & H26) & H19o & H21 & H27) & H23).
  unfold pd_cs2 in HR. cbv [In] in HR.
  unfold p_rC5. split; [| split; [exact H19 | split]].
  - unfold p_rbase, spZ. rewrite !HR by tauto. unfold spZ in Hsp. repeat split; assumption.
  - rewrite HR by tauto. exact H21.
  - rewrite HR by tauto. exact H27.
Qed.
Lemma pd_cs_pres : forall regs regs', aregs_preserved regs regs' -> forall r, In r pd_cs -> getr regs' r = getr regs r.
Proof.
  intros regs regs' HP r Hr. unfold pd_cs in Hr. cbv [In] in Hr.
  repeat (destruct Hr as [<-|Hr]; [first [exact (HP 2 ltac:(unfold acallee_saved; lia)) | exact (HP 3 ltac:(unfold acallee_saved; lia))
    | exact (HP 4 ltac:(unfold acallee_saved; lia)) | exact (HP 8 ltac:(unfold acallee_saved; lia))
    | exact (HP 9 ltac:(unfold acallee_saved; lia)) | exact (HP 18 ltac:(unfold acallee_saved; lia))
    | exact (HP 19 ltac:(unfold acallee_saved; lia)) | exact (HP 20 ltac:(unfold acallee_saved; lia))
    | exact (HP 21 ltac:(unfold acallee_saved; lia)) | exact (HP 22 ltac:(unfold acallee_saved; lia))
    | exact (HP 23 ltac:(unfold acallee_saved; lia)) | exact (HP 24 ltac:(unfold acallee_saved; lia))
    | exact (HP 25 ltac:(unfold acallee_saved; lia)) | exact (HP 26 ltac:(unfold acallee_saved; lia))
    | exact (HP 27 ltac:(unfold acallee_saved; lia))]|]).
  destruct Hr.
Qed.

Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis MT_TRIV : MT = ameter_triv.

Ltac pd_rsr H := lazymatch type of H with context [sr_get ?sr ?r] =>
  let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v in H end.
Ltac pd_ldcall POFF SIGL RAk :=
  let cx := fresh "cx" in let h := fresh "h" in let W := fresh "W" in let c := fresh "c" in let H := fresh "H" in
  intros cx h W c H;
  destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hf0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
    Hcan0 & HR & Hframe & Hblocks & Hour & HX);
  pose proof Hframe as (E & HdE & HRG & Hflag);
  assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
    by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]);
  destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HC)
    as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR3 & Hfin & Efa & Efl);
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
  pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2);
  assert (HAr : 0 <= d_A cx < 2 ^ 64) by (unfold MFRAME, LLVMF_STK in *; lia);
  assert (HFr : 0 <= d_FB cx < 2 ^ 64) by lia;
  pose proof (pd_regs_ok cx E regs HdE (proj1 (proj1 HR)) HAr HFr) as HROK;
  pose proof (p_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx dsh_loop ps_C4 ly3 S3 W regs mem3 md3 k E POFF pd_sr
    (pd_vals regs) [] [] [] (d_facts [] []) HC HdE HRG Hflag HROK
    (d_facts_ok B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k E (pd_vals regs) [] [] HC HdE I I)
    (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity)) as HS;
  unfold ss_p in HS;
  assert (HEI : img_env VAL A_LIM (d_env cx E (pd_vals regs)))
    by (destruct HdE as (_ & _ & HI & _); intros a Ha; unfold d_env;
        rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia); exact (HI a Ha));
  assert (EFB : ew (d_env cx E (pd_vals regs)) 516 = Z_to_bv 64 (d_FB cx))
    by (unfold d_env; rewrite ew_havoc_old by (cbv; lia); destruct HdE as (_ & _ & _ & _ & HF516 & _); exact HF516);
  assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (pd_vals regs)) (rd W mem3)) by constructor;
  pose (RUN := paj_run (fx := fq) B LAWS);
  unfold cfg_at; change (w64 (BASE + POFF)) with (Z_to_bv 64 (BASE + POFF));
  pd_ro_base HS 516%nat; pd_ro_base HS 529%nat; pd_ro_base HS 60%nat;
  paj_run_tok RUN HS HJ SHOK PDspan;
  [ cbn [ss_mem]; repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil | ];
  lazymatch goal with
  | HF0 : frame_of _ _ mem3 (ms_mem ?ms), HFr0 : frame_of _ _ (rd _ mem3) _, HG0 : mem_grows _ _
    |- SRr _ _ {| cfg_ms := ?ms; cfg_model := ?md4 |} _ =>
  pose proof (pd_frame_of_ro _ _ _ _ HF0 ltac:(vm_compute; reflexivity)) as Em; clear HF0 HFr0 HG0;
  rewrite SIGL in HS;
  pose proof (st_ok_restrict_mkst SEGS (w_H W) _ _ ms HS eq_refl) as Hms; cbn [ss_pc setpc] in Hms;
  pose proof (pd_regs_same fq _ _ ms regs pd_cs (w_H W) HS HROK ltac:(vm_compute; reflexivity)) as RG;
  pose proof (st_ok_restrict_reg SEGS (w_H W) _ _ ms 1%bv HS) as R1;
  pose proof (st_ok_restrict_reg SEGS (w_H W) _ _ ms 10%bv HS) as R10;
  pd_rsr R1; pd_rsr R10;
  apply SRr_ret; unfold pd_at, d_at;
  exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md4, k, acc;
  split; [unfold cfg_at, w64; rewrite <- Hms; reflexivity|];
  rewrite Em in HJ |- *;
  split; [exact Hf0|]; split; [exact Hbase|]; split; [exact HJ|]; split; [exact Hfrs|]; split; [exact Hk|];
  split; [exact Hnev|]; split; [exact Hmo|]; split; [exact Hacc|]; split; [exact Hcan0|];
  split; [|split; [exact Hframe|split; [exact Hblocks|split; [exact Hour| exact HX]]]];
  split; [exact (p_rC4_eq cx h regs _ RG HR)|]; split;
  [ rewrite R1; exact (codeptr_val _ RAk HEI)
  | rewrite R10; cbn [sv_denot]; rewrite EFB, pd_w64_add; reflexivity ]
  end.

Lemma pd_c4_at : forall cx h W c, pro_C4 B MT XM_LIB RLO RHI tfib_K cx h W c ->
  pd_at cx h POFF_C4 ps_C4 (p_rC4 cx h B) (pd_objs cx []) W c.
Proof.
  intros cx h W c (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Hc & Hf0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
    Hcan0 & HR & Hframe & Hblocks & Hour).
  exists fq, ly3, S3, regs, mem3, md3, k, acc.
  split; [exact Hc|]. split; [exact Hf0|]. split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
  split; [exact Hnev|]. split; [exact Hmo|]. split; [exact Hacc|]. split; [exact Hcan0|].
  split; [exact HR|]. split; [exact Hframe|]. split; [exact Hblocks|]. split; [exact Hour|]. constructor.
Qed.
Lemma pd_s1 : forall cx h W c, pd_at cx h POFF_C4 ps_C4 (p_rC4 cx h B) (pd_objs cx []) W c ->
  SRr SEGS W c (pd_q1 cx h).
Proof. pd_ldcall POFF_C4 (pa_sigma_reac_disco_table_init (PI := PI)) RA_TI. Qed.
Lemma pd_s3 : forall cx h W c, pd_q2 cx h W c -> SRr SEGS W c (pd_q3 cx h).
Proof. pd_ldcall RA_TI (pa_sigma_reac_disco_gate_init (PI := PI)) RA_GI. Qed.
Lemma pd_s5 : forall cx h W c, pd_q4 cx h W c -> SRr SEGS W c (pd_q5 cx h).
Proof. pd_ldcall RA_GI (pa_sigma_reac_disco_peer_lock_init (PI := PI)) RA_LI. Qed.

Definition pd_okV (o : dobj) (V : list byte) : Prop :=
  match o with
  | OT => disco_table_c.table_ok V | OG => disco_classify_c.gate_ok V | OLOCK => disco_classify_c.lock_ok V
  | _ => True
  end.
Definition pd_ispec (AF STK : Z) (o : dobj) (V : list byte) : Prop :=
  forall (fq : YK11.FPState) STKj sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
    (regs : bvmap 5 word) (x : Z),
  ajournal SEGS B STKj sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 10 = w64 x ->
  spZ regs mod 16 = 0 -> sp0 - STKj <= spZ regs - STK -> spZ regs <= sp0 ->
  x <> 0 -> x mod 8 = 0 -> 0 <= x -> x + dobj_size o <= 2 ^ 63 ->
  (spZ regs <= x \/ x + dobj_size o <= spZ regs - STK) ->
  (forall a, x <= a < x + dobj_size o ->
     awr_byte STKj sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a) ->
  amem_range x (dobj_size o) ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF x (dobj_size o) ->
  shadow_hull_vis (aview SEGS (w_H W) memc) x (dobj_size o) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF) regs memc mdc)
    (fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
       c2 = mkCfg (mkst (fx := fq) regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
       ajournal SEGS B STKj sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
       aregs_preserved regs regs2 /\ frames S2 = frames Sc /\ Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
       pd_ikept STK (dobj_size o) lyc Sc W memc W2 mem2 (spZ regs) x /\
       garr8 SEGS (mrestrict (w_H W2) mem2) x (map (fun b : byte => bv_unsigned b) V) /\
       length V = Z.to_nat (dobj_size o) /\ pd_okV o V).

Lemma pd_ispec_ti : treac_disco_table_init_spec B ->
  pd_ispec AF_reac_disco_table_init REAC_DISCO_TABLE_INIT_STK OT reac_disco_table_init_c.zero_table.
Proof.
  intros T fq STKj sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs x HJ Hra Hra4 Hgp Htp H10 Hal Hs1 Hs2
    Hx0 Hx8 Hx1 Hx2 Hsep Hwr Hmr Hrad Hhv.
  eapply SRr_mono; [exact (T fq STKj sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs x HJ Hra Hra4 Hgp Htp H10
    Hal Hs1 Hs2 Hx0 Hx8 Hx1 Hx2 Hsep Hwr Hmr Hrad Hhv)|].
  intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Hc & HJ2 & HP & _ & Hfr & Hperm & HK & HG & Hok).
  exists ly2, S2, regs2, mem2, md2. split; [exact Hc|]. split; [exact HJ2|]. split; [exact HP|]. split; [exact Hfr|].
  split; [exact Hperm|]. split; [exact HK|]. split; [exact HG|]. split; [vm_compute; reflexivity | exact Hok].
Qed.
Lemma pd_ispec_gi : treac_disco_gate_init_spec B ->
  pd_ispec AF_reac_disco_gate_init REAC_DISCO_GATE_INIT_STK OG (repeat (CtrlParsed.zb 0) 264).
Proof.
  intros T fq STKj sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs x HJ Hra Hra4 Hgp Htp H10 Hal Hs1 Hs2
    Hx0 Hx8 Hx1 Hx2 Hsep Hwr Hmr Hrad Hhv.
  eapply SRr_mono; [exact (T fq STKj sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs x HJ Hra Hra4 Hgp Htp H10
    Hal Hs1 Hs2 Hx1 Hx2 Hsep Hwr Hmr Hrad Hhv)|].
  intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Hc & HJ2 & HP & _ & _ & Hfr & Hperm & HK & HG & Hok).
  exists ly2, S2, regs2, mem2, md2. split; [exact Hc|]. split; [exact HJ2|]. split; [exact HP|]. split; [exact Hfr|].
  split; [exact Hperm|]. split; [exact HK|]. split; [exact HG|]. split; [vm_compute; reflexivity | exact Hok].
Qed.
Lemma pd_ispec_li : treac_disco_peer_lock_init_spec B ->
  pd_ispec AF_reac_disco_peer_lock_init REAC_DISCO_PEER_LOCK_INIT_STK OLOCK (repeat (CtrlParsed.zb 0) 12).
Proof.
  intros T fq STKj sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs x HJ Hra Hra4 Hgp Htp H10 Hal Hs1 Hs2
    Hx0 Hx8 Hx1 Hx2 Hsep Hwr Hmr Hrad Hhv.
  eapply SRr_mono; [exact (T fq STKj sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs x HJ Hra Hra4 Hgp Htp H10
    Hal Hs1 Hs2 ltac:(clear - Hx8; lia) Hx1 Hx2 Hsep Hwr Hmr Hrad Hhv)|].
  intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Hc & HJ2 & HP & _ & _ & Hfr & Hperm & HK & HG & Hok).
  exists ly2, S2, regs2, mem2, md2. split; [exact Hc|]. split; [exact HJ2|]. split; [exact HP|]. split; [exact Hfr|].
  split; [exact Hperm|]. split; [exact HK|]. split; [exact HG|]. split; [vm_compute; reflexivity | exact Hok].
Qed.
Lemma pd_obj_new_of : forall cx o V (W : world SEGS) m, (o = OT \/ o = OG \/ o = OLOCK) ->
  length V = Z.to_nat (dobj_size o) -> pd_okV o V ->
  garr8 SEGS (rd W m) (d_obj cx o) (map (fun b : byte => bv_unsigned b) V) -> d_obj_new cx o W m.
Proof.
  intros cx o V W m [-> | [-> | ->]] HL Hok HG; cbn [d_obj_new]; exists V;
    (split; [exact HL|]); (split; [exact HG | exact Hok]).
Qed.
Lemma pd_obj_box : forall o, 0 <= dobj_off o /\ dobj_off o + dobj_size o <= 3072.
Proof. intros o. destruct o; cbn; lia. Qed.

Lemma pd_init_step : forall AF STK o V ra os cx h W c,
  pd_ispec AF STK o V -> 0 <= STK <= 16 + ESTACK -> (o = OT \/ o = OG \/ o = OLOCK) -> pd_obj_shb o = true ->
  Forall (fun o' => dobj_off o' + dobj_size o' <= dobj_off o \/ dobj_off o + dobj_size o <= dobj_off o') (OOUR :: os) ->
  0 <= ra < 2 ^ 40 -> ra mod 2 = 0 ->
  pd_at cx h AF ps_C4 (fun regs => p_rC4 cx h B regs /\ getr regs 1 = w64 (BASE + ra) /\ getr regs 10 = w64 (d_obj cx o))
    (pd_objs cx os) W c ->
  SRr SEGS W c (pd_at cx h ra ps_C4 (p_rC4 cx h B) (pd_objs cx (o :: os))).
Proof.
  intros AF STK o V ra os cx h W c HSP HSTK Ho Hshb Hdisj Hra0 Hra2 H.
  assert (Hoff : 56 <= dobj_off o /\ dobj_off o + dobj_size o <= 3000 /\ 0 < dobj_size o /\ dobj_off o mod 8 = 0)
    by (destruct Ho as [-> | [-> | ->]]; cbn; lia).
  destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hf0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
    Hcan0 & (HrC4 & Hra1 & H10) & Hframe & Hblocks & Hour & Hobjs).
  assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
    by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
  destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HC)
    as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR3 & Hfin & Efa & Efl).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
  pose proof (pd_dshadow cx ps_C4 W mem3 ltac:(lia) ltac:(lia) Hframe) as Hsh.
  pose proof (proj1 (proj1 HrC4)) as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H22 & H24 & H25 & H26).
  pose proof pa_B_ok as (HB0 & HB1 & _). pose proof pa_base_lo as HBlo.
  assert (Hraz : raZ regs = BASE + ra) by (unfold raZ; rewrite Hra1; apply unsigned_lit_small; lia).
  assert (HFB8 : d_FB cx mod 8 = 0) by lia.
  assert (Hhin : In (h, HUNT_SIZE) (ablocks B ly3 S3)).
  { destruct Hblocks as (HPm & _). apply (Permutation_in _ (Permutation_sym HPm)). left. reflexivity. }
  eapply SRr_mono.
  { apply (HSP fq LLVMF_STK (d_S cx) (@nil (Z * Z)) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)]
      ly3 S3 W mem3 md3 k regs (d_obj cx o) HJ).
    - rewrite Hra1. apply ret_ok_codeptr_v; [lia | exact Hra2].
    - rewrite Hraz. unfold IMG_LO in HBlo. lia.
    - exact Hgp.
    - exact Htp.
    - exact H10.
    - rewrite Hsp. lia.
    - rewrite Hsp. unfold LLVMF_STK, ESTACK, MFRAME in *. lia.
    - rewrite Hsp. unfold MFRAME in *. lia.
    - unfold d_obj. lia.
    - unfold d_obj. lia.
    - unfold d_obj. lia.
    - unfold d_obj. lia.
    - right. rewrite Hsp. unfold d_obj, ESTACK, LLVMF_STK, MFRAME in *. lia.
    - intros a Ha. split.
      + right. right. right. exists DFRAME_CLASS, (c_fpos cx). split; [left; reflexivity|]. left.
        unfold in_zr. cbn [fst snd]. rewrite Efa. change (fs_frame_bytes DFRAME_CLASS) with 4096. unfold d_obj in Ha. lia.
      + apply HFpres. unfold d_obj in Ha. lia.
    - unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, ASAN_CEIL in *. unfold d_obj. lia.
    - exact (pd_obj_ra cx W mem3 o Hsh HFB8 ltac:(lia) Hshb).
    - exact (pd_obj_hull cx W mem3 o Hsh HFB8 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Hc2 & HJ2 & HP & Hfr2 & Hperm & HK & HG & HL & Hok).
  assert (HC2 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly2 S2 W2 mem2 md2 k)
    by (split; [exact Hbase | split; [exact HJ2 | rewrite Hfr2; exact Hfrs]]).
  destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HC2)
    as (_ & _ & _ & _ & _ & _ & _ & _ & HFpres2 & HSpres2 & HWpres2 & _ & _ & _ & _).
  rewrite Hsp in HK.
  pose proof (pd_ikept_view cx h STK (dobj_size o) ly3 S3 W mem3 W2 mem2 (d_obj cx o) HK
    ltac:(unfold LLVMF_STK in *; lia) Hhi ltac:(unfold MFRAME in *; lia) Hfin Efa Hhin) as HV.
  assert (Hfp : forall a, pd_fp cx a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem3 a).
  { intros a Ha. apply HV.
    - unfold pd_fp, pd_dom in *. lia.
    - unfold pd_fp, d_obj, shadow_addr, in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, ASAN_CEIL, LLVMF_STK, MFRAME in *.
      lia. }
  unfold pd_at, d_at.
  exists fq, ly2, S2, regs2, mem2, md2, k, acc.
  split; [rewrite Hc2, Hra1; reflexivity|].
  split; [exact Hf0|]. split; [exact Hbase|]. split; [exact HJ2|]. split; [rewrite Hfr2; exact Hfrs|]. split; [exact Hk|].
  split; [pose proof HJ2 as (_ & _ & _ & _ & _ & _ & Hnev2 & _); lia|].
  split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|]. split; [exact Hcan0|].
  split; [exact (p_rC4_eq cx h regs regs2 (pd_cs_pres regs regs2 HP) HrC4)|].
  split.
  { apply (pd_frame_kept cx dsh_loop ps_C4 W W2 mem3 mem2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(unfold MFRAME, LLVMF_STK in *; lia) ltac:(unfold MFRAME in *; lia) Hhi ltac:(lia) ltac:(lia) Hframe Hfp).
    - intros a Ha. apply HWpres2. unfold LLVMF_STK, MFRAME in *. lia.
    - exact HFpres2.
    - exact HSpres2. }
  split; [exact (pd_blocks_kept cx h ly3 S3 ly2 S2 Hblocks Hperm)|].
  pose proof (Forall_inv Hdisj) as HdO. cbn [dobj_off dobj_size] in HdO.
  split.
  { apply (pd_garr8_kept W W2 mem3 mem2 _ _ Hour). intros a Ha. rewrite length_map, pd_our_len in Ha.
    apply HV; unfold pd_dom, d_obj in *; cbn [dobj_off] in *; lia. }
  constructor.
  - exact (pd_obj_new_of cx o V W2 mem2 Ho HL Hok HG).
  - apply (pd_objs_kept cx os W W2 mem3 mem2 Hobjs). intros o' a Ho' Ha.
    pose proof (proj1 (Forall_forall _ _) (Forall_inv_tail Hdisj) o' Ho') as Hd.
    pose proof (pd_obj_box o') as Hb'.
    apply HV; unfold pd_dom, d_objr, d_obj in *; lia.
Qed.

Hypothesis TTI : treac_disco_table_init_spec B.
Hypothesis TGI : treac_disco_gate_init_spec B.
Hypothesis TLI : treac_disco_peer_lock_init_spec B.

Lemma pd_s2 : forall cx h W c, pd_q1 cx h W c -> SRr SEGS W c (pd_q2 cx h).
Proof.
  intros cx h W c H.
  exact (pd_init_step _ _ OT _ RA_TI [] cx h W c (pd_ispec_ti TTI)
    ltac:(unfold REAC_DISCO_TABLE_INIT_STK, ESTACK; lia) ltac:(left; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(repeat apply Forall_cons; try apply Forall_nil; cbn [dobj_off dobj_size]; lia)
    ltac:(unfold RA_TI; lia) ltac:(reflexivity) H).
Qed.
Lemma pd_s4 : forall cx h W c, pd_q3 cx h W c -> SRr SEGS W c (pd_q4 cx h).
Proof.
  intros cx h W c H.
  exact (pd_init_step _ _ OG _ RA_GI [OT] cx h W c (pd_ispec_gi TGI)
    ltac:(unfold REAC_DISCO_GATE_INIT_STK, ESTACK; lia) ltac:(right; left; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(repeat apply Forall_cons; try apply Forall_nil; cbn [dobj_off dobj_size]; lia)
    ltac:(unfold RA_GI; lia) ltac:(reflexivity) H).
Qed.
Lemma pd_s6 : forall cx h W c, pd_q5 cx h W c -> SRr SEGS W c (pd_q6 cx h).
Proof.
  intros cx h W c H.
  exact (pd_init_step _ _ OLOCK _ RA_LI [OG; OT] cx h W c (pd_ispec_li TLI)
    ltac:(unfold REAC_DISCO_PEER_LOCK_INIT_STK, ESTACK; lia) ltac:(right; right; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(repeat apply Forall_cons; try apply Forall_nil; cbn [dobj_off dobj_size]; lia)
    ltac:(unfold RA_LI; lia) ltac:(reflexivity) H).
Qed.

Lemma pd_regupd8 : forall (regs : bvmap 5 word) (r : bv 5), r <> 8%bv -> getr (regupd regs 8 (Z_to_bv 64 0)) r = getr regs r.
Proof.
  intros regs r Hr. unfold getr. cbn. destruct (bv_eqb r 0); [reflexivity|].
  rewrite regupd_other; [reflexivity | intros X; apply Hr; exact X].
Qed.
Lemma pd_callZ : forall (fq : YK11.FPState) W (regsc : bvmap 5 word) memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k
  STK1 FP1 EV1 (o : Z) raw
  (K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
  spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  (afn_pre SEGS B STK1 lyc Sc W (regupd regsc 8 (Z_to_bv 64 0)) memc mdc [] ->
   SRr SEGS W (mkCfg (mkst (fx := fq) regsc pc memc (seg_rom SEGS)) mdc)
     (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 regs2 mem2 md2,
        c2 = mkCfg (mkst (fx := fx') regs2 raw mem2 (seg_rom SEGS)) md2 /\
        (forall r : bv 5, bv_unsigned r <> 10 -> Sem.reg_get (@YK11.fp_regs fx') r = Sem.reg_get (@YK11.fp_regs fq) r) /\
        (@YK11.fp_csr fx' = @YK11.fp_csr fq \/ Z.land (Z.shiftr (bv_unsigned (@YK11.fp_csr fx')) 5) 7 = 0) /\
        ajournal SEGS B STK1 (spZ regsc) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 /\
        aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2)) ->
  (forall a, inFP FP1 a -> inFP FP a \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regsc pc memc (seg_rom SEGS)) mdc)
    (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 regs2 mem2 md2,
       c2 = mkCfg (mkst (fx := fx') regs2 raw mem2 (seg_rom SEGS)) md2 /\
       (lib.Lib.FP.frm0 (@YK11.fp_csr fq) -> lib.Lib.FP.frm0 (@YK11.fp_csr fx')) /\
       ajournal SEGS B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + EV1) /\
       ajournal SEGS B STK1 (sp0 + o) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 /\
       aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2).
Proof.
  intros fq W regsc memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 o raw K
    HJ Hsp' Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hcallee HF.
  pose proof asan_consts as (C1 & _).
  assert (G1 : getr (regupd regsc 8 (Z_to_bv 64 0)) 1 = getr regsc 1) by (apply pd_regupd8; discriminate).
  assert (G2 : getr (regupd regsc 8 (Z_to_bv 64 0)) 2 = getr regsc 2) by (apply pd_regupd8; discriminate).
  assert (G3 : getr (regupd regsc 8 (Z_to_bv 64 0)) 3 = getr regsc 3) by (apply pd_regupd8; discriminate).
  assert (G4 : getr (regupd regsc 8 (Z_to_bv 64 0)) 4 = getr regsc 4) by (apply pd_regupd8; discriminate).
  assert (G8 : s0Z (regupd regsc 8 (Z_to_bv 64 0)) = 0).
  { unfold s0Z, getr. cbn. rewrite regupd_same. reflexivity. }
  assert (Usp : spZ (regupd regsc 8 (Z_to_bv 64 0)) = spZ regsc) by (unfold spZ; rewrite G2; reflexivity).
  eapply SRr_mono.
  { apply Hcallee.
    apply (afn_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k (regupd regsc 8 (Z_to_bv 64 0)) STK1 o []
      HJ ltac:(rewrite Usp; exact Hsp') Hal Hneg Hstk1 Hbud).
    - rewrite G1, Hra. exact Hraw.
    - unfold raZ. rewrite G1, Hra. exact Hra4.
    - rewrite G3. exact Hgp.
    - rewrite G4. exact Htp.
    - rewrite G8. left. split; [|reflexivity]. left. lia. }
  cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & regs2 & mem2 & md2 & -> & _ & Hcsr & HJ1 & HP & HK).
  exists fx', ly2, S2, regs2, mem2, md2. split; [reflexivity|]. rewrite Hsp' in HJ1.
  split; [unfold lib.Lib.FP.frm0; intros Hf; destruct Hcsr as [Ec | Ec]; [rewrite Ec; exact Hf | exact Ec]|].
  split; [| split; [exact HJ1 | split; [exact HP | exact HK]]].
  change own with ([] ++ own). eapply (ajournal_sub_tok SEGS B LAWS pa_segs_low); [exact HJ | exact HJ1 | lia | lia | exact HF].
Qed.

Lemma pd_s7 : forall cx h W c, pd_q6 cx h W c -> SRr SEGS W c (pd_q7 cx h).
Proof.
  intros cx h W c H.
  destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hf0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
    Hcan0 & HR & Hframe & Hblocks & Hour & HX).
  pose proof Hframe as (E & HdE & HRG & Hflag).
  assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
    by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
  destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HC)
    as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR3 & Hfin & Efa & Efl).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
  assert (HAr : 0 <= d_A cx < 2 ^ 64) by (unfold MFRAME, LLVMF_STK in *; lia).
  assert (HFr : 0 <= d_FB cx < 2 ^ 64) by lia.
  pose proof (pd_regs_ok cx E regs HdE (proj1 (proj1 HR)) HAr HFr) as HROK.
  pose proof (p_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx dsh_loop ps_C4 ly3 S3 W regs mem3 md3 k E RA_LI pd_sr
    (pd_vals regs) [] [] [] (d_facts [] []) HC HdE HRG Hflag HROK
    (d_facts_ok B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k E (pd_vals regs) [] [] HC HdE I I)
    (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity)) as HS.
  unfold ss_p in HS.
  assert (HEI : img_env VAL A_LIM (d_env cx E (pd_vals regs)))
    by (destruct HdE as (_ & _ & HI & _); intros a Ha; unfold d_env;
        rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia); exact (HI a Ha)).
  assert (EFB : ew (d_env cx E (pd_vals regs)) 516 = Z_to_bv 64 (d_FB cx))
    by (unfold d_env; rewrite ew_havoc_old by (cbv; lia); destruct HdE as (_ & _ & _ & _ & HF516 & _); exact HF516).
  assert (EA : ew (d_env cx E (pd_vals regs)) 60 = Z_to_bv 64 (d_A cx))
    by (unfold d_env; rewrite ew_havoc_old by (cbv; lia); destruct HdE as (_ & _ & _ & HA60 & _); exact HA60).
  assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (pd_vals regs)) (rd W mem3)) by constructor.
  pose (RUN := paj_run (fx := fq) B LAWS).
  unfold cfg_at. change (w64 (BASE + RA_LI)) with (Z_to_bv 64 (BASE + RA_LI)).
  pd_ro_base HS 516%nat. pd_ro_base HS 529%nat.
  paj_run_tok RUN HS HJ SHOK PDspan.
  { cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|].
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (d_A cx - d_S cx));
      [reflexivity | rewrite EA, unsigned_lit_small by lia; lia
      | cbn [YP09.r_wlo]; unfold LLVMF_STK, MFRAME in *; lia | cbn [YP09.r_whi]; unfold MFRAME in *; lia |].
    repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  rewrite (pa_sigma_reac_hunt_init (PI := PI)) in HS.
  lazymatch goal with
  | HF0 : frame_of _ _ mem3 (ms_mem ?ms0), HFr0 : frame_of _ ?rs0 (rd _ mem3) (rd _ (ms_mem ?ms0)), HG0 : mem_grows _ _
    |- SRr _ _ {| cfg_ms := ?ms0; cfg_model := ?md4 |} _ =>
    rename HFr0 into HFm; clear HF0 HG0; set (md5 := md4) in *;
    assert (HW60 : pd_wr60 rs0 = true) by (vm_compute; reflexivity)
  end.
  pose proof (st_ok_restrict_mkst SEGS (w_H W) _ _ ms HS eq_refl) as Hms. cbn [ss_pc setpc] in Hms.
  pose proof (pd_regs_same fq _ _ ms regs pd_cs (w_H W) HS HROK ltac:(vm_compute; reflexivity)) as RG.
  pose proof (st_ok_restrict_reg SEGS (w_H W) _ _ ms 1%bv HS) as R1.
  pose proof (st_ok_restrict_reg SEGS (w_H W) _ _ ms 10%bv HS) as R10.
  pose proof (st_ok_restrict_reg SEGS (w_H W) _ _ ms 11%bv HS) as R11.
  pose proof (st_ok_restrict_reg SEGS (w_H W) _ _ ms 12%bv HS) as R12.
  pd_rsr R1. pd_rsr R10. pd_rsr R11. pd_rsr R12.
  assert (E554 : ew (d_env cx E (pd_vals regs)) 554 = Z_to_bv 64 h).
  { change 554%nat with (AT_X + 23)%nat. rewrite (d_env_x cx E (pd_vals regs) 23 ltac:(cbn; lia)).
    cbn [pd_vals map seq nth Z.of_nat]. exact (proj2 HR). }
  lazymatch type of HS with st_ok _ ?Ex (setpc ?ssx _) ?msx =>
    assert (HSpi : st_ok_pi SEGS VAL Ex (setpc ssx AF_reac_hunt_init) msx) by exact HS;
    let r := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
    pose proof (st_ok_pi_region_nth Ex (setpc ssx AF_reac_hunt_init) msx 1 r HSpi ltac:(vm_compute; reflexivity)) as R60
  end.
  change (ms_mem (restrict (w_H W) ms)) with (rd W (ms_mem ms)) in R60.
  assert (HC' : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms) md5 k)
    by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
  destruct (p_land B MT XM_LIB RLO RHI tfib_K LAWS FFL fq cx dsh_loop ps_C4 ly3 S3 W md5 k (d_env cx E (pd_vals regs)) _ ms
    HC' (d_E_env cx E _ HdE) (d_env_fl cx E _) HSpi ltac:(vm_compute; reflexivity)) as [Hframe' _].
  assert (HV : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx <= a < d_A cx + 472) ->
    aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a).
  { intros a Ha Hn. apply (pd_aview_frame _ _ _ _ _ a HFm Ha). intros Hw.
    pose proof (pd_wr60_ok _ _ a HW60 Hw) as Hw'. cbn [base_val] in Hw'. rewrite EA, unsigned_lit_small in Hw' by lia.
    exact (Hn Hw'). }
  apply SRr_ret. unfold pd_q7, pd_at, d_at.
  exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md5, k, acc.
  split; [unfold cfg_at, w64; rewrite <- Hms; reflexivity|].
  split; [exact Hf0|]. split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
  split; [exact Hnev|]. split; [exact Hmo|]. split; [exact Hacc|]. split; [exact Hcan0|].
  split.
  { split; [exact (p_rC4_eq cx h regs _ RG HR)|].
    split; [rewrite R1; exact (codeptr_val _ RA_HI HEI)|].
    split; [rewrite R10; cbn [sv_denot]; rewrite E554, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
    split; [rewrite R11; cbn [sv_denot]; rewrite EFB, pd_w64_add; reflexivity|].
    rewrite R12. reflexivity. }
  split; [exact Hframe'|]. split; [exact Hblocks|].
  split.
  { apply (pd_garr8_kept W W mem3 (ms_mem ms) _ _ Hour). intros a Ha. rewrite length_map, pd_our_len in Ha.
    apply HV; unfold d_obj, dobj_off, LLVMF_STK, MFRAME in *; lia. }
  split.
  { apply (pd_objs_kept cx _ W W mem3 (ms_mem ms) HX). intros o' a Ho' Ha. pose proof (pd_obj_box o') as Hb'.
    apply HV; unfold d_objr, d_obj, LLVMF_STK, MFRAME in *; lia. }
  unfold pd_v216.
  assert (Hhin : In (h, HUNT_SIZE) (ablocks B ly3 S3))
    by (destruct Hblocks as (HPm & _); apply (Permutation_in _ (Permutation_sym HPm)); left; reflexivity).
  assert (Hh64 : 0 <= h < 2 ^ 64).
  { destruct ((al_blocks _ _ LAWS) ly3 S3 W mem3 md3 h HUNT_SIZE HAR3 Hhin) as (_ & Hp4096 & Hbceil & _).
    unfold req_size, HUNT_SIZE in Hbceil. cbn in Hbceil. lia. }
  exact (field_of_region _ _ 60%nat (d_A cx) _ 0 472 0 472 216 8%N (SOff 554 0) h R60
    ltac:(rewrite EA; apply unsigned_lit_small; lia) ltac:(left; reflexivity)
    ltac:(cbn [sv_denot]; rewrite E554, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
    ltac:(cbn [Z.of_N]; change (8 * 8) with 64; lia) ltac:(cbn; lia)).
Qed.

Hypothesis THI : treac_hunt_init_spec B.

Lemma pd_hbytes : forall (ob : list byte) now, length ob = 6%nat ->
  length (reac_hunt_init_c.hunt_init_bytes ob now) = 480%nat /\
  firstn 6 (skipn 412 (reac_hunt_init_c.hunt_init_bytes ob now)) = ob.
Proof.
  intros ob now Hob.
  assert (Hr : length (repeat (Z_to_bv 8 0) 412) = 412%nat) by apply repeat_length.
  split.
  - unfold reac_hunt_init_c.hunt_init_bytes. rewrite !length_app, !repeat_length, Hob, Mem.length_le8. reflexivity.
  - assert (Hsk : skipn 412 (reac_hunt_init_c.hunt_init_bytes ob now)
      = ob ++ repeat (Z_to_bv 8 0) 6 ++ Mem.le8 (Z_to_bv 64 now) ++ repeat (Z_to_bv 8 0) 48).
    { unfold reac_hunt_init_c.hunt_init_bytes.
      rewrite skipn_app, Hr, Nat.sub_diag, skipn_all2 by (rewrite Hr; lia). reflexivity. }
    rewrite Hsk, firstn_app, Hob, Nat.sub_diag, firstn_all2 by lia.
    cbn [firstn]. rewrite app_nil_r. reflexivity.
Qed.

Lemma pd_s8 : forall cx h W c, pd_q7 cx h W c -> SRr SEGS W c (pd_q8 cx h).
Proof.
  intros cx h W c H.
  destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hf0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
    Hcan0 & (HrC4 & Hra1 & H10 & H11 & H12) & Hframe & Hblocks & Hour & Hobjs & Hv216).
  pose proof Hframe as (E & HdE & HRG & Hflag).
  assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
    by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
  destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HC)
    as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR3 & Hfin & Efa & Efl).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
  pose proof (proj1 (proj1 HrC4)) as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H22 & H24 & H25 & H26).
  pose proof pa_B_ok as (HB0 & HB1 & _). pose proof pa_base_lo as HBlo.
  assert (Hhin : In (h, HUNT_SIZE) (ablocks B ly3 S3))
    by (destruct Hblocks as (HPm & _); apply (Permutation_in _ (Permutation_sym HPm)); left; reflexivity).
  destruct ((al_blocks _ _ LAWS) ly3 S3 W mem3 md3 h HUNT_SIZE HAR3 Hhin) as (Hh16 & Hh4096 & Hhceil & Hhapp & _).
  replace (req_size HUNT_SIZE) with 480 in Hhceil by (vm_compute; reflexivity).
  assert (HFB8 : d_FB cx mod 8 = 0) by lia.
  assert (Hoob : (d_obj cx OOUR =? 0) = false) by (apply Z.eqb_neq; unfold d_obj; cbn [dobj_off]; lia).
  assert (Hpstk : REAC_HUNT_INIT_STK = 4160) by (vm_compute; reflexivity).
  assert (Hdshadow : d_shadow cx dsh_loop W mem3) by (apply (pd_dshadow cx ps_C4); [lia | lia | exact Hframe]).
  assert (Hraw_ok : YK0s.ret_ok (getr regs 1)) by (rewrite Hra1; apply ret_ok_codeptr_v; [unfold RA_HI; lia | reflexivity]).
  assert (Hraw4 : 4096 <= bv_unsigned (getr regs 1))
    by (rewrite Hra1; unfold w64, RA_HI; rewrite unsigned_lit_small by lia; unfold IMG_LO in HBlo; lia).
  unfold cfg_at.
  eapply SRr_mono.
  { eapply (pd_callZ fq W regs mem3 (w64 (BASE + AF_reac_hunt_init)) LLVMF_STK (d_S cx) (@nil (Z * Z)) (c_ly cx) (c_S cx)
      (c_W cx) (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)] ly3 S3 md3 k REAC_HUNT_INIT_STK [(h, h + 480)] 0
      (d_A cx - d_S cx) (getr regs 1) _ HJ).
    - rewrite Hsp. lia.
    - lia.
    - unfold MFRAME in *. lia.
    - rewrite Hpstk. lia.
    - rewrite Hpstk. unfold LLVMF_STK, MFRAME in *. lia.
    - exact Hgp.
    - exact Htp.
    - reflexivity.
    - exact Hraw_ok.
    - exact Hraw4.
    - intro Hpre.
      eapply SRr_mono.
      { apply (THI fq ly3 S3 W regs mem3 md3 [] h (d_obj cx OOUR) NOW0 h HUNT_SIZE (our_of (c_pl cx)) Hpre H10 H11 H12).
        - unfold d_obj; cbn [dobj_off]; lia.
        - unfold NOW0. lia.
        - lia.
        - lia.
        - exact Hhin.
        - lia.
        - unfold req_size, HUNT_SIZE. cbn. lia.
        - intros _. split; [|split; [apply pd_our_len | exact Hour]].
          unfold afobj. split.
          + exists DFRAME_CLASS, (c_fpos cx). split; [exact Hfin|]. split; [unfold DFRAME_CLASS; lia|].
            split; [rewrite Efa; lia|]. split; [unfold d_obj; cbn [dobj_off]; lia|].
            rewrite Efa. change (fs_frame_bytes DFRAME_CLASS) with 4096. unfold d_obj; cbn [dobj_off]; lia.
          + split; [unfold d_obj; cbn [dobj_off]; lia|].
            exact (pd_obj_ra cx W mem3 OOUR Hdshadow HFB8 ltac:(lia) ltac:(vm_compute; reflexivity)). }
      cbv beta. intros W2 c2 _ Hp. unfold treac_hunt_init_post, apost_base in Hp. exact Hp.
    - intros a HaFP. right. apply inFP_cons in HaFP as [Ha | Ha]; [|destruct (inFP_nil _ Ha)].
      exists h, HUNT_SIZE. split; [exact Hhin|]. split.
      + destruct Hblocks as (_ & HnF & _). exact (Forall_inv HnF).
      + unfold req_size, HUNT_SIZE in *. cbn. lia. }
  cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & regs2 & mem2 & md2 & -> & Hf0' & HJouter & HJcallee & HP & HK).
  rewrite Hoob in HK. destruct HK as (Hgarr & Hhok & Hperm).
  pose proof HJouter as (_ & _ & _ & _ & _ & Hfr2 & Hnev2 & _).
  pose proof HJcallee as (_ & _ & _ & _ & _ & Hfrc & _).
  assert (Hfrs2 : frames S2 = [(DFRAME_CLASS, c_fpos cx)]) by (rewrite Hfrc; cbn [app]; exact Hfrs).
  assert (HC2 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly2 S2 W2 mem2 md2 k)
    by (split; [exact Hbase | split; [rewrite Z.add_0_r in HJouter; exact HJouter | exact Hfrs2]]).
  destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HC2)
    as (_ & _ & _ & _ & _ & _ & _ & _ & HFpres2 & HSpres2 & HWpres2 & _ & _ & _ & _).
  assert (Hh2 : In (h, HUNT_SIZE) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hhin).
  assert (Hsep : h + HUNT_SIZE <= d_FB cx \/ d_FB cx + 4096 <= h).
  { pose proof (sep_block_frame SEGS B LAWS ly3 S3 W mem3 md3 h HUNT_SIZE DFRAME_CLASS (c_fpos cx) HAR3 Hhin Hfin) as Hd.
    unfold zdisjoint in Hd. rewrite Efa in Hd. cbn [fst snd] in Hd.
    replace (req_size HUNT_SIZE) with 480 in Hd by (vm_compute; reflexivity).
    change (fs_frame_bytes DFRAME_CLASS) with 4096 in Hd. unfold HUNT_SIZE. lia. }
  replace (d_S cx + (d_A cx - d_S cx)) with (d_A cx) in HJcallee by lia.
  assert (HV : forall a, pd_dom cx h a -> ~ (h <= a < h + HUNT_SIZE) ->
    aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem3 a).
  { intros a Ha Hx. apply (pd_aj_view cx h REAC_HUNT_INIT_STK [(h, h + 480)] ly3 S3 W mem3 md3 ly2 S2 W2 mem2 md2 0
      HJcallee ltac:(unfold LLVMF_STK in *; lia) Hhi ltac:(unfold MFRAME in *; lia) Hfin Efa Hhin Hh2 a Ha).
    intros HaFP. apply inFP_cons in HaFP as [Hc | Hc]; [|destruct (inFP_nil _ Hc)]. unfold HUNT_SIZE in *. lia. }
  assert (Hfp : forall a, pd_fp cx a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem3 a).
  { intros a Ha. apply HV.
    - unfold pd_fp, pd_dom in *. lia.
    - assert (Hd0 : 0 <= d_FB cx / 8) by (apply Z.div_pos; lia).
      assert (Hd1 : d_FB cx / 8 <= 17592184995840) by (apply Z.div_le_upper_bound; lia).
      unfold in_app in Hhapp. destruct Hhapp as (_ & Happ).
      replace (req_size HUNT_SIZE) with 480 in Happ by (vm_compute; reflexivity).
      rewrite C3 in Happ.
      unfold pd_fp, shadow_addr, SHADOW_OFF, HUNT_SIZE, MFRAME, LLVMF_STK, ASAN_CEIL, kLowShadowBeg in *.
      destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]];
        [ lia | lia | destruct Hsep; lia | destruct Hsep; lia | destruct Happ as [Hlow|[Hhigh _]]; lia ]. }
  unfold pd_q8, pd_at, d_at.
  exists fx', ly2, S2, regs2, mem2, md2, k, acc.
  split; [rewrite Hra1; reflexivity|].
  split; [exact (Hf0' Hf0)|]. split; [exact Hbase|]. split; [rewrite Z.add_0_r in HJouter; exact HJouter|]. split; [exact Hfrs2|].
  split; [exact Hk|]. split; [rewrite Z.add_0_r in Hnev2; lia|]. split; [rewrite MT_TRIV; exact I|].
  split; [exact Hacc|]. split; [exact Hcan0|].
  split; [exact (p_rC4_eq cx h regs regs2 (pd_cs_pres regs regs2 HP) HrC4)|].
  split.
  { apply (pd_frame_kept cx dsh_loop ps_C4 W W2 mem3 mem2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(unfold MFRAME, LLVMF_STK in *; lia) ltac:(unfold MFRAME in *; lia) Hhi ltac:(lia) ltac:(lia) Hframe Hfp).
    - intros a Ha. apply HWpres2. unfold LLVMF_STK, MFRAME in *. lia.
    - exact HFpres2.
    - exact HSpres2. }
  split; [exact (pd_blocks_kept cx h ly3 S3 ly2 S2 Hblocks Hperm)|].
  split.
  { apply (pd_garr8_kept W W2 mem3 mem2 _ _ Hour). intros a Ha. rewrite length_map, pd_our_len in Ha.
    apply HV; unfold pd_dom, d_obj, dobj_off, HUNT_SIZE in *; lia. }
  split.
  { apply (pd_objs_kept cx _ W W2 mem3 mem2 Hobjs). intros o' a Ho' Ha. pose proof (pd_obj_box o') as Hb'.
    apply HV; unfold pd_dom, d_objr, d_obj, HUNT_SIZE in *; lia. }
  split.
  { unfold pd_v216. apply (pd_val_mem_kept W W2 mem3 mem2 _ _ _ Hv216). intros a Ha.
    apply HV; unfold pd_dom, HUNT_SIZE, MFRAME, LLVMF_STK in *; lia. }
  destruct (pd_hbytes (our_of (c_pl cx)) NOW0 (pd_our_len (c_pl cx))) as (HLb & HFb).
  exists (reac_hunt_init_c.hunt_init_bytes (our_of (c_pl cx)) NOW0).
  split; [exact HLb|]. split; [exact Hgarr|]. split; [exact Hhok | exact HFb].
Qed.

Lemma pd_nth_firstn : forall (l : list byte) a j d, (j < a)%nat -> nth j (firstn a l) d = nth j l d.
Proof.
  induction l as [|x l IH]; intros a j d Hj; (destruct a as [|a]; [lia|]); cbn [firstn].
  - destruct j; reflexivity.
  - destruct j as [|j]; [reflexivity | cbn [nth]; apply IH; lia].
Qed.
Lemma pd_nth_skipn : forall (l : list byte) c j d, nth j (skipn c l) d = nth (c + j) l d.
Proof.
  induction l as [|x l IH]; intros c j d; destruct c as [|c]; cbn [skipn].
  - reflexivity.
  - destruct j; reflexivity.
  - reflexivity.
  - cbn [Nat.add nth]. apply IH.
Qed.
Definition pd_splice (H P : list byte) (a : nat) : list byte :=
  firstn a H ++ P ++ skipn (a + length P) H.
Lemma pd_splice_len : forall H P a, (a + length P <= length H)%nat -> length (pd_splice H P a) = length H.
Proof.
  intros H P a Ha. unfold pd_splice. rewrite !length_app, length_firstn, length_skipn.
  rewrite Nat.min_l by lia. lia.
Qed.
Lemma pd_splice_nth : forall H P a j d, (a + length P <= length H)%nat -> (j < length H)%nat ->
  nth j (pd_splice H P a) d =
    (if (j <? a)%nat then nth j H d else if (j <? a + length P)%nat then nth (j - a) P d else nth j H d).
Proof.
  intros H P a j d Ha Hj. unfold pd_splice.
  assert (Hfl : length (firstn a H) = a) by (rewrite length_firstn; lia).
  destruct (Nat.ltb_spec j a) as [Hja|Hja].
  - rewrite app_nth1 by lia. apply pd_nth_firstn; lia.
  - rewrite app_nth2 by lia. rewrite Hfl.
    destruct (Nat.ltb_spec j (a + length P)) as [Hjp|Hjp].
    + rewrite app_nth1 by lia. reflexivity.
    + rewrite app_nth2 by lia. rewrite pd_nth_skipn. f_equal. lia.
Qed.
Lemma pd_splice_firstn : forall H P a k, (a + length P <= length H)%nat -> (k <= a)%nat ->
  firstn k (pd_splice H P a) = firstn k H.
Proof.
  intros H P a k Ha Hk. apply nth_ext with (d := Z_to_bv 8 0) (d' := Z_to_bv 8 0).
  - rewrite !length_firstn, pd_splice_len by lia. reflexivity.
  - intros j Hjlen. rewrite length_firstn, pd_splice_len in Hjlen by lia.
    rewrite Nat.min_glb_lt_iff in Hjlen. destruct Hjlen as (Hjk & Hjl).
    rewrite !pd_nth_firstn by lia. rewrite pd_splice_nth by lia.
    destruct (Nat.ltb_spec j a); [reflexivity | lia].
Qed.
Lemma pd_splice_skipn : forall H P a c, (a + length P <= length H)%nat -> (a + length P <= c)%nat ->
  skipn c (pd_splice H P a) = skipn c H.
Proof.
  intros H P a c Ha Hc. apply nth_ext with (d := Z_to_bv 8 0) (d' := Z_to_bv 8 0).
  - rewrite !length_skipn, pd_splice_len by lia. reflexivity.
  - intros j Hjlen. rewrite length_skipn, pd_splice_len in Hjlen by lia.
    rewrite !pd_nth_skipn. rewrite pd_splice_nth by lia.
    destruct (Nat.ltb_spec (c + j) a); [lia|]. destruct (Nat.ltb_spec (c + j) (a + length P)); [lia | reflexivity].
Qed.
Lemma pd_splice_fs : forall H P a k n, (a + length P <= length H)%nat -> (k + n <= a)%nat ->
  firstn n (skipn k (pd_splice H P a)) = firstn n (skipn k H).
Proof.
  intros H P a k n Ha Hk. apply nth_ext with (d := Z_to_bv 8 0) (d' := Z_to_bv 8 0).
  - rewrite !length_firstn, !length_skipn, pd_splice_len by lia. reflexivity.
  - intros j Hjlen. rewrite length_firstn, length_skipn, pd_splice_len in Hjlen by lia.
    rewrite Nat.min_glb_lt_iff in Hjlen. destruct Hjlen as (Hjn & Hjl).
    rewrite !pd_nth_firstn by lia. rewrite !pd_nth_skipn. rewrite pd_splice_nth by lia.
    destruct (Nat.ltb_spec (k + j) a); [reflexivity | lia].
Qed.
Lemma pd_hpatch : forall cx h (W W' : world SEGS) m m' (off : Z) (P : list byte),
  d_h_new cx h W m ->
  418 <= off -> off + Z.of_nat (length P) <= 440 ->
  (forall a, h <= a < h + HUNT_SIZE -> (a < h + off \/ h + off + Z.of_nat (length P) <= a) ->
     aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  garr8 SEGS (rd W' m') (h + off) (map (fun b : byte => bv_unsigned b) P) ->
  d_h_new cx h W' m'.
Proof.
  intros cx h W W' m m' off P (H & HL & HG & Hok & Hour) Hoff1 Hoff2 Hkeep Hpatch.
  set (a := Z.to_nat off).
  assert (HaP : (a + length P <= length H)%nat) by (unfold a; rewrite HL; lia).
  assert (Hoffa : Z.of_nat a = off) by (unfold a; rewrite Z2Nat.id; lia).
  exists (pd_splice H P a). split; [rewrite pd_splice_len by exact HaP; exact HL|].
  split.
  { intros j Hj. rewrite length_map, pd_splice_len in Hj by exact HaP. rewrite HL in Hj.
    rewrite (pd_nth_map_bv _ j ltac:(rewrite pd_splice_len by exact HaP; rewrite HL; lia)).
    rewrite pd_splice_nth by (try exact HaP; rewrite HL; lia).
    destruct (Nat.ltb_spec j a) as [Hja|Hja].
    - split; [|apply bv_unsigned_in_range].
      pose proof (HG j ltac:(rewrite length_map, HL; lia)) as (Hvm & _).
      rewrite (pd_nth_map_bv _ j ltac:(rewrite HL; lia)) in Hvm.
      apply (pd_val_mem_kept W W' m m' (h + Z.of_nat j) 1 _ Hvm). intros b Hb.
      apply Hkeep; [unfold HUNT_SIZE in *; lia | left; lia].
    - destruct (Nat.ltb_spec j (a + length P)) as [Hjp|Hjp].
      + pose proof (Hpatch (j - a)%nat ltac:(rewrite length_map; lia)) as (Hvm & _).
        rewrite (pd_nth_map_bv P (j - a)%nat ltac:(lia)) in Hvm.
        assert (Haddr : h + off + Z.of_nat (j - a)%nat = h + Z.of_nat j)
          by (rewrite <- Hoffa; rewrite Nat2Z.inj_sub by lia; lia).
        rewrite Haddr in Hvm.
        split; [exact Hvm | apply bv_unsigned_in_range].
      + split; [|apply bv_unsigned_in_range].
        pose proof (HG j ltac:(rewrite length_map, HL; lia)) as (Hvm & _).
        rewrite (pd_nth_map_bv _ j ltac:(rewrite HL; lia)) in Hvm.
        apply (pd_val_mem_kept W W' m m' (h + Z.of_nat j) 1 _ Hvm). intros b Hb.
        apply Hkeep; [unfold HUNT_SIZE in *; lia | right; lia]. }
  split.
  - unfold hunt_c.hunt_ok in Hok |- *. destruct Hok as (HokL & HokT & HokLk & HokS).
    split; [rewrite pd_splice_len by exact HaP; exact HL|].
    split; [rewrite pd_splice_firstn by (unfold a; (try exact HaP); rewrite HL in *; lia); exact HokT|].
    split.
    + rewrite (pd_splice_fs H P a 400 12) by (unfold a; (try exact HaP); rewrite HL in *; lia). exact HokLk.
    + replace (disco_table_c.s32_at (pd_splice H P a) 440) with (disco_table_c.s32_at H 440); [exact HokS|].
      unfold disco_table_c.s32_at, disco_table_c.u_at, disco_table_c.sub. change (Z.to_nat 440) with 440%nat.
      rewrite (pd_splice_skipn H P a 440) by (unfold a; (try exact HaP); rewrite HL in *; lia). reflexivity.
  - rewrite (pd_splice_fs H P a 412 6) by (unfold a; (try exact HaP); rewrite HL in *; lia). exact Hour.
Qed.

Lemma pd_hsep : forall cx h,
  alloc_ceiling + LLVMF_STK <= d_S cx -> d_S cx - MFRAME - 31 <= d_A cx ->
  d_FB cx + 4096 <= alloc_ceiling -> 4096 <= d_FB cx -> h + 480 <= alloc_ceiling ->
  (h + 480 <= kLowShadowBeg \/ kHighMemBeg <= h) ->
  (h + HUNT_SIZE <= d_FB cx \/ d_FB cx + 4096 <= h) -> alloc_ceiling <= 140737479966720 ->
  forall a, pd_fp cx a \/ (d_FB cx <= a < d_FB cx + 4096) \/ (d_A cx <= a < d_A cx + 472) -> ~ (h <= a < h + 480).
Proof.
  intros cx h Hlo HA HFc HF0 Hhc Happ Hsep Hcl a Ha.
  pose proof asan_consts as (_ & _ & C3 & _ & _).
  assert (Hd0 : 0 <= d_FB cx / 8) by (apply Z.div_pos; lia).
  assert (Hd1 : d_FB cx / 8 <= 17592184995840) by (apply Z.div_le_upper_bound; lia).
  rewrite C3 in Happ.
  unfold pd_fp, shadow_addr, SHADOW_OFF, HUNT_SIZE, MFRAME, LLVMF_STK, kLowShadowBeg in *.
  destruct Ha as [[Ha|[Ha|[Ha|[Ha|Ha]]]] | [Ha | Ha]];
    first [lia | destruct Hsep; lia | destruct Happ; lia].
Qed.

Hypothesis THP : treac_hunt_pin_spec B.

Lemma pd_s10 : forall cx h W c, pd_q9 cx h W c -> SRr SEGS W c (pd_q10 cx h).
Proof.
  intros cx h W c H.
  destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hf0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
    Hcan0 & (HrC4 & Hra1 & H10) & Hframe & Hblocks & Hour & (Hobjs & Hv216 & Hhnew)).
  assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
    by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
  destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HC)
    as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR3 & Hfin & Efa & Efl).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
  pose proof (proj1 (proj1 HrC4)) as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H22 & H24 & H25 & H26).
  pose proof pa_B_ok as (HB0 & HB1 & _). pose proof pa_base_lo as HBlo.
  assert (Hhin : In (h, HUNT_SIZE) (ablocks B ly3 S3))
    by (destruct Hblocks as (HPm & _); apply (Permutation_in _ (Permutation_sym HPm)); left; reflexivity).
  destruct ((al_blocks _ _ LAWS) ly3 S3 W mem3 md3 h HUNT_SIZE HAR3 Hhin) as (Hh16 & Hh4096 & Hhceil & Hhapp & _).
  replace (req_size HUNT_SIZE) with 480 in Hhceil, Hhapp by (vm_compute; reflexivity).
  assert (Happ : h + 480 <= kLowShadowBeg \/ kHighMemBeg <= h)
    by (unfold in_app in Hhapp; destruct Hhapp as (_ & [Hl | [Hh _]]); [left | right]; lia).
  assert (Hsep : h + HUNT_SIZE <= d_FB cx \/ d_FB cx + 4096 <= h).
  { pose proof (sep_block_frame SEGS B LAWS ly3 S3 W mem3 md3 h HUNT_SIZE DFRAME_CLASS (c_fpos cx) HAR3 Hhin Hfin) as Hd.
    unfold zdisjoint in Hd. rewrite Efa in Hd. cbn [fst snd] in Hd.
    replace (req_size HUNT_SIZE) with 480 in Hd by (vm_compute; reflexivity).
    change (fs_frame_bytes DFRAME_CLASS) with 4096 in Hd. unfold HUNT_SIZE. lia. }
  pose proof (pd_hsep cx h Hlo (proj1 HA1) HFc HF0 Hhceil Happ Hsep ltac:(lia)) as Hout.
  assert (Hpstk : REAC_HUNT_PIN_STK = 4112) by (vm_compute; reflexivity).
  assert (Hraw_ok : YK0s.ret_ok (getr regs 1)) by (rewrite Hra1; apply ret_ok_codeptr_v; [unfold RA_PIN; lia | reflexivity]).
  assert (Hraw4 : 4096 <= bv_unsigned (getr regs 1))
    by (rewrite Hra1; unfold w64, RA_PIN; rewrite unsigned_lit_small by lia; unfold IMG_LO in HBlo; lia).
  unfold cfg_at.
  eapply SRr_mono.
  { eapply (pd_callZ fq W regs mem3 (w64 (BASE + AF_reac_hunt_pin)) LLVMF_STK (d_S cx) (@nil (Z * Z)) (c_ly cx) (c_S cx)
      (c_W cx) (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)] ly3 S3 md3 k REAC_HUNT_PIN_STK [(h + 432, h + 440)] 0
      (d_A cx - d_S cx) (getr regs 1) _ HJ).
    - rewrite Hsp. lia.
    - lia.
    - unfold MFRAME in *. lia.
    - rewrite Hpstk. lia.
    - rewrite Hpstk. unfold LLVMF_STK, MFRAME in *. lia.
    - exact Hgp.
    - exact Htp.
    - reflexivity.
    - exact Hraw_ok.
    - exact Hraw4.
    - intro Hpre. eapply SRr_mono.
      { apply (THP fq ly3 S3 W regs mem3 md3 [] h h HUNT_SIZE Hpre H10).
        - lia.
        - lia.
        - exact Hhin.
        - lia.
        - unfold req_size, HUNT_SIZE. cbn. lia. }
      cbv beta. intros W2 c2 _ Hp. unfold treac_hunt_pin_post, apost_base in Hp. exact Hp.
    - intros a HaFP. right. apply inFP_cons in HaFP as [Ha | Ha]; [|destruct (inFP_nil _ Ha)].
      exists h, HUNT_SIZE. split; [exact Hhin|]. split.
      + destruct Hblocks as (_ & HnF & _). exact (Forall_inv HnF).
      + unfold req_size, HUNT_SIZE in *. cbn. cbn [fst snd] in Ha. lia. }
  cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & regs2 & mem2 & md2 & -> & Hf0' & HJouter & HJcallee & HP & HK).
  destruct HK as (Hgarr & Hperm).
  pose proof HJouter as (_ & _ & _ & _ & _ & Hfr2 & Hnev2 & _).
  pose proof HJcallee as (_ & _ & _ & _ & _ & Hfrc & _).
  assert (Hfrs2 : frames S2 = [(DFRAME_CLASS, c_fpos cx)]) by (rewrite Hfrc; cbn [app]; exact Hfrs).
  assert (HC2 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly2 S2 W2 mem2 md2 k)
    by (split; [exact Hbase | split; [rewrite Z.add_0_r in HJouter; exact HJouter | exact Hfrs2]]).
  destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HC2)
    as (_ & _ & _ & _ & _ & _ & _ & _ & HFpres2 & HSpres2 & HWpres2 & _ & _ & _ & _).
  assert (Hh2 : In (h, HUNT_SIZE) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hhin).
  replace (d_S cx + (d_A cx - d_S cx)) with (d_A cx) in HJcallee by lia.
  assert (HnFP : forall a, ~ (h <= a < h + 480) -> ~ inFP [(h + 432, h + 440)] a).
  { intros a Ha HaFP. apply inFP_cons in HaFP as [Hc | Hc]; [cbn [fst snd] in Hc; lia | destruct (inFP_nil _ Hc)]. }
  assert (HVfp : forall a, pd_dom cx h a -> ~ inFP [(h + 432, h + 440)] a ->
    aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem3 a)
    by (intros a Ha Hx; exact (pd_aj_view cx h REAC_HUNT_PIN_STK [(h + 432, h + 440)] ly3 S3 W mem3 md3 ly2 S2 W2 mem2 md2 0
      HJcallee ltac:(unfold LLVMF_STK in *; lia) Hhi ltac:(unfold MFRAME in *; lia) Hfin Efa Hhin Hh2 a Ha Hx)).
  assert (Hfp : forall a, pd_fp cx a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem3 a).
  { intros a Ha. apply HVfp; [unfold pd_fp, pd_dom in *; lia | apply HnFP; apply Hout; left; exact Ha]. }
  unfold pd_q10, pd_at, d_at.
  exists fx', ly2, S2, regs2, mem2, md2, k, acc.
  split; [rewrite Hra1; reflexivity|].
  split; [exact (Hf0' Hf0)|]. split; [exact Hbase|]. split; [rewrite Z.add_0_r in HJouter; exact HJouter|]. split; [exact Hfrs2|].
  split; [exact Hk|]. split; [rewrite Z.add_0_r in Hnev2; lia|]. split; [rewrite MT_TRIV; exact I|].
  split; [exact Hacc|]. split; [exact Hcan0|].
  split; [exact (p_rC4_eq cx h regs regs2 (pd_cs_pres regs regs2 HP) HrC4)|].
  split.
  { apply (pd_frame_kept cx dsh_loop ps_C4 W W2 mem3 mem2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(unfold MFRAME, LLVMF_STK in *; lia) ltac:(unfold MFRAME in *; lia) Hhi ltac:(lia) ltac:(lia) Hframe Hfp).
    - intros a Ha. apply HWpres2. unfold LLVMF_STK, MFRAME in *. lia.
    - exact HFpres2.
    - exact HSpres2. }
  split; [exact (pd_blocks_kept cx h ly3 S3 ly2 S2 Hblocks Hperm)|].
  split.
  { apply (pd_garr8_kept W W2 mem3 mem2 _ _ Hour). intros a Ha. rewrite length_map, pd_our_len in Ha.
    apply HVfp; [unfold pd_dom, d_obj, dobj_off in *; lia
      | apply HnFP; apply Hout; right; left; unfold d_obj, dobj_off in *; lia]. }
  split.
  { apply (pd_objs_kept cx _ W W2 mem3 mem2 Hobjs). intros o' a Ho' Ha. pose proof (pd_obj_box o') as Hb'.
    apply HVfp; [unfold pd_dom, d_objr, d_obj in *; lia
      | apply HnFP; apply Hout; right; left; unfold d_objr, d_obj in *; lia]. }
  split.
  { unfold pd_v216. apply (pd_val_mem_kept W W2 mem3 mem2 _ _ _ Hv216). intros a Ha.
    apply HVfp; [unfold pd_dom in *; lia | apply HnFP; apply Hout; right; right; lia]. }
  apply (pd_hpatch cx h W W2 mem3 mem2 432 (Mem.le4 (Z_to_bv 64 1) ++ Mem.le4 (getr regs 11)) Hhnew).
  - lia.
  - rewrite length_app, !Mem.length_le4. cbn. lia.
  - intros a Ha Hx. apply HVfp; [unfold pd_dom; right; right; right; right; exact Ha|].
    intros HaFP. apply inFP_cons in HaFP as [Hc | Hc]; [cbn [fst snd] in Hc|destruct (inFP_nil _ Hc)].
    rewrite length_app, !Mem.length_le4 in Hx. cbn in Hx. lia.
  - exact Hgarr.
Qed.

Lemma pd_objs_of : forall cx h (W : world SEGS) m, pd_X8 cx h W m ->
  garr8 SEGS (rd W m) (d_obj cx OOUR) (map (fun b : byte => bv_unsigned b) (our_of (c_pl cx))) ->
  exists T G Lk H : list byte, d_objs cx h T G Lk H W m.
Proof.
  intros cx h W m (Hobjs & _ & (H & HhL & HhG & Hhok & Hhour)) Hour.
  pose proof (Forall_inv Hobjs) as HLk. apply Forall_inv_tail in Hobjs.
  pose proof (Forall_inv Hobjs) as HG. apply Forall_inv_tail in Hobjs.
  pose proof (Forall_inv Hobjs) as HT.
  cbn [d_obj_new] in HLk, HG, HT.
  destruct HT as (T & HTl & HTg & HTok). destruct HG as (Gt & HGl & HGg & HGok).
  destruct HLk as (Lk & HLl & HLg & HLok).
  exists T, Gt, Lk, H. unfold d_objs.
  split; [exact HTl|]. split; [exact HTg|]. split; [exact HTok|].
  split; [exact HGl|]. split; [exact HGg|]. split; [exact HGok|].
  split; [exact HLl|]. split; [exact HLg|]. split; [exact HLok|].
  split; [exact Hour|]. split; [exact HhL|]. split; [exact HhG|]. split; [exact Hhok | exact Hhour].
Qed.

Hypothesis THS : treac_hunt_silence_proven_spec B.

Lemma pd_s12 : forall cx h W c, pd_q11 cx h W c -> SRr SEGS W c (pro_C5 B MT XM_LIB RLO RHI tfib_K cx h).
Proof.
  intros cx h W c H.
  destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hf0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
    Hcan0 & (HrC5 & Hra1 & H10) & Hframe & Hblocks & Hour & (Hobjs & Hv216 & Hhnew)).
  assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
    by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
  destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HC)
    as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR3 & Hfin & Efa & Efl).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
  pose proof (proj1 HrC5) as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H22 & H24 & H25 & H26).
  pose proof pa_B_ok as (HB0 & HB1 & _). pose proof pa_base_lo as HBlo.
  assert (Hhin : In (h, HUNT_SIZE) (ablocks B ly3 S3))
    by (destruct Hblocks as (HPm & _); apply (Permutation_in _ (Permutation_sym HPm)); left; reflexivity).
  destruct ((al_blocks _ _ LAWS) ly3 S3 W mem3 md3 h HUNT_SIZE HAR3 Hhin) as (Hh16 & Hh4096 & Hhceil & Hhapp & _).
  replace (req_size HUNT_SIZE) with 480 in Hhceil, Hhapp by (vm_compute; reflexivity).
  assert (Happ : h + 480 <= kLowShadowBeg \/ kHighMemBeg <= h)
    by (unfold in_app in Hhapp; destruct Hhapp as (_ & [Hl | [Hh _]]); [left | right]; lia).
  assert (Hsep : h + HUNT_SIZE <= d_FB cx \/ d_FB cx + 4096 <= h).
  { pose proof (sep_block_frame SEGS B LAWS ly3 S3 W mem3 md3 h HUNT_SIZE DFRAME_CLASS (c_fpos cx) HAR3 Hhin Hfin) as Hd.
    unfold zdisjoint in Hd. rewrite Efa in Hd. cbn [fst snd] in Hd.
    replace (req_size HUNT_SIZE) with 480 in Hd by (vm_compute; reflexivity).
    change (fs_frame_bytes DFRAME_CLASS) with 4096 in Hd. unfold HUNT_SIZE. lia. }
  pose proof (pd_hsep cx h Hlo (proj1 HA1) HFc HF0 Hhceil Happ Hsep ltac:(lia)) as Hout.
  assert (Hpstk : REAC_HUNT_SILENCE_PROVEN_STK = 4112) by (vm_compute; reflexivity).
  assert (Hraw_ok : YK0s.ret_ok (getr regs 1))
    by (rewrite Hra1; apply ret_ok_codeptr_v; [unfold POFF_C5; lia | reflexivity]).
  assert (Hraw4 : 4096 <= bv_unsigned (getr regs 1))
    by (rewrite Hra1; unfold w64, POFF_C5; rewrite unsigned_lit_small by lia; unfold IMG_LO in HBlo; lia).
  unfold cfg_at.
  eapply SRr_mono.
  { eapply (pd_callZ fq W regs mem3 (w64 (BASE + AF_reac_hunt_silence_proven)) LLVMF_STK (d_S cx) (@nil (Z * Z)) (c_ly cx) (c_S cx)
      (c_W cx) (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)] ly3 S3 md3 k REAC_HUNT_SILENCE_PROVEN_STK
      [(h + 420, h + 424)] 0 (d_A cx - d_S cx) (getr regs 1) _ HJ).
    - rewrite Hsp. lia.
    - lia.
    - unfold MFRAME in *. lia.
    - rewrite Hpstk. lia.
    - rewrite Hpstk. unfold LLVMF_STK, MFRAME in *. lia.
    - exact Hgp.
    - exact Htp.
    - reflexivity.
    - exact Hraw_ok.
    - exact Hraw4.
    - intro Hpre. eapply SRr_mono.
      { apply (THS fq ly3 S3 W regs mem3 md3 [] h h HUNT_SIZE Hpre H10).
        - lia.
        - lia.
        - exact Hhin.
        - lia.
        - unfold req_size, HUNT_SIZE. cbn. lia. }
      cbv beta. intros W2 c2 _ Hp. unfold treac_hunt_silence_proven_post, apost_base in Hp. exact Hp.
    - intros a HaFP. right. apply inFP_cons in HaFP as [Ha | Ha]; [|destruct (inFP_nil _ Ha)].
      exists h, HUNT_SIZE. split; [exact Hhin|]. split.
      + destruct Hblocks as (_ & HnF & _). exact (Forall_inv HnF).
      + unfold req_size, HUNT_SIZE in *. cbn. cbn [fst snd] in Ha. lia. }
  cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & regs2 & mem2 & md2 & -> & Hf0' & HJouter & HJcallee & HP & HK).
  destruct HK as (Hgarr & Hperm).
  pose proof HJouter as (_ & _ & _ & _ & _ & Hfr2 & Hnev2 & _).
  pose proof HJcallee as (_ & _ & _ & _ & _ & Hfrc & _).
  assert (Hfrs2 : frames S2 = [(DFRAME_CLASS, c_fpos cx)]) by (rewrite Hfrc; cbn [app]; exact Hfrs).
  assert (HC2 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly2 S2 W2 mem2 md2 k)
    by (split; [exact Hbase | split; [rewrite Z.add_0_r in HJouter; exact HJouter | exact Hfrs2]]).
  destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HC2)
    as (_ & _ & _ & _ & _ & _ & _ & _ & HFpres2 & HSpres2 & HWpres2 & _ & _ & _ & _).
  assert (Hh2 : In (h, HUNT_SIZE) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hhin).
  replace (d_S cx + (d_A cx - d_S cx)) with (d_A cx) in HJcallee by lia.
  assert (HnFP : forall a, ~ (h <= a < h + 480) -> ~ inFP [(h + 420, h + 424)] a).
  { intros a Ha HaFP. apply inFP_cons in HaFP as [Hc | Hc]; [cbn [fst snd] in Hc; lia | destruct (inFP_nil _ Hc)]. }
  assert (HVfp : forall a, pd_dom cx h a -> ~ inFP [(h + 420, h + 424)] a ->
    aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem3 a)
    by (intros a Ha Hx; exact (pd_aj_view cx h REAC_HUNT_SILENCE_PROVEN_STK [(h + 420, h + 424)] ly3 S3 W mem3 md3
      ly2 S2 W2 mem2 md2 0 HJcallee ltac:(unfold LLVMF_STK in *; lia) Hhi ltac:(unfold MFRAME in *; lia)
      Hfin Efa Hhin Hh2 a Ha Hx)).
  assert (Hfp : forall a, pd_fp cx a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem3 a).
  { intros a Ha. apply HVfp; [unfold pd_fp, pd_dom in *; lia | apply HnFP; apply Hout; left; exact Ha]. }
  assert (Hour2 : garr8 SEGS (rd W2 mem2) (d_obj cx OOUR) (map (fun b : byte => bv_unsigned b) (our_of (c_pl cx)))).
  { apply (pd_garr8_kept W W2 mem3 mem2 _ _ Hour). intros a Ha. rewrite length_map, pd_our_len in Ha.
    apply HVfp; [unfold pd_dom, d_obj, dobj_off in *; lia
      | apply HnFP; apply Hout; right; left; unfold d_obj, dobj_off in *; lia]. }
  assert (HX2 : pd_X8 cx h W2 mem2).
  { split.
    { apply (pd_objs_kept cx _ W W2 mem3 mem2 Hobjs). intros o' a Ho' Ha. pose proof (pd_obj_box o') as Hb'.
      apply HVfp; [unfold pd_dom, d_objr, d_obj in *; lia
        | apply HnFP; apply Hout; right; left; unfold d_objr, d_obj in *; lia]. }
    split.
    { unfold pd_v216. apply (pd_val_mem_kept W W2 mem3 mem2 _ _ _ Hv216). intros a Ha.
      apply HVfp; [unfold pd_dom in *; lia | apply HnFP; apply Hout; right; right; lia]. }
    apply (pd_hpatch cx h W W2 mem3 mem2 420 (Mem.le4 (Z_to_bv 64 1)) Hhnew).
    - lia.
    - rewrite Mem.length_le4. cbn. lia.
    - intros a Ha Hx. apply HVfp; [unfold pd_dom; right; right; right; right; exact Ha|].
      intros HaFP. apply inFP_cons in HaFP as [Hc | Hc]; [cbn [fst snd] in Hc|destruct (inFP_nil _ Hc)].
      rewrite Mem.length_le4 in Hx. cbn in Hx. lia.
    - exact Hgarr. }
  unfold pro_C5, d_at.
  exists fx', ly2, S2, regs2, mem2, md2, k, acc.
  split; [rewrite Hra1; reflexivity|].
  split; [exact (Hf0' Hf0)|]. split; [exact Hbase|]. split; [rewrite Z.add_0_r in HJouter; exact HJouter|]. split; [exact Hfrs2|].
  split; [exact Hk|]. split; [rewrite Z.add_0_r in Hnev2; lia|]. split; [rewrite MT_TRIV; exact I|].
  split; [exact Hacc|]. split; [exact Hcan0|].
  split; [exact (p_rC5_eq cx h regs regs2 (pd_cs_pres regs regs2 HP) HrC5)|].
  split.
  { apply (pd_frame_kept cx dsh_loop ps_C5 W W2 mem3 mem2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(unfold MFRAME, LLVMF_STK in *; lia) ltac:(unfold MFRAME in *; lia) Hhi ltac:(lia) ltac:(lia) Hframe Hfp).
    - intros a Ha. apply HWpres2. unfold LLVMF_STK, MFRAME in *. lia.
    - exact HFpres2.
    - exact HSpres2. }
  split; [exact (pd_blocks_kept cx h ly3 S3 ly2 S2 Hblocks Hperm)|].
  split; [exact (proj1 (proj2 HX2))|].
  exact (pd_objs_of cx h W2 mem2 HX2 Hour2).
Qed.

Lemma pd_s9 : forall cx h W c, pd_q8 cx h W c ->
  SRr SEGS W c (fun W' c' => pd_q9 cx h W' c' \/ pd_q10 cx h W' c').
Proof.
  intros cx h W c H.
  destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hf0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
    Hcan0 & HR & Hframe & Hblocks & Hour & (Hobjs & Hv216 & Hhnew)).
  pose proof Hframe as (E & HdE & HRG & Hflag).
  assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
    by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
  destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HC)
    as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR3 & Hfin & Efa & Efl).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
  assert (HAr : 0 <= d_A cx < 2 ^ 64) by (unfold MFRAME, LLVMF_STK in *; lia).
  assert (HFr : 0 <= d_FB cx < 2 ^ 64) by lia.
  assert (Hhin : In (h, HUNT_SIZE) (ablocks B ly3 S3))
    by (destruct Hblocks as (HPm & _); apply (Permutation_in _ (Permutation_sym HPm)); left; reflexivity).
  destruct ((al_blocks _ _ LAWS) ly3 S3 W mem3 md3 h HUNT_SIZE HAR3 Hhin) as (Hh16 & Hh4096 & Hhceil & _).
  replace (req_size HUNT_SIZE) with 480 in Hhceil by (vm_compute; reflexivity).
  assert (Hh64 : 0 <= h < 2 ^ 64) by lia.
  pose proof (pd_regs_ok cx E regs HdE (proj1 (proj1 HR)) HAr HFr) as HROK.
  assert (E554 : ew (d_env cx E (pd_vals regs)) 554 = Z_to_bv 64 h).
  { change 554%nat with (AT_X + 23)%nat. rewrite (d_env_x cx E (pd_vals regs) 23 ltac:(cbn; lia)).
    cbn [pd_vals map seq nth Z.of_nat]. exact (proj2 HR). }
  assert (Hacs : Forall (YP09.chunk_ok SEGS (d_env cx E (pd_vals regs)) (rd W mem3) (d_A cx)) [pd_c216]).
  { apply Forall_cons; [|apply Forall_nil]. unfold pd_c216.
    apply (chunk_ok_val SEGS (d_env cx E (pd_vals regs)) (rd W mem3) (d_A cx) 216 8%N (SOff (AT_X + 23) 0) h).
    - cbn [sv_denot]. change (AT_X + 23)%nat with 554%nat. rewrite E554, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - cbn [Z.of_N]. change (8 * 8) with 64. lia.
    - cbn [Z.of_N]. lia.
    - cbn [N.to_nat]. exact Hv216. }
  pose proof (p_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx dsh_loop ps_C4 ly3 S3 W regs mem3 md3 k E RA_HI pd_sr
    (pd_vals regs) [pd_c216] [] [] (d_facts [] []) HC HdE HRG Hflag HROK
    (d_facts_ok B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k E (pd_vals regs) [] [] HC HdE I I)
    Hacs (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity)) as HS.
  unfold ss_p in HS.
  assert (HEI : img_env VAL A_LIM (d_env cx E (pd_vals regs)))
    by (destruct HdE as (_ & _ & HI & _); intros a Ha; unfold d_env;
        rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia); exact (HI a Ha)).
  assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (pd_vals regs)) (rd W mem3)) by constructor.
  pose (RUN := paj_run (fx := fq) B LAWS).
  pose (RUNTO := paj_run_to (fx := fq) B LAWS).
  pose (BR := paj_branch (fx := fq) (PI := PI)).
  unfold cfg_at. change (w64 (BASE + RA_HI)) with (Z_to_bv 64 (BASE + RA_HI)).
  pd_ro_base HS 516%nat. pd_ro_base HS 529%nat. pd_ro_base HS 60%nat.
  paj_run_tok RUN HS HJ SHOK PDspan.
  { cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  clear SHOK.
  lazymatch goal with
  | HF0 : frame_of _ _ mem3 (ms_mem ?ms0), HFr0 : frame_of _ _ (mrestrict _ _) _, HG0 : mem_grows _ _
    |- SRr _ _ {| cfg_ms := ?ms0; cfg_model := _ |} _ =>
    pose proof (pd_frame_of_ro _ _ _ _ HF0 ltac:(vm_compute; reflexivity)) as Em0; clear HF0 HFr0 HG0;
    assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (pd_vals regs)) (rd W (ms_mem ms0))) by constructor
  end.
  psrr_branch_tok RUN BR HS SHOK PDspan.
  - paj_run_to_tok RUNTO HS HJ SHOK PDspan 0x770.
    { cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
    lazymatch goal with
    | HF0 : frame_of _ _ ?mprev (ms_mem ?msN), HFr0 : frame_of _ _ (mrestrict _ _) _, HG0 : mem_grows _ _
      |- SRr _ _ {| cfg_ms := ?msN; cfg_model := ?md4 |} _ =>
      pose proof (pd_frame_of_ro _ _ _ _ HF0 ltac:(vm_compute; reflexivity)) as Em; clear HF0 HFr0 HG0;
      pose proof (st_ok_restrict_mkst SEGS (w_H W) _ _ msN HS eq_refl) as Hms; cbn [ss_pc setpc abs_ss] in Hms;
      pose proof (pd_regs_same fq _ _ msN regs pd_cs (w_H W) HS HROK ltac:(vm_compute; reflexivity)) as RG;
      apply SRr_ret; right; unfold pd_q10, pd_at, d_at;
      exists fq, ly3, S3, (ms_regs msN), (ms_mem msN), md4, k, acc
    end.
    split; [unfold cfg_at, w64, RA_PIN; rewrite <- Hms; reflexivity|].
    rewrite Em, Em0 in HJ |- *.
    split; [exact Hf0|]. split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
    split; [exact Hnev|]. split; [exact Hmo|]. split; [exact Hacc|]. split; [exact Hcan0|].
    split; [exact (p_rC4_eq cx h regs _ RG HR)|].
    split; [exact Hframe|]. split; [exact Hblocks|]. split; [exact Hour | split; [exact Hobjs | split; [exact Hv216 | exact Hhnew]]].
  - paj_run_tok RUN HS HJ SHOK PDspan.
    { cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
    rewrite (pa_sigma_reac_hunt_pin (PI := PI)) in HS.
    lazymatch goal with
    | HF0 : frame_of _ _ ?mprev (ms_mem ?msN), HFr0 : frame_of _ _ (mrestrict _ _) _, HG0 : mem_grows _ _
      |- SRr _ _ {| cfg_ms := ?msN; cfg_model := ?md4 |} _ =>
      pose proof (pd_frame_of_ro _ _ _ _ HF0 ltac:(vm_compute; reflexivity)) as Em; clear HF0 HFr0 HG0;
      pose proof (st_ok_restrict_mkst SEGS (w_H W) _ _ msN HS eq_refl) as Hms; cbn [ss_pc setpc abs_ss] in Hms;
      pose proof (pd_regs_same fq _ _ msN regs pd_cs (w_H W) HS HROK ltac:(vm_compute; reflexivity)) as RG;
      pose proof (st_ok_restrict_reg SEGS (w_H W) _ _ msN 1%bv HS) as R1;
      pose proof (st_ok_restrict_reg SEGS (w_H W) _ _ msN 10%bv HS) as R10;
      pd_rsr R1; pd_rsr R10;
      apply SRr_ret; left; unfold pd_q9, pd_at, d_at;
      exists fq, ly3, S3, (ms_regs msN), (ms_mem msN), md4, k, acc
    end.
    split; [unfold cfg_at, w64; rewrite <- Hms; reflexivity|].
    rewrite Em, Em0 in HJ |- *.
    split; [exact Hf0|]. split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
    split; [exact Hnev|]. split; [exact Hmo|]. split; [exact Hacc|]. split; [exact Hcan0|].
    split.
    { split; [exact (p_rC4_eq cx h regs _ RG HR)|].
      split; [rewrite R1; exact (codeptr_val _ RA_PIN HEI)|].
      rewrite R10. cbn [sv_denot]. rewrite E554, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
    split; [exact Hframe|]. split; [exact Hblocks|]. split; [exact Hour | split; [exact Hobjs | split; [exact Hv216 | exact Hhnew]]].
Qed.

Lemma pd_objr_offA : forall cx o a, d_objr cx o a -> 0 <= d_FB cx -> d_FB cx + 3072 <= d_A cx ->
  d_A cx + 472 <= 2 ^ 64 -> 0 <= a < 2 ^ 64 /\ ~ (d_A cx <= a < d_A cx + 472).
Proof. intros cx o a Ha H0 H1 H2. pose proof (pd_obj_box o). unfold d_objr, d_obj in Ha. lia. Qed.
Lemma pd_rng_offA : forall A lo n a, lo <= a < lo + n -> 0 <= lo -> lo + n <= A -> A + 472 <= 2 ^ 64 ->
  0 <= a < 2 ^ 64 /\ ~ (A <= a < A + 472).
Proof. intros A lo n a Ha H0 H1 H2. lia. Qed.

Lemma pd_s11 : forall cx h W c, pd_q10 cx h W c ->
  SRr SEGS W c (fun W' c' => pd_q11 cx h W' c' \/ pro_C5 B MT XM_LIB RLO RHI tfib_K cx h W' c').
Proof.
  intros cx h W c H.
  destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hf0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
    Hcan0 & HR & Hframe & Hblocks & Hour & (Hobjs & Hv216 & Hhnew)).
  pose proof Hframe as (E & HdE & HRG & Hflag).
  assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
    by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
  destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HC)
    as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR3 & Hfin & Efa & Efl).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
  assert (HAr : 0 <= d_A cx < 2 ^ 64) by (unfold MFRAME, LLVMF_STK in *; lia).
  assert (HFr : 0 <= d_FB cx < 2 ^ 64) by lia.
  assert (Hhin : In (h, HUNT_SIZE) (ablocks B ly3 S3))
    by (destruct Hblocks as (HPm & _); apply (Permutation_in _ (Permutation_sym HPm)); left; reflexivity).
  destruct ((al_blocks _ _ LAWS) ly3 S3 W mem3 md3 h HUNT_SIZE HAR3 Hhin) as (Hh16 & Hh4096 & Hhceil & _).
  replace (req_size HUNT_SIZE) with 480 in Hhceil by (vm_compute; reflexivity).
  assert (Hh64 : 0 <= h < 2 ^ 64) by lia.
  assert (HFbelow : d_FB cx + 3072 <= d_A cx) by (unfold LLVMF_STK, MFRAME in *; lia).
  assert (Hhbelow : h + 480 <= d_A cx) by (unfold LLVMF_STK, MFRAME in *; lia).
  assert (HAtop : d_A cx + 472 <= 2 ^ 64) by (unfold LLVMF_STK, MFRAME in *; lia).
  assert (HFpos : 0 <= d_FB cx) by lia.
  assert (Hhpos : 0 <= h) by lia.
  assert (HObelow : d_obj cx OOUR + 6 <= d_A cx) by (unfold d_obj; cbn [dobj_off]; lia).
  assert (HOpos : 0 <= d_obj cx OOUR) by (unfold d_obj; cbn [dobj_off]; lia).
  pose proof (pd_regs_ok cx E regs HdE (proj1 (proj1 HR)) HAr HFr) as HROK.
  assert (E554 : ew (d_env cx E (pd_vals regs)) 554 = Z_to_bv 64 h).
  { change 554%nat with (AT_X + 23)%nat. rewrite (d_env_x cx E (pd_vals regs) 23 ltac:(cbn; lia)).
    cbn [pd_vals map seq nth Z.of_nat]. exact (proj2 HR). }
  assert (EA : ew (d_env cx E (pd_vals regs)) 60 = Z_to_bv 64 (d_A cx))
    by (unfold d_env; rewrite ew_havoc_old by (cbv; lia); destruct HdE as (_ & _ & _ & HA60 & _); exact HA60).
  assert (Hacs : Forall (YP09.chunk_ok SEGS (d_env cx E (pd_vals regs)) (rd W mem3) (d_A cx)) [pd_c216]).
  { apply Forall_cons; [|apply Forall_nil]. unfold pd_c216.
    apply (chunk_ok_val SEGS (d_env cx E (pd_vals regs)) (rd W mem3) (d_A cx) 216 8%N (SOff (AT_X + 23) 0) h).
    - cbn [sv_denot]. change (AT_X + 23)%nat with 554%nat. rewrite E554, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - cbn [Z.of_N]. change (8 * 8) with 64. lia.
    - cbn [Z.of_N]. lia.
    - cbn [N.to_nat]. exact Hv216. }
  pose proof (p_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx dsh_loop ps_C4 ly3 S3 W regs mem3 md3 k E RA_PIN pd_sr
    (pd_vals regs) [pd_c216] [] [] (d_facts [] []) HC HdE HRG Hflag HROK
    (d_facts_ok B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k E (pd_vals regs) [] [] HC HdE I I)
    Hacs (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity)) as HS.
  unfold ss_p in HS.
  assert (HEI : img_env VAL A_LIM (d_env cx E (pd_vals regs)))
    by (destruct HdE as (_ & _ & HI & _); intros a Ha; unfold d_env;
        rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia); exact (HI a Ha)).
  assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (pd_vals regs)) (rd W mem3)) by constructor.
  pose (RUN := paj_run (fx := fq) B LAWS).
  pose (RUNTO := paj_run_to (fx := fq) B LAWS).
  pose (BR := paj_branch (fx := fq) (PI := PI)).
  unfold cfg_at. change (w64 (BASE + RA_PIN)) with (Z_to_bv 64 (BASE + RA_PIN)).
  pd_ro_base HS 516%nat. pd_ro_base HS 529%nat.
  paj_run_tok RUN HS HJ SHOK PDspan.
  { cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|].
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (d_A cx - d_S cx));
      [reflexivity | rewrite EA, unsigned_lit_small by lia; lia
      | cbn [YP09.r_wlo]; unfold LLVMF_STK, MFRAME in *; lia | cbn [YP09.r_whi]; unfold MFRAME in *; lia |].
    repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  clear SHOK.
  lazymatch goal with
  | HF0 : frame_of _ _ mem3 (ms_mem ?ms0), HFr0 : frame_of _ ?rs0 (rd _ mem3) (rd _ (ms_mem ?ms0)), HG0 : mem_grows _ _
    |- SRr _ _ {| cfg_ms := ?ms0; cfg_model := _ |} _ =>
    rename HFr0 into HFm; clear HF0 HG0;
    assert (HW60 : pd_wr60 rs0 = true) by (vm_compute; reflexivity);
    assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (pd_vals regs)) (rd W (ms_mem ms0))) by constructor;
    assert (HVpre : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx <= a < d_A cx + 472) ->
      aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem3 a)
      by (intros a Ha Hn; apply (pd_aview_frame _ _ _ _ _ a HFm Ha); intros Hw;
          pose proof (pd_wr60_ok _ _ a HW60 Hw) as Hw'; cbn [base_val] in Hw';
          rewrite EA, unsigned_lit_small in Hw' by lia; exact (Hn Hw'))
  end.
  psrr_branch_tok RUN BR HS SHOK PDspan.
  - paj_run_to_tok RUNTO HS HJ SHOK PDspan 0x78c.
    { cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|].
      eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (d_A cx - d_S cx));
        [reflexivity | rewrite EA, unsigned_lit_small by lia; lia
        | cbn [YP09.r_wlo]; unfold LLVMF_STK, MFRAME in *; lia | cbn [YP09.r_whi]; unfold MFRAME in *; lia |].
      repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
    lazymatch goal with
    | HF1 : frame_of _ _ _ (ms_mem ?msF), HFr1 : frame_of _ ?rs1 (mrestrict _ (ms_mem ?msp)) (mrestrict _ _),
      HG1 : mem_grows _ _ |- SRr _ _ {| cfg_ms := ?msF; cfg_model := ?mdF |} _ =>
      clear HF1 HG1; assert (HW60b : pd_wr60 rs1 = true) by (vm_compute; reflexivity);
      assert (HVtot : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx <= a < d_A cx + 472) ->
        aview SEGS (w_H W) (ms_mem msF) a = aview SEGS (w_H W) mem3 a)
        by (intros a Ha Hn; rewrite (pd_aview_frame _ _ _ _ _ a HFr1 Ha
              ltac:(intros Hw; pose proof (pd_wr60_ok _ _ a HW60b Hw) as Hw'; cbn [base_val] in Hw';
                    rewrite EA, unsigned_lit_small in Hw' by lia; exact (Hn Hw'))); apply HVpre; [exact Ha | exact Hn]);
      pose proof (st_ok_restrict_mkst SEGS (w_H W) _ _ msF HS eq_refl) as Hms; cbn [ss_pc setpc abs_ss] in Hms;
      pose proof (pd_regs_same fq _ _ msF regs pd_cs2 (w_H W) HS HROK ltac:(vm_compute; reflexivity)) as RG;
      pose proof (st_ok_restrict_reg SEGS (w_H W) _ _ msF 19%bv HS) as R19; pd_rsr R19;
      lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssF ?msx =>
        pose proof HS as HSpi;
        let r := eval vm_compute in (nth 1 (ss_mem ssF) got_regionP) in
        pose proof (st_ok_pi_region_nth Ex ssF msx 1 r HSpi ltac:(vm_compute; reflexivity)) as R60 end;
      assert (HCf : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem msF) mdF k)
        by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]);
      destruct (p_land B MT XM_LIB RLO RHI tfib_K LAWS FFL fq cx dsh_loop ps_C5 ly3 S3 W mdF k
        (d_env cx E (pd_vals regs)) _ msF HCf (d_E_env cx E _ HdE) (d_env_fl cx E _) HSpi ltac:(vm_compute; reflexivity))
        as [Hframe' _];
      change (ms_mem (restrict (w_H W) msF)) with (rd W (ms_mem msF)) in R60
    end.
    lazymatch goal with
    | |- SRr _ _ {| cfg_ms := ?msF; cfg_model := ?mdF |} _ =>
      assert (Hv216' : pd_v216 cx h W (ms_mem msF))
        by (unfold pd_v216; exact (field_of_region _ _ 60%nat (d_A cx) _ 0 472 0 472 216 8%N (SOff 554 0) h R60
          ltac:(rewrite EA; apply unsigned_lit_small; lia) ltac:(clear; cbn; repeat first [left; reflexivity | right])
          ltac:(cbn [sv_denot]; rewrite E554, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
          ltac:(cbn [Z.of_N]; change (8 * 8) with 64; lia) ltac:(cbn; lia)));
      assert (HX2 : pd_X8 cx h W (ms_mem msF));
      [ split;
        [ apply (pd_objs_kept cx _ W W mem3 (ms_mem msF) Hobjs); intros o' a Ho' Ha;
          destruct (pd_objr_offA cx o' a Ha HFpos HFbelow HAtop) as [B1 B2]; exact (HVtot a B1 B2)
        | split;
          [ exact Hv216'
          | apply (pd_hnew_kept cx h W W mem3 (ms_mem msF) Hhnew); intros a Ha; unfold HUNT_SIZE in Ha;
            destruct (pd_rng_offA (d_A cx) h 480 a Ha Hhpos Hhbelow HAtop) as [B1 B2]; exact (HVtot a B1 B2) ] ]
      | ];
      assert (Hour2 : garr8 SEGS (rd W (ms_mem msF)) (d_obj cx OOUR) (map (fun b : byte => bv_unsigned b) (our_of (c_pl cx))));
      [ apply (pd_garr8_kept W W mem3 (ms_mem msF) _ _ Hour); intros a Ha; rewrite length_map, pd_our_len in Ha;
        change (Z.of_nat 6) with 6 in Ha;
        destruct (pd_rng_offA (d_A cx) (d_obj cx OOUR) 6 a Ha HOpos HObelow HAtop) as [B1 B2]; exact (HVtot a B1 B2)
      | ];
      apply SRr_ret; right; unfold pro_C5, d_at;
      exists fq, ly3, S3, (ms_regs msF), (ms_mem msF), mdF, k, acc;
      split; [unfold cfg_at, w64, POFF_C5; rewrite <- Hms; reflexivity|];
      split; [exact Hf0|]; split; [exact Hbase|]; split; [exact HJ|]; split; [exact Hfrs|]; split; [exact Hk|];
      split; [exact Hnev|]; split; [rewrite MT_TRIV; exact I|]; split; [exact Hacc|]; split; [exact Hcan0|];
      split; [exact (p_rC5_build cx h regs (ms_regs msF) (fun r Hr => RG r Hr)
        ltac:(rewrite R19; cbn [sv_denot]; change (AT_X + 23)%nat with 554%nat;
              rewrite E554, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) HR)|];
      split; [exact Hframe'|]; split; [exact Hblocks|];
      split; [exact Hv216'|];
      exact (pd_objs_of cx h W (ms_mem msF) HX2 Hour2)
    end.
  - paj_run_tok RUN HS HJ SHOK PDspan.
    { cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|].
      eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (d_A cx - d_S cx));
        [reflexivity | rewrite EA, unsigned_lit_small by lia; lia
        | cbn [YP09.r_wlo]; unfold LLVMF_STK, MFRAME in *; lia | cbn [YP09.r_whi]; unfold MFRAME in *; lia |].
      repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
    rewrite (pa_sigma_reac_hunt_silence_proven (PI := PI)) in HS.
    lazymatch goal with
    | HF1 : frame_of _ _ _ (ms_mem ?msF), HFr1 : frame_of _ ?rs1 (mrestrict _ (ms_mem ?msp)) (mrestrict _ _),
      HG1 : mem_grows _ _ |- SRr _ _ {| cfg_ms := ?msF; cfg_model := ?mdF |} _ =>
      clear HF1 HG1; assert (HW60b : pd_wr60 rs1 = true) by (vm_compute; reflexivity);
      assert (HVtot : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx <= a < d_A cx + 472) ->
        aview SEGS (w_H W) (ms_mem msF) a = aview SEGS (w_H W) mem3 a)
        by (intros a Ha Hn; rewrite (pd_aview_frame _ _ _ _ _ a HFr1 Ha
              ltac:(intros Hw; pose proof (pd_wr60_ok _ _ a HW60b Hw) as Hw'; cbn [base_val] in Hw';
                    rewrite EA, unsigned_lit_small in Hw' by lia; exact (Hn Hw'))); apply HVpre; [exact Ha | exact Hn]);
      pose proof (st_ok_restrict_mkst SEGS (w_H W) _ _ msF HS eq_refl) as Hms; cbn [ss_pc setpc abs_ss] in Hms;
      pose proof (pd_regs_same fq _ _ msF regs pd_cs2 (w_H W) HS HROK ltac:(vm_compute; reflexivity)) as RG;
      pose proof (st_ok_restrict_reg SEGS (w_H W) _ _ msF 19%bv HS) as R19; pd_rsr R19;
      pose proof (st_ok_restrict_reg SEGS (w_H W) _ _ msF 1%bv HS) as R1; pd_rsr R1;
      pose proof (st_ok_restrict_reg SEGS (w_H W) _ _ msF 10%bv HS) as R10; pd_rsr R10;
      lazymatch type of HS with st_ok _ ?Ex (setpc ?ssx _) ?msx =>
        assert (HSpi : st_ok_pi SEGS VAL Ex (setpc ssx AF_reac_hunt_silence_proven) msx) by exact HS;
        let r := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
        pose proof (st_ok_pi_region_nth Ex (setpc ssx AF_reac_hunt_silence_proven) msx 1 r HSpi
          ltac:(vm_compute; reflexivity)) as R60 end;
      assert (HCf : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem msF) mdF k)
        by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]);
      destruct (p_land B MT XM_LIB RLO RHI tfib_K LAWS FFL fq cx dsh_loop ps_C5 ly3 S3 W mdF k
        (d_env cx E (pd_vals regs)) _ msF HCf (d_E_env cx E _ HdE) (d_env_fl cx E _) HSpi ltac:(vm_compute; reflexivity))
        as [Hframe' _];
      change (ms_mem (restrict (w_H W) msF)) with (rd W (ms_mem msF)) in R60;
      assert (Hv216' : pd_v216 cx h W (ms_mem msF))
        by (unfold pd_v216; exact (field_of_region _ _ 60%nat (d_A cx) _ 0 472 0 472 216 8%N (SOff 554 0) h R60
          ltac:(rewrite EA; apply unsigned_lit_small; lia) ltac:(clear; cbn; repeat first [left; reflexivity | right])
          ltac:(cbn [sv_denot]; rewrite E554, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
          ltac:(cbn [Z.of_N]; change (8 * 8) with 64; lia) ltac:(cbn; lia)));
      assert (HX2 : pd_X8 cx h W (ms_mem msF));
      [ split;
        [ apply (pd_objs_kept cx _ W W mem3 (ms_mem msF) Hobjs); intros o' a Ho' Ha;
          destruct (pd_objr_offA cx o' a Ha HFpos HFbelow HAtop) as [B1 B2]; exact (HVtot a B1 B2)
        | split;
          [ exact Hv216'
          | apply (pd_hnew_kept cx h W W mem3 (ms_mem msF) Hhnew); intros a Ha; unfold HUNT_SIZE in Ha;
            destruct (pd_rng_offA (d_A cx) h 480 a Ha Hhpos Hhbelow HAtop) as [B1 B2]; exact (HVtot a B1 B2) ] ]
      | ];
      assert (Hour2 : garr8 SEGS (rd W (ms_mem msF)) (d_obj cx OOUR) (map (fun b : byte => bv_unsigned b) (our_of (c_pl cx))));
      [ apply (pd_garr8_kept W W mem3 (ms_mem msF) _ _ Hour); intros a Ha; rewrite length_map, pd_our_len in Ha;
        change (Z.of_nat 6) with 6 in Ha;
        destruct (pd_rng_offA (d_A cx) (d_obj cx OOUR) 6 a Ha HOpos HObelow HAtop) as [B1 B2]; exact (HVtot a B1 B2)
      | ];
      apply SRr_ret; left; unfold pd_q11, pd_at, d_at;
      exists fq, ly3, S3, (ms_regs msF), (ms_mem msF), mdF, k, acc;
      split; [unfold cfg_at, w64; rewrite <- Hms; reflexivity|];
      split; [exact Hf0|]; split; [exact Hbase|]; split; [exact HJ|]; split; [exact Hfrs|]; split; [exact Hk|];
      split; [exact Hnev|]; split; [rewrite MT_TRIV; exact I|]; split; [exact Hacc|]; split; [exact Hcan0|];
      split;
      [ split;
        [ exact (p_rC5_build cx h regs (ms_regs msF) (fun r Hr => RG r Hr)
            ltac:(rewrite R19; cbn [sv_denot]; change (AT_X + 23)%nat with 554%nat;
                  rewrite E554, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) HR)
        | split;
          [ rewrite R1; exact (codeptr_val _ POFF_C5 HEI)
          | rewrite R10; cbn [sv_denot]; change (AT_X + 23)%nat with 554%nat;
            rewrite E554, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity ] ]
      | ];
      split; [exact Hframe'|]; split; [exact Hblocks|]; split; [exact Hour2 | exact HX2]
    end.
Qed.

Lemma pd_from_q10 : forall cx h W c, pd_q10 cx h W c -> SRr SEGS W c (pro_C5 B MT XM_LIB RLO RHI tfib_K cx h).
Proof.
  intros cx h W c H.
  eapply SRr_bind; [exact (pd_s11 cx h W c H) |].
  intros W' c' _ [Hq11 | HC5].
  - exact (pd_s12 cx h W' c' Hq11).
  - apply SRr_ret. exact HC5.
Qed.

Theorem pb_proD : pro_segD B MT XM_LIB RLO RHI tfib_K.
Proof.
  unfold pro_segD. intros cx h W c H.
  apply pd_c4_at in H.
  eapply SRr_bind; [exact (pd_s1 cx h W c H) |]. intros W1 c1 _ H1.
  eapply SRr_bind; [exact (pd_s2 cx h W1 c1 H1) |]. intros W2 c2 _ H2.
  eapply SRr_bind; [exact (pd_s3 cx h W2 c2 H2) |]. intros W3 c3 _ H3.
  eapply SRr_bind; [exact (pd_s4 cx h W3 c3 H3) |]. intros W4 c4 _ H4.
  eapply SRr_bind; [exact (pd_s5 cx h W4 c4 H4) |]. intros W5 c5 _ H5.
  eapply SRr_bind; [exact (pd_s6 cx h W5 c5 H5) |]. intros W6 c6 _ H6.
  eapply SRr_bind; [exact (pd_s7 cx h W6 c6 H6) |]. intros W7 c7 _ H7.
  eapply SRr_bind; [exact (pd_s8 cx h W7 c7 H7) |]. intros W8 c8 _ H8.
  eapply SRr_bind; [exact (pd_s9 cx h W8 c8 H8) |]. intros W9 c9 _ [H9 | H10].
  - eapply SRr_bind; [exact (pd_s10 cx h W9 c9 H9) |]. intros W10 c10 _ H10'.
    exact (pd_from_q10 cx h W10 c10 H10').
  - exact (pd_from_q10 cx h W9 c9 H10).
Qed.

End h.
End f.
End d.
