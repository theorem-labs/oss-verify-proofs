(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a segment of reac_headamp_tx_next on fuzz_grant.asan (NextEntry), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/NextEntry.v at a working branch af735a950e2 (blob 8725db69d2a; the walk was ported from blob 7788bf8f6e4 at a working branch afd75724b5b, which differs from it only by 4 added and 0 removed lines, the licence header), restated over image B's listing, addresses and walk layer (lib/B/Prog) against GrantBContracts.v; frame 96 with twelve saved registers, UBSan traps T1 and T2, and the .rodata divisor read at 0x85fa4 (IMG_NEXT_DIV3) *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/B/Prog/NextEntry.v, with its module paths and module names changed; 542 of its 591 lines of code are new or changed and 711 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_link_alias_readExit.v, with its module names changed; 702 of its 768 lines of code are new or changed and 525 lines of the source are left out. *)
(* model_write (fuzz_link.asan 0x88100) on image A, the SEND piece's first half: from the SEND cut (+0x16c) to
   the RQ cut (+0x1d8) of lib/A/Prog/model_writeSendC.v, the request built in the side frame (cut interface
   lib/A/Prog/model_writeDefs.v; listing (internal path) (internal record, sha256 2152d78b142c)):
     S1   +0x16c..+0x17c  s6 := the index, s9 := F + 32 (the request), a0 := F's shadow + 4, a1 := 64: a plain run to
                          meta_fill_00
     MF   +0x17c          meta_fill_00(F's shadow + 4, 64): LinkWalkSide.v aj_gx_set_shadow_at (the request in scope)
     S2   +0x180..+0x198  s10 := ((|alias| + 7) & 0x1fc) + 32 (the request's length), a0 := s9, a1 := 0, a2 := s10:
                          a plain run to checked_memset
     SET  +0x198          checked_memset(req, 0, len): link_ajkit.v aj_gx_intrin_at, op OSet
     S3   +0x19c..+0x1d4  the header stores (rta_len, rta_type, nlmsg_len, type and flags, seq, the index), a0 :=
                          req + 36, a1 := alias, a2 := |alias|: a plain run to checked_memcpy over the request's first
                          36 bytes
     CPY  +0x1d4          checked_memcpy(req + 36, alias, |alias|): aj_gx_intrin_at, op OCpy; then the RQ cut
   Template: lib/A/Prog/reac_link_alias_writeSend.v, stages 1, 2,
   set and cpy (its request has the same layout).

   Section hypotheses: LAWS, TB, HSEGS, LV, MFF8, TALK (as model_writeSendC.v), MF00 (meta_fill_00's contract,
   lib/A/Rt/SetShadow.v link_set_shadow_00), AMSET, AMCPY (checked_memset / checked_memcpy, lib/A/AE2r.v
   asan_memset_realizes / asan_memcpy_realizes).

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 SetShadowDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b YC88 LinkWalk LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkShadow LinkWalkCall LinkWalkZsh.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
index_of_c talk_c model_write_c model_writeDefs model_writeKit model_writeStep model_writeArmsA model_writeCut
model_writeCall model_writeArmsB model_writeArmsC model_writeArmsD model_writeSendA model_writeSendC.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Definition MW_S2 : Z := AF_model_write + 0x180.    (* the return address of meta_fill_00 *)
Definition MW_S3 : Z := AF_model_write + 0x19c.    (* the return address of checked_memset *)

(* the length word's ALU expression (+0x180..+0x188), after reac_link_alias_writeSend.v aws_denot_len *)
Lemma mw_denot_and508 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 ->
  sv_denot E (SAlu ALU_AND (SOff n 7) (SLit 508)) = Z_to_bv 64 (Z.land (v + 7) 508).
Proof.
  intros E n v Hn Hv. rewrite denot_lit_U. f_equal.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v 7 Hn) by lia.
  change (zcanon 508) with 508. rewrite mw_land_508 by lia. apply zcanon_id. unfold M64. lia.
Qed.

Lemma mw_denot_len : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff n 7) (SLit 508)) (SLit 32)) =
  Z_to_bv 64 (32 + nl_align (RTA_HDR + v)).
Proof.
  intros E n v Hn Hv. rewrite <- (mw_len_val v Hv). rewrite denot_lit_U. f_equal.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 32) with 32.
  assert (HU : U E (SAlu ALU_AND (SOff n 7) (SLit 508)) = Z.land (v + 7) 508).
  { unfold U. rewrite (mw_denot_and508 E n v Hn Hv). apply unsigned_lit_small. rewrite mw_land_508 by lia. lia. }
  rewrite HU, mw_land_508 by lia. apply zcanon_id. unfold M64. lia.
Qed.

Lemma mw_denot_add0 : forall E x, sv_denot E (SAlu ALU_ADD x (SLit 0)) = sv_denot E x.
Proof.
  intros E x. rewrite (denot_lit_U E (SAlu ALU_ADD x (SLit 0))), (denot_lit_U E x). f_equal.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 0) with 0. rewrite Z.add_0_r.
  apply zcanon_id. exact (U_range E x).
Qed.

Lemma mw_zero_of_region : forall segs (Ex : env) (m : word -> option byte) (r : YP09.region) base off len j,
  region_ok segs Ex m r -> base_val Ex (YP09.r_base r) = base ->
  In (YP09.mkChunk off (CZero len)) (YP09.r_chunks r) -> 0 <= j < len ->
  mbyte segs m (base + off + j) = Some (Z_to_bv 8 0).
Proof.
  intros segs Ex m r base off len j HR Hb Hin Hj.
  destruct HR as (_ & _ & _ & HCh). rewrite Forall_forall in HCh.
  pose proof (HCh _ Hin) as Hc. rewrite Hb in Hc.
  destruct (Hc j ltac:(cbn; lia)) as (bb & Hb1 & Hb2).
  cbn [YP09.c_off YP09.c_val] in Hb1, Hb2. cbn in Hb1. injection Hb1 as <-. exact Hb2.
Qed.

Lemma mw_vm_keep : forall segs (m m' : word -> option byte) a (n : nat) v, val_mem segs m a n v ->
  (forall k, (k < n)%nat -> mbyte segs m' (a + Z.of_nat k) = mbyte segs m (a + Z.of_nat k)) -> val_mem segs m' a n v.
Proof. intros segs m m' a n v Hv Hk k Hlt. rewrite (Hk k Hlt). exact (Hv k Hlt). Qed.

Lemma mw_shape_of : forall {fx : YK11.FPState} segs (ms : machine_state) R pc m, ms = mkst R pc m (seg_rom segs) ->
  ms_resv ms = None /\ ms_svc_pending ms = None /\ ms_rom ms = seg_rom segs /\ ms_fregs ms = fp_regs /\
  ms_fcsr ms = fp_csr.
Proof. intros fx segs ms R pc m ->. repeat split; reflexivity. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Lemma mw_mbyte0 : forall segs H (m : word -> option byte) a, aview segs H m a = Some 0 ->
  mbyte segs (mrestrict H m) a = Some (zb 0).
Proof.
  intros segs H m a E. unfold aview in E. destruct (mbyte segs (mrestrict H m) a) as [b|] eqn:Eb; cbn in E; [|discriminate].
  injection E as E. f_equal. apply bv_eq. rewrite E. reflexivity.
Qed.

Lemma mw_aview_some : forall segs H (m : word -> option byte) a b, mbyte segs (mrestrict H m) a = Some b ->
  aview segs H m a <> None.
Proof. intros segs H m a b E. unfold aview. rewrite E. cbn. discriminate. Qed.

Lemma mw_frame_aview : forall segs E rs (H : word -> bool) (m m' : word -> option byte) x,
  frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= x < 2 ^ 64 -> ~ in_wrange E rs x ->
  aview segs H m' x = aview segs H m x.
Proof.
  intros segs E rs H m m' x HF Hx Hn. unfold aview, mbyte. rewrite HF; [reflexivity|].
  rewrite unsigned_lit_small by lia. exact Hn.
Qed.

Lemma mw_not_wr1 : forall (E : env) (n : nat) b lo hi wlo whi cs x,
  bv_unsigned (ew E n) = b -> ~ (b + wlo <= x < b + whi) ->
  ~ in_wrange E [YP09.mkRegion (Some n) lo hi wlo whi cs] x.
Proof.
  intros E n b lo hi wlo whi cs x Hb Hx (r & [<- | []] & Hr).
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite Hb in Hr. exact (Hx Hr).
Qed.

Lemma mwE_sv0 : forall ms n (r : bv 5) v, Z.of_nat n = bv_unsigned r -> getr (ms_regs ms) r = w64 v ->
  sv_denot (mwE ms []) (SOff n 0) = Z_to_bv 64 v.
Proof. intros ms n r v Hn H. rewrite (mwE_sv ms [] n r Hn). exact H. Qed.

Lemma mwE_svc : forall ms n (r : bv 5) v c, Z.of_nat n = bv_unsigned r -> getr (ms_regs ms) r = w64 v ->
  0 <= v < 2 ^ 64 -> sv_denot (mwE ms []) (SOff n c) = Z_to_bv 64 (v + c).
Proof.
  intros ms n r v c Hn H Hv. cbn [sv_denot]. rewrite (mwE_reg ms [] n r Hn), H. unfold w64.
  rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Lemma mwE_U : forall ms n (r : bv 5) v, Z.of_nat n = bv_unsigned r -> getr (ms_regs ms) r = w64 v -> 0 <= v < 2 ^ 64 ->
  bv_unsigned (ew (mwE ms []) n) = v.
Proof. intros ms n r v Hn H Hv. rewrite (mwE_reg ms [] n r Hn), H. unfold w64. apply unsigned_lit_small. exact Hv. Qed.

Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : SEGS = tfibsegs.
Hypothesis LV : LinkVals.
Hypothesis MFF8 : aset_shadow_realizes SEGS B (pa_sigma LS___asan_set_shadow_f8) 0xf8.
Hypothesis TALK : forall rlo rhi, talk_acontract SK SEGS rlo rhi B.
(* meta_fill_00 (0x55e74): lib/A/Rt/SetShadow.v link_set_shadow_00 *)
Hypothesis MF00 : aset_shadow_realizes SEGS B (pa_sigma LS___asan_set_shadow_00) 0x00.
(* checked_memset (0x53214), checked_memcpy (0x52d78): lib/A/AE2r.v *)
Hypothesis AMSET : aintrin_realizes SEGS B OSet (pa_sigma LS___asan_memset).
Hypothesis AMCPY : aintrin_realizes SEGS B OCpy (pa_sigma LS___asan_memcpy).
Hypothesis EXIT : mw_exit_obl SK B.
Set Default Proof Using "All".

Section c.
Variables (cx : mwcx) (fpos : Z) (sn sa : list byte) (tab : list (list byte * Z)) (kbs : list byte).
Hypothesis HPX : mw_pre SK B cx.
Hypothesis HNK : anlk_at SEGS (mw_m0 cx) LA_G_NL kbs.
Hypothesis HIT : aiftab_at SEGS (mw_m0 cx) LA_G_NL kbs tab.
Hypothesis HSN : acstr_at SEGS (mw_m0 cx) (mw_name cx) sn.
Hypothesis Hn0 : mw_name cx <> 0.
Hypothesis Hsn : sn <> [].
Hypothesis HSA : acstr_at SEGS (mw_m0 cx) (mw_alias cx) sa.
Hypothesis Ha0 : mw_alias cx <> 0.
Hypothesis HAL : Z.of_nat (length sa) < ALIAS_MAX.
Hypothesis Hidx : index_of tab sn <> 0.

#[local] Notation F := (mw_F cx fpos).
#[local] Notation SH := (mw_SH cx fpos).
#[local] Notation RQ := (mw_F cx fpos + 32).
#[local] Notation LEN := (32 + nl_align (RTA_HDR + Z.of_nat (length sa))).
#[local] Notation V := (Z.of_nat (length sa)).
#[local] Notation IDX := (index_of tab sn).

Lemma mw_L : 0 <= V < 256 /\ 36 <= LEN <= 292 /\ 36 + V <= LEN.
Proof. unfold ALIAS_MAX in HAL. unfold nl_align, RTA_HDR. lia. Qed.

Lemma mw_idx_rng : 0 <= IDX < 2 ^ 31.
Proof. apply mw_index_rng. intros i n ix Hi. destruct HIT as (_ & _ & E). exact (proj1 (E i n ix Hi)). Qed.

(* the request's shadow is in scope: 0 at F's shadow bytes 4 .. 67 *)
Definition SHZ (W : world SEGS) (m : word -> option byte) : Prop :=
  forall j, 4 <= j < 68 -> aview SEGS (w_H W) m (SH + j) = Some 0.

(* the request before checked_memcpy: all but the alias's bytes *)
Definition RQ0 (W : world SEGS) (m : word -> option byte) : Prop :=
  val_mem SEGS (rdW W m) RQ 4 LEN /\ val_mem SEGS (rdW W m) (RQ + 4) 4 327696 /\
  val_mem SEGS (rdW W m) (RQ + 8) 4 1 /\
  (forall i, 12 <= i < 20 -> mbyte SEGS (rdW W m) (RQ + i) = Some (zb 0)) /\
  val_mem SEGS (rdW W m) (RQ + 20) 4 IDX /\
  (forall i, 24 <= i < 32 -> mbyte SEGS (rdW W m) (RQ + i) = Some (zb 0)) /\
  val_mem SEGS (rdW W m) (RQ + 32) 2 (V + 4) /\ val_mem SEGS (rdW W m) (RQ + 34) 2 20 /\
  (forall i, 36 + V <= i < LEN -> mbyte SEGS (rdW W m) (RQ + i) = Some (zb 0)).

(* the frame facts at a cut *)
Lemma mw_Ff : forall (X : Z -> Prop) ly S W ms md, mw_base SK B cx fpos X ly S W ms md ->
  4096 <= F /\ F + 1024 <= alloc_ceiling /\ F mod 64 = 0 /\ (F + 1024 <= kLowMemEnd \/ kHighMemBeg <= F) /\
  SH = SHADOW_OFF + F / 8 /\ frame_addr ly MW_CID fpos = F /\ 0 <= fpos < fs_frames MW_CID /\
  ~ In (MW_CID, fpos) (frames (mw_Sc cx)) /\ In (MW_CID, fpos) (frames S) /\
  (forall a, F <= a < F + 1024 -> apresent (w_H W) (ms_mem ms) a) /\
  (forall a, SH <= a < SH + 128 -> apresent (w_H W) (ms_mem ms) a).
Proof.
  intros X ly S W ms md HB.
  destruct (mw_side_facts SK B LAWS TB HSEGS cx fpos X ly S W ms md HPX HB)
    as (F1 & F2 & F3 & F4 & _ & _ & ESH & EF & _ & HFp & HSp & _).
  destruct (mw_cut_facts SK B LAWS TB HSEGS cx fpos X ly S W ms md HPX HB)
    as (_ & _ & _ & _ & _ & _ & _ & Hin & Hfpos & Hnin & _).
  unfold MW_FB in *. unfold MW_SHN in HSp.
  split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [reflexivity|].
  split; [exact EF|]. split; [exact Hfpos|]. split; [exact Hnin|]. split; [exact Hin|].
  split; [intros a Ha; exact (proj1 (HFp a Ha)) | exact HSp].
Qed.

Lemma mw_F8 : forall (X : Z -> Prop) ly S W ms md, mw_base SK B cx fpos X ly S W ms md -> F mod 8 = 0.
Proof.
  intros X ly S W ms md HB. destruct (mw_Ff X ly S W ms md HB) as (_ & _ & F3 & _).
  apply Z.mod_divide; [lia|]. apply Z.mod_divide in F3; [|lia]. destruct F3 as [q Hq]. exists (8 * q). lia.
Qed.

(* the request's bytes are frame bytes the journal lets the call write *)
Lemma mw_awr_F : forall (X : Z -> Prop) ly S W ms md a, mw_base SK B cx fpos X ly S W ms md -> F <= a < F + 1024 ->
  awr_byte (mw_STK cx) (mw_sp0 cx) (mw_FP cx) (ablocks B (mw_ly cx) (mw_S cx)) (ablocks B ly S) ly
    ((MW_CID, fpos) :: mw_own cx) a /\ ~ (mw_sp0 cx <= a < mw_sp0 cx + mw_XO cx).
Proof.
  intros X ly S W ms md a HB Ha. destruct (mw_Ff X ly S W ms md HB) as (_ & _ & _ & _ & _ & EF & _).
  apply (aj_gx_awr_frame SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MW_CID fpos a
           (mw_base_jx SK B cx fpos X ly S W ms md HB) (or_introl eq_refl)).
  left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF. change (fs_frame_bytes MW_CID) with 1024. exact Ha.
Qed.

(* SHZ survives a step that writes no byte of F's shadow *)
Lemma mw_shz_keep : forall (W : world SEGS) m m' (X : Z -> Prop),
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  (forall a, X a -> ~ (SH + 4 <= a < SH + 68)) -> 0 <= SH -> SH + 68 <= 2 ^ 64 -> SHZ W m -> SHZ W m'.
Proof.
  intros W m m' X UN HX H0 H1 HS j Hj. rewrite UN; [exact (HS j Hj) | lia |]. intros Hx. exact (HX _ Hx ltac:(lia)).
Qed.

(* ==========================================================================
   CPY: checked_memcpy(req + 36, alias, |alias|), then the RQ cut
   ========================================================================== *)
Lemma mw_cpy : forall ly S W (R : bvmap 5 word) m md,
  mw_base SK B cx fpos NoX ly S W (mkst R (Z_to_bv 64 (pa_sigma LS___asan_memcpy)) m (seg_rom SEGS)) md ->
  getr R 1 = Z_to_bv 64 (BASE + MW_RQ) ->
  getr R 10 = w64 (RQ + 36) -> getr R 11 = w64 (mw_alias cx) -> getr R 12 = w64 V ->
  getr R 25 = w64 RQ -> getr R 26 = w64 LEN ->
  SHZ W m -> RQ0 W m ->
  SRr SEGS W (mkCfg (mkst R (Z_to_bv 64 (pa_sigma LS___asan_memcpy)) m (seg_rom SEGS)) md) (mw_post SK B cx).
Proof.
  intros ly S W R m md HB Hra R10 R11 R12 R25 R26 HSZ HRQ.
  set (ms := mkst R (Z_to_bv 64 (pa_sigma LS___asan_memcpy)) m (seg_rom SEGS)) in *.
  pose proof (mw_sp_facts SK B LAWS TB HSEGS cx HPX) as HSPF.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK : MODEL_WRITE_AK = 8416) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
  destruct mw_L as (HL & Hlen & HLV).
  destruct (mw_Ff NoX ly S W ms md HB) as (F1 & F2 & F3 & F4 & ESH & EF & Hfpos & Hnin & Hin & HFp & HSp).
  pose proof (mw_base_jx SK B cx fpos NoX ly S W ms md HB) as HJ.
  pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  pose proof (mw_base_sp SK B LAWS TB HSEGS cx fpos NoX ly S W ms md HPX HB) as Hsp. change (ms_regs ms) with R in Hsp.
  pose proof HB as HB0. unfold mw_base in HB0. cbv zeta in HB0.
  destruct HB0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R19 & _ & R3 & R4 & _).
  change (ms_regs ms) with R in R3, R4.
  pose proof HPX as (HAPRE & HRD & HP).
  assert (HGx : gx_ok SEGS B (mw_G cx)) by (unfold apre in HAPRE; tauto).
  pose proof HP as (mbs0 & kbs0 & tab0 & nm0 & al0 & _ & _ & _ & _ & _ & _ & HAL0 & _ & _ & _ & _ & HAS0 & _).
  assert (Eal : al0 = Some sa)
    by (apply (mw_astr_arg_unique SEGS (mw_m0 cx) (mw_alias cx)); [exact HAL0 | split; assumption]).
  destruct (HAS0 sa Eal) as (Hl32 & Hmra & Hraa & Hhva & Hafr & _).
  assert (Hakba : forall a, mw_alias cx <= a < mw_alias cx + (V + 1) ->
     akb SEGS B (mw_lyc cx) (mw_Sc cx) (mw_sp cx - MODEL_WRITE_AK) (mw_sp cx) a).
  { intros a Ha. apply HRD. right; left. split; [exact Ha0|]. exists sa. split; [exact HSA | unfold mw_alias in Ha; lia]. }
  assert (Hal1 : 0 < mw_alias cx /\ mw_alias cx + V + 1 <= 2 ^ 47 - 1).
  { pose proof HSA as ((H0 & _ & _) & _). pose proof Ha0 as Ha0'.
    unfold mw_alias in *. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hmra. lia. }
  destruct (mw_shadow_at SK B LAWS TB HSEGS cx fpos ly S W ms md (mw_alias cx) (V + 1) HPX HB ltac:(lia) Hakba Hraa Hhva)
    as (Hra3 & Hhv3).
  change (ms_mem ms) with m in Hra3, Hhv3, HFp, HSp.
  assert (HVA : forall a, mw_alias cx <= a < mw_alias cx + (V + 1) ->
            aview SEGS (w_H W) m a = aview SEGS (w_H (mw_W cx)) (mw_memc cx) a).
  { intros a Ha. exact (mw_view_akb SK B LAWS TB HSEGS cx fpos ly S W ms md a HPX HB (Hakba a Ha)). }
  assert (Hvis : forall i, (i < length sa)%nat ->
            mbyte SEGS (rdW (mw_W cx) (mw_memc cx)) (mw_alias cx + Z.of_nat i) = nth_error sa i).
  { intros i Hi. pose proof HSA as ((_ & _ & Hb) & _).
    change (rdW (mw_W cx) (mw_memc cx)) with (mw_m0 cx). rewrite (Hb i ltac:(rewrite length_app; cbn [length]; lia)).
    rewrite nth_error_app1 by exact Hi. reflexivity. }
  eapply SRr_bind.
  { apply (aj_gx_intrin_at SK SEGS B LAWS pa_segs_low OCpy (pa_sigma LS___asan_memcpy) AMCPY
      (mw_G cx) (mw_XO cx) (mw_OUT cx) W R m (mw_STK cx) (mw_sp0 cx) (mw_FP cx) (mw_ly cx) (mw_S cx)
      (mw_W0 cx) (mw_mem0 cx) (mw_md0 cx) ((MW_CID, fpos) :: mw_own cx) ly S md (mw_k cx)
      (RQ + 36) (mw_alias cx) V (getr R 1)).
    - exact HGx.
    - exact HJ.
    - exact R10.
    - exact R11.
    - exact R12.
    - lia.
    - lia.
    - lia.
    - rewrite Hsp. lia.
    - rewrite Hsp, Hes. unfold mw_sp in *. lia.
    - rewrite Hsp. unfold mw_sp in *. lia.
    - rewrite R3. pose proof HAPRE as (_ & _ & _ & _ & _ & Hgp & _). exact Hgp.
    - rewrite R4. pose proof HAPRE as (_ & _ & _ & _ & _ & _ & Htp & _). exact Htp.
    - reflexivity.
    - rewrite Hra. apply ret_ok_codeptr_v; [unfold MW_RQ, AF_model_write; lia | reflexivity].
    - intros a Ha. left. destruct (mw_awr_F NoX ly S W ms md a HB ltac:(lia)) as [H1 H2].
      split; [exact H1|]. split; [exact H2|]. rewrite Hsp, Hes. unfold mw_sp in *. lia.
    - unfold amem_range. destruct F4; [left | right]; unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia.
    - exact (mw_req_ra (aview SEGS (w_H W) m) F (RQ + 36) V (mw_F8 NoX ly S W ms md HB) ltac:(lia)
        ltac:(intros j Hj; exact (HSZ j Hj)) ltac:(lia) ltac:(lia)).
    - intros Hpos. apply (shadow_hull_vis_of_frame SEGS B LAWS ly S W m md MW_CID fpos (RQ + 36) V HAR Hin);
        rewrite ?EF; change (fs_frame_bytes MW_CID) with 1024; lia.
    - cbv beta iota.
      split; [lia|].
      split; [lia|].
      split.
      { intros a Ha. split.
        - rewrite (HVA a ltac:(lia)).
          replace a with (mw_alias cx + Z.of_nat (Z.to_nat (a - mw_alias cx))) by lia.
          pose proof (Hvis (Z.to_nat (a - mw_alias cx)) ltac:(lia)) as Hv1.
          rewrite (mwc_nth_some _ _ (Z_to_bv 8 0)) in Hv1 by lia.
          exact (mw_aview_some SEGS _ _ _ _ Hv1).
        - rewrite Hsp, Hes. unfold apart_frame, mw_sp, mw_alias in *. lia. }
      split.
      { destruct (Z_le_gt_dec (RQ + 36 + V) (mw_alias cx)) as [Hle | Hgt]; [left; exact Hle|].
        destruct (Z_le_gt_dec (mw_alias cx + V) (RQ + 36)) as [Hle2 | Hgt2]; [right; exact Hle2|].
        exfalso. pose proof (Hakba (Z.max (mw_alias cx) (RQ + 36)) ltac:(lia)) as Hk.
        assert (HE : ~ (NoX (Z.max (mw_alias cx) (RQ + 36)) \/
                        aside_rng (mw_lyc cx) MW_CID fpos (Z.max (mw_alias cx) (RQ + 36)))).
        { intros [[] | HS']. revert HS'. pose proof (@pa_img_range _ link_listing PI) as HIMG.
          pose proof (mw_pre_jc SK B cx HPX) as HJc.
          eapply (akb_not_side SK SEGS B).
          all: first [ exact LAWS | exact TB | exact HIMG | exact HJc | (unfold MW_CID; lia) | exact Hfpos | exact Hnin
                     | exact Hk ]. }
        apply HE. right. left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes MW_CID) with 1024.
        change (frame_addr (mw_lyc cx) MW_CID fpos) with F. lia. }
      split; [unfold amem_range in *; unfold mw_alias in *; unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia|].
      split; [exact (mw_ra_sub _ (mw_alias cx) (V + 1) (mw_alias cx) V Hra3 ltac:(lia) ltac:(lia))|].
      intros Hpos. exact (mw_hull_sub _ (mw_alias cx) (V + 1) (mw_alias cx) V Hhv3 ltac:(lia) Hpos ltac:(lia) ltac:(lia)). }
  (* the return of checked_memcpy: the RQ cut *)
  intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & H10 & HCP & UN & HPR & HSBM).
  rewrite Hra.
  assert (Hfd2 : m_fds md2 = m_fds md /\ m_fs md2 = m_fs md) by exact (mw_sbm_fds2 _ _ HSBM).
  set (ms2 := mkst regs2 (Z_to_bv 64 (BASE + MW_RQ)) mem2 (seg_rom SEGS)).
  assert (HB2 : mw_base SK B cx fpos NoX ly S W ms2 md2).
  { apply (mw_base_step SK B LAWS TB HSEGS cx fpos NoX ly S W ms md ly S W ms2 md2 (mw_sp1 cx - ESTACK) (mw_sp1 cx)
             (fun a => RQ + 36 <= a < RQ + 36 + V) HPX HB); try reflexivity.
    - exact HJ2.
    - unfold mw_base in HB. cbv zeta in HB. tauto.
    - unfold mw_base in HB. cbv zeta in HB. tauto.
    - apply (mw_akept_un SK B LAWS TB HSEGS ly S W m md mem2 _ _ _ HAR); [lia | lia | | | ].
      + intros a Ha. apply (aj_gx_present SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
        unfold mw_sp in *. lia.
      + intros a Ha Hn Hw. apply UN; [exact Ha | exact Hn | rewrite Hsp; exact Hw].
      + intros a _ Hp. exact (HPR a Hp).
    - rewrite Hes. unfold mw_sp in *. lia.
    - intros a Ha. right. left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes MW_CID) with 1024.
      change (frame_addr (mw_lyc cx) MW_CID fpos) with F. cbv beta in Ha. lia.
    - intros a Ha Hs. cbv beta in Hs. unfold mw_sp in *. lia.
    - intros a Ha Hs. cbv beta in Hs. unfold MW_FLAGPTR in Ha. lia.
    - exact (mw_rsame_of_pres SK B LAWS TB HSEGS _ _ HP2).
    - exact (proj1 Hfd2).
    - exact (proj2 Hfd2). }
  assert (UN' : forall a, 0 <= a < 2 ^ 64 -> ~ (RQ + 36 <= a < RQ + 36 + V) -> ~ (mw_sp1 cx - ESTACK <= a < mw_sp1 cx) ->
            aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) m a).
  { intros a Ha H1 H2. apply UN; [exact Ha | exact H1 | rewrite Hsp; exact H2]. }
  apply (mw_rq SK B LAWS TB HSEGS LV MFF8 TALK EXIT cx fpos ly S W ms2 md2 HPX).
  unfold ms2 in HB2 |- *. cbn [ms_mem ms_regs ms_pc_val] in HB2 |- *.
  exists sn, sa, tab, kbs.
  split; [reflexivity|].
  split; [exact HNK|]. split; [exact HIT|]. split; [exact HSN|]. split; [exact Hn0|]. split; [exact Hsn|].
  split; [exact HSA|]. split; [exact Ha0|]. split; [exact HAL|]. split; [exact Hidx|].
  split; [etransitivity; [exact (HP2 25 ltac:(unfold acallee_saved; lia)) | exact R25]|].
  split; [etransitivity; [exact (HP2 26 ltac:(unfold acallee_saved; lia)) | exact R26]|].
  split.
  { destruct HRQ as (V0 & V4 & V8 & Z12 & V20 & Z24 & V32 & V34 & ZT).
    assert (KM : forall a, RQ <= a < RQ + 292 -> ~ (RQ + 36 <= a < RQ + 36 + V) ->
      mbyte SEGS (rdW W mem2) a = mbyte SEGS (rdW W m) a).
    { intros a Ha Hn. apply (mbyte_of_aview_eq SEGS _ _ _ _ a a). apply UN'; [lia | exact Hn |].
      unfold mw_sp in *. rewrite Hes. lia. }
    apply (mw_req_bytes SEGS (rdW W mem2) RQ IDX sa ltac:(lia) ltac:(lia) ltac:(lia)).
    - apply (mw_vm_keep _ _ _ _ _ _ V0); intros k Hk; apply KM; lia.
    - apply (mw_vm_keep _ _ _ _ _ _ V4); intros k Hk; apply KM; lia.
    - apply (mw_vm_keep _ _ _ _ _ _ V8); intros k Hk; apply KM; lia.
    - intros i Hi. rewrite KM by lia. apply Z12; lia.
    - apply (mw_vm_keep _ _ _ _ _ _ V20); intros k Hk; apply KM; lia.
    - intros i Hi. rewrite KM by lia. apply Z24; lia.
    - apply (mw_vm_keep _ _ _ _ _ _ V32); intros k Hk; apply KM; lia.
    - apply (mw_vm_keep _ _ _ _ _ _ V34); intros k Hk; apply KM; lia.
    - intros i Hi. rewrite <- (Hvis i Hi).
      apply (mbyte_of_aview_eq SEGS _ _ _ _ _ _).
      rewrite (HCP (Z.of_nat i) ltac:(lia)). exact (HVA (mw_alias cx + Z.of_nat i) ltac:(lia)).
    - intros i Hi. rewrite KM by lia. apply ZT; lia. }
  split.
  { intros j Hj. rewrite UN'; [exact (HSZ j Hj) | unfold SHADOW_OFF in *; lia | | ].
    - unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg in *. rewrite ESH. destruct F4; lia.
    - rewrite ESH. unfold SHADOW_OFF, mw_sp in *. lia. }
  exact HB2.
Qed.


(* ==========================================================================
   S3: the header stores, to the call of checked_memcpy
   ========================================================================== *)
Definition mw_RQR : YP09.region := YP09.mkRegion (Some 25%nat) 0 36 0 36 [YP09.mkChunk 12 (CZero 24)].

Lemma mw_s3 : forall ly S W (R : bvmap 5 word) m md,
  mw_base SK B cx fpos NoX ly S W (mkst R (Z_to_bv 64 (BASE + MW_S3)) m (seg_rom SEGS)) md ->
  getr R 22 = w64 IDX -> getr R 24 = w64 V -> getr R 25 = w64 RQ -> getr R 26 = w64 LEN ->
  SHZ W m -> (forall i, 0 <= i < LEN -> mbyte SEGS (rdW W m) (RQ + i) = Some (zb 0)) ->
  SRr SEGS W (mkCfg (mkst R (Z_to_bv 64 (BASE + MW_S3)) m (seg_rom SEGS)) md) (mw_post SK B cx).
Proof.
  intros ly S W R m md HB R22 R24 R25 R26 HSZ HZ.
  set (ms := mkst R (Z_to_bv 64 (BASE + MW_S3)) m (seg_rom SEGS)) in *.
  pose proof (mw_sp_facts SK B LAWS TB HSEGS cx HPX) as HSPF.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK : MODEL_WRITE_AK = 8416) by reflexivity.
  destruct mw_L as (HL & Hlen & HLV). pose proof mw_idx_rng as HIR.
  destruct (mw_Ff NoX ly S W ms md HB) as (F1 & F2 & F3 & F4 & ESH & EF & Hfpos & Hnin & Hin & HFp & HSp).
  change (ms_mem ms) with m in HFp, HSp.
  pose proof (mw_base_jx SK B cx fpos NoX ly S W ms md HB) as HJ.
  pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  pose proof HPX as (HAPRE & _ & _).
  assert (HGx : gx_ok SEGS B (mw_G cx)) by (unfold apre in HAPRE; tauto).
  pose proof (mw_base_X SK B LAWS TB HSEGS cx fpos NoX ly S W ms md HB) as R19.
  assert (U25 : bv_unsigned (ew (mwE ms []) 25) = RQ) by (apply (mwE_U ms 25 25%bv); [reflexivity | exact R25 | lia]).
  assert (HEI : img_env VAL A_LIM (mwE ms [])) by apply Eimg_env.
  assert (Hrms : restrict (w_H W) ms = mkst R (Z_to_bv 64 (BASE + MW_S3)) (rdW W m) (seg_rom SEGS))
    by (unfold ms; rewrite restrict_mkst_fx; reflexivity).
  assert (HS : st_ok_pi SEGS VAL (mwE ms []) (mkSS MW_S3 sr_atoms [mw_RQR] None (mkFacts [] [] []))
                 (restrict (w_H W) ms)).
  { rewrite Hrms. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute; reflexivity.
    - apply Forall_cons; [|apply Forall_nil].
      unfold region_ok, mw_RQR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U25. split; [lia|]. split; [lia|]. split.
      + intros o Ho. apply (YCbq.apresent_writable SEGS). apply HFp. lia.
      + apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. intros i Hi.
        replace (RQ + 12 + i) with (RQ + (12 + i)) by lia. apply HZ. lia.
    - cbn [pairwise_disjoint all_disjoint]. split; exact I.
    - split; [exact I | split; exact I]. }
  pose (RUNC := paj_run_call_plain_x SK B LAWS (mw_G cx) HGx (mw_XO cx) (mw_OUT cx)).
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ev ?ssx (restrict (w_H ?Wx) ?msx) =>
    lazymatch type of RUNC with context [sym_runN_pi ?tpi _ _] =>
      let r := eval vm_compute in (sym_runN_pi tpi FUEL ssx) in
      lazymatch r with (?ssf, PRS_call ?sf) =>
        let Hrun := fresh "Hrun" in
        assert (Hrun : sym_runN_pi tpi FUEL ssx = (ssf, PRS_call sf)) by (vm_compute; reflexivity);
        eapply (RUNC Wx FUEL Ev ssx ssf sf msx _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun HJ);
        clear Hrun
      end
    end
  end.
  { cbn [ss_mem]. apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros a Ha. unfold mw_RQR in Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U25 in Ha.
    left. exact (mw_awr_F NoX ly S W ms md a HB ltac:(lia)). }
  cbv beta. intros ms' mat' HS' HJ' HF HF' HG'. cbn [ms_mem mkst] in HF, HF', HG'.
  pose proof (st_ok_restrict_mkst SEGS (w_H W) _ _ ms' HS' eq_refl) as Ems. cbn [ss_pc setpc] in Ems.
  sreg HS' (1%bv : bv 5) Q1. sreg HS' (10%bv : bv 5) Q10. sreg HS' (11%bv : bv 5) Q11. sreg HS' (12%bv : bv 5) Q12.
  sreg HS' (22%bv : bv 5) Q22. sreg HS' (24%bv : bv 5) Q24. sreg HS' (25%bv : bv 5) Q25. sreg HS' (26%bv : bv 5) Q26.
  sregion HS' 0%nat HR2.
  assert (HR' : mw_rsame (ms_regs ms) (ms_regs ms')) by (unfold mw_rsame; mwc_rsame HS' ms).
  set (md' := with_vm_backing (m_vm_lazy md) mat' md) in *.
  (* the run wrote the request's first 36 bytes only *)
  assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (RQ <= a < RQ + 36) ->
    aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) m a).
  { intros a Ha Hn. exact (mw_frame_aview SEGS _ _ (w_H W) m (ms_mem ms') a HF' Ha
      (mw_not_wr1 _ 25 RQ 0 36 0 36 _ a U25 ltac:(lia))). }
  destruct (mw_shape_of SEGS ms' _ _ _ Ems) as (Sh1 & Sh2 & Sh3 & Sh4 & Sh5).
  pose proof HB as HB00. unfold mw_base in HB00. cbv zeta in HB00.
  destruct HB00 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HfS0 & Hperm0 & _).
  assert (HB' : mw_base SK B cx fpos NoX ly S W ms' md').
  { apply (mw_base_step SK B LAWS TB HSEGS cx fpos NoX ly S W ms md ly S W ms' md' (mw_sp1 cx) (mw_sp1 cx)
             (fun a => RQ <= a < RQ + 36) HPX HB Sh1 Sh2 Sh3 Sh4 Sh5 HJ' eq_refl HfS0 Hperm0).
    - apply (mw_akept_un SK B LAWS TB HSEGS ly S W m md (ms_mem ms') _ _ _ HAR); [lia | lia | intros a Ha; lia | | ].
      + intros a Ha Hn _. exact (UN a Ha Hn).
      + intros a _ Hp. exact (apresent_grows _ _ _ a HG' Hp).
    - unfold mw_sp in *. lia.
    - lia.
    - intros a Ha. right. left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes MW_CID) with 1024.
      change (frame_addr (mw_lyc cx) MW_CID fpos) with F. cbv beta in Ha. lia.
    - intros a Ha Hs. cbv beta in Hs. unfold mw_sp in *. lia.
    - intros a Ha Hs. cbv beta in Hs. unfold MW_FLAGPTR in Ha. lia.
    - exact HR'.
    - exact (proj1 (wvb_fds_fs (m_vm_lazy md) mat' md)).
    - exact (proj2 (wvb_fds_fs (m_vm_lazy md) mat' md)). }
  assert (E22 : ew (mwE ms []) 22 = Z_to_bv 64 IDX) by exact (eq_trans (mwE_reg ms [] 22 22%bv eq_refl) R22).
  assert (E24 : ew (mwE ms []) 24 = Z_to_bv 64 V) by exact (eq_trans (mwE_reg ms [] 24 24%bv eq_refl) R24).
  assert (E26 : ew (mwE ms []) 26 = Z_to_bv 64 LEN) by exact (eq_trans (mwE_reg ms [] 26 26%bv eq_refl) R26).
  (* the request's bytes the region's chunks give, and its tail kept *)
  assert (HRQ0 : RQ0 W (ms_mem ms')).
  { split.
    { pose proof (YC4b.field_of_region (segs := SEGS) _ _ 25 RQ _ 0 36 0 36 0 4%N (SOff 26 0) LEN
       HR2 U25 ltac:(cbn; repeat (first [left; reflexivity | right])) (mwE_sv0 ms 26 26%bv LEN eq_refl R26)
       ltac:(cbn; lia) ltac:(cbn; lia)) as VL.
      rewrite Z.add_0_r in VL. exact VL. }
    split; [exact (YC4b.field_of_region (segs := SEGS) _ _ 25 RQ _ 0 36 0 36 4 4%N (SLit 327696) 327696
       HR2 U25 ltac:(cbn; repeat (first [left; reflexivity | right])) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    split; [exact (YC4b.field_of_region (segs := SEGS) _ _ 25 RQ _ 0 36 0 36 8 4%N (SLit 1) 1
       HR2 U25 ltac:(cbn; repeat (first [left; reflexivity | right])) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    split.
    { intros i Hi. pose proof (mw_zero_of_region SEGS _ _ _ RQ 12 8 (i - 12) HR2 ltac:(cbn [YP09.r_base base_val]; exact U25)
        ltac:(cbn; repeat (first [left; reflexivity | right])) ltac:(lia)) as Hz.
      replace (RQ + 12 + (i - 12)) with (RQ + i) in Hz by lia. exact Hz. }
    split; [exact (YC4b.field_of_region (segs := SEGS) _ _ 25 RQ _ 0 36 0 36 20 4%N (SOff 22 0) IDX
       HR2 U25 ltac:(cbn; repeat (first [left; reflexivity | right])) (mwE_sv0 ms 22 22%bv IDX eq_refl R22)
       ltac:(cbn; lia) ltac:(cbn; lia))|].
    split.
    { intros i Hi. pose proof (mw_zero_of_region SEGS _ _ _ RQ 24 8 (i - 24) HR2 ltac:(cbn [YP09.r_base base_val]; exact U25)
        ltac:(cbn; repeat (first [left; reflexivity | right])) ltac:(lia)) as Hz.
      replace (RQ + 24 + (i - 24)) with (RQ + i) in Hz by lia. exact Hz. }
    split; [exact (YC4b.field_of_region (segs := SEGS) _ _ 25 RQ _ 0 36 0 36 32 2%N (SOff 24 4) (V + 4)
       HR2 U25 ltac:(cbn; repeat (first [left; reflexivity | right])) (mwE_svc ms 24 24%bv V 4 eq_refl R24 ltac:(lia))
       ltac:(cbn; lia) ltac:(cbn; lia))|].
    split; [exact (YC4b.field_of_region (segs := SEGS) _ _ 25 RQ _ 0 36 0 36 34 2%N (SLit 20) 20
       HR2 U25 ltac:(cbn; repeat (first [left; reflexivity | right])) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    intros i Hi. rewrite (mbyte_of_aview_eq SEGS (w_H W) (w_H W) m (ms_mem ms') (RQ + i) (RQ + i)
      (UN (RQ + i) ltac:(lia) ltac:(lia))). apply HZ. lia. }
  rewrite Ems.
  apply (mw_cpy ly S W (ms_regs ms') (ms_mem ms') md').
  - rewrite <- Ems. exact HB'.
  - rewrite Q1. exact (codeptr_val _ _ HEI).
  - rewrite Q10. exact (mwE_svc ms 25 25%bv RQ 36 eq_refl R25 ltac:(lia)).
  - rewrite Q11. exact (eq_trans (mwE_sv ms [] 19 19%bv eq_refl) R19).
  - rewrite Q12. exact (mwE_sv0 ms 24 24%bv V eq_refl R24).
  - rewrite Q25. exact (mwE_sv0 ms 25 25%bv RQ eq_refl R25).
  - rewrite Q26. exact (mwE_sv0 ms 26 26%bv LEN eq_refl R26).
  - apply (mw_shz_keep W m (ms_mem ms') (fun a => RQ <= a < RQ + 36) UN).
    + intros a Ha. cbv beta in Ha. rewrite ESH. unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg in *. destruct F4; lia.
    + rewrite ESH. unfold SHADOW_OFF. lia.
    + rewrite ESH. unfold SHADOW_OFF. lia.
    + exact HSZ.
  - exact HRQ0.
Qed.

(* ==========================================================================
   SET: checked_memset(req, 0, len), then S3
   ========================================================================== *)
Lemma mw_set : forall ly S W (R : bvmap 5 word) m md,
  mw_base SK B cx fpos NoX ly S W (mkst R (Z_to_bv 64 (pa_sigma LS___asan_memset)) m (seg_rom SEGS)) md ->
  getr R 1 = Z_to_bv 64 (BASE + MW_S3) ->
  getr R 10 = w64 RQ -> getr R 11 = w64 0 -> getr R 12 = w64 LEN ->
  getr R 22 = w64 IDX -> getr R 24 = w64 V -> getr R 25 = w64 RQ -> getr R 26 = w64 LEN ->
  SHZ W m ->
  SRr SEGS W (mkCfg (mkst R (Z_to_bv 64 (pa_sigma LS___asan_memset)) m (seg_rom SEGS)) md) (mw_post SK B cx).
Proof.
  intros ly S W R m md HB Hra R10 R11 R12 R22 R24 R25 R26 HSZ.
  set (ms := mkst R (Z_to_bv 64 (pa_sigma LS___asan_memset)) m (seg_rom SEGS)) in *.
  pose proof (mw_sp_facts SK B LAWS TB HSEGS cx HPX) as HSPF.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK : MODEL_WRITE_AK = 8416) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
  destruct mw_L as (HL & Hlen & HLV).
  destruct (mw_Ff NoX ly S W ms md HB) as (F1 & F2 & F3 & F4 & ESH & EF & Hfpos & Hnin & Hin & HFp & HSp).
  pose proof (mw_base_jx SK B cx fpos NoX ly S W ms md HB) as HJ.
  pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  pose proof (mw_base_sp SK B LAWS TB HSEGS cx fpos NoX ly S W ms md HPX HB) as Hsp. change (ms_regs ms) with R in Hsp.
  pose proof HB as HB0. unfold mw_base in HB0. cbv zeta in HB0.
  destruct HB0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R3 & R4 & _).
  change (ms_regs ms) with R in R3, R4.
  pose proof HPX as (HAPRE & _ & _).
  assert (HGx : gx_ok SEGS B (mw_G cx)) by (unfold apre in HAPRE; tauto).
  eapply SRr_bind.
  { apply (aj_gx_intrin_at SK SEGS B LAWS pa_segs_low OSet (pa_sigma LS___asan_memset) AMSET
      (mw_G cx) (mw_XO cx) (mw_OUT cx) W R m (mw_STK cx) (mw_sp0 cx) (mw_FP cx) (mw_ly cx) (mw_S cx)
      (mw_W0 cx) (mw_mem0 cx) (mw_md0 cx) ((MW_CID, fpos) :: mw_own cx) ly S md (mw_k cx)
      RQ 0 LEN (getr R 1)).
    - exact HGx.
    - exact HJ.
    - exact R10.
    - exact R11.
    - exact R12.
    - lia.
    - lia.
    - lia.
    - rewrite Hsp. lia.
    - rewrite Hsp, Hes. unfold mw_sp in *. lia.
    - rewrite Hsp. unfold mw_sp in *. lia.
    - rewrite R3. pose proof HAPRE as (_ & _ & _ & _ & _ & Hgp & _). exact Hgp.
    - rewrite R4. pose proof HAPRE as (_ & _ & _ & _ & _ & _ & Htp & _). exact Htp.
    - reflexivity.
    - rewrite Hra. apply ret_ok_codeptr_v; [unfold MW_S3, AF_model_write; lia | reflexivity].
    - intros a Ha. left. destruct (mw_awr_F NoX ly S W ms md a HB ltac:(lia)) as [H1 H2].
      split; [exact H1|]. split; [exact H2|]. rewrite Hsp, Hes. unfold mw_sp in *. lia.
    - unfold amem_range. destruct F4; [left | right]; unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia.
    - exact (mw_req_ra (aview SEGS (w_H W) m) F RQ LEN (mw_F8 NoX ly S W ms md HB) ltac:(lia)
        ltac:(intros j Hj; exact (HSZ j Hj)) ltac:(lia) ltac:(lia)).
    - intros Hpos. apply (shadow_hull_vis_of_frame SEGS B LAWS ly S W m md MW_CID fpos RQ LEN HAR Hin);
        rewrite ?EF; change (fs_frame_bytes MW_CID) with 1024; lia.
    - exact I. }
  intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & H10 & HCP & UN & HPR & HSBM).
  rewrite Hra.
  assert (Hfd2 : m_fds md2 = m_fds md /\ m_fs md2 = m_fs md) by exact (mw_sbm_fds2 _ _ HSBM).
  set (ms2 := mkst regs2 (Z_to_bv 64 (BASE + MW_S3)) mem2 (seg_rom SEGS)).
  assert (HB2 : mw_base SK B cx fpos NoX ly S W ms2 md2).
  { apply (mw_base_step SK B LAWS TB HSEGS cx fpos NoX ly S W ms md ly S W ms2 md2 (mw_sp1 cx - ESTACK) (mw_sp1 cx)
             (fun a => RQ <= a < RQ + LEN) HPX HB); try reflexivity.
    - exact HJ2.
    - unfold mw_base in HB. cbv zeta in HB. tauto.
    - unfold mw_base in HB. cbv zeta in HB. tauto.
    - apply (mw_akept_un SK B LAWS TB HSEGS ly S W m md mem2 _ _ _ HAR); [lia | lia | | | ].
      + intros a Ha. apply (aj_gx_present SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
        unfold mw_sp in *. lia.
      + intros a Ha Hn Hw. apply UN; [exact Ha | exact Hn | rewrite Hsp; exact Hw].
      + intros a _ Hp. exact (HPR a Hp).
    - rewrite Hes. unfold mw_sp in *. lia.
    - intros a Ha. right. left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes MW_CID) with 1024.
      change (frame_addr (mw_lyc cx) MW_CID fpos) with F. cbv beta in Ha. lia.
    - intros a Ha Hs. cbv beta in Hs. unfold mw_sp in *. lia.
    - intros a Ha Hs. cbv beta in Hs. unfold MW_FLAGPTR in Ha. lia.
    - exact (mw_rsame_of_pres SK B LAWS TB HSEGS _ _ HP2).
    - exact (proj1 Hfd2).
    - exact (proj2 Hfd2). }
  apply (mw_s3 ly S W regs2 mem2 md2 HB2).
  - etransitivity; [exact (HP2 22 ltac:(unfold acallee_saved; lia)) | exact R22].
  - etransitivity; [exact (HP2 24 ltac:(unfold acallee_saved; lia)) | exact R24].
  - etransitivity; [exact (HP2 25 ltac:(unfold acallee_saved; lia)) | exact R25].
  - etransitivity; [exact (HP2 26 ltac:(unfold acallee_saved; lia)) | exact R26].
  - intros j Hj. rewrite UN; [exact (HSZ j Hj) | rewrite ESH; unfold SHADOW_OFF in *; lia | | ].
    + rewrite ESH. unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg in *. destruct F4; lia.
    + rewrite Hsp, ESH. unfold SHADOW_OFF, mw_sp in *. lia.
  - intros i Hi. apply mw_mbyte0. rewrite (HCP i Hi). reflexivity.
Qed.

(* ==========================================================================
   S2: the request's length, to the call of checked_memset
   ========================================================================== *)
Lemma mw_s2 : forall ly S W (R : bvmap 5 word) m md,
  mw_base SK B cx fpos NoX ly S W (mkst R (Z_to_bv 64 (BASE + MW_S2)) m (seg_rom SEGS)) md ->
  getr R 22 = w64 IDX -> getr R 24 = w64 V -> getr R 25 = w64 RQ -> SHZ W m ->
  SRr SEGS W (mkCfg (mkst R (Z_to_bv 64 (BASE + MW_S2)) m (seg_rom SEGS)) md) (mw_post SK B cx).
Proof.
  intros ly S W R m md HB R22 R24 R25 HSZ.
  set (ms := mkst R (Z_to_bv 64 (BASE + MW_S2)) m (seg_rom SEGS)) in *.
  destruct mw_L as (HL & Hlen & HLV).
  pose proof (mw_base_jx SK B cx fpos NoX ly S W ms md HB) as HJ.
  pose proof HPX as (HAPRE & _ & _).
  assert (HGx : gx_ok SEGS B (mw_G cx)) by (unfold apre in HAPRE; tauto).
  pose proof (mw_Ff NoX ly S W ms md HB) as (F1 & F2 & _).
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (HEI : img_env VAL A_LIM (mwE ms [])) by apply Eimg_env.
  assert (Hrms : restrict (w_H W) ms = mkst R (Z_to_bv 64 (BASE + MW_S2)) (rdW W m) (seg_rom SEGS))
    by (unfold ms; rewrite restrict_mkst_fx; reflexivity).
  assert (HS : st_ok_pi SEGS VAL (mwE ms []) (mkSS MW_S2 sr_atoms [] None (mkFacts [] [] []))
                 (restrict (w_H W) ms)).
  { rewrite Hrms. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute; reflexivity.
    - constructor.
    - exact I.
    - split; [exact I | split; exact I]. }
  pose (RUNC := paj_run_call_plain_x SK B LAWS (mw_G cx) HGx (mw_XO cx) (mw_OUT cx)).
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ev ?ssx (restrict (w_H ?Wx) ?msx) =>
    lazymatch type of RUNC with context [sym_runN_pi ?tpi _ _] =>
      let r := eval vm_compute in (sym_runN_pi tpi FUEL ssx) in
      lazymatch r with (?ssf, PRS_call ?sf) =>
        let Hrun := fresh "Hrun" in
        assert (Hrun : sym_runN_pi tpi FUEL ssx = (ssf, PRS_call sf)) by (vm_compute; reflexivity);
        eapply (RUNC Wx FUEL Ev ssx ssf sf msx _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun HJ);
        clear Hrun
      end
    end
  end.
  { cbn [ss_mem]. apply awr_ok_x_nil. }
  cbv beta. intros ms' mat' HS' HJ' HF HF' HG'. cbn [ms_mem mkst] in HF, HF', HG'.
  assert (Hmem : ms_mem ms' = ms_mem ms).
  { apply functional_extensionality. intros x. apply HF. cbn [ss_mem]. intros (r0 & Hin & _). destruct Hin. }
  pose proof (st_ok_restrict_mkst SEGS (w_H W) _ _ ms' HS' eq_refl) as Ems. cbn [ss_pc setpc] in Ems.
  sreg HS' (1%bv : bv 5) Q1. sreg HS' (10%bv : bv 5) Q10. sreg HS' (11%bv : bv 5) Q11. sreg HS' (12%bv : bv 5) Q12.
  sreg HS' (22%bv : bv 5) Q22. sreg HS' (24%bv : bv 5) Q24. sreg HS' (25%bv : bv 5) Q25. sreg HS' (26%bv : bv 5) Q26.
  assert (HR' : mw_rsame (ms_regs ms) (ms_regs ms')) by (unfold mw_rsame; mwc_rsame HS' ms).
  assert (E24 : ew (mwE ms []) 24 = Z_to_bv 64 V) by exact (eq_trans (mwE_reg ms [] 24 24%bv eq_refl) R24).
  assert (DL : getr (ms_regs ms') 26 = w64 LEN) by (rewrite Q26; exact (mw_denot_len _ 24 V E24 HL)).
  set (md' := with_vm_backing (m_vm_lazy md) mat' md) in *.
  destruct (mw_shape_of SEGS ms' _ _ _ Ems) as (Sh1 & Sh2 & Sh3 & Sh4 & Sh5).
  assert (HB' : mw_base SK B cx fpos NoX ly S W ms' md')
    by exact (mw_base_nomemX SK B LAWS TB HSEGS cx fpos NoX ly S W ms md ms' md' HPX HB Hmem Sh1 Sh2 Sh3 Sh4 Sh5 HJ'
                (proj1 (wvb_fds_fs (m_vm_lazy md) mat' md)) (proj2 (wvb_fds_fs (m_vm_lazy md) mat' md)) HR').
  rewrite Ems.
  apply (mw_set ly S W (ms_regs ms') (ms_mem ms') md').
  - rewrite <- Ems. exact HB'.
  - rewrite Q1. exact (codeptr_val _ _ HEI).
  - rewrite Q10. exact (mwE_sv0 ms 25 25%bv RQ eq_refl R25).
  - rewrite Q11. reflexivity.
  - rewrite Q12, mw_denot_add0. exact (mw_denot_len _ 24 V E24 HL).
  - rewrite Q22. exact (mwE_sv0 ms 22 22%bv IDX eq_refl R22).
  - rewrite Q24. exact (mwE_sv0 ms 24 24%bv V eq_refl R24).
  - rewrite Q25. exact (mwE_sv0 ms 25 25%bv RQ eq_refl R25).
  - exact DL.
  - rewrite Hmem. exact HSZ.
Qed.

(* ==========================================================================
   MF: meta_fill_00(F's shadow + 4, 64), then S2
   ========================================================================== *)
Lemma mw_mf : forall ly S W (R : bvmap 5 word) m md,
  mw_base SK B cx fpos NoX ly S W (mkst R (Z_to_bv 64 (pa_sigma LS___asan_set_shadow_00)) m (seg_rom SEGS)) md ->
  getr R 1 = Z_to_bv 64 (BASE + MW_S2) -> getr R 10 = w64 (SH + 4) -> getr R 11 = w64 64 ->
  getr R 22 = w64 IDX -> getr R 24 = w64 V -> getr R 25 = w64 RQ ->
  SRr SEGS W (mkCfg (mkst R (Z_to_bv 64 (pa_sigma LS___asan_set_shadow_00)) m (seg_rom SEGS)) md) (mw_post SK B cx).
Proof.
  intros ly S W R m md HB Hra R10 R11 R22 R24 R25.
  set (ms := mkst R (Z_to_bv 64 (pa_sigma LS___asan_set_shadow_00)) m (seg_rom SEGS)) in *.
  pose proof (mw_sp_facts SK B LAWS TB HSEGS cx HPX) as HSPF.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK : MODEL_WRITE_AK = 8416) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
  destruct (mw_Ff NoX ly S W ms md HB) as (F1 & F2 & F3 & F4 & ESH & EF & Hfpos & Hnin & Hin & HFp & HSp).
  pose proof (mw_base_jx SK B cx fpos NoX ly S W ms md HB) as HJ.
  pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  pose proof (mw_base_sp SK B LAWS TB HSEGS cx fpos NoX ly S W ms md HPX HB) as Hsp. change (ms_regs ms) with R in Hsp.
  pose proof HB as HB0. unfold mw_base in HB0. cbv zeta in HB0.
  destruct HB0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R3 & R4 & _).
  change (ms_regs ms) with R in R3, R4.
  pose proof HPX as (HAPRE & _ & _).
  assert (HGx : gx_ok SEGS B (mw_G cx)) by (unfold apre in HAPRE; tauto).
  eapply SRr_bind.
  { eapply (aj_gx_set_shadow_at SK SEGS B LAWS pa_segs_low (pa_sigma LS___asan_set_shadow_00) 0x00 MF00
      (mw_G cx) (mw_XO cx) (mw_OUT cx) W R m (mw_STK cx) (mw_sp0 cx) (mw_FP cx)
      (mw_ly cx) (mw_S cx) (mw_W0 cx) (mw_mem0 cx) (mw_md0 cx) ((MW_CID, fpos) :: mw_own cx) ly S md (mw_k cx)
      4 fpos (SH + 4) 64 (getr R 1) HGx HJ (or_introl eq_refl)).
    - exact R10.
    - exact R11.
    - lia.
    - change (frame_addr ly 4 fpos) with (frame_addr ly MW_CID fpos). rewrite EF, ESH. unfold shadow_addr. lia.
    - change (frame_addr ly 4 fpos) with (frame_addr ly MW_CID fpos). rewrite EF, ESH.
      change (fs_frame_bytes 4 / 8) with 128. unfold shadow_addr. lia.
    - rewrite Hsp. lia.
    - rewrite Hsp, Hes. unfold mw_sp in *. lia.
    - rewrite Hsp. unfold mw_sp in *. lia.
    - rewrite R3. pose proof HAPRE as (_ & _ & _ & _ & _ & Hgp & _). exact Hgp.
    - rewrite R4. pose proof HAPRE as (_ & _ & _ & _ & _ & _ & Htp & _). exact Htp.
    - reflexivity.
    - rewrite Hra. apply ret_ok_codeptr_v; [unfold MW_S2, AF_model_write; lia | reflexivity]. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hset2 & Hun2 & Hpres2 & Hsm2).
  rewrite Hra.
  set (ms2 := mkst regs2 (Z_to_bv 64 (BASE + MW_S2)) mem2 (seg_rom SEGS)).
  assert (HB2 : mw_base SK B cx fpos NoX ly S W ms2 md2).
  { apply (mw_base_step SK B LAWS TB HSEGS cx fpos NoX ly S W ms md ly S W ms2 md2 (mw_sp1 cx) (mw_sp1 cx)
             (fun a => SH + 4 <= a < SH + 4 + 64) HPX HB); try reflexivity.
    - exact HJ2.
    - unfold mw_base in HB. cbv zeta in HB. tauto.
    - unfold mw_base in HB. cbv zeta in HB. tauto.
    - apply (mw_akept_un SK B LAWS TB HSEGS ly S W m md mem2 (mw_sp1 cx) (mw_sp1 cx) _ HAR);
        [lia | lia | intros a Ha; lia | | ].
      + intros a Ha Hn _. exact (Hun2 a Ha Hn).
      + intros a _ Hp. exact (Hpres2 a Hp).
    - unfold mw_sp in *. lia.
    - intros a Ha. right. right. left. unfold in_zr, shadow_addr. cbn [fst snd].
      change (fs_frame_bytes MW_CID / 8) with 128.
      change (frame_addr (mw_lyc cx) MW_CID fpos) with F. cbv beta in Ha. rewrite ESH in Ha. lia.
    - intros a Ha Hs. cbv beta in Hs. rewrite ESH in Hs. unfold mw_sp in *.
      unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg in *. destruct F4; lia.
    - intros a Ha Hs. cbv beta in Hs. rewrite ESH in Hs. unfold MW_FLAGPTR in Ha.
      unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg in *. destruct F4; lia.
    - exact (mw_rsame_of_pres SK B LAWS TB HSEGS _ _ HP2).
    - exact (proj1 (mw_sbm_fds2 _ _ Hsm2)).
    - exact (proj2 (mw_sbm_fds2 _ _ Hsm2)). }
  apply (mw_s2 ly S W regs2 mem2 md2 HB2).
  - etransitivity; [exact (HP2 22 ltac:(unfold acallee_saved; lia)) | exact R22].
  - etransitivity; [exact (HP2 24 ltac:(unfold acallee_saved; lia)) | exact R24].
  - etransitivity; [exact (HP2 25 ltac:(unfold acallee_saved; lia)) | exact R25].
  - intros j Hj. replace (SH + j) with (SH + 4 + (j - 4)) by lia. exact (Hset2 (j - 4) ltac:(lia)).
Qed.

End c.

(* ==========================================================================
   S1: THE SEND CUT, to the call of meta_fill_00
   ========================================================================== *)
Theorem mw_send : mw_send_obl SK B.
Proof.
  intros cx fpos ly3 S3 W3 ms3 md3 HPX
    (sn & sa & tab & kbs & Hpc & HNK & HIT & HSN & Hn0 & Hsn & HSA & Ha0 & HAL & R10 & Hidx & R24 & HB).
  pose proof (mw_base_shape SK B LAWS TB HSEGS cx fpos NoX ly3 S3 W3 ms3 md3 HB) as (Hrv & Hsv & Hrom & Hfr & Hfc).
  pose proof (mw_base_jx SK B cx fpos NoX ly3 S3 W3 ms3 md3 HB) as HJ3.
  pose proof HPX as (HAPRE & _ & _).
  assert (HGx : gx_ok SEGS B (mw_G cx)) by (unfold apre in HAPRE; tauto).
  pose proof asan_consts as ((C1a & C1b) & _).
  pose proof (mw_Ff cx fpos sn sa tab kbs HPX HNK HIT HSN Hn0 Hsn HSA Ha0 HAL Hidx NoX ly3 S3 W3 ms3 md3 HB)
    as (F1 & F2 & F3 & F4 & ESH & _).
  pose proof HB as HB0. unfold mw_base in HB0. cbv zeta in HB0.
  destruct HB0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R27 & _ & R23 & _).
  assert (Hms : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + MW_CUT_SEND)) (ms_mem ms3) (seg_rom SEGS))
    by (apply (mw_mkst_at ms3 MW_CUT_SEND); assumption).
  assert (Hrms : restrict (w_H W3) ms3 =
     mkst (ms_regs ms3) (Z_to_bv 64 (BASE + MW_CUT_SEND)) (rdW W3 (ms_mem ms3)) (seg_rom SEGS)).
  { rewrite Hms at 1. rewrite restrict_mkst_fx. reflexivity. }
  assert (HEI : img_env VAL A_LIM (mwE ms3 [])) by apply Eimg_env.
  assert (HS : st_ok_pi SEGS VAL (mwE ms3 []) (mkSS MW_CUT_SEND sr_atoms [] None (mkFacts [] [] []))
                 (restrict (w_H W3) ms3)).
  { rewrite Hrms. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute; reflexivity.
    - constructor.
    - exact I.
    - split; [exact I | split; exact I]. }
  pose (RUNC := paj_run_call_plain_x SK B LAWS (mw_G cx) HGx (mw_XO cx) (mw_OUT cx)).
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ev ?ssx (restrict (w_H ?Wx) ?msx) =>
    lazymatch type of RUNC with context [sym_runN_pi ?tpi _ _] =>
      let r := eval vm_compute in (sym_runN_pi tpi FUEL ssx) in
      lazymatch r with (?ssf, PRS_call ?sf) =>
        let Hrun := fresh "Hrun" in
        assert (Hrun : sym_runN_pi tpi FUEL ssx = (ssf, PRS_call sf)) by (vm_compute; reflexivity);
        eapply (RUNC Wx FUEL Ev ssx ssf sf msx _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun HJ3);
        clear Hrun
      end
    end
  end.
  { cbn [ss_mem]. apply awr_ok_x_nil. }
  cbv beta. intros ms' mat' HS' HJ' HF HF' HG'. cbn [ms_mem mkst] in HF, HF', HG'.
  assert (Hmem : ms_mem ms' = ms_mem ms3).
  { apply functional_extensionality. intros x. apply HF. cbn [ss_mem]. intros (r0 & Hin & _). destruct Hin. }
  pose proof (st_ok_restrict_mkst SEGS (w_H W3) _ _ ms' HS' eq_refl) as Ems. cbn [ss_pc setpc] in Ems.
  sreg HS' (1%bv : bv 5) Q1. sreg HS' (10%bv : bv 5) Q10. sreg HS' (11%bv : bv 5) Q11.
  sreg HS' (22%bv : bv 5) Q22. sreg HS' (24%bv : bv 5) Q24. sreg HS' (25%bv : bv 5) Q25.
  assert (HR' : mw_rsame (ms_regs ms3) (ms_regs ms')) by (unfold mw_rsame; mwc_rsame HS' ms3).
  set (md' := with_vm_backing (m_vm_lazy md3) mat' md3) in *.
  destruct (mw_shape_of SEGS ms' _ _ _ Ems) as (Sh1 & Sh2 & Sh3 & Sh4 & Sh5).
  assert (HB' : mw_base SK B cx fpos NoX ly3 S3 W3 ms' md')
    by exact (mw_base_nomemX SK B LAWS TB HSEGS cx fpos NoX ly3 S3 W3 ms3 md3 ms' md' HPX HB Hmem Sh1 Sh2 Sh3 Sh4 Sh5 HJ'
                (proj1 (wvb_fds_fs (m_vm_lazy md3) mat' md3)) (proj2 (wvb_fds_fs (m_vm_lazy md3) mat' md3)) HR').
  rewrite Ems.
  apply (mw_mf cx fpos sn sa tab kbs HPX HNK HIT HSN Hn0 Hsn HSA Ha0 HAL Hidx ly3 S3 W3 (ms_regs ms') (ms_mem ms') md').
  - rewrite <- Ems. exact HB'.
  - rewrite Q1. exact (codeptr_val _ _ HEI).
  - rewrite Q10. first [ exact (mwE_sv0 ms3 23 23%bv (mw_SH cx fpos + 4) eq_refl R23)
                       | rewrite mw_denot_add0; exact (mwE_sv0 ms3 23 23%bv (mw_SH cx fpos + 4) eq_refl R23) ].
  - rewrite Q11. reflexivity.
  - rewrite Q22. exact (mwE_sv0 ms3 10 10%bv (index_of tab sn) eq_refl R10).
  - rewrite Q24. exact (mwE_sv0 ms3 24 24%bv (Z.of_nat (length sa)) eq_refl R24).
  - rewrite Q25. exact (mwE_svc ms3 27 27%bv (mw_F cx fpos) 32 eq_refl R27 ltac:(lia)).
Qed.

End b.
End a.
