(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30 (a Theorem Labs lane, row G-BRE): the image-B (asan-ubsan) walk of plugin-hostd's
   relay_event in the `_x` + room form, pb_relay_event_x : re_spec_x B PST ARx MT RP MMAX G RG (BASE +
   AF_fr_relay_event).  A three-way merge: base lib/A/W_relay_event.v at a working branch 26a1ccdf1c1 (the AR walk
   lib/B/W_relay_event.v was ported from), one side lib/B/W_relay_event.v (image B's numerals, 01344381e6c), the
   other lib/A/W_relay_event.v at 9f5567c9e80 (a Theorem Labs lane row C1: the walk over any allocator relation ARx with BLKM
   and HLPST; a Theorem Labs lane room round F3: RP after MT, re_spec_x's room premises kr / RM / the counts at relay_event's
   peak handed to send_line unchanged, the post's RM at S' send_line's).  Both originals are in the form of the cgif walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v (runtime call sites) and lib/A/ACh2.v with lib/YC85.v cl_callS (the
   internal call), here over lib/B/W_journal_x.v's ajournal_gx_x.  This is the one generic walk: lib/B/W_relay_event.v's
   AR statement pb_relay_event is its corollary at ARx := ARi0, PST := [], RP := RP_AR (a Theorem Labs lane, Section cAR). *)
(* Image B's relay_event (0x82804, lib/B/W_listing.v AF_fr_relay_event 0x4c0) is image A's (0x826e4) instruction for
   instruction (fuzz_reply.asan-ubsan sha256 10ffb5f9202a): UBSan adds no check here.  What moves: the lock is the
   listing's object 3 (A: 6; ew index 244, A: 247), the return address of the lock call is BASE + 0x4e4 (1252; A:
   0x41c), send_line sits at 0x82854 (AF_fr_send_line 0x510) with frame 144 (so RE_STK = 16560; A: 16544), and the
   image band ends at 0x5fc000 (A: 0x5fb000). *)
(* relay_event(line) at 0x82804, 20 instructions: under g_lock (pthread_mutex_lock, a PCall), send_line(line,
   strlen(line) + 1) (strlen a PCall to the interceptor; send_line an internal call, its spec SL composed into this
   journal with ajournal_gx_G_mono_x and ajournal_gx_sub_x), then the unlock as a tail call (PTail) from the entry sp.
   Section hypotheses: the program function SL (send_line), the runtime entries ALOCK / AUNLOCK and ASTRLEN, LAWS /
   HP0 / BLKM / HG (the instance), and the placement facts (HV3, HLA, HLD, HLRW, HAOD, HAO3, HLPST) the pinned
   instance discharges by computation at fr_globals_b / PB_fr (lib/B/W_img.v). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a YP07.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_journal W_contract W_sites W_rep W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YCe5x YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x W_contract_x W_sites_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_send_line_xR W_contract_xR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require HarnessRep.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Open Scope bv_scope.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
Definition A_relay_event : Z := AF_fr_relay_event.
Definition A_relay_eventP : Z := BASE + A_relay_event.
Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable G : list (Z * Z).
Variable RG : rep_globals.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
(* a Theorem Labs lane's ruling 15:26Z: the instance has no hidden heads (W_journal_x Section hp0) *)
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
(* a live block's request is below 2^30: cgif's AR_blocks_law bounds it by MALLOC_MAX = 2^28, ARx_blocks_law gives no
   bound (W_kit_x's BLKN is its lower half).  2^30, not MALLOC_MAX: at the cf instance a live block can exceed 2^28
   (CfParamsReply.v: cf_malloc_max = 2^30 - 2^20, the harness's 2^29-byte vector), and 2^30 holds there by
   AR_blocks_law_ok_cf with YG08cf.cf_malloc_max_bound.  The walk needs it only for strlen's kk + 1 < 2^32. *)
Hypothesis BLKM : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n < 2 ^ 30.
Hypothesis HG : gx_ok SEGS B G.
Hypothesis SL : sl_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_send_line).
Hypothesis ALOCK : alock_realizes_x B ARx (SIGMA WS_pthread_mutex_lock).
Hypothesis AUNLOCK : aunlock_realizes_x B ARx (SIGMA WS_pthread_mutex_unlock).
Hypothesis ASTRLEN : astrlen_realizes_x B ARx (SIGMA WS_strlen).
(* placement: g_lock is the listing's object 3 (the auipc/addi pair at 0x82818; A: object 6), its address is
   4-aligned (the mutex entries need it; the listing does not fix the addi offset), and its 12 bytes are apart from
   send_line's globals (send_line's journal may change every byte of G_SL). *)
Hypothesis HV3 : VAL (A_OBJ 3) = rg_lock RG.
Hypothesis HLA : rg_lock RG mod 4 = 0.
Hypothesis HLD : forall a, rg_lock RG <= a < rg_lock RG + 12 -> ~ inG (G_SL B RG) a.
(* g_lock is in a writable segment: its bytes are not read-only image bytes.  Needed to carry the walk's rom_view
   past the mutex's write of the lock word. *)
Hypothesis HLRW : forall a, rg_lock RG <= a < rg_lock RG + 12 -> ~ in_rom SEGS a.
(* and apart from the three output globals that are not in G_SL (G_SL's six are HLD's) *)
Hypothesis HAOD : forall a, rg_lock RG <= a < rg_lock RG + 12 ->
  ~ (rg_send_max RG <= a < rg_send_max RG + 8) /\ ~ (rg_client RG <= a < rg_client RG + 4) /\
  ~ (rg_send_dead RG <= a < rg_send_dead RG + 1).
(* the same three cells lie in image B's band [0x10000, 0x5fc000) (the other six of aout_fp are G_SL's, hence image
   bytes by gx_ok) *)
Hypothesis HAO3 : (0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= 0x5fc000) /\
  (0x10000 <= rg_client RG /\ rg_client RG + 4 <= 0x5fc000) /\
  (0x10000 <= rg_send_dead RG /\ rg_send_dead RG + 1 <= 0x5fc000).
(* ...and outside the generic journal's PST (the image ranges ARx may change under any callee; at PST = [] none) *)
Hypothesis HLPST : forall a, rg_lock RG <= a < rg_lock RG + 12 -> ~ Exists (in_zr a) PST.
Let RUN := paj_run_x_x B PST ARx LAWS G HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS G HG 0 [].
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).
Definition re_Bx : sv := SOff 32 0.
Definition re_regions : smem := [ stack_region RE_FRAME ].
Definition re_facts : facts := mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF SB SB 0) ] [] [].
Definition ss_re : sstate := mkSS A_relay_event sr_atoms re_regions None re_facts.
Definition re_SH : list shent := [].
Definition re_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition re_extra : list word := map (Z_to_bv 64) [SB].
Lemma re_entry : forall W ly S Hp regs mem md ch,
afn_pre_x SEGS B ARx RE_STK ly S Hp W regs mem md ch ->
st_ok_pi SEGS VAL (Eimg (Ereg regs re_extra)) ss_re
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_relay_eventP) mem (seg_rom SEGS)))
/\ sh_ok SEGS re_Bx re_SH (Eimg (Ereg regs re_extra)) (mrestrict (w_H W) mem).
Proof.
intros W ly S Hp regs mem md ch HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : RE_STK = 16560) by reflexivity.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs re_extra)). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
split.
- unfold ss_re, A_relay_eventP. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold re_regions, stack_region, RE_FRAME.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite WS. lia.
+ apply pairwise_disjoint_of_extents. unfold re_regions, stack_region, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. repeat split.
+ split; [|split; [exact I | exact I]].
cbn [re_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E32, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hal16 C1 C3 WS Hstk0. clear.
unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, re_SH. constructor.
Qed.
(* ---- Helpers of this walk. ----
   (a) writable_at depends on the memory only through the byte at the address, so a step that keeps every present
   byte present keeps every writable byte writable (Reusable/YP09.v writable_at_grows). *)
Lemma re_wr_pres : forall (W : world SEGS) (m m' : word -> option byte) a,
(forall x, apresent (w_H W) m x -> apresent (w_H W) m' x) ->
writable_at SEGS (mrestrict (w_H W) m) a -> writable_at SEGS (mrestrict (w_H W) m') a.
Proof.
intros W m m' a Hp Hw. apply (writable_at_grows SEGS (mrestrict (w_H W) m) (mrestrict (w_H W) m') a); [|exact Hw].
intros x Hx. unfold mrestrict in Hx |- *.
destruct (w_H W x) eqn:Hh; [exfalso; exact (Hx eq_refl)|].
destruct (m x) as [b|] eqn:Em; [|exfalso; exact (Hx eq_refl)].
destruct (Hp (bv_unsigned x)) as [Hh' [b' Hb']].
{ split; rewrite Z_to_bv_bv_unsigned; [exact Hh | exists b; exact Em]. }
rewrite Z_to_bv_bv_unsigned in Hb'. rewrite Hb'. discriminate.
Qed.
(* the same across a step that may change the world: writable_at reads the memory only at the address *)
Lemma re_wr_pt : forall (m m' : word -> option byte) a,
m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> writable_at SEGS m a -> writable_at SEGS m' a.
Proof. intros m m' a E H. unfold writable_at, wview in *. rewrite E. exact H. Qed.
Lemma re_wr_pres2 : forall (W W' : world SEGS) (m m' : word -> option byte) a,
(apresent (w_H W) m a -> apresent (w_H W') m' a) ->
writable_at SEGS (mrestrict (w_H W) m) a -> writable_at SEGS (mrestrict (w_H W') m') a.
Proof.
intros W W' m m' a Hp Hw.
destruct (mrestrict (w_H W') m' (Z_to_bv 64 a)) as [b'|] eqn:E'.
- apply (apresent_writable SEGS). unfold mrestrict in E'.
  destruct (w_H W' (Z_to_bv 64 a)) eqn:Hh'; [discriminate|]. split; [exact Hh' | exists b'; exact E'].
- destruct (mrestrict (w_H W) m (Z_to_bv 64 a)) as [b|] eqn:E.
  + exfalso. unfold mrestrict in E. destruct (w_H W (Z_to_bv 64 a)) eqn:Hh; [discriminate|].
    destruct (Hp (conj Hh (ex_intro _ b E))) as [Hh2 [b2 Hb2]].
    unfold mrestrict in E'. rewrite Hh2, Hb2 in E'. discriminate.
  + exact (re_wr_pt (mrestrict (w_H W) m) (mrestrict (w_H W') m') a ltac:(rewrite E, E'; reflexivity) Hw).
Qed.
(* (b) a value kept by the ASan view is kept in memory *)
Lemma re_vm_kept : forall (W W' : world SEGS) (m m' : word -> option byte) a (n : nat) v,
(forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
val_mem SEGS (mrestrict (w_H W) m) a n v -> val_mem SEGS (mrestrict (w_H W') m') a n v.
Proof.
intros W W' m m' a n v Hk Hv k Hk2.
assert (Hx : a <= a + Z.of_nat k < a + Z.of_nat n) by lia.
rewrite (mbyte_of_aview SEGS (w_H W) (w_H W') m m' (a + Z.of_nat k) (Hk _ Hx)).
exact (Hv k Hk2).
Qed.
(* (c) one byte of a val_mem, as an aview *)
Lemma re_av1 : forall (W : world SEGS) (m : word -> option byte) a (n : nat) v,
val_mem SEGS (mrestrict (w_H W) m) a n v -> (0 < n)%nat ->
aview SEGS (w_H W) m a = Some (le_byte v n 0).
Proof.
intros W m a n v Hv Hn. specialize (Hv 0%nat Hn). cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv.
unfold aview. rewrite Hv. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. apply bv_wrap_small.
change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_pos_bound. lia.
Qed.
(* (d) every byte of a val_mem is visible *)
Lemma re_av_ne : forall (W : world SEGS) (m : word -> option byte) a (n : nat) v x,
val_mem SEGS (mrestrict (w_H W) m) a n v -> a <= x < a + Z.of_nat n -> aview SEGS (w_H W) m x <> None.
Proof.
intros W m a n v x Hv Hx. unfold aview.
assert (Hk : (Z.to_nat (x - a) < n)%nat) by lia.
specialize (Hv (Z.to_nat (x - a)) Hk). rewrite Z2Nat.id in Hv by lia.
replace (a + (x - a)) with x in Hv by lia. rewrite Hv. discriminate.
Qed.
(* (e) the bytes of the NUL-terminated line, as the walk reads them off garr8 *)
Lemma re_av_garr : forall (W : world SEGS) (m : word -> option byte) a l j,
garr8 SEGS (mrestrict (w_H W) m) a l -> (j < length l)%nat ->
aview SEGS (w_H W) m (a + Z.of_nat j) = Some (nth j l 0).
Proof.
intros W m a l j Hg Hj. destruct (Hg j Hj) as [Hv Hr].
pose proof (re_av1 W m (a + Z.of_nat j) 1%nat (nth j l 0) Hv ltac:(lia)) as HA.
replace (le_byte (nth j l 0) 1 0) with (nth j l 0) in HA; [exact HA|].
unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small (nth j l 0) 256) by lia.
symmetry. apply Z.mod_small. lia.
Qed.
Lemma re_nth_lo : forall (e : list byte) j, (j < length e)%nat ->
nth j (HarnessRep.bzs (e ++ [Z_to_bv 8 0])) 0 = bv_unsigned (nth j e (Z_to_bv 8 0)).
Proof.
intros e j Hj. unfold HarnessRep.bzs. rewrite map_app, app_nth1 by (rewrite length_map; lia).
change 0 with (HarnessRep.bz (Z_to_bv 8 0)) at 1. apply map_nth.
Qed.
Lemma re_nth_hi : forall (e : list byte), nth (length e) (HarnessRep.bzs (e ++ [Z_to_bv 8 0])) 0 = 0.
Proof.
intros e. unfold HarnessRep.bzs. rewrite map_app, app_nth2 by (rewrite length_map; lia).
rewrite length_map, Nat.sub_diag. cbn [nth]. unfold HarnessRep.bz. vm_compute. reflexivity.
Qed.
Lemma re_len_bzs : forall (e : list byte), length (HarnessRep.bzs (e ++ [Z_to_bv 8 0])) = S (length e).
Proof. intros e. unfold HarnessRep.bzs. rewrite length_map, length_app. cbn [length]. lia. Qed.
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): relay_event's walk at a world relation R.  send_line reallocs g_out, so at the
   cf instance (R := wle' SEGS RZ_cf) the walk crosses a re-hide: send_line's contract is taken at R (SL_R,
   W_send_line_xR); lock / strlen / unlock stay strict and enter through W_sites_x's R call steps.  At R := wle this
   is pb_relay_event_x (below the section). *)
Section cR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Hypothesis SL_R : sl_spec_xR B PST ARx R MT RP MMAX RG (BASE + AF_fr_send_line).
Let RUNR := paj_run_x_xG B PST ARx LAWS R G HG 0 [].
Let RUNTOR := paj_run_to_x_xG B PST ARx LAWS R G HG 0 [].
Theorem pb_relay_event_xR : re_spec_xR B PST ARx R MT RP MMAX G RG (BASE + AF_fr_relay_event).
Proof.
intros W ly S Hp regs mem md ch c O mx no cap out line e q m HPRE H10 HGA HNZ Hq Hqo Hql Hinb HTV HOUT HLK HROM
HLG HSLG HLE HCAP HLIVE HMO kr HRM HCNT.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (re_entry W ly S Hp regs mem md ch HPRE) as [HS SHOK].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : RE_STK = 16560) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (ajournal_gx_init_xR SEGS B PST ARx R_refl G 0 [] RE_STK (ablocks_fp (aout_blks cap out)) ly S Hp W regs mem md ch HPRE
  ltac:(lia) eq_refl ltac:(lia) ltac:(intros a Ha; lia)) as HJ.
remember (Eimg (Ereg regs re_extra)) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (HAE : env_agree 32 (Ereg regs re_extra) E) by (rewrite HE; split; [intros m0 Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
unfold cfg_at. change (w64 (BASE + AF_fr_relay_event)) with (Z_to_bv 64 (BASE + A_relay_event)).
paj_run_tok_xR RUNR HS HJ SHOK re_Bspan. { apply awr_ok_x_of0. awr_ok_tac. exact Usp. }
(* ---- the lock (a PCall to pthread_mutex_lock, a0 = &g_lock = VAL (A_OBJ 3)) ---- *)
pose proof HLK as (LK0 & LK4 & LK8 & LKW). unfold arm in LK0, LK4, LK8, LKW.
assert (HL3a : 0x10000 <= rg_lock RG) by (rewrite <- HV3; exact (proj1 (pa_obj_img 3 ltac:(lia)))).
assert (HL3b : rg_lock RG + 8 <= 0x5fc000) by (rewrite <- HV3; exact (proj2 (pa_obj_img 3 ltac:(lia)))).
assert (HLOW : rg_lock RG + 12 < spZ regs - RE_STK) by (rewrite WS; lia).
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
  mrestrict (w_H W) (ms_mem ms) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a)).
{ intros a Ha Hno. apply HFr. rewrite unsigned_lit_small by lia.
  intros (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite Usp in Hr. lia. }
assert (KEEPV : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a)
  by (intros a Ha Hno; apply aview_eq_of; apply KEEP1; assumption).
lazymatch goal with Hx : mem_grows _ (mrestrict _ (ms_mem ms)) |- _ => pose proof Hx as MG1 end.
assert (LKa : alock_at RG W (ms_mem ms) false).
{ unfold alock_at, arm. split; [|split; [|split]].
  - apply (re_vm_kept W W mem (ms_mem ms)); [intros x Hx; apply KEEPV; cbn in Hx; lia | exact LK0].
  - apply (re_vm_kept W W mem (ms_mem ms)); [intros x Hx; apply KEEPV; cbn in Hx; lia | exact LK4].
  - apply (re_vm_kept W W mem (ms_mem ms)); [intros x Hx; apply KEEPV; cbn in Hx; lia | exact LK8].
  - intros i Hi. apply (writable_at_grows SEGS (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms)) (rg_lock RG + i) MG1).
    exact (LKW i Hi). }
pose proof LKa as (LK0a & LK4a & LK8a & LKWa). unfold arm in LK0a, LK4a, LK8a, LKWa.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (10%bv : bv 5) Q10.
assert (U244 : bv_unsigned (ew E 244%nat) = rg_lock RG)
  by (rewrite <- HV3; change 244%nat with (A_OBJ 3); exact (HEI (A_OBJ 3) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
assert (E244 : ew E 244%nat = Z_to_bv 64 (rg_lock RG))
  by (apply bv_eq; rewrite U244, unsigned_lit_small by lia; reflexivity).
assert (Usp2 : spZ (ms_regs ms) = spZ regs + (-32)).
{ unfold spZ. rewrite Q2, Usp. apply unsigned_lit_small. unfold spZ in *. lia. }
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G 0 [] RE_STK (spZ regs) (ablocks_fp (aout_blks cap out))
  ly S _ W mem md [] ly S _ W (ms_mem ms) _ 0 HJ) as HARc.
assert (AVL : aview SEGS (w_H W) (ms_mem ms) (rg_lock RG) = Some 0).
{ pose proof (re_av1 W (ms_mem ms) (rg_lock RG) 4%nat 0 LK0a ltac:(lia)) as HA.
  replace (le_byte 0 4 0) with 0 in HA by (vm_compute; reflexivity). exact HA. }
assert (HNOWN : forall a, rg_lock RG <= a < rg_lock RG + 12 -> ~ aowned B ly S a).
{ intros a Ha Ho. destruct (HG a (HLG a Ha)) as (Hi & Hno & _).
  apply Hno. exact (proj1 (alx_owned_image _ _ _ LAWS ly S _ W (ms_mem ms) _ a HARc Hi) Ho). }
eapply (SRrG_bind SEGS R R_trans).
{ eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R G 0 [] ESTACK (SIGMA WS_pthread_mutex_lock)
    (fun a => rg_lock RG + 4 <= a < rg_lock RG + 8)
    (fun _ mem' => val_mem SEGS (mrestrict (w_H W) mem') (rg_lock RG + 4) 4 16)
    W (ms_regs ms) (ms_mem ms) RE_STK (spZ regs) (ablocks_fp (aout_blks cap out)) ly S _ W mem md
    ([] : list (Z * Z)) ly S _ _ 0 (-32) _ HG eq_refl HJ Usp2 eq_refl ltac:(lia) ltac:(lia) ltac:(rewrite WS; unfold ESTACK; lia)
    ltac:(rewrite Q3, (EE 3%nat 3%bv eq_refl); exact Hgp)
    ltac:(rewrite Q4, (EE 4%nat 4%bv eq_refl); exact Htp)
    Q1 (ret_ok_codeptr_v 1252 ltac:(lia) eq_refl)).
  - intros a. lia.
  - intros a Hwa _. exact (re_av_ne W (ms_mem ms) (rg_lock RG + 4) 4%nat 0 a LK4a ltac:(cbn; lia)).
  - intros a Hwa HnG. exfalso. apply HnG. apply HLG. lia.
  - intros HPRE2 HSC2.
    exact (ALOCK ly S _ W (ms_regs ms) (ms_mem ms) _ (rg_lock RG) 0 HPRE2
      ltac:(rewrite Q10, E244; reflexivity) ltac:(lia) HLA ltac:(lia) AVL eq_refl LK4a
      ltac:(intros a Ha; split;
            [ destruct (Z_lt_le_dec a (rg_lock RG + 4)) as [Hlt | Hge];
              [ exact (re_av_ne W (ms_mem ms) (rg_lock RG) 4%nat 0 a LK0a ltac:(cbn; lia))
              | exact (re_av_ne W (ms_mem ms) (rg_lock RG + 4) 4%nat 0 a LK4a ltac:(cbn; lia)) ]
            | rewrite Usp2; unfold ESTACK; lia ])
      ltac:(intros a Ha; split;
            [ replace a with (rg_lock RG + (a - rg_lock RG)) by lia; exact (LKWa (a - rg_lock RG) ltac:(lia))
            | split; [ apply HNOWN; lia | rewrite Usp2; unfold ESTACK; lia ] ])
      (fun a Ha HK => proj2 (proj2 (HG a (HLG a ltac:(lia)))) (proj1 (proj2 HK)))). }
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJa & HPa & Hlk2 & Hfra & Hpresa).
(* back in relay_event, the lock held *)
pose proof (ajournal_gx_inner_xR SEGS B PST ARx G 0 [] RE_STK (spZ regs) (ablocks_fp (aout_blks cap out))
  ly S _ W mem md [] ly S _ W mem2 md2 _ HJa) as (memS2 & HJin2 & _).
pose proof HJin2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPR2 & _).
jafter_call_keep_pi HS 33%nat regs2 (mrestrict (w_H W) mem2) HPa [0]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
  unfold stack_region, RE_FRAME.
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply Hfra; [lia | intros Hw; lia | unfold ESTACK; lia].
  - intros a Ha _. apply (apresent_writable SEGS). apply HPR2. rewrite WS. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 33 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall n, (n < 33)%nat -> ew Ea n = ew E n) by (intros n Hn; rewrite HEa; apply YN3v.ew_havoc_old; exact Hn).
assert (HAEa : env_agree 32 (Ereg regs re_extra) Ea) by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEa.
assert (SHOKa : sh_ok SEGS re_Bx re_SH Ea (mrestrict (w_H W) mem2)) by (unfold sh_ok, re_SH; constructor).
assert (Uspa : bv_unsigned (ew Ea 2) = spZ regs) by (rewrite OLDa by lia; exact Usp).
paj_run_tok_xR RUNR HS HJa SHOKa re_Bspan. { apply awr_ok_x_of0. awr_ok_tac. exact Uspa. }
(* ---- strlen (line): an interceptor PCall ---- *)
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G 0 [] RE_STK (spZ regs) (ablocks_fp (aout_blks cap out))
  ly S _ W mem md [] ly S _ W (ms_mem ms0) _ 0 HJa) as HARa.
destruct (alx_blocks _ _ _ LAWS ly S _ W mem md q m HAR Hq) as (Hq16 & Hq4096 & Hqceil & Hqapp & Hqpres & Hqdisj).
pose proof (BLKM ly S _ W mem md q m HAR Hq) as Hqn.
assert (HRS : req_size m <= Z.max 1 m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
pose proof (proj1 (req_size_pos m ltac:(lia))) as HRS1.
assert (HBNI : forall a, q <= a < q + req_size m -> ~ in_img SEGS a)
  by (intros a Ha; exact (blk_img_x SEGS B ARx LAWS ly S _ W mem md q m a HAR Hq Ha)).
assert (HLIMG : forall a, rg_lock RG <= a < rg_lock RG + 12 -> in_img SEGS a)
  by (intros a Ha; exact (proj1 (HG a (HLG a Ha)))).
assert (KEEPB : forall a, q <= a < q + req_size m -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
{ intros a Ha.
  assert (HA1 : aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem2 a).
  { lazymatch type of HFr0 with frame_of ?Ev ?rs _ _ =>
    apply (aview_kept_out Ev rs (w_H W) mem2 (ms_mem ms0) HFr0 a ltac:(lia)) end.
    intros (r & Hin & Hr).
    lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
    cbn [In] in Hin. destruct Hin as [<- | []].
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite Uspa in Hr. lia. }
  rewrite HA1. rewrite (Hfra a ltac:(lia) ltac:(intros Hw; apply (HBNI a Ha); apply HLIMG; lia) ltac:(unfold ESTACK; lia)).
  apply KEEPV; lia. }
assert (GAR2 : garr8 SEGS (arm W (ms_mem ms0)) line (HarnessRep.bzs (e ++ [Z_to_bv 8 0]))).
{ unfold arm. apply (garr8_frame SEGS (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms0))); [exact HGA|].
  intros a Ha. rewrite re_len_bzs in Ha. apply (mbyte_of_aview SEGS). apply KEEPB.
  pose proof (Z.mod_pos_bound (- (line + re_len e)) 8 ltac:(lia)). unfold re_len in *. lia. }
assert (GAV : forall j, (j < length (HarnessRep.bzs (e ++ [Z_to_bv 8 0])))%nat ->
  aview SEGS (w_H W) (ms_mem ms0) (line + Z.of_nat j) = Some (nth j (HarnessRep.bzs (e ++ [Z_to_bv 8 0])) 0))
  by (intros j Hj; exact (re_av_garr W (ms_mem ms0) line _ j GAR2 Hj)).
assert (FB : first_byte SEGS W (ms_mem ms0) line (Z.of_nat (length e) + 1) 0 (Z.of_nat (length e))).
{ split; [lia|]. split.
  - intros i Hi. exists (nth (Z.to_nat i) (HarnessRep.bzs (e ++ [Z_to_bv 8 0])) 0).
    split.
    + rewrite <- (Z2Nat.id i) at 1 by lia. apply GAV. rewrite re_len_bzs. lia.
    + rewrite re_nth_lo by lia. intros Hz. apply HNZ.
      replace (Z_to_bv 8 0) with (nth (Z.to_nat i) e (Z_to_bv 8 0)) by (apply bv_eq; rewrite Hz; reflexivity).
      apply nth_In. lia.
  - intros _. rewrite (GAV (length e) ltac:(rewrite re_len_bzs; lia)). rewrite re_nth_hi. reflexivity. }
assert (KEEPI : forall a, 0 <= a < alloc_ceiling -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) ->
  aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hnw.
  assert (HA1 : aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem2 a).
  { lazymatch type of HFr0 with frame_of ?Ev ?rs _ _ =>
    apply (aview_kept_out Ev rs (w_H W) mem2 (ms_mem ms0) HFr0 a ltac:(lia)) end.
    intros (r & Hin & Hr).
    lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
    cbn [In] in Hin. destruct Hin as [<- | []].
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite Uspa in Hr. rewrite WS in HLOW. lia. }
  rewrite HA1, (Hfra a ltac:(lia) Hnw ltac:(unfold ESTACK; rewrite WS in HLOW; lia)). apply KEEPV; [lia | rewrite WS in HLOW; lia]. }
assert (ROM2 : rom_view SEGS W (ms_mem ms0)).
{ intros a Hrom.
  assert (Hi : in_img SEGS a) by (destruct Hrom as (sg & Hin & _ & Hr); exists sg; split; [exact Hin | exact Hr]).
  pose proof (Hsegs a Hi) as Hlow. unfold kLowMemEnd in Hlow.
  rewrite KEEPI; [apply HROM; exact Hrom | lia | intros Hw; exact (HLRW a ltac:(lia) Hrom)]. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3.
prreg HS (4%bv : bv 5) P4. prreg HS (10%bv : bv 5) P10.
assert (Usp3 : spZ (ms_regs ms0) = spZ regs + (-32)).
{ unfold spZ. rewrite P2, Uspa. apply unsigned_lit_small. unfold spZ in *. lia. }
assert (Ea10 : ew Ea 10%nat = Z_to_bv 64 line) by (rewrite OLDa by lia; rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (HINB : line + Z.of_nat (length e) + 1 <= q + req_size m)
  by (pose proof (Z.mod_pos_bound (- (line + re_len e)) 8 ltac:(lia)); unfold re_len in *; lia).
assert (HBOUT : forall a, q <= a < q + req_size m -> 4096 <= a < spZ regs - 16560) by (rewrite WS in Hslo; lia).
(* strlen's granule tail (past the NUL, to the end of its 8-byte granule): visible at entry (re_spec), so visible at
   the call; a byte of it that is a lock-word byte is visible because the lock just wrote 16 there *)
assert (HTV2 : forall a, line + Z.of_nat (length e) < a < line + Z.of_nat (length e) - (line + Z.of_nat (length e)) mod 8 + 8 ->
  aview SEGS (w_H W) (ms_mem ms0) a <> None).
{ intros a Ha.
  pose proof ASAN_CEIL_range as (_ & HC8). unfold ASAN_CEIL in HC8.
  pose proof (Z.div_mod (line + Z.of_nat (length e)) 8 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (line + Z.of_nat (length e)) 8 ltac:(lia)) as R1.
  pose proof (Z.div_mod alloc_ceiling 4096 ltac:(lia)) as D2. rewrite HC8, Z.add_0_r in D2.
  assert (Hac : 0 <= a < alloc_ceiling) by lia.
  destruct (Z_le_gt_dec (rg_lock RG + 4) a) as [H1 | H1]; [destruct (Z_lt_le_dec a (rg_lock RG + 8)) as [H2 | H2]|].
  - assert (A3 : aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem2 a).
    { lazymatch type of HFr0 with frame_of ?Ev ?rs _ _ =>
      apply (aview_kept_out Ev rs (w_H W) mem2 (ms_mem ms0) HFr0 a ltac:(lia)) end.
      intros (r & Hin & Hr).
      lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
      cbn [In] in Hin. destruct Hin as [<- | []].
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite Uspa in Hr.
      rewrite WS in Hslo. lia. }
    rewrite A3. exact (re_av_ne W mem2 (rg_lock RG + 4) 4%nat 16 a Hlk2 ltac:(cbn; lia)).
  - rewrite KEEPI; [apply HTV; exact Ha | exact Hac | lia].
  - rewrite KEEPI; [apply HTV; exact Ha | exact Hac | lia]. }
eapply (SRrG_bind SEGS R R_trans).
{ eapply (aj_strlen_gx_at_xR B PST ARx LAWS R_trans WLE_R (SIGMA WS_strlen) ASTRLEN G 0 [] W (ms_regs ms0) (ms_mem ms0) RE_STK (spZ regs)
    (ablocks_fp (aout_blks cap out)) ly S _ W mem md ([] : list (Z * Z)) ly S _ _ _ line (Z.of_nat (length e)) (-32) _
    HG eq_refl HJa).
  - rewrite P10, Ea10. reflexivity.
  - lia.
  - lia.
  - pose proof (Z.mod_pos_bound (- (line + re_len e)) 8 ltac:(lia)); unfold re_len in *; lia.
  - pose proof (Z.mod_pos_bound (- (line + re_len e)) 8 ltac:(lia)); unfold re_len in *; lia.
  - exact Usp3.
  - reflexivity.
  - lia.
  - rewrite WS. unfold ESTACK. lia.
  - rewrite P3, OLDa by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite P4, OLDa by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact P1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact FB.
  - intros a Ha. split.
    + replace a with (line + Z.of_nat (Z.to_nat (a - line))) by (rewrite Z2Nat.id by lia; lia).
      rewrite (GAV (Z.to_nat (a - line)) ltac:(rewrite re_len_bzs; lia)). discriminate.
    + rewrite Usp3. unfold ESTACK. pose proof (HBOUT a ltac:(lia)). lia.
  - intros a Ha. unfold ESTACK. pose proof (HBOUT a ltac:(lia)). lia.
  - exact (amem_range_of_block_x SEGS B ARx LAWS ly S _ W mem md q m line (Z.of_nat (length e) + 1) HAR Hq ltac:(lia)
      ltac:(pose proof (Z.mod_pos_bound (- (line + re_len e)) 8 ltac:(lia)); unfold re_len in *; lia)).
  - unfold amem_range, in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *. lia.
  - exact (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly S _ W (ms_mem ms0) _ q m line (Z.of_nat (length e) + 1) HARa Hq
      ltac:(lia) ltac:(pose proof (Z.mod_pos_bound (- (line + re_len e)) 8 ltac:(lia)); unfold re_len in *; lia)).
  - exact (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly S _ W (ms_mem ms0) _ q m line (Z.of_nat (length e) + 1) HARa Hq
      ltac:(lia) ltac:(pose proof (Z.mod_pos_bound (- (line + re_len e)) 8 ltac:(lia)); unfold re_len in *; lia) ltac:(lia)).
  - exact HTV2.
  - exact ROM2. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJb & HPb & Hlen3 & Hfrb & Hpresb).
(* back in relay_event with a0 = |e| *)
lazymatch goal with Hx : mem_grows _ (mrestrict _ (ms_mem ms0)) |- _ => pose proof Hx as MG2 end.
pose proof (ajournal_gx_inner_xR SEGS B PST ARx G 0 [] RE_STK (spZ regs) (ablocks_fp (aout_blks cap out))
  ly S _ W mem md [] ly S _ W mem3 md3 _ HJb) as (memS3 & HJin3 & _).
pose proof HJin3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPR3 & _).
jafter_call_keep_pi HS 49%nat regs3 (mrestrict (w_H W) mem3) HPb [0]%nat HS3.
match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
  unfold stack_region, RE_FRAME.
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Uspa.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply Hfrb; [lia | unfold ESTACK; lia].
  - intros a Ha _. apply (apresent_writable SEGS). apply HPR3. rewrite WS. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc Ea 49 (map (getr regs3) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall n, (n < 49)%nat -> ew Eb n = ew Ea n) by (intros n Hn; rewrite HEb; apply YN3v.ew_havoc_old; exact Hn).
assert (HAEb : env_agree 32 (Ereg regs re_extra) Eb) by (rewrite HEb; apply env_agree_havoc_ge; [cbv; lia | exact HAEa]).
clear HEb.
assert (SHOKb : sh_ok SEGS re_Bx re_SH Eb (mrestrict (w_H W) mem3)) by (unfold sh_ok, re_SH; constructor).
assert (Uspb : bv_unsigned (ew Eb 2) = spZ regs) by (rewrite OLDb, OLDa by lia; exact Usp).
prreg HS (10%bv : bv 5) R10b.
paj_run_to_tok_xR RUNTOR HS HJb SHOKb re_Bspan AF_fr_send_line. { apply awr_ok_x_of0. awr_ok_tac. exact Uspb. }
(* ---- send_line (line, |e| + 1): an internal call ---- *)
lazymatch goal with Hx : mem_grows _ (mrestrict _ (ms_mem ms1)) |- _ => pose proof Hx as MG3 end.
assert (KEEPC : forall a, 0 <= a < alloc_ceiling -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) ->
  aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hnw.
  assert (H1 : aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem3 a).
  { lazymatch type of HFr1 with frame_of ?Ev ?rs _ _ =>
    apply (aview_kept_out Ev rs (w_H W) mem3 (ms_mem ms1) HFr1 a ltac:(lia)) end.
    intros (r & Hin & Hr).
    lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
    cbn [In] in Hin. destruct Hin as [<- | []].
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite Uspb in Hr.
    rewrite WS in Hslo. lia. }
  rewrite H1, (Hfrb a ltac:(lia) ltac:(unfold ESTACK; rewrite WS in Hslo; lia)). apply KEEPI; assumption. }
assert (WKEEP : forall a, writable_at SEGS (mrestrict (w_H W) mem) a -> writable_at SEGS (mrestrict (w_H W) (ms_mem ms1)) a).
{ intros a Hw.
  apply (writable_at_grows SEGS (mrestrict (w_H W) mem3) (mrestrict (w_H W) (ms_mem ms1)) a MG3).
  apply (re_wr_pres W (ms_mem ms0) mem3 a Hpresb).
  apply (writable_at_grows SEGS (mrestrict (w_H W) mem2) (mrestrict (w_H W) (ms_mem ms0)) a MG2).
  apply (re_wr_pres W (ms_mem ms) mem2 a Hpresa).
  apply (writable_at_grows SEGS (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms)) a MG1).
  exact Hw. }
assert (HINSL : forall a,
  (rg_client_broken RG <= a < rg_client_broken RG + 1) \/ (rg_send_eintr RG <= a < rg_send_eintr RG + 1) \/
  (rg_nout RG <= a < rg_nout RG + 8) \/ (rg_capout RG <= a < rg_capout RG + 8) \/
  (rg_out RG <= a < rg_out RG + 8) \/ (as_errno B <= a < as_errno B + 4) -> inG (G_SL B RG) a).
{ intros a Ha. unfold G_SL, inG. apply Exists_exists.
  destruct Ha as [H|[H|[H|[H|[H|H]]]]].
  - exists (rg_client_broken RG, 1); split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
  - exists (rg_send_eintr RG, 1); split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
  - exists (rg_nout RG, 8); split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
  - exists (rg_capout RG, 8); split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
  - exists (rg_out RG, 8); split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
  - exists (as_errno B, 4); split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia]. }
assert (HGSL : forall a, inG (G_SL B RG) a -> 0 <= a < alloc_ceiling /\ ~ (rg_lock RG + 4 <= a < rg_lock RG + 8)).
{ intros a Ha. split.
  - pose proof (Hsegs a (proj1 (HG a (HSLG a Ha)))). unfold kLowMemEnd in *. lia.
  - intros Hw. exact (HLD a ltac:(lia) Ha). }
assert (HOUTB : forall b, In b (aout_blks cap out) -> In b (ablocks B ly S)).
{ intros b Hb. unfold aout_blks in Hb. destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0]; [destruct Hb|].
  cbn [In] in Hb. destruct Hb as [<- | []].
  destruct HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H26).
  destruct H26 as [(Hc & _) | (_ & _ & Hin & _)]; [lia | exact Hin]. }
assert (AKEPT : akept W mem W (ms_mem ms1) (aout_fp B RG cap out)).
{ intros r Hr a Har.
  assert (HR : 0 <= a < alloc_ceiling /\ ~ (rg_lock RG + 4 <= a < rg_lock RG + 8)).
  { unfold aout_fp in Hr. cbn [In] in Hr.
    destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]];
    cbn [fst snd] in Har.
    - split; [lia | intros Hw; exact (proj1 (HAOD a ltac:(lia)) ltac:(lia))].
    - exact (HGSL a (HINSL a ltac:(tauto))).
    - exact (HGSL a (HINSL a ltac:(tauto))).
    - exact (HGSL a (HINSL a ltac:(tauto))).
    - split; [lia | intros Hw; exact (proj1 (proj2 (HAOD a ltac:(lia))) ltac:(lia))].
    - exact (HGSL a (HINSL a ltac:(tauto))).
    - split; [lia | intros Hw; exact (proj2 (proj2 (HAOD a ltac:(lia))) ltac:(lia))].
    - exact (HGSL a (HINSL a ltac:(tauto))).
    - exact (HGSL a (HINSL a ltac:(tauto))).
    - destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0]; [destruct Hr|].
      cbn [In] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Har.
      assert (Hin : In (out, cap) (ablocks B ly S)) by (apply HOUTB; unfold aout_blks; rewrite (proj2 (Z.eqb_neq cap 0) Hc0); left; reflexivity).
      destruct (alx_blocks _ _ _ LAWS ly S _ W mem md out cap HAR Hin) as (_ & Ho4096 & Hoceil & _ & _ & _).
      pose proof (proj1 (req_size_pos cap ltac:(lia))) as Hrs1.
      assert (Hrq : req_size cap = cap) by (unfold req_size; destruct (Z.eqb_spec cap 0); lia).
      split; [lia|]. intros Hw.
      exact (blk_img_x SEGS B ARx LAWS ly S _ W mem md out cap a HAR Hin ltac:(lia) (HLIMG a ltac:(lia))). }
  split; [apply KEEPC; [exact (proj1 HR) | exact (proj2 HR)] | exact (WKEEP a)]. }
assert (AOUT1 : aout_at B RG ly S W (ms_mem ms1) c O mx no cap out)
  by exact (aout_at_kept B RG ly S W mem ly S W (ms_mem ms1) c O mx no cap out HOUT AKEPT HOUTB).
assert (GAR1 : garr8 SEGS (arm W (ms_mem ms1)) line (HarnessRep.bzs (e ++ [Z_to_bv 8 0]))).
{ unfold arm. apply (garr8_frame SEGS (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms1))); [exact HGA|].
  intros a Ha. rewrite re_len_bzs in Ha. apply (mbyte_of_aview SEGS). apply KEEPC.
  - pose proof (HBOUT a ltac:(lia)). lia.
  - intros Hw. exact (blk_img_x SEGS B ARx LAWS ly S _ W mem md q m a HAR Hq ltac:(lia) (HLIMG a ltac:(lia))). }
assert (HLB : Z.of_nat (length (e ++ [Z_to_bv 8 0])) = re_len e)
  by (unfold re_len; rewrite length_app; cbn [length]; lia).
assert (Eb10 : ew Eb 10%nat = Z_to_bv 64 line)
  by (rewrite OLDb, OLDa by lia; rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (Eb53 : ew Eb 53%nat = w64 (Z.of_nat (length e))) by (rewrite <- R10b; exact Hlen3).
pose proof (ajournal_gx_inner_xR SEGS B PST ARx G 0 [] RE_STK (spZ regs) (ablocks_fp (aout_blks cap out))
  ly S _ W mem md [] ly S _ W (ms_mem ms1) _ _ HJb) as (memS4 & HJin4 & _).
pmkst HS.
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3.
prreg HS (4%bv : bv 5) T4. prreg HS (8%bv : bv 5) T8. prreg HS (10%bv : bv 5) T10.
prreg HS (11%bv : bv 5) T11.
assert (Usp4 : spZ (ms_regs ms1) = spZ regs + (-32))
  by (unfold spZ; rewrite T2, Uspb; apply unsigned_lit_small; unfold spZ in *; lia).
assert (HPRE4 : afn_pre_x SEGS B ARx SL_STK ly S Hp W (ms_regs ms1) (ms_mem ms1) (with_vm_backing (m_vm_lazy md3) mat1 md3) []).
{ eapply (afn_pre_x_atR SEGS B PST ARx (RE_STK + 0) (spZ regs + 0) (ablocks_fp (aout_blks cap out)) ly S _ W memS4 md []
    ly S _ W (ms_mem ms1) _ _ (ms_regs ms1) SL_STK (-32) [] HJin4).
  - rewrite Usp4. lia.
  - reflexivity.
  - lia.
  - unfold SL_STK, SL_FRAME, ASTACK. lia.
  - rewrite WS. unfold SL_STK, SL_FRAME, ASTACK. lia.
  - rewrite T1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite T1, unsigned_lit_small by lia. lia.
  - rewrite T3, OLDb, OLDa by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite T4, OLDb, OLDa by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
  - apply achain_low. unfold s0Z. rewrite T8, Eb10, unsigned_lit_small by lia.
    pose proof (HBOUT line ltac:(lia)). lia. }
assert (ROM3 : rom_view SEGS W (ms_mem ms1)).
{ intros a Hrom.
  assert (Hi : in_img SEGS a) by (destruct Hrom as (sg & Hin & _ & Hr); exists sg; split; [exact Hin | exact Hr]).
  pose proof (Hsegs a Hi) as Hlow. unfold kLowMemEnd in Hlow.
  rewrite KEEPC; [apply HROM; exact Hrom | lia | intros Hw; exact (HLRW a ltac:(lia) Hrom)]. }
eapply (SRrG_bind SEGS R R_trans).
{ exact (SL_R W ly S _ (ms_regs ms1) (ms_mem ms1) _ [] c O mx no cap out line (e ++ [Z_to_bv 8 0]) HPRE4
    ltac:(rewrite T10, Eb10; reflexivity)
    ltac:(rewrite T11, Eb53, unsigned_lit_small by lia; rewrite HLB; unfold re_len, w64; reflexivity)
    AOUT1 ROM3 GAR1 ltac:(pose proof (HBOUT line ltac:(lia)); lia)
    ltac:(rewrite HLB; unfold re_len; pose proof (HBOUT line ltac:(lia)); lia)
    ltac:(right; left; exists q, m; split; [exact Hq | split; [exact Hqo | split; [exact Hql | rewrite HLB; unfold re_len; lia]]])
    (* W7's new premise (a working branch 14d97d478bb): the line is no byte of G_SL.  It lies in the live
       block q, and a heap byte is not an image byte, while every G_SL byte is one. *)
    ltac:(intros a Ha Hin; rewrite HLB in Ha; unfold re_len in Ha;
          exact (HBNI a ltac:(clear - Ha Hql HINB; lia) (proj1 (HG a (HSLG a Hin)))))
    ltac:(rewrite HLB; exact HCAP)
    ltac:(rewrite HLB; exact HLIVE)
    ltac:(rewrite HLB; exact HMO)
    (* the room (C3): send_line runs at relay_event's own S, with the same charge (its length is re_len e) and
       the same peak (re_pk and sl_pk are one function) *)
    kr ltac:(rewrite HLB; exact HRM) HCNT). }
cbv beta. intros W4 c4 Hwle4 (ly' & S' & Hp' & regs4 & mem4 & md4 & k4 & out' & -> & HJsl & HPsl & HAKsl & HMOsl & HRMsl & HPERM & HAOsl & _).
rewrite T1.
pose proof (ajournal_gx_G_mono_xR SEGS B PST ARx (G_SL B RG) G 0 [] SL_STK (spZ (ms_regs ms1))
  (ablocks_fp (aout_blks cap out)) ly S _ W (ms_mem ms1) _ [] ly' S' _ W4 mem4 md4 k4 HSLG HJsl) as HJslG.
pose proof (ajournal_gx_sub_xR SEGS B PST ARx LAWS Hsegs R_trans G RE_STK (spZ regs) 0 [] (ablocks_fp (aout_blks cap out))
  ly S _ W mem md [] ly S _ W (ms_mem ms1) _ _ SL_STK (spZ (ms_regs ms1)) 0 []
  (ablocks_fp (aout_blks cap out)) [] ly' S' _ W4 mem4 md4 k4 HJb HJslG
  ltac:(rewrite Usp4, WS; unfold SL_STK, SL_FRAME, ASTACK; lia)
  ltac:(rewrite Usp4; lia)
  ltac:(rewrite Usp4; lia)
  ltac:(intros a Hf; exfalso; exact (inFP_nil a Hf))
  HG
  ltac:(intros a Hf; left; split; [exact Hf|];
        destruct (inFP_ablocks_fp_inv (aout_blks cap out) a Hf) as (p & n & Hin & Hr);
        exists p, n; split; [apply HOUTB; exact Hin | exact Hr])) as HJc.
pose proof (ajournal_gx_inner_xR SEGS B PST ARx (G_SL B RG) 0 [] SL_STK (spZ (ms_regs ms1))
  (ablocks_fp (aout_blks cap out)) ly S _ W (ms_mem ms1) _ [] ly' S' _ W4 mem4 md4 k4 HJsl) as (memS5 & HJin5 & HagS5).
pose proof HJin5 as (_ & _ & _ & _ & _ & _ & _ & _ & FR5 & _).
pose proof (ajournal_gx_inner_xR SEGS B PST ARx G 0 [] RE_STK (spZ regs) (ablocks_fp (aout_blks cap out))
  ly S _ W mem md _ ly' S' _ W4 mem4 md4 _ HJc) as (memS6 & HJin6 & _).
pose proof HJin6 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPR6 & _).
jafter_call_keep_pi HS 65%nat regs4 (mrestrict (w_H W4) mem4) HPsl [0]%nat HS4.
match type of HS4 with ?ty -> _ => assert (HRK : ty); [|specialize (HS4 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
  unfold stack_region, RE_FRAME.
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Uspb.
  - intros a Ha. apply (mbyte_of_aview SEGS).
    rewrite (FR5 a ltac:(rewrite WS in Hslo; lia) ltac:(rewrite Usp4; unfold SL_STK, SL_FRAME, ASTACK; lia)).
    apply HagS5. rewrite unsigned_lit_small by (rewrite WS in Hslo; lia).
    intros Hin. pose proof (proj1 (HGSL a Hin)). rewrite WS in Hslo. lia.
  - intros a Ha _. apply (apresent_writable SEGS). apply HPR6. rewrite WS. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS.
remember (havoc Eb 65 (map (getr regs4) CLOB)) as Ec eqn:HEc in HS.
assert (HEIc : img_env VAL A_LIM Ec) by (rewrite HEc; apply img_env_havoc; [exact HEIb | cbv; lia]).
assert (OLDc : forall n, (n < 65)%nat -> ew Ec n = ew Eb n) by (intros n Hn; rewrite HEc; apply YN3v.ew_havoc_old; exact Hn).
assert (HAEc : env_agree 32 (Ereg regs re_extra) Ec) by (rewrite HEc; apply env_agree_havoc_ge; [cbv; lia | exact HAEb]).
clear HEc.
assert (SHOKc : sh_ok SEGS re_Bx re_SH Ec (mrestrict (w_H W4) mem4)) by (unfold sh_ok, re_SH; constructor).
assert (Uspc : bv_unsigned (ew Ec 2) = spZ regs) by (rewrite OLDc, OLDb, OLDa by lia; exact Usp).
paj_run_tok_xR RUNR HS HJc SHOKc re_Bspan. { apply awr_ok_x_of0. awr_ok_tac. exact Uspc. }
(* ---- the unlock: a tail call (PTail) at the entry sp, with the caller's ra ---- *)
pose proof HJin5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IMG5 & _).
assert (HFPS : ~ YI16.sink_open_fp (ablocks_fp (aout_blks cap out))).
{ apply sink_closed_ablocks_fp. unfold aout_blks. destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0]; [apply Forall_nil|].
  apply Forall_cons; [|apply Forall_nil]. cbn [fst].
  assert (Hin : In (out, cap) (ablocks B ly S)) by (apply HOUTB; unfold aout_blks; rewrite (proj2 (Z.eqb_neq cap 0) Hc0); left; reflexivity).
  destruct (alx_blocks _ _ _ LAWS ly S _ W mem md out cap HAR Hin) as (_ & Ho4096 & _). lia. }
assert (KEEPL3 : forall a, rg_lock RG <= a < rg_lock RG + 12 ->
  aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem2 a).
{ intros a Ha. rewrite WS in Hslo.
  assert (A1 : aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem3 a).
  { lazymatch type of HFr1 with frame_of ?Ev ?rs _ _ =>
    apply (aview_kept_out Ev rs (w_H W) mem3 (ms_mem ms1) HFr1 a ltac:(lia)) end.
    intros (r & Hin & Hr).
    lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
    cbn [In] in Hin. destruct Hin as [<- | []].
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite Uspb in Hr. lia. }
  assert (A2 : aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) (ms_mem ms0) a)
    by (apply Hfrb; [lia | unfold ESTACK; lia]).
  assert (A3 : aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem2 a).
  { lazymatch type of HFr0 with frame_of ?Ev ?rs _ _ =>
    apply (aview_kept_out Ev rs (w_H W) mem2 (ms_mem ms0) HFr0 a ltac:(lia)) end.
    intros (r & Hin & Hr).
    lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
    cbn [In] in Hin. destruct Hin as [<- | []].
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite Uspa in Hr. lia. }
  rewrite A1, A2, A3. reflexivity. }
assert (KEEPL4 : forall a, rg_lock RG <= a < rg_lock RG + 12 ->
  aview SEGS (w_H W4) (ms_mem ms2) a = aview SEGS (w_H W) mem2 a).
{ intros a Ha. rewrite WS in Hslo.
  assert (A4 : aview SEGS (w_H W4) (ms_mem ms2) a = aview SEGS (w_H W4) mem4 a).
  { lazymatch type of HFr2 with frame_of ?Ev ?rs _ _ =>
    apply (aview_kept_out Ev rs (w_H W4) mem4 (ms_mem ms2) HFr2 a ltac:(lia)) end.
    intros (r & Hin & Hr).
    lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
    cbn [In] in Hin. destruct Hin as [<- | []].
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite Uspc in Hr. lia. }
  assert (A5 : aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W) (ms_mem ms1) a).
  { rewrite (IMG5 a (HLIMG a Ha) ltac:(intros Ho; exact (proj1 (proj2 (HG a (HLG a Ha))) Ho)) (HLE a Ha) (HLPST a Ha)
      ltac:(apply fp_spares_closed; exact HFPS)).
    apply HagS5. rewrite unsigned_lit_small by lia. intros Hin. exact (HLD a Ha Hin). }
  rewrite A4, A5. apply KEEPL3. exact Ha. }
lazymatch goal with Hx : mem_grows _ (mrestrict _ (ms_mem ms2)) |- _ => pose proof Hx as MG4 end.
assert (WKEEP2 : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) ->
  writable_at SEGS (mrestrict (w_H W) mem) a -> writable_at SEGS (mrestrict (w_H W4) (ms_mem ms2)) a).
{ intros a Hi Ho He Hw.
  apply (writable_at_grows SEGS (mrestrict (w_H W4) mem4) (mrestrict (w_H W4) (ms_mem ms2)) a MG4).
  apply (re_wr_pres2 W W4 (ms_mem ms1) mem4 a ltac:(intros Hpr; exact (HAKsl a Hi Ho He Hpr))).
  exact (WKEEP a Hw). }
assert (LK0b : val_mem SEGS (mrestrict (w_H W) mem2) (rg_lock RG) 4 0).
{ apply (re_vm_kept W W (ms_mem ms) mem2); [|exact LK0a].
  intros x Hx. apply Hfra; [rewrite WS in Hslo; lia | intros Hw; cbn in Hx; lia | unfold ESTACK; rewrite WS in Hslo; cbn in Hx; lia]. }
assert (LK8b : val_mem SEGS (mrestrict (w_H W) mem2) (rg_lock RG + 8) 4 0).
{ apply (re_vm_kept W W (ms_mem ms) mem2); [|exact LK8a].
  intros x Hx. apply Hfra; [rewrite WS in Hslo; lia | intros Hw; cbn in Hx; lia | unfold ESTACK; rewrite WS in Hslo; cbn in Hx; lia]. }
assert (LKF : alock_at RG W4 (ms_mem ms2) true).
{ unfold alock_at, arm. split; [|split; [|split]].
  - apply (re_vm_kept W W4 mem2 (ms_mem ms2)); [intros x Hx; apply KEEPL4; cbn in Hx; lia | exact LK0b].
  - apply (re_vm_kept W W4 mem2 (ms_mem ms2)); [intros x Hx; apply KEEPL4; cbn in Hx; lia | exact Hlk2].
  - apply (re_vm_kept W W4 mem2 (ms_mem ms2)); [intros x Hx; apply KEEPL4; cbn in Hx; lia | exact LK8b].
  - intros i Hi. apply WKEEP2.
    + apply HLIMG. lia.
    + intros Ho. exact (proj1 (proj2 (HG (rg_lock RG + i) (HLG (rg_lock RG + i) ltac:(lia)))) Ho).
    + exact (HLE (rg_lock RG + i) ltac:(lia)).
    + exact (LKW i Hi). }
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G 0 [] RE_STK (spZ regs) (ablocks_fp (aout_blks cap out))
  ly S _ W mem md _ ly' S' _ W4 (ms_mem ms2) _ _ HJc) as HARf.
pmkst HS.
assert (APR1 : aregs_preserved regs (ms_regs ms2))
  by (eapply (aregs_preserved_of_st_ok SEGS _ Ec _ _ regs re_extra HS); [exact HAEc | vm_compute; reflexivity]).
prreg HS (1%bv : bv 5) V1. prreg HS (2%bv : bv 5) V2. prreg HS (3%bv : bv 5) V3.
prreg HS (4%bv : bv 5) V4. prreg HS (10%bv : bv 5) V10.
assert (Usp5 : spZ (ms_regs ms2) = spZ regs + 0) by (unfold spZ in *; rewrite V2, Uspc; lia).
assert (Ec244 : ew Ec 244%nat = Z_to_bv 64 (rg_lock RG)).
{ apply bv_eq. rewrite unsigned_lit_small by lia. rewrite <- HV3.
  change 244%nat with (A_OBJ 3). exact (HEIc (A_OBJ 3) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)). }
assert (V1' : getr (ms_regs ms2) 1 = getr regs 1)
  by (rewrite V1, OLDc, OLDb, OLDa by lia; exact (EE 1%nat 1%bv eq_refl)).
pose proof LKF as (LK0f & LK4f & LK8f & LKWf). unfold arm in LK0f, LK4f, LK8f, LKWf.
assert (HNOWN2 : forall a, rg_lock RG <= a < rg_lock RG + 12 -> ~ aowned B ly' S' a).
{ intros a Ha Ho. destruct (HG a (HLG a Ha)) as (Hi & Hno & _).
  apply Hno. exact (proj1 (alx_owned_image _ _ _ LAWS ly' S' _ W4 (ms_mem ms2) _ a HARf Hi) Ho). }
eapply (SRrG_bind SEGS R R_trans).
{ eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R G 0 [] ESTACK (SIGMA WS_pthread_mutex_unlock)
    (fun a => rg_lock RG + 4 <= a < rg_lock RG + 8)
    (fun regs' mem' => getr regs' 10 = w64 0 /\ val_mem SEGS (mrestrict (w_H W4) mem') (rg_lock RG + 4) 4 0)
    W4 (ms_regs ms2) (ms_mem ms2) RE_STK (spZ regs) (ablocks_fp (aout_blks cap out)) ly S _ W mem md _
    ly' S' _ _ _ 0 _ HG eq_refl HJc Usp5 eq_refl ltac:(lia) ltac:(lia) ltac:(rewrite WS; unfold ESTACK; lia)
    ltac:(rewrite V3, OLDc, OLDb, OLDa by lia; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp)
    ltac:(rewrite V4, OLDc, OLDb, OLDa by lia; rewrite (EE 4%nat 4%bv eq_refl); exact Htp)
    V1' Hra).
  - intros a. lia.
  - intros a Hwa _. exact (re_av_ne W4 (ms_mem ms2) (rg_lock RG + 4) 4%nat 16 a LK4f ltac:(cbn; lia)).
  - intros a Hwa HnG. exfalso. apply HnG. apply HLG. lia.
  - intros HPRE5 HSC5.
    exact (AUNLOCK ly' S' _ W4 (ms_regs ms2) (ms_mem ms2) _ (rg_lock RG) HPRE5
      ltac:(rewrite V10, Ec244; reflexivity) ltac:(lia) HLA ltac:(lia) LK0f LK4f LK8f
      ltac:(intros a Ha; split;
            [ destruct (Z_lt_le_dec a (rg_lock RG + 4)) as [Hlt | Hge];
              [ exact (re_av_ne W4 (ms_mem ms2) (rg_lock RG) 4%nat 0 a LK0f ltac:(cbn; lia))
              | destruct (Z_lt_le_dec a (rg_lock RG + 8)) as [Hlt2 | Hge2];
                [ exact (re_av_ne W4 (ms_mem ms2) (rg_lock RG + 4) 4%nat 16 a LK4f ltac:(cbn; lia))
                | exact (re_av_ne W4 (ms_mem ms2) (rg_lock RG + 8) 4%nat 0 a LK8f ltac:(cbn; lia)) ] ]
            | rewrite Usp5; unfold ESTACK; rewrite WS in Hslo; lia ])
      ltac:(intros a Ha; split;
            [ replace a with (rg_lock RG + (a - rg_lock RG)) by lia; exact (LKWf (a - rg_lock RG) ltac:(lia))
            | split; [ apply HNOWN2; lia | rewrite Usp5; unfold ESTACK; rewrite WS in Hslo; lia ] ])
      (fun a Ha HK => proj2 (proj2 (HG a (HLG a ltac:(lia)))) (proj1 (proj2 HK)))). }
cbv beta. intros W5 c5 Hwle5 (-> & regs5 & mem5 & md5 & -> & HJf & HPf & (HA0f & HLK4f) & Hfrf & Hpresf).
(* ---- the post ---- *)
rewrite HLB in HMOsl, HPERM, HAOsl.
assert (HOUTB2 : forall b, In b (aout_blks (sl_cap c mx no cap (re_len e)) out') -> In b (ablocks B ly' S')).
{ intros b Hb. destruct HPERM as (rest & HP1 & HP2).
  eapply Permutation_in; [apply Permutation_sym; exact HP2|]. apply in_or_app. left. exact Hb. }
assert (KEEPF : forall a, 0 <= a < alloc_ceiling -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) ->
  aview SEGS (w_H W4) mem5 a = aview SEGS (w_H W4) mem4 a).
{ intros a Ha Hnw. rewrite WS in Hslo.
  rewrite (Hfrf a ltac:(lia) Hnw ltac:(unfold ESTACK; lia)).
  lazymatch type of HFr2 with frame_of ?Ev ?rs _ _ =>
  apply (aview_kept_out Ev rs (w_H W4) mem4 (ms_mem ms2) HFr2 a ltac:(lia)) end.
  intros (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite Uspc in Hr. lia. }
assert (WKEEPF : forall a, writable_at SEGS (mrestrict (w_H W4) mem4) a -> writable_at SEGS (mrestrict (w_H W4) mem5) a).
{ intros a Hw. apply (re_wr_pres2 W4 W4 (ms_mem ms2) mem5 a ltac:(intros Hpr; exact (Hpresf a Hpr))).
  apply (writable_at_grows SEGS (mrestrict (w_H W4) mem4) (mrestrict (w_H W4) (ms_mem ms2)) a MG4). exact Hw. }
pose proof (ajournal_gx_AR_xR SEGS B PST ARx (G_SL B RG) 0 [] SL_STK (spZ (ms_regs ms1)) (ablocks_fp (aout_blks cap out))
  ly S _ W (ms_mem ms1) _ [] ly' S' _ W4 mem4 md4 k4 HJsl) as HAR4.
assert (AKEPT2 : akept W4 mem4 W4 mem5 (aout_fp B RG (sl_cap c mx no cap (re_len e)) out')).
{ intros r Hr a Har.
  assert (HR : 0 <= a < alloc_ceiling /\ ~ (rg_lock RG + 4 <= a < rg_lock RG + 8)).
  { unfold aout_fp in Hr. cbn [In] in Hr.
    destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]];
    cbn [fst snd] in Har.
    - split; [lia | intros Hw; exact (proj1 (HAOD a ltac:(lia)) ltac:(lia))].
    - exact (HGSL a (HINSL a ltac:(tauto))).
    - exact (HGSL a (HINSL a ltac:(tauto))).
    - exact (HGSL a (HINSL a ltac:(tauto))).
    - split; [lia | intros Hw; exact (proj1 (proj2 (HAOD a ltac:(lia))) ltac:(lia))].
    - exact (HGSL a (HINSL a ltac:(tauto))).
    - split; [lia | intros Hw; exact (proj2 (proj2 (HAOD a ltac:(lia))) ltac:(lia))].
    - exact (HGSL a (HINSL a ltac:(tauto))).
    - exact (HGSL a (HINSL a ltac:(tauto))).
    - destruct (Z.eqb_spec (sl_cap c mx no cap (re_len e)) 0) as [Hc0 | Hc0]; [destruct Hr|].
      cbn [In] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Har.
      assert (Hin : In (out', sl_cap c mx no cap (re_len e)) (ablocks B ly' S'))
        by (apply HOUTB2; unfold aout_blks; rewrite (proj2 (Z.eqb_neq _ 0) Hc0); left; reflexivity).
      destruct (alx_blocks _ _ _ LAWS ly' S' _ W4 mem4 md4 out' _ HAR4 Hin) as (_ & Ho4096 & Hoceil & _).
      pose proof (proj1 (req_size_pos (sl_cap c mx no cap (re_len e)) ltac:(lia))) as Hrs1.
      assert (Hrq : req_size (sl_cap c mx no cap (re_len e)) = sl_cap c mx no cap (re_len e))
        by (unfold req_size; destruct (Z.eqb_spec (sl_cap c mx no cap (re_len e)) 0); lia).
      split; [lia|]. intros Hw.
      exact (blk_img_x SEGS B ARx LAWS ly' S' _ W4 mem4 md4 out' _ a HAR4 Hin ltac:(lia) (HLIMG a ltac:(lia))). }
  split; [apply KEEPF; [exact (proj1 HR) | exact (proj2 HR)] | exact (WKEEPF a)]. }
apply (SRrG_ret SEGS R R_refl). unfold re_post_xR.
exists ly', S', Hp', regs5, mem5, md5, (0 + k4), out'.
split; [reflexivity|].
split; [exact HJf|].
split; [exact (aregs_preserved_trans regs (ms_regs ms2) regs5 APR1 HPf)|].
split.
{ intros a Hi Ho He Hpa. apply Hpresf.
  apply (apresent_grows (w_H W4) mem4 (ms_mem ms2) a MG4).
  apply (HAKsl a Hi Ho He).
  apply (apresent_grows (w_H W) mem3 (ms_mem ms1) a MG3).
  apply (Hpresb a).
  apply (apresent_grows (w_H W) mem2 (ms_mem ms0) a MG2).
  apply (Hpresa a).
  apply (apresent_grows (w_H W) mem (ms_mem ms) a MG1).
  exact Hpa. }
split; [exact HMOsl|].
split; [exact HRMsl|].
split; [exact HPERM|].
split.
{ exact (aout_at_kept B RG ly' S' W4 mem4 ly' S' W4 mem5 _ _ mx _ _ out' HAOsl AKEPT2 HOUTB2). }
unfold alock_at, arm. split; [|split; [|split]].
- apply (re_vm_kept W4 W4 (ms_mem ms2) mem5); [|exact LK0f].
  intros x Hx. cbn in Hx. rewrite WS in Hslo.
  apply Hfrf; [lia | intros Hw; lia | unfold ESTACK; lia].
- exact HLK4f.
- apply (re_vm_kept W4 W4 (ms_mem ms2) mem5); [|exact LK8f].
  intros x Hx. cbn in Hx. rewrite WS in Hslo.
  apply Hfrf; [lia | intros Hw; lia | unfold ESTACK; lia].
- intros i Hi.
  apply (re_wr_pres2 W4 W4 (ms_mem ms2) mem5 (rg_lock RG + i) ltac:(intros Hpr; exact (Hpresf (rg_lock RG + i) Hpr))).
  exact (LKWf i Hi).
Qed.
End cR.
(* the strict walk is the R walk at R := wle (route R's rule: one walk text) *)
Theorem pb_relay_event_x : re_spec_x B PST ARx MT RP MMAX G RG (BASE + AF_fr_relay_event).
Proof.
eapply (pb_relay_event_xR (@wle SEGS));
  first [ exact SL | intros ? ? H; exact H | intros ?; apply wle_refl
        | intros ? ? ? H1 H2; eapply wle_trans; [exact H1 | exact H2] ].
Qed.
End c.
End b.
End a.
Print Assumptions pb_relay_event_x.
