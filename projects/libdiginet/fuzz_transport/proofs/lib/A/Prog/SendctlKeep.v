(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 369 of its 416 lines of code are new or changed and 1877 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SendctlRel.v; 559 of its 645 lines of code are new or changed and 330 lines of the source are left out. *)
(* SendctlKeep: Lemma sendctl_keep : sendctl_keep_stmt (lib/A/Prog/SendctlCut.v), the keep piece of send_control,
   offsets +0x1b4 .. +0x1d4 of the listing lib/A/Prog/DgnTransportList.v (fuzz_transport.asan 0x86f10 .. 0x86f30),
   taken with kp <> 0 and falling into the send cut sendctl_send_at at +0x1d8.

   What the code does. +0x1b4 `mv a0, s6` (a0 = kp), +0x1b8 `mv a1, s7` (a1 = f = F + 32), +0x1bc `mv a2, s5`
   (a2 = n = 60); +0x1c0 `jal __asan_memcpy` (transport_sigma TS___asan_memcpy), return +0x1c4: the 60 bytes at f
   are copied to kp. +0x1c4 `srli a0, s4, 3`, +0x1c8 `add a0, a0, s10` and +0x1cc `lbu a0, 0(a0)`: the shadow byte
   of klp (s4 = klp, s10 = SHADOW_OFF); +0x1d0 `bnez a0` is NOT taken (the shadow token of lib/A/Prog/PaShadow.v
   reads the byte as 0 from the run's shadow entry SKP_SH, whose range_addressable is the decode_rd_ok of
   [klp, klp + 8) the cut carries), so the error path errpath_store8 at +0x3d4 is unreached; +0x1d4 `sd s5, 0(s4)`:
   the 8-byte store of n = 60 at klp, the OUT CELL.

   Two runs of the position-abstract engine over the caller's G journal (lib/A/Prog/TransportGRunA.v paj_run_x /
   paj_run_to_x):
     run A  +0x1b4 .. +0x1c0  three register moves and the `jal`; no memory region, no shadow entry; it stops at
                              the call of __asan_memcpy;
     memcpy                   lib/A/Prog/TransportGCg.v gx_intrin_at at OCpy: d = kp, x = F + 32, n = 60. The
                              destination's write right is the caller's (transport_twr_ok_g: every byte of
                              [kp, kp + 60) is an awr_byte of the caller's journal, moved to the walk's own frame
                              list by skp_awr_move, and outside the call's ESTACK window by decode_off_win); its
                              amem_range, range_addressable and shadow_hull_vis come from the cut's decode_rd_ok;
                              the source [F + 32, F + 92) lies in the frame the walk owns (src_ok, amem_range and
                              the two shadow facts from the cut's decode_rd_ok of f), apart from the destination
                              because an awr_byte of the caller is never a byte of the own frame
                              (TransportGFrame.v dkg_nf_sep_gw);
     run B  +0x1c4 .. +0x1d4  the shadow check of klp and the 8-byte store, a run to +0x1d8. Its one region is
                              [klp, klp + 8) (writable: the cut carries those bytes' presence), its shadow entry
                              SKP_SH and its shadow base SKP_Bx = s10.

   The piece then applies sendctl_send_at at +0x1d8. Every byte outside [kp, kp + 60), [klp, klp + 8) and the
   ESTACK window below the realigned sp is the cut's (KA) and presence grows, so
   - acall_kept_g (read at the memory with the out cells put back) carries by TransportGFrame.v dk_kept_step_gw at
     the two gover memories (skp_gover_view / skp_gover_pres: an out byte reads memc on both sides);
   - the world relation at Bw carries by TWorldA.v tw_kept_GA (no byte of G is a byte of [kp, kp + 60) or of
     [klp, klp + 8), and the ESTACK window lies above alloc_ceiling);
   - trans_rom_view_rd carries (a TRANS_RO_RD byte is an image byte, and an awr_byte of the caller is not);
   - the 60 bytes at f, their decode_rd_ok, the twelve saved words and the frame's last word carry;
   - the out cells: the 60 bytes at kp are f's (the copy's own equation, skp_garr8_move) and the 8 bytes at klp
     hold TW.put 8 60 (the store's chunk, read off the run's region). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI09 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_frame_build_cg io_send_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import send_control_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import CanKit TransportGFrame SendctlCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TWorldLemmas TImg TSess0 TSess.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The two symbolic states                                          *)
(* ------------------------------------------------------------------ *)

(* The return address of the `jal __asan_memcpy` at +0x1c0, and run B's first instruction. *)
Definition SKP_C1 : Z := AF_send_control + 0x1c4.
(* Run A reads and writes no byte, so its shadow span is empty. *)
Definition SKP_B0 : Z * Z := (0, 0).
Definition ss_skpa : sstate := mkSS SENDCTL_KEEP sr_atoms [] None (mkFacts [] [] []).
(* Run B's one region: the 8 bytes at klp (s4 = atom 20), written by `sd s5, 0(s4)`. *)
Definition skp_rg_kl : YP09.region := YP09.mkRegion (Some 20%nat) 0 8 0 8 [].
(* klp lies in application memory (the cut's decode_rd_ok gives amem_range); s10 (atom 26) is the shadow base. *)
Definition skp_facts : facts :=
  mkFacts [(20%nat, mkAF 0 (2 ^ 47 - 8) 0); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_skpb : sstate := mkSS SKP_C1 sr_atoms [skp_rg_kl] None skp_facts.
(* The shadow entry the check of the store at klp reads, and the shadow base of the token engine. *)
Definition SKP_SH : list shent := [mkSHE 20 0 8].
Definition SKP_Bx : sv := SOff 26 0.

(* The write obligation's regions, computed. *)
Ltac skp_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.

Section keep. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The walk's valuation: the 32 registers at the run's first instruction, no extra atom. *)
Definition skp_E (rg : bvmap 5 word) : env := Eimg (PI := PI_transport) (Ereg rg []).

Lemma skp_ew_reg : forall rg n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (skp_E rg) n = YK11.getr rg r.
Proof. intros rg n r Hn. unfold skp_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.

Lemma skp_env_img : forall rg, img_env VAL A_LIM (skp_E rg).
Proof. intros rg. unfold skp_E. apply Eimg_env. Qed.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac skp_reg HS r v H tac :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
(* A register the run does not touch, from the equation Q of its value at the run's start. *)
Ltac skp_kreg HS rg r n Q H :=
  lazymatch type of Q with _ = ?v =>
    skp_reg HS r v H
      ltac:(cbn [sv_denot]; rewrite (skp_ew_reg rg n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.
(* ---- the two entry states ---- *)

Lemma skp_entry_a : forall (W : world segs) rg mem,
  st_ok_pi segs VAL (skp_E rg) ss_skpa
    (restrict (w_H W) (@YK11.mkst fx rg (Z_to_bv 64 (BASE + SENDCTL_KEEP)) mem (YK11.seg_rom segs))).
Proof.
intros W rg mem. rewrite restrict_mkst_fx. unfold ss_skpa.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

Lemma skp_entry_b : forall (W : world segs) rg mem (klp : Z),
  YK11.getr rg 20 = w64 klp -> YK11.getr rg 26 = w64 SHADOW_OFF ->
  0 <= klp -> amem_range klp 8 ->
  (forall i, 0 <= i < 8 -> apresent (w_H W) mem (klp + i)) ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF klp 8 ->
  st_ok_pi segs VAL (skp_E rg) ss_skpb
    (restrict (w_H W) (@YK11.mkst fx rg (Z_to_bv 64 (BASE + SKP_C1)) mem (YK11.seg_rom segs))) /\
  sh_ok segs SKP_Bx SKP_SH (skp_E rg) (mrestrict (w_H W) mem).
Proof.
intros W rg mem klp R20 R26 Hk0 Hamr Hpres HRA.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold amem_range in Hamr.
assert (Hkhi : klp + 8 <= 2 ^ 47 - 1).
{ destruct Hamr as [Ha | [Ha Hb]]; unfold kLowMemEnd, kHighMemEnd in *; lia. }
assert (U20 : bv_unsigned (ew (skp_E rg) 20) = klp)
  by (rewrite (skp_ew_reg rg 20 20%bv eq_refl), R20; unfold w64; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew (skp_E rg) 26) = SHADOW_OFF)
  by (rewrite (skp_ew_reg rg 26 26%bv eq_refl), R26; unfold w64; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_skpb.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold skp_rg_kl, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U20. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  + apply pairwise_disjoint_of_extents.
    unfold skp_rg_kl, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  + unfold skp_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U20, U26.
    rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
- unfold sh_ok, SKP_SH. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H W) mem _ SKP_Bx 20 klp 8 klp 0 8 HRA).
  + unfold U, SKP_Bx. cbn [sv_denot]. rewrite U26, Z.add_0_r. apply unsigned_lit_small.
    unfold SHADOW_OFF; lia.
  + unfold U. cbn [sv_denot]. rewrite U20, Z.add_0_r. apply unsigned_lit_small. lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF.
    destruct Hamr as [Ha | [Ha Hb]]; unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia.
Qed.

(* ---- small kit: bytes, cells, write rights ---- *)

(* Two views that agree at one address agree on the byte there. *)
Lemma skp_mbyte_eq : forall (H : word -> bool) (m m0 : word -> option byte) a b,
  aview segs H m a = aview segs H m0 b -> mbyte segs (mrestrict H m) a = mbyte segs (mrestrict H m0) b.
Proof.
intros H m m0 a b Hv. unfold aview in Hv.
destruct (mbyte segs (mrestrict H m) a) as [x|] eqn:E1; destruct (mbyte segs (mrestrict H m0) b) as [y|] eqn:E2;
cbn in Hv; try discriminate; [|reflexivity].
injection Hv as Hv. f_equal. apply bv_eq. exact Hv.
Qed.

(* A cell read at one place and written at another (the copy), or kept in place (q = q0). *)
Lemma skp_garr8_move : forall (H : word -> bool) (m m0 : word -> option byte) q q0 (l : list Z),
  (forall j, (j < length l)%nat -> aview segs H m (q + Z.of_nat j) = aview segs H m0 (q0 + Z.of_nat j)) ->
  garr8 segs (mrestrict H m0) q0 l -> garr8 segs (mrestrict H m) q l.
Proof.
intros H m m0 q q0 l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hb]. split; [|exact Hb].
intros i Hi. assert (Ei : i = 0%nat) by lia. subst i.
change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
rewrite (skp_mbyte_eq H m m0 (q + Z.of_nat j) (q0 + Z.of_nat j) (Hk j Hj)).
specialize (Hv 0%nat ltac:(lia)). change (Z.of_nat 0) with 0 in Hv. rewrite Z.add_0_r in Hv. exact Hv.
Qed.

(* At the memory with the out cells put back, a byte the walk keeps is kept: an out byte reads memc on both sides. *)
Lemma skp_gover_view : forall (outs : list (Z * Z)) (H : word -> bool) (m m' mc : word -> option byte) a,
  (inGb outs (bv_unsigned (Z_to_bv 64 a)) = false -> aview segs H m' a = aview segs H m a) ->
  aview segs H (gover outs m' mc) a = aview segs H (gover outs m mc) a.
Proof.
intros outs H m m' mc a Hk. destruct (inGb outs (bv_unsigned (Z_to_bv 64 a))) eqn:Eb.
- apply (aview_eq_of segs). unfold mrestrict, gover. rewrite Eb. reflexivity.
- rewrite (aview_eq_of segs H m' (gover outs m' mc) a) by (unfold mrestrict, gover; rewrite Eb; reflexivity).
  rewrite (aview_eq_of segs H m (gover outs m mc) a) by (unfold mrestrict, gover; rewrite Eb; reflexivity).
  exact (Hk eq_refl).
Qed.

Lemma skp_gover_pres : forall (outs : list (Z * Z)) (H : word -> bool) (m m' mc : word -> option byte) a,
  (apresent H m a -> apresent H m' a) ->
  apresent H (gover outs m mc) a -> apresent H (gover outs m' mc) a.
Proof.
intros outs H m m' mc a Hg Hp. unfold apresent, gover in Hp |- *. cbv beta in Hp |- *.
destruct Hp as (Hh & b & Hb).
destruct (inGb outs (bv_unsigned (Z_to_bv 64 a))) eqn:Eb.
- split; [exact Hh | exists b; exact Hb].
- destruct (Hg (conj Hh (ex_intro _ b Hb))) as (Hh' & b' & Hb').
  split; [exact Hh' | exists b'; exact Hb'].
Qed.

(* A write right of the caller's journal is one of the walk's own journal (one more owned frame, the same frame
   addresses, the same blocks up to a permutation). *)
Lemma skp_awr_move : forall STKq sp0q FPq lyq Sq lycq Scq ly2q S2q ownq x a,
  Permutation (ablocks B ly2q S2q) (ablocks B lycq Scq) -> ly_F ly2q = ly_F lycq ->
  awr_byte STKq sp0q FPq (ablocks B lyq Sq) (ablocks B lycq Scq) lycq ownq a ->
  awr_byte STKq sp0q FPq (ablocks B lyq Sq) (ablocks B ly2q S2q) ly2q (x :: ownq) a.
Proof.
intros STKq sp0q FPq lyq Sq lycq Scq ly2q S2q ownq x a Hperm ELF Hw.
assert (Hbl : forall bm, In bm (ablocks B lycq Scq) -> In bm (ablocks B ly2q S2q))
  by (intros bm Hb; eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hb]).
assert (Efa : forall c p, frame_addr ly2q c p = frame_addr lycq c p)
  by (intros c p; unfold frame_addr; rewrite ELF; reflexivity).
destruct Hw as [Hw | [(Hf & b & n & Hb & Hr) | [(b & n & Hb & Hnb & Hr) | (c0 & p0 & Hc & Hr)]]].
- left. exact Hw.
- right; left. split; [exact Hf|]. exists b, n. split; [exact (Hbl _ Hb) | exact Hr].
- right; right; left. exists b, n. split; [exact (Hbl _ Hb)|]. split; [exact Hnb | exact Hr].
- right; right; right. exists c0, p0. split; [right; exact Hc|]. rewrite (Efa c0 p0). exact Hr.
Qed.

(* A byte the caller's journal lets a callee write is never an image byte. *)
Lemma skp_awr_not_img : forall STKq sp0q FPq lyq Sq lycq Scq (Wq : world segs) memq mdq ownq a,
  AR_laws segs B -> @AR rc segs B lycq Scq Wq memq mdq ->
  frames Scq = ownq ++ frames Sq -> alloc_ceiling <= sp0q - STKq ->
  awr_byte STKq sp0q FPq (ablocks B lyq Sq) (ablocks B lycq Scq) lycq ownq a ->
  ~ in_img segs a.
Proof.
intros STKq sp0q FPq lyq Sq lycq Scq Wq memq mdq ownq a LAWSq HARq Hfr Hce Hw Hi.
pose proof asan_consts as (D1 & D2 & D3 & D4 & D5).
pose proof (transport_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
destruct Hw as [Hw | [(_ & b & n & Hb & Hr) | [(b & n & Hb & _ & Hr) | (c0 & p0 & Hc & Hr)]]].
- lia.
- exact (blk_img segs B LAWSq lycq Scq Wq memq mdq b n a HARq Hb Hr Hi).
- exact (blk_img segs B LAWSq lycq Scq Wq memq mdq b n a HARq Hb Hr Hi).
- assert (Hc' : In (c0, p0) (frames Scq)) by (rewrite Hfr; apply in_or_app; left; exact Hc).
  destruct Hr as [Hr | Hr]; unfold in_zr in Hr; cbn [fst snd] in Hr.
  + exact (frm_img segs B LAWSq lycq Scq Wq memq mdq c0 p0 a HARq Hc' Hr Hi).
  + destruct (frames_bounds segs B LAWSq lycq Scq Wq memq mdq c0 p0 HARq Hc') as (F1 & F2 & _).
    pose proof (Z.div_pos (frame_addr lycq c0 p0) 8 ltac:(lia) ltac:(lia)).
    unfold shadow_addr, SHADOW_OFF in Hr. lia.
Qed.

(* A byte of a caller's frame or of its shadow lies below the allocation ceiling. *)
Lemma skp_frame_below : forall lycq Scq (Wq : world segs) memq mdq cid pos a,
  AR_laws segs B -> @AR rc segs B lycq Scq Wq memq mdq -> In (cid, pos) (frames Scq) ->
  (in_zr a (frame_rng lycq (cid, pos)) \/
   in_zr a (shadow_addr (frame_addr lycq cid pos), fs_frame_bytes cid / 8)) ->
  0 <= a < alloc_ceiling.
Proof.
intros lycq Scq Wq memq mdq cid pos a LAWSq HARq Hin Hr.
pose proof asan_consts as (D1 & D2 & D3 & D4 & D5).
destruct (frames_bounds segs B LAWSq lycq Scq Wq memq mdq cid pos HARq Hin) as (F1 & F2 & _).
pose proof (fs_frame_bytes_nonneg cid) as Hfs.
destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
pose proof (shadow_range_end (frame_addr lycq cid pos) (fs_frame_bytes cid) Hfs) as Hse.
assert (Hd : (frame_addr lycq cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
pose proof (Z.div_pos (frame_addr lycq cid pos) 8 ltac:(lia) ltac:(lia)).
unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The piece                                                         *)
(* ------------------------------------------------------------------ *)

Lemma sendctl_keep : @sendctl_keep_stmt fx rc B MT.
Proof.
unfold sendctl_keep_stmt, sendctl_keep_at.
intros SEND LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs cmd ack kp klp r K KL f TF
  Bw Bw' pos sp1 F ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HREGS HKP0.
pose proof LAWS0 as HLAWS. pose proof CALLEES as HCALL. pose proof HFIX as HFIXs.
destruct LAWS0 as (HPCS & HCELLS & HSC & HROU & HRNE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGNE).
destruct CALLEES as (ASM & FBC & AI & IOS).
destruct HFIX as (HJ0 & Hret & Hra4 & Hgp & Htp & Hsa0 & Hsa1 & Hsa2 & Hsa3 & Hsa4 & Hsp16 & Hlo & Hhi & Hcmd &
  Hackr & HKP & HTW0 & Hgf0 & HM & HROM & HFLY & HCMDL & HCNT & HEVb & ESP1 & EF & HF0 & HF64 & HFc & HFapp).
destruct HCUR as ((HJ1 & He & Hfrs & Hperm & ELF & Hmo & HK & Hsaved & HFLw & HKLPp) & HTW2 & HROM2 & HLF & HGF &
  HRDF & HIN).
destruct HREGS as (((R2 & R3 & R4 & R8 & R9 & R18 & R21 & R24 & R25 & R27) & R19 & R23 & R26) & R20 & R22).
destruct HKP as [Hk0 | (Hkpos & HinF & HTWK & HRDK & HOWK & HNGK & HLK & HGK & HKLP8 & HTWKL & HRDKL & HOWKL &
  HNGKL & HLKL & HGKL & HSEP)]; [exfalso; exact (HKP0 Hk0)|].
destruct HIN as [Hk0 | (HGKm & HRDKm & HGKLm & HRDKLm)]; [exfalso; exact (HKP0 Hk0)|].
destruct HKLPp as [Hk0 | HKLPp]; [exfalso; exact (HKP0 Hk0)|].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
change SENDCTL_F with 60 in *.
change SENDCTL_FOFF with 32 in *.
change SENDCTL_FBYTES with 256 in *.
assert (EST : ESTACK = 4096) by reflexivity.
assert (HBS : 4240 <= SENDCTL_STK).
{ unfold SENDCTL_STK, SENDCTL_FRAME, SENDCTL_ALIGN.
  lazymatch goal with |- _ <= _ + _ + Z.max ?a ?b =>
    pose proof (Z.le_max_l a b) as Hmx; assert (Ha : a = 4096) by reflexivity end.
  lia. }
(* the entry journal's stack facts *)
pose proof HJ0 as (HSTK0 & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (HARc0 & _ & _ & _ & _ & HfrsC & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk0 & _).
pose proof Hstk0 as (Hsp0a & HSTKnn & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
assert (Hce : alloc_ceiling <= spZ regs - SENDCTL_STK) by lia.
assert (Hceil0 : alloc_ceiling <= sp0 - STK) by lia.
(* the realigned stack pointer *)
unfold SENDCTL_FRAME in ESP1.
replace (spZ regs - 128) with (spZ regs + -128) in ESP1 by lia.
destruct (can_sp1_facts (spZ regs + -128) ltac:(lia)
  ltac:(rewrite <- Zplus_mod_idemp_l, Hsp16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
rewrite <- ESP1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1b : spZ regs - 144 <= sp1 <= spZ regs - 128) by lia.
(* the AR state at the cut *)
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
(* the own frame and its separations *)
assert (Hin2 : In (SENDCTL_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hb; eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hb]).
set (FL := flag_addr lyc SENDCTL_CID pos) in *.
destruct (dkg_nf_sep_gw segs B LAWS transport_segs_low lyc Sc ly2 S2 W2 mem2 md2 SENDCTL_CID pos F FL HAR2 Hfrs
  Hbl ELF EF eq_refl FFL) as (N1 & N2 & N3 & N4).
assert (NFW : forall a, awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a ->
  ~ dkg_nf SENDCTL_CID F FL a).
{ intros a Hw Hn.
  destruct Hw as [Hw | [(_ & b & m & Hb & Hr) | [(b & m & Hb & _ & Hr) | (c0 & p0 & Hc & Hr)]]].
  - pose proof (N4 a Hn). lia.
  - apply (N1 b m (a - b) Hb ltac:(lia)). replace (b + (a - b)) with a by lia. exact Hn.
  - apply (N1 b m (a - b) Hb ltac:(lia)). replace (b + (a - b)) with a by lia. exact Hn.
  - assert (Hc' : In (c0, p0) (frames Sc)) by (rewrite HfrsC; apply in_or_app; left; exact Hc).
    exact (N3 c0 p0 a Hc' Hr Hn). }
(* the two written ranges are write rights of the caller *)
assert (HKPF : forall a, kp <= a < kp + 60 ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a).
{ intros a Ha. destruct (HTWK a Ha) as [(Hw & _ & _ & _) | Hg]; [exact Hw|].
  exfalso. exact (HNGK a Ha Hg). }
assert (HKLPF : forall a, klp <= a < klp + 8 ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a).
{ intros a Ha. destruct (HTWKL a Ha) as [(Hw & _ & _ & _) | Hg]; [exact Hw|].
  exfalso. exact (HNGKL a Ha Hg). }
assert (NKF : forall a, kp <= a < kp + 60 -> ~ dkg_nf SENDCTL_CID F FL a)
  by (intros a Ha; exact (NFW a (HKPF a Ha))).
assert (NKLF : forall a, klp <= a < klp + 8 -> ~ dkg_nf SENDCTL_CID F FL a)
  by (intros a Ha; exact (NFW a (HKLPF a Ha))).
assert (NKimg : forall a, kp <= a < kp + 60 -> ~ in_img segs a)
  by (intros a Ha; exact (skp_awr_not_img STK sp0 FP ly S lyc Sc W memc mdc own a LAWS HARc0 HfrsC Hceil0
        (HKPF a Ha))).
assert (NKLimg : forall a, klp <= a < klp + 8 -> ~ in_img segs a)
  by (intros a Ha; exact (skp_awr_not_img STK sp0 FP ly S lyc Sc W memc mdc own a LAWS HARc0 HfrsC Hceil0
        (HKLPF a Ha))).
(* where the two written ranges and the call's ESTACK window lie *)
unfold decode_off_win in HOWK, HOWKL.
assert (NKW : forall a, kp <= a < kp + 60 -> ~ (sp1 - ESTACK <= a < sp1)).
{ destruct HOWK as [HOWK | HOWK]; intros a [Ha1 Ha2] [H1 H2]; lia. }
assert (NKLW : forall a, klp <= a < klp + 8 -> ~ (sp1 - ESTACK <= a < sp1)).
{ destruct HOWKL as [HOWKL | HOWKL]; intros a [Ha1 Ha2] [H1 H2]; lia. }
assert (NSVW : forall a, spZ regs - 96 <= a < spZ regs -> ~ (sp1 - ESTACK <= a < sp1))
  by (intros a [Ha1 Ha2] [H1 H2]; lia).
assert (NSVK : forall a, spZ regs - 96 <= a < spZ regs -> ~ (kp <= a < kp + 60)).
{ destruct HOWK as [HOWK | HOWK]; intros a [Ha1 Ha2] [H1 H2]; lia. }
assert (NSVKL : forall a, spZ regs - 96 <= a < spZ regs -> ~ (klp <= a < klp + 8)).
{ destruct HOWKL as [HOWKL | HOWKL]; intros a [Ha1 Ha2] [H1 H2]; lia. }
assert (HWlo : alloc_ceiling <= sp1 - ESTACK) by lia.
(* the destination's placement: a frame of the call's frames, so below the allocation ceiling *)
destruct HinF as (cidK & posK & HinK & HKlo & HKhi).
assert (HKbelow : forall a, kp <= a < kp + 60 -> 0 <= a < alloc_ceiling).
{ intros a Ha. apply (skp_frame_below lyc Sc W memc mdc cidK posK a LAWS HARc0 HinK).
  left. unfold in_zr, frame_rng. cbn [fst snd]. lia. }
(* the cut's read rights, opened *)
pose proof HRDKm as HRDKmD. destruct HRDKmD as (HRDKm1 & HRDKm2 & HRDKm3 & HRDKm4 & HRDKm5 & HRDKm6).
pose proof HRDKLm as HRDKLmD. destruct HRDKLmD as (HRDKLm1 & HRDKLm2 & HRDKLm3 & HRDKLm4 & HRDKLm5 & HRDKLm6).
pose proof HRDF as HRDFD. destruct HRDFD as (HRDF1 & HRDF2 & HRDF3 & HRDF4 & HRDF5 & HRDF6).
pose proof HRDKm4 as HAMRK. pose proof HRDKLm4 as HAMRKL.
unfold amem_range in HAMRK, HAMRKL.
assert (NKband : forall a, kp <= a < kp + 60 -> ~ (kLowMemEnd <= a < kHighShadowEnd)).
{ destruct HAMRK as [Hq | [Hq1 Hq2]]; intros a [Ha1 Ha2] [H1 H2]; lia. }
assert (NKLband : forall a, klp <= a < klp + 8 -> ~ (kLowMemEnd <= a < kHighShadowEnd)).
{ destruct HAMRKL as [Hq | [Hq1 Hq2]]; intros a [Ha1 Ha2] [H1 H2]; lia. }
assert (NWband : forall a, sp1 - ESTACK <= a < sp1 -> ~ (kLowMemEnd <= a < kHighShadowEnd))
  by (intros a [Ha1 Ha2] [H1 H2]; lia).
assert (NKbandC : forall s, kLowMemEnd <= s < kHighShadowEnd -> ~ (kp <= s < kp + 60))
  by (intros s Hs Hq; exact (NKband s Hq Hs)).
assert (NKLbandC : forall s, kLowMemEnd <= s < kHighShadowEnd -> ~ (klp <= s < klp + 8))
  by (intros s Hs Hq; exact (NKLband s Hq Hs)).
assert (NWbandC : forall s, kLowMemEnd <= s < kHighShadowEnd -> ~ (sp1 - ESTACK <= s < sp1))
  by (intros s Hs Hq; exact (NWband s Hq Hs)).
(* the model's f has 60 bytes *)
assert (HL60 : length f = 60%nat) by (rewrite HLF; reflexivity).
assert (LZF : length (TW.zs f) = 60%nat) by (unfold TW.zs; rewrite length_map; exact HL60).
assert (EFm : (match f with [] => K | _ => f end) = f /\
              (match f with [] => KL | _ => TW.put 8 (Z.of_nat (length f)) end) = TW.put 8 60).
{ destruct f as [|b0 f0]; [cbn in HL60; discriminate HL60|].
  split; [reflexivity | rewrite HL60; reflexivity]. }
destruct EFm as [EFm1 EFm2].
(* the out cells, as a list *)
assert (HOUTS : sendctl_outs kp klp = [(klp, 8)]).
{ unfold sendctl_outs. destruct (Z.eqb_spec kp 0) as [Hz|Hz]; [exfalso; exact (HKP0 Hz) | reflexivity]. }
assert (HNOUT : forall a, 0 <= a < 2 ^ 64 ->
  inGb (sendctl_outs kp klp) (bv_unsigned (Z_to_bv 64 a)) = false -> ~ (klp <= a < klp + 8)).
{ intros a Ha Hb [H1 H2].
  assert (Hin : inG (sendctl_outs kp klp) a).
  { rewrite HOUTS. unfold inG. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia. }
  rewrite (unsigned_lit_small a Ha) in Hb.
  exact (proj1 (inGb_false (sendctl_outs kp klp) a) Hb Hin). }
(* ---- run A: +0x1b4 .. +0x1c0 ---- *)
pose proof (skp_entry_a W2 regs2 mem2) as HS.
assert (HEI : img_env VAL A_LIM (skp_E regs2)) by apply skp_env_img.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (skp_E regs2) (mrestrict (w_H W2) mem2)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX
  0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS
  HGX 0 []) as RUNTO.
pose proof HJ1 as HJ.
paj_run_tok RUN HS HJ SHOK SKP_B0.
{ skp_awr_rs. apply awr_ok_x_nil. }
set (mdA := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody mdA. clear mat.
assert (KA0 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem2 a).
{ apply (can_aview_kept_frame (segs := segs) (skp_E regs2) (ss_mem ss_skpa) (w_H W2) mem2 (ms_mem ms) 0 HFr
    ltac:(lia)).
  intros x Hx (rg0 & Hin0 & _). exact Hin0. }
assert (GA0 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
(* the registers at the call *)
skp_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + SKP_C1)) T1 ltac:(apply codeptr_val; exact HEI).
skp_kreg HS regs2 (2%bv : bv 5) 2%nat R2 T2.
skp_kreg HS regs2 (3%bv : bv 5) 3%nat R3 T3b.
skp_kreg HS regs2 (4%bv : bv 5) 4%nat R4 T4b.
assert (T3 : YK11.getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite T3b; exact Hgp).
assert (T4 : YK11.getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite T4b; exact Htp).
skp_reg HS (10%bv : bv 5) (w64 kp) T10
  ltac:(cbn [sv_denot]; rewrite (skp_ew_reg regs2 22 22%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R22).
skp_reg HS (11%bv : bv 5) (w64 (F + 32)) T11
  ltac:(cbn [sv_denot]; rewrite (skp_ew_reg regs2 23 23%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R23).
skp_reg HS (12%bv : bv 5) (w64 60) T12
  ltac:(cbn [sv_denot]; rewrite (skp_ew_reg regs2 21 21%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R21).
skp_kreg HS regs2 (8%bv : bv 5) 8%nat R8 T8.
skp_kreg HS regs2 (9%bv : bv 5) 9%nat R9 T9.
skp_kreg HS regs2 (18%bv : bv 5) 18%nat R18 T18.
skp_kreg HS regs2 (19%bv : bv 5) 19%nat R19 T19.
skp_kreg HS regs2 (20%bv : bv 5) 20%nat R20 T20.
skp_kreg HS regs2 (21%bv : bv 5) 21%nat R21 T21.
skp_kreg HS regs2 (23%bv : bv 5) 23%nat R23 T23.
skp_kreg HS regs2 (24%bv : bv 5) 24%nat R24 T24.
skp_kreg HS regs2 (25%bv : bv 5) 25%nat R25 T25.
skp_kreg HS regs2 (26%bv : bv 5) 26%nat R26 T26.
skp_kreg HS regs2 (27%bv : bv 5) 27%nat R27 T27.
assert (ESPA : spZ (ms_regs ms) = sp1) by (unfold spZ; rewrite T2; apply unsigned_lit_small; lia).
(* the cut's read rights at the memory run A left *)
assert (RDKA : decode_rd_ok W2 (ms_mem ms) kp 60).
{ apply (trans_rd_ok_view W2 W2 mem2 (ms_mem ms) kp 60 HRDKm);
  [intros a Ha; apply KA0; lia | intros s Hs; apply KA0; lia]. }
assert (RDKLA : decode_rd_ok W2 (ms_mem ms) klp 8).
{ apply (trans_rd_ok_view W2 W2 mem2 (ms_mem ms) klp 8 HRDKLm);
  [intros a Ha; apply KA0; lia | intros s Hs; apply KA0; lia]. }
assert (RDFA : decode_rd_ok W2 (ms_mem ms) (F + 32) 60).
{ apply (trans_rd_ok_view W2 W2 mem2 (ms_mem ms) (F + 32) 60 HRDF);
  [intros a Ha; apply KA0; lia | intros s Hs; apply KA0; lia]. }
destruct RDKA as (RDKA1 & RDKA2 & RDKA3 & RDKA4 & RDKA5 & RDKA6).
destruct RDFA as (RDFA1 & RDFA2 & RDFA3 & RDFA4 & RDFA5 & RDFA6).
(* the destination's write right, at the walk's own journal *)
assert (HTWR : transport_twr_ok_g segs B TG.G_HARNESS STK sp0 FP ly S ly2 S2 ((SENDCTL_CID, pos) :: own) W2
                 (ms_mem ms) (spZ (ms_regs ms)) kp 60).
{ rewrite ESPA. eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ|].
  intros a Ha. left. split; [|exact (NKW a Ha)].
  exact (skp_awr_move STK sp0 FP ly S lyc Sc ly2 S2 own (SENDCTL_CID, pos) a Hperm ELF (HKPF a Ha)). }
(* the source and the destination are apart *)
assert (HDISJ : kp + 60 <= F + 32 \/ F + 32 + 60 <= kp).
{ destruct (Z_le_gt_dec (kp + 60) (F + 32)) as [h|h]; [left; lia|].
  destruct (Z_le_gt_dec (F + 92) kp) as [h2|h2]; [right; lia|].
  exfalso. apply (NKF (Z.max kp (F + 32)) ltac:(lia)). unfold dkg_nf. left.
  change (fs_frame_bytes SENDCTL_CID) with 256. lia. }
(* +0x1c0: __asan_memcpy (kp, f, 60) *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_memcpy)) mm rom) mdx) Q) end.
eapply SRr_bind.
{ apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transport_segs_low OCpy
    (transport_sigma TS___asan_memcpy) (AI fx) TG.G_HARNESS W2 (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0
    mem0 md0 ((SENDCTL_CID, pos) :: own) ly2 S2 mdA (k + e) kp (F + 32) 60 (sp1 - sp0)
    (Z_to_bv 64 (BASE + SKP_C1)) HGX G_HARNESS_rw HJ T10 T11 T12).
  - lia.
  - lia.
  - lia.
  - rewrite ESPA. lia.
  - rewrite Zminus_mod, Hsp1al16, Hsp0a. reflexivity.
  - lia.
  - lia.
  - exact T3.
  - exact T4.
  - exact T1.
  - apply (ret_ok_codeptr_v (PI := PI_transport)); [unfold SKP_C1, AF_send_control; lia | reflexivity].
  - exact HTWR.
  - exact RDKA4.
  - exact RDKA2.
  - intros _. exact RDKA3.
  - split; [lia|]. split; [lia|]. split.
    + intros a Ha. split; [exact (RDFA1 a Ha)|]. rewrite ESPA. intros [H1 H2]. lia.
    + split; [exact HDISJ|]. split; [exact RDFA4|]. split; [exact RDFA2 | intros _; exact RDFA3]. }
cbv beta. intros W3 c3 _ (HWe & rgB & memB & mdB & Hc3 & HJB & HPB & HB10 & HBcpy & HBfr & HBgr).
subst W3. subst c3.
(* what the copy kept *)
assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (kp <= a < kp + 60) -> ~ (sp1 - ESTACK <= a < sp1) ->
  aview segs (w_H W2) memB a = aview segs (w_H W2) (ms_mem ms) a).
{ intros a Ha H1 H2. apply HBfr; [exact Ha | intros [Q1 Q2]; apply H1; lia | intros [Q1 Q2]; apply H2; lia]. }
assert (GAB : forall a, apresent (w_H W2) (ms_mem ms) a -> apresent (w_H W2) memB a)
  by (intros a Ha; exact (HBgr a Ha)).
(* the registers at +0x1c4 *)
assert (RB2 : YK11.getr rgB 2 = w64 sp1)
  by (transitivity (YK11.getr (ms_regs ms) 2); [exact (HPB 2 ltac:(unfold acallee_saved; lia)) | exact T2]).
assert (RB3 : YK11.getr rgB 3 = YK11.getr regs 3)
  by (transitivity (YK11.getr (ms_regs ms) 3); [exact (HPB 3 ltac:(unfold acallee_saved; lia)) | exact T3b]).
assert (RB4 : YK11.getr rgB 4 = YK11.getr regs 4)
  by (transitivity (YK11.getr (ms_regs ms) 4); [exact (HPB 4 ltac:(unfold acallee_saved; lia)) | exact T4b]).
assert (RB8 : YK11.getr rgB 8 = w64 (spZ regs))
  by (transitivity (YK11.getr (ms_regs ms) 8); [exact (HPB 8 ltac:(unfold acallee_saved; lia)) | exact T8]).
assert (RB9 : YK11.getr rgB 9 = w64 sp1)
  by (transitivity (YK11.getr (ms_regs ms) 9); [exact (HPB 9 ltac:(unfold acallee_saved; lia)) | exact T9]).
assert (RB18 : YK11.getr rgB 18 = w64 F)
  by (transitivity (YK11.getr (ms_regs ms) 18); [exact (HPB 18 ltac:(unfold acallee_saved; lia)) | exact T18]).
assert (RB19 : YK11.getr rgB 19 = w64 SENDCTL_S)
  by (transitivity (YK11.getr (ms_regs ms) 19); [exact (HPB 19 ltac:(unfold acallee_saved; lia)) | exact T19]).
assert (RB20 : YK11.getr rgB 20 = w64 klp)
  by (transitivity (YK11.getr (ms_regs ms) 20); [exact (HPB 20 ltac:(unfold acallee_saved; lia)) | exact T20]).
assert (RB21 : YK11.getr rgB 21 = w64 60)
  by (transitivity (YK11.getr (ms_regs ms) 21); [exact (HPB 21 ltac:(unfold acallee_saved; lia)) | exact T21]).
assert (RB23 : YK11.getr rgB 23 = w64 (F + 32))
  by (transitivity (YK11.getr (ms_regs ms) 23); [exact (HPB 23 ltac:(unfold acallee_saved; lia)) | exact T23]).
assert (RB24 : YK11.getr rgB 24 = w64 (SHADOW_OFF + F / 8))
  by (transitivity (YK11.getr (ms_regs ms) 24); [exact (HPB 24 ltac:(unfold acallee_saved; lia)) | exact T24]).
assert (RB25 : YK11.getr rgB 25 = w64 F)
  by (transitivity (YK11.getr (ms_regs ms) 25); [exact (HPB 25 ltac:(unfold acallee_saved; lia)) | exact T25]).
assert (RB26 : YK11.getr rgB 26 = w64 SHADOW_OFF)
  by (transitivity (YK11.getr (ms_regs ms) 26); [exact (HPB 26 ltac:(unfold acallee_saved; lia)) | exact T26]).
assert (RB27 : YK11.getr rgB 27 = YK11.getr regs 27)
  by (transitivity (YK11.getr (ms_regs ms) 27); [exact (HPB 27 ltac:(unfold acallee_saved; lia)) | exact T27]).
(* the out cell is readable at the memory the copy left *)
assert (RDKLB : decode_rd_ok W2 memB klp 8).
{ apply (trans_rd_ok_view W2 W2 (ms_mem ms) memB klp 8 RDKLA).
  - intros a Ha. apply KB; [lia | intros [Q1 Q2]; destruct HSEP as [HQ|HQ]; lia | exact (NKLW a Ha)].
  - intros s Hs. apply KB; [lia | exact (NKbandC s Hs) | exact (NWbandC s Hs)]. }
pose proof RDKLB as RDKLBD. destruct RDKLBD as (RDKLB1 & RDKLB2 & RDKLB3 & RDKLB4 & RDKLB5 & RDKLB6).
(* ---- run B: +0x1c4 .. +0x1d4, to the send cut ---- *)
clear HS SHOK.
destruct (skp_entry_b W2 rgB memB klp RB20 RB26 ltac:(lia) RDKLB4
  ltac:(intros i Hi; apply GAB; apply GA0; apply HKLPp; lia) RDKLB2) as [HS SHOK].
assert (HEIb : img_env VAL A_LIM (skp_E rgB)) by apply skp_env_img.
assert (UB20 : bv_unsigned (ew (skp_E rgB) 20) = klp)
  by (rewrite (skp_ew_reg rgB 20 20%bv eq_refl), RB20; unfold w64; apply unsigned_lit_small; lia).
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + SKP_C1)) mm rom) mdx) Q) end.
paj_run_to_tok RUNTO HS HJB SHOK YC4b.Bspan SENDCTL_SEND.
{ skp_awr_rs.
  apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite UB20 in Ha.
  left. split; [|lia].
  exact (skp_awr_move STK sp0 FP ly S lyc Sc ly2 S2 own (SENDCTL_CID, pos) a Hperm ELF
          (HKLPF a ltac:(lia))). }
set (mdF := with_vm_backing (m_vm_lazy mdB) mat mdB) in *. clearbody mdF. clear mat.
assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (klp <= a < klp + 8) ->
  aview segs (w_H W2) (ms_mem ms0) a = aview segs (w_H W2) memB a).
{ apply (kept_of_frame (segs := segs) (skp_E rgB) (ss_mem ss_skpb) (w_H W2) memB (ms_mem ms0) _ HFr).
  intros b wlo whi x Hw Hx. unfold ss_skpb, windows in Hw.
  cbn [ss_mem map In YP09.r_base YP09.r_wlo YP09.r_whi skp_rg_kl] in Hw.
  destruct Hw as [Hw | []]; injection Hw as <- <- <-; cbn [base_val] in Hx; rewrite UB20 in Hx. lia. }
assert (GAC : forall a, apresent (w_H W2) memB a -> apresent (w_H W2) (ms_mem ms0) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
(* every byte outside the two written ranges and the ESTACK window is the cut's *)
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (kp <= a < kp + 60) -> ~ (klp <= a < klp + 8) ->
  ~ (sp1 - ESTACK <= a < sp1) -> aview segs (w_H W2) (ms_mem ms0) a = aview segs (w_H W2) mem2 a).
{ intros a Ha H1 H2 H3. rewrite (KC a Ha H2). rewrite (KB a Ha H1 H3). exact (KA0 a Ha). }
assert (GAall : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms0) a)
  by (intros a Ha; exact (GAC a (GAB a (GA0 a Ha)))).
(* the own frame's bytes are the cut's *)
assert (KFR : forall a, F <= a < F + 256 ->
  aview segs (w_H W2) (ms_mem ms0) a = aview segs (w_H W2) mem2 a).
{ intros a Ha. apply KA.
  - lia.
  - intros Hq. apply (NKF a Hq). unfold dkg_nf. left.
    change (fs_frame_bytes SENDCTL_CID) with 256. lia.
  - intros Hq. apply (NKLF a Hq). unfold dkg_nf. left.
    change (fs_frame_bytes SENDCTL_CID) with 256. lia.
  - intros [Q1 Q2]. lia. }
assert (KF : forall a, F + 32 <= a < F + 32 + 60 ->
  aview segs (w_H W2) (ms_mem ms0) a = aview segs (w_H W2) mem2 a)
  by (intros a Ha; apply KFR; lia).
assert (KSH : forall s, kLowMemEnd <= s < kHighShadowEnd ->
  aview segs (w_H W2) (ms_mem ms0) s = aview segs (w_H W2) mem2 s).
{ intros s Hs. apply KA; [lia | exact (NKbandC s Hs) | exact (NKLbandC s Hs) | exact (NWbandC s Hs)]. }
(* the copy's own equation, from the cut's memory to the memory the piece leaves *)
assert (KCPY : forall j, (j < 60)%nat ->
  aview segs (w_H W2) (ms_mem ms0) (kp + Z.of_nat j) = aview segs (w_H W2) mem2 (F + 32 + Z.of_nat j)).
{ intros j Hj.
  rewrite (KC (kp + Z.of_nat j) ltac:(pose proof (HKbelow kp ltac:(lia)); lia)
    ltac:(intros [Q1 Q2]; destruct HSEP as [HQ|HQ]; lia)).
  rewrite (HBcpy (Z.of_nat j) ltac:(lia)).
  apply KA0. lia. }
(* ---- the facts the send cut asks for ---- *)
(* the chunk the store left at klp *)
lazymatch type of HS with
| st_ok_pi _ _ _ ?ssE _ =>
    let rr := eval vm_compute in (nth_error (ss_mem ssE) 0) in
    lazymatch rr with
    | Some ?rg0 => pose proof (can_region_nth (segs := segs) _ _ _ 0 rg0 HS eq_refl) as HR0
    end
end.
cbn [ms_mem restrict] in HR0.
skp_kreg HS rgB (20%bv : bv 5) 20%nat RB20 Y20.
skp_kreg HS rgB (21%bv : bv 5) 21%nat RB21 Y21.
assert (D21 : sv_denot (skp_E rgB) (SOff 21 0) = Z_to_bv 64 60).
{ cbn [sv_denot]. rewrite (skp_ew_reg rgB 21 21%bv eq_refl), RB21.
  unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity. }
pose proof (can_field_of_region (segs := segs) (skp_E rgB) (mrestrict (w_H W2) (ms_mem ms0)) 20 klp
  _ 0 8 0 8 0 8%N (SOff 21 0) 60 HR0 UB20 ltac:(cbn [In]; auto) D21 ltac:(cbn; lia) ltac:(cbn; lia)) as VKL.
rewrite Z.add_0_r in VKL. cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in VKL.
assert (EZS : TW.zs (TW.put 8 60) = [60; 0; 0; 0; 0; 0; 0; 0]) by (vm_compute; reflexivity).
assert (GKL3 : garr8 segs (mrestrict (w_H W2) (ms_mem ms0)) klp (TW.zs (TW.put 8 60))).
{ rewrite EZS. intros j Hj. cbn [length] in Hj. split.
  - intros i Hi. assert (Ei : i = 0%nat) by lia. subst i.
    change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
    rewrite (VKL j ltac:(lia)).
    do 8 (destruct j as [|j];
          [ lazymatch goal with |- Some (Z_to_bv 8 ?x) = Some (Z_to_bv 8 ?y) =>
              replace y with x by (vm_compute; reflexivity) end; reflexivity |]).
    exfalso. lia.
  - do 8 (destruct j as [|j]; [cbn [nth]; lia|]). exfalso. lia. }
(* the 60 bytes at kp are f's *)
assert (GK3 : garr8 segs (mrestrict (w_H W2) (ms_mem ms0)) kp (TW.zs f)).
{ apply (skp_garr8_move (w_H W2) (ms_mem ms0) mem2 kp (F + 32) (TW.zs f)); [|exact HGF].
  intros j Hj. rewrite LZF in Hj. exact (KCPY j Hj). }
(* the frame's 60 bytes and their read rights *)
assert (GF3 : garr8 segs (mrestrict (w_H W2) (ms_mem ms0)) (F + 32) (TW.zs f)).
{ apply (skp_garr8_move (w_H W2) (ms_mem ms0) mem2 (F + 32) (F + 32) (TW.zs f)); [|exact HGF].
  intros j Hj. rewrite LZF in Hj. apply KF. lia. }
assert (RDF3 : decode_rd_ok W2 (ms_mem ms0) (F + 32) 60).
{ apply (trans_rd_ok_view W2 W2 mem2 (ms_mem ms0) (F + 32) 60 HRDF); [exact KF | exact KSH]. }
(* the twelve saved words and the frame's last word *)
assert (KSV : forall o : Z * Z, In o SENDCTL_SAVED ->
  rdword (aview segs (w_H W2) (ms_mem ms0)) (spZ regs - fst o) =
  rdword (aview segs (w_H W2) mem2) (spZ regs - fst o)).
{ intros o Ho.
  assert (Hfo : 8 <= fst o <= 96).
  { unfold SENDCTL_SAVED in Ho. cbn [In] in Ho.
    repeat (destruct Ho as [Ho | Ho]; [subst o; cbn [fst]; lia|]). destruct Ho. }
  apply rdword_ext. intros i Hi.
  apply KA; [lia | apply NSVK; lia | apply NSVKL; lia | apply NSVW; lia]. }
assert (HSV3 : Forall (fun o : Z * Z => rdword (aview segs (w_H W2) (ms_mem ms0)) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) SENDCTL_SAVED).
{ apply Forall_forall. intros o Ho. rewrite (KSV o Ho).
  exact (proj1 (Forall_forall _ _) Hsaved o Ho). }
assert (HFL3 : rdword (aview segs (w_H W2) (ms_mem ms0)) (F + 256 - 8) = Some FL).
{ rewrite <- HFLw. apply rdword_ext. intros i Hi. apply KFR. lia. }
(* the world relation and the read-only bytes *)
assert (TW3 : tw_at TMAP_A (aview segs (w_H W2) (ms_mem ms0)) Bw).
{ apply (tw_kept_GA (aview segs (w_H W2) mem2)); [exact HTW2|].
  intros b n i Hbn Hi.
  assert (HGb : inG TG.G_HARNESS (b + i))
    by (unfold inG; apply Exists_exists; exists (b, n); split;
        [exact Hbn | unfold in_zr; cbn [fst snd]; lia]).
  destruct (HGX _ HGb) as [HiG _].
  pose proof (transport_segs_low _ HiG) as Hl. unfold kLowMemEnd in Hl.
  apply KA; [lia | intros Hq; exact (HNGK (b + i) Hq HGb) | intros Hq; exact (HNGKL (b + i) Hq HGb)
            | intros [Q1 Q2]; lia]. }
assert (ROM3 : trans_rom_view_rd W2 (ms_mem ms0)).
{ intros a Ha. rewrite <- (HROM2 a Ha). apply KA.
  - pose proof (trans_ro_rd_bounds a Ha). lia.
  - intros Hq. exact (NKimg a Hq (trans_ro_img a Ha)).
  - intros Hq. exact (NKLimg a Hq (trans_ro_img a Ha)).
  - intros [Q1 Q2]. pose proof (trans_ro_rd_bounds a Ha). lia. }
(* what the call kept, at the memory with the out cells put back *)
assert (KG3 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2
  (gover (sendctl_outs kp klp) (ms_mem ms0) memc) (spZ regs - SENDCTL_STK) (spZ regs) (sendctl_wr kp klp)).
{ apply (dk_kept_step_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc W memc mdc W2
    (gover (sendctl_outs kp klp) mem2 memc) (gover (sendctl_outs kp klp) (ms_mem ms0) memc)
    (spZ regs - SENDCTL_STK) (spZ regs) (sendctl_wr kp klp)
    (fun a => (kp <= a < kp + 60) \/ (sp1 - ESTACK <= a < sp1)) HARc0 HK).
  - intros a Ha Hn. apply skp_gover_view. intros Hb.
    apply KA; [exact Ha | intros Hq; apply Hn; left; exact Hq | exact (HNOUT a Ha Hb)
              | intros Hq; apply Hn; right; exact Hq].
  - intros a Hp. exact (skp_gover_pres (sendctl_outs kp klp) (w_H W2) mem2 (ms_mem ms0) memc a (GAall a) Hp).
  - intros a [Hq | Hq] Hc; [pose proof (HKbelow a Hq); lia | lia].
  - intros b m i Hb Hi [Hq | Hq].
    + right; right. split; [exact HKP0 | left; unfold SENDCTL_F; lia].
    + exfalso. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HARc0 Hb) as (_ & Hb4096 & Hbce & _). lia.
  - intros a [Hq | Hq] Hi HnG Hno Hne.
    + exact (NKimg a Hq Hi).
    + pose proof (transport_segs_low a Hi) as Hl. unfold kLowMemEnd in Hl. lia.
  - intros cid0 pos0 a Hc Hr [Hq | Hq].
    + right; right. split; [exact HKP0 | left; unfold SENDCTL_F; lia].
    + exfalso. pose proof (skp_frame_below lyc Sc W memc mdc cid0 pos0 a LAWS HARc0 Hc Hr). lia. }
(* the registers at +0x1d8 *)
skp_kreg HS rgB (2%bv : bv 5) 2%nat RB2 Y2.
skp_kreg HS rgB (3%bv : bv 5) 3%nat RB3 Y3.
skp_kreg HS rgB (4%bv : bv 5) 4%nat RB4 Y4.
skp_kreg HS rgB (8%bv : bv 5) 8%nat RB8 Y8.
skp_kreg HS rgB (9%bv : bv 5) 9%nat RB9 Y9.
skp_kreg HS rgB (18%bv : bv 5) 18%nat RB18 Y18.
skp_kreg HS rgB (19%bv : bv 5) 19%nat RB19 Y19.
skp_kreg HS rgB (23%bv : bv 5) 23%nat RB23 Y23.
skp_kreg HS rgB (24%bv : bv 5) 24%nat RB24 Y24.
skp_kreg HS rgB (25%bv : bv 5) 25%nat RB25 Y25.
skp_kreg HS rgB (26%bv : bv 5) 26%nat RB26 Y26.
skp_kreg HS rgB (27%bv : bv 5) 27%nat RB27 Y27.
(* +0x1d8: the send cut *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + SENDCTL_SEND)) mm rom) mdx) Q) end.
apply (SEND HLAWS HCALL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs cmd ack kp klp r K KL f TF
  Bw Bw' pos sp1 F ly2 S2 W2 (ms_mem ms0) mdF e (ms_regs ms0) HFIXs).
- unfold sendctl_send_cur, sendctl_cur.
  refine (conj (conj HJB (conj He (conj Hfrs (conj Hperm (conj ELF (conj Hmo (conj KG3 (conj HSV3
    (conj HFL3 _)))))))))
    (conj TW3 (conj ROM3 (conj HLF (conj GF3 (conj RDF3 _)))))).
  + right. intros i Hi. apply GAall. apply HKLPp. exact Hi.
  + right. rewrite EFm1, EFm2. split; [exact GK3 | exact GKL3].
- unfold sendctl_regs_send, sendctl_regs_rel.
  exact (conj (conj Y2 (conj Y3 (conj Y4 (conj Y8 (conj Y9 (conj Y18 (conj Y21 (conj Y24 (conj Y25 Y27)))))))))
    (conj Y19 (conj Y23 Y26))).
Qed.

End keep.

Print Assumptions sendctl_keep.
