(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryHead), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACa2.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACez.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChf.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChz.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntryHead.v, with its module paths, module names and numbers changed; 580 of its 698 lines of code are new or changed and 479 lines of the source are left out. *)
(* pcap_source_next, the ENTRY phase of the walk on the ASAN-UBSAN image of libreac v1.9.0
   (fuzz_pcap.asan-ubsan, lib/B): the slots 0x815b8 .. the record loop's head NP_loop 0x8174c, and the
   closed reader's NP_h0 0x818c4 -> NP_x0 0x818cc. It proves `nx_start POST` (lib/B's
   PcapSourceNextDefs) from the two phases it reaches: `nx_from POST (nx_loop_at (fun _ _ => True))`
   and `nx_from POST nx_x0_inv` (the shape of H_entry in lib/B/Prog/PcapSourceNext.v).

   WHAT THE CODE DOES HERE (the pinned fuzz_pcap.asan-ubsan image (sha256 9e66f771f22a),
   symbols from its unstripped twin fuzz_pcap.asan-ubsan (sha256 c969d83cdd59), capstone 5; listing base
   0x80788, so a listing offset is address - 0x80788):
   - 0x815b8..0x815fc: the 256-byte machine frame (`addi sp,sp,-0x100`), the probe store at sp0-256,
     ra and s0..s11 saved at sp0-8 .. sp0-104, s0 := sp0, `andi sp,sp,-0x20` and s1 := sp1 (atom 60);
   - 0x81600..0x81624: s2 := ts, s7 := cap, buf into 0x60(s1), the two GOT words (object 1 -> object
     15 the shadow-base cell, object 0 -> object 16 the use-after-return cell), a2 := the 32-bit
     use-after-return flag, a5 := the shadow base 0x7fff8000, s5 := ps;
   - 0x81628 `beqz a2`: the flag cell is 1 in every state the ASan model allows (AR_const_law through
     al_const, YG0d.v), so the run decides the branch not taken: 0x81640 is never reached;
   - 0x8162c..0x81634: `__asan_stack_malloc_0(0x40)`, the shadow base kept in s3 across it. The call is
     YC85.aj_stack_malloc_atS (lib/B/Prog/YC85.v): from astack_malloc_realizes 0, the model's
     stack_malloc_progressP and this call's premise `count_cid NX_CID (frames Sc) < fs_frames NX_CID`,
     the path `apath (stack_malloc 0 S) [] (PFake 0 pos, S')` exists, so a0 = frame_addr lyc 0 pos;
   - 0x81638..0x81648: a5 := s3, s3 := a0 = F, `bnez a0`: F is a frame address, 4096 <= F
     (frames_bounds; atom 516's fact HPTR), so the run decides it taken: the machine-stack arm
     0x8164c..0x81664, which would put the record header on the machine stack, is not reached;
   - 0x81668..0x816c0: 0x90(s1) := F, the frame's header (magic 0x41b58ab3, object 13, object 14)
     and its 8 shadow bytes f1 f1 f1 f1 f8 f8 f3 f3 through s9 = (F >> 3) + 0x7fff8000 (atom 529);
   - 0x816c4, 0x816cc: the two UBSan guards on ps (null, `ps & 7`) to the trap 0x81b64: decided
     not taken by the run from ps's facts (4096 <= ps, ps 8-aligned, atom 10);
   - 0x816d0..0x816e0: 0x68(s1) := F, the shadow check of ps (`lbu a0,0(s10)`, `bnez` to the report
     0x81c00): decided not taken, ps's first shadow byte is 0 (nxb_shadow0, a region of the state);
   - 0x816e4..0x816e8: `ld a0,0(s5)` = ps->f, `beqz a0`: the walk splits on h;
     h = 0: 0x818c4 a1 := -1, a6 := 0x68(s1) = F, then NP_x0 (nx_x0_inv, landed by nx_land0_by);
     h <> 0: the spills 0x816ec..0x81748, then NP_loop (nx_loop_inv at q = p, lh = None, landed by
     nx_land_by; the caller's struct, its shadow, the stream, the buffer and ts are kept by the walk's
     own journal, acall_kept_of_journal).
   The walk runs on a journal that starts at this call (ajournal_sub_init, window NX_STK_B below sp,
   footprint []); each cut extends the caller's journal with it (ajournal_sub), which puts the frame
   (NX_CID, fp) at the head of the caller's own frames, as nx_from asks. *)
(* Modified by Theorem Labs, 2026-10: nxb_vm_frame / nxb_asource_at_frame / nxb_ra_frame (a renamed copy of
   lib/B/Prog/PcapSourceClose.v's vm_frame / asource_at_frame / ra_frame) deleted; their uses name
   lib/A/Prog/PcapSourceCloseSpec.v's vm_frame_segs / asource_at_frame_segs / ra_frame. *)
From OSSVerify.libreac.fuzz_pcap Require Symbols.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YN3v YI04 YI09 YI08 YI00 YI0s YI16 YG0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 PcapImgEnd YE00 YG0p YC5d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSyms PcapList PcapPa PcapPaLib.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapBase YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import YC1g YC1h YC85 PcapFrame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PFreadISpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextKit.
(* LAST: lib/B's phase layer (it exports lib/A's Defs for the shared statement; lib/B's names shadow lib/A's). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextDefs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextSeat.
(* The image-free frame lemmas, Required without Import and used qualified. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapSourceCloseSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* The run cuts inside this phase, as listing offsets (address - 0x80788). *)
Definition NE_mvs1 : Z := Eval compute in ((Symbols.AsanUbsan.s_pcap_source_next + 0x44) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.      (* 0x815fc, `mv s1,sp`: the realigned sp becomes an atom first *)

(* ---- the atoms and the regions of the entry state ---- *)
(* Atoms 0..31 are the entry registers; 32 the shadow base, 33 the FILE pointer ps->f, 34 the
   shadow byte of ps. *)
Definition nxb_saves_region : YP09.region := YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 [].
Definition nxb_probe_region : YP09.region := YP09.mkRegion (Some 2%nat) (-256) (-248) (-256) (-248) [].
Definition nxb_ps_region : YP09.region :=
  YP09.mkRegion (Some 10%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))].
Definition nxb_pssh_region : YP09.region :=
  YP09.mkRegion (Some 34%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].

Definition nxb_regions0 : smem :=
  [ nxb_saves_region; nxb_probe_region; got_regionP; bcell_regionP 32;
    uar_got_regionP (A_OBJ 16); uar_cell_regionP (A_OBJ 16); nxb_ps_region; nxb_pssh_region ].

Definition nxb_atoms0 : list (nat * afact) :=
  [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 (2 ^ 47) 3); (32%nat, mkAF SB SB 0) ].
Definition nxb_alias0 : list (sv * sv) :=
  [ (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 32 0), SOff 34 0) ].
Definition nxb_facts0 : facts := mkFacts nxb_atoms0 [] nxb_alias0.
Definition ss_nxb0 : sstate := mkSS NP_entry sr_atoms nxb_regions0 None nxb_facts0.

Definition nxb_extra (h ps : Z) : list word :=
  [Z_to_bv 64 SB; Z_to_bv 64 h; Z_to_bv 64 (SB + ps / 8)].

(* The low atoms of two environments that both hold the entry registers agree. *)
Lemma nxb_env_low : forall (E E0 : env) (regs : bvmap 5 word),
  (forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) ->
  (forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = getr regs r) ->
  forall n, (n < 32)%nat -> ew E n = ew E0 n.
Proof.
intros E E0 regs H1 H2 n Hn.
assert (Hr : Z.of_nat n = bv_unsigned (Z_to_bv 5 (Z.of_nat n))).
{ rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small; lia. }
rewrite (H1 n _ Hr), (H2 n _ Hr). reflexivity.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg pcap_listing}.
#[local] Abbreviation SEGS := (pa_segs).
#[local] Abbreviation VAL := (pa_val).
#[local] Abbreviation SIGMA := (pa_sigma).
#[local] Abbreviation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* One byte, read back from the shadow. *)
Lemma nxb_val_mem1 : forall (H : word -> bool) (m : word -> option byte) a v,
  aview SEGS H m a = Some v -> 0 <= v < 256 -> val_mem SEGS (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv Hr k Hk. replace k with 0%nat by lia. cbn [Z.of_nat]. rewrite Z.add_0_r.
unfold aview in Hv. destruct (mbyte SEGS (mrestrict H m) a) as [b|] eqn:Hb; [|discriminate Hv].
cbn [option_map] in Hv. injection Hv as <-. f_equal.
rewrite (le_byte_small (bv_unsigned b) 1 0) by (cbn [Z.of_nat]; lia).
rewrite Z.mul_0_r, Z.shiftr_0_r. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* The first shadow byte of a range that is addressable and starts 8-aligned is 0. *)
Lemma nxb_shadow0 : forall (rd : Z -> option Z) p n,
  p mod 8 = 0 -> 8 <= n -> range_addressable rd SHADOW_OFF p n -> rd (SHADOW_OFF + p / 8) = Some 0.
Proof.
intros rd p n Hp Hn HR. destruct (HR (p + 7) ltac:(lia)) as (s & Hs & Hok).
assert (E : shadow_of_addr SHADOW_OFF (p + 7) = SHADOW_OFF + p / 8).
{ unfold shadow_of_addr. f_equal. symmetry. apply (Z.div_unique (p + 7) 8 (p / 8) 7); [left; lia|].
  pose proof (Z.div_mod p 8 ltac:(lia)) as D. rewrite Hp, Z.add_0_r in D. lia. }
rewrite E in Hs. unfold saddr_ok in Hok.
assert (Hm : (p + 7) mod 8 = 7).
{ rewrite <- Zplus_mod_idemp_l, Hp. reflexivity. }
rewrite Hm in Hok. destruct Hok as [-> | [H1 H2]]; [exact Hs | lia].
Qed.

(* The caller's struct, read through bytes that did not change. *)
Lemma nxb_ps_at_frame : forall (m m' : word -> option byte) ps h sw lol lvt lvid pad,
  (forall x, ps <= x < ps + PS_LEN -> mbyte SEGS m' x = mbyte SEGS m x) ->
  nx_ps_at SEGS m ps h sw lol lvt lvid pad -> nx_ps_at SEGS m' ps h sw lol lvt lvid pad.
Proof.
intros m m' ps h sw lol lvt lvid pad Hfr (V1 & V2 & V3 & V4 & V5 & G & Hl). unfold nx_ps_at.
unfold PS_LEN, PS_F_OFF, PS_SW_OFF, PS_OL_OFF, PS_VT_OFF, PS_VID_OFF in *.
split; [eapply PcapSourceCloseSpec.vm_frame_segs; [|exact V1]; intros x Hx; apply Hfr; lia|].
split; [eapply PcapSourceCloseSpec.vm_frame_segs; [|exact V2]; intros x Hx; apply Hfr; lia|].
split; [eapply PcapSourceCloseSpec.vm_frame_segs; [|exact V3]; intros x Hx; apply Hfr; lia|].
split; [eapply PcapSourceCloseSpec.vm_frame_segs; [|exact V4]; intros x Hx; apply Hfr; lia|].
split; [eapply PcapSourceCloseSpec.vm_frame_segs; [|exact V5]; intros x Hx; apply Hfr; lia|].
split; [|exact Hl].
apply (garr8_frame SEGS m m' _ _ G). intros x Hx. rewrite Hl in Hx. apply Hfr. lia.
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.

Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTL : ameter_laws MT.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis ASM0 : astack_malloc_realizes SEGS B 0.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis ASIL : @asource_img_laws SK SEGS B KS.

Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (PI := PI).
Let RUNC := SRr_run_pi_AJ_call B LAWS.

(* ---- the symbolic state at the first slot ---- *)

Lemma nxb_entry_st : forall (W : world SEGS) lyc Sc (memc : word -> option byte) mdc
  (regs : bvmap 5 word) (ps h : Z),
  AR SEGS B lyc Sc W memc mdc ->
  (forall a, spZ regs - NX_STK_B <= a < spZ regs -> apresent (w_H W) memc a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  getr regs 10 = w64 ps ->
  alloc_ceiling + NX_STK_B <= spZ regs ->
  ps mod 8 = 0 -> 4096 <= ps -> ps + 24 <= 2 ^ 47 -> off_img ps 24 -> in_app ps 24 ->
  val_mem SEGS (rdW W memc) ps 8 h -> 0 <= h < 2 ^ 64 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF ps 24 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (nxb_extra h ps))) ss_nxb0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + NP_entry)) memc (seg_rom SEGS))).
Proof.
intros W lyc Sc memc mdc regs ps h HAR Hpres Hsp Hal16 H10 Hspc Hps8 Hps0 Hpshi Hpsimg Hpsapp Hfv Hh Hsh.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (HNS : NX_STK_B = 8464) by reflexivity.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite (palf_got_uar B TL) in Kguar. rewrite (pal_uar_cell B TL) in Kguar, Kuar.
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1.
pose proof (pa_obj_img 15 ltac:(lia)) as Hob15. pose proof (pa_obj_img 16 ltac:(lia)) as Hob16.
pose proof (palf_sep B TLF) as Hsep. rewrite (pal_uar_cell B TL) in Hsep.
cbn [zseps zseps_from fst snd] in Hsep.
unfold pcap_img_end, YImgTop.IMG_TOP in Hob0, Hob1, Hob15, Hob16.
unfold off_img, pcap_img_end, YImgTop.IMG_TOP, YImgTop.IMG_LO in Hpsimg.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (nxb_extra h ps))).
assert (E2 : ew E 2 = getr regs 2)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 ps)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
      rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 h)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (SB + ps / 8))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (EO : forall i, (i < 17)%nat -> ew E (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)))
  by (intros i Hi; subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros nn v Hn' Hv. cbn [base_val]. rewrite Hn'. apply unsigned_lit_small. exact Hv. }
assert (Hps64 : 0 <= ps < 2 ^ 64) by lia.
assert (Hsb64 : 0 <= SB + ps / 8 < 2 ^ 64)
  by (unfold SB; pose proof (Z.div_pos ps 8 ltac:(lia) ltac:(lia));
      pose proof (Z.div_lt_upper_bound ps 8 (2 ^ 47) ltac:(lia) ltac:(lia)); lia).
assert (Hps_shadow : aview SEGS (w_H W) memc (SHADOW_OFF + ps / 8) = Some 0)
  by (apply (nxb_shadow0 _ ps 24); [exact Hps8 | lia | exact Hsh]).
unfold ss_nxb0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold nxb_regions0, nxb_saves_region, nxb_probe_region, got_regionP, bcell_regionP,
         uar_got_regionP, uar_cell_regionP, nxb_ps_region, nxb_pssh_region.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. fold E. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + cbn [base_val]. fold E. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + fold E. rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) (EO 1%nat ltac:(lia)))
      by (pose proof (pa_val_range (A_OBJ 1)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 15) 0) (VAL (A_OBJ 15)));
    [cbn [sv_denot]; rewrite (EO 15%nat ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | pose proof (pa_val_range (A_OBJ 15)); cbv [A_OBJ Nat.add] in *; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
  + fold E. rewrite (VB (A_OBJ 15) (VAL (A_OBJ 15)) (EO 15%nat ltac:(lia)))
      by (pose proof (pa_val_range (A_OBJ 15)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 15)) 0 8 (SOff 32 0) SB);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | unfold SB; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
  + fold E. rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) (EO 0%nat ltac:(lia)))
      by (pose proof (pa_val_range (A_OBJ 0)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 16) 0) (VAL (A_OBJ 16)));
    [cbn [sv_denot]; rewrite (EO 16%nat ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | pose proof (pa_val_range (A_OBJ 16)); cbv [A_OBJ Nat.add] in *; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kguar).
  + fold E. rewrite (VB (A_OBJ 16) (VAL (A_OBJ 16)) (EO 16%nat ltac:(lia)))
      by (pose proof (pa_val_range (A_OBJ 16)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 16)) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) memc _ _ Kuar).
  + fold E. rewrite (VB 10%nat ps E10) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ ps 0 8 (SOff 33 0) h);
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact Hfv.
  + fold E. rewrite (VB 34%nat (SB + ps / 8) E34) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (SB + ps / 8) 0 1 (SLit 0) 0); [reflexivity | zside | zside |].
    rewrite Z.add_0_r. apply (nxb_val_mem1 (w_H W) memc); [|lia].
    rewrite SB_SHADOW_OFF. exact Hps_shadow.
- apply pairwise_disjoint_of_extents.
  unfold nxb_regions0, nxb_saves_region, nxb_probe_region, got_regionP, bcell_regionP,
         uar_got_regionP, uar_cell_regionP, nxb_ps_region, nxb_pssh_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. fold E.
  rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) (EO 1%nat ltac:(lia))) by (pose proof (pa_val_range (A_OBJ 1)); lia).
  rewrite (VB (A_OBJ 15) (VAL (A_OBJ 15)) (EO 15%nat ltac:(lia))) by (pose proof (pa_val_range (A_OBJ 15)); lia).
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) (EO 0%nat ltac:(lia))) by (pose proof (pa_val_range (A_OBJ 0)); lia).
  rewrite (VB (A_OBJ 16) (VAL (A_OBJ 16)) (EO 16%nat ltac:(lia))) by (pose proof (pa_val_range (A_OBJ 16)); lia).
  rewrite (VB 10%nat ps E10) by lia.
  rewrite (VB 34%nat (SB + ps / 8) E34) by lia.
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  pose proof (Z.div_pos ps 8 ltac:(lia) ltac:(lia)) as Hd0.
  pose proof (Z.div_lt_upper_bound ps 8 (2 ^ 44) ltac:(lia) ltac:(lia)) as Hd1.
  pose proof (Z.div_mod ps 8 ltac:(lia)) as Hd2. pose proof (Z.mod_pos_bound ps 8 ltac:(lia)) as Hd3.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpsapp. rewrite HNS in Hspc.
  revert Hsep Hob0 Hob1 Hob15 Hob16 Hpsimg Hpsapp Hps0 Hpshi Hsp Hspc Hd0 Hd1 Hd2 Hd3 C1.
  unfold SB. clear. intros.
  repeat split; lia.
- split; [|split; [exact I | ]].
  + cbn [f_atoms atoms_ok nxb_facts0 nxb_atoms0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    fold E. rewrite Usp, E10, E32. rewrite !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
    repeat split; try exact I; unfold SB; lia.
  + cbn [f_alias nxb_facts0 nxb_alias0 alias_ok]. split; [|exact I].
    exact (shadow_decl_ok E 10 32 34 ps SB E10 Hps64 E32 E34).
Qed.

(* A byte of [F, F + Fb) has its shadow byte in the frame's shadow [F/8, F/8 + Fb/8) (F, Fb 8-aligned). *)
Lemma nxb_shadow_in : forall F Fb p, F mod 8 = 0 -> Fb mod 8 = 0 -> F <= p -> p < F + Fb ->
  SHADOW_OFF + F / 8 <= SHADOW_OFF + p / 8 /\ SHADOW_OFF + p / 8 + 1 <= SHADOW_OFF + F / 8 + Fb / 8.
Proof.
intros F Fb p H1 H2 H3 H4.
pose proof (Z.div_mod F 8 ltac:(lia)) as D1. pose proof (Z.div_mod Fb 8 ltac:(lia)) as D2.
pose proof (Z.div_mod p 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as M3.
rewrite H1 in D1. rewrite H2 in D2. lia.
Qed.

(* nx_kept is acall_kept with the one extra premise `~ E a` in the top clause. *)
Lemma nxb_kept_of_acall : forall lyc Sc (W : world SEGS) memc W2 mem2 sp E,
  acall_kept SEGS B lyc Sc W memc W2 mem2 (sp - NX_STK_B) sp E ->
  nx_kept SEGS NX_STK_B B lyc Sc W memc W2 mem2 sp E.
Proof.
intros lyc Sc W memc W2 mem2 sp E (K1 & K2 & K3 & K4 & K5 & K6).
split; [intros a Ha Hw _; exact (K1 a Ha Hw)|].
split; [exact K2|]. split; [exact K3|]. split; [exact K4|].
split; [intros a Ha Hw Hp; exact (K5 a Ha Hw Hp) | exact K6].
Qed.

Lemma nxb_mod64_8 : forall x, x mod 64 = 0 -> x mod 8 = 0.
Proof.
intros x H. pose proof (Z.div_mod x 64 ltac:(lia)) as D. rewrite H, Z.add_0_r in D. rewrite D.
replace (64 * (x / 64)) with ((8 * (x / 64)) * 8) by lia. apply Z_mod_mult.
Qed.

(* ---- the entry phase ---- *)

Theorem nx_entryX : forall POST,
  nx_from SK B KS POST (nx_loop_at B MT KS (fun _ _ => True)) ->
  nx_from SK B KS POST (nx_x0_inv B MT KS) ->
  nx_start SK B KS POST.
Proof.
intros POST HLOOP HX0 cx HB. unfold nx_from in HLOOP, HX0.
pose proof HB as (HJ & HROD & Hraw & Hra4 & Hgp & Htp & H10 & H11 & H12 & H13 & Hal16 & Hwlo & Hwhi
  & Hchn & Hroom & Hfv & Hh64 & Hps8 & Hps0 & Hpshi & Hamr & Hown & Hfa1 & Hfa2 & Hsh
  & Hpsat & Hswz & Hrng & Hwrps & Hbufb & Htsb & Hstream & Hmeta & HEE & HEsp).
(* the open reader's premises are implications over arithmetic: boxed, so that lia does not split on them *)
box Hpsat. box Hswz. box Hrng. box Hwrps. box Hbufb. box Htsb. box Hstream. box Hmeta.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (pa_base_lo (PL := PL_pcap) (PI := PI)) as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk0 & F1 & F2 & F3 & F4 & Hgone
  & Hpres & Hstk & F5 & HQT).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (HNS : NX_STK_B = 8464) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
unfold PS_F_OFF, PS_LEN in *. rewrite Z.add_0_r in Hfv.
(* ps lies in a frame of the caller's journal: so it is outside the image. *)
assert (Hin : In (n_cid cx, n_pos cx) (frames (n_Sc cx)))
  by (rewrite Hfrs; apply in_or_app; left; exact Hown).
pose proof (frm_off_imgP B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx)
  (n_cid cx) (n_pos cx) HAR Hin) as Hfimg.
destruct (frames_bounds SEGS B LAWS (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx)
  (n_cid cx) (n_pos cx) HAR Hin) as (Hf4096 & Hfceil & Hfapp).
assert (Hpsimg : off_img (n_ps cx) 24) by (unfold off_img in *; lia).
assert (Hsplo : 2 ^ 46 <= spZ (n_regs cx)) by (unfold alloc_ceiling in *; lia).
assert (Hsphi : spZ (n_regs cx) <= 2 ^ 47) by lia.
assert (Hpresw : forall a, spZ (n_regs cx) - NX_STK_B <= a < spZ (n_regs cx) ->
                   apresent (w_H (n_W cx)) (n_memc cx) a)
  by (intros a Ha; apply Hpres; lia).
assert (Hspc : alloc_ceiling + NX_STK_B <= spZ (n_regs cx)) by lia.
assert (Hpsapp : in_app (n_ps cx) 24)
  by (apply (in_app_sub _ _ _ _ Hfapp); lia).
pose proof (nxb_entry_st (n_W cx) (n_lyc cx) (n_Sc cx) (n_memc cx) (n_mdc cx) (n_regs cx)
  (n_ps cx) (n_h cx) HAR Hpresw (conj Hsplo Hsphi) Hal16 H10 Hspc Hps8 Hps0 Hpshi Hpsimg Hpsapp Hfv Hh64 Hsh) as HS.
(* the inner journal: from the call's entry memory, with this call's own stack window *)
pose proof (ajournal_sub_init SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx)
  (n_mem0 cx) (n_md0 cx) (n_own cx) (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) (n_k cx)
  NX_STK_B (spZ (n_regs cx)) [] (spZ (n_regs cx) - n_sp0 cx) HJ ltac:(lia)
  ltac:(rewrite <- Zminus_mod_idemp_l, Hal16, <- Zminus_mod_idemp_r, Hsp0al; reflexivity)
  ltac:(lia) ltac:(lia) ltac:(lia)) as HJ0.
remember (Eimg (Ereg (n_regs cx) (nxb_extra (n_h cx) (n_ps cx)))) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (n_regs cx) (nxb_extra (n_h cx) (n_ps cx))) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr (n_regs cx) 2)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 (n_ps cx))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat _ _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (n_h cx))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (SB + n_ps cx / 8))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 2)).
assert (EEa : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (n_regs cx) r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAE : env_agree 32 (Ereg (n_regs cx) (nxb_extra (n_h cx) (n_ps cx))) E)
  by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ (n_regs cx)) by (rewrite E2; reflexivity).
clear HEdef EL.
img_factsF E. img_hull_factsF.
unfold pcap_img_end, YImgTop.IMG_TOP in Hob241, Hob242, Hob256, Hob257.
pose proof (Z.div_pos (n_ps cx) 8 ltac:(lia) ltac:(lia)) as Hq0.
pose proof (Z.div_lt_upper_bound (n_ps cx) 8 (2 ^ 44) ltac:(lia) ltac:(lia)) as Hq1.
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
assert (EFA0 : forall c p, frame_addr (n_lyc cx) c p = frame_addr (n_lyc cx) c p) by reflexivity.
unfold nx_start. change (w64 (BASE + NP_entry)) with (Z_to_bv 64 (BASE + NP_entry)).
(* 0x815b8 .. 0x815f8: the frame, the probe, the 13 saves and the realignment. *)
hei_havoc HS; paj_run_to_sh RUNTOP HS HJ0 NE_mvs1. { awrFL AG 0 0 EFA0. }
upd_aboveW_init HFr AG HUP. clear_frames. cbn [ms_mem mkst] in HUP.
(* the realigned stack pointer sp1 becomes atom 60, in sp; the probe word is dropped and the slots
   [sp1, sp1 + 152) become one region (the highest slot is NS_F1 = 0x90). *)
set (sp1 := 32 * ((spZ (n_regs cx) + -256) / 32)).
destruct (sp1_facts (spZ (n_regs cx) + -256) ltac:(lia)
  ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ (n_regs cx) - 272 <= sp1 <= spZ (n_regs cx) - 256) by lia. clear Hsp1r.
assert (Esp1 : n_sp1 cx = sp1) by reflexivity.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  rreg_by HS (2%bv : bv 5) (Z_to_bv 64 sp1)
    (denot_and_m32 Ev 2 (spZ (n_regs cx)) (-256) ltac:(rewrite E2; symmetry; apply Z_to_bv_bv_unsigned)
       ltac:(lia) ltac:(lia) ltac:(lia)) R2 end.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_pi_havoc_hi 60 Ev ssv msv [Z_to_bv 64 sp1] HS ltac:(vm_compute; reflexivity)) as HS3;
  hei_pose Ev 60%nat [Z_to_bv 64 sp1] end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  assert (E60 : ew Ev 60 = Z_to_bv 64 sp1)
    by (rewrite HEv; exact (ew_havoc_new _ 60 [Z_to_bv 64 sp1] 0 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (2%bv : bv 5) (SOff 60 0) HS ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E60, Z.add_0_r, R2;
          rewrite unsigned_lit_small by lia; reflexivity)) as HS3;
  clear HS; rename HS3 into HS end.
norm_ss HS. clear R2.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_pi_add_fact Ev ssx msx 60%nat (mkAF (2 ^ 46 - 512) (2 ^ 47) 5) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E60, unsigned_lit_small by lia;
          change (2 ^ 5) with 32; lia)) as HS3;
  clear HS; rename HS3 into HS end.
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let rs' := eval vm_compute in (filter (fun r => negb (Z.eqb (YP09.r_lo r) (-256))) rs) in
  pose proof (st_ok_pi_submem Ex ssx (restrict (w_H (n_W cx)) msX) rs' HS
    ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
  clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msX) =>
  assert (HR60 : region_ok SEGS Ev (ms_mem (restrict (w_H (n_W cx)) msX)) (YP09.mkRegion (Some 60%nat) 0 152 0 152 []));
  [ unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
    rewrite E60, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
    intros o Ho; apply (apresent_writable SEGS); apply HJpres; rewrite HNS; lia
  | ];
  assert (HD60 : all_disjoint Ev (YP09.mkRegion (Some 60%nat) 0 152 0 152 []) (ss_mem ssx));
  [ let rs2 := eval vm_compute in (ss_mem ssx) in change (all_disjoint Ev (YP09.mkRegion (Some 60%nat) 0 152 0 152 []) rs2);
    cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    evalE AG; unfold SB;
    pose proof Hpsapp as Hpa; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpa;
    revert Hq0 Hq1 Hsp1 Hsplo Hsphi Hps0 Hpshi Hob241 Hob242 Hob256 Hob257 Hpa Hspc C1 HNS;
    clear; intros;
    repeat split; lia
  | ];
  pose proof (st_ok_pi_add_region Ev ssx (restrict (w_H (n_W cx)) msX) (YP09.mkRegion (Some 60%nat) 0 152 0 152 []) HS eq_refl HR60 HD60) as HS3;
  clear HJpres HR60 HD60; clear HS; rename HS3 into HS end.
norm_ss HS.
(* 0x815fc .. 0x81634: buf into 0x60(s1), the GOT words, the flag (1: beqz not taken), the shadow
   base, and the call of __asan_stack_malloc_0(0x40). *)
hei_havoc HS; paj_run_shc RUNP RUNC HS HJ0. { awrFL AG 0 0 EFA0. }
upd_aboveW HUP HFr AG. clear HF HFr HG.
aconstsF HJ0 Kgot0 Kcell0 Kguar0 Kuar0.
prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (1%bv : bv 5) R1.
pmkst HS.
rewrite (palf_sm0 B TLF).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
  eapply (aj_stack_malloc_atS SEGS B LAWS Hsegs errno_low ML SMP 0 ASM0 ltac:(lia) (n_W cx) (ms_regs msX)
    (ms_mem msX) NX_STK_B (spZ (n_regs cx)) [] (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) []
    (n_lyc cx) (n_Sc cx) _ 0 (sp1 - spZ (n_regs cx)) _ HJ0) end.
  - unfold spZ at 1. rewrite R2. evalE AG.
  - rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity.
  - lia.
  - rewrite HNS, Hes; lia.
  - rewrite R3. evalE AG. rewrite (EEa 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite R4. evalE AG. rewrite (EEa 4%nat 4%bv eq_refl). exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [lazymatch goal with |- _ <= ?k < _ => try unfold k end; lia | reflexivity].
  - exact Hroom. }
cbv beta. clear R2 R3 R4 R1.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2
  & Hbb2 & Hz & Hflag & HK & HJc & (fS2 & ES2)).
rewrite Hes in HK.
replace (spZ (n_regs cx) + (sp1 - spZ (n_regs cx)) - 4096) with (sp1 - 4096) in HK by lia.
replace (spZ (n_regs cx) + (sp1 - spZ (n_regs cx))) with sp1 in HK, HJc by lia.
assert (HUP2 : forall a, spZ (n_regs cx) <= a < 2 ^ 64 ->
          aview SEGS (w_H (n_W cx)) mem2 a = aview SEGS (w_H (n_W cx)) (n_memc cx) a).
{ intros a Ha. rewrite <- (HUP a Ha). pose proof HK as (K1 & _). apply K1; lia. }
clear HUP. rename HUP2 into HUP.
aconstsF HJ2 Kgot2 Kcell2 Kguar2 Kuar2.
pose proof (proj1 HJ2) as HAR2.
assert (Hfin2 : In (0, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR2 Hfin2) as (HFal & [HFhi _] & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFhigh).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFhigh_img.
pose proof (frame_al64 SEGS B _ _ _ _ _ 0 fpos HAR2 Hfin2) as (HFa64 & _ & _).
pose proof (frame_al64 SEGS B _ _ _ _ _ _ _ HAR Hin) as (Hca64 & Hcb64 & Hcb).
destruct (in_split _ _ Hin) as (l1 & l2 & Hl12).
pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (0, fpos) (n_cid cx, n_pos cx) [] l1 l2 HAR2
  ltac:(rewrite Hfrs2, Hl12; reflexivity)) as HdFP.
unfold zdisjoint, frame_rng in HdFP. cbn [fst snd] in HdFP.
change (fs_frame_bytes 0) with 64 in *.
set (F := frame_addr (n_lyc cx) 0 fpos) in *. set (FL := flag_addr (n_lyc cx) 0 fpos) in *.
(* the call kept the caller's struct shadow byte: it is in the shadow of the caller's frame (cid, pos) *)
pose proof (nxb_mod64_8 _ Hca64) as Hc8. pose proof (nxb_mod64_8 _ Hcb64) as Hcb8.
pose proof (nxb_shadow_in _ _ _ Hc8 Hcb8 Hfa1 ltac:(lia)) as Hpssh.
reseat HS HJ2 HP2 [0; 1; 2; 3; 4; 5; 6; 7]%nat AG
ltac:(idtac; keptFL_with ltac:(idtac; lazymatch goal with
            |- region_kept _ _ _ _ (YP09.mkRegion (Some 34%nat) _ _ _ _ _) =>
              (* the struct's shadow byte: in the shadow of the caller's frame (cid, pos) *)
              eapply region_kept_ownframe_ajO with (b := SB + n_ps cx / 8) (cid := n_cid cx) (pos := n_pos cx);
              [ kexact HK | evalE AG | exact Hin
              | right; unfold shadow_addr; rewrite <- SB_SHADOW_OFF in Hpssh |- *; unfold SB in *; lia
              | intros a Ha Hn; exact Hn | intros a Ha; lia ] end)
          HK HJ2 AG Kgot0 Kgot2 Kcell0 Kcell2 Kguar0 Kguar2 Kuar0 Kuar2 ltac:(idtac; fail) ltac:(idtac; fail)).
(* ---- the frame F (atom 516), its flag pointer FL (528) and shadow address (529) ---- *)
prreg HS (10%bv : bv 5) RF. cbn [ms_regs] in RF. rewrite Ha0 in RF. symmetry in RF. unfold w64 in RF. fold F in RF.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_pi_havoc_hi 528 Ev ssv msv [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS
    ltac:(vm_compute; reflexivity)) as HS3;
  hei_pose Ev 528%nat [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  assert (E528 : ew Ev 528 = Z_to_bv 64 FL)
    by (rewrite HEv; exact (ew_havoc_new _ 528 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
  assert (E529 : ew Ev 529 = Z_to_bv 64 (SB + F / 8))
    by (rewrite HEv; exact (ew_havoc_new _ 528 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia)));
  assert (E32' : ew Ev 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat) by lia; exact E32) end.
clear HEv.
assert (HFq : F = 64 * (F / 64)) by (pose proof (Z.div_mod F 64 ltac:(lia)); lia).
assert (HF8 : F / 8 = 8 * (F / 64))
  by (rewrite HFq at 1; replace (64 * (F / 64)) with (8 * (F / 64) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 + 8 <= 2 ^ 44)
  by (assert (F / 8 < 2 ^ 44 - 7) by (apply Z.div_lt_upper_bound; lia); lia).
destruct (FFL _ _ _ _ _ 0 fpos HAR2 Hfin2) as (HFLpres & HFLown & HFLrng). fold FL in HFLpres, HFLown, HFLrng.
pose proof HFhigh as HFapp2. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp2.
pose proof HFLrng as HFLapp. try (unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFLapp).
pose proof Hpsapp as Hpa. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpa.
pose proof (Z.div_mod (n_ps cx) 8 ltac:(lia)) as Hpd. pose proof (Z.mod_pos_bound (n_ps cx) 8 ltac:(lia)) as Hpm.
pose proof HFhigh_img as HFoi. unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HFoi.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  pose proof (st_ok_pi_add_fact Ev _ _ 516 (HPTR 5) HS
    ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite RF, unsigned_lit_small by lia;
          change (2 ^ 5) with 32; lia)) as HS3;
  clear HS; rename HS3 into HS;
  pose proof (st_ok_pi_add_fact Ev _ _ 528 (HPTR 0) HS
    ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E528, unsigned_lit_small by lia;
          rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
  clear HS; rename HS3 into HS;
  pose proof (st_ok_pi_add_fact Ev _ _ 529 (mkAF (SB + 512) (SB + 17592186044416) 2) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E529, unsigned_lit_small by (unfold SB; lia);
          change (2 ^ 2) with 4; unfold SB;
          split; [lia|]; split; [rewrite HF8; replace (2147450880 + 8 * (F / 64)) with ((536862720 + 2 * (F / 64)) * 4) by lia;
                                  apply Z_mod_mult | lia])) as HS3;
  clear HS; rename HS3 into HS;
  pose proof (st_ok_pi_add_alias Ev _ _ _ _ HS (shadow_decl_ok Ev 516 32 529 F SB RF ltac:(lia) E32' E529)) as HS3;
  clear HS; rename HS3 into HS end.
norm_ss HS.
(* the frame region (the flag pointer in its last word) *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msX) =>
  assert (HRF : region_ok SEGS Ev (ms_mem (restrict (w_H (n_W cx)) msX))
            (YP09.mkRegion (Some 516%nat) 0 64 0 64 [YP09.mkChunk 56 (CVal 8 (SOff 528 0))]));
  [ unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
    rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
    [ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia)))
    | apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Ev _ F 56 8 _ FL);
      [ cbn [sv_denot]; rewrite E528, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside
      | replace (F + 56) with (F + 64 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag) ] ]
  | ];
  assert (HDF : all_disjoint Ev (YP09.mkRegion (Some 516%nat) 0 64 0 64 [YP09.mkChunk 56 (CVal 8 (SOff 528 0))]) (ss_mem ssx));
  [ let rs2 := eval vm_compute in (ss_mem ssx) in
      change (all_disjoint Ev (YP09.mkRegion (Some 516%nat) 0 64 0 64 [YP09.mkChunk 56 (CVal 8 (SOff 528 0))]) rs2);
    cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite RF; evalE AG; unfold SB;
    revert Hq0 Hq1 Hsp1 Hsplo Hsphi Hps0 Hpshi Hob241 Hob242 Hob256 Hob257 Hpa Hspc C1 HNS
      HF4096 HFceil HFapp2 HFoi HdFP Hfa1 Hfa2;
    clear; intros;
    repeat split; lia
  | ];
  pose proof (st_ok_pi_add_region Ev ssx (restrict (w_H (n_W cx)) msX) (YP09.mkRegion (Some 516%nat) 0 64 0 64 [YP09.mkChunk 56 (CVal 8 (SOff 528 0))]) HS eq_refl HRF HDF) as HS3;
  clear HRF HDF; clear HS; rename HS3 into HS end.
norm_ss HS.
(* the frame's shadow: 8 zero bytes after __asan_stack_malloc_0 *)
assert (ZS : val_mem SEGS (mrestrict (w_H (n_W cx)) mem2) (SB + F / 8) 8 0).
{ apply val_mem_zero8. intros ii Hii. unfold zero_shadow, shadow_of_addr in Hz. rewrite <- SB_SHADOW_OFF in Hz.
  apply Hz. change (64 / 8) with 8. lia. }
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msX) =>
  assert (HRS : region_ok SEGS Ev (ms_mem (restrict (w_H (n_W cx)) msX))
            (fshadow_region 529 0 0 8 [YP09.mkChunk 0 (CVal 8 (SLit 0))]));
  [ unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
    change (fs_frame_bytes 0 / 8) with 8; rewrite E529, unsigned_lit_small by (unfold SB; lia);
    split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
    [ intros o Ho; apply (apresent_writable SEGS); unfold shadow_addr in HFSpres; rewrite <- SB_SHADOW_OFF in HFSpres;
      apply (proj1 (HFSpres o ltac:(change (64 / 8) with 8; lia)))
    | apply Forall_cons; [|apply Forall_nil];
      apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 0 8 _ 0); [reflexivity | zside | zside | rewrite Z.add_0_r; exact ZS] ]
  | ];
  assert (HDS : all_disjoint Ev (fshadow_region 529 0 0 8 [YP09.mkChunk 0 (CVal 8 (SLit 0))]) (ss_mem ssx));
  [ let rs2 := eval vm_compute in (ss_mem ssx) in
      change (all_disjoint Ev (fshadow_region 529 0 0 8 [YP09.mkChunk 0 (CVal 8 (SLit 0))]) rs2);
    cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    change (fs_frame_bytes 0 / 8) with 8; rewrite E529, RF; evalE AG; unfold SB;
    revert Hq0 Hq1 Hsp1 Hsplo Hsphi Hps0 Hpshi Hob241 Hob242 Hob256 Hob257 Hpa Hspc C1 HNS
      HF4096 HFceil HFapp2 HFoi HdFP Hfa1 Hfa2 HF8lo HF8hi HFq HF8 Hpd Hpm;
    clear; intros;
    repeat split; lia
  | ];
  pose proof (st_ok_pi_add_region Ev ssx (restrict (w_H (n_W cx)) msX) (fshadow_region 529 0 0 8 [YP09.mkChunk 0 (CVal 8 (SLit 0))]) HS eq_refl HRS HDS) as HS3;
  clear HRS HDS; clear HS; rename HS3 into HS end.
norm_ss HS.
(* 0x81638 .. 0x816e8: a5 := the shadow base, s3 := F, `bnez a0` (F <> 0), 0x90(s1) := F, the header,
   the shadow f1 f1 f1 f1 f8 f8 f3 f3, the UBSan guards on ps, 0x68(s1) := F, the shadow check of ps,
   ps->f, up to `beqz a0`. *)
hei_havoc HS; paj_run_sh RUNP HS HJ2. { awrFL AG fpos F EFA0. }
upd_aboveW HUP HFr AG. clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
- (* h = 0, the closed reader: 0x818c4 a1 := -1, a6 := 0x68(s1) = F, then NP_x0 0x818cc *)
  rewrite branch_eq_U, (U_atom _ 33 (n_h cx) E33 Hh64), U_lit in Hc by lia. apply Z.eqb_eq in Hc. rename Hc into Hh0.
  hei_havoc HS; paj_run_to_sh RUNTOP HS HJ2 NP_x0. { awrFL AG fpos F EFA0. }
  upd_aboveW HUP HFr AG. clear HF HFr HG.
  (* the caller's journal with this call's frame on its own list *)
  pose proof (ajournal_sub SEGS B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HJ2
    ltac:(lia) ltac:(lia) ltac:(intros a (rg & [] & _))) as HJF.
  cbn [app] in HJF.
  pose proof HJ2 as (_ & _ & _ & _ & Haos & _).
  destruct (aos_step_closed [] _ _ sink_closed_nil Haos) as (Hfd & Hfsys & _ & _).
  pose proof (acall_kept_of_journal SEGS B Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun _ => False) HJ2 HAR
    ltac:(intros a (rg & [] & _)) ltac:(intros b m i Hb _ _; rewrite Eab; exact Hb) sink_closed_nil) as HKc.
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msF) =>
  assert (HENV : nx_env cx fpos Ev);
  [ split; [intros n Hn; rewrite AG by lia; exact (nxb_env_low _ _ _ EEa HEE n Hn)|];
    split; [exact E32'|]; split; [exact E60|]; split; [exact RF|]; split; [exact E528 | exact E529]
  | ];
  prreg HS (19%bv : bv 5) R19; prreg HS (16%bv : bv 5) R16; prreg HS (11%bv : bv 5) R11;
  lazymatch goal with |- SRr _ ?Wg (mkCfg ?msG ?mdG) _ =>
    apply (HX0 cx fpos (n_k cx + 0) (n_lyc cx) S2 Wg msG mdG HB HJF Hfrs2) end;
  unfold nx_x0_inv; split; [|split; [|split; [|split]]];
  [ exact (nx_land0_by B KS LAWS cx fpos (n_k cx + 0) (n_lyc cx) S2 (n_W cx) msF _ HB HJF Hfrs2 Ev ssx false
      [18446744073709551601; 18446744073709551601; 18446744073709551601; 18446744073709551601;
       18446744073709551608; 18446744073709551608; 18446744073709551603; 18446744073709551603]
      NSH_entry HENV (ltac:(assumption)) HS eq_refl
      (nx_sr_ok_std B KS cx fpos HB Ev (ss_regs ssx) HENV eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl)
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl)
  | rewrite R19; exact RF
  | rewrite R16; exact RF
  | split; [reflexivity|]; split; [exact Eab|];
    split; [rewrite ES2; apply (mo_le_set_fs_r MT MTF); exact (mle_start MT _ MTL)|];
    split; [unfold m_fds; rewrite Hfd; reflexivity | unfold m_fs; rewrite Hfsys; reflexivity]
  | left; split; [exact Hh0|]; split;
    [ rewrite R11; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity
    | apply nxb_kept_of_acall; exact HKc ] ] end.
- (* h <> 0, the open reader: the spills 0x816ec .. 0x81748, then the loop head NP_loop 0x8174c *)
  rewrite branch_eq_U, (U_atom _ 33 (n_h cx) E33 Hh64), U_lit in Hc by lia. apply Z.eqb_neq in Hc. rename Hc into Hh0.
  hei_havoc HS; paj_run_to_sh RUNTOP HS HJ2 NP_loop. { awrFL AG fpos F EFA0. }
  upd_aboveW HUP HFr AG. clear HF HFr HG.
  pose proof (ajournal_sub SEGS B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HJ2
    ltac:(lia) ltac:(lia) ltac:(intros a (rg & [] & _))) as HJF.
  cbn [app] in HJF.
  pose proof HJ2 as (_ & _ & _ & _ & Haos & _).
  destruct (aos_step_closed [] _ _ sink_closed_nil Haos) as (Hfd & Hfsys & _ & _).
  pose proof (acall_kept_of_journal SEGS B Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun _ => False) HJ2 HAR
    ltac:(intros a (rg & [] & _)) ltac:(intros b m i Hb _ _; rewrite Eab; exact Hb) sink_closed_nil) as HKc.
  pose proof HKc as (K1 & K2 & K3 & K4 & _).
  unbox. specialize (Hpsat Hh0). specialize (Hswz Hh0). specialize (Hrng Hh0).
  destruct (Hbufb Hh0) as (Hbin & Hb4096 & Hbhi & Hbj & Hbjl & Hcap & _ & _).
  destruct (Hstream Hh0) as (Hhin & Hbin2 & Hsrc & HClen & Hp & _).
  clear Hbufb Hstream. box Htsb. box Hwrps. box Hmeta.
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msF) =>
  assert (KF : forall a, frame_addr (n_lyc cx) (n_cid cx) (n_pos cx) <= a <
                 frame_addr (n_lyc cx) (n_cid cx) (n_pos cx) + fs_frame_bytes (n_cid cx) ->
            mbyte SEGS (rdW (n_W cx) (ms_mem msF)) a = mbyte SEGS (rdW (n_W cx) (n_memc cx)) a);
  [ intros a Ha; apply (mbyte_of_aview SEGS); apply (K4 _ _ a Hin);
    [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | intros []] | ];
  assert (KFS : forall a, frame_addr (n_lyc cx) (n_cid cx) (n_pos cx) <= a <
                  frame_addr (n_lyc cx) (n_cid cx) (n_pos cx) + fs_frame_bytes (n_cid cx) ->
            aview SEGS (w_H (n_W cx)) (ms_mem msF) (shadow_of_addr SHADOW_OFF a) =
            aview SEGS (w_H (n_W cx)) (n_memc cx) (shadow_of_addr SHADOW_OFF a));
  [ intros a Ha; apply (K4 _ _ _ Hin);
    [ right; unfold in_zr, shadow_addr, shadow_of_addr; cbn [fst snd];
      pose proof (nxb_shadow_in _ _ a Hc8 Hcb8 (proj1 Ha) (proj2 Ha)); lia
    | intros [] ] | ];
  assert (KB : forall b n i, In (b, n) (ablocks B (n_lyc cx) (n_Sc cx)) -> 0 <= i < req_size n ->
            mbyte SEGS (rdW (n_W cx) (ms_mem msF)) (b + i) = mbyte SEGS (rdW (n_W cx) (n_memc cx)) (b + i));
  [ intros b n i Hb Hi; apply (mbyte_of_aview SEGS); apply (K2 b n i Hb Hi); intros [] | ];
  assert (HENV : nx_env cx fpos Ev);
  [ split; [intros n Hn; rewrite AG by lia; exact (nxb_env_low _ _ _ EEa HEE n Hn)|];
    split; [exact E32'|]; split; [exact E60|]; split; [exact RF|]; split; [exact E528 | exact E529]
  | ];
  prreg HS (19%bv : bv 5) R19; prreg HS (21%bv : bv 5) R21; prreg HS (23%bv : bv 5) R23;
  prreg HS (26%bv : bv 5) R26; prreg HS (27%bv : bv 5) R27;
  pose proof (st_ok_pi_restrict_reg _ _ _ _ (20%bv : bv 5) HS) as R20;
  let e20 := eval vm_compute in (sr_get (ss_regs ssx) (20%bv : bv 5)) in
    change (sr_get (ss_regs ssx) (20%bv : bv 5)) with e20 in R20; cbn [ms_regs restrict mkst] in R20;
  lazymatch goal with |- SRr _ ?Wg (mkCfg ?msG ?mdG) _ =>
    apply (HLOOP cx fpos (n_k cx + 0) (n_lyc cx) S2 Wg msG mdG HB HJF Hfrs2) end;
  exists (n_p cx), None; split; [exact I|];
  unfold nx_loop_inv, nx_mid;
  split; [split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split;
          [|split; [|split; [|split; [|split; [|split]]]]]]]]]]]]] | split; [|split]];
  [ (* nx_body *)
    exact (nx_land_by B KS LAWS cx fpos (n_k cx + 0) (n_lyc cx) S2 (n_W cx) msF _ HB HJF Hfrs2 Ev ssx
      [18446744073709551601; 18446744073709551601; 18446744073709551601; 18446744073709551601;
       18446744073709551608; 18446744073709551608; 18446744073709551603; 18446744073709551603]
      NSH_entry HENV (ltac:(assumption)) HS eq_refl
      (nx_sr_ok_std B KS cx fpos HB Ev (ss_regs ssx) HENV eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl)
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl Hh0)
  | (* s5 = ps *) rewrite R21, (AG 10%nat) by lia; exact E10
  | (* s7 = cap *) rewrite R23, (AG 12%nat) by lia; rewrite (EEa 12%nat 12%bv eq_refl); exact H12
  | (* s10 = the shadow address of ps *) rewrite R26; exact E34
  | (* s11 = ps + 8 *) rewrite R27, (AG 10%nat) by lia; rewrite E10, unsigned_lit_small by lia; reflexivity
  | (* the journal's bookkeeping *)
    split; [reflexivity|]; split; [exact Eab|];
    split; [rewrite ES2; apply (mo_le_set_fs_r MT MTF); exact (mle_start MT _ MTL)|];
    split; [unfold m_fds; rewrite Hfd; reflexivity | unfold m_fs; rewrite Hfsys; reflexivity]
  | (* kept *)
    apply (nx_kept_mono SEGS NX_STK_B B _ _ _ _ _ _ _ (fun _ => False) (nx_E cx) (fun a (H : False) => False_ind _ H));
    apply nxb_kept_of_acall; exact HKc
  | intros a Ha; exact Ha
  | exact Hh0
  | (* the struct *)
    apply (nxb_ps_at_frame (rdW (n_W cx) (n_memc cx))); [|exact Hpsat];
    intros x Hx; apply KF; unfold PS_LEN in Hx; lia
  | (* its shadow *)
    apply (PcapSourceCloseSpec.ra_frame (aview SEGS (w_H (n_W cx)) (n_memc cx))); [exact Hsh|];
    intros x Hx; apply KFS; unfold PS_LEN in Hx; lia
  | (* the stream at p *)
    apply (PcapSourceCloseSpec.asource_at_frame_segs _ KS (rdW (n_W cx) (n_memc cx))); [|exact Hsrc];
    intros a [Ha | [Ha | Ha]];
    [ replace a with (n_h cx + (a - n_h cx)) by lia; apply (KB _ SRC_FILE_BLOCK); [exact Hhin|];
      change (req_size SRC_FILE_BLOCK) with 1304; unfold SRC_FILE_BLOCK in Ha; lia
    | replace a with (n_b cx + (a - n_b cx)) by lia; apply (KB _ (Z.of_nat (length (n_C cx)))); [exact Hbin2|];
      pose proof (req_size_pos (Z.of_nat (length (n_C cx))) ltac:(lia)); lia
    | destruct (asil_env _ _ _ _ ASIL a Ha) as (Hi & Hno & Hne);
      apply (mbyte_of_aview SEGS); exact (K3 a Hi Hno Hne) ]
  | lia
  | (* the buffer *)
    exists (n_bj cx); split; [|reflexivity];
    apply (garr8_frame SEGS _ _ _ _ Hbj); intros a Ha;
    replace a with (n_buf cx + (a - n_buf cx)) by lia; apply (KB _ (nx_bufn (n_cap cx))); [exact Hbin|];
    pose proof (req_size_pos (nx_bufn (n_cap cx)) ltac:(unfold nx_bufn; lia)); lia
  | (* the timestamp cell *)
    intros Hts0; unbox;
    destruct (Htsb Hh0 Hts0) as (Htsv & Hts8 & Hts4096 & Htshi & _ & (tcid & tpos & Htown & Htf1 & Htf2) & _ & Htsra & _);
    assert (Htin : In (tcid, tpos) (frames (n_Sc cx))) by (rewrite Hfrs; apply in_or_app; left; exact Htown);
    pose proof (frame_al64 SEGS B _ _ _ _ _ _ _ HAR Htin) as (Hta64 & Htb64 & _);
    pose proof (nxb_mod64_8 _ Hta64) as Ht8; pose proof (nxb_mod64_8 _ Htb64) as Htb8;
    split;
    [ eapply PcapSourceCloseSpec.vm_frame_segs; [|exact Htsv]; intros x Hx; apply (mbyte_of_aview SEGS);
      apply (K4 _ _ x Htin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | intros []]
    | apply (PcapSourceCloseSpec.ra_frame (aview SEGS (w_H (n_W cx)) (n_memc cx))); [exact Htsra|];
      intros x Hx; apply (K4 _ _ _ Htin);
      [ right; unfold in_zr, shadow_addr, shadow_of_addr; cbn [fst snd];
        pose proof (nxb_shadow_in _ _ x Ht8 Htb8 ltac:(lia) ltac:(lia)); lia
      | intros [] ] ]
  | (* s3 = ph = F + 32 *) rewrite R19, RF, unsigned_lit_small by lia; reflexivity
  | (* s4 = the shadow address of ps + 8 *)
    rewrite R20;
    exact (nx_U_shx Ev 10 (n_ps cx) 8 E32' ltac:(rewrite (AG 10%nat) by lia; exact E10) ltac:(lia) ltac:(lia) ltac:(lia))
  | (* the model's chain from p *)
    apply nx_chain_start; lia ] end.
Qed.


End c.
End b.
End a.

(* SK is explicit (a Theorem Labs lane 21:57Z): the closure's only global sink_head instance is the PLAIN build's. *)
Arguments nx_entryX {fx rc} SK {PI}.

