(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryHead), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACa2.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACez.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChf.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChz.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntryHead.v, with its module paths, module names and numbers changed; 715 of its 824 lines of code are new or changed and 488 lines of the source are left out. *)
(* pcap_source_next, the ENTRY phase of the ASan walk (libreac v1.9.0, fuzz_pcap.asan): the slots
   NP_entry 0x8181c .. NP_loop 0x81998, and the closed reader's two slots NP_h0 0x81b2c -> NP_x0
   0x81d34. It proves `nx_start POST` from the two phases it reaches: the record loop's and the
   exit's.

   WHAT THE CODE DOES HERE (next.dis (sha256 06286410ee55; internal record), the pinned
   fuzz_pcap.asan image, sha256 b7a91d9b1fb0017d...):
   - 0x8181c..0x81860: the 224-byte machine frame (`addi sp,sp,-0xe0`), the probe store at sp0-224,
     ra and s0..s11 saved at sp0-8 .. sp0-104, s0 := sp0, `andi sp,sp,-0x20` and s1 := that
     realigned pointer (nx_sp1);
   - 0x81864..0x81888: the arguments into s4 (buf), s5 (ps), s6 (ts), s7 (cap); the two GOT words
     (object 1 -> object 15 the shadow-base cell, object 0 -> object 16 the use-after-return cell);
     s9 := the shadow base 0x7fff8000; a2 := the 32-bit use-after-return flag;
   - 0x8188c `beqz a2`: the flag is 1 in every state the ASan model allows (AR_const_law,
     YG0d.v:461-467 `rd32 (aview ..) (as_uar_cell B) 1`, a law of AR_laws, al_const YG0d.v:503,
     proved for the model in YG0s.v:70), so the branch to the machine-stack arm is NOT taken;
   - 0x81890..0x81898: `__asan_stack_malloc_0(0x40)`; its result is the class-0 frame F;
   - 0x818a4..0x818a8 `bnez a5`: F is a frame address, so 4096 <= F (frames_bounds) and the second
     entry to the machine-stack arm is not taken either. The arm 0x818ac..0x818c4 is therefore
     dead; it is refuted, never budgeted. (Independently of the flag, the arm could not be walked
     in this kit at all: it writes 0xf1/0xf8/0xf3 into the shadow of [sp1-64, sp1), inside
     [ly_stk_lo, ly_stk_hi), which every AR state keeps zero -- ARm's am_zshadow, YG0n.v:218 with
     the ranges :188-189 -- and which no clause of awr_byte (YCbq.v:457) permits to write.)
   - 0x818c8..0x81924: the frame's header (the live magic 0x41b58ab3, object 13 the frame's
     description string, object 14 the function's own address) and its 8 shadow bytes NSH_entry;
   - 0x81928..0x81930: the shadow check of ps (`lbu a0,0(s8)`, `bnez a0` to the error path at
     0x81e6c). The branch into the error path is proved not taken: ps is 8-aligned and
     range_addressable, so its first shadow byte is 0;
   - 0x81934..0x81938: `ld a0,0(s5)` = ps->f, `beqz a0` -> NP_h0 (the closed reader);
   - 0x8193c..0x81994: the ten remaining spill slots, then NP_loop;
   - NP_h0 0x81b2c..0x81b30: s6 := -1 and `j` NP_x0.

   The walk is the plain (region) engine of lib/Reusable/PaRun.v through PcapFrame's journal runs
   (SRr_run_pi_AJ / SRr_run_to_pi_AJ) and YC45's call run; the shadow bytes of ps and of the frame
   are regions of the symbolic state, so no shadow-token run is needed. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
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
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal PcapSyms PcapList PcapPa PcapPaLib PcapBase YC4b YC81 YC1g YC1h YC45 YC85 YC88 PcapFrame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PFreadISpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceNextDefs PcapSourceNextKit.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournalFs PcapSourceClose PcapSourceNextSeat.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the atoms and the regions of the entry state ---- *)
(* Atoms 0..31 are the entry registers; 32 the shadow base, 33 the FILE pointer ps->f, 34 the
   shadow byte of ps (so that the shadow check at 0x81928 needs no fresh atom), 60 the realigned
   stack pointer, and (after the call, by the kit's convention k = A_LIM = 512 and CLOB's fifth
   register a0) 516 the frame F, 528 its flag word and 529 its shadow. *)
Definition SB_NX : Z := 0x7fff8000.
Definition NXBx : sv := SOff 32 0.
Definition NXspan : Z * Z := (SB_NX, SB_NX + 2 ^ 44 - 1).

(* The saved registers of the machine frame (sp0-104 .. sp0), and the lowest word of the frame,
   which the prologue probes once (`sd zero,0(sp)` 0x81820). They are two regions because the
   realigned frame below s1 overlaps the rest of the 224 bytes. *)
Definition nx_saves_region : YP09.region := YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 [].
Definition nx_probe_region : YP09.region := YP09.mkRegion (Some 2%nat) (-224) (-216) (-224) (-216) [].
(* The caller's struct, as far as this phase reads it: its FILE pointer. *)
Definition nx_ps_region : YP09.region :=
  YP09.mkRegion (Some 10%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))].
(* Its first shadow byte, which the check at 0x81928 reads: 0, because ps is 8-aligned and the
   whole struct is addressable. *)
Definition nx_pssh_region : YP09.region :=
  YP09.mkRegion (Some 34%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].

Definition nx_regions0 : smem :=
  [ nx_saves_region; nx_probe_region; got_regionP; bcell_regionP 32;
    uar_got_regionP (A_OBJ 16); uar_cell_regionP (A_OBJ 16); nx_ps_region; nx_pssh_region ].

(* sp is 16-aligned and in the stack band; ps is 8-aligned and an application pointer; the shadow
   base is the constant. The alias lets the engine read `(ps >> 3) + s9` as atom 34
   (YP0i.v:189 shadow_decl_ok, YP0i.v:20 find_shadow_decl). *)
Definition nx_atoms0 : list (nat * afact) :=
  [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 (2 ^ 47) 3); (32%nat, mkAF SB_NX SB_NX 0) ].
Definition nx_alias0 : list (sv * sv) :=
  [ (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 32 0), SOff 34 0) ].
Definition nx_facts0 : facts := mkFacts nx_atoms0 [] nx_alias0.
Definition ss_nx0 : sstate := mkSS NP_entry sr_atoms nx_regions0 None nx_facts0.

Definition nx_extra (h ps : Z) : list word :=
  [Z_to_bv 64 SB_NX; Z_to_bv 64 h; Z_to_bv 64 (SB_NX + ps / 8)].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg pcap_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation SIGMA := (pa_sigma).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* One byte, read back from the shadow. *)
Lemma nx_val_mem1 : forall (H : word -> bool) (m : word -> option byte) a v,
  aview SEGS H m a = Some v -> 0 <= v < 256 -> val_mem SEGS (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv Hr k Hk. replace k with 0%nat by lia. cbn [Z.of_nat]. rewrite Z.add_0_r.
unfold aview in Hv. destruct (mbyte SEGS (mrestrict H m) a) as [b|] eqn:Hb; [|discriminate Hv].
cbn [option_map] in Hv. injection Hv as <-. f_equal.
rewrite (le_byte_small (bv_unsigned b) 1 0) by (cbn [Z.of_nat]; lia).
rewrite Z.mul_0_r, Z.shiftr_0_r. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* The first shadow byte of a range that is addressable and starts 8-aligned is 0: an address with
   x mod 8 = 7 forces saddr_ok's second arm to be impossible (YG0v.v:29). *)
Lemma nx_shadow0 : forall (rd : Z -> option Z) p n,
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


(* The shadow byte of an 8-aligned address inside a frame lies in the frame's shadow range. *)
Lemma nx_shadow_in_frame : forall f n q, f mod 64 = 0 -> n mod 64 = 0 -> q mod 8 = 0 ->
  f <= q -> q + 8 <= f + n ->
  shadow_addr f <= SHADOW_OFF + q / 8 /\ SHADOW_OFF + q / 8 + 1 <= shadow_addr f + n / 8.
Proof.
intros f n q Hf Hn Hq H1 H2. unfold shadow_addr.
pose proof (Z.div_mod f 64 ltac:(lia)) as Df. pose proof (Z.div_mod n 64 ltac:(lia)) as Dn.
pose proof (Z.div_mod q 8 ltac:(lia)) as Dq. rewrite Hf, Z.add_0_r in Df. rewrite Hn, Z.add_0_r in Dn.
rewrite Hq, Z.add_0_r in Dq.
assert (Ef : f / 8 = 8 * (f / 64)) by (rewrite Df at 1; replace (64 * (f / 64)) with ((8 * (f / 64)) * 8) by lia;
  apply Z.div_mul; lia).
assert (Efn : (f + n) / 8 = 8 * (f / 64) + 8 * (n / 64))
  by (rewrite Df at 1; rewrite Dn at 1;
      replace (64 * (f / 64) + 64 * (n / 64)) with ((8 * (f / 64) + 8 * (n / 64)) * 8) by lia;
      apply Z.div_mul; lia).
assert (En : n / 8 = 8 * (n / 64)) by (rewrite Dn at 1; replace (64 * (n / 64)) with ((8 * (n / 64)) * 8) by lia;
  apply Z.div_mul; lia).
rewrite Ef, En. lia.
Qed.

Local Ltac nlt := unfold A_TEXT; clear; lia.
(* nx_env of the walk's environment: atoms 0..31 are the entry registers (AG / EEa / HEE), and the
   atoms 32, 60, 516, 528, 529 carry their facts. *)
Local Ltac nx_env_tac AG EEa HEE E32 E60 Hsp1n RF E528 E529 :=
  unfold nx_env; split;
  [ let n := fresh "n" in let Hn := fresh "Hn" in intros n Hn; rewrite (AG n) by lia;
    assert (Hr : Z.of_nat n = bv_unsigned (Z_to_bv 5 (Z.of_nat n)))
      by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 5) with 32; rewrite Z.mod_small by lia;
          reflexivity);
    rewrite (EEa n _ Hr), (HEE n _ Hr); reflexivity
  | split; [cbv [NA_SB]; rewrite (AG 32%nat) by lia; exact E32|];
    split; [cbv [NA_SP1]; rewrite E60, Hsp1n; reflexivity|];
    split; [cbv [NA_F]; rewrite RF; reflexivity|];
    split; [cbv [NA_FL]; rewrite E528; reflexivity | cbv [NA_FSH]; rewrite E529; reflexivity] ].
(* Disjointness of region extents, once evalE has placed every base: the atoms' values are literals
   below 2 ^ 64, and the zone facts in the context separate them. *)
Local Ltac nx_dj :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 (pa_val ?a))] =>
      rewrite (unsigned_lit_small (pa_val a)) by (pose proof (pa_val_range a); lia)
  | |- context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (unsigned_lit_small x) by (first [lia | unfold SB_NX; lia])
  end;
  unfold SB_NX; repeat split; lia.

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
(* The runtime entry this phase calls, by cgif's name (YG0d.v:285), and the model's progress law
   for a class-0 frame (YCbq.v:803). *)
Hypothesis ASM0 : astack_malloc_realizes SEGS B NX_CID.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis FFL : frame_flag_lawP SEGS B.
(* The stream's environment cells lie in the image and are neither the allocator's static ranges nor
   errno (a Theorem Labs lane's lib/A/Stdio/PSourceMeta.v; PcapSourceClose takes the same hypothesis). *)
Hypothesis ASIL : PSourceMeta.asource_img_laws SK SEGS B KS.

Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let BR := paj_branch (PI := PI).

(* ---- what a kept call leaves of the caller's memory ---- *)

Lemma nx_keep_frame : forall lyc Sc (W : world SEGS) memc W2 mem2 slo shi cid pos a,
  acall_kept SEGS B lyc Sc W memc W2 mem2 slo shi (fun _ => False) ->
  In (cid, pos) (frames Sc) ->
  (in_zr a (frame_rng lyc (cid, pos)) \/
   in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
  mbyte SEGS (mrestrict (w_H W2) mem2) a = mbyte SEGS (mrestrict (w_H W) memc) a.
Proof.
intros lyc Sc W memc W2 mem2 slo shi cid pos a (_ & _ & _ & K4 & _) Hin Hr.
apply (mbyte_of_aview SEGS). exact (K4 cid pos a Hin Hr (fun H : False => H)).
Qed.

Lemma nx_keep_block : forall lyc Sc (W : world SEGS) memc W2 mem2 slo shi b m i,
  acall_kept SEGS B lyc Sc W memc W2 mem2 slo shi (fun _ => False) ->
  In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m ->
  mbyte SEGS (mrestrict (w_H W2) mem2) (b + i) = mbyte SEGS (mrestrict (w_H W) memc) (b + i).
Proof.
intros lyc Sc W memc W2 mem2 slo shi b m i (_ & K2 & _) Hin Hi.
apply (mbyte_of_aview SEGS). exact (K2 b m i Hin Hi (fun H : False => H)).
Qed.

Lemma nx_keep_img : forall lyc Sc (W : world SEGS) memc W2 mem2 slo shi a,
  acall_kept SEGS B lyc Sc W memc W2 mem2 slo shi (fun _ => False) ->
  in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  mbyte SEGS (mrestrict (w_H W2) mem2) a = mbyte SEGS (mrestrict (w_H W) memc) a.
Proof.
intros lyc Sc W memc W2 mem2 slo shi a (_ & _ & K3 & _) Hi Ho He.
apply (mbyte_of_aview SEGS). exact (K3 a Hi Ho He).
Qed.

(* ---- the symbolic state at NP_entry ---- *)

Lemma nx_entry_st : forall (W : world SEGS) lyc Sc (memc : word -> option byte) mdc
  (regs : bvmap 5 word) (ps h : Z),
  AR SEGS B lyc Sc W memc mdc ->
  (forall a, spZ regs - NX_STK <= a < spZ regs -> apresent (w_H W) memc a) ->
  alloc_ceiling + NX_STK <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  getr regs 10 = w64 ps ->
  ps mod 8 = 0 -> 4096 <= ps -> ps + PS_LEN <= alloc_ceiling -> off_img ps PS_LEN ->
  (ps + PS_LEN <= kLowShadowBeg \/ kHighMemBeg <= ps) ->
  val_mem SEGS (rdW W memc) (ps + PS_F_OFF) 8 h -> 0 <= h < 2 ^ 64 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF ps PS_LEN ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (nx_extra h ps))) ss_nx0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + NP_entry)) memc (seg_rom SEGS))).
Proof.
intros W lyc Sc memc mdc regs ps h HAR Hpres Hsp Hal16 H10 Hps8 Hps0 Hpsc Hpsimg Hpsband Hfv Hh Hsh.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Hpshi : ps + PS_LEN <= 2 ^ 47) by lia.
assert (HNS : NX_STK = 8496) by reflexivity.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite (palf_got_uar B TL) in Kguar. rewrite (pal_uar_cell B TL) in Kguar, Kuar.
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1.
pose proof (pa_obj_img 15 ltac:(lia)) as Hob15. pose proof (pa_obj_img 16 ltac:(lia)) as Hob16.
pose proof (palf_sep B TLF) as Hsep. rewrite (pal_uar_cell B TL) in Hsep.
cbn [zseps zseps_from fst snd] in Hsep.
unfold pcap_img_end, YImgTop.IMG_TOP in Hob0, Hob1, Hob15, Hob16.
unfold off_img, pcap_img_end, YImgTop.IMG_TOP, YImgTop.IMG_LO in Hpsimg.
unfold PS_LEN in *.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (nx_extra h ps))).
assert (E2 : ew E 2 = getr regs 2)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 ps)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
      rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB_NX)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 h)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (SB_NX + ps / 8))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (EO : forall i, (i < 17)%nat -> ew E (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)))
  by (intros i Hi; subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros nn v Hn' Hv. cbn [base_val]. rewrite Hn'. apply unsigned_lit_small. exact Hv. }
assert (Hps64 : 0 <= ps < 2 ^ 64) by lia.
assert (Hsb64 : 0 <= SB_NX + ps / 8 < 2 ^ 64)
  by (unfold SB_NX; pose proof (Z.div_pos ps 8 ltac:(lia) ltac:(lia));
      pose proof (Z.div_lt_upper_bound ps 8 (2 ^ 47) ltac:(lia) ltac:(lia)); lia).
assert (Hps_shadow : aview SEGS (w_H W) memc (SHADOW_OFF + ps / 8) = Some 0)
  by (apply (nx_shadow0 _ ps 24); [exact Hps8 | lia | exact Hsh]).
unfold ss_nx0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- (unfold nx_regions0, nx_saves_region, nx_probe_region, got_regionP, bcell_regionP,
         uar_got_regionP, uar_cell_regionP, nx_ps_region, nx_pssh_region).
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
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 15)) 0 8 (SOff 32 0) SB_NX);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | unfold SB_NX; zside | zside |].
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
    rewrite Z.add_0_r. unfold PS_F_OFF in Hfv. rewrite Z.add_0_r in Hfv. exact Hfv.
  + fold E. rewrite (VB 34%nat (SB_NX + ps / 8) E34) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (SB_NX + ps / 8) 0 1 (SLit 0) 0); [reflexivity | zside | zside |].
    rewrite Z.add_0_r. apply (nx_val_mem1 (w_H W) memc); [|lia].
    change SHADOW_OFF with SB_NX in Hps_shadow. exact Hps_shadow.
- apply pairwise_disjoint_of_extents.
  unfold nx_regions0, nx_saves_region, nx_probe_region, got_regionP, bcell_regionP,
         uar_got_regionP, uar_cell_regionP, nx_ps_region, nx_pssh_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. fold E.
  rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) (EO 1%nat ltac:(lia))) by (pose proof (pa_val_range (A_OBJ 1)); lia).
  rewrite (VB (A_OBJ 15) (VAL (A_OBJ 15)) (EO 15%nat ltac:(lia))) by (pose proof (pa_val_range (A_OBJ 15)); lia).
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) (EO 0%nat ltac:(lia))) by (pose proof (pa_val_range (A_OBJ 0)); lia).
  rewrite (VB (A_OBJ 16) (VAL (A_OBJ 16)) (EO 16%nat ltac:(lia))) by (pose proof (pa_val_range (A_OBJ 16)); lia).
  rewrite (VB 10%nat ps E10) by lia.
  rewrite (VB 34%nat (SB_NX + ps / 8) E34) by lia.
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  pose proof (Z.div_pos ps 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_lt_upper_bound ps 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
  assert (Hpsd : ps = 8 * (ps / 8)) by (pose proof (Z.div_mod ps 8 ltac:(lia)); lia).
  revert Hsep Hob0 Hob1 Hob15 Hob16 Hpsimg Hpsband Hps0 Hpsc Hpshi Hsp Hpsd C1 HNS.
  unfold SB_NX, kLowShadowBeg, kHighMemBeg. clear. intros.
  repeat split; lia.
- split; [|split; [exact I | ]].
  + cbn [f_atoms atoms_ok nx_facts0 nx_atoms0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    fold E. rewrite Usp, E10, E32. rewrite !unsigned_lit_small by (unfold SB_NX; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
    repeat split; try exact I; unfold SB_NX; lia.
  + cbn [f_alias nx_facts0 nx_alias0 alias_ok]. split; [|exact I].
    exact (shadow_decl_ok E 10 32 34 ps SB_NX E10 Hps64 E32 E34).
Qed.

(* nx_kept is acall_kept with the one extra premise `~ E a` in the top clause. *)
Lemma nx_kept_of_acall : forall lyc Sc (W : world SEGS) memc W2 mem2 sp E,
  acall_kept SEGS B lyc Sc W memc W2 mem2 (sp - NX_STK) sp E ->
  nx_kept SEGS NX_STK B lyc Sc W memc W2 mem2 sp E.
Proof.
intros lyc Sc W memc W2 mem2 sp E (K1 & K2 & K3 & K4 & K5 & K6).
split; [intros a Ha Hw _; exact (K1 a Ha Hw)|].
split; [exact K2|]. split; [exact K3|]. split; [exact K4|].
split; [intros a Ha Hw Hp; exact (K5 a Ha Hw Hp) | exact K6].
Qed.

(* ---- the entry phase ---- *)

Theorem nx_entryX : forall POST,
  nx_from SK B KS POST (nx_loop_at B MT KS (fun _ _ => True)) ->
  nx_from SK B KS POST (nx_x0_inv B MT KS) ->
  nx_start SK B KS POST.
Proof.
intros POST HLOOP HX0 cx HB.
pose proof HB as (HJ & HROD & Hraw & Hra4 & Hgp & Htp & H10 & H11 & H12 & H13 & Hal16 & Hwlo & Hwhi
  & Hchn & Hroom & Hfv & Hh64 & Hps8 & Hps0 & Hpshi & Hamr & Hown & Hfa1 & Hfa2 & Hsh
  & Hpsat & Hswz & Hrng & Hwrps & Hbufb & Htsb & Hstream & Hmeta & HEE & HEsp).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (pa_base_lo (PL := PL_pcap) (PI := PI)) as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk0 & F1 & F2 & F3 & F4 & Hgone
  & Hpres & Hstk & F5 & HQT).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (HNS : NX_STK = 8496) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
unfold PS_LEN in Hpshi, Hfa2.
(* ps lies in a frame of the caller's journal: so it is outside the image. *)
assert (Hin : In (n_cid cx, n_pos cx) (frames (n_Sc cx)))
  by (rewrite Hfrs; apply in_or_app; left; exact Hown).
pose proof (frm_off_imgP B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx)
  (n_cid cx) (n_pos cx) HAR Hin) as Hfimg.
destruct (frames_bounds SEGS B LAWS (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx)
  (n_cid cx) (n_pos cx) HAR Hin) as (Hf4096 & Hfceil & Hfapp).
pose proof (frame_al64 SEGS B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx)
  (n_cid cx) (n_pos cx) HAR Hin) as (HFc64 & HFb64 & HFb).
assert (Hpsimg : off_img (n_ps cx) PS_LEN)
  by (clear - Hfimg Hfa1 Hfa2 Hps0; unfold off_img, PS_LEN in *; lia).
assert (Hsplo : alloc_ceiling + NX_STK <= spZ (n_regs cx)) by (clear - Hceil Hslo Hwlo; lia).
assert (Hsphi : spZ (n_regs cx) <= 2 ^ 47) by (clear - Hwhi Hshi H47; lia).
assert (Hpsc : n_ps cx + 24 <= alloc_ceiling) by (clear - Hfa2 Hfceil; lia).
assert (Hpsband : n_ps cx + 24 <= kLowShadowBeg \/ kHighMemBeg <= n_ps cx)
  by (clear - Hfapp Hfa1 Hfa2; unfold in_app, PS_LEN in *; lia).
unfold kLowShadowBeg, kHighMemBeg in Hpsband.
assert (Hpsd : n_ps cx = 8 * (n_ps cx / 8))
  by (clear - Hps8; pose proof (Z.div_mod (n_ps cx) 8 ltac:(lia)); lia).
assert (Hpsd0 : 0 <= n_ps cx / 8) by (clear - Hps0; apply Z.div_pos; lia).
assert (Hpresw : forall a, spZ (n_regs cx) - NX_STK <= a < spZ (n_regs cx) ->
                   apresent (w_H (n_W cx)) (n_memc cx) a)
  by (intros a Ha; apply Hpres; clear - Ha Hwlo Hwhi; lia).
pose proof (nx_entry_st (n_W cx) (n_lyc cx) (n_Sc cx) (n_memc cx) (n_mdc cx) (n_regs cx)
  (n_ps cx) (n_h cx) HAR Hpresw (conj Hsplo Hsphi) Hal16 H10 Hps8 Hps0 Hpsc Hpsimg Hpsband
  Hfv Hh64 Hsh) as HS.
(* the inner journal: from the call's entry memory, with this call's own stack window *)
pose proof (ajournal_sub_init SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx)
  (n_mem0 cx) (n_md0 cx) (n_own cx) (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) (n_k cx)
  NX_STK (spZ (n_regs cx)) [] (spZ (n_regs cx) - n_sp0 cx) HJ ltac:(ring)
  ltac:(rewrite <- Zminus_mod_idemp_l, Hal16, <- Zminus_mod_idemp_r, Hsp0al; reflexivity)
  ltac:(clear - Hwhi; lia) ltac:(rewrite HNS; clear; lia) ltac:(clear - Hwlo; lia)) as HJ0.
remember (Eimg (Ereg (n_regs cx) (nx_extra (n_h cx) (n_ps cx)))) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (n_regs cx) (nx_extra (n_h cx) (n_ps cx))) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr (n_regs cx) 1)
  by (rewrite EL by nlt; exact (ew_Ereg_nat _ _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr (n_regs cx) 2)
  by (rewrite EL by nlt; exact (ew_Ereg_nat _ _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr (n_regs cx) 3)
  by (rewrite EL by nlt; exact (ew_Ereg_nat _ _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr (n_regs cx) 4)
  by (rewrite EL by nlt; exact (ew_Ereg_nat _ _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr (n_regs cx) 8)
  by (rewrite EL by nlt; exact (ew_Ereg_nat _ _ 8 8%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 (n_ps cx))
  by (rewrite EL by nlt; rewrite (ew_Ereg_nat _ _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 (n_buf cx))
  by (rewrite EL by nlt; rewrite (ew_Ereg_nat _ _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 (n_cap cx))
  by (rewrite EL by nlt; rewrite (ew_Ereg_nat _ _ 12 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 (n_ts cx))
  by (rewrite EL by nlt; rewrite (ew_Ereg_nat _ _ 13 13%bv eq_refl); exact H13).
assert (E32 : ew E 32 = Z_to_bv 64 SB_NX)
  by (rewrite EL by nlt; exact (ew_Ereg_extra _ _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (n_h cx))
  by (rewrite EL by nlt; exact (ew_Ereg_extra _ _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (SB_NX + n_ps cx / 8))
  by (rewrite EL by nlt; exact (ew_Ereg_extra _ _ 2)).
change SB_NX with SB in E32, E34.
assert (EEa : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (n_regs cx) r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAE : env_agree 32 (Ereg (n_regs cx) (nx_extra (n_h cx) (n_ps cx))) E)
  by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; clear - Hn; lia | reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ (n_regs cx)) by (rewrite E2; reflexivity).
clear HEdef EL.
img_factsF E. img_hull_factsF.
unfold pcap_img_end, YImgTop.IMG_TOP in Hob241, Hob242, Hob256, Hob257.
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
assert (EFA0 : forall c p, frame_addr (n_lyc cx) c p = frame_addr (n_lyc cx) c p) by reflexivity.
unfold nx_start. change (w64 (BASE + NP_entry)) with (Z_to_bv 64 (BASE + NP_entry)).
(* 0x8181c .. 0x81860: the frame, the probe, the 13 saves and the realignment. *)
box HB. box HJ. box HROD. box Hchn. box Hpsat. box Hswz. box Hrng. box Hwrps. box Hbufb. box Htsb.
box Hstream. box Hmeta. box HEE. box HEsp. box F1. box F2. box F3. box F4. box F5. box Hgone. box Hly.
box Hio. box HQT. box Hwle. box Hsecs. box Hnev.
hei_havoc HS; paj_run_to_sh RUNTOP HS HJ0 (symaddr ((Symbols.Asan.s_pcap_source_next + 0x44) - Symbols.Asan.s_libreac_fuzz_fopen)%Z). { awrFL AG 0 0 EFA0. }
clear HF HFr HG.
(* sp is now 32 * ((sp0 - 224) / 32) = n_sp1; atom 60 names it, and the spill slots below
   s1 + 120 get their own region. *)
set (sp1 := 32 * ((spZ (n_regs cx) + -224) / 32)).
destruct (sp1_facts (spZ (n_regs cx) + -224) ltac:(clear - Hsplo C1 HNS; lia)
  ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ (n_regs cx) - 240 <= sp1 <= spZ (n_regs cx) - 224) by (clear - Hsp1r; lia).
clear Hsp1r.
assert (Hsp1n : n_sp1 cx = sp1)
  by (unfold n_sp1, nx_sp1, NX_MFRAME, sp1; f_equal; f_equal; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  rreg_by HS (2%bv : bv 5) (Z_to_bv 64 sp1)
    (denot_and_m32 Ev 2 (spZ (n_regs cx)) (-224) ltac:(rewrite E2; symmetry; apply Z_to_bv_bv_unsigned)
       ltac:(clear - Hsplo C1 HNS; lia) ltac:(clear - Hsphi; lia) ltac:(clear - Hsplo Hsphi C1 HNS; lia)) R2 end.
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
          rewrite unsigned_lit_small by (clear - Hsp1 Hsplo Hsphi C1 HNS; lia); reflexivity)) as HS3;
  clear HS; rename HS3 into HS end.
norm_ss HS. clear R2.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_pi_add_fact Ev ssx msx 60%nat (mkAF (2 ^ 46 - 512) (2 ^ 47) 5) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2];
          rewrite E60, unsigned_lit_small by (clear - Hsp1 Hsplo Hsphi C1 HNS; lia);
          change (2 ^ 5) with 32; clear - Hsp1 Hsp1al Hsplo Hsphi C1 HNS; lia)) as HS3;
  clear HS; rename HS3 into HS end.
(* drop the probe's region: the spill region below overlaps it when sp1 = sp0 - 240 *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (ss_mem ssx) in
  lazymatch rs with
  | ?r0 :: ?r1 :: ?rt =>
    pose proof (st_ok_pi_submem Ex ssx msx (r0 :: rt) HS ltac:(cbn [ss_mem]; submem_to)
      ltac:(vm_compute; reflexivity)) as HS3;
    clear HS; rename HS3 into HS
  end
end.
norm_ss HS.
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 60%nat) 0 120 0 120 []) HS eq_refl
    ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks
                                 base_val ms_mem restrict mkst];
          rewrite E60, unsigned_lit_small by (clear - Hsp1 Hsplo Hsphi C1 HNS; lia);
          split; [clear - Hsp1 Hsplo C1 HNS; lia|]; split; [clear - Hsp1 Hsphi; lia|];
          split; [|apply Forall_nil];
          intros o Ho; apply (apresent_writable SEGS); apply HJpres; clear - Ho Hsp1 HNS; lia)
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
            let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
          cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
          evalE AG; nx_dj)) as HS3;
  clear HS; rename HS3 into HS end.
norm_ss HS.
(* 0x81860 .. 0x81894: s1, the arguments, the two GOT words, the use-after-return flag and the
   call. The flag cell holds 1 (uar_cell_regionP's chunk, from AR_const_law), so the engine itself
   decides `beqz a2` 0x8188c: the machine-stack arm is not entered here. *)
paj_run_shc RUNP RUNC HS HJ0. { awrFL AG 0 0 EFA0. }
clear HF HFr HG.
aconstsF HJ0 Kgot0 Kcell0 Kguar0 Kuar0.
prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (1%bv : bv 5) R1.
pmkst HS.
rewrite (palf_sm0 B TLF).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
  eapply (aj_stack_malloc_atS SEGS B LAWS Hsegs errno_low ML SMP 0 ASM0 ltac:(lia) (n_W cx)
    (ms_regs msX) (ms_mem msX) NX_STK (spZ (n_regs cx)) [] (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx)
    (n_mdc cx) [] (n_lyc cx) (n_Sc cx) _ 0 (sp1 - spZ (n_regs cx)) _ HJ0) end.
  - unfold spZ at 1. rewrite R2. evalE AG.
  - rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity.
  - clear - Hsp1; lia.
  - rewrite HNS, Hes; clear - Hsp1; lia.
  - rewrite R3. evalE AG. rewrite (EEa 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite R4. evalE AG. rewrite (EEa 4%nat 4%bv eq_refl). exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact Hroom. }
cbv beta. clear R2 R3 R4 R1.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2
  & Hbb2 & Hz & Hflag & HK & HJsm & (fS2 & ES2)).
(* the frame __asan_stack_malloc_0 gave: slot fpos of class 0, F = frame_addr, its flag word FL *)
aconstsF HJ2 Kgot2 Kcell2 Kguar2 Kuar2.
pose proof (proj1 HJ2) as HAR2.
assert (Hfin2 : In (0, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR2 Hfin2) as (HFal & [HFhi _] & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFhigh).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFhigh_img.
pose proof (frame_al64 SEGS B _ _ _ _ _ 0 fpos HAR2 Hfin2) as (HF64 & _ & _).
change (fs_frame_bytes 0) with 64 in HFal, HFhi, HFpres, HFSpres, HF4096, HFceil, HFhigh, HFhigh_img, Hz, Hflag.
set (F := frame_addr (n_lyc cx) 0 fpos) in *. set (FL := flag_addr (n_lyc cx) 0 fpos) in *.
(* the state after the call: its eight regions are kept (the call wrote only its ESTACK window and
   the fresh frame) *)
reseat HS HJ2 HP2 [0; 1; 2; 3; 4; 5; 6; 7]%nat AG
  ltac:(idtac; keptFL_with
    ltac:(lazymatch goal with
          | |- region_kept _ _ _ _ (YP09.mkRegion (Some 60%nat) _ _ _ _ _) =>
              eapply (region_kept_stack_ajO _ _);
              [ kexact HK | exact HJ2 | evalE AG | clear - Hsp1; lia | rewrite HNS; clear - Hsp1; lia
              | clear - Hsp1; lia | lia | lia ]
          | |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
              eapply (region_kept_stack_ajO _ _);
              [ kexact HK | exact HJ2 | evalE AG | clear - Hsp1; lia | rewrite HNS; clear - Hsp1; lia
              | clear - Hsp1; lia | lia | lia ]
          | |- region_kept _ _ _ _ (YP09.mkRegion (Some 34%nat) _ _ _ _ _) =>
              eapply (region_kept_ownframe_ajO _ _);
              [ kexact HK | evalE AG | exact Hin
              | right; destruct (nx_shadow_in_frame (frame_addr (n_lyc cx) (n_cid cx) (n_pos cx))
                                   (fs_frame_bytes (n_cid cx)) (n_ps cx) HFc64 HFb64 Hps8 Hfa1
                                   ltac:(clear - Hfa2; lia)) as [X1 X2];
                change SHADOW_OFF with 2147450880 in X1, X2; lia
              | intros a Ha Hn; exact Hn
              | intros a Ha; lia ]
          | |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some ?nn) _ _ _ _ _) =>
              lazymatch nn with
              | 242%nat => apply (region_kept_val_at Ex _ _ 242%nat (pa_val (A_OBJ 1)) 8 (pa_val (A_OBJ 15)));
                  [ match goal with Hh : img_env _ _ Ex |- _ => let Hq := fresh "Hq" in pose proof (Hh nn ltac:(unfold A_TEXT, A_LIM; lia)) as Hq; exact Hq end
                  | exact Kgot0
                  | exact Kgot2 | lia ]
              | 256%nat => apply (region_kept_val_at Ex _ _ 256%nat (pa_val (A_OBJ 15)) 8 SHADOW_OFF);
                  [ match goal with Hh : img_env _ _ Ex |- _ => let Hq := fresh "Hq" in pose proof (Hh nn ltac:(unfold A_TEXT, A_LIM; lia)) as Hq; exact Hq end
                  | exact Kcell0
                  | exact Kcell2 | lia ]
              | 241%nat => apply (region_kept_val_at Ex _ _ 241%nat (pa_val (A_OBJ 0)) 8 (as_uar_cell B));
                  [ match goal with Hh : img_env _ _ Ex |- _ => let Hq := fresh "Hq" in pose proof (Hh nn ltac:(unfold A_TEXT, A_LIM; lia)) as Hq; exact Hq end
                  | exact Kguar0
                  | exact Kguar2 | lia ]
              | 10%nat => eapply (region_kept_frame_ajO _ _ _ _ _ _ _ _ _ _ _ _ 10%nat _ _ _ _ _ (n_ps cx)
                              (n_cid cx) (n_pos cx));
                  [ kexact HK
                  | rewrite (AG 10%nat) by lia; rewrite E10; apply unsigned_lit_small; lia
                  | exact Hin
                  | clear - Hfa1; lia
                  | clear - Hfa2; lia
                  | lia
                  | intros a Ha Hn; exact Hn ]
              | 257%nat => apply (region_kept_val_at Ex _ _ 257%nat (as_uar_cell B) 4 1);
                  [ rewrite (pal_uar_cell B TL); match goal with Hh : img_env _ _ Ex |- _ => let Hq := fresh "Hq" in pose proof (Hh nn ltac:(unfold A_TEXT, A_LIM; lia)) as Hq; exact Hq end
                  | exact Kuar0
                  | exact Kuar2 | lia ]
              end
          end)
    HK HJ2 AG Kgot0 Kgot2 Kcell0 Kcell2 Kguar0 Kguar2 Kuar0 Kuar2 ltac:(idtac; fail) ltac:(idtac; fail)).
(* a0 = F: atom 516 by the kit's convention; atoms 528 / 529 name the flag word FL and the frame's
   shadow SB + F / 8; F's region carries the flag word __asan_stack_malloc_0 left in its last word *)
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
    by (rewrite HEv; exact (ew_havoc_new _ 528 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  assert (E32' : ew Ev 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat) by lia; exact E32) end.
assert (HFq : F = 64 * (F / 64)) by (clear - HF64; pose proof (Z.div_mod F 64 ltac:(lia)); lia).
assert (HF8 : F / 8 = 8 * (F / 64))
  by (clear - HFq; rewrite HFq at 1; replace (64 * (F / 64)) with (8 * (F / 64) * 8) by lia;
      rewrite Z.div_mul by lia; reflexivity).
assert (HF32 : F mod 32 = 0)
  by (clear - HFq; rewrite HFq; replace (64 * (F / 64)) with ((2 * (F / 64)) * 32) by lia; apply Z_mod_mult).
assert (HF8lo : 512 <= F / 8) by (clear - HF4096 HF8 HFq; lia).
assert (HF8hi : F / 8 < 17592186044416) by (clear - HFceil HF8 HFq C1; lia).
destruct (FFL (n_lyc cx) S2 (n_W cx) mem2 md2 0 fpos HAR2 Hfin2) as (HFLpres & HFLown & HFLrng).
fold FL in HFLpres, HFLown, HFLrng.
(* the caller's frame holding ps and the new frame are disjoint (both are frames of S2) *)
assert (HFsep : F + 64 <= frame_addr (n_lyc cx) (n_cid cx) (n_pos cx) \/
                frame_addr (n_lyc cx) (n_cid cx) (n_pos cx) + fs_frame_bytes (n_cid cx) <= F).
{ destruct (in_split _ _ Hin) as (l1 & l2 & Hl).
  pose proof (sep_frames_pos SEGS B LAWS (n_lyc cx) S2 (n_W cx) mem2 md2 (0, fpos) (n_cid cx, n_pos cx)
    [] l1 l2 HAR2 ltac:(rewrite Hfrs2, Hl; reflexivity)) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 0) with 64 in Hd.
  fold F in Hd. lia. }
assert (HFcq : frame_addr (n_lyc cx) (n_cid cx) (n_pos cx) = 64 * (frame_addr (n_lyc cx) (n_cid cx) (n_pos cx) / 64))
  by (clear - HFc64; pose proof (Z.div_mod (frame_addr (n_lyc cx) (n_cid cx) (n_pos cx)) 64 ltac:(lia)); lia).
assert (HFbq : fs_frame_bytes (n_cid cx) = 64 * (fs_frame_bytes (n_cid cx) / 64))
  by (clear - HFb64; pose proof (Z.div_mod (fs_frame_bytes (n_cid cx)) 64 ltac:(lia)); lia).
assert (HFzone : (F + 64 <= 2147450880 \/ 17594333495296 <= F) /\ (F + 64 <= 65536 \/ (symaddr ImgPages.Asan.top) <= F))
  by (clear - HFhigh HFhigh_img; unfold in_app, off_img, kLowShadowBeg, kHighMemBeg, pcap_img_end,
        YImgTop.IMG_TOP, YImgTop.IMG_LO in *; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  pose proof (st_ok_pi_add_fact Ev _ _ 516 (HPTR 5) HS
    ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite RF, unsigned_lit_small by lia;
          change (2 ^ 5) with 32; clear - HF4096 HFceil HF32 C1; lia)) as HS3;
  clear HS; rename HS3 into HS;
  pose proof (st_ok_pi_add_fact Ev _ _ 528 (HPTR 0) HS
    ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2];
          rewrite E528, unsigned_lit_small by (clear - HFLrng C1; unfold zone2, off_img, in_app,
            kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia);
          rewrite Z.pow_0_r, Z.mod_1_r; clear - HFLrng C1;
          unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia)) as HS3;
  clear HS; rename HS3 into HS;
  pose proof (st_ok_pi_add_fact Ev _ _ 529 (mkAF (SB + 512) (SB + 17592186044416) 2) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E529, unsigned_lit_small by (unfold SB; lia);
          change (2 ^ 2) with 4; unfold SB;
          split; [lia|]; split; [rewrite HF8; replace (2147450880 + 8 * (F / 64)) with ((536862720 + 2 * (F / 64)) * 4) by lia;
                                 apply Z_mod_mult | lia])) as HS3;
  clear HS; rename HS3 into HS;
  pose proof (st_ok_pi_add_alias Ev _ _ _ _ HS (shadow_decl_ok Ev 516 32 529 F SB RF ltac:(lia) E32' E529)) as HS3;
  clear HS; rename HS3 into HS; norm_ss HS;
  pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 516%nat) 0 64 0 24 [YP09.mkChunk 56 (CVal 8 (SOff 528 0))])
    HS eq_refl
    ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val
                                 ms_mem restrict mkst app];
          rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
          [ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia)))
          | apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Ev _ F 56 8 _ FL);
            [ cbn [sv_denot]; rewrite E528, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
            | clear - HFLrng C1; unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; zside
            | zside
            | replace (F + 56) with (F + 64 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag) ] ])
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
            let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
          cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
          rewrite RF; evalE AG; nx_dj)) as HS3;
  clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  pose proof (st_ok_pi_add_region Ev _ _ (fshadow_region 529 0 0 8 []) HS eq_refl
    ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi
                                                 YP09.r_chunks base_val ms_mem restrict mkst app];
          change (fs_frame_bytes 0 / 8) with 8; rewrite E529, unsigned_lit_small by (unfold SB; lia);
          split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
          [ intros o Ho; apply (apresent_writable SEGS); unfold shadow_addr in HFSpres;
            rewrite <- SB_SHADOW_OFF in HFSpres; apply (proj1 (HFSpres o ltac:(change (64 / 8) with 8; lia)))
          | apply Forall_nil ])
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
            let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
          cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
          change (fs_frame_bytes 0 / 8) with 8; rewrite E529, RF; evalE AG; nx_dj)) as HS3;
  clear HS; rename HS3 into HS end.
norm_ss HS.
(* 0x81898 .. 0x81938: a5 := F (`bnez a5` taken: 4096 <= F, the fact on atom 516, so the machine-stack
   arm is not entered either), the frame's header and its 8 shadow bytes, NS_F0, the shadow check of
   ps (its byte is 0: the region of atom 34), ps->f, up to the `beqz` on it. *)
paj_run_sh RUNP HS HJ2. { awrFL AG fpos F EFA0. }
clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
- (* h = 0: the closed reader, NP_h0 0x81b2c: s6 := -1, `j` NP_x0 *)
  rewrite branch_eq_U, (U_atom _ 33 (n_h cx) E33 Hh64), U_lit in Hc by (clear - Hh64; lia).
  apply Z.eqb_eq in Hc.
  paj_run_to_sh RUNTOP HS HJ2 (symaddr ((Symbols.Asan.s_pcap_source_next + 0x518) - Symbols.Asan.s_libreac_fuzz_fopen)%Z). { awrFL AG fpos F EFA0. }
  clear HF HFr HG.
  lazymatch goal with |- SRr _ _ (mkCfg ?msG ?mdG) _ => set (msF := msG) in *; set (mdF := mdG) in * end.
  unbox.
  destruct (ajournal_sub_closed_fs SK SEGS B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    HJ HJ2 ltac:(clear - Hwlo; lia) ltac:(clear - Hwhi; lia) ltac:(intros a (r & [] & _)) sink_closed_nil)
    as (HJout & Hfds & Hfs).
  cbn [app] in HJout.
  assert (HKin : acall_kept SEGS B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_W cx) (ms_mem msF)
                   (spZ (n_regs cx) - NX_STK) (spZ (n_regs cx)) (fun _ => False)).
  { eapply (acall_kept_of_journal SEGS B Hsegs);
      [exact HJ2 | exact HAR | intros a (r & [] & _) | | exact sink_closed_nil].
    intros b m i Hb Hi _. rewrite Eab. exact Hb. }
  apply (HX0 cx fpos (n_k cx + 0) (n_lyc cx) S2 (n_W cx) msF mdF HB HJout Hfrs2).
  prreg HS (15%bv : bv 5) R15. prreg HS (22%bv : bv 5) R22.
  lazymatch type of HS with st_ok_pi _ _ ?Ec ?ssF _ =>
    assert (HEnv : nx_env cx fpos Ec) by (nx_env_tac AG EEa HEE E32 E60 Hsp1n RF E528 E529);
    unfold nx_x0_inv;
    split; [| split; [| split]];
    [ change NP_x0 with (ss_pc ssF);
      exact (nx_land0_by B KS LAWS cx fpos (n_k cx + 0) (n_lyc cx) S2 (n_W cx) msF mdF HB HJout Hfrs2
               Ec ssF false
               [18446744073709551601; 18446744073709551601; 18446744073709551601; 18446744073709551601;
                18446744073709551608; 18446744073709551608; 18446744073709551603; 18446744073709551603]
               NSH_entry HEnv ltac:(assumption) HS eq_refl
               (nx_sr_ok_std B KS cx fpos HB Ec (ss_regs ssF) HEnv eq_refl eq_refl eq_refl eq_refl eq_refl
                  eq_refl eq_refl)
               ltac:(vm_compute; reflexivity) eq_refl eq_refl)
    | rewrite R15, RF; reflexivity
    | unfold nx_jbk, EV_NEXT; split; [clear; lia|]; split; [exact Eab|];
      split; [rewrite ES2; apply (mo_le_set_fs_r MT MTF); apply (mo_le_refl MT MTL)|];
      split; [exact Hfds | exact Hfs]
    | unfold nx_fin_at, PcapSourceNextSpec.nx_fin; left; split; [exact Hc|]; split;
      [ rewrite R22; apply bv_eq; reflexivity
      | apply nx_kept_of_acall; exact HKin ] ]
  end.
- (* h <> 0: the ten remaining spill slots, up to NP_loop *)
  rewrite branch_eq_U, (U_atom _ 33 (n_h cx) E33 Hh64), U_lit in Hc by (clear - Hh64; lia).
  apply Z.eqb_neq in Hc.
  paj_run_to_sh RUNTOP HS HJ2 (symaddr ((Symbols.Asan.s_pcap_source_next + 0x17c) - Symbols.Asan.s_libreac_fuzz_fopen)%Z). { awrFL AG fpos F EFA0. }
  clear HF HFr HG.
  lazymatch goal with |- SRr _ _ (mkCfg ?msG ?mdG) _ => set (msF := msG) in *; set (mdF := mdG) in * end.
  destruct (ajournal_sub_closed_fs SK SEGS B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    HJ HJ2 ltac:(clear - Hwlo; lia) ltac:(clear - Hwhi; lia) ltac:(intros a (r & [] & _)) sink_closed_nil)
    as (HJout & Hfds & Hfs).
  cbn [app] in HJout.
  assert (HKin : acall_kept SEGS B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_W cx) (ms_mem msF)
                   (spZ (n_regs cx) - NX_STK) (spZ (n_regs cx)) (fun _ => False)).
  { eapply (acall_kept_of_journal SEGS B Hsegs);
      [exact HJ2 | exact HAR | intros a (r & [] & _) | | exact sink_closed_nil].
    intros b m i Hb Hi _. rewrite Eab. exact Hb. }
  (* the caller's struct and its shadow lie in the caller's own frame: both are kept *)
  assert (KPS : forall a, n_ps cx <= a < n_ps cx + 24 ->
            mbyte SEGS (rdW (n_W cx) (ms_mem msF)) a = mbyte SEGS (rdW (n_W cx) (n_memc cx)) a).
  { intros a Ha. apply (nx_keep_frame _ _ _ _ _ _ _ _ (n_cid cx) (n_pos cx) a HKin Hin).
    left. unfold in_zr, frame_rng. cbn [fst snd]. clear - Ha Hfa1 Hfa2. unfold PS_LEN in *. lia. }
  assert (Hps16 : (n_ps cx + 16) mod 8 = 0)
    by (clear - Hps8; rewrite Z.add_mod, Hps8 by lia; reflexivity).
  assert (Hhi8 : (n_ps cx + 16) / 8 = n_ps cx / 8 + 2).
  { clear - Hps8. pose proof (Z.div_mod (n_ps cx) 8 ltac:(lia)) as D. rewrite Hps8, Z.add_0_r in D.
    symmetry. apply (Z.div_unique (n_ps cx + 16) 8 (n_ps cx / 8 + 2) 0); [left; lia | lia]. }
  destruct (nx_shadow_in_frame (frame_addr (n_lyc cx) (n_cid cx) (n_pos cx)) (fs_frame_bytes (n_cid cx))
              (n_ps cx) HFc64 HFb64 Hps8 Hfa1 ltac:(clear - Hfa2; unfold PS_LEN in *; lia)) as [X1 X2].
  destruct (nx_shadow_in_frame (frame_addr (n_lyc cx) (n_cid cx) (n_pos cx)) (fs_frame_bytes (n_cid cx))
              (n_ps cx + 16) HFc64 HFb64 Hps16 ltac:(clear - Hfa1; lia)
              ltac:(clear - Hfa2; unfold PS_LEN in *; lia)) as [Y1 Y2].
  unfold shadow_addr in X1, X2, Y1, Y2. rewrite Hhi8 in Y2.
  assert (KPSSH : forall x, n_ps cx <= x < n_ps cx + 24 ->
            aview SEGS (w_H (n_W cx)) (ms_mem msF) (shadow_of_addr SHADOW_OFF x) =
            aview SEGS (w_H (n_W cx)) (n_memc cx) (shadow_of_addr SHADOW_OFF x)).
  { intros x Hx. pose proof HKin as (_ & _ & _ & K4 & _).
    apply (K4 (n_cid cx) (n_pos cx) _ Hin); [|exact (fun H : False => H)].
    right. unfold in_zr, shadow_addr, shadow_of_addr. cbn [fst snd].
    assert (H23 : (n_ps cx + 23) / 8 = n_ps cx / 8 + 2).
    { clear - Hps8. pose proof (Z.div_mod (n_ps cx) 8 ltac:(lia)) as D. rewrite Hps8, Z.add_0_r in D.
      symmetry. apply (Z.div_unique (n_ps cx + 23) 8 (n_ps cx / 8 + 2) 7); [left; lia | lia]. }
    assert (Hx8 : n_ps cx / 8 <= x / 8 <= n_ps cx / 8 + 2).
    { split; [apply Z.div_le_mono; clear - Hx; lia|].
      rewrite <- H23. apply Z.div_le_mono; [clear; lia | clear - Hx; lia]. }
    clear - X1 Y2 Hx8 Hhi8. lia. }
  destruct (Hstream Hc) as (Hinh & Hinb & HSRC & HClen & Hpq & _).
  destruct (Hbufb Hc) as (Hinbuf & Hbuf4096 & Hbufhi & Hgbuf & Hbjlen & Hcap & _).
  destruct (Hpsat Hc) as (Vf & Vsw & Vol & Vvt & Vvid & Vpad & Hpadlen).
  assert (KH : forall a, n_h cx <= a < n_h cx + SRC_FILE_BLOCK ->
            mbyte SEGS (rdW (n_W cx) (ms_mem msF)) a = mbyte SEGS (rdW (n_W cx) (n_memc cx)) a).
  { intros a Ha. replace a with (n_h cx + (a - n_h cx)) by (clear - Ha; lia).
    apply (nx_keep_block _ _ _ _ _ _ _ _ (n_h cx) SRC_FILE_BLOCK (a - n_h cx) HKin Hinh).
    change (req_size SRC_FILE_BLOCK) with SRC_FILE_BLOCK. clear - Ha. unfold SRC_FILE_BLOCK in *. lia. }
  assert (KBB : forall a, n_b cx <= a < n_b cx + Z.of_nat (length (n_C cx)) ->
            mbyte SEGS (rdW (n_W cx) (ms_mem msF)) a = mbyte SEGS (rdW (n_W cx) (n_memc cx)) a).
  { intros a Ha. replace a with (n_b cx + (a - n_b cx)) by (clear - Ha; lia).
    apply (nx_keep_block _ _ _ _ _ _ _ _ (n_b cx) (Z.of_nat (length (n_C cx))) (a - n_b cx) HKin Hinb).
    pose proof (req_size_pos (Z.of_nat (length (n_C cx))) ltac:(lia)) as [_ Hq]. clear - Ha Hq. lia. }
  assert (KENV : forall a, PSourceMeta.asrc_env_addr KS a ->
            mbyte SEGS (rdW (n_W cx) (ms_mem msF)) a = mbyte SEGS (rdW (n_W cx) (n_memc cx)) a).
  { intros a Ha. destruct (PSourceMeta.asil_env _ _ _ _ ASIL a Ha) as (Hi & Ho & He).
    exact (nx_keep_img _ _ _ _ _ _ _ _ a HKin Hi Ho He). }
  assert (KBUF : forall a, n_buf cx <= a < n_buf cx + Z.of_nat (length (n_bj cx)) ->
            mbyte SEGS (rdW (n_W cx) (ms_mem msF)) a = mbyte SEGS (rdW (n_W cx) (n_memc cx)) a).
  { intros a Ha. replace a with (n_buf cx + (a - n_buf cx)) by (clear - Ha; lia).
    apply (nx_keep_block _ _ _ _ _ _ _ _ (n_buf cx) (nx_bufn (n_cap cx)) (a - n_buf cx) HKin Hinbuf).
    pose proof (req_size_pos (nx_bufn (n_cap cx)) ltac:(unfold nx_bufn; lia)) as [_ Hq].
    clear - Ha Hq Hbjlen. lia. }
  apply (HLOOP cx fpos (n_k cx + 0) (n_lyc cx) S2 (n_W cx) msF mdF HB HJout Hfrs2).
  exists (n_p cx), None. split; [exact I|].
  prreg HS (24%bv : bv 5) R24. prreg HS (20%bv : bv 5) R20. prreg HS (21%bv : bv 5) R21.
  prreg HS (23%bv : bv 5) R23. prreg HS (26%bv : bv 5) R26.
  lazymatch type of HS with st_ok_pi _ _ ?Ec ?ssF _ =>
    assert (HEnv : nx_env cx fpos Ec) by (nx_env_tac AG EEa HEE E32 E60 Hsp1n RF E528 E529);
    assert (HBody : nx_body cx fpos NP_loop (n_W cx) msF NSH_entry)
      by (change NP_loop with (ss_pc ssF);
          exact (nx_land_by B KS LAWS cx fpos (n_k cx + 0) (n_lyc cx) S2 (n_W cx) msF mdF HB HJout Hfrs2
                   Ec ssF
                   [18446744073709551601; 18446744073709551601; 18446744073709551601; 18446744073709551601;
                    18446744073709551608; 18446744073709551608; 18446744073709551603; 18446744073709551603]
                   NSH_entry HEnv ltac:(assumption) HS eq_refl
                   (nx_sr_ok_std B KS cx fpos HB Ec (ss_regs ssF) HEnv eq_refl eq_refl eq_refl eq_refl eq_refl
                      eq_refl eq_refl)
                   ltac:(vm_compute; reflexivity) eq_refl eq_refl Hc));
    assert (HS8 : getr (ms_regs msF) 24 = w64 (shadow_of_addr SHADOW_OFF (n_ps cx)))
      by (rewrite R24; cbn [sv_denot]; rewrite ?E34, ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
          unfold shadow_of_addr, SB_NX, w64; first [reflexivity | f_equal; clear; lia]);
    assert (HR20 : getr (ms_regs msF) 20 = w64 (n_buf cx))
      by (rewrite R20; cbn [sv_denot]; rewrite ?(AG 11%nat) by (clear; lia);
          rewrite ?E11, ?Z.add_0_r, ?Z_to_bv_bv_unsigned; unfold w64; first [reflexivity | f_equal; clear; lia]);
    assert (HR21 : getr (ms_regs msF) 21 = w64 (n_ps cx))
      by (rewrite R21; cbn [sv_denot]; rewrite ?(AG 10%nat) by (clear; lia);
          rewrite ?E10, ?Z.add_0_r, ?Z_to_bv_bv_unsigned; unfold w64; first [reflexivity | f_equal; clear; lia]);
    assert (HR23 : getr (ms_regs msF) 23 = w64 (n_cap cx))
      by (rewrite R23; cbn [sv_denot]; rewrite ?(AG 12%nat) by (clear; lia);
          rewrite ?E12, ?Z.add_0_r, ?Z_to_bv_bv_unsigned; unfold w64; first [reflexivity | f_equal; clear; lia]);
    assert (HR26 : getr (ms_regs msF) 26 = w64 (nF cx fpos + NO_PH))
      by (rewrite R26; cbn [sv_denot]; rewrite ?RF; unfold nF, NO_PH, w64;
          rewrite ?unsigned_lit_small by (clear - HF4096 HFceil C1; lia);
          first [reflexivity | f_equal; clear - HF4096 HFceil C1; lia])
  end.
  unfold nx_loop_inv. split.
  { unfold nx_mid.
    split; [exact HBody|].
    split; [exact HS8|].
    split.
    { unfold nx_jbk, EV_NEXT. split; [clear; lia|]. split; [exact Eab|].
      split; [rewrite ES2; apply (mo_le_set_fs_r MT MTF); apply (mo_le_refl MT MTL)|].
      split; [exact Hfds | exact Hfs]. }
    split.
    { apply nx_kept_of_acall. apply (acall_kept_mono_E SEGS B _ _ _ _ _ _ _ _ _ _ HKin). intros a []. }
    split; [intros a Ha; exact Ha|].
    split; [exact Hc|].
    split.
    { unfold nx_ps_at, nx_ol.
      split; [eapply vm_frame; [intros x Hx; apply KPS; cbn [Z.of_nat] in Hx; unfold PS_F_OFF in *; clear - Hx; lia | exact Vf]|].
      split; [eapply vm_frame; [intros x Hx; apply KPS; cbn [Z.of_nat] in Hx; unfold PS_SW_OFF in *; clear - Hx; lia | exact Vsw]|].
      split; [eapply vm_frame; [intros x Hx; apply KPS; cbn [Z.of_nat] in Hx; unfold PS_OL_OFF in *; clear - Hx; lia | exact Vol]|].
      split; [eapply vm_frame; [intros x Hx; apply KPS; cbn [Z.of_nat] in Hx; unfold PS_VT_OFF in *; clear - Hx; lia | exact Vvt]|].
      split; [eapply vm_frame; [intros x Hx; apply KPS; cbn [Z.of_nat] in Hx; unfold PS_VID_OFF in *; clear - Hx; lia | exact Vvid]|].
      split; [| exact Hpadlen].
      apply (garr8_frame SEGS _ _ _ _ Vpad). intros x Hx. rewrite Hpadlen in Hx. cbn [Z.of_nat] in Hx.
      apply KPS. clear - Hx. lia. }
    split.
    { apply (ra_frame (aview SEGS (w_H (n_W cx)) (n_memc cx))); [exact Hsh|].
      intros x Hx. apply KPSSH. unfold PS_LEN in Hx. exact Hx. }
    split.
    { apply (asource_at_frame KS (rdW (n_W cx) (n_memc cx))); [| exact HSRC].
      intros a [Ha | [Ha | Ha]]; [apply KH; exact Ha | apply KBB; exact Ha | apply KENV; exact Ha]. }
    split; [clear - Hpq; lia|].
    split.
    { exists (n_bj cx). split; [| reflexivity].
      apply (garr8_frame SEGS _ _ _ _ Hgbuf). intros x Hx. apply KBUF. exact Hx. }
    intros Hts.
    destruct (Htsb Hc Hts) as (Vts & Hts8 & Hts4096 & Htshi & Htsamr &
                               (tcid & tpos & Htin & Htfa1 & Htfa2) & _ & Htsra & _).
    assert (Htinf : In (tcid, tpos) (frames (n_Sc cx)))
      by (rewrite Hfrs; apply in_or_app; left; exact Htin).
    pose proof (frame_al64 SEGS B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) tcid tpos HAR Htinf)
      as (Htc64 & Htb64 & _).
    destruct (nx_shadow_in_frame (frame_addr (n_lyc cx) tcid tpos) (fs_frame_bytes tcid) (n_ts cx)
                Htc64 Htb64 Hts8 Htfa1 ltac:(clear - Htfa2; lia)) as [Z1 Z2].
    unfold shadow_addr in Z1, Z2.
    assert (H7 : (n_ts cx + 7) / 8 = n_ts cx / 8).
    { clear - Hts8. pose proof (Z.div_mod (n_ts cx) 8 ltac:(lia)) as D. rewrite Hts8, Z.add_0_r in D.
      symmetry. apply (Z.div_unique (n_ts cx + 7) 8 (n_ts cx / 8) 7); [left; lia | lia]. }
    split.
    { eapply vm_frame; [| exact Vts]. intros x Hx. cbn [Z.of_nat] in Hx.
      apply (nx_keep_frame _ _ _ _ _ _ _ _ tcid tpos x HKin Htinf).
      left. unfold in_zr, frame_rng. cbn [fst snd]. clear - Hx Htfa1 Htfa2. lia. }
    apply (ra_frame (aview SEGS (w_H (n_W cx)) (n_memc cx))); [exact Htsra|].
    intros x Hx. pose proof HKin as (_ & _ & _ & K4 & _).
    apply (K4 tcid tpos _ Htinf); [|exact (fun H : False => H)].
    right. unfold in_zr, shadow_addr, shadow_of_addr. cbn [fst snd].
    assert (Hx8 : n_ts cx / 8 <= x / 8 <= n_ts cx / 8).
    { split; [apply Z.div_le_mono; clear - Hx; lia|].
      rewrite <- H7. apply Z.div_le_mono; [clear; lia | clear - Hx; lia]. }
    clear - Z1 Z2 Hx8. lia. }
  split; [exact HR20|]. split; [exact HR21|]. split; [exact HR23|]. split; [exact HR26|].
  apply nx_chain_start. clear - Hpq. lia.
Qed.

End c.
End b.
End a.
