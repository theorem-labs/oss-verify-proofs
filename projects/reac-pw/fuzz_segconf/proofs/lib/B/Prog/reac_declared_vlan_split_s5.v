(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_box_catalogue on fuzz_segconf.asan-ubsan (image B, pin sha256
   c3796c0b38f3, twin 80e82127e8ca; entry 0x8a8a0, 84 bytes, 21 instructions, a 16-byte frame, no side-stack
   frame): reac_box_catalogue_contract of lib/B/Prog/reac_box_catalogue_c.v (image B's copy of the image-A owner's FINAL
   text at 6f783602b5e3) at image B's numbers, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the
   entry, SRr of apost_base at the return, over `Context {PI : PAImg seg_listing}` of image B's listing,
   lib/B/Prog/SegPa.v).
   ADAPTATION (relocation + one trap) of lib/A/Prog/reac_box_catalogueA.v (the image-A m_file-family lane, commit
   434ade288123, both arms): the same entry seeds, token runs and return steps over image B's listing modules and
   B's kit copies. The UBSan alignment check is read from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_catalogue.v
   at origin/ossv/recipes 3abc3740de97 (the same image-B code but 4 pc-relative words; caller-journal form, not
   copied), whose token run decides it the same way.
   Image B's code differs from image A's by two instructions: `andi a1,a0,7` (0x8a8ac) and `bnez a1,0x8a8ec`
   (0x8a8b0) to `unimp` (0x8a8ec), the UBSan alignment check of the 8-byte store through c.
   UBSan trap branch (one): 0x8a8b0 `bnez a1` -> unimp 0x8a8ec. Not taken: the c <> 0 run's entry seed carries the
   fact (10%nat, mkAF 4096 (2 ^ 47 - 8) 3) on a0 (rbc_facts: c is 2^3-aligned, from the contract premise
   c mod 8 = 0, seeded by rbc_entry), so the token executor (paj_run_tok, its branch step under facts_ok) computes
   a1 = c & 7 = 0 and decides the branch not taken; the trap instruction is never executed. The c = 0 run leaves at
   the beqz 0x8a8a8 (a0 pinned to 0) before the check.
   c <> 0: the instrumented check of the 8-byte cell (a load of the shadow byte at (c >> 3) + the shadow base, lbu
   0x8a8c8, and a compare, bnez 0x8a8cc) reads 0, because the contract's sa_addr gives the cell addressable; so the
   error path (the call of errpath_store8 at 0x8a8f0) is not reached; the sd at 0x8a8d4 writes 11 as 8 bytes. In
   both arms a0 = fuzz_catalogue (auipc/addi 0x8a8d8-0x8a8dc, 0xa20a0). The shadow base is the word the GOT cell
   as_got_shadow B holds (image B 0xa3210, the ld at 0x8a8b8, listing object 0; its target
   __asan_shadow_memory_dynamic_address 0xac7b8, listing object 12): the walk takes both from PALib (pal_got_shadow,
   pal_cell), a listing fact, not a contract premise.
   Positional names checked against image B's own listing (lib/B/Prog/SegAddr.v seg_objs, SegList.v) by address and
   anchor symbol (twin nm): A_OBJ 0 = 0xa3210 (the .got word the ld at 0x8a8b8 reads), A_OBJ 12 = 0xac7b8
   (__asan_shadow_memory_dynamic_address), A_OBJ 77 = RBC_CAT_OBJ = 0xa20a0 (fuzz_catalogue; SegList.v
   `PAddHi (10%bv : reg) (10%bv : reg) 123 (A_OBJ 77) 0x0` at 0x8a8dc), AF_reac_box_catalogue = 0x5ae0 =
   0x8a8a0 - seg_text 0x84dc0, atom 32 = the first extra env word (the shadow base SB, rbc_extra): 5 checked, 0
   pointing elsewhere.
   Image B's numbers of the statement: the entry BASE + AF_reac_box_catalogue; STK_reac_box_catalogue = 16 (the
   contract's STK comment: its frame, 0x8a8a0 addi sp,sp,-16 released at 0x8a8e4; the unimp at 0x8a8ec and the jal
   at 0x8a8f0 are the dead trap and error arms; no callee); cat = catA = 0xa20a0. Both are lib/B/Prog/SegInstB.v's
   definitions (SegInstA's names at image B): SegInstB.STK_reac_box_catalogue and SegInstB.catA, tied to this walk
   by the lemmas STK_reac_box_catalogue_B (the value 16) and catA_B (listing object 77 of B's seg_objs). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 387 of its 436 lines of code are new or changed and 404 lines of the source are left out. *)
(* reac_declared_vlan_split on fuzz_segconf image B (fuzz_segconf.asan-ubsan): the point K5 (0x8a388, listing offset
   0x55c8), after the checked memcpy, to the point K6 (0x8a3b0), after name_ok.
   0x8a388 `not a0,s1`, 0x8a38c `bltu a0,s4` to the UBSan trap `unimp` 0x8a3d8 (parent + plen wraps; refuted:
   parent + 16 <= 2 ^ 47 and plen <= 15); 0x8a390 `add a0,s1,s4`; the instrumented check of the 1-byte store at
   parent + plen (0x8a394-0x8a3a0, slow path 0x8a3e8, error path 0x8a3f0; killed by the shadow of [parent,
   parent + 16)); 0x8a3a4 `sb zero,0(a0)`, the NUL; 0x8a3a8 `mv a0,s1`; 0x8a3ac `jal name_ok` (B 0x8a408), a program
   call through PaCall's cl_callS against name_ok_contract; its post gives the point K6. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0p YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaDenot PaSB PaLibG PaLibH PaLibF PaCallRun PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegGlob SegPgBase SegABase SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import name_ok_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_split_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_split_lem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_split_k reac_declared_vlan_split_d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_split_r reac_declared_vlan_split_h.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the seeded state at K5: atom 40 (the extra word) is parent + plen, and the alias s1 + s4 = atom 40 lets the run
   address the NUL store as atom 40 + 0; the store's region is the one byte there, its check the shadow entry *)
Definition vs5_R : YP09.region := YP09.mkRegion (Some 40%nat) 0 1 0 1 [].
Definition vs5_Bx : sv := SOff 22 0.
Definition vs5_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition vs5_SH : list shent := [mkSHE 40 0 1].
Definition vs5_fs : list (nat * afact) := [(40%nat, mkAF 4096 (2 ^ 47 - 2) 0)].
Definition vs5_al : sv := SAlu ALU_ADD (SOff 9 0) (SOff 20 0).

(* 0x8a38c `bltu a0,s4`, a0 = not parent (0x8a388), s4 = plen: the branch to the trap is taken only when
   parent + plen wraps (the image-B fuzz_command exemplar: sup_host_setting_aux.v hsb_ub_774 at 501c0d516c69) *)
Lemma vs5_lxor_ones : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x (2 ^ 64 - 1) = 2 ^ 64 - 1 - x.
Proof.
intros x Hx.
pose proof (Z.sub_lxor_2rlandn (2 ^ 64 - 1) x) as H.
assert (H0 : Z.land (Z.lnot (2 ^ 64 - 1)) x = 0).
{ replace (Z.lnot (2 ^ 64 - 1)) with (- (2 ^ 64)) by reflexivity.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
  destruct (Z_lt_dec n 64).
  - replace (- (2 ^ 64)) with (Z.shiftl (-1) 64) by reflexivity. rewrite Z.shiftl_spec_low by lia. reflexivity.
  - rewrite (Z.bits_above_log2 x); [apply Bool.andb_false_r | lia |].
    destruct (Z.eq_dec x 0); [subst; cbn; lia|].
    apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia | lia]. }
rewrite Z.lxor_comm. lia.
Qed.
Lemma vs5_ub_38c : forall t k, 0 <= t -> 0 <= k -> t + k < 2 ^ 64 ->
  branch_taken BC_LTU (alu64 ALU_XOR (Z_to_bv 64 t) (Z_to_bv 64 (-1))) (Z_to_bv 64 k) = false.
Proof.
intros t k H0 H1 H2. cbn [branch_taken]. rewrite bv_ltu_unsigned, alu64_unsigned. cbn [zalu_raw].
rewrite (unsigned_lit_small t), (unsigned_lit_small k) by lia.
replace (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1) by (vm_compute; reflexivity).
rewrite vs5_lxor_ones by lia.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
apply Z.ltb_ge. lia.
Qed.

(* a shadow fact moves to any reader that agrees on the shadow band *)
Lemma vs5_ra_band : forall (rd rd' : reader) a n,
  (forall s, SHADOW_OFF <= s < SHADOW_OFF + 2 ^ 44 -> rd' s = rd s) -> 0 <= a -> a + n <= 2 ^ 47 ->
  range_addressable rd SHADOW_OFF a n -> range_addressable rd' SHADOW_OFF a n.
Proof.
intros rd rd' a n HK Ha Han HR x Hx. destruct (HR x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
rewrite <- Hs. apply HK. unfold shadow_of_addr.
assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
assert (0 <= x / 8) by (apply Z.div_pos; lia). lia.
Qed.
Lemma vs5_hull_band : forall (rd rd' : reader) a n,
  (forall s, SHADOW_OFF <= s < SHADOW_OFF + 2 ^ 44 -> rd' s = rd s) -> 0 <= a -> a + n <= 2 ^ 47 -> 0 < n ->
  shadow_hull_vis rd a n -> shadow_hull_vis rd' a n.
Proof.
intros rd rd' a n HK Ha Han Hn HV s Hs. rewrite HK; [exact (HV s Hs)|].
unfold shadow_addr, SHADOW_OFF in Hs |- *.
replace (2147450880 + a / 8) with (268431360 * 8 + a / 8) in Hs by lia.
replace (2147450880 + (a + n - 1) / 8) with (268431360 * 8 + (a + n - 1) / 8) in Hs by lia.
rewrite !Z.div_add_l in Hs by lia.
pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)) as P1.
pose proof (Z.div_pos (a / 8) 8 ltac:(lia) ltac:(lia)) as P2.
assert (P3 : (a + n - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
pose proof (Z.mul_div_le ((a + n - 1) / 8) 8 ltac:(lia)) as P4.
lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the read-only window of arodata_okP lies in the image's span *)
Lemma vs5_ro_img : forall a, in_roP SEGS SegInstB.RLO_A SegInstB.RHI_A a -> 0x10000 <= a < kImgEnd.
Proof using.
intros a [(s & Hin & _ & Hr) | Hr].
- apply pa_img_range. exists s. split; [exact Hin | exact Hr].
- unfold SegInstB.RLO_A, SegInstB.RHI_A, SEG_RLO, SEG_RHI, kImgEnd in *. lia.
Qed.
Lemma vs5_rod_kept : forall B rlo rhi (rd rd' : reader),
  arodata_okP SEGS rlo rhi B rd -> (forall a, in_roP SEGS rlo rhi a -> rd' a = rd a) -> arodata_okP SEGS rlo rhi B rd'.
Proof using. intros B rlo rhi rd rd' H HK a Ha H1 H2. rewrite (HK a Ha). exact (H a Ha H1 H2). Qed.

Section e.
Variable B : asyms.
Variables gotw guard : Z.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Hypothesis NAMEOK : name_ok_contract SEGS B (BASE + AF_name_ok) NAME_OK_STK SegInstB.RLO_A SegInstB.RHI_A.
Hypothesis SIGP : seg_sig_prog.

(* a destination of sa_dst is present at the entry *)
Lemma vs5_dst_pres : forall ly S W mem md regs d n a,
  AR SEGS B ly S W mem md -> sa_dst SEGS B ly S W mem regs d n -> d <= a < d + n -> apresent (w_H W) mem a.
Proof using.
intros ly S W mem md regs d n a HAR HD Ha.
destruct HD as [((cid & pos & Hin & Hc & H1 & H2) & _) | [((b & m & Hin & H1 & H2) & _) | (H1 & H2 & HP & _)]].
- destruct (al_frames _ _ LAWS ly S W mem md cid pos HAR Hin) as (_ & _ & Hb & _). exact (proj1 (Hb a ltac:(lia))).
- destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & _ & _ & _ & Hb & _ & Bm).
  pose proof (req_size_pos m ltac:(lia)) as [Q1 Q2]. exact (proj1 (Hb a ltac:(lia))).
- replace a with (d + (a - d)) by lia. apply HP. lia.
Qed.
(* a destination of sa_dst holds no image byte and lies outside the image's span *)
Lemma vs5_dst_img : forall ly S W mem md regs STK d n a,
  AR SEGS B ly S W mem md -> astk_ok STK ly (spZ regs) -> sa_dst SEGS B ly S W mem regs d n -> d <= a < d + n ->
  ~ in_img SEGS a /\ (a < 0x10000 \/ kImgEnd <= a).
Proof using.
intros ly S W mem md regs STK d n a HAR Hstk HD Ha.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (pa_img_cover ly S md (proj1 (proj2 HAR))) as [IC1 IC2].
destruct HD as [((cid & pos & Hin & Hc & H1 & H2) & _) | [((b & m & Hin & H1 & H2) & _) | (H1 & H2 & HP & _)]].
- destruct (al_client_img _ _ LAWS ly S W mem md a HAR) as [N1 N2].
  { right; left. exists cid, pos. split; [exact Hin | lia]. }
  split; [exact N2|]. unfold in_zr in N1. lia.
- destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & _ & _ & _ & _ & _ & Bm).
  pose proof (req_size_pos m ltac:(lia)) as [Q1 Q2].
  destruct (al_client_img _ _ LAWS ly S W mem md a HAR) as [N1 N2].
  { left. exists b, m. split; [exact Hin | lia]. }
  split; [exact N2|]. unfold in_zr in N1. lia.
- split.
  + intros Him. pose proof (pa_segs_low a Him). lia.
  + right. unfold kImgEnd. lia.
Qed.
(* a register a run to a call left as an atom of the seeded state *)
Lemma vs5_reg_c : forall E ss (ms : machine_state) (H : word -> bool) n (r : bv 5) w,
  st_ok SEGS E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> ew E n = w -> getr (ms_regs ms) r = w.
Proof using.
intros E ss ms H n r w HS Hr Hn. rewrite (st_ok_restrict_reg SEGS H E ss ms r HS), Hr.
cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
(* the shadow hull of a shorter range *)
Lemma vs5_hull_sub : forall (rd : reader) x n n', 0 <= x -> 0 < n' <= n ->
  shadow_hull_vis rd x n -> shadow_hull_vis rd x n'.
Proof using.
intros rd x n n' Hx Hn H s Hs. apply H. unfold shadow_addr in *.
pose proof (Z.div_le_mono (x + n' - 1) (x + n - 1) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_le_mono (SHADOW_OFF + (x + n' - 1) / 8) (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia) ltac:(lia)).
lia.
Qed.

Lemma vs_K5 : vs_K6_stmt B gotw guard -> vs_K5_stmt B gotw guard.
Proof using NAMEOK SIGP.
intros HK6. unfold vs_K5_stmt.
intros e regs' mem' md' di v HE HCW Hd Hdi0 Hne Hdig Hv Hvr R20 R21 HCP.
pose proof HE as (HPRE & HROD & H10 & B10 & H11 & B11 & H12 & H13 & B13 & HSP & Hnev).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HCW as (HJ & HR & HSL & HK & HPR).
pose proof HR as (Hsp & G3 & G4 & G8 & G9 & G18 & G19 & G22 & G27).
pose proof HSP as (Hs0 & Hstr & Hlen & Hsadd & Hamr & Hsloc & Hp0 & Hcap & Hpdst & Hpadd & Hpdisj & Hv0 & Hv2 & Hvdst & Hvadd & Hvdisj & Hssp).
assert (HVS : VS_STK = 12352) by reflexivity.
unfold e_sp in *.
assert (Hnul : SegModel.nulfree (e_s e)) by exact (proj2 (proj1 Hstr)).
pose proof (vs_di_lt _ _ Hnul Hd) as Hdil.
assert (Hcopy : split_copy (e_s e) = Some di)
  by (apply vs_copy_some; [exact Hnul | exact Hlen | exact Hd | exact Hdi0 | exact Hne | exact Hdig | unfold vs_tail in Hv; lia]).
destruct (vs_dst_facts B _ _ _ _ _ _ _ _ 16 HAR Hstk ltac:(lia) Hpdst) as (Plo & Phi & Pplace).
destruct (vs_dst_facts B _ _ _ _ _ _ _ _ 2 HAR Hstk ltac:(lia) Hvdst) as (Vlo & Vhi & Vplace).
(* the shadow band is apart from the stack window and from [parent, parent + 16) *)
assert (BANDW : forall s, SHADOW_OFF <= s < SHADOW_OFF + 2 ^ 44 -> ~ (spZ (e_regs e) - VS_STK <= s < spZ (e_regs e)))
  by (intros s Hs Hw; unfold SHADOW_OFF in Hs; lia).
assert (BANDP : forall s, SHADOW_OFF <= s < SHADOW_OFF + 2 ^ 44 -> ~ (e_parent e <= s < e_parent e + 16)).
{ intros s Hs Hw. unfold SHADOW_OFF in Hs.
  destruct Pplace as [(Hia & _) | (Hsv & _)]; [unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hia | ]; lia. }
assert (BAND1 : forall s, SHADOW_OFF <= s < SHADOW_OFF + 2 ^ 44 -> rdW (e_W e) mem' s = rdW (e_W e) (e_mem e) s).
{ intros s Hs. apply HK; [unfold SHADOW_OFF in Hs; lia | exact (BANDW s Hs) | intros Hw; apply (BANDP s Hs); lia]. }
pose proof Hpadd as (Pa0 & Pa63 & Pamr & Pra & Phull).
assert (RAP : range_addressable (rdW (e_W e) mem') SHADOW_OFF (e_parent e) 16)
  by (apply (vs5_ra_band _ _ _ _ BAND1); [lia | lia | exact Pra]).
(* the seed: atom 40 = parent + plen *)
set (ys := [Z_to_bv 64 (e_parent e + Z.of_nat di)]).
set (E := Eimg (Ereg regs' (vs_xs (e_regs e) ++ ys))).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EV : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs' r)
  by (intros n r Hn; subst E; apply vs_EE; exact Hn).
assert (E40 : ew E 40 = Z_to_bv 64 (e_parent e + Z.of_nat di)) by (subst E; exact (vs_Ey regs' (e_regs e) ys 0 ltac:(lia))).
assert (HS0 : st_ok_pi SEGS VAL E (vs_ssK VS_K5 vs5_fs)
  (restrict (w_H (e_W e)) (mkst regs' (Z_to_bv 64 (BASE + VS_K5)) mem' (seg_rom SEGS)))).
{ apply vs_seedK.
  - replace (spZ regs' + 64) with (spZ (e_regs e)) by lia. exact HSL.
  - lia.
  - rewrite Hsp. replace (spZ (e_regs e) - 64) with (spZ (e_regs e) + (-4) * 16) by lia.
    rewrite Z_mod_plus_full. exact Hal16.
  - exact G22.
  - unfold vs5_fs. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E.
    rewrite E40, unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r.
    repeat split; first [exact I | lia]. }
assert (ALq : sv_denot E vs5_al = sv_denot E (SOff 40 0)).
{ unfold vs5_al. cbn [sv_denot]. rewrite (EV 9%nat 9%bv eq_refl), (EV 20%nat 20%bv eq_refl), E40, G9, R20.
  unfold w64. rewrite !Z.add_0_r. rewrite !unsigned_lit_small by lia.
  apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by lia.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
pose proof (st_ok_pi_add_alias E _ _ vs5_al (SOff 40 0) HS0 ALq) as HS1. clear HS0.
(* the region of the NUL store *)
assert (PRES : forall i, 0 <= i < 16 -> apresent (w_H (e_W e)) mem' (e_parent e + i))
  by (intros i Hi; apply HPR; apply (vs5_dst_pres _ _ _ _ _ _ _ _ _ HAR Hpdst); lia).
assert (BV40 : base_val E (Some 40%nat) = e_parent e + Z.of_nat di)
  by (cbn [base_val]; rewrite E40; apply unsigned_lit_small; lia).
assert (BV2 : base_val E (Some 2%nat) = spZ (e_regs e) - 64)
  by (cbn [base_val]; rewrite (EV 2%nat 2%bv eq_refl); exact Hsp).
assert (Rok : region_ok SEGS E (mrestrict (w_H (e_W e)) mem') vs5_R).
{ unfold region_ok, vs5_R. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite BV40. split; [lia|]. split; [lia|].
  split; [intros o Ho; apply (apresent_writable SEGS); replace (e_parent e + Z.of_nat di + o) with (e_parent e + (Z.of_nat di + o)) by lia; apply PRES; lia | constructor]. }
lazymatch type of HS1 with st_ok_pi _ _ _ ?ss ?msx =>
assert (Rdj : all_disjoint E vs5_R (ss_mem ss));
[ cbn [ss_mem set_facts vs_ssK all_disjoint extent_disjoint vs5_R vs_slots_r YP09.r_base YP09.r_lo YP09.r_hi];
  unfold extent_disjoint; cbn [vs5_R vs_slots_r YP09.r_base YP09.r_lo YP09.r_hi];
  rewrite BV40, BV2; split; [|exact I]; destruct Pplace as [(_ & Hp1) | (Hp1 & _)]; lia
| pose proof (st_ok_pi_add_region E ss msx vs5_R HS1 eq_refl Rok Rdj) as HS; clear HS1 ] end.
(* the shadow entry of the store's check *)
assert (UB : U E vs5_Bx = SHADOW_OFF).
{ unfold vs5_Bx. apply U_atom; [rewrite (EV 22%nat 22%bv eq_refl), G22; reflexivity | unfold SHADOW_OFF; lia]. }
assert (SHOK : sh_ok SEGS vs5_Bx vs5_SH E (mrestrict (w_H (e_W e)) mem')).
{ unfold sh_ok, vs5_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H (e_W e)) mem' E vs5_Bx 40 (e_parent e) 16 (e_parent e + Z.of_nat di) 0 1 RAP UB).
  - apply U_atom; [exact E40 | lia].
  - lia.
  - lia.
  - intros x Hx Hb. cbn [Z.min Z.max] in Hx. apply (BANDP x Hb). lia. }
assert (EU40 : bv_unsigned (ew E 40) = e_parent e + Z.of_nat di) by (rewrite E40; apply unsigned_lit_small; lia).
unfold vs_goal, vs_cfg.
(* 0x8a388 `not a0,s1`; the run stops at 0x8a38c `bltu a0,s4` *)
paj_run_tok RUN HS HJ SHOK vs5_Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  eapply (@awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 40%nat (e_parent e + Z.of_nat di)); [reflexivity | exact EU40 | |].
  - intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
    apply (vs_dst_awr B (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) (e_regs e) _ _ (e_ly e) (e_S e) [] (e_parent e) 16 a HAR Hpdst eq_refl (Permutation_refl _)); [| lia].
    unfold e_FP, split_W. rewrite Hcopy. exists (e_parent e, e_parent e + Z.of_nat di + 1).
    split; [apply in_or_app; left; left; reflexivity | cbn [fst snd]; lia].
  - repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
rename ms into ms1. rename HG into HG1.
lazymatch goal with Hfr : frame_of ?Ex _ (mrestrict _ _) (mrestrict _ _) |- _ =>
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => e_parent e + Z.of_nat di <= a < e_parent e + Z.of_nat di + 1) Hfr
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
      repeat (rewrite ew_ewset_other in Hrr by lia); rewrite ?EU40 in Hrr; cbv beta; lia|]);
    destruct Hin)) as UN1 end.
clear HF HFr.
psrr_branch_tok RUN BR HS SHOK vs5_Bspan.
{ (* 0x8a38c `bltu a0,s4` -> unimp 0x8a3d8: refuted by vs5_ub_38c from parent + plen < 2 ^ 64 (vs_dst_facts on
     split_pre's sa_dst parent 16: parent + 16 <= 2 ^ 47; plen < length s < 16) *)
  exfalso.
  cbn [sv_denot] in Hc. rewrite (EV 9%nat 9%bv eq_refl), (EV 20%nat 20%bv eq_refl), G9, R20 in Hc.
  unfold w64 in Hc. rewrite !Z.add_0_r, !unsigned_lit_small in Hc by lia.
  rewrite (vs5_ub_38c (e_parent e) (Z.of_nat di)) in Hc by lia. discriminate Hc. }
(* 0x8a390 .. 0x8a3ac: a0 := parent + plen (atom 40 by the alias), the check of the store (covered by the shadow entry
   of atom 40: decided, the error path 0x8a3f0 is not reached), `sb zero`, a0 := parent, the call of name_ok *)
paj_run_tok RUN HS HJ SHOK vs5_Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  eapply (@awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 40%nat (e_parent e + Z.of_nat di));
    [reflexivity | repeat (rewrite ew_ewset_other by lia); exact EU40 | |].
  - intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
    apply (vs_dst_awr B (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) (e_regs e) _ _ (e_ly e) (e_S e) [] (e_parent e) 16 a HAR Hpdst eq_refl (Permutation_refl _)); [| lia].
    unfold e_FP, split_W. rewrite Hcopy. exists (e_parent e, e_parent e + Z.of_nat di + 1).
    split; [apply in_or_app; left; left; reflexivity | cbn [fst snd]; lia].
  - repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
rename HG into HG2.
lazymatch goal with Hfr : frame_of ?Ex _ (mrestrict _ _) (mrestrict _ _) |- _ =>
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => e_parent e + Z.of_nat di <= a < e_parent e + Z.of_nat di + 1) Hfr
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
      repeat (rewrite ew_ewset_other in Hrr by lia); rewrite ?EU40 in Hrr; cbv beta; lia|]);
    destruct Hin)) as UN2 end.
clear HF HFr.
(* what the stretch K5 .. the call wrote: only parent[plen] *)
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (e_parent e + Z.of_nat di <= a < e_parent e + Z.of_nat di + 1) ->
  rdW (e_W e) (ms_mem ms) a = rdW (e_W e) mem' a)
  by (intros a Ha Hn; rewrite (UN2 a Ha Hn); exact (UN1 a Ha Hn)).
assert (GRW : forall a, apresent (w_H (e_W e)) mem' a -> apresent (w_H (e_W e)) (ms_mem ms) a)
  by (intros a Ha; apply (apresent_grows _ (ms_mem ms1) _ _ HG2); apply (apresent_grows _ mem' _ _ HG1); exact Ha).
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (e_regs e) - VS_STK <= a < spZ (e_regs e)) ->
  ~ (e_parent e <= a < e_parent e + Z.of_nat di + 1) -> rdW (e_W e) (ms_mem ms) a = rdW (e_W e) (e_mem e) a).
{ intros a Ha Hw Hp. rewrite (UN a Ha ltac:(lia)). apply HK; [exact Ha | exact Hw | cbv beta; lia]. }
(* the byte parent[plen] is the NUL: the chunk the store left in the region of atom 40 *)
assert (NUL : rdW (e_W e) (ms_mem ms) (e_parent e + Z.of_nat di) = Some 0).
{ lazymatch type of HS with st_ok _ ?Ex ?ss _ =>
    let r := eval vm_compute in (nth 0 (ss_mem ss) vs5_R) in
    pose proof (st_ok_region_nth Ex ss _ 0 r HS ltac:(vm_compute; reflexivity)) as Rv end.
  lazymatch type of Rv with region_ok _ _ _ (YP09.mkRegion _ _ _ _ _ [?c]) =>
    pose proof (region_ok_chunk SEGS _ _ _ c Rv (or_introl eq_refl)) as Hck end.
  cbn [YP09.r_base base_val] in Hck. repeat (rewrite ew_ewset_other in Hck by lia). rewrite EU40 in Hck.
  pose proof (val_of_chunk_ok SEGS _ _ _ _ _ _ 0 Hck eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as Hval.
  specialize (Hval 0%nat ltac:(cbn; lia)). cbn [ms_mem restrict Z.of_nat] in Hval. rewrite !Z.add_0_r in Hval.
  unfold aview. rewrite Hval. reflexivity. }
pmkst HS.
prreg HS (1%bv : bv 5) P1.
assert (REGK : forall r, acallee_saved r -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs' (Z_to_bv 5 r)).
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hcases : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct Hcases as [-> | Hcases]); try subst r;
  lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
    let n := eval compute in (Z.to_nat k) in
    eapply (vs5_reg_c _ _ _ _ n _ _ HS); [vm_compute; reflexivity | repeat (rewrite ew_ewset_other by lia); apply EV; reflexivity] end. }
assert (M2 : getr (ms_regs ms) 2 = getr regs' 2) by exact (REGK 2 ltac:(unfold acallee_saved; lia)).
assert (M3 : getr (ms_regs ms) 3 = getr regs' 3) by exact (REGK 3 ltac:(unfold acallee_saved; lia)).
assert (M4 : getr (ms_regs ms) 4 = getr regs' 4) by exact (REGK 4 ltac:(unfold acallee_saved; lia)).
assert (M8 : getr (ms_regs ms) 8 = getr regs' 8) by exact (REGK 8 ltac:(unfold acallee_saved; lia)).
assert (P10 : getr (ms_regs ms) 10 = w64 (e_parent e)).
{ eapply (vs5_reg_c _ _ _ _ 9%nat 10%bv _ HS); [vm_compute; reflexivity|].
  repeat (rewrite ew_ewset_other by lia). rewrite (EV 9%nat 9%bv eq_refl). exact G9. }
assert (HspT : spZ (ms_regs ms) = spZ (e_regs e) + -64)
  by (unfold spZ at 1; rewrite M2; change (spZ regs' = spZ (e_regs e) + -64); lia).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
(* the stack above the callee's sp: its window from the journal, the caller's real stack from the entry *)
assert (ASTP : astack_pres (e_ly e) (w_H (e_W e)) (e_mem e) (spZ (e_regs e)) ->
  astack_pres (e_ly e) (w_H (e_W e)) (ms_mem ms) (spZ (e_regs e) + -64)).
{ unfold astack_pres. intros HA a Ha. destruct (Z_lt_le_dec a (spZ (e_regs e))) as [Hb | Hb].
  - apply HJpres. lia.
  - apply GRW. apply HPR. apply HA. lia. }
(* name_ok's premises at the call *)
assert (ROD : arodata_okP SEGS SegInstB.RLO_A SegInstB.RHI_A B (rdW (e_W e) (ms_mem ms))).
{ apply (vs5_rod_kept B _ _ _ _ HROD). intros a Ha. pose proof (vs5_ro_img a Ha) as Ra.
  apply KM; [unfold kImgEnd in Ra; lia | unfold kImgEnd in Ra; lia |].
  intros Hp. destruct (vs5_dst_img _ _ _ _ _ _ _ _ _ a HAR Hstk Hpdst ltac:(lia)) as [_ Hx]. lia. }
assert (Hlp : length (firstn di (e_s e)) = di) by (rewrite length_firstn; lia).
assert (BANDM : forall s, SHADOW_OFF <= s < SHADOW_OFF + 2 ^ 44 -> rdW (e_W e) (ms_mem ms) s = rdW (e_W e) (e_mem e) s).
{ intros s Hs. apply KM; [unfold SHADOW_OFF in Hs; lia | exact (BANDW s Hs) | intros Hp; apply (BANDP s Hs); lia]. }
assert (RAPM : range_addressable (rdW (e_W e) (ms_mem ms)) SHADOW_OFF (e_parent e) 16)
  by (apply (vs5_ra_band _ _ _ _ BANDM); [lia | lia | exact Pra]).
assert (HULM : shadow_hull_vis (rdW (e_W e) (ms_mem ms)) (e_parent e) 16)
  by (apply (vs5_hull_band _ _ _ _ BANDM); [lia | lia | lia | exact (Phull ltac:(lia))]).
assert (PRESM : forall i, 0 <= i < 16 -> apresent (w_H (e_W e)) (ms_mem ms) (e_parent e + i))
  by (intros i Hi; apply GRW; apply PRES; exact Hi).
assert (Hn0 : ~ In 0 (firstn di (e_s e))).
{ intros Hin. apply (proj2 (proj1 Hstr)). rewrite <- (firstn_skipn di (e_s e)). apply in_or_app. left. exact Hin. }
assert (SZM : sa_strz (rdW (e_W e) (ms_mem ms)) (e_parent e) (firstn di (e_s e))).
{ split; [|exact Hn0]. intros i Hi. rewrite length_app, Hlp in Hi. cbn [length] in Hi.
  destruct (Nat.eq_dec i di) as [-> | Hne'].
  - rewrite app_nth2 by lia. rewrite Hlp, Nat.sub_diag. cbn [nth]. exact NUL.
  - rewrite app_nth1 by lia. rewrite nth_firstn. replace (i <? di)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    rewrite UN by lia. apply HCP. lia. }
assert (NPRE : name_ok_pre SEGS B (e_ly e) (e_S e) (e_W e) (ms_mem ms) (ms_regs ms) (e_parent e) (firstn di (e_s e))).
{ unfold name_ok_pre. rewrite Hlp.
  split; [exact Hp0|]. split; [exact SZM|]. split.
  - unfold sa_addr. split; [lia|]. split; [lia|]. split; [unfold amem_range in *; lia|].
    split; [eapply range_addressable_sub; [exact RAPM | lia | lia]|].
    intros _. apply (vs5_hull_sub _ _ 16); [lia | lia | exact HULM].
  - destruct Hpdst as [((cid & pos & Hin & Hcid & H1 & H2) & _) | [((b & m & Hin & H1 & H2) & _) | (H1 & H2 & HP & HAP)]].
    + left. split; [exists cid, pos; repeat split; first [exact Hin | lia] | eapply range_addressable_sub; [exact RAPM | lia | lia]].
    + right; left. split; [exists b, m; repeat split; first [exact Hin | lia] | eapply range_addressable_sub; [exact RAPM | lia | lia]].
    + right; right. split; [rewrite HspT; lia|]. split; [lia|]. split.
      * intros i Hi. apply PRESM. lia.
      * rewrite HspT. apply ASTP. exact HAP. }
(* name_ok's achain at s0 = vid: below the allocator's ceiling for a frame or block, else the caller's real stack *)
assert (HCH : exists ch1, achain (e_ly e) (rdW (e_W e) (ms_mem ms)) (spZ (e_regs e) + -64) (s0Z (ms_regs ms)) ch1).
{ unfold s0Z. rewrite M8, G8. unfold w64. rewrite unsigned_lit_small by lia.
  destruct Hvdst as [((cid & pos & Hin & Hcid & H1 & H2) & _) | [((b & m & Hin & H1 & H2) & _) | (H1 & H2 & HP & HAP)]].
  - exists []. apply achain_low. destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hin) as (F0 & F1 & F2). lia.
  - exists []. apply achain_low. destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & _ & Bc & _ & _ & _ & Bm).
    pose proof (req_size_pos m ltac:(lia)) as [Q1 Q2]. lia.
  - apply achain_any; [apply (astack_rd_of_pres SEGS); apply ASTP; exact HAP | right; right; right; lia]. }
destruct HCH as [ch1 HCH].
(* 0x8a3ac `jal name_ok`: the program call (SIGP: the listing's target is BASE + AF_name_ok) *)
rewrite (SIGP SS_name_ok ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_name_ok) with AF_name_ok by (vm_compute; reflexivity).
eapply SRr_bind.
{ eapply (cl_callS B LAWS (e_W e) (ms_regs ms) (ms_mem ms) _ VS_STK (spZ (e_regs e)) (e_FP e) (e_ly e) (e_S e) (e_W e)
    (e_mem e) (e_md e) [] (e_ly e) (e_S e) _ 0 NAME_OK_STK [] 0 (-64) (getr (ms_regs ms) 1) ch1
    (fun ly2 S2 W2 regs2 mem2 md2 =>
      getr regs2 10 = w64 (seg_spec.b2z (SegModel.name_ok (firstn di (e_s e)))) /\
      sa_kept SEGS (e_W e) (ms_mem ms) W2 mem2 (ms_regs ms) NAME_OK_STK (fun _ => False) /\
      sa_noalloc B (e_ly e) (e_S e) ly2 S2)
    HJ HspT).
  - reflexivity.
  - lia.
  - unfold NAME_OK_STK, ESTACK; lia.
  - unfold NAME_OK_STK, ESTACK; lia.
  - rewrite M3, G3. exact Hgp.
  - rewrite M4, G4. exact Htp.
  - reflexivity.
  - rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite P1. pose proof pa_B_ok as HBo. pose proof pa_base_lo as HBl. rewrite unsigned_lit_small by lia. lia.
  - exact HCH.
  - intros HPRE1. eapply SRr_mono.
    + apply (NAMEOK (e_ly e) (e_S e) (e_W e) (ms_regs ms) (ms_mem ms) _ ch1 (e_parent e) (firstn di (e_s e))
        HPRE1 ROD P10 B11 NPRE).
      unfold EV_name_ok. lia.
    + cbv beta. unfold apost_base.
      intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (A0 & HKP & NA)).
      exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|].
      exact (conj A0 (conj HKP NA)).
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJa & HJia & HPa & (A0a & KCa & NAa)).
rewrite P1.
(* the point K6 *)
assert (R2E : forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regs' (Z_to_bv 5 r))
  by (intros r Hr; rewrite (HPa r Hr); exact (REGK r Hr)).
assert (VR2 : vs_regs e regs2).
{ pose proof HR as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
  unfold vs_regs. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  - unfold spZ. transitivity (bv_unsigned (getr regs' 2)); [f_equal; exact (R2E 2 ltac:(unfold acallee_saved; lia)) | exact Q1].
  - transitivity (getr regs' 3); [exact (R2E 3 ltac:(unfold acallee_saved; lia)) | exact Q2].
  - transitivity (getr regs' 4); [exact (R2E 4 ltac:(unfold acallee_saved; lia)) | exact Q3].
  - transitivity (getr regs' 8); [exact (R2E 8 ltac:(unfold acallee_saved; lia)) | exact Q4].
  - transitivity (getr regs' 9); [exact (R2E 9 ltac:(unfold acallee_saved; lia)) | exact Q5].
  - transitivity (getr regs' 18); [exact (R2E 18 ltac:(unfold acallee_saved; lia)) | exact Q6].
  - transitivity (getr regs' 19); [exact (R2E 19 ltac:(unfold acallee_saved; lia)) | exact Q7].
  - transitivity (getr regs' 22); [exact (R2E 22 ltac:(unfold acallee_saved; lia)) | exact Q8].
  - intros r Hr. rewrite (R2E r) by (unfold acallee_saved; lia). exact (Q9 r Hr). }
assert (R21' : getr regs2 21 = w64 v)
  by (transitivity (getr regs' 21); [exact (R2E 21 ltac:(unfold acallee_saved; lia)) | exact R21]).
assert (SL2 : vs_slots (rdW W2 mem2) (spZ (e_regs e)) (e_regs e)).
{ apply (vs_slots_kept (rdW (e_W e) mem')); [exact HSL|]. intros a Ha.
  rewrite (KCa a ltac:(lia) ltac:(rewrite HspT; unfold NAME_OK_STK, ESTACK; lia) (fun x => x)).
  apply UN; [lia|]. destruct Pplace as [(_ & Hp1) | (Hp1 & _)]; lia. }
assert (SZ2 : sa_strz (rdW W2 mem2) (e_parent e) (firstn di (e_s e))).
{ destruct SZM as [Hzs Hz0]. split; [|exact Hz0]. intros i Hi. rewrite <- (Hzs i Hi).
  rewrite length_app, Hlp in Hi. cbn [length] in Hi.
  apply KCa; [lia | rewrite HspT; unfold NAME_OK_STK, ESTACK; destruct Pplace as [(_ & Hp1) | (Hp1 & _)]; lia | exact (fun x => x)]. }
assert (KP2 : sa_kept SEGS (e_W e) (e_mem e) W2 mem2 (e_regs e) VS_STK (fun a => e_parent e <= a < e_parent e + Z.of_nat di + 1)).
{ intros a Ha Hw He. rewrite (KCa a Ha ltac:(rewrite HspT; unfold NAME_OK_STK, ESTACK; lia) (fun x => x)).
  apply KM; [exact Ha | exact Hw | exact He]. }
assert (VP2 : forall i, 0 <= i < 2 -> apresent (w_H W2) mem2 (e_vid e + i)).
{ intros i Hi. destruct (vs5_dst_img _ _ _ _ _ _ _ _ _ (e_vid e + i) HAR Hstk Hvdst ltac:(lia)) as [Ni _].
  apply (apresent_transfer SEGS (w_H (e_W e)) (w_H W2) (e_mem e) mem2 (e_vid e + i));
    [lia | exact Ni | | apply (vs5_dst_pres _ _ _ _ _ _ _ _ _ HAR Hvdst); lia].
  apply KP2; [lia | destruct Vplace as [(_ & Hv1) | (Hv1 & _)]; lia | cbv beta; unfold sa_disj in Hvdisj; lia]. }
assert (VRA2 : range_addressable (rdW W2 mem2) SHADOW_OFF (e_vid e) 2).
{ pose proof Hvadd as (Va0 & Va63 & Vamr & Vra & Vhull).
  apply (vs5_ra_band (rdW (e_W e) (e_mem e))); [| lia | lia | exact Vra].
  intros s Hs. apply KP2; [unfold SHADOW_OFF in Hs; lia | exact (BANDW s Hs) | cbv beta; intros Hp; apply (BANDP s Hs); lia]. }
exact (HK6 e ly2 S2 W2 regs2 mem2 md2 di v HE HJa VR2 SL2 Hd Hdi0 Hne Hdig Hv Hvr R21' A0a SZ2 NAa VP2 VRA2 KP2).
Qed.
End e.
End f.
End d.
