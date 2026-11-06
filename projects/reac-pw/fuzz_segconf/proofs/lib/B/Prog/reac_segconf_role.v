(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of check_groupa on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACa2.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACb8.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChf.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CheckGroupaWalk.v, with its module paths, module names and numbers changed; 722 of its 780 lines of code are new or changed and 1129 lines of the source are left out. *)
(* the image-B port of lib/A/Prog/reac_segconf_role.v (commit 3e8a17ad1bc0; Qed there at
   3f948d4966a5), ADAPTED: image A's walk over image B's listing (lib/B/Prog, image B's kit and contract copies),
   plus image B's two UBSan alignment traps.
   reac_segconf_role on fuzz_segconf image B (fuzz_segconf.asan-ubsan, entry 0x89be0 = BASE + AF_reac_segconf_role,
   BASE = 0x84dc0, 55 instructions, 32-byte frame, no side-stack frame): the walk that proves its contract
   (lib/B/Prog/reac_segconf_role_c.v), in plugin-hostd/fuzz_command's released B/Prog form: an entry seed, the
   shadow-token executor (paj_run_tok, psrr_branch_tok) over the listing, the call of reac_segconf_find (0x89c00,
   target BASE + AF_reac_segconf_find = 0x89a84) through its contract (PaNoChain.cl_callS_wide), and the return
   through paj_ret_at.

   Image B's code is image A's with other addresses (the shadow-base GOT word 0xa3210 for A's 0xa2a50, the call
   and error-path targets), `addi a0,a1,20` at 0x89c14 for A's `addi a0,a0,20` (the same value: a1 = a0 = p), and
   two UBSan alignment traps, each a branch to the `unimp` at 0x89c80:
     0x89c0c andi a0,a0,3; 0x89c10 bnez a0 -> unimp 0x89c80 (alignment of the entry p that find returns): not
       taken. The token run decides it from atom 44's fact (mkAF 0 (2 ^ 47 - 24) 2, alignment 2 ^ 2, added after
       the call from Hp4: p = c + 356 i with c 16-aligned by query_pre's al_blocks, YP0m.s_and_ptr gives
       andi (SOff 44 0) 3 = SLit 0).
     0x89c38 andi a2,s0,3; 0x89c3c bnez a2 -> unimp 0x89c80 (alignment of out): not taken. Reached only when
       out <> 0 (the beqz s0 at 0x89c34 goes first), where role_pre gives out mod 4 = 0: the token run decides it
       from atom 12's fact (mkAF 0 (2 ^ 47 - 4) 2) when out is apart from the entry's fields, and from atom 44's
       fact when out = p + 16 or p + 20 (s0 rebased to SOff 44 16 / SOff 44 20: Z.land 16 3 = Z.land 20 3 = 0).
   The `unimp` at 0x89c80 is reached by these two branches only (it follows the `ret` at 0x89c7c).

   Atoms: 0..31 the entry registers, 32 the shadow base SB, 33 the role of the entry find returns (0 when it
   returns NULL). Regions at the entry: the frame, the GOT word of the shadow-base cell (A_OBJ 0 = 0xa3210 in
   image B, the .got word holding the cell) and the cell (A_OBJ 12 = 0xac7b8 in image B). After the call (atoms
   40..55 the clobbered registers, 44 = a0 = find's result p): the entry fields role (p + 0x10) and role_set
   (p + 0x14) as a region based at p, and the out cell when out <> 0. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaSB PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaNoChain.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegObj SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_segconf_find_c reac_segconf_role_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_segconf_role_lem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* Image B's pure numbers, image B's instance file's (lib/B/Prog/SegInstB.v), the twin of the SegInstA names image
   A's walk takes, under the names the proofs below use:
   - RLO_B / RHI_B := SegInstB.RLO_A / RHI_A, lib/B/Prog/SegGlob.v SEG_RLO / SEG_RHI = 0xa1c60 / 0xa3f08, image B's
     .data.rel.ro start and .got end.
   - STK_reac_segconf_find_B := SegInstB.STK_reac_segconf_find: image B's reac_segconf_find has a 64-byte frame
     (0x89a84 `addi sp,sp,-64`, released at 0x89b5c) and calls the strcmp wrapper (jal 0x89b18, 2 * ESTACK) at that
     sp: 64 + 2 * ESTACK = 8256.
   - STK_reac_segconf_role_B := SegInstB.STK_reac_segconf_role: this function's 32-byte frame (0x89be0
     `addi sp,sp,-32`, released at 0x89c78) and find's window at that sp (jal 0x89c00): 32 + 8256 = 8288. *)
#[local] Notation RLO_B := SegInstB.RLO_A (only parsing).
#[local] Notation RHI_B := SegInstB.RHI_A (only parsing).
#[local] Notation STK_reac_segconf_find_B := SegInstB.STK_reac_segconf_find (only parsing).
#[local] Notation STK_reac_segconf_role_B := SegInstB.STK_reac_segconf_role (only parsing).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the entry seed *)
Definition rol_Bx : sv := SOff 32 0.
Definition rol_regions : smem := [stack_region 32; got_regionP; bcell_regionP 32].
Definition rol_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0)] [] [].
Definition ss_rol : sstate := mkSS AF_reac_segconf_role sr_atoms rol_regions None rol_facts.
Definition rol_extra (v : Z) : list word := [Z_to_bv 64 SB; Z_to_bv 64 v].
Definition EC (regs : bvmap 5 word) (v : Z) : env := Eimg (Ereg regs (rol_extra v)).
Section e.
Variable B : asyms.
(* the callee's contract, at find's entry and stack *)
Hypothesis FIND : forall fx0 : YK11.FPState,
  @reac_segconf_find_contract fx0 rc SK SEGS B (BASE + AF_reac_segconf_find) SegInstB.STK_reac_segconf_find
    SegInstB.RLO_A SegInstB.RHI_A.
(* the record: the GOT word and the shadow-base cell are the listing's objects 0 and 12 *)
Hypothesis TL : PALib B.
(* every program function's call target against the listing's base (SegObj.seg_sig_prog; the instance gives it) *)
Hypothesis SIGP : seg_sig_prog (PI := PI).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_seg) (PI := PI).
(* the reader at a is the reader at a mod 2 ^ 64 *)
Lemma rol_aview_mod : forall H (m : word -> option byte) a, aview SEGS H m a = aview SEGS H m (a mod 2 ^ 64).
Proof using.
intros H m a. unfold aview, mbyte.
replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma rol_rd_some : forall H (m : word -> option byte) a, aview SEGS H m a <> None ->
exists v, aview SEGS H m a = Some v /\ 0 <= v.
Proof using.
intros H m a Hn. unfold aview in *. destruct (mbyte SEGS (mrestrict H m) a) as [b|]; cbn [option_map] in *;
[|exfalso; exact (Hn eq_refl)].
exists (bv_unsigned b). split; [reflexivity | exact (proj1 (bv_unsigned_in_range _ b))].
Qed.
(* the image's read-only view survives a run that writes only [lo, hi), a window above the image whose bytes are
   mapped (so none of them is a read-only byte) *)
Lemma rol_aro_frame : forall (W : world SEGS) (mem m : word -> option byte) lo hi,
arodata_okP SEGS RLO_B RHI_B B (rdW W mem) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> rdW W m a = rdW W mem a) ->
(forall a, lo <= a < hi -> rdW W mem a <> None) ->
kImgEnd <= lo -> hi <= 2 ^ 64 ->
arodata_okP SEGS RLO_B RHI_B B (rdW W m).
Proof using.
intros W mem m lo hi H Hk Hp Hlo Hhi a Hro Ho He.
pose proof (H a Hro Ho He) as Ha.
assert (Ea : Z_to_bv 64 a = Z_to_bv 64 (a mod 2 ^ 64)).
{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_mod by lia. reflexivity. }
rewrite rol_aview_mod in Ha |- *. rewrite Ea in Ha |- *.
pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ra.
set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' lo) as [Hl | Hl]; [rewrite Hk by lia; exact Ha|].
destruct (Z_lt_le_dec a' hi) as [Hh | Hh]; [|rewrite Hk by lia; exact Ha].
exfalso. apply (Hp a' ltac:(lia)). rewrite Ha.
destruct (seg_rom SEGS (Z_to_bv 64 a')) as [b|] eqn:Eb; [|reflexivity].
exfalso. pose proof (seg_rom_in_img SEGS a' Ra ltac:(rewrite Eb; discriminate)) as Himg.
pose proof (pa_img_range a' Himg). lia.
Qed.
(* every place an object of the program lies is below the allocator's ceiling *)
Lemma rol_loc_low : forall ly S W mem md q n, AR SEGS B ly S W mem md -> sa_loc SEGS B ly S q n -> 0 < n ->
4096 <= q /\ q + n <= alloc_ceiling.
Proof using.
intros ly S W mem md q n HAR [(b & m & Hin & Hb1 & Hb2) | [(cid & pos & Hin & Hc & Hf1 & Hf2) | Himg]] Hn.
- destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & H4 & Hce & _ & _ & _ & Hm).
  pose proof (req_size_pos m ltac:(lia)) as [_ Hr]. lia.
- destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (H4 & Hce & _). lia.
- destruct (Himg q ltac:(lia)) as (I1 & _ & _). destruct (Himg (q + n - 1) ltac:(lia)) as (I2 & _ & _).
  pose proof (pa_img_range q I1). pose proof (pa_img_range _ I2). pose proof asan_consts as (C1 & _).
  unfold kImgEnd in *. lia.
Qed.
(* the shadow facts of a range below the ceiling only read below lo *)
Lemma rol_addr_agree : forall (rd rd' : reader) q n lo,
(forall a, 0 <= a < lo -> rd' a = rd a) -> 0 <= q -> q + n <= alloc_ceiling -> alloc_ceiling + 16 <= lo ->
sa_addr rd q n -> sa_addr rd' q n.
Proof using.
intros rd rd' q n lo Hk Hq Hqn Hlo (A0 & A1 & A2 & A3 & A4).
pose proof asan_consts as (C1 & _).
assert (HAC : alloc_ceiling / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
split; [exact A0|]. split; [exact A1|]. split; [exact A2|]. split.
- intros x Hx. destruct (A3 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok]. rewrite Hk; [exact Hs|].
  assert (x / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
  assert (0 <= x / 8) by (apply Z.div_pos; lia).
  unfold shadow_of_addr, SHADOW_OFF. lia.
- intros Hn s Hs. rewrite Hk; [exact (A4 Hn s Hs)|].
  unfold shadow_addr, SHADOW_OFF in Hs.
  assert ((q + n - 1) / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
  assert (0 <= q / 8) by (apply Z.div_pos; lia).
  assert ((2147450880 + (q + n - 1) / 8) / 8 * 8 <= 2147450880 + (q + n - 1) / 8)
    by (rewrite Z.mul_comm; apply Z.mul_div_le; lia).
  assert (0 <= (2147450880 + q / 8) / 8 * 8) by (apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia).
  lia.
Qed.
(* query_pre survives a change of the reader above lo *)
Lemma rol_qp_agree : forall ly S W mem md (rd' : reader) c name rcs nm lo,
AR SEGS B ly S W mem md ->
query_pre SEGS B ly S (rdW W mem) c name rcs nm ->
(forall a, 0 <= a < lo -> rd' a = rdW W mem a) -> alloc_ceiling + 16 <= lo ->
query_pre SEGS B ly S rd' c name rcs nm.
Proof using.
intros ly S W mem md rd' c name rcs nm lo HAR (Hc0 & Hc16 & (bs & HB & HE) & HCH & HCA & Hn0 & HNS & HNL & HNA & HN32)
  Hk Hlo.
pose proof asan_consts as (C1 & _).
destruct (rol_loc_low ly S W mem md c seg_spec.SEG_C_SIZE HAR (or_introl HCH) ltac:(unfold seg_spec.SEG_C_SIZE; lia))
  as [Lc1 Lc2].
destruct (rol_loc_low ly S W mem md name (Z.of_nat (length nm) + 1) HAR HNL ltac:(lia)) as [Ln1 Ln2].
pose proof HE as (HL & _). unfold seg_spec.SEG_C_SIZE in HL, Lc2.
refine (conj Hc0 (conj Hc16 (conj _ (conj HCH (conj _ (conj Hn0 (conj _ (conj HNL (conj _ HN32))))))))).
- exists bs. split; [|exact HE]. intros i Hi. rewrite Hk; [exact (HB i Hi)|]. lia.
- exact (rol_addr_agree _ _ c seg_spec.SEG_C_SIZE lo Hk ltac:(lia) ltac:(unfold seg_spec.SEG_C_SIZE; lia) Hlo HCA).
- destruct HNS as ((HZ & HNZ) & HT). split; [split; [|exact HNZ] |].
  + intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. rewrite Hk; [exact (HZ i ltac:(rewrite length_app; cbn [length]; lia))|]. lia.
  + intros x Hx. pose proof (Z.mod_pos_bound (name + Z.of_nat (length nm)) 8 ltac:(lia)). rewrite Hk; [exact (HT x Hx)|]. lia.
- exact (rol_addr_agree _ _ name (Z.of_nat (length nm) + 1) lo Hk ltac:(lia) Ln2 Hlo HNA).
Qed.


Lemma rol_entry : forall ly S W (regs : bvmap 5 word) mem md ch v,
afn_pre SEGS B STK_reac_segconf_role_B ly S W regs mem md ch ->
st_ok_pi SEGS VAL (EC regs v) ss_rol
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_segconf_role)) mem (seg_rom SEGS)))
/\ sh_ok SEGS rol_Bx [] (EC regs v) (mrestrict (w_H W) mem).
Proof using TL.
intros ly S W regs mem md ch v HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : STK_reac_segconf_role_B = 8288) by reflexivity.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_obj_img 0 ltac:(lia)) as HO0. pose proof (pa_obj_img 12 ltac:(lia)) as HO12.
unfold kImgEnd in HO0, HO12.
pose proof (pal_got_cell B TL) as HGC.
pose proof (pa_val_range (A_OBJ 0)) as R0. pose proof (pa_val_range (A_OBJ 12)) as R12.
rewrite restrict_mkst_fx.
set (E := EC regs v).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (rol_extra v)) n)
  by (intros n Hn; subst E; unfold EC; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (subst E; unfold EC; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (subst E; unfold EC; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n w, ew E n = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some n) = w).
{ intros n w Hn Hw. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hw. }
assert (B0 : base_val E (Some (A_OBJ 0)) = VAL (A_OBJ 0)) by (apply VB; [exact EO0 | lia]).
assert (B12 : base_val E (Some (A_OBJ 12)) = VAL (A_OBJ 12)) by (apply VB; [exact EO12 | lia]).
split.
- unfold ss_rol. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold rol_regions, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite WS. lia.
    * rewrite B0. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
        [cbn [sv_denot]; rewrite EO12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite B12. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SHADOW_OFF);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  + apply pairwise_disjoint_of_extents.
    unfold rol_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B0, B12. cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite WS in Hslo.
    clear - Hslo Hceil C1 HO0 HO12 HGC. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [rol_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    rewrite WS in Hslo. unfold SB. clear - Hal16 Hslo Hshi H47 C1 Hceil. repeat split; first [lia | reflexivity].
- unfold sh_ok. constructor.
Qed.

(* the two fields of the found entry p = c + 356 i as a region based at find's result (atom 44): role at p + 0x10 (the
   entry's role, atom 33) and role_set at p + 0x14 (the literal fl, 0 or 1) *)
Definition R_SEG (fl : Z) : YP09.region :=
  YP09.mkRegion (Some 44%nat) 16 24 0 0 [YP09.mkChunk 16 (CVal 4 (SOff 33 0)); YP09.mkChunk 20 (CVal 4 (SLit fl))].
(* the same two fields when the out cell is one of them (out = p + wlo): the store at 0x89c68 writes [wlo, wlo + 4) *)
Definition R_SEGW (fl wlo : Z) : YP09.region :=
  YP09.mkRegion (Some 44%nat) 16 24 wlo (wlo + 4) [YP09.mkChunk 16 (CVal 4 (SOff 33 0)); YP09.mkChunk 20 (CVal 4 (SLit fl))].
(* the out cell, when it is apart from the entry's two fields: written by the store at 0x89c68 *)
Definition R_OUT : YP09.region := YP09.mkRegion (Some 12%nat) 0 4 0 4 [].
Lemma rol_val_mem : forall H (mem : word -> option byte) a n v,
sa_val (aview SEGS H mem) a n v -> val_mem SEGS (mrestrict H mem) a n v.
Proof using.
intros H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H mem) (a + Z.of_nat k)) as [bb|] eqn:Hb; [|discriminate].
cbn in Hv. injection Hv as Hv. rewrite <- (Z_to_bv_bv_unsigned _ bb) at 1. do 2 f_equal. exact Hv.
Qed.
(* the shadow entry of the found entry's two fields: they lie in a live block, addressable *)
Lemma rol_shent_seg : forall E (W' : world SEGS) mem' p b len,
ew E 32 = Z_to_bv 64 SB -> ew E 44 = Z_to_bv 64 p ->
range_addressable (rdW W' mem') SHADOW_OFF (p + 16) 8 -> in_app b len -> b <= p -> p + 24 <= b + len ->
shent_ok SEGS rol_Bx E (mrestrict (w_H W') mem') (mkSHE 44 16 24).
Proof using.
intros E W' mem' p b len H32 H44 RA Happ Hb1 Hb2.
pose proof asan_consts as (C1 & _).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
apply (shent_ok_of_range SEGS (w_H W') mem' E rol_Bx 44 (p + 16) 8 p 16 24 RA).
- unfold rol_Bx. rewrite (U_atom E 32 SB H32) by (unfold SB; lia). reflexivity.
- apply U_atom; [exact H44 | lia].
- lia.
- lia.
- intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.
Ltac rol_seg_ok A44 A33 RD16 RD20 Rrole Hv :=
  unfold region_ok, R_SEG;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
  rewrite A44, unsigned_lit_small by lia;
  split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
  apply Forall_cons;
  [ eapply (chunk_ok_val SEGS _ _ _ 16 4 (SOff 33 0) _);
      [ cbn [sv_denot]; rewrite A33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | rewrite Hv; change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | zside | exact (rol_val_mem _ _ _ _ _ RD16) ]
  | apply Forall_cons;
    [ eapply (chunk_ok_val SEGS _ _ _ 20 4 (SLit _) _);
        [ reflexivity | zside | zside | exact (rol_val_mem _ _ _ _ _ RD20) ]
    | apply Forall_nil ] ].
Ltac rol_segw_ok A44 A33 RD16 RD20 Rrole Hv OPd :=
  unfold region_ok, R_SEGW;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
  rewrite A44, unsigned_lit_small by lia;
  split; [lia|]; split; [lia|];
  split; [let o := fresh "o" in let Ho := fresh "Ho" in intros o Ho; apply (apresent_writable SEGS); apply OPd; lia|];
  apply Forall_cons;
  [ eapply (chunk_ok_val SEGS _ _ _ 16 4 (SOff 33 0) _);
      [ cbn [sv_denot]; rewrite A33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | rewrite Hv; change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | zside | exact (rol_val_mem _ _ _ _ _ RD16) ]
  | apply Forall_cons;
    [ eapply (chunk_ok_val SEGS _ _ _ 20 4 (SLit _) _);
        [ reflexivity | zside | zside | exact (rol_val_mem _ _ _ _ _ RD20) ]
    | apply Forall_nil ] ].
Ltac rol_seg_disj A44 Usp1 :=
  lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
  cbn [all_disjoint]; unfold extent_disjoint; try unfold R_SEG; try unfold R_SEGW; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  rewrite A44, Usp1, unsigned_lit_small by lia; split; [lia | exact I].

Lemma rol_beq0 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (v =? 0).
Proof using. intros E n v Hn Hv. rewrite branch_eq_U, (U_atom E n v Hn Hv), U_SLit. reflexivity. Qed.
(* the role as the store writes it back: lw sign-extends the entry's 4 bytes, and the role is below 2 ^ 31 *)
Lemma rol_sext_role : forall E v, ew E 33 = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 ->
  sv_denot E (SExt true 32 (SOff 33 0)) = Z_to_bv 64 v.
Proof using.
intros E v H Hv. rewrite denot_lit_U. f_equal. rewrite U_SExt, (U_atom E 33 v H) by lia.
change (2 ^ Z.of_N 32) with 4294967296. rewrite (Z.mod_small v 4294967296) by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296.
change (4294967296 / 2) with 2147483648.
rewrite (Z.mod_small (v + 2147483648) 4294967296) by lia. replace (v + 2147483648 - 2147483648) with v by lia.
apply zcanon_id. unfold M64. lia.
Qed.
Lemma rol_sa_of_val : forall H (mem : word -> option byte) a n v,
  val_mem SEGS (mrestrict H mem) a n v -> sa_val (aview SEGS H mem) a n v.
Proof using.
intros H mem a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia.
Qed.
Lemma rol_ew_bv : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E n) = v.
Proof using. intros E n v H Hv. rewrite H. apply unsigned_lit_small. exact Hv. Qed.
Ltac rol_agree32 HAE1 :=
  lazymatch goal with |- env_agree 32 _ _ =>
    let HA1 := fresh "HA1" in let HD1 := fresh "HD1" in
    destruct HAE1 as [HA1 HD1]; split;
    [ let n := fresh "n" in let Hn := fresh "Hn" in
      intros n Hn; cbn [extK]; rewrite ?ew_ewset_other by lia; apply HA1; lia
    | cbn [extK]; rewrite ?ed_ewset; exact HD1 ] end.
(* an atom's value in an environment the token runs extended above K *)
Ltac rol_ew A := cbn [extK]; rewrite ?ew_ewset_other by lia; exact A.
(* the write windows of a run: the frame, and the out cell when its region is in the state *)
Ltac rol_win Usp1 A12 A44 :=
  let b0 := fresh "b0" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
  let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
  intros b0 wlo whi a Hin Hrr; vm_compute in Hin;
  repeat (destruct Hin as [Hq | Hin];
    [injection Hq as <- <- <-; cbn [base_val] in Hrr; revert Hrr; cbn [extK]; rewrite ?ew_ewset_other by lia;
     rewrite ?Usp1, ?A12, ?A44, ?unsigned_lit_small by lia; intros Hrr; cbv beta; lia |]);
  destruct Hin.
(* the return's first three conjuncts of apost_base: ra, the journal, the callee-saved registers *)
Ltac rol_head HS HJ R1 HAG F1 Hra HAE1 regs v :=
  split; [cbn [ms_regs]; rewrite R1; rewrite ?ew_ewset_other by lia; rewrite (proj1 HAG 1%nat) by lia;
          rewrite F1, Hra; reflexivity|];
  split; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ|];
  split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (rol_extra v) HS); [rol_agree32 HAE1 | vm_compute; reflexivity]|].
(* a run's writes when the head region's write window is the out cell (the call's footprint), based at atom n = b *)
Ltac rol_awr_at OAWR nn A Usp1 bb :=
  lazymatch goal with |- awr_ok ?sg ?bb ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?fr ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb E rs' stk sp0 fp b0 bc fr ly own) end;
  eapply awr_ok_cons_gen with (n := nn) (b := bb);
  [ reflexivity
  | cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite A; apply unsigned_lit_small; lia
  | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply OAWR; lia
  | awr_ok_tac; rol_ew Usp1 ].
Theorem reac_segconf_role_walk :
  reac_segconf_role_contract SEGS B (BASE + AF_reac_segconf_role) SegInstB.STK_reac_segconf_role SegInstB.RLO_A
    SegInstB.RHI_A.
Proof using FIND TL SIGP.
unfold reac_segconf_role_contract.
intros ly S W regs mem md ch c name out rcs nm HPRE HROD H10 Rc H11 Rn H12 Ro [HQP HOUT] Hev.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : STK_reac_segconf_role_B = 8288) by reflexivity.
set (v := match r_find rcs nm with Some i => rs_role (r_seg rcs i) | None => 0 end).
destruct (rol_entry ly S W regs mem md ch v HPRE) as [HS SHOK].
pose proof (ajournal_init SEGS B STK_reac_segconf_role_B (role_W out (r_role rcs nm)) ly S W regs mem md ch HPRE) as HJ.
remember (EC regs v) as E0 eqn:HE0.
assert (HEI : img_env VAL A_LIM E0) by (rewrite HE0; unfold EC; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E0 n = ew (Ereg regs (rol_extra v)) n)
  by (intros n Hn; rewrite HE0; unfold EC; apply Eimg_low; exact Hn).
assert (F1 : ew E0 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (F3 : ew E0 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (F4 : ew E0 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (F2 : ew E0 2 = Z_to_bv 64 (spZ regs))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (F10 : ew E0 10 = Z_to_bv 64 c) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (F11 : ew E0 11 = Z_to_bv 64 name) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (F12 : ew E0 12 = Z_to_bv 64 out) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (F32 : ew E0 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (F33 : ew E0 33 = Z_to_bv 64 v) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (HAE : env_agree 32 (Ereg regs (rol_extra v)) E0)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | rewrite HE0; reflexivity]).
assert (Usp0 : bv_unsigned (ew E0 2) = spZ regs) by (rewrite F2; apply unsigned_lit_small; unfold spZ; apply bv_unsigned_in_range).
clear HE0 EL.
unfold cfg_at. change (w64 (BASE + AF_reac_segconf_role)) with (Z_to_bv 64 (BASE + AF_reac_segconf_role)).
(* 0x89be0 .. 0x89c00: the frame, the saves of ra, s0, s1, s0 := out, the shadow base through the GOT word, and the
   call of reac_segconf_find *)
paj_run_tok RUN HS HJ SHOK Bspan; [awr_ok_tac; exact Usp0 |].
(* the run wrote the frame only *)
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - 32 <= a < spZ regs) HFr
  ltac:(intros b wlo whi a Hin' Hrr; vm_compute in Hin';
        repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp0 in Hrr; lia|]);
        destruct Hin')) as UN1.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
assert (Qsp : spZ (ms_regs ms) = spZ regs + -32)
  by (unfold spZ at 1; rewrite Q2, Usp0; rewrite unsigned_lit_small by lia; lia).
pmkst HS.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
(* find's premises at the call: the read-only view, query_pre and the frame chain at s0 = out, from the entry's,
   since the run wrote only the frame [sp - 32, sp) *)
assert (HROc : arodata_okP SEGS RLO_B RHI_B B (rdW W (ms_mem ms))).
{ apply (rol_aro_frame W mem (ms_mem ms) (spZ regs - 32) (spZ regs) HROD).
  - intros a Ha Hn. exact (UN1 a Ha Hn).
  - intros a Ha. apply (aview_some_of_apresent SEGS). apply Hpres. rewrite WS. lia.
  - pose proof asan_consts as (C1' & _). unfold kImgEnd. rewrite WS in Hslo. lia.
  - lia. }
assert (HQPc : query_pre SEGS B ly S (rdW W (ms_mem ms)) c name rcs nm).
{ apply (rol_qp_agree ly S W mem md _ c name rcs nm (spZ regs - 32) HAR HQP); [|rewrite WS in Hslo; lia].
  intros a Ha. apply UN1; lia. }
assert (HCH1 : exists ch1, achain ly (rdW W (ms_mem ms)) (spZ regs + -32) (s0Z (ms_regs ms)) ch1).
{ unfold s0Z. rewrite Q8, F12, unsigned_lit_small by lia.
  destruct HOUT as [-> | (Ho4 & HD)]; [exists []; apply achain_low; lia|].
  destruct HD as [((cid & pos & Hin & Hc & Hf1 & Hf2) & _) | [((b & m & Hin & Hb1 & Hb2) & _) | (Hsp & Hot & Hpr & HAP)]].
  - destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (_ & Hce & _).
    exists []. apply achain_low. lia.
  - destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & _ & Hce & _ & _ & _ & Hm).
    pose proof (req_size_pos m ltac:(lia)) as [_ Hr]. exists []. apply achain_low. lia.
  - apply achain_any; [|right; right; right; lia].
    intros a Ha. apply rol_rd_some.
    destruct (Z_lt_le_dec a (spZ regs)) as [Hlt | Hge].
    + apply (aview_some_of_apresent SEGS). apply HJpres. rewrite WS. lia.
    + rewrite UN1 by lia. apply (aview_some_of_apresent SEGS). apply HAP. lia. }
destruct HCH1 as (ch1 & Hch1).
pose proof pa_B_ok as HBo.
(* 0x89c00: jal reac_segconf_find, through find's contract; the return address 0x89c04 = BASE + 0x4e44 *)
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W (ms_regs ms) (ms_mem ms) _ STK_reac_segconf_role_B (spZ regs) (role_W out (r_role rcs nm))
    ly S W mem md [] ly S _ 0 STK_reac_segconf_find_B [] EV_reac_segconf_find (-32) (Z_to_bv 64 (BASE + 20036)) ch1
    (fun ly' S' W' regs' mem' md' => getr regs' 10 = w64 (seg_spec.find_ptr c rcs nm) /\
       sa_kept SEGS W (ms_mem ms) W' mem' (ms_regs ms) STK_reac_segconf_find_B (fun _ => False) /\ sa_noalloc B ly S ly' S') HJ).
  - exact Qsp.
  - reflexivity.
  - lia.
  - unfold STK_reac_segconf_find_B, ESTACK. lia.
  - rewrite WS. unfold STK_reac_segconf_find_B, ESTACK. lia.
  - rewrite Q3, F3. exact Hgp.
  - rewrite Q4, F4. exact Htp.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - exact Hch1.
  - intros HPRE1.
    rewrite (SIGP SS_reac_segconf_find) by (unfold seg_prog_syms; cbn [In]; repeat first [left; reflexivity | right]).
    change (seg_af SS_reac_segconf_find) with AF_reac_segconf_find.
    eapply SRr_mono.
    { apply (FIND fx ly S W (ms_regs ms) (ms_mem ms) _ ch1 c name rcs nm HPRE1 HROc);
        [rewrite Q10, F10; reflexivity | exact Rc | rewrite Q11, F11; reflexivity | exact Rn | exact HQPc | exact Hev]. }
    cbv beta. intros W' c' _ (ly' & S' & regs' & mem' & md' & -> & HJ' & HP' & HK').
    exists ly', S', regs', mem', md'. rewrite Q1. split; [reflexivity|]. split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - intros a (r & Hr & _). destruct Hr.
  - intros ? ? ? ? ? ? _ a (r & Hr & _). destruct Hr. }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & (Ha03 & HKF & HNA3)).
(* the reader after the call is the entry's outside this call's stack window *)
assert (UN3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_reac_segconf_role_B <= a < spZ regs) -> rdW W3 mem3 a = rdW W mem a).
{ intros a Ha Hn. rewrite WS in Hn. rewrite (HKF a Ha); [| rewrite Qsp; unfold STK_reac_segconf_find_B, ESTACK; lia | tauto].
  apply UN1; [exact Ha | cbv beta; lia]. }
(* back at 0x89c04: the frame region is kept (find wrote below sp - 32 only) *)
jafter_call_keep_pi HS 40%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0%nat] HS2.
lazymatch type of HS2 with ?P -> _ => assert (HQ : P); [| specialize (HS2 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  eapply region_kept_stack_sub; [exact HJc3 | exact HJ3 | exact Usp0 | lia | rewrite WS; lia | lia | lia | lia |].
  intros a Ha (r & Hr & _). destruct Hr. }
rewrite <- restrict_mkst_fx in HS2. clear HS SHOK HFr HG. rename HF into HF1.
assert (HEI1 : img_env VAL A_LIM (havoc E0 40 (map (getr regs3) CLOB)))
  by (apply img_env_havoc; [exact HEI | apply Nat.leb_le; vm_compute; reflexivity]).
assert (HAG : env_agree 40 E0 (havoc E0 40 (map (getr regs3) CLOB)))
  by (apply env_agree_havoc_ge; [lia | split; [intros; reflexivity | reflexivity]]).
assert (E44 : ew (havoc E0 40 (map (getr regs3) CLOB)) 44 = getr regs3 10)
  by (rewrite (ew_havoc_new E0 40 _ 4 (Z_to_bv 64 0)) by (rewrite length_map; cbn; lia); reflexivity).
remember (havoc E0 40 (map (getr regs3) CLOB)) as E1 eqn:HE1. clear HE1.
assert (HAE1 : env_agree 32 (Ereg regs (rol_extra v)) E1).
{ destruct HAE as [HA1 HD1]. destruct HAG as [HA2 HD2].
  split; [intros n Hn; rewrite HA2 by lia; apply HA1; lia | congruence]. }
assert (Usp1 : bv_unsigned (ew E1 2) = spZ regs) by (rewrite (proj1 HAG 2%nat) by lia; exact Usp0).
unfold YK0s.ret_ok in Hra.
assert (Hv : v = match r_find rcs nm with Some i => rs_role (r_seg rcs i) | None => 0 end) by reflexivity.
clearbody v.
unfold seg_spec.find_ptr, seg_spec.rseg_addr, seg_spec.RSEG_SIZE in Ha03.
destruct (r_find rcs nm) as [i|] eqn:RF.
2:{ (* find returned NULL: a0 = 0, the branch at 0x89c04 to the epilogue, and the return of 0 *)
  assert (RR : r_role rcs nm = None) by (unfold r_role; rewrite RF; reflexivity).
  rewrite RR in *. cbn [role_W] in *.
  pose proof (st_ok_pi_set_reg _ _ _ (10%bv : bv 5) (SLit 0) HS2
    ltac:(intros Hz; apply (f_equal bv_unsigned) in Hz; discriminate Hz)
    ltac:(cbn [ms_regs restrict mkst sv_denot]; rewrite Ha03; reflexivity)) as HS3.
  clear HS2.
  assert (SHOK3 : sh_ok SEGS rol_Bx [] E1 (mrestrict (w_H W3) mem3)) by constructor.
  paj_run_tok RUN HS3 HJ3 SHOK3 Bspan; [awr_ok_tac; exact Usp1 |].
  eapply (RET W3 _ _ _ _ _ HS3 eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'.
  prreg HS3 (1%bv : bv 5) R1. prreg HS3 (10%bv : bv 5) R10.
  (* the return of 0: the run wrote the frame only *)
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - 32 <= a < spZ regs) HFr
    ltac:(intros b wlo whi a Hin' Hrr; vm_compute in Hin';
          repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp1 in Hrr; lia|]);
          destruct Hin')) as UN4.
  unfold apost_base. eexists _, _, _, _, _.
  split; [cbn [ms_regs]; rewrite R1, (proj1 HAG 1%nat) by lia; rewrite F1, Hra; reflexivity|].
  split; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ3|].
  split; [eapply (aregs_preserved_of_st_ok SEGS _ E1 _ _ regs (rol_extra v) HS3); [exact HAE1 | vm_compute; reflexivity]|].
  split; [cbn [ms_regs]; rewrite R10; reflexivity|].
  split; [exact I|].
  split; [|exact HNA3].
  intros a Ha Hn _. rewrite WS in Hn. rewrite UN4 by (first [exact Ha | cbv beta; lia]). apply UN3; [exact Ha | rewrite WS; lia]. }
(* find returned p = c + 356 i, the entry i of the table *)
cbn beta iota in Hv.
pose proof HQP as (Hc0 & Hc16 & HRC & HCH & HCA & _).
destruct (rol_find_bound _ c rcs nm i HRC RF) as [Hi Hi32].
destruct (rol_rd_role (rdW W mem) c rcs i HRC Hi) as (Rrole & HROLE).
pose proof (rol_rd_role_set (rdW W mem) c rcs i HRC Hi) as HRSET.
unfold seg_spec.RS_ROLE in HROLE. unfold seg_spec.RS_ROLE_SET in HRSET.
destruct HCH as (b & m & Hbin & Hb1 & Hb2). unfold seg_spec.SEG_C_SIZE in Hb2.
destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hbin) as (Hb16 & Hb4096 & Hbceil & Hbapp & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hrm].
assert (Hp4 : (c + 356 * Z.of_nat i) mod 4 = 0).
{ replace (c + 356 * Z.of_nat i) with ((4 * (c / 16) + 89 * Z.of_nat i) * 4)
    by (pose proof (Z.div_mod c 16 ltac:(lia)); lia).
  apply Z.mod_mul. lia. }
set (p := c + 356 * Z.of_nat i) in *.
assert (Hp : c <= p /\ p + 356 <= c + 16616) by (subst p; lia).
pose proof (HNA3) as (HPerm & Hly3 & _).
assert (Hbin3 : In (b, m) (ablocks B ly3 S3)) by (apply (Permutation_in _ (Permutation_sym HPerm)); exact Hbin).
pose proof (proj1 HJ3) as HAR3.
(* the two fields of the entry, read through the reader after the call *)
assert (RD16 : sa_val (rdW W3 mem3) (p + 16) 4 v).
{ subst v. intros k Hk. rewrite UN3; [exact (HROLE k Hk) | lia | rewrite WS; lia]. }
assert (RD20 : sa_val (rdW W3 mem3) (p + 20) 4 (if rs_role_set (r_seg rcs i) then 1 else 0)).
{ intros k Hk. rewrite UN3; [exact (HRSET k Hk) | lia | rewrite WS; lia]. }
(* the entry's 8 bytes are addressable at the call's return: they lie in the live block of c *)
assert (RA16 : range_addressable (rdW W3 mem3) SHADOW_OFF (p + 16) 8)
  by (apply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 mem3 md3 b m); [exact HAR3 | exact Hbin3 | lia | lia]).
assert (A12 : ew E1 12 = Z_to_bv 64 out) by (rewrite (proj1 HAG 12%nat) by lia; exact F12).
assert (A32 : ew E1 32 = Z_to_bv 64 SB) by (rewrite (proj1 HAG 32%nat) by lia; exact F32).
assert (A33 : ew E1 33 = Z_to_bv 64 v) by (rewrite (proj1 HAG 33%nat) by lia; exact F33).
assert (A44 : ew E1 44 = Z_to_bv 64 p) by (rewrite E44, Ha03; reflexivity).
destruct (rs_role_set (r_seg rcs i)) eqn:RSS.
2:{ (* role_set = 0: the load at 0x89c28 gives 0, the branch at 0x89c2c to the epilogue, and the return of 0 *)
  assert (RR : r_role rcs nm = None) by (unfold r_role; rewrite RF, RSS; reflexivity).
  rewrite RR in *. cbn [role_W] in *.
  pose proof (st_ok_pi_add_fact _ _ _ 44%nat (mkAF 0 (2 ^ 47 - 24) 2) HS2
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite A44, unsigned_lit_small by lia; change (2 ^ 2) with 4; lia))
    as HS4.
  clear HS2.
  pose proof (st_ok_pi_add_region _ _ _ (R_SEG 0) HS4 eq_refl
    ltac:(rol_seg_ok A44 A33 RD16 RD20 Rrole Hv)
    ltac:(rol_seg_disj A44 Usp1)) as HS5.
  clear HS4.
  assert (SHOK5 : sh_ok SEGS rol_Bx [mkSHE 44 16 24] E1 (mrestrict (w_H W3) mem3)).
  { constructor; [|constructor].
    exact (rol_shent_seg E1 W3 mem3 p b (req_size m) A32 A44 RA16 Hbapp ltac:(lia) ltac:(lia)). }
  (* 0x89c04 beqz a0: p <> 0, not taken *)
  psrr_branch_tok RUN BR HS5 SHOK5 Bspan.
  { exfalso. rewrite (rol_beq0 _ 44 p A44 ltac:(lia)) in Hc. apply Z.eqb_eq in Hc. lia. }
  (* 0x89c08 .. 0x89c7c: the alignment trap of p (0x89c10, not taken: atom 44's fact), the check of p + 20 (its slow
     arm 0x89c84 passes), role_set = 0, the epilogue *)
  paj_run_tok RUN HS5 HJ3 SHOK5 Bspan; [awr_ok_tac; exact Usp1 |].
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - 32 <= a < spZ regs) HFr
    ltac:(intros b0 wlo whi a Hin' Hrr; vm_compute in Hin';
          repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp1 in Hrr; lia|]);
          destruct Hin')) as UN4.
  eapply (RET W3 _ _ _ _ _ HS5 eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'.
  prreg HS5 (1%bv : bv 5) R1. prreg HS5 (10%bv : bv 5) R10.
  unfold apost_base. eexists _, _, _, _, _.
  split; [cbn [ms_regs]; rewrite R1; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia;
          rewrite (proj1 HAG 1%nat) by lia; rewrite F1, Hra; reflexivity|].
  split; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ3|].
  split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (rol_extra v) HS5); [|vm_compute; reflexivity]|].
  { rol_agree32 HAE1. }
  split; [cbn [ms_regs]; rewrite R10; reflexivity|].
  split; [exact I|].
  split; [|exact HNA3].
  intros a Ha Hn _. rewrite WS in Hn. rewrite UN4 by (first [exact Ha | cbv beta; lia]). apply UN3; [exact Ha | rewrite WS; lia]. }
(* role_set = 1: a0 = 1, and the role is stored at out when out <> 0 *)
assert (RR : r_role rcs nm = Some v) by (unfold r_role; rewrite RF, RSS, Hv; reflexivity).
rewrite RR in *. cbn [role_W] in *.
pose proof (st_ok_pi_add_fact _ _ _ 44%nat (mkAF 0 (2 ^ 47 - 24) 2) HS2
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite A44, unsigned_lit_small by lia; change (2 ^ 2) with 4; lia))
  as HS4.
clear HS2.
pose proof (st_ok_pi_add_region _ _ _ (R_SEG 1) HS4 eq_refl
  ltac:(rol_seg_ok A44 A33 RD16 RD20 Rrole Hv)
  ltac:(rol_seg_disj A44 Usp1)) as HS5.
(* HS4, the state before the entry's region, is kept for the cases where out lies in the entry *)
assert (SH44 : shent_ok SEGS rol_Bx E1 (mrestrict (w_H W3) mem3) (mkSHE 44 16 24))
  by exact (rol_shent_seg E1 W3 mem3 p b (req_size m) A32 A44 RA16 Hbapp ltac:(lia) ltac:(lia)).
destruct (Z.eq_dec out 0) as [Ho0 | Ho0].
{ (* out = 0: the branch at 0x89c34 to the epilogue, and the return of 1 with no store *)
  subst out. cbn [Z.eqb] in *.
  assert (SHOK5 : sh_ok SEGS rol_Bx [mkSHE 44 16 24] E1 (mrestrict (w_H W3) mem3)) by (constructor; [exact SH44 | constructor]).
  psrr_branch_tok RUN BR HS5 SHOK5 Bspan.
  { exfalso. rewrite (rol_beq0 _ 44 p A44 ltac:(lia)) in Hc. apply Z.eqb_eq in Hc. lia. }
  paj_run_tok RUN HS5 HJ3 SHOK5 Bspan; [awr_ok_tac; exact Usp1 |].
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - 32 <= a < spZ regs) HFr ltac:(rol_win Usp1 A12 A44)) as UN4.
  clear HFr HF HG Hc.
  (* 0x89c34 beqz s0: out = 0, taken *)
  psrr_branch_tok RUN BR HS5 SHOK5 Bspan.
  2:{ exfalso. rewrite (rol_beq0 _ 12 0) in Hc; [discriminate Hc | rol_ew A12 | lia]. }
  paj_run_tok RUN HS5 HJ3 SHOK5 Bspan; [awr_ok_tac; exact Usp1 |].
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - 32 <= a < spZ regs) HFr ltac:(rol_win Usp1 A12 A44)) as UN5.
  eapply (RET W3 _ _ _ _ _ HS5 eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'.
  prreg HS5 (1%bv : bv 5) R1. prreg HS5 (10%bv : bv 5) R10.
  unfold apost_base. eexists _, _, _, _, _.
  rol_head HS5 HJ3 R1 HAG F1 Hra HAE1 regs v.
  split; [cbn [ms_regs]; rewrite R10; reflexivity|].
  split; [intros Hz; exfalso; exact (Hz eq_refl)|].
  split; [|exact HNA3].
  intros a Ha Hn _. rewrite WS in Hn. rewrite UN5 by (first [exact Ha | cbv beta; lia]).
  rewrite UN4 by (first [exact Ha | cbv beta; lia]). apply UN3; [exact Ha | rewrite WS; lia]. }
(* out <> 0: the cell the store writes, at the call's return *)
replace (out =? 0) with false in * by (symmetry; apply Z.eqb_neq; exact Ho0).
destruct HOUT as [Ho0' | (Ho4 & HD)]; [contradiction|].
pose proof HJc3 as (_ & _ & _ & _ & _ & HFR3 & _). cbn [app] in HFR3.
pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
assert (UN3k : forall a, 0 <= a < spZ regs - STK_reac_segconf_role_B -> rdW W3 mem3 a = rdW W mem a)
  by (intros a Ha; apply UN3; lia).
assert (OF : 4096 <= out /\ out + 4 <= 2 ^ 47 /\
  (forall o, 0 <= o < 4 -> apresent (w_H W3) mem3 (out + o)) /\
  range_addressable (rdW W3 mem3) SHADOW_OFF out 4 /\
  (forall x, out <= x < out + 4 -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)) /\
  (out + 4 <= spZ regs - STK_reac_segconf_role_B \/ spZ regs <= out) /\
  (forall a, out <= a < out + 4 ->
     awr_byte SEGS B STK_reac_segconf_role_B (spZ regs) [(out, out + 4)] (ablocks B ly S) (ablocks B ly3 S3) (frames S) ly3 [] a)).
{ destruct HD as [((cid & pos & Hin & Hcid & Hf1 & Hf2) & RA0) | [((b' & m' & Hin & Hb1' & Hb2') & RA0) | (Hsp & Hot & Hpr & HAP)]].
  - (* a side-stack frame of the caller *)
    destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (FB4 & Fce & Fapp).
    assert (Hin3 : In (cid, pos) (frames S3)) by (rewrite HFR3; exact Hin).
    destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 cid pos HAR3 Hin3) as (_ & _ & HFP & _).
    rewrite Hly3 in HFP. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Fapp.
    split; [lia|]. split; [lia|]. split; [intros o Ho; apply (proj1 (HFP (out + o) ltac:(lia)))|].
    split; [intros x Hx; destruct (RA0 x Hx) as (s & Hs & Hok); exists s; split; [|exact Hok];
            rewrite UN3k; [exact Hs|]; unfold shadow_of_addr, SHADOW_OFF;
            assert (x / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia);
            assert (0 <= x / 8) by (apply Z.div_pos; lia);
            assert (alloc_ceiling / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia); rewrite WS; lia|].
    split; [intros x Hx; unfold SHADOW_OFF; lia|].
    split; [left; rewrite WS; lia|].
    intros a Ha. right; right; right; right. right; right. split; [exists (out, out + 4); split; [left; reflexivity | cbn [fst snd]; lia]|].
    exists cid, pos. split; [exact Hin|]. left. unfold in_zr. cbn [fst snd]. rewrite Hly3. lia.
  - (* a heap block *)
    assert (Hin3 : In (b', m') (ablocks B ly3 S3)) by (apply (Permutation_in _ (Permutation_sym HPerm)); exact Hin).
    destruct (al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 b' m' HAR3 Hin3) as (_ & B4 & Bce & Bapp & BP & _ & Bm).
    pose proof (req_size_pos m' ltac:(lia)) as [_ Hrm'].
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Bapp.
    split; [lia|]. split; [lia|]. split; [intros o Ho; apply (proj1 (BP (out + o) ltac:(lia)))|].
    split; [apply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 mem3 md3 b' m'); [exact HAR3 | exact Hin3 | lia | lia]|].
    split; [intros x Hx; unfold SHADOW_OFF; lia|].
    split; [left; rewrite WS; lia|].
    intros a Ha. right; left. split; [exists (out, out + 4); split; [left; reflexivity | cbn [fst snd]; lia]|].
    exists b', m'. split; [exact Hin3 | lia].
  - (* a slot of the caller's real stack *)
    assert (HPc : astack_pres ly (w_H W) (ms_mem ms) (spZ regs + -32)).
    { intros a Ha. destruct (Z_lt_le_dec a (spZ regs)) as [Hlt | Hge]; [apply HJpres; rewrite WS; lia|].
      destruct (HAP a ltac:(lia)) as [Hh Hb]. split; [exact Hh|].
      rewrite HF1; [exact Hb|]. intros (r & Hr & Hrr). vm_compute in Hr.
      repeat (destruct Hr as [<- | Hr];
        [cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Hrr; rewrite ?Usp0 in Hrr;
         unfold w64 in Hrr; rewrite unsigned_lit_small in Hrr by lia; lia|]).
      destruct Hr. }
    pose proof (astack_pres_journal SEGS B pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc3 HPc
      ltac:(intros a (r & Hr & _); destruct Hr)) as HPS3.
    pose proof (al_zshadow _ _ LAWS ly3 S3 W3 mem3 md3 _ HAR3 ltac:(unfold zero_shadow_ranges; left; reflexivity)) as HZ.
    cbn [fst snd] in HZ. rewrite Hly3 in HPS3, HZ.
    unfold page_aligned in T5, T6.
    split; [lia|]. split; [lia|]. split; [intros o Ho; apply HPS3; unfold STK_reac_segconf_find_B, ESTACK; lia|].
    split.
    { apply (range_addressable_sub _ _ (ly_stk_lo ly) (ly_stk_hi ly - ly_stk_lo ly)); [| lia | lia].
      apply zero_shadow_range; [| | exact HZ].
      - replace (ly_stk_lo ly) with ((512 * (ly_stk_lo ly / 4096)) * 8) by (pose proof (Z.div_mod (ly_stk_lo ly) 4096 ltac:(lia)); lia).
        apply Z.mod_mul. lia.
      - replace (ly_stk_hi ly - ly_stk_lo ly) with ((512 * (ly_stk_hi ly / 4096) - 512 * (ly_stk_lo ly / 4096)) * 8)
          by (pose proof (Z.div_mod (ly_stk_lo ly) 4096 ltac:(lia)); pose proof (Z.div_mod (ly_stk_hi ly) 4096 ltac:(lia)); lia).
        apply Z.mod_mul. lia. }
    split; [intros x Hx; unfold SHADOW_OFF; lia|].
    split; [right; lia|].
    intros a Ha. right; right; right; right. right; left. split; [exists (out, out + 4); split; [left; reflexivity | cbn [fst snd]; lia]|].
    rewrite Hly3. lia. }
destruct OF as (O4 & O47 & OP & ORA & OAPP & OWIN & OAWR).
cbv iota in HJ3 |- *.
assert (Hsep : (out + 4 <= p + 16 \/ p + 24 <= out) \/ out = p + 16 \/ out = p + 20)
  by (pose proof (Z.div_mod out 4 ltac:(lia)); pose proof (Z.div_mod p 4 ltac:(lia)); lia).
assert (SH12 : shent_ok SEGS rol_Bx E1 (mrestrict (w_H W3) mem3) (mkSHE 12 0 4)).
{ apply (shent_ok_of_range SEGS (w_H W3) mem3 E1 rol_Bx 12 out 4 out 0 4 ORA).
  - unfold rol_Bx. rewrite (U_atom E1 32 SB A32) by (unfold SB; lia). reflexivity.
  - apply U_atom; [exact A12 | lia].
  - lia.
  - lia.
  - intros x Hx. cbn [Z.min Z.max] in Hx. apply OAPP. lia. }
destruct Hsep as [Hap | [Hov | Hov]].
{ (* out apart from the entry's two fields: the out cell is a region of its own *)
  pose proof (st_ok_pi_add_fact _ _ _ 12%nat (mkAF 0 (2 ^ 47 - 4) 2) HS5
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite A12, unsigned_lit_small by lia; change (2 ^ 2) with 4; lia))
    as HS6.
  clear HS5.
  pose proof (st_ok_pi_add_region _ _ _ R_OUT HS6 eq_refl
    ltac:(unfold region_ok, R_OUT;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
          rewrite A12, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
          intros o Ho; apply (apresent_writable SEGS); apply OP; lia)
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
          cbn [all_disjoint]; unfold extent_disjoint, R_OUT; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
          rewrite A12, A44, Usp1, !unsigned_lit_small by lia; rewrite WS in OWIN; repeat split; lia)) as HS7.
  clear HS6.
  assert (SHOK7 : sh_ok SEGS rol_Bx [mkSHE 44 16 24; mkSHE 12 0 4] E1 (mrestrict (w_H W3) mem3))
    by (constructor; [exact SH44 | constructor; [exact SH12 | constructor]]).
  (* 0x89c04 beqz a0: p <> 0, not taken *)
  psrr_branch_tok RUN BR HS7 SHOK7 Bspan.
  { exfalso. rewrite (rol_beq0 _ 44 p A44 ltac:(lia)) in Hc. apply Z.eqb_eq in Hc. lia. }
  clear Hc.
  paj_run_tok RUN HS7 HJ3 SHOK7 Bspan; [rol_awr_at OAWR 12%nat A12 Usp1 out |].
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => (spZ regs - 32 <= a < spZ regs) \/ (out <= a < out + 4)) HFr
    ltac:(rol_win Usp1 A12 A44)) as UN4.
  clear HFr HF HG.
  (* 0x89c34 beqz s0: out <> 0, not taken; the run after it passes the alignment trap of out (0x89c3c, not taken:
     atom 12's fact) *)
  psrr_branch_tok RUN BR HS7 SHOK7 Bspan.
  { exfalso. rewrite (rol_beq0 _ 12 out) in Hc; [apply Z.eqb_eq in Hc; lia | rol_ew A12 | lia]. }
  clear Hc.
  paj_run_tok RUN HS7 HJ3 SHOK7 Bspan; [rol_awr_at OAWR 12%nat A12 Usp1 out |].
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => (spZ regs - 32 <= a < spZ regs) \/ (out <= a < out + 4)) HFr
    ltac:(rol_win Usp1 A12 A44)) as UN5.
  eapply (RET W3 _ _ _ _ _ HS7 eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'.
  prreg HS7 (1%bv : bv 5) R1. prreg HS7 (10%bv : bv 5) R10.
  (* the out cell holds the role: the chunk the store left in the out region *)
  pose proof (st_ok_pi_region_nth _ _ _ 0
    (YP09.mkRegion (Some 12%nat) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SExt true 32 (SOff 33 0)))]) HS7
    ltac:(vm_compute; reflexivity)) as RO.
  destruct RO as (_ & _ & _ & RCH). apply Forall_inv in RCH.
  cbn [base_val YP09.r_base] in RCH.
  rewrite (rol_ew_bv _ 12 out) in RCH; [| rol_ew A12 | lia].
  pose proof (val_of_chunk_ok SEGS _ _ _ 0 4 _ v RCH
    ltac:(apply rol_sext_role; [rol_ew A33 | rewrite Hv; lia])
    ltac:(change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); rewrite Hv; lia) ltac:(zside)) as VM.
  rewrite Z.add_0_r in VM.
  unfold apost_base. eexists _, _, _, _, _.
  rol_head HS7 HJ3 R1 HAG F1 Hra HAE1 regs v.
  split; [cbn [ms_regs]; rewrite R10; reflexivity|].
  split; [intros _; exact (rol_sa_of_val _ _ _ _ _ VM)|].
  split; [|exact HNA3].
  intros a Ha Hn Ho. rewrite WS in Hn. rewrite UN5 by (first [exact Ha | cbv beta; lia]).
  rewrite UN4 by (first [exact Ha | cbv beta; lia]). apply UN3; [exact Ha | rewrite WS; lia]. }
{ (* out = p + 16: the out cell is the entry's field at + 16, which the store overwrites; s0 is rebased on
     find's result (atom 44) so every access of the rest goes through one region *)
  clear HS5.
  prreg HS4 (8%bv : bv 5) Q8b.
  pose proof (st_ok_pi_set_reg _ _ _ (8%bv : bv 5) (SOff 44 16) HS4
    ltac:(intros Hz; apply (f_equal bv_unsigned) in Hz; discriminate Hz)
    ltac:(cbn [ms_regs restrict mkst]; rewrite Q8b; cbn [sv_denot]; rewrite ?A12, ?A44, ?unsigned_lit_small by lia; f_equal; lia)) as HS6.
  clear HS4.
  assert (OPd : forall o, 16 <= o < 16 + 4 -> apresent (w_H W3) mem3 (p + o))
    by (intros o Ho; replace (p + o) with (out + (o - 16)) by lia; apply OP; lia).
  pose proof (st_ok_pi_add_region _ _ _ (R_SEGW 1 16) HS6 eq_refl
    ltac:(rol_segw_ok A44 A33 RD16 RD20 Rrole Hv OPd)
    ltac:(rol_seg_disj A44 Usp1)) as HS7.
  clear HS6.
  assert (SHOK7 : sh_ok SEGS rol_Bx [mkSHE 44 16 24] E1 (mrestrict (w_H W3) mem3))
    by (constructor; [exact SH44 | constructor]).
  (* 0x89c04 beqz a0: p <> 0, not taken *)
  psrr_branch_tok RUN BR HS7 SHOK7 Bspan.
  { exfalso. rewrite (rol_beq0 _ 44 p A44 ltac:(lia)) in Hc. apply Z.eqb_eq in Hc. lia. }
  clear Hc.
  paj_run_tok RUN HS7 HJ3 SHOK7 Bspan; [rol_awr_at OAWR 44%nat A44 Usp1 p |].
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => (spZ regs - 32 <= a < spZ regs) \/ (out <= a < out + 4)) HFr
    ltac:(rol_win Usp1 A12 A44)) as UN4.
  (* s0 = p + 16 <> 0 and s0 & 3 = 0 (atom 44's fact), so the run went through the beqz s0 at 0x89c34 and the
     alignment trap of out at 0x89c3c (neither taken) and the store to the return *)
  eapply (RET W3 _ _ _ _ _ HS7 eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'.
  prreg HS7 (1%bv : bv 5) R1. prreg HS7 (10%bv : bv 5) R10.
  (* the out cell holds the role: the chunk the store left at + 16 *)
  pose proof (st_ok_pi_region_nth _ _ _ 0
    (YP09.mkRegion (Some 44%nat) 16 24 16 20 [YP09.mkChunk 16 (CVal 4 (SExt true 32 (SOff 33 0))); YP09.mkChunk 20 (CVal 4 (SLit 1))]) HS7
    ltac:(vm_compute; reflexivity)) as RO.
  destruct RO as (_ & _ & _ & RCH). apply Forall_inv in RCH.
  cbn [base_val YP09.r_base] in RCH.
  rewrite (rol_ew_bv _ 44 p) in RCH; [| rol_ew A44 | lia].
  pose proof (val_of_chunk_ok SEGS _ _ _ 16 4 _ v RCH
    ltac:(apply rol_sext_role; [rol_ew A33 | rewrite Hv; lia])
    ltac:(change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); rewrite Hv; lia) ltac:(zside)) as VM.
  replace (p + 16) with out in VM by lia.
  unfold apost_base. eexists _, _, _, _, _.
  rol_head HS7 HJ3 R1 HAG F1 Hra HAE1 regs v.
  split; [cbn [ms_regs]; rewrite R10; reflexivity|].
  split; [intros _; exact (rol_sa_of_val _ _ _ _ _ VM)|].
  split; [|exact HNA3].
  intros a Ha Hn Ho. rewrite WS in Hn.
  rewrite UN4 by (first [exact Ha | cbv beta; lia]). apply UN3; [exact Ha | rewrite WS; lia]. }
{ (* out = p + 20: the out cell is the entry's field at + 20, which the store overwrites; s0 is rebased on
     find's result (atom 44) so every access of the rest goes through one region *)
  clear HS5.
  prreg HS4 (8%bv : bv 5) Q8b.
  pose proof (st_ok_pi_set_reg _ _ _ (8%bv : bv 5) (SOff 44 20) HS4
    ltac:(intros Hz; apply (f_equal bv_unsigned) in Hz; discriminate Hz)
    ltac:(cbn [ms_regs restrict mkst]; rewrite Q8b; cbn [sv_denot]; rewrite ?A12, ?A44, ?unsigned_lit_small by lia; f_equal; lia)) as HS6.
  clear HS4.
  assert (OPd : forall o, 20 <= o < 20 + 4 -> apresent (w_H W3) mem3 (p + o))
    by (intros o Ho; replace (p + o) with (out + (o - 20)) by lia; apply OP; lia).
  pose proof (st_ok_pi_add_region _ _ _ (R_SEGW 1 20) HS6 eq_refl
    ltac:(rol_segw_ok A44 A33 RD16 RD20 Rrole Hv OPd)
    ltac:(rol_seg_disj A44 Usp1)) as HS7.
  clear HS6.
  assert (SHOK7 : sh_ok SEGS rol_Bx [mkSHE 44 16 24] E1 (mrestrict (w_H W3) mem3))
    by (constructor; [exact SH44 | constructor]).
  (* 0x89c04 beqz a0: p <> 0, not taken *)
  psrr_branch_tok RUN BR HS7 SHOK7 Bspan.
  { exfalso. rewrite (rol_beq0 _ 44 p A44 ltac:(lia)) in Hc. apply Z.eqb_eq in Hc. lia. }
  clear Hc.
  paj_run_tok RUN HS7 HJ3 SHOK7 Bspan; [rol_awr_at OAWR 44%nat A44 Usp1 p |].
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => (spZ regs - 32 <= a < spZ regs) \/ (out <= a < out + 4)) HFr
    ltac:(rol_win Usp1 A12 A44)) as UN4.
  (* s0 = p + 20 <> 0 and s0 & 3 = 0 (atom 44's fact), so the run went through the beqz s0 at 0x89c34 and the
     alignment trap of out at 0x89c3c (neither taken) and the store to the return *)
  eapply (RET W3 _ _ _ _ _ HS7 eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'.
  prreg HS7 (1%bv : bv 5) R1. prreg HS7 (10%bv : bv 5) R10.
  (* the out cell holds the role: the chunk the store left at + 20 *)
  pose proof (st_ok_pi_region_nth _ _ _ 0
    (YP09.mkRegion (Some 44%nat) 16 24 20 24 [YP09.mkChunk 20 (CVal 4 (SExt true 32 (SOff 33 0))); YP09.mkChunk 16 (CVal 4 (SOff 33 0))]) HS7
    ltac:(vm_compute; reflexivity)) as RO.
  destruct RO as (_ & _ & _ & RCH). apply Forall_inv in RCH.
  cbn [base_val YP09.r_base] in RCH.
  rewrite (rol_ew_bv _ 44 p) in RCH; [| rol_ew A44 | lia].
  pose proof (val_of_chunk_ok SEGS _ _ _ 20 4 _ v RCH
    ltac:(apply rol_sext_role; [rol_ew A33 | rewrite Hv; lia])
    ltac:(change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); rewrite Hv; lia) ltac:(zside)) as VM.
  replace (p + 20) with out in VM by lia.
  unfold apost_base. eexists _, _, _, _, _.
  rol_head HS7 HJ3 R1 HAG F1 Hra HAE1 regs v.
  split; [cbn [ms_regs]; rewrite R10; reflexivity|].
  split; [intros _; exact (rol_sa_of_val _ _ _ _ _ VM)|].
  split; [|exact HNA3].
  intros a Ha Hn Ho. rewrite WS in Hn.
  rewrite UN4 by (first [exact Ha | cbv beta; lia]). apply UN3; [exact Ha | rewrite WS; lia]. }
Qed.
End e.
End f.
End d.
Print Assumptions reac_segconf_role_walk.
About reac_segconf_role_walk.
